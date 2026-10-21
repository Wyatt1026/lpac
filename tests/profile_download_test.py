#!/usr/bin/env python3
"""Drives `lpac profile download` against a fake eUICC and a fake SM-DP+.

lpac's stdio APDU and HTTP drivers hand every card exchange and every HTTPS
request to whoever holds lpac's stdin and stdout, so this script plays both the
card and the server and records what reached each of them. Nothing here talks
to a real card or a real SM-DP+.

What it is mostly there to check is how a download that did not finish is
cancelled. In SGP.22 v2.2.2 section 3.1.3.1 the SM-DP+ keeps the order in
'Released', available for a further retry, only for postponed(1) and
timeout(2); every other CancelSession reason ends the order for good.

usage: LPAC=<lpac> python3 tests/profile_download_test.py [unittest options]

<lpac> is an installed lpac (`DESTDIR=<dir> cmake --install <build>`), whose
drivers sit beside it in driver/.
"""

from __future__ import annotations

import base64
import hashlib
import json
import os
import signal
import subprocess
import tempfile
import threading
import time
import unittest

LPAC = os.environ.get("LPAC", "")

SMDP = "smdp.example.com"
MATCHING_ID = "TEST-MATCHING-ID"
CONFIRMATION_CODE = "4711"
TRANSACTION_ID = bytes.fromhex("0123456789ABCDEF0123456789ABCDEF")
ICCID = "89440000000000000012"
CI_PKID = bytes.fromhex("81370F5125D0B1D408D4C3B232E6D25E795BEBFB")
SMDP_OID = bytes.fromhex("2B0601040182ED6F")

# CancelSessionReason, SGP.22 v2.2.2 section 5.7.14.
END_USER_REJECTION = 0
POSTPONED = 1
LOAD_BPP_EXECUTION_ERROR = 5

SW_OK = bytes.fromhex("9000")


def tlv(tag: int, value: bytes = b"") -> bytes:
    """One BER-TLV, in the definite length form libeuicc reads."""
    tag_bytes = tag.to_bytes(max(1, (tag.bit_length() + 7) // 8), "big")
    if len(value) < 0x80:
        length = bytes([len(value)])
    else:
        count = (len(value).bit_length() + 7) // 8
        length = bytes([0x80 | count]) + len(value).to_bytes(count, "big")
    return tag_bytes + length + value


def read_tlv(data: bytes, offset: int = 0) -> tuple[int, bytes, int]:
    """The tag and value of the TLV at `offset`, and the offset past it."""
    tag = data[offset]
    offset += 1
    if tag & 0x1F == 0x1F:
        while True:
            tag = (tag << 8) | data[offset]
            offset += 1
            if not data[offset - 1] & 0x80:
                break
    length = data[offset]
    offset += 1
    if length & 0x80:
        count = length & 0x7F
        length = int.from_bytes(data[offset : offset + count], "big")
        offset += count
    return tag, data[offset : offset + length], offset + length


def children(data: bytes) -> dict[int, bytes]:
    """The value of each TLV in `data`, by tag."""
    found: dict[int, bytes] = {}
    offset = 0
    while offset < len(data):
        tag, value, offset = read_tlv(data, offset)
        found.setdefault(tag, value)
    return found


def b64(data: bytes) -> str:
    return base64.b64encode(data).decode()


def swapped_bcd(digits: str) -> bytes:
    """An ICCID the way the card stores it, two digits a byte, low nibble first."""
    return bytes(int(digits[i + 1] + digits[i], 16) for i in range(0, len(digits), 2))


def signature() -> bytes:
    return tlv(0x5F37, bytes(64))


class Card:
    """An eUICC that answers every ES10 command lpac sends in a download.

    It checks no signature, which is the server's business and not lpac's;
    what it keeps is what lpac asked of it.
    """

    def __init__(self, refuses_bpp: bool = False) -> None:
        self.refuses_bpp = refuses_bpp
        # The tag of each ES10 command, in the order they arrived.
        self.commands: list[int] = []
        # The children of the PrepareDownloadRequest, by tag, once one arrives.
        self.prepare_download: dict[int, bytes] | None = None
        self.cancel_reasons: list[int] = []
        self._blocks = b""

    def handle(self, func: str, param: str | None) -> dict:
        if func == "logic_channel_open":
            return {"ecode": 1}
        if func != "transmit":
            return {"ecode": 0}
        apdu = bytes.fromhex(param or "")
        ins, p1, lc = apdu[1], apdu[2], apdu[4]
        if ins != 0xE2:  # STORE DATA carries every ES10 command.
            return {"ecode": 0, "data": "6D00"}
        self._blocks += apdu[5 : 5 + lc]
        if not p1 & 0x80:  # More blocks of the same command follow.
            return {"ecode": 0, "data": SW_OK.hex()}
        command, self._blocks = self._blocks, b""
        return {"ecode": 0, "data": self.answer(command).hex()}

    def answer(self, command: bytes) -> bytes:
        tag, value, _ = read_tlv(command)
        self.commands.append(tag)
        if tag == 0xBF2E:  # GetEuiccChallenge
            return tlv(0xBF2E, tlv(0x80, bytes(16))) + SW_OK
        if tag == 0xBF20:  # GetEuiccInfo1
            info = tlv(0x82, bytes([2, 2, 0])) + tlv(0xA9, tlv(0x04, CI_PKID)) + tlv(0xAA, tlv(0x04, CI_PKID))
            return tlv(0xBF20, info) + SW_OK
        if tag == 0xBF38:  # AuthenticateServer
            signed = tlv(0x30, tlv(0x80, TRANSACTION_ID))
            return tlv(0xBF38, tlv(0xA0, signed + signature())) + SW_OK
        if tag == 0xBF21:  # PrepareDownload
            self.prepare_download = children(value)
            signed = tlv(0x30, tlv(0x80, TRANSACTION_ID) + tlv(0x5F49, bytes(65)))
            return tlv(0xBF21, tlv(0xA0, signed + signature())) + SW_OK
        if tag == 0xBF41:  # CancelSession
            reason = children(value)[0x81]
            self.cancel_reasons.append(int.from_bytes(reason, "big"))
            signed = tlv(0x30, tlv(0x80, TRANSACTION_ID) + tlv(0x06, SMDP_OID) + tlv(0x81, reason))
            return tlv(0xBF41, tlv(0x30, signed + signature())) + SW_OK
        # What is left is a segment of the Bound Profile Package, which arrives
        # one ES10b.LoadBoundProfilePackage at a time: the BF36 header with
        # InitialiseSecureChannel, then each of the parts after it.
        if self.refuses_bpp:
            return bytes.fromhex("6A80")
        if tag == 0x86:  # The last segment: the Profile Installation Result.
            metadata = tlv(0x80, b"\x07") + tlv(0x81, bytes([0x07, 0x80])) + tlv(0x5A, swapped_bcd(ICCID))
            result = tlv(0xA2, tlv(0xA0, tlv(0x4F, bytes(16)) + tlv(0x04, b"")))
            data = tlv(0x80, TRANSACTION_ID) + tlv(0xBF2F, metadata) + tlv(0x06, SMDP_OID) + result
            return tlv(0xBF37, tlv(0xBF27, data) + signature()) + SW_OK
        return SW_OK


def executed(**fields: str) -> dict:
    return {"header": {"functionExecutionStatus": {"status": "Executed-Success"}}, **fields}


def failed(subject: str, reason: str, message: str | None = None) -> dict:
    status = {"subjectCode": subject, "reasonCode": reason}
    if message is not None:
        status["message"] = message
    return {"header": {"functionExecutionStatus": {"status": "Failed", "statusCodeData": status}}}


class Server:
    """An SM-DP+ holding one order, which may want a confirmation code.

    `answers` replaces what an ES9+ function returns, by function name, with an
    (HTTP status, JSON body) pair.
    """

    def __init__(self, cc_required: bool = False, answers: dict[str, tuple[int, dict]] | None = None) -> None:
        self.cc_required = cc_required
        self.answers = answers or {}
        # The ES9+ function of each request, in the order they arrived.
        self.calls: list[str] = []
        # The reason inside each CancelSessionResponse lpac passed on.
        self.cancel_reasons: list[int] = []

    def handle(self, url: str, body: bytes) -> tuple[int, bytes]:
        function = url.rsplit("/", 1)[-1]
        self.calls.append(function)
        request = json.loads(body)
        if function == "cancelSession":
            response = base64.b64decode(request["cancelSessionResponse"])
            _, ok, _ = read_tlv(response)
            _, signed, _ = read_tlv(children(ok)[0x30])
            self.cancel_reasons.append(int.from_bytes(children(signed)[0x81], "big"))
        status, answer = self.answers.get(function) or (200, self.answer(function))
        return status, json.dumps(answer).encode()

    def answer(self, function: str) -> dict:
        transaction_id = TRANSACTION_ID.hex().upper()
        if function == "initiateAuthentication":
            return executed(
                transactionId=transaction_id,
                serverSigned1=b64(tlv(0x30, tlv(0x80, TRANSACTION_ID) + tlv(0x83, SMDP.encode()))),
                serverSignature1=b64(signature()),
                euiccCiPKIdToBeUsed=b64(tlv(0x04, CI_PKID)),
                serverCertificate=b64(tlv(0x30)),
            )
        if function == "authenticateClient":
            metadata = (
                tlv(0x5A, swapped_bcd(ICCID))
                + tlv(0x91, b"Test Telco")
                + tlv(0x92, b"Test Profile")
                + tlv(0x95, b"\x02")
            )
            cc_required_flag = tlv(0x01, b"\xff" if self.cc_required else b"\x00")
            return executed(
                transactionId=transaction_id,
                profileMetadata=b64(tlv(0xBF25, metadata)),
                smdpSigned2=b64(tlv(0x30, tlv(0x80, TRANSACTION_ID) + cc_required_flag)),
                smdpSignature2=b64(signature()),
                smdpCertificate=b64(tlv(0x30)),
            )
        if function == "getBoundProfilePackage":
            bpp = (
                tlv(0xBF23, tlv(0xA0, b"") + tlv(0x5F49, bytes(65)) + signature())
                + tlv(0xA0, tlv(0x87, bytes(8)))
                + tlv(0xA1, tlv(0x88, bytes(8)))
                + tlv(0xA3, tlv(0x86, bytes(8)))
            )
            return executed(transactionId=transaction_id, boundProfilePackage=b64(tlv(0xBF36, bpp)))
        return executed()


class Run:
    """What one lpac run printed of its own, rather than of its drivers."""

    def __init__(self) -> None:
        self.steps: list[str] = []
        self.result: dict | None = None
        self.stderr = ""


def download(
    args: list[str],
    card: Card,
    server: Server,
    preview_answer: str | None = None,
    interrupt_on: str | None = None,
) -> Run:
    """Runs `lpac profile download <args>`, playing `card` and `server`.

    `preview_answer` is what lpac reads when it asks for one; `interrupt_on`
    names the ES9+ function during which lpac is sent SIGINT.
    """
    run = Run()
    with tempfile.TemporaryFile() as stderr, subprocess.Popen(
        [LPAC, "profile", "download", *args],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=stderr,
        env={"LPAC_APDU": "stdio", "LPAC_HTTP": "stdio"},
    ) as lpac:
        assert lpac.stdin is not None and lpac.stdout is not None
        # A request the fakes left unanswered would otherwise hang the test.
        watchdog = threading.Timer(30, lpac.kill)
        watchdog.start()
        try:
            for line in lpac.stdout:
                message = json.loads(line)
                kind, payload = message["type"], message["payload"]
                if kind == "apdu":
                    reply = card.handle(payload["func"], payload["param"])
                elif kind == "http":
                    function = payload["url"].rsplit("/", 1)[-1]
                    if function == interrupt_on:
                        lpac.send_signal(signal.SIGINT)
                        time.sleep(0.2)
                    rcode, body = server.handle(payload["url"], bytes.fromhex(payload["tx"]))
                    reply = {"rcode": rcode, "rx": body.hex()}
                else:
                    if kind == "progress":
                        run.steps.append(payload["message"])
                        if payload["message"] == "preview" and preview_answer is not None:
                            # lpac reads one character, with getchar(), from the
                            # stdin the drivers read their answers from: a newline
                            # after it would be taken for the next answer.
                            lpac.stdin.write(preview_answer.encode())
                            lpac.stdin.flush()
                    elif kind == "lpa":
                        run.result = payload
                    continue
                lpac.stdin.write(json.dumps({"type": kind, "payload": reply}).encode() + b"\n")
                lpac.stdin.flush()
            lpac.wait(timeout=10)
        finally:
            watchdog.cancel()
            if lpac.poll() is None:
                lpac.kill()
        stderr.seek(0)
        run.stderr = stderr.read().decode(errors="replace")
    return run


class ProfileDownloadTest(unittest.TestCase):
    def assert_result(self, run: Run, message: str, data: str | None = None) -> None:
        self.assertIsNotNone(run.result, f"lpac printed no result; stderr: {run.stderr}")
        self.assertEqual(run.result["message"], message, run.result)
        if data is not None:
            self.assertEqual(run.result["data"], data, run.result)

    def assert_cancelled(self, card: Card, server: Server, reason: int) -> None:
        """The session was cancelled with `reason`, on the card and then at the server."""
        self.assertEqual(card.cancel_reasons, [reason])
        self.assertEqual(server.cancel_reasons, [reason])
        self.assertEqual(server.calls[-1], "cancelSession")

    def test_a_code_only_the_smdp_asks_for_is_reported_and_leaves_the_order_open(self) -> None:
        # The Vodafone Portugal order of 2026-10-21: no $1 in the activation
        # code, ccRequiredFlag set in smdpSigned2.
        card, server = Card(), Server(cc_required=True)
        run = download(["-s", SMDP, "-m", MATCHING_ID], card, server)

        self.assert_result(run, "confirmation_code", "required")
        # Nothing was asked of the card that it could have answered.
        self.assertNotIn(0xBF21, card.commands)
        self.assertNotIn("getBoundProfilePackage", server.calls)
        self.assert_cancelled(card, server, POSTPONED)

    def test_a_code_the_smdp_asks_for_is_hashed_into_prepare_download(self) -> None:
        card, server = Card(), Server(cc_required=True)
        run = download(["-s", SMDP, "-m", MATCHING_ID, "-c", CONFIRMATION_CODE], card, server)

        self.assert_result(run, "success")
        expected = hashlib.sha256(hashlib.sha256(CONFIRMATION_CODE.encode()).digest() + TRANSACTION_ID).digest()
        self.assertIsNotNone(card.prepare_download)
        self.assertEqual(card.prepare_download.get(0x04), expected)
        self.assertEqual(card.cancel_reasons, [])
        self.assertNotIn("cancelSession", server.calls)

    def test_a_download_no_one_asked_a_code_for_sends_none(self) -> None:
        card, server = Card(), Server(cc_required=False)
        run = download(["-s", SMDP, "-m", MATCHING_ID], card, server)

        self.assert_result(run, "success")
        self.assertEqual(run.result["data"]["iccid"], ICCID)
        self.assertNotIn(0x04, card.prepare_download)
        self.assertEqual(card.cancel_reasons, [])

    def test_an_activation_code_that_flags_the_code_stops_before_the_card(self) -> None:
        card, server = Card(), Server(cc_required=True)
        run = download(["-a", f"LPA:1${SMDP}${MATCHING_ID}$$1"], card, server)

        self.assert_result(run, "confirmation_code", "required")
        self.assertEqual(card.commands, [])
        self.assertEqual(server.calls, [])

    def test_a_server_that_refused_the_client_leaves_the_order_open(self) -> None:
        # What every retry of the 2026-10-21 order met.
        refusal = failed("8.8.5", "3.8", "Profile Download Cancelled by End-User")
        card, server = Card(), Server(answers={"authenticateClient": (200, refusal)})
        run = download(["-s", SMDP, "-m", MATCHING_ID], card, server)

        self.assert_result(run, "es9p_authenticate_client", "Profile Download Cancelled by End-User")
        self.assert_cancelled(card, server, POSTPONED)

    def test_an_http_failure_at_get_bound_profile_package_leaves_the_order_open(self) -> None:
        card, server = Card(), Server(answers={"getBoundProfilePackage": (503, {})})
        run = download(["-s", SMDP, "-m", MATCHING_ID], card, server)

        self.assert_result(run, "es9p_get_bound_profile_package", "HTTP status code error")
        self.assert_cancelled(card, server, POSTPONED)

    def test_a_refused_code_leaves_the_order_open_for_another_try(self) -> None:
        # Section 3.1.3.2 step 8: until the retry limit, the LPA MAY try again.
        refusal = failed("8.2.7", "3.8", "Confirmation Code is refused")
        card, server = Card(), Server(cc_required=True, answers={"getBoundProfilePackage": (200, refusal)})
        run = download(["-s", SMDP, "-m", MATCHING_ID, "-c", "0000"], card, server)

        self.assert_result(run, "es9p_get_bound_profile_package", "Confirmation Code is refused")
        self.assert_cancelled(card, server, POSTPONED)

    def test_a_card_that_will_not_take_the_bpp_is_a_load_bpp_execution_error(self) -> None:
        # Section 3.1.3.3: status words other than 90 00 or 91 XX.
        card, server = Card(refuses_bpp=True), Server()
        run = download(["-s", SMDP, "-m", MATCHING_ID], card, server)

        self.assert_result(run, "es10b_load_bound_profile_package")
        self.assert_cancelled(card, server, LOAD_BPP_EXECUTION_ERROR)

    def test_a_preview_answered_no_rejects_the_profile(self) -> None:
        card, server = Card(), Server()
        run = download(["-s", SMDP, "-m", MATCHING_ID, "-p"], card, server, preview_answer="n")

        self.assertIn("preview", run.steps)
        self.assert_result(run, "cancelled")
        self.assertNotIn(0xBF21, card.commands)
        self.assert_cancelled(card, server, END_USER_REJECTION)

    def test_an_interrupted_download_rejects_the_profile(self) -> None:
        card, server = Card(), Server()
        run = download(["-s", SMDP, "-m", MATCHING_ID], card, server, interrupt_on="authenticateClient")

        self.assert_result(run, "cancelled")
        self.assert_cancelled(card, server, END_USER_REJECTION)


if __name__ == "__main__":
    if not LPAC:
        raise SystemExit("set LPAC to the lpac executable to test")
    unittest.main()
