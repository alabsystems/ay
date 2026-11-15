# ay-script: z3-reference-tests
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
"""Tests for scripts/_z3_reference.py: the ci/z3.pin reader and the provisioner
of the pinned z3 release asset into the read-only content-addressed cache.

Hermetic: fake archives are written with zipfile and served by an injected
fetch, the cache root is a temporary directory, and nothing touches the network
(urlopen is patched to fail wherever a test asserts it is not reached). The
fake z3 is test_z3_oracle.py's REAL template. Runnable via:

    python3 -m unittest scripts.tests.test_z3_reference
"""
import hashlib
import io
import os
import stat
import subprocess
import sys
import tempfile
import unittest
import warnings
import zipfile
from contextlib import redirect_stderr, redirect_stdout
from unittest import mock

TESTS_DIR = os.path.dirname(os.path.abspath(__file__))
SCRIPTS_DIR = os.path.dirname(TESTS_DIR)
REPO = os.path.dirname(SCRIPTS_DIR)
sys.path.insert(0, SCRIPTS_DIR)
sys.path.insert(0, TESTS_DIR)

import _z3_reference as zr  # noqa: E402
from test_z3_oracle import REAL  # noqa: E402

VERSION = "5.1.0"
STEM = f"z3-{VERSION}-arm64-osx-13.3"
FAKE_Z3 = REAL.format(banner=f"Z3 version {VERSION} - 64 bit")
ROW_KEYS = ("darwin_arm64", "darwin_x86_64", "linux_x86_64", "linux_aarch64")


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def member(name: str, data: bytes, mode: int = 0o100644) -> tuple:
    info = zipfile.ZipInfo(name, date_time=(2026, 8, 16, 0, 0, 0))
    info.create_system = 3
    info.external_attr = mode << 16
    return info, data


def archive(members) -> bytes:
    buffer = io.BytesIO()
    with warnings.catch_warnings():
        warnings.simplefilter("ignore")  # zipfile warns on the duplicate-member fixture
        with zipfile.ZipFile(buffer, "w", zipfile.ZIP_DEFLATED) as zf:
            for info, data in members:
                zf.writestr(info, data)
    return buffer.getvalue()


def release(z3_text: str = FAKE_Z3, stem: str = STEM) -> bytes:
    """A release-shaped zip: one top directory, bin/z3 mode 0755, two data files."""
    return archive([
        member(f"{stem}/LICENSE.txt", b"MIT\n"),
        member(f"{stem}/bin/z3", z3_text.encode(), 0o100755),
        member(f"{stem}/include/z3.h", b"/* z3 */\n"),
    ])


def pin_text(asset_bytes: bytes, bin_bytes: bytes = FAKE_Z3.encode(), stem: str = STEM, extra: str = "",
             rows=ROW_KEYS) -> str:
    """A pin whose darwin_arm64 row is the given archive; the other rows are well formed."""
    lines = [
        "# a fabricated pin",
        f"Z3_VERSION={VERSION}",
        f"Z3_RELEASE_URL=https://example.invalid/releases/download/z3-{VERSION}",
        "Z3_REFERENCE_ROW=darwin_arm64",
        "Z3_ROWS=" + ",".join(rows),
    ]
    for index, key in enumerate(rows):
        if key == "darwin_arm64":
            asset, size, asset_sha, bin_sha = stem + ".zip", len(asset_bytes), sha(asset_bytes), sha(bin_bytes)
        else:
            asset, size = f"z3-{VERSION}-{key}.zip", 1000 + index
            asset_sha, bin_sha = f"{index:x}" * 64, f"{index + 5:x}" * 64
        lines += [f"Z3_ASSET_{key}={asset}", f"Z3_ASSET_SIZE_{key}={size}",
                  f"Z3_ASSET_SHA256_{key}={asset_sha}", f"Z3_BIN_SHA256_{key}={bin_sha}"]
    return "\n".join(lines) + "\n" + extra


class Server:
    """An injected fetch: serves one payload and counts the bytes handed out."""

    def __init__(self, payload: bytes) -> None:
        self.payload = payload
        self.urls = []
        self.served = 0

    def __call__(self, url: str):
        self.urls.append(url)
        server = self

        class Response(io.BytesIO):
            def read(self, n: int = -1) -> bytes:
                data = super().read(n)
                server.served += len(data)
                return data

        return Response(self.payload)


def refuse(_url: str):
    raise AssertionError("fetch must not be called")


def write_bits(root: str):
    """Every path under root (root included) that has any write bit set."""
    found = []
    for directory, dirs, files in os.walk(root):
        for path in [directory] + [os.path.join(directory, f) for f in files]:
            if os.lstat(path).st_mode & 0o222:
                found.append(path)
    return found


class CacheCase(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.root = os.path.join(self._tmp.name, "cache", "ay-z3")
        self.payload = release()
        self.pin = zr.parse_pin(pin_text(self.payload), "<test>")
        self.row = self.pin.row("darwin_arm64")

    def tearDown(self) -> None:
        # The provisioned tree is read-only by design; make it removable.
        subprocess.run(["chmod", "-R", "u+w", self._tmp.name], check=False)
        self._tmp.cleanup()

    def provision(self, fetch, pin=None):
        return zr.provision(root=self.root, key="darwin_arm64", fetch=fetch, pin=pin or self.pin)

    def leftovers(self):
        if not os.path.isdir(self.root):
            return []
        return sorted(name for name in os.listdir(self.root))


class PinTests(unittest.TestCase):
    """Z1: the checked-in pin parses, and each malformed pin is refused by name."""

    def test_checked_in_pin_is_well_formed(self) -> None:
        pin = zr.load_pin()
        self.assertEqual(pin.source, os.path.join(REPO, "ci", "z3.pin"))
        self.assertRegex(pin.version, r"^\d+\.\d+\.\d+$")
        self.assertTrue(pin.release_url.startswith("https://"))
        self.assertTrue(pin.release_url.endswith("/z3-" + pin.version))
        self.assertIn(pin.reference_row, [row.key for row in pin.rows])
        self.assertEqual(sorted(row.key for row in pin.rows), sorted(ROW_KEYS))
        for row in pin.rows:
            with self.subTest(row=row.key):
                self.assertRegex(row.asset_sha256, r"^[0-9a-f]{64}$")
                self.assertRegex(row.bin_sha256, r"^[0-9a-f]{64}$")
                self.assertIn(pin.version, row.asset)
                self.assertTrue(row.asset.endswith(".zip"))
                self.assertGreater(row.size, 0)
                self.assertEqual(pin.url(row), pin.release_url + "/" + row.asset)
        # No two rows share bytes: a sha names exactly one row.
        self.assertEqual(len({row.bin_sha256 for row in pin.rows}), len(pin.rows))
        self.assertEqual(len({row.asset_sha256 for row in pin.rows}), len(pin.rows))

    def test_print_pin_round_trips(self) -> None:
        pin = zr.load_pin()
        out = io.StringIO()
        with redirect_stdout(out):
            self.assertEqual(zr.main(["--print-pin"]), 0)
        self.assertEqual(zr.parse_pin(out.getvalue(), "<printed>")._replace(source=pin.source), pin)

    def test_explicit_audit_pin_does_not_replace_default(self) -> None:
        original = zr.load_pin()
        with tempfile.TemporaryDirectory() as directory:
            path = os.path.join(directory, "audit.pin")
            text = original.render().replace(original.version, "99.8.7")
            with open(path, "w") as stream:
                stream.write(text)
            out = io.StringIO()
            with redirect_stdout(out):
                self.assertEqual(zr.main(["--pin", path, "--print-pin"]), 0)
            self.assertEqual(zr.parse_pin(out.getvalue(), path).version, "99.8.7")
        self.assertEqual(zr.load_pin(), original)

    def test_missing_explicit_pin_fails_without_default_fallback(self) -> None:
        with tempfile.TemporaryDirectory() as directory, redirect_stderr(io.StringIO()):
            self.assertEqual(zr.main(["--pin", os.path.join(directory, "absent"), "--path"]), 2)

    def test_fabricated_pins_are_refused(self) -> None:
        good = pin_text(release())
        zr.parse_pin(good, "<control>")  # the control parses
        sha_line = next(line for line in good.splitlines() if line.startswith("Z3_BIN_SHA256_darwin_arm64="))
        size_line = next(line for line in good.splitlines() if line.startswith("Z3_ASSET_SIZE_darwin_x86_64="))
        cases = {
            "space after =": good.replace(f"Z3_VERSION={VERSION}", f"Z3_VERSION= {VERSION}"),
            "trailing space": good.replace(f"Z3_VERSION={VERSION}\n", f"Z3_VERSION={VERSION} \n"),
            "space in key": good.replace("Z3_REFERENCE_ROW=", "Z3_REFERENCE_ROW ="),
            "double quotes": good.replace(f"Z3_VERSION={VERSION}", f'Z3_VERSION="{VERSION}"'),
            "single quotes": good.replace(f"Z3_VERSION={VERSION}", f"Z3_VERSION='{VERSION}'"),
            "expansion": good.replace("Z3_REFERENCE_ROW=darwin_arm64", "Z3_REFERENCE_ROW=$ROW"),
            "duplicate key": good + "Z3_VERSION=9.9.9\n",
            "duplicate same value": good + f"Z3_VERSION={VERSION}\n",
            "unknown key": good + "Z3_MIRROR=https://example.invalid\n",
            "Z3_TAG": good + f"Z3_TAG=z3-{VERSION}\n",
            "Z3_SOURCE_COMMIT": good + "Z3_SOURCE_COMMIT=" + "a" * 40 + "\n",
            "short sha": good.replace(sha_line, sha_line[:-1]),
            "uppercase sha": good.replace(sha_line, sha_line.split("=")[0] + "=" + sha_line.split("=")[1].upper()),
            "zero size": good.replace(size_line, "Z3_ASSET_SIZE_darwin_x86_64=0"),
            "signed size": good.replace(size_line, "Z3_ASSET_SIZE_darwin_x86_64=+5"),
            "row missing a key": "\n".join(line for line in good.splitlines()
                                           if not line.startswith("Z3_ASSET_SHA256_linux_aarch64=")) + "\n",
            "orphan row key": good + "Z3_ASSET_SIZE_freebsd_x86_64=10\n",
            "reference row not listed": good.replace("Z3_REFERENCE_ROW=darwin_arm64", "Z3_REFERENCE_ROW=freebsd_x86_64"),
            "duplicate row": good.replace("Z3_ROWS=darwin_arm64,", "Z3_ROWS=darwin_arm64,darwin_arm64,"),
            "http url": good.replace("https://example.invalid", "http://example.invalid"),
            "url not the tag": good.replace(f"download/z3-{VERSION}", "download/z3-9.9.9"),
            "asset without the version": good.replace(f"Z3_ASSET_darwin_x86_64=z3-{VERSION}-", "Z3_ASSET_darwin_x86_64=z3-"),
            "asset not a zip": good.replace(f"Z3_ASSET_darwin_x86_64=z3-{VERSION}-darwin_x86_64.zip",
                                            f"Z3_ASSET_darwin_x86_64=z3-{VERSION}-darwin_x86_64.tar.gz"),
            "asset with a directory": good.replace(f"Z3_ASSET_darwin_x86_64=z3-{VERSION}",
                                                   f"Z3_ASSET_darwin_x86_64=sub/z3-{VERSION}"),
            "not KEY=VALUE": good + "Z3_VERSION\n",
            "missing version": "\n".join(line for line in good.splitlines()
                                         if not line.startswith("Z3_VERSION=")) + "\n",
        }
        for name, text in cases.items():
            with self.subTest(name):
                with self.assertRaises(zr.PinError) as caught:
                    zr.parse_pin(text, "<fabricated>")
                self.assertIn("<fabricated>", str(caught.exception))


class ProvisionTests(CacheCase):
    def test_provision_installs_the_verified_tree_read_only_and_is_idempotent(self) -> None:
        """Z2."""
        server = Server(self.payload)
        path = self.provision(server)
        entry = os.path.join(self.root, sha(self.payload))
        self.assertEqual(path, os.path.join(entry, STEM, "bin", "z3"))
        self.assertEqual(server.urls, [self.pin.release_url + "/" + STEM + ".zip"])
        with open(path, "rb") as handle:
            self.assertEqual(sha(handle.read()), self.row.bin_sha256)
        self.assertEqual(stat.S_IMODE(os.stat(path).st_mode), 0o555)
        self.assertEqual(stat.S_IMODE(os.stat(os.path.join(entry, STEM, "LICENSE.txt")).st_mode), 0o444)
        self.assertEqual(write_bits(entry), [])
        archives = [os.path.join(d, f) for d, _, fs in os.walk(self.root) for f in fs if f.endswith(".zip")]
        self.assertEqual(archives, [], "the archive must not survive inside the cache")
        self.assertEqual(self.leftovers(), [sha(self.payload)])
        # Idempotent: a second provision verifies the entry and never fetches.
        self.assertEqual(self.provision(refuse), path)
        self.assertEqual(zr.resolve_pinned(root=self.root, key="darwin_arm64", pin=self.pin), path)

    def test_archive_that_differs_from_the_pin_installs_nothing(self) -> None:
        """Z3."""
        flipped = self.payload[:-1] + bytes([self.payload[-1] ^ 1])  # same size, other bytes
        for other in (flipped, self.payload[:-1]):
            with self.subTest(size=len(other)):
                with self.assertRaises(zr.ArchiveMismatch) as caught:
                    self.provision(Server(other))
                self.assertIn(sha(other), str(caught.exception))
                self.assertIn(self.row.asset_sha256, str(caught.exception))
                self.assertEqual(self.leftovers(), [], "no entry, .tmp-* or .dl-* may remain")
        with self.assertRaises(zr.NotProvisioned):
            zr.resolve_pinned(root=self.root, key="darwin_arm64", pin=self.pin)

    def test_an_oversized_download_is_cut_at_the_pinned_size(self) -> None:
        """Z4."""
        server = Server(self.payload + b"\0" * (3 * zr.CHUNK))
        with self.assertRaises(zr.SizeExceeded):
            self.provision(server)
        self.assertLessEqual(server.served, self.row.size + zr.CHUNK)
        self.assertEqual(self.leftovers(), [])

    def test_a_binary_that_differs_from_the_pin_is_refused_from_a_matching_archive(self) -> None:
        """Z5."""
        pin = zr.parse_pin(pin_text(self.payload, bin_bytes=b"other bytes"), "<test>")
        with self.assertRaises(zr.BinaryMismatch) as caught:
            self.provision(Server(self.payload), pin)
        self.assertIn(sha(FAKE_Z3.encode()), str(caught.exception))
        self.assertIn(sha(b"other bytes"), str(caught.exception))
        self.assertEqual(self.leftovers(), [])

    def test_a_tampered_entry_is_refused_and_never_overwritten(self) -> None:
        """Z6."""
        path = self.provision(Server(self.payload))
        entry = os.path.dirname(os.path.dirname(os.path.dirname(path)))
        os.chmod(path, 0o755)
        with open(path, "w") as handle:
            handle.write("#!/bin/sh\necho tampered\n")
        tampered = sha(b"#!/bin/sh\necho tampered\n")
        for attempt in (lambda: zr.resolve_pinned(root=self.root, key="darwin_arm64", pin=self.pin),
                        lambda: self.provision(refuse)):
            with self.assertRaises(zr.Tampered) as caught:
                attempt()
            message = str(caught.exception)
            self.assertIn(tampered, message)
            self.assertIn(self.row.bin_sha256, message)
            self.assertIn(f"chmod -R u+w {entry} && rm -rf {entry}", message)
        with open(path) as handle:
            self.assertEqual(handle.read(), "#!/bin/sh\necho tampered\n")
        # A missing bin/z3 inside a present entry is tampering too, not absence.
        os.chmod(os.path.dirname(path), 0o755)
        os.unlink(path)
        with self.assertRaises(zr.Tampered):
            zr.resolve_pinned(root=self.root, key="darwin_arm64", pin=self.pin)

    def test_members_stay_inside_one_top_directory(self) -> None:
        """Z7."""
        z3 = FAKE_Z3.encode()
        bad = {
            "parent": [member(f"{STEM}/bin/z3", z3, 0o100755), member("../x", b"x")],
            "nested parent": [member(f"{STEM}/bin/z3", z3, 0o100755), member(f"{STEM}/../../x", b"x")],
            "absolute": [member(f"{STEM}/bin/z3", z3, 0o100755), member("/abs/x", b"x")],
            "two top directories": [member(f"{STEM}/bin/z3", z3, 0o100755), member("other/x", b"x")],
            "top-level file": [member(f"{STEM}/bin/z3", z3, 0o100755), member("README", b"x")],
            "symlink": [member(f"{STEM}/bin/z3", z3, 0o100755),
                        member(f"{STEM}/bin/link", b"/etc/passwd", 0o120777)],
            "directory entry": [member(f"{STEM}/bin/z3", z3, 0o100755), member(f"{STEM}/bin/", b"", 0o040755)],
            "no unix mode": [member(f"{STEM}/bin/z3", z3, 0)],
            "duplicate member": [member(f"{STEM}/bin/z3", z3, 0o100755), member(f"{STEM}/bin/z3", z3, 0o100755)],
            "no bin/z3": [member(f"{STEM}/LICENSE.txt", b"MIT\n")],
        }
        for name, members in bad.items():
            with self.subTest(name):
                payload = archive(members)
                pin = zr.parse_pin(pin_text(payload), "<test>")
                with self.assertRaises(zr.BadMember):
                    self.provision(Server(payload), pin)
                self.assertEqual(self.leftovers(), [])
                self.assertFalse(os.path.exists(os.path.join(self._tmp.name, "x")))
                self.assertFalse(os.path.exists(os.path.join(self._tmp.name, "cache", "x")))

    def test_a_racer_that_published_first_is_verified_and_ours_discarded(self) -> None:
        racer = []

        def racing_fetch(url):
            # Another provisioner publishes the entry while ours is downloading.
            if not racer:
                racer.append(self.provision(Server(self.payload)))
            return Server(self.payload)(url)

        self.assertEqual(self.provision(racing_fetch), racer[0])
        self.assertEqual(self.leftovers(), [sha(self.payload)])
        self.assertEqual(zr.resolve_pinned(root=self.root, key="darwin_arm64", pin=self.pin), racer[0])


class HostRowTests(unittest.TestCase):
    """Z8."""

    def test_the_four_platforms_map_and_others_are_refused(self) -> None:
        pin = zr.parse_pin(pin_text(release()), "<test>")
        expected = {("Darwin", "arm64"): "darwin_arm64", ("Darwin", "x86_64"): "darwin_x86_64",
                    ("Linux", "x86_64"): "linux_x86_64", ("Linux", "aarch64"): "linux_aarch64"}
        for (system, machine), key in expected.items():
            with self.subTest(system=system, machine=machine), \
                    mock.patch.object(zr.platform, "system", return_value=system), \
                    mock.patch.object(zr.platform, "machine", return_value=machine):
                self.assertEqual(zr.host_row_key(pin), key)
        for system, machine in (("Linux", "riscv64"), ("Windows", "AMD64"), ("Darwin", "arm64e"),
                                ("Linux", "arm64"), ("FreeBSD", "amd64")):
            with self.subTest(system=system, machine=machine), \
                    mock.patch.object(zr.platform, "system", return_value=system), \
                    mock.patch.object(zr.platform, "machine", return_value=machine):
                with self.assertRaises(zr.NoRow) as caught:
                    zr.host_row_key(pin)
                for key in ROW_KEYS:
                    self.assertIn(key, str(caught.exception))
        # A platform the code knows but the pin does not list is refused too.
        narrow = zr.parse_pin(pin_text(release(), rows=ROW_KEYS[:3]), "<narrow>")
        with mock.patch.object(zr.platform, "system", return_value="Linux"), \
                mock.patch.object(zr.platform, "machine", return_value="aarch64"):
            with self.assertRaises(zr.NoRow):
                zr.host_row_key(narrow)

    def test_cache_root_is_explicit_then_xdg_then_home(self) -> None:
        self.assertEqual(zr.cache_root("/explicit/dir"), "/explicit/dir")
        with mock.patch.dict(os.environ, {"XDG_CACHE_HOME": "/xdg", "HOME": "/home/u"}):
            self.assertEqual(zr.cache_root(), "/xdg/ay-z3")
        with mock.patch.dict(os.environ, {"XDG_CACHE_HOME": "", "HOME": "/home/u"}):
            self.assertEqual(zr.cache_root(), "/home/u/.cache/ay-z3")
        env = dict(os.environ, HOME="/home/u")
        env.pop("XDG_CACHE_HOME", None)
        with mock.patch.dict(os.environ, env, clear=True):
            self.assertEqual(zr.cache_root(), "/home/u/.cache/ay-z3")


class CliTests(CacheCase):
    """Z9."""

    def test_path_is_offline_and_exits_setup_when_not_provisioned(self) -> None:
        out, err = io.StringIO(), io.StringIO()
        with mock.patch.object(zr.urllib.request, "urlopen", side_effect=AssertionError("network")) as urlopen, \
                mock.patch.object(zr.platform, "system", return_value="Darwin"), \
                mock.patch.object(zr.platform, "machine", return_value="arm64"), \
                redirect_stdout(out), redirect_stderr(err):
            self.assertEqual(zr.main(["--path", "--cache", self.root]), 2)
            self.assertEqual(zr.main(["--verify", "--cache", self.root]), 2)
        urlopen.assert_not_called()
        self.assertEqual(out.getvalue(), "")
        self.assertIn("--provision", err.getvalue())
        self.assertEqual(self.leftovers(), [])

    def test_path_prints_the_provisioned_binary(self) -> None:
        path = self.provision(Server(self.payload))
        out = io.StringIO()
        with mock.patch.object(zr, "load_pin", return_value=self.pin), redirect_stdout(out):
            self.assertEqual(zr.main(["--path", "--platform", "darwin_arm64", "--cache", self.root]), 0)
            self.assertEqual(zr.main(["--verify", "--platform", "darwin_arm64", "--cache", self.root]), 0)
        self.assertEqual(out.getvalue().splitlines()[0], path)


if __name__ == "__main__":
    unittest.main()
