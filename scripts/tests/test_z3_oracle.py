# ay-script: z3-oracle-tests
"""Tests for scripts/_z3_oracle.py against fake z3 programs written to a
temporary directory: never the real z3, never the ambient PATH or Z3_PATH.

The cases mirror crates/ay-sys/src/z3_oracle_tests.rs, so the Python and Rust
resolvers are held to the same rule. Runnable via:

    python3 -m unittest scripts.tests.test_z3_oracle
"""
import os
import sys
import tempfile
import unittest
from unittest import mock

SCRIPTS_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, SCRIPTS_DIR)

import _z3_oracle as zo  # noqa: E402

REAL = (
    "#!/bin/sh\ncase \"$1\" in\n"
    "  --version) echo '{banner}'; exit 0;;\n"
    "  --z3-mode) echo 'Error: invalid command line option: --z3-mode'; exit 109;;\n"
    "esac\necho sat\n"
)
REFUSING = "#!/bin/sh\necho \"'z3' is refused by name\" >&2\nexit 2\n"
SILENT = "#!/bin/sh\nexit 0\n"
IMPOSTOR = "#!/bin/sh\necho 'Z3 version 5.1.0 - 64 bit'\nexit 0\n"
STUB = (
    "#!/bin/sh\n" + zo.REROUTE_STUB_SIGNATURE + "\ntouch '{sentinel}'\n"
    "echo 'Z3 version 5.1.0 - 64 bit'\nexit 0\n"
)


class FakePath:
    def __init__(self, root: str) -> None:
        self.root = root
        self.sentinel = os.path.join(root, "stub-was-executed")

    def install(self, directory: str, script: str) -> str:
        path = os.path.join(self.root, directory)
        os.makedirs(path, exist_ok=True)
        z3 = os.path.join(path, "z3")
        with open(z3, "w") as handle:
            handle.write(script.replace("{sentinel}", self.sentinel))
        os.chmod(z3, 0o755)
        return z3

    def mark_reroute(self, directory: str) -> None:
        with open(os.path.join(self.root, directory, zo.REROUTE_DIR_MARKER), "w") as handle:
            handle.write("aterm\n")

    def path(self, *directories: str) -> str:
        return os.pathsep.join(os.path.join(self.root, d) for d in directories)


class Z3OracleTests(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.fake = FakePath(self._tmp.name)

    def tearDown(self) -> None:
        self._tmp.cleanup()

    def test_banner_identifies_only_a_real_z3(self) -> None:
        self.assertEqual(
            zo.z3_version_banner(0, "Z3 version 4.16.0 - 64 bit\n"), "Z3 version 4.16.0 - 64 bit"
        )
        self.assertIsNone(zo.z3_version_banner(2, ""))
        self.assertIsNone(zo.z3_version_banner(1, "Z3 version 4.16.0 - 64 bit\n"))
        self.assertIsNone(zo.z3_version_banner(0, ""))
        self.assertIsNone(zo.z3_version_banner(0, "cvc5 version 1.0.8\n"))
        self.assertEqual(zo.parse_banner_version("Z3 version 4.8.12 - 64 bit"), (4, 8, 12))
        self.assertEqual(zo.parse_banner_version("Z3 version 4.15 - 64 bit"), (4, 15, 0))
        self.assertIsNone(zo.parse_banner_version("not z3"))

    def test_refusing_stub_directory_ahead_of_z3_resolves_to_z3_by_path(self) -> None:
        stub = self.fake.install("reroute", REFUSING)
        self.fake.mark_reroute("reroute")
        real = self.fake.install("real", REAL.format(banner="Z3 version 4.16.0 - 64 bit"))
        oracle = zo.resolve_z3(None, self.fake.path("reroute", "real"))
        self.assertEqual(oracle.path, real)
        self.assertEqual(oracle.banner, "Z3 version 4.16.0 - 64 bit")
        self.assertEqual(oracle.version(), (4, 16, 0))
        self.assertEqual(oracle.source, "PATH")
        self.assertEqual([p.path for p in oracle.passed_over], [stub])
        self.assertIn(real, oracle.identity())
        self.assertIn(zo.REROUTE_DIR_MARKER, oracle.identity())

    def test_stub_without_marker_is_skipped_by_signature_and_never_run(self) -> None:
        stub = self.fake.install("unmarked", STUB)
        real = self.fake.install("real", REAL.format(banner="Z3 version 4.16.0 - 64 bit"))
        oracle = zo.resolve_z3(None, self.fake.path("unmarked", "real"))
        self.assertEqual(oracle.path, real)
        self.assertEqual(oracle.passed_over, (zo.PassedOver(stub, "aterm reroute stub"),))
        self.assertFalse(os.path.exists(self.fake.sentinel), "the resolver ran a reroute stub")

    def test_refusing_program_without_markers_is_rejected_and_passed_over(self) -> None:
        refusing = self.fake.install("refusing", REFUSING)
        real = self.fake.install("real", REAL.format(banner="Z3 version 4.8.12 - 64 bit"))
        oracle = zo.resolve_z3(None, self.fake.path("refusing", "real"))
        self.assertEqual(oracle.path, real)
        self.assertEqual(oracle.passed_over[0].path, refusing)
        self.assertIn("did not print a Z3 banner", oracle.passed_over[0].reason)

    def test_program_exiting_zero_without_banner_is_not_z3(self) -> None:
        silent = self.fake.install("silent", SILENT)
        with self.assertRaises(zo.Z3Unavailable) as caught:
            zo.resolve_z3(None, self.fake.path("silent"))
        self.assertFalse(caught.exception.misconfigured)
        self.assertEqual([p.path for p in caught.exception.passed_over], [silent])

    def test_ay_drop_in_answering_the_negative_control_is_refused(self) -> None:
        self.fake.install("impostor", IMPOSTOR)
        with self.assertRaises(zo.Z3Unavailable) as caught:
            zo.resolve_z3(None, self.fake.path("impostor"))
        self.assertIn("AY drop-in", caught.exception.passed_over[0].reason)

    def test_z3_path_wins_and_a_wrong_one_never_falls_back(self) -> None:
        self.fake.install("on-path", REAL.format(banner="Z3 version 4.16.0 - 64 bit"))
        configured = self.fake.install("configured", REAL.format(banner="Z3 version 4.8.12 - 64 bit"))
        search = self.fake.path("on-path")
        oracle = zo.resolve_z3(configured, search)
        self.assertEqual((oracle.path, oracle.source), (configured, "Z3_PATH"))
        self.assertEqual(zo.resolve_z3("", search).source, "PATH")
        impostor = self.fake.install("impostor", IMPOSTOR)
        stub = self.fake.install("stub", STUB)
        for wrong in ("z3", impostor, stub, os.path.join(self._tmp.name, "missing", "z3")):
            with self.assertRaises(zo.Z3Unavailable) as caught:
                zo.resolve_z3(wrong, search)
            self.assertTrue(caught.exception.misconfigured, wrong)
        self.assertFalse(os.path.exists(self.fake.sentinel), "Z3_PATH ran a reroute stub")

    def test_empty_relative_and_non_executable_entries_are_skipped(self) -> None:
        self.fake.install("relative", REAL.format(banner="Z3 version 4.16.0 - 64 bit"))
        plain = os.path.join(self._tmp.name, "plain")
        os.makedirs(plain)
        with open(os.path.join(plain, "z3"), "w") as handle:
            handle.write("#!/bin/sh\necho 'Z3 version 4.16.0 - 64 bit'\n")
        os.chmod(os.path.join(plain, "z3"), 0o644)
        real = self.fake.install("real", REAL.format(banner="Z3 version 4.16.0 - 64 bit"))
        relative = os.path.relpath(os.path.join(self._tmp.name, "relative"))
        self.assertTrue(os.path.isfile(os.path.join(relative, "z3")))
        search = os.pathsep.join(["", relative, plain, os.path.join(self._tmp.name, "real")])
        oracle = zo.resolve_z3(None, search)
        self.assertEqual(oracle.path, real)
        self.assertEqual(oracle.passed_over, ())

    def test_nothing_found_and_the_cached_process_oracle(self) -> None:
        os.makedirs(os.path.join(self._tmp.name, "empty"))
        with self.assertRaises(zo.Z3Unavailable):
            zo.resolve_z3(None, self.fake.path("empty"))
        with self.assertRaises(zo.Z3Unavailable):
            zo.resolve_z3(None, None)
        real = self.fake.install("real", REAL.format(banner="Z3 version 4.16.0 - 64 bit"))
        env = {"PATH": self.fake.path("real")}
        with mock.patch.dict(os.environ, env, clear=True), mock.patch.object(zo, "_RESOLVED", None):
            self.assertEqual(zo.find_z3().path, real)
            self.assertEqual(zo.resolve_z3_spelling("z3").path, real)
        with mock.patch.dict(os.environ, {"PATH": self.fake.path("empty")}, clear=True), \
                mock.patch.object(zo, "_RESOLVED", None):
            self.assertIsNone(zo.find_z3())
        with mock.patch.dict(os.environ, {"Z3_PATH": "z3", "PATH": env["PATH"]}, clear=True), \
                mock.patch.object(zo, "_RESOLVED", None):
            with self.assertRaises(zo.Z3Unavailable):
                zo.find_z3()


if __name__ == "__main__":
    unittest.main()
