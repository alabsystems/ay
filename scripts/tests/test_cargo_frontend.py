#!/usr/bin/env python3
"""scripts/lib/cargo_frontend.sh picks the Cargo-family frontend per host.

A script that ships in the public snapshot runs on two kinds of machine: an
ALab host, where Rust is the Trust toolchain's `targo` and a compiling command
must name a lane, and a public clone, which pins a stock toolchain and has no
`targo` at all. These tests drive the helper with recording stubs (never a
compiler) and hold the exported shell scripts to it: none of them may run
`targo` directly, which would break every public clone.
"""

from pathlib import Path
import re
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]
HELPER = ROOT / "scripts" / "lib" / "cargo_frontend.sh"

# Records its own name and argv. As `targo` it accepts `--unverified
# --version` (the discriminator) unless FAKE_STOCK is set, in which case it
# answers like stock Cargo installed under the `targo` name.
RECORDER = """#!/bin/bash
if [ "$1 $2" = "--unverified --version" ]; then
  if [ -n "${FAKE_STOCK:-}" ]; then
    echo "error: unexpected argument '--unverified' found" >&2
    exit 1
  fi
  echo "targo 1.99.0-dev (fake)"
  exit 0
fi
printf '%s' "$(basename "$0")" >> "$RECORD"
printf ' %s' "$@" >> "$RECORD"
printf '\\n' >> "$RECORD"
"""


class CargoFrontendTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix="ay-cargo-frontend-")
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        self.bin = self.root / "bin"
        self.bin.mkdir()
        self.record = self.root / "record"

    def plant(self, *names):
        for name in names:
            path = self.bin / name
            path.write_text(RECORDER)
            path.chmod(0o755)

    def run_helper(self, body, **environment):
        result = subprocess.run(
            ["/bin/bash", "-c", f'. "{HELPER}"\n{body}'],
            env={"PATH": f"{self.bin}:/usr/bin:/bin", "RECORD": str(self.record), **environment},
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        return result.stdout

    def recorded(self):
        return self.record.read_text().splitlines()

    def test_trust_host_names_the_unverified_lane_for_compiling_commands(self):
        self.plant("targo", "cargo")
        self.run_helper(
            "ay_cargo build --release -p ay\n"
            "ay_cargo test -p ay-milp --lib\n"
            "ay_cargo run -p ay -- gate solver\n"
            "ay_cargo metadata --no-deps --format-version 1\n"
        )
        self.assertEqual(
            self.recorded(),
            [
                "targo --unverified build --release -p ay",
                "targo --unverified test -p ay-milp --lib",
                "targo --unverified run -p ay -- gate solver",
                "targo metadata --no-deps --format-version 1",
            ],
        )

    def test_argv_form_serves_wrapper_commands(self):
        self.plant("targo", "cargo")
        out = self.run_helper(
            "printf '[%s]' $(ay_cargo_argv build); echo\n"
            "printf '[%s]' $(ay_cargo_argv metadata); echo\n"
            "exec $(ay_cargo_argv run) run -p ay\n"
        )
        self.assertEqual(out.splitlines(), ["[targo][--unverified]", "[targo]"])
        self.assertEqual(self.recorded(), ["targo --unverified run -p ay"])

    def test_public_host_without_targo_runs_plain_cargo(self):
        self.plant("cargo")
        self.run_helper("ay_cargo build --release -p ay\nay_cargo metadata --no-deps\n")
        self.assertEqual(self.recorded(), ["cargo build --release -p ay", "cargo metadata --no-deps"])

    def test_stock_cargo_under_the_targo_name_is_not_taken_for_targo(self):
        self.plant("targo", "cargo")
        self.run_helper("ay_cargo build -p ay\n", FAKE_STOCK="1")
        self.assertEqual(self.recorded(), ["cargo build -p ay"])


# Manifest-excluded (development-only) scripts may name targo directly; every
# other shell script under scripts/ ships to public clones. A public clone has
# no publish/ directory, and every script in it is one that shipped.
def exported_shell_scripts():
    excluded = set()
    manifest = ROOT / "publish" / "manifest.txt"
    for line in manifest.read_text().splitlines() if manifest.is_file() else []:
        line = line.strip()
        if line.startswith("!scripts/"):
            excluded.add(line[1:].rstrip("/"))
    for path in sorted((ROOT / "scripts").rglob("*")):
        rel = path.relative_to(ROOT).as_posix()
        if not path.is_file() or any(rel == e or rel.startswith(e + "/") for e in excluded):
            continue
        head = path.read_bytes()[:64]
        if path.suffix in (".sh", ".bash", ".zsh") or re.match(rb"#!.*\b(ba|z)?sh\b", head):
            yield rel, path


# `targo` in command position: at the start of a line, after a separator, or
# after exec/then/do/`nice -n N`. Echoed hints are prose, not commands.
DIRECT_TARGO = re.compile(r"(^|[;&|(!]\s*|\b(exec|then|do)\s+|\bnice\s+-n\s+\d+\s+)targo\s")


class ExportedScriptsTests(unittest.TestCase):
    def test_exported_shell_scripts_do_not_run_targo_directly(self):
        offenders = []
        scanned = 0
        for rel, path in exported_shell_scripts():
            scanned += 1
            for number, line in enumerate(path.read_text(errors="replace").splitlines(), 1):
                code = line.strip()
                if code.startswith("#") or re.match(r"(echo|printf|die|note|fail)\b", code):
                    continue
                # Quoted text is prose (a hint), and `NAME=(targo ...)` is a
                # program table chosen by the script's own discriminator.
                code = re.sub(r'"[^"]*"|\'[^\']*\'', '""', code)
                if re.match(r"[A-Za-z_]\w*=\(targo\b", code):
                    continue
                if DIRECT_TARGO.search(code):
                    offenders.append(f"{rel}:{number}: {code}")
        self.assertGreater(scanned, 0)
        self.assertEqual(offenders, [], "use ay_cargo from scripts/lib/cargo_frontend.sh")


if __name__ == "__main__":
    unittest.main()
