#!/usr/bin/env python3
# ay-script: sat-soundness-gate-resource-tests
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0

from __future__ import annotations

import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import textwrap
import unittest


ROOT = Path(__file__).resolve().parents[2]
GATE = ROOT / "scripts" / "ci" / "sat_soundness_gate.sh"
RESOURCE_ENV = (
    "AY_OOM_GUARD_PARENT_LEASE",
    "AY_CONTINUOUS_JOBS",
    "AY_CONTINUOUS_MEMLIMIT_MB",
    "AY_CONTINUOUS_HEADROOM_MB",
    "MEMLIMIT",
    "NBCORE",
)


class SatSoundnessGateResourceTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.repo = Path(self.temporary.name)
        scripts = self.repo / "scripts"
        (scripts / "ci").mkdir(parents=True)
        shutil.copy2(GATE, scripts / "ci" / GATE.name)
        canary = self.repo / "benchmarks" / "sat" / "canary"
        canary.mkdir(parents=True)
        (canary / "tiny_sat.cnf").write_text("p cnf 1 1\n1 0\n")
        (canary / "tiny_unsat.cnf").write_text(
            "p cnf 1 2\n1 0\n-1 0\n"
        )
        self.trace = self.repo / "trace.log"
        self.marker = self.repo / "lease.marker"
        self._write_fake_guard(scripts / "_oom_guard.py")
        self.solver = self.repo / "fake-ay"
        self._write_fake_solver(self.solver)

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def _write_fake_guard(self, path: Path) -> None:
        path.write_text(
            textwrap.dedent(
                """\
                import os
                from pathlib import Path
                import sys

                trace = Path(os.environ["FAKE_TRACE"])
                marker = Path(os.environ["FAKE_LEASE_MARKER"])

                def record(value):
                    with trace.open("a", encoding="utf-8") as handle:
                        handle.write(value + "\\n")

                if len(sys.argv) < 2:
                    raise SystemExit(90)
                if sys.argv[1] == "lease":
                    marker.write_text(str(os.getpid()), encoding="utf-8")
                    record("lease-start")
                    print("AY_OOM_HARNESS_LEASE_READY_V1", flush=True)
                    try:
                        while sys.stdin.buffer.read(8192):
                            pass
                    finally:
                        record("lease-end")
                        marker.unlink(missing_ok=True)
                    raise SystemExit(0)
                if sys.argv[1] == "plan":
                    record(
                        "plan:"
                        + " ".join(sys.argv[2:])
                        + f":lease_alive={marker.is_file()}"
                    )
                    if (
                        sys.argv[2:4] != ["--jobs", "1"]
                        or "--warn-concurrent-build" not in sys.argv
                        or not marker.is_file()
                    ):
                        raise SystemExit(91)
                    print("PLAN_JOBS=1")
                    print("PLAN_MEMLIMIT_MB=4096")
                    print("PLAN_NBCORE=4")
                    print("PLAN_HEADROOM_MB=16384")
                    raise SystemExit(0)
                record("unexpected:" + " ".join(sys.argv[1:]))
                raise SystemExit(92)
                """
            )
        )

    def _write_fake_solver(self, path: Path) -> None:
        path.write_text(
            textwrap.dedent(
                """\
                #!/usr/bin/env python3
                import json
                import os
                from pathlib import Path
                import sys

                argv = sys.argv[1:]
                marker = Path(os.environ["FAKE_LEASE_MARKER"])
                if os.environ.get("EXPECT_LEASE_ALIVE") == "1" and not marker.is_file():
                    raise SystemExit(91)
                try:
                    memory = argv[argv.index("--memory") + 1]
                except (ValueError, IndexError):
                    raise SystemExit(92)
                row = {
                    "path": argv[0],
                    "memory_arg": memory,
                    "continuous_memlimit": os.environ.get(
                        "AY_CONTINUOUS_MEMLIMIT_MB"
                    ),
                    "memlimit": os.environ.get("MEMLIMIT"),
                    "nbcore": os.environ.get("NBCORE"),
                    "jobs": os.environ.get("AY_CONTINUOUS_JOBS"),
                    "headroom": os.environ.get("AY_CONTINUOUS_HEADROOM_MB"),
                    "lease_alive": marker.is_file(),
                }
                with Path(os.environ["FAKE_TRACE"]).open(
                    "a", encoding="utf-8"
                ) as handle:
                    handle.write("solver:" + json.dumps(row, sort_keys=True) + "\\n")
                raise SystemExit(20 if "tiny_unsat" in argv[0] else 10)
                """
            )
        )
        path.chmod(0o755)

    def _environment(self) -> dict[str, str]:
        env = os.environ.copy()
        for key in RESOURCE_ENV:
            env.pop(key, None)
        env.update(
            {
                "FAKE_TRACE": str(self.trace),
                "FAKE_LEASE_MARKER": str(self.marker),
                "EXPECT_LEASE_ALIVE": "1",
            }
        )
        return env

    def _run(self, env: dict[str, str]) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [
                "bash",
                str(self.repo / "scripts" / "ci" / GATE.name),
                str(self.solver),
                "drat",
                "5",
            ],
            cwd=self.repo,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=10,
            check=False,
        )

    def _solver_rows(self) -> list[dict[str, str | bool | None]]:
        return [
            json.loads(line.removeprefix("solver:"))
            for line in self.trace.read_text().splitlines()
            if line.startswith("solver:")
        ]

    def test_standalone_gate_holds_lease_and_enforces_planned_memory(self) -> None:
        completed = self._run(self._environment())
        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertIn(
            "RESOURCE_ENVELOPE_V1 requested_jobs=1 jobs=1 "
            "memlimit_mb_per_child=4096 nbcore_per_child=4 "
            "headroom_mb=16384 memory_enforcement=ay-main--memory "
            "lease=sidecar source=auto-plan",
            completed.stdout,
        )
        trace = self.trace.read_text().splitlines()
        self.assertEqual(trace[0], "lease-start")
        self.assertIn(
            "plan:--jobs 1 --label sat-soundness-gate "
            "--warn-concurrent-build:lease_alive=True",
            trace,
        )
        self.assertEqual(trace[-1], "lease-end")
        self.assertFalse(self.marker.exists())
        rows = self._solver_rows()
        self.assertEqual(len(rows), 2)
        for row in rows:
            self.assertEqual(row["memory_arg"], "4096")
            self.assertEqual(row["continuous_memlimit"], "4096")
            self.assertEqual(row["memlimit"], "4096")
            self.assertEqual(row["nbcore"], "4")
            self.assertEqual(row["jobs"], "1")
            self.assertEqual(row["headroom"], "16384")
            self.assertTrue(row["lease_alive"])

    def test_standalone_gate_keeps_stricter_caller_caps(self) -> None:
        env = self._environment()
        env.update({"MEMLIMIT": "3072", "NBCORE": "2"})
        completed = self._run(env)
        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertIn(
            "memlimit_mb_per_child=3072 nbcore_per_child=2 "
            "headroom_mb=16384 memory_enforcement=ay-main--memory "
            "lease=sidecar source=auto-plan-capped",
            completed.stdout,
        )
        for row in self._solver_rows():
            self.assertEqual(row["memory_arg"], "3072")
            self.assertEqual(row["memlimit"], "3072")
            self.assertEqual(row["nbcore"], "2")

    def test_parent_plan_is_reused_without_a_second_lease(self) -> None:
        self.marker.write_text("external-parent", encoding="utf-8")
        env = self._environment()
        env.update(
            {
                "AY_OOM_GUARD_PARENT_LEASE": "1",
                "AY_CONTINUOUS_JOBS": "1",
                "AY_CONTINUOUS_MEMLIMIT_MB": "3072",
                "AY_CONTINUOUS_HEADROOM_MB": "8192",
                "MEMLIMIT": "3072",
                "NBCORE": "3",
            }
        )
        completed = self._run(env)
        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertIn(
            "RESOURCE_ENVELOPE_V1 requested_jobs=1 jobs=1 "
            "memlimit_mb_per_child=3072 nbcore_per_child=3 "
            "headroom_mb=8192 memory_enforcement=ay-main--memory "
            "lease=parent-held source=parent-plan",
            completed.stdout,
        )
        trace = self.trace.read_text().splitlines()
        self.assertFalse(any(line.startswith(("lease-", "plan:")) for line in trace))
        self.assertTrue(self.marker.exists())
        for row in self._solver_rows():
            self.assertEqual(row["memory_arg"], "3072")
            self.assertEqual(row["memlimit"], "3072")
            self.assertEqual(row["nbcore"], "3")
            self.assertTrue(row["lease_alive"])

    def test_parent_plan_rejects_inconsistent_memory_values(self) -> None:
        self.marker.write_text("external-parent", encoding="utf-8")
        env = self._environment()
        env.update(
            {
                "AY_OOM_GUARD_PARENT_LEASE": "1",
                "AY_CONTINUOUS_JOBS": "1",
                "AY_CONTINUOUS_MEMLIMIT_MB": "3072",
                "AY_CONTINUOUS_HEADROOM_MB": "8192",
                "MEMLIMIT": "4096",
                "NBCORE": "3",
            }
        )
        completed = self._run(env)
        self.assertEqual(completed.returncode, 2)
        self.assertIn(
            "AY_CONTINUOUS_MEMLIMIT_MB and MEMLIMIT must match",
            completed.stderr,
        )
        self.assertFalse(self.trace.exists())


if __name__ == "__main__":
    unittest.main()
