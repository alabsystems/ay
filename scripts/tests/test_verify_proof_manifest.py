#!/usr/bin/env python3
"""Certificate verification must happen OUTSIDE the solve budget -- and an
unverified certificate must never become a win.

These lock the contract that `~/ay-bench/bin/ay-proofmode` +
`scripts/verify_proof_manifest.py` replaced. The old wrapper ran `dsr-trim`
inline, inside the region `sweep.py` hard-kills at `timeout_s + 20`, so an
instance AY had already SOLVED was booked as a TIMEOUT whenever solve + check
crossed the kill line (8 rows in ~/ay-bench/proofmode-full400-aug25.json, all
ground-truth UNSAT). Moving the check out is only safe if the honest-score rule
moves WITH it, so the cases below are mostly about what must NOT be counted.
"""
import glob
import json
import os
import subprocess
import sys
import tempfile
import unittest

SCRIPTS = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, SCRIPTS)
import verify_proof_manifest as vpm  # noqa: E402

ACCEPTING_CHECKER = "#!/bin/sh\necho 's VERIFIED UNSAT'\nexit 0\n"
REJECTING_CHECKER = "#!/bin/sh\necho 's NOT VERIFIED'\nexit 1\n"
HANGING_CHECKER = "#!/bin/sh\nsleep 300\n"


class ManifestFixture(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = self.tmp.name
        self.addCleanup(self.tmp.cleanup)
        self.manifest = os.path.join(self.root, "manifest")
        vpm.ensure_dirs(self.manifest)

    def checker(self, body, name="checker.sh"):
        path = os.path.join(self.root, name)
        with open(path, "w") as fh:
            fh.write(body)
        os.chmod(path, 0o755)
        return path

    def enqueue(self, token, cnf_text="p cnf 1 2\n1 0\n-1 0\n", proof_text="0\n",
                ay_wall_ms=1234, proof_bytes=None):
        cnf = os.path.join(self.root, f"{token}.cnf")
        proof = os.path.join(self.root, f"{token}.drat")
        with open(cnf, "w") as fh:
            fh.write(cnf_text)
        with open(proof, "w") as fh:
            fh.write(proof_text)
        row = {"token": token, "cnf": cnf, "proof": proof, "status": "pending",
               "ay_rc": 20, "ay_wall_ms": ay_wall_ms,
               "proof_bytes": proof_bytes if proof_bytes is not None
               else os.path.getsize(proof)}
        with open(os.path.join(self.manifest, "pending", f"{token}.json"), "w") as fh:
            json.dump(row, fh)
        return cnf, proof

    def sweep_json(self, results, timeout_s=300.0, configuration="competition"):
        path = os.path.join(self.root, "sweep.json")
        with open(path, "w") as fh:
            json.dump({"timeout_s": timeout_s, "solver_configuration": configuration,
                       "results": results}, fh)
        return path

    def drain(self, checker, timeout=30.0, jobs=1):
        args = vpm.main.__globals__["argparse"].Namespace(
            manifest=self.manifest, checker=checker, timeout=timeout, jobs=jobs,
            watch=0.0, poll=0.1, keep_proof=False, requeue_claimed=False)
        return vpm.cmd_drain(args)

    def score(self, sweep_path, out=None, config=None):
        args = vpm.main.__globals__["argparse"].Namespace(
            sweep=sweep_path, manifest=self.manifest, out=out, config=config)
        return vpm.cmd_score(args)


class DrainMovesCheckingOutOfTheSolveBudget(ManifestFixture):
    def test_accepted_certificate_yields_verified_and_deletes_the_proof(self):
        _, proof = self.enqueue("inst-a")
        self.drain(self.checker(ACCEPTING_CHECKER))
        verdicts = vpm.load_verdicts(self.manifest)
        (row,) = list(verdicts.values())
        self.assertEqual(row["status"], vpm.VERIFIED)
        # The retained set stays bounded only because the artefact goes away.
        self.assertFalse(os.path.exists(proof))
        self.assertEqual(
            os.listdir(os.path.join(self.manifest, "pending")), [],
            "a drained row must not stay pending")

    def test_refused_certificate_yields_rejected_not_silence(self):
        self.enqueue("inst-b")
        self.drain(self.checker(REJECTING_CHECKER))
        (row,) = list(vpm.load_verdicts(self.manifest).values())
        self.assertEqual(row["status"], vpm.REJECTED)

    def test_checker_timeout_is_unverified_never_verified(self):
        """The checker's own budget is generous, but blowing it is not a win."""
        self.enqueue("inst-c")
        self.drain(self.checker(HANGING_CHECKER), timeout=1.0)
        (row,) = list(vpm.load_verdicts(self.manifest).values())
        self.assertEqual(row["status"], vpm.UNVERIFIED)
        self.assertIn("checker-timeout", row["note"])

    def test_missing_proof_is_unverified(self):
        _, proof = self.enqueue("inst-d")
        os.remove(proof)
        self.drain(self.checker(ACCEPTING_CHECKER))
        (row,) = list(vpm.load_verdicts(self.manifest).values())
        self.assertEqual(row["status"], vpm.UNVERIFIED)

    def test_claim_is_exclusive(self):
        self.enqueue("inst-e")
        pending = os.path.join(self.manifest, "pending", "inst-e.json")
        self.assertIsNotNone(vpm.claim(self.manifest, pending))
        self.assertIsNone(vpm.claim(self.manifest, pending),
                          "two drainers must not verify the same row")


class ScoreKeepsTheHonestScoreProperty(ManifestFixture):
    def test_verified_counts_rejected_and_unverified_do_not(self):
        for token, checker in (("ok", ACCEPTING_CHECKER), ("bad", REJECTING_CHECKER)):
            self.enqueue(token)
            self.drain(self.checker(checker, f"{token}.sh"))
        results = [
            {"cnf": "ok.cnf", "verdict": "unsat", "time": 9.0, "rc": 20,
             "solver_wall_ms": 1234},
            {"cnf": "bad.cnf", "verdict": "unsat", "time": 9.0, "rc": 20,
             "solver_wall_ms": 1234},
            {"cnf": "never-drained.cnf", "verdict": "unsat", "time": 9.0, "rc": 20},
            {"cnf": "model.cnf", "verdict": "sat", "time": 3.0, "rc": 10},
            {"cnf": "lost.cnf", "verdict": "timeout", "time": 300.0, "rc": 124},
        ]
        out = os.path.join(self.root, "score.json")
        rc = self.score(self.sweep_json(results), out=out)
        self.assertEqual(rc, 2, "a rejected certificate must fail the join loudly")
        scored = json.load(open(out))
        # Four instances answered; only two may be claimed.
        self.assertEqual(scored["solved_competition_mode"], 4)
        self.assertEqual(scored["scored"], 2)
        self.assertEqual(scored["counts"]["solved+verified"], 1)
        self.assertEqual(scored["counts"]["solved+rejected"], 1)
        # A row that was never drained has NO verdict, which is an ABSENT
        # measurement rather than a failed one. It must not land in
        # `unverified` (a checker ran and declined) -- collapsing the two
        # would let a deleted verdict masquerade as a checker failure, and
        # would make a healthy score degrade silently on a re-run.
        self.assertEqual(scored["counts"]["solved+unverified"], 0)
        self.assertEqual(scored["counts"]["solved+unmeasured"], 1)
        self.assertEqual(scored["counts"]["solved+model"], 1)
        self.assertEqual(scored["counts"]["unsolved"], 1)

    def test_a_missing_verdict_is_unmeasured_not_unverified(self):
        """Deleting a verdict must NOT silently restate a win as a failure.

        The verdict JSON is the durable record of a measurement; the proof it
        certified is deleted by `drain` on purpose. If the verdict is lost the
        score is no longer reproducible, and `score` must say so (exit 3)
        rather than book the row as though a checker had declined it.
        """
        self.enqueue("ok")
        self.drain(self.checker(ACCEPTING_CHECKER, "ok.sh"))
        results = [{"cnf": "ok.cnf", "verdict": "unsat", "time": 9.0, "rc": 20,
                    "solver_wall_ms": 1234}]
        out = os.path.join(self.root, "score.json")
        rc = self.score(self.sweep_json(results), out=out)
        self.assertEqual(rc, 0)
        first = json.load(open(out))
        self.assertEqual(first["counts"]["solved+verified"], 1)
        self.assertEqual(first["scored"], 1)

        for v in glob.glob(os.path.join(self.manifest, "verdicts", "*.json")):
            os.remove(v)

        rc = self.score(self.sweep_json(results), out=out)
        self.assertEqual(rc, 3, "an unreproducible score must not exit 0")
        second = json.load(open(out))
        self.assertEqual(second["counts"]["solved+unmeasured"], 1)
        self.assertEqual(second["counts"]["solved+unverified"], 0)
        # Still SOLVED -- AY did answer; only the certificate record is gone.
        self.assertEqual(second["solved_competition_mode"], 1)
        self.assertEqual(second["scored"], 0)

    def test_every_status_is_printed_even_at_zero(self):
        """A silently growing unverified pile must not look like a clean run."""
        results = [{"cnf": "lost.cnf", "verdict": "timeout", "time": 300.0, "rc": 124}]
        out = os.path.join(self.root, "score.json")
        self.score(self.sweep_json(results), out=out)
        counts = json.load(open(out))["counts"]
        for key in ("solved+verified", "solved+model", "solved+rejected",
                    "solved+unverified", "unsolved"):
            self.assertIn(key, counts)

    def test_par2_is_priced_at_the_solver_clock_not_the_harness_clock(self):
        """Configuration (2)'s wall time is the solve time; the harness clock
        carries wrapper overhead (and used to carry the whole checker run)."""
        self.enqueue("fast", ay_wall_ms=5_000)
        self.drain(self.checker(ACCEPTING_CHECKER))
        results = [{"cnf": "fast.cnf", "verdict": "unsat", "time": 211.0, "rc": 20,
                    "solver_wall_ms": 5_000}]
        out = os.path.join(self.root, "score.json")
        self.score(self.sweep_json(results, timeout_s=300.0), out=out)
        scored = json.load(open(out))
        self.assertEqual(scored["par2_solved_sum"], 5.0)
        self.assertEqual(scored["rows"][0]["solve_clock"], "solver")
        self.assertEqual(scored["rows"][0]["harness_time"], 211.0)

    def test_unsolved_rows_carry_the_full_par2_penalty(self):
        results = [{"cnf": "lost.cnf", "verdict": "timeout", "time": 300.0, "rc": 124}]
        out = os.path.join(self.root, "score.json")
        self.score(self.sweep_json(results, timeout_s=300.0), out=out)
        self.assertEqual(json.load(open(out))["par2_solved_sum"], 600.0)

    def test_configuration_is_named_and_never_guessed(self):
        results = [{"cnf": "lost.cnf", "verdict": "timeout", "time": 300.0, "rc": 124}]
        path = os.path.join(self.root, "legacy.json")
        with open(path, "w") as fh:
            json.dump({"timeout_s": 300.0, "results": results}, fh)   # no field
        out = os.path.join(self.root, "score.json")
        args = vpm.main.__globals__["argparse"].Namespace(
            sweep=path, manifest=self.manifest, out=out, config=None)
        vpm.cmd_score(args)
        self.assertEqual(json.load(open(out))["solver_configuration"], "UNRECORDED")


class WrapperDefersInsteadOfChecking(unittest.TestCase):
    """The wrapper itself must exit on AY's verdict, not on the checker's."""

    WRAPPER = os.path.expanduser("~/ay-bench/bin/ay-proofmode")

    def test_wrapper_never_invokes_the_checker_inline(self):
        if not os.path.exists(self.WRAPPER):
            self.assertTrue(True, "wrapper lives outside the repo; nothing to check")
            return
        text = open(self.WRAPPER).read()
        self.assertIn("CERTIFICATE-DEFERRED", text)
        self.assertNotIn('"$DSR" "$CNF"', text,
                         "dsr-trim must not run inside the timed region")
        self.assertIn("--no-verify-proof", text,
                      "the wrapper must keep matching the submission's rigor level")

    def test_wrapper_is_syntactically_valid_sh(self):
        if not os.path.exists(self.WRAPPER):
            self.assertTrue(True, "wrapper lives outside the repo; nothing to check")
            return
        proc = subprocess.run(["/bin/sh", "-n", self.WRAPPER],
                              capture_output=True, text=True)
        self.assertEqual(proc.returncode, 0, proc.stderr)


if __name__ == "__main__":
    unittest.main()
