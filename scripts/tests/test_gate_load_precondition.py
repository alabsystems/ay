"""The MILP gates and the host's load: the node ratchet's quiet-box
precondition, and the corpus guard, whose verdicts are counts and need none.

`scripts/milp_node_gate.py` refuses above 0.35 x cpu_count: two of its pinned
instances have wall-deadline-bounded root cut loops. These tests pin its three
behaviours: busy -> refuse (SETUP), quiet -> proceed, no load average -> proceed.

`scripts/corpus_guard.py` refused the same way from 2026-08-26, because three
of its five tripwires were wall ratios. Since 2026-10-15 every verdict it
gives is a count (the development design notes DR-37's rule): nodes, simplex iterations
(`ITERLEDGER engine=`), an exact optimum, a proof of optimality. A wall time
decides nothing; a solve its wall limit ended is COULD NOT RUN, never a pass,
unless the counts it reached are already past the baseline's whole search;
the clock-steered instance decides only its answer and status. So it runs on a
busy box, and these tests hold `compare` and `baseline_refusals` to that on
synthetic records: a slowdown that is only wall decides nothing, a count that
moved is a FAIL, the clock is never a verdict either way, and a baseline the
clock decided is not written.

Nothing here runs a solver or needs the corpus.
"""

import importlib.util
import sys
import unittest
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parents[1]


def load_script(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


node_gate = load_script("milp_node_gate_load_test", SCRIPTS / "milp_node_gate.py")
corpus_guard = load_script("corpus_guard_load_test", SCRIPTS / "corpus_guard.py")


class NodeGateQuietBox(unittest.TestCase):
    def test_busy_box_reports_load_cpus_and_a_verdict(self):
        busy, load, cpus = node_gate.busy_box()
        self.assertIsInstance(cpus, int)
        self.assertGreaterEqual(cpus, 1)
        if busy is None:
            self.assertIsNone(load)  # platform without getloadavg: proceed, do not block
        else:
            self.assertIsInstance(busy, bool)
            self.assertEqual(busy, load > node_gate.LOAD_FRACTION * cpus)

    def test_threshold_is_a_fraction_of_the_cpu_count_not_an_absolute(self):
        # 0.35 x 14 = 4.9 here; on a 4-core box the same fraction is 1.4. An
        # absolute number would be wrong on every machine but the one it was
        # typed on.
        #
        # The low bound is NEGATIVE, not 0.0, and that is deliberate: a load
        # average of exactly 0.00 is reachable on a genuinely idle machine, and
        # `0.0 > 0.0` is False, so a 0.0 fraction here would be a test that
        # passes on a busy box and fails on the quiet one it is meant to model.
        self.assertEqual(node_gate.LOAD_FRACTION, 0.35)
        self.assertTrue(node_gate.busy_box(fraction=-1.0)[0])
        self.assertFalse(node_gate.busy_box(fraction=1e9)[0])


def solve(status="OPTIMAL", obj=None, wall=1.0, nodes=100, work=5000, limit=120.0, short=None):
    rec = {"status": status, "obj": obj, "wall": wall, "nodes": nodes, "work": work, "limit": limit}
    if short is not None:
        rec["short"] = short
    return rec


# A stable instance (not clock-steered), its known optimum, and a baseline row.
STABLE = "gt2"
OPT = corpus_guard.OPTIMA[STABLE]


def verdicts(current, baseline=None):
    base = {STABLE: baseline or solve(obj=OPT)}
    fails, warns, notes, cnr = corpus_guard.compare(base, {STABLE: current})
    return fails, warns, notes, cnr


class CorpusGuardDecidesByCounts(unittest.TestCase):
    def test_a_slowdown_that_is_only_wall_decides_nothing(self):
        # The phantom of 2026-08-26 (qnet1 4.663s -> 8.482s at the same nodes):
        # the same nodes and work, slower. No FAIL, nothing unrun, nothing said.
        self.assertEqual(verdicts(solve(obj=OPT, wall=1.82, short=solve(obj=OPT, limit=3.0))),
                         ([], [], [], []))

    def test_more_work_at_the_same_nodes_is_a_fail(self):
        fails, _warns, _notes, _cnr = verdicts(solve(obj=OPT, work=9000))
        self.assertEqual(len(fails), 1, fails)
        self.assertIn("WORK 5000 -> 9000", fails[0])
        self.assertIn("UNCHANGED node count", fails[0])

    def test_more_nodes_is_a_fail(self):
        fails, _warns, _notes, _cnr = verdicts(solve(obj=OPT, nodes=130))
        self.assertTrue(any("NODES 100 -> 130" in fail for fail in fails), fails)

    def test_a_wrong_answer_is_a_fail(self):
        fails, _warns, _notes, _cnr = verdicts(solve(obj=OPT + 1))
        self.assertTrue(any("WRONG ANSWER" in fail for fail in fails), fails)

    def test_a_solve_the_wall_limit_ended_could_not_run_unless_its_counts_decided(self):
        # FEASIBLE at the 120 s limit, its counts inside the baseline's whole
        # search: the clock decided its status, and nothing else decided.
        for current in (solve(status="FEASIBLE", obj=OPT + 5, wall=120.01, nodes=90, work=4000),
                        solve(status="HARNESS_TIMEOUT", wall=None, nodes=None, work=None)):
            with self.subTest(current["status"]):
                fails, _warns, _notes, cnr = verdicts(current)
                self.assertEqual(fails, [])
                self.assertEqual(len(cnr), 1, cnr)
        # gt2's 208x explosion, cut short by the limit: the nodes it counted
        # are a lower bound on its whole search, which load cannot raise.
        fails, _warns, _notes, cnr = verdicts(solve(status="FEASIBLE", obj=OPT + 5, wall=120.01,
                                                    nodes=20800, work=4000))
        self.assertEqual(cnr, [])
        self.assertTrue(any("NODES 100 -> at least 20800" in fail for fail in fails), fails)
        # The same for work past the tolerance at fewer nodes.
        fails, _warns, _notes, cnr = verdicts(solve(status="FEASIBLE", obj=OPT + 5, wall=120.01,
                                                    nodes=90, work=9000))
        self.assertEqual(cnr, [])
        self.assertTrue(any("WORK 5000 -> at least 9000" in fail for fail in fails), fails)
        # The control: the same status, reached before the limit, is the solver's.
        fails, _warns, _notes, cnr = verdicts(solve(status="FEASIBLE", obj=OPT + 5, wall=10.0))
        self.assertTrue(any("STATUS OPTIMAL -> FEASIBLE" in fail for fail in fails), fails)

    def test_no_work_count_could_not_run_its_work_tripwire(self):
        fails, _warns, _notes, cnr = verdicts(solve(obj=OPT), baseline=solve(obj=OPT, work=None))
        self.assertEqual(fails, [])
        self.assertTrue(any("capture one with --baseline" in row for row in cnr), cnr)
        # A solve that printed no ITERLEDGER line counted no work; it is not 0.
        fails, _warns, _notes, cnr = verdicts(solve(obj=OPT, work=None))
        self.assertEqual(fails, [])
        self.assertTrue(any("no ITERLEDGER line" in row for row in cnr), cnr)

    def test_zero_work_is_a_count(self):
        # `ITERLEDGER total=0 engine=0`: a solve no simplex walk served (rout).
        # It is captured, it decides, and work appearing at the same nodes FAILs.
        self.assertEqual(corpus_guard.baseline_refusals({STABLE: solve(obj=OPT, work=0)}), [])
        self.assertEqual(verdicts(solve(obj=OPT, work=0, short=solve(obj=OPT, work=0)),
                                  baseline=solve(obj=OPT, work=0)), ([], [], [], []))
        fails, _warns, _notes, cnr = verdicts(solve(obj=OPT, work=40, short=solve(obj=OPT, work=40)),
                                              baseline=solve(obj=OPT, work=0))
        self.assertEqual(cnr, [])
        self.assertTrue(any("WORK 0 -> 40" in fail for fail in fails), fails)

    def test_limit_invariance_is_the_same_search_at_both_limits(self):
        self.assertIn(STABLE, corpus_guard.LIMIT_PROBES)
        same = solve(obj=OPT, wall=0.2, limit=3.0)
        self.assertEqual(verdicts(solve(obj=OPT, short=same)), ([], [], [], []))
        for name, short in (("nodes", solve(obj=OPT, nodes=90, limit=3.0)),
                            ("work", solve(obj=OPT, work=3000, limit=3.0)),
                            ("status before the limit", solve(status="FEASIBLE", obj=OPT + 5, wall=1.0,
                                                              limit=3.0)),
                            ("more nodes by the limit", solve(status="FEASIBLE", obj=OPT + 5, wall=3.0,
                                                              nodes=150, limit=3.0))):
            with self.subTest(name):
                fails, _warns, _notes, _cnr = verdicts(solve(obj=OPT, short=short))
                self.assertTrue(any("NOT LIMIT-INVARIANT" in fail for fail in fails), fails)
        # A short solve its limit ended short of the long run's counts, or none
        # at all: the probe did not decide, and says so.
        for name, current in (("ended at its limit", solve(obj=OPT, short=solve(
                                  status="FEASIBLE", obj=OPT + 5, wall=3.0, nodes=50, limit=3.0))),
                              ("not run", solve(obj=OPT))):
            with self.subTest(name):
                fails, _warns, _notes, cnr = verdicts(current)
                self.assertEqual(fails, [])
                self.assertTrue(any("LIMIT-INVARIANCE" in row for row in cnr), cnr)

    def test_the_clock_steered_instance_decides_only_its_answer_and_status(self):
        # misc07's root cut loop is wall-deadline bounded: its nodes and work
        # decide nothing, and are not reported.
        name = "misc07"
        opt = corpus_guard.OPTIMA[name]
        base = {name: solve(obj=opt, nodes=6000, work=5000)}
        self.assertEqual(corpus_guard.compare(base, {name: solve(obj=opt, nodes=9000, work=9000)}),
                         ([], [], [], []))
        # Cut short by its limit, its answer did not decide: COULD NOT RUN.
        fails, _warns, _notes, cnr = corpus_guard.compare(
            base, {name: solve(status="FEASIBLE", obj=opt * 1.01, wall=120.0, nodes=90000)})
        self.assertEqual(fails, [])
        self.assertEqual(len(cnr), 1, cnr)
        # Its answer still decides.
        fails, _warns, _notes, _cnr = corpus_guard.compare(base, {name: solve(obj=1.0)})
        self.assertTrue(any("WRONG ANSWER" in fail for fail in fails), fails)


class CorpusGuardBaselineRefusesTheClock(unittest.TestCase):
    def test_a_capture_the_clock_decided_is_refused_row_by_row(self):
        good = solve(obj=OPT)
        self.assertEqual(corpus_guard.baseline_refusals({STABLE: good}), [])
        for why, row in (("at its limit", solve(status="FEASIBLE", obj=OPT + 5, wall=120.01)),
                         ("timed out", solve(status="HARNESS_TIMEOUT", wall=None, nodes=None, work=None)),
                         ("wrong answer", solve(obj=OPT + 1)),
                         ("no work count", solve(obj=OPT, work=None))):
            with self.subTest(why):
                refused = corpus_guard.baseline_refusals({STABLE: row, "p0201": solve(
                    obj=corpus_guard.OPTIMA["p0201"])})
                self.assertEqual(len(refused), 1, refused)
                self.assertTrue(refused[0].startswith(STABLE + ":"), refused)
        # The clock-steered instance's work is never read, so it needs none.
        misc07 = solve(obj=corpus_guard.OPTIMA["misc07"], work=None)
        self.assertEqual(corpus_guard.baseline_refusals({"misc07": misc07}), [])


if __name__ == "__main__":
    unittest.main()
