"""The quiet-box precondition, and that BOTH milp gates actually have it.

`scripts/corpus_guard.py` shipped for six days with NO load guard while
`scripts/milp_node_gate.py` next door refused above 0.35 x cpu_count -- and the
unguarded one is the MORE load-coupled of the two, because it gates wall ratios
(30% WALL, 1.25x LIMIT-INVARIANCE) and a 120 s deadline, where the ratchet gates
only node counts. That gap produced FAILs with no commit behind them and nearly
put a phantom regression on the record.

A guard nothing tests is a guard that can be deleted by accident, so this file
pins the three behaviours that matter and the fact that there is ONE definition
of "quiet" rather than two that can drift apart:

  * busy  -> refuse (exit 2, SETUP), and MEASURE NOTHING;
  * quiet -> proceed;
  * --allow-busy -> proceed anyway, because reproducing a failure you already
    have in hand is a legitimate thing to want.

It deliberately does NOT test that a real regression still fails -- that needs a
solver and a corpus, and lives in the gate run itself. What it does test is that
the refusal is a SETUP exit and never a clean one, which is the property that
stops the guard from becoming a mute button.
"""

import importlib.util
import io
import sys
import unittest
from contextlib import redirect_stderr
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parents[1]


def load_script(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


corpus_guard = load_script("corpus_guard_load_test", SCRIPTS / "corpus_guard.py")
# NOT a second load_script: this is the module `corpus_guard` itself imported,
# fished back out of sys.modules. Loading the file twice would give two distinct
# function objects and make the identity assertion below vacuous -- which is the
# exact thing it exists to rule out.
node_gate = sys.modules["milp_node_gate"]


class OneDefinitionOfQuiet(unittest.TestCase):
    def test_both_gates_share_the_same_threshold_object(self):
        # Not "both happen to say 0.35": the SAME function, imported. A constant
        # spelled in two gates is a constant that drifts.
        self.assertIs(corpus_guard.busy_box, node_gate.busy_box)
        self.assertEqual(node_gate.LOAD_FRACTION, 0.35)

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
        self.assertTrue(node_gate.busy_box(fraction=-1.0)[0])
        self.assertFalse(node_gate.busy_box(fraction=1e9)[0])


class CorpusGuardRefusesOnABusyBox(unittest.TestCase):
    def _with_load(self, fraction):
        """Force busy_box's verdict without touching the real machine."""
        real = corpus_guard.busy_box
        corpus_guard.busy_box = lambda: (fraction, 99.0 if fraction else 0.1, 14)
        self.addCleanup(setattr, corpus_guard, "busy_box", real)

    def test_busy_refuses_and_says_setup(self):
        self._with_load(True)
        err = io.StringIO()
        with redirect_stderr(err):
            ok = corpus_guard.quiet_box_ok(allow_busy=False)
        self.assertFalse(ok)
        text = err.getvalue()
        self.assertTrue(text.startswith("SETUP:"), text)
        self.assertIn("--allow-busy", text)
        self.assertIn("load average", text)

    def test_quiet_proceeds_silently(self):
        self._with_load(False)
        err = io.StringIO()
        with redirect_stderr(err):
            ok = corpus_guard.quiet_box_ok(allow_busy=False)
        self.assertTrue(ok)
        self.assertEqual(err.getvalue(), "")

    def test_allow_busy_overrides(self):
        self._with_load(True)
        err = io.StringIO()
        with redirect_stderr(err):
            ok = corpus_guard.quiet_box_ok(allow_busy=True)
        self.assertTrue(ok)
        self.assertEqual(err.getvalue(), "")

    def test_unknown_load_proceeds_rather_than_blocking(self):
        # busy is None on a platform with no getloadavg. Blocking every gate
        # there would cost more than the drift it prevents.
        self._with_load(None)
        ok = corpus_guard.quiet_box_ok(allow_busy=False)
        self.assertTrue(ok)

    def test_the_flag_exists_on_the_command_line(self):
        # The escape hatch has to be reachable, or people reach for `git commit
        # --no-verify` instead.
        source = (SCRIPTS / "corpus_guard.py").read_text()
        self.assertIn("'--allow-busy'", source)


if __name__ == "__main__":
    unittest.main()
