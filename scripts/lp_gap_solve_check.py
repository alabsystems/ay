#!/usr/bin/env python3
"""What does the SOLVER do with the LPs its float diagnostics gave up on?

`diag lp-only` truncating is a statement about one cold walk. `diag shipped-lp`
DECLINING is a statement about the float ladder — and its own docstring says a
real solve CONTINUES INTO THE EXACT RIM from there. Neither is the solver's
answer, so neither can size the defect on its own.

This runs `ay-milp solve`, which is the answer, and checks it against the pinned
HiGHS oracle where one exists. `solve` is also the only entry point that
UNSCALES (`MpsProblem::unscale`), so its objective is the one directly
comparable to a reference; the diag lanes' values are in the reader's scaled
units and are NOT (see `MpsProblem::units_clause`).

Usage: lp_gap_solve_check.py <ay-milp> <secs> <name>=<path> [...]
"""
from __future__ import annotations

import json
import os
import re
import subprocess
import sys

OPT_RE = re.compile(r"^(OPTIMAL|INFEASIBLE|UNBOUNDED|UNKNOWN|TIMEOUT)\s*(\S+)?", re.M)
ORACLE = os.path.expanduser("~/ay-bench/oracle_v2/oracle")


def main() -> int:
    binary, secs = sys.argv[1], float(sys.argv[2])
    print(f"{'instance':28s} {'ay solve':12s} {'objective':24s} {'oracle':24s} agree")
    for spec in sys.argv[3:]:
        name, path = spec.split("=", 1)
        try:
            r = subprocess.run([binary, "solve", path, "--time-limit", str(secs)],
                               capture_output=True, text=True, timeout=secs + 120)
            txt = (r.stdout or "") + (r.stderr or "")
        except subprocess.TimeoutExpired:
            txt = "TIMEOUT"
        m = OPT_RE.search(txt)
        verdict = m.group(1) if m else "NOPARSE"
        val = m.group(2) if m and m.group(2) else ""
        oj = os.path.join(ORACLE, f"{name}_lprelax.json")
        ref = ""
        agree = "-"
        if os.path.exists(oj):
            ref = json.load(open(oj))["objective"]
            try:
                a, b = float(val), float(ref)
                # The oracle is HiGHS f64; ay's is an exact rational printed as
                # decimal. Same tolerance the corpus's own verifier uses.
                agree = "YES" if abs(a - b) <= 5e-6 + 1e-9 * abs(b) else "NO"
            except ValueError:
                agree = "?"
        print(f"{name[:28]:28s} {verdict:12s} {val[:24]:24s} {ref[:24]:24s} {agree}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
