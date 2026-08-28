#!/usr/bin/env python3
# ay-script: milp-limit-invariance
"""
LIMIT-INVARIANCE -- a LOAD-FREE instrument for wall-coupling in the SEARCH.

WHY THIS EXISTS.  `scripts/milp_node_gate.py` pins twenty instances to exact node
counts and excludes four by name in `.milp_node_baseline.toml`'s `[flaky]`
section. That exclusion list is the SYMPTOM of a defect nobody had localized: the
branch-and-bound reads the wall clock, so a model's tree is partly a function of
the machine rather than of the model. Establishing it took repeated sampling --
"5 repeats at fixed config on an idle machine" -- which needs a quiet box, needs
many runs, and still only ever yields a spread, never a mechanism.

THE INSTRUMENT.  Solve ONE model with ONE binary at TWO `--limit` values. If the
run PROVES optimality inside both budgets, then the budget was not the binding
constraint in either, and a search whose tree is a function of its input MUST
return the same (verdict, objective, nodes) both times. If it does not, the tree
is denominated in the caller's deadline, and that is a property of the code, not
of the box.

WHAT MAKES IT BETTER THAN REPEATING RUNS.  No load control, no quiet box, no
spinners, no statistics. The two arms differ in ONE input the caller supplies on
purpose, and both arms can run on a machine at load 50 -- which is why this file
has no `busy_box()` guard while `milp_node_gate.py` and `corpus_guard.py` both
need one. It is also STRICTLY STRONGER on what it does cover: `corpus_guard.py`'s
own limit-invariance tripwire compares WALL at two limits, and wall cannot
distinguish "the same tree, slower" from "a different tree".

WHAT IT CANNOT SEE, stated so a clean run is not over-read:

  * A model that does not PROVE at one of the two limits is EXCLUDED, not passed.
    A truncated run stops where the clock says stop, so its node count carries no
    signal (this is the same control the development design notes
    identity.md` established on four other models, where one binary run twice
    disagreed with itself by up to 1.9x). `mas74` and `air05` are excluded on
    every budget tried here.
  * Wall-coupling that happens to land on the same tree at both limits is INVISIBLE
    to this. `blend2` and `mod010` are invariant here and are still known to move
    under CONTENTION (measured in `milp_node_gate.py`'s header: blend2 9,070 ->
    8,995, mod010 2,381 -> 2,291 under a concurrent `cargo test`). A clean result
    here means "not budget-coupled", never "reproducible".

  * A VERY BUSY BOX MAKES THIS INSTRUMENT LESS SENSITIVE, NOT MORE -- the opposite
    of the usual worry, and measured here. At 1-minute load 5.5..14 `misc07` gives
    a different node count essentially every run (6279..6403); at load 140..211 it
    gave 6,347 SIX times out of six, and one such pair reads INVARIANT. The
    mechanism is the point: the devices this instrument hunts are budgeted in wall,
    so under saturation they accomplish nothing at EITHER limit and the tree
    collapses to one fixed low-work shape. Prefer a quiet box; a clean result taken
    at high load is the weakest form of the evidence.

MEASURED 2026-08-27, aarch64-apple-darwin, release + target-cpu=native, one
binary (`examples/mps_solve`, sha256 78a72dad490d995c at build time; a later
`cargo test --no-run` in the same target dir relinked it after a doc-comment-only
edit and it hashes c04acafc7f0fd5b8 at teardown -- zero executable lines differ),
`AY_MILP_THREADS=1`,
197 solves, arms interleaved, 1-minute load 3.61..230.99 recorded per run. Full
per-run record: the development design notes.

    INVARIANT (20)   air03 blend2 dcmulti enigma gt2 lseu mas76 misc03 mod008
                     mod010 p0033 p0201 p0282 p0548 pk1 qiu qnet1 rout stein27
                     stein45 -- i.e. EVERY model the node ratchet pins, each
                     returning ONE node count whenever it returned OPTIMAL.
                     14 of them across limits 5/20/60/300 (a 60x swing), 2 reps
                     each, 112 runs, every field identical in all four arms.

    NOT INVARIANT (3)
                     misc07  OPTIMAL 2810 always; TEN distinct node counts in
                             thirteen runs -- 6279 6282 6347 6361 6363 6370 6375
                             6389 6393 6403.
                     nw04    OPTIMAL 16862 always; 398 / 638 at limit 20 and
                             2,571 at limits 60 and 300. ALSO the sharpest wall
                             reading in the corpus: the SAME 2,571-node tree
                             costs 17.423/17.420/17.443 s at limit 60 and
                             41.565/41.590 s at limit 300 -- spread under 0.03 s
                             inside each arm, ~24 s bought nothing -- because the
                             set-partition devices size themselves off the
                             remaining budget (`SETPART_TIME_SHARE` 0.5,
                             `SPLNS_TIME_SHARE` 0.8).
                     p2756   OPTIMAL 3124 whenever it proves; FOUR node counts --
                             92,145 at limit 60, {78,752 | 88,883 | 78,401} at
                             limit 120, and 88,883 five times at limit 300 across
                             1-minute load 37.7 .. 231.0.

    EXCLUDED (2)     mas74 air05 -- never proved inside any budget tried.

THE OVERLAP WITH `[flaky]` IS THE RESULT.  That list is mas74 / misc07 / nw04 /
p2756. Three of the four are the three this instrument flags, and the fourth is
the one it excludes for the documented reason. The list was assembled by hand
from repeated sampling over months; it falls out of one pair of runs per model.

USAGE

    milp_limit_invariance.py --solver target/release/examples/mps_solve \\
        [--corpus DIR] [--instances a,b,c] [--limits 60,300] [--reps 2] \\
        [--json OUT] [--check]

`--check` compares the measured partition against `EXPECTED` below and exits 1 if
a model recorded INVARIANT is found NOT to be. It never rewrites anything: like
the node ratchet, a value a passing run can silently update is not a pin.
"""
import argparse
import json
import os
import subprocess
import sys
import time

CORPUS = os.path.expanduser('~/ay-bench/milp-gate/instances')

# The partition measured on 2026-08-27 (see the module docstring). `True` means
# "proved optimal at every limit tried, with identical nodes and objective".
EXPECTED = {
    'air03': True, 'blend2': True, 'dcmulti': True, 'enigma': True,
    'gt2': True, 'lseu': True, 'mas76': True, 'misc03': True,
    'mod008': True, 'mod010': True, 'p0033': True, 'p0201': True,
    'p0282': True, 'p0548': True, 'pk1': True, 'qiu': True,
    'qnet1': True, 'rout': True, 'stein27': True, 'stein45': True,
    'misc07': False, 'nw04': False, 'p2756': False,
}

DEFAULT_INSTANCES = sorted(EXPECTED)


def run(solver, mps, secs):
    """One solve. `mps_solve` prints `status value wall nodes` as its last line."""
    env = dict(os.environ, AY_MILP_THREADS='1')
    lo = round(os.getloadavg()[0], 2)
    t = time.time()
    try:
        out = subprocess.run([solver, mps, str(secs)], capture_output=True,
                             text=True, env=env, timeout=secs * 3 + 120)
    except subprocess.TimeoutExpired:
        return {'status': 'HARNESS_TIMEOUT', 'load1': lo}
    wall = round(time.time() - t, 3)
    # A REFUSED FLAG EXITS 2 WITH EMPTY STDOUT, and a harness that reads the last
    # stdout line records that as a missing datum. Same guard, same reason, as
    # `milp_node_gate.py`.
    if out.returncode != 0:
        return {'status': 'EXIT_%d' % out.returncode, 'load1': lo, 'wall_s': wall,
                'raw': (out.stdout[-200:] + out.stderr[-200:]).strip()}
    line = (out.stdout.strip().splitlines() or [''])[-1].split()
    if len(line) < 4:
        return {'status': 'NO_OUTPUT', 'load1': lo, 'wall_s': wall}
    try:
        return {'status': line[0], 'obj': float(line[1]), 'nodes': int(line[-1]),
                'wall_s': wall, 'load1': lo}
    except ValueError:
        return {'status': 'PARSE_ERROR', 'load1': lo, 'raw': ' '.join(line)}


def find(name, corpus):
    for ext in ('.mps', '.mps.gz'):
        p = os.path.join(corpus, name + ext)
        if os.path.exists(p):
            return p
    return None


def verdict(runs):
    """INVARIANT / NOT-INVARIANT / EXCLUDED for one model's runs."""
    proved = [r for r in runs if r.get('status') == 'OPTIMAL']
    if len(proved) != len(runs) or not proved:
        return 'EXCLUDED', 'did not prove at every limit (%s)' % (
            ','.join(sorted({r.get('status', '?') for r in runs})))
    nodes = sorted({r['nodes'] for r in proved})
    objs = sorted({r['obj'] for r in proved})
    if len(nodes) == 1 and len(objs) == 1:
        return 'INVARIANT', 'nodes=%d obj=%s over %d runs' % (nodes[0], objs[0], len(proved))
    return 'NOT-INVARIANT', 'nodes %s obj %s' % (
        ' '.join(str(n) for n in nodes), ' '.join(str(o) for o in objs))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--solver', required=True)
    ap.add_argument('--corpus', default=CORPUS)
    ap.add_argument('--instances', default=','.join(DEFAULT_INSTANCES))
    ap.add_argument('--limits', default='60,300')
    ap.add_argument('--reps', type=int, default=2)
    ap.add_argument('--json')
    ap.add_argument('--check', action='store_true')
    a = ap.parse_args()

    names = [s for s in a.instances.split(',') if s]
    limits = [float(s) for s in a.limits.split(',')]
    rows, by_name, missing = [], {}, []
    for name in names:
        mps = find(name, a.corpus)
        if mps is None:
            print('MISSING  %s' % name)
            missing.append(name)
            continue
        # ARMS INTERLEAVED, NEVER BLOCKED: the inner loop is over limits, so a
        # drifting ambient load is common-mode between the arms rather than
        # aligned with one of them.
        for rep in range(a.reps):
            for lim in limits:
                rec = run(a.solver, mps, lim)
                rec.update(name=name, limit=lim, rep=rep)
                rows.append(rec)
                by_name.setdefault(name, []).append(rec)
                print('  %-9s lim=%-6g rep=%d  %-9s obj=%-16s nodes=%-8s wall=%-8s load=%s'
                      % (name, lim, rep, rec['status'], rec.get('obj'), rec.get('nodes'),
                         rec.get('wall_s'), rec.get('load1')), flush=True)

    print()
    fails = []
    for name in names:
        if name not in by_name:
            continue
        v, why = verdict(by_name[name])
        print('%-14s %-14s %s' % (name, v, why))
        if a.check and EXPECTED.get(name) is True and v == 'NOT-INVARIANT':
            fails.append('%s: recorded INVARIANT, measured NOT-INVARIANT -- %s' % (name, why))

    if a.json:
        with open(a.json, 'w') as f:
            json.dump({'limits': limits, 'reps': a.reps, 'solver': a.solver,
                       'results': rows}, f, indent=1)

    if a.check:
        print()
        # VACUITY FIRST. A harness that measured NOTHING must never print
        # `0 fail` and exit 0 -- that is this repo's signature defect, and it
        # has bitten twice: `milp_w0.py`/`ay_gurobi_closure.py` selected ZERO
        # instances for a fortnight and reported clean, and a green gate was
        # once cited as safety evidence over a branch that was UNREACHABLE on
        # the entire gated corpus. Exit 2 = SETUP, which is neither pass nor
        # fail, matching `milp_node_gate.py` and `corpus_guard.py`.
        if missing:
            print('SETUP: %d of %d instance(s) not found in %s: %s'
                  % (len(missing), len(names), a.corpus, ' '.join(missing)))
            print('       Nothing was measured for them, so this run is NOT a pass.')
            return 2
        if not by_name:
            print('SETUP: no instance produced a measurement; refusing to report a verdict.')
            return 2
        for f in fails:
            print('FAIL  %s' % f)
        print('%d fail (%d instance(s) measured)' % (len(fails), len(by_name)))
        return 1 if fails else 0
    return 0


sys.exit(main())
