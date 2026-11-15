#!/usr/bin/env python3
# ay-script: milp-decision-census
"""
DECISION CENSUS -- the instrument for MECHANISM D (node-rate steering).

WHY THIS EXISTS.  the development design notes sorted the
branch-and-bound's clock reads into four mechanisms and measured two of them with
`scripts/milp_limit_invariance.py`: solve one model at two `--limit` values, and if
it PROVES inside both then neither run was budget-bound, so the trees must match.
That instrument is blind to mechanism D BY CONSTRUCTION, and its own residue
section says so:

    Mechanism D was not measured, only read. The node-rate steering (`slow_tree`,
    `rins_rescue`, the node-cut repayment) is genuinely load-coupled rather than
    budget-coupled, so limit-invariance is blind to it by construction.

The reason is mechanical. D divides a node or bound count by ELAPSED WALL and
branches on the quotient. Both arms of a limit-invariance pair run on the same box
at the same speed, so both see the same rate, and the instrument reads INVARIANT
however hard the site is steering.

THE INSTRUMENT.  Vary the RATE instead of the budget. Hold `--limit` fixed, run one
arm at ambient load and one with N spinners pinned on, and read the per-site
(evals, fires, steer_sum) triples that `--features dcensus` compiles into the node
loop (`crates/ay-milp/src/dcensus.rs`), alongside the ordinary (verdict, objective,
nodes). Arms are interleaved LOW,HIGH,LOW,HIGH -- never in blocks.

WHY THE COUNTER IS NOT THE ONE THE CENSUS REJECTED.  That report rejected a firing
counter, in terms worth repeating:

    a counter that covers 12 of 258 steering sites reports 0 on a model it simply
    does not watch, and a 0 that reads as "reproducible" is precisely the
    instrument artifact this campaign exists to kill.

That objection kills a counter that records only FIRINGS. Every site here carries
`evals` (the predicate was reached and computed) as well as `fires`, and the dump
prints ALL SIX SITES on EVERY run including the all-zero rows, so:

    evals = 0, fires = 0   ->  the site is NOT ON THIS MODEL'S PATH (nothing seen)
    evals = N, fires = 0   ->  the site ran N times and steered nothing (evidence)

"not watched" is therefore always distinguishable from "watched and quiet".

COVERAGE, stated so a clean census is not over-read.  Six sites, and they are not a
sample: they are the complete set of NODE-RATE reads in `bab.rs`, enumerated
structurally rather than from memory by

    grep -n "nodes as f64 / \\|/ solve_start.elapsed()\\|/ t_start.elapsed()\\|\\
pace_rate\\|proof_on_pace" crates/ay-milp/src/bab.rs

which returns the two rate helpers plus exactly six call sites, all instrumented.
This says NOTHING about mechanisms A (anytime stop), B (share of the remaining
deadline) or C (multiple of an observed wall) -- those are limit-invariance's job --
and it is NOT a claim to cover all 258 steering sites the source census counted.

MEASURED 2026-08-28, aarch64-apple-darwin, release + target-cpu=native,
`AY_MILP_THREADS=1`, limit 60, 3 reps, 14 spinners, 24 solves, interleaved,
1-minute load 4.10..24.33 on 14 cpus. Census binary `mps_solve` built
`--features dcensus`, sha256 ad62201d194db687. RESULT:

  p2756   LOW  98,783 / 82,144 / 89,879 nodes (three distinct), slow_tree FIRES
               4/2/2, rins_wide_interval fires 6/4/4, steer_sum 5595/4666/4420
          HIGH 88,883 nodes THREE TIMES OUT OF THREE, and every one of the six
               sites at evals=0 -- the steering lane is not entered at all.
  misc07  LOW  6403 / 6345 / 6385 (three distinct), rins_wide_interval fires 5/5/5
          HIGH 6347 / 6347 / 6347, rins_wide_interval fires 0/1/1 (the 512 floor
               clamp binds, so the RATE does not choose the interval)
  mas76   273,252 nodes in ALL SIX runs, while rins_on_pace fires 2 (LOW) vs
          3 (HIGH) reproducibly -- a D site whose firing count MOVES with load
          over a tree that does not. D firing is not sufficient for drift.
  stein45 58,692 nodes in all six, every counter identical in both arms.

So D does silently change a reproducible quantity, and it does it on exactly the
two models `.milp_node_baseline.toml` already quarantines as `[flaky]` and which
the limit-invariance census could not localize. It also explains that census's
oddest datum -- "at --limit 300 p2756 is load-invariant over a 6.2x load swing,
88,883 nodes at load 37.66 and again at 230.99": 88,883 is the D-SILENT tree.

  node_cut_repay reached evals=0 on all 19 instances scanned and all 4 censused.
  It is instrumented and simply not exercised at limit 60 on this corpus, so this
  census makes NO claim about it -- which is the distinction the `evals` column
  exists to preserve.
  rins_rescue was reached up to 947 times (mas74) and FIRED ZERO TIMES in 23/23
  runs across the whole corpus.
  endgame_on_pace was evaluated 434,851 times on mas74 and fired zero times.

BUILD:  CARGO_TARGET_DIR=<own> targo --unverified build --release -p ay-milp \\
            --features dcensus --example mps_solve
        (without the Trust toolchain: cargo build with the same arguments)
RUN:    python3 scripts/milp_decision_census.py --solver <that binary> --check

A HARNESS THAT MEASURED NOTHING MUST NOT REPORT SUCCESS: an empty instance
selection, or a missing instance, exits 2 (SETUP) rather than printing "0 fail".

CORRECTION, 2026-08-28. As first shipped (`6e6077641`) the drift key was the
whole result LINE, which carries `{dt:.3}` -- a wall clock -- so `--check` could
never report clean and its exit code carried no information. Reproduced against
a shim emitting a CONSTANT status, objective and node count (see `reproducible`
below for the transcript): two instances, both reported DRIFT, exit 1. The key
is now the parsed wall-free tuple, and the same shim run reports `0 drift`,
exit 0. The census RESULTS recorded above were read off the printed per-run
lines rather than off that classifier, so they are unaffected; what was broken
was the pass/fail verdict, which could not distinguish p2756 from the stein45
control because it called both DRIFT.
"""

import argparse
import os
import re
import subprocess
import sys
import time

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CORPUS = os.path.expanduser('~/ay-bench/milp-gate/instances')
SOLVER = os.path.join(REPO, 'target-dc', 'release', 'examples', 'mps_solve')

# The four models the reference census used: two the node ratchet quarantines as
# [flaky] (misc07, p2756) and two it pins exactly (mas76, stein45) as controls.
DEFAULT_INSTANCES = ['misc07', 'p2756', 'mas76', 'stein45']

SITE_RE = re.compile(
    r'^dcensus site=(\S+)\s+evals=(\d+)\s+fires=(\d+)\s+steer_sum=(\d+)')
RESULT_RE = re.compile(r'^(OPTIMAL|FEASIBLE|INFEASIBLE|UNKNOWN|BOUND)\b(.*)$')


def reproducible(verdict):
    """The load-INVARIANT part of a `mps_solve` result line.

    THE INSTRUMENT DEFECT THIS EXISTS TO CLOSE, reproduced 2026-08-28 before it
    was fixed. `mps_solve` prints `<status> <objective> {dt:.3} <nodes>`
    (`crates/ay-milp/examples/mps_solve.rs:542` and its five siblings), so the
    SECOND-TO-LAST field is a wall clock. Keying drift on the whole line made
    every run drift: driven against a shim that emits a constant status,
    objective and node count and varies only the wall, `--check` reported

        p0033  LOW  [OPTIMAL 3089 0.228 287]   p0033  HIGH [OPTIMAL 3089 0.266 287]
        p0282  LOW  [OPTIMAL 258411 0.033 368] p0282  HIGH [OPTIMAL 258411 0.354 368]
          p0033 DRIFT ; p0282 DRIFT ; === 2 drift ===        exit 1

    i.e. it could never report clean, so its green/red output carried no
    information and could not distinguish p2756 from the stein45 control.

    The wall is dropped by POSITION, not by parsing the number, so a status
    whose payload contains spaces (`UNKNOWN {reason:?}`) keeps all of it.
    """
    # ALWAYS A TUPLE, so a run that printed no result line at all sorts beside
    # the ones that did instead of raising `TypeError: '<' not supported between
    # NoneType and tuple` in the summary. A crashed arm is drift, loudly.
    if verdict is None:
        return ('<NO RESULT LINE>',)
    fields = verdict.split()
    if len(fields) < 3:
        return tuple(fields)
    return tuple(fields[:-2]) + (fields[-1],)


def load1():
    """1-minute load average. Recorded with every run, never used as a gate."""
    return os.getloadavg()[0]


def spinners(n):
    """N busy-loop children, returned so the caller can always reap them."""
    return [subprocess.Popen([sys.executable, '-c', 'while True: pass'])
            for _ in range(n)]


def reap(procs):
    for p in procs:
        p.kill()
    for p in procs:
        p.wait()


def run(solver, mps, secs):
    """One solve. The solver's OWN budget is used -- never an external killer,
    because SIGALRM lands before the incumbent is printed and that has been
    misread as 'found nothing' in this campaign before."""
    env = dict(os.environ, AY_MILP_THREADS='1')
    t0 = time.time()
    proc = subprocess.run([solver, mps, str(secs)], capture_output=True,
                          text=True, env=env)
    wall = time.time() - t0
    rc = proc.returncode
    verdict = None
    for line in proc.stdout.splitlines():
        m = RESULT_RE.match(line)
        if m:
            verdict = line.strip()
            break
    sites = {}
    for line in proc.stderr.splitlines():
        m = SITE_RE.match(line)
        if m:
            sites[m.group(1)] = (int(m.group(2)), int(m.group(3)),
                                 int(m.group(4)))
    return {'rc': rc, 'verdict': verdict, 'sites': sites, 'wall': wall}


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--solver', default=SOLVER,
                    help='mps_solve built with --features dcensus')
    ap.add_argument('--corpus', default=CORPUS)
    ap.add_argument('--instances', default=','.join(DEFAULT_INSTANCES))
    ap.add_argument('--limit', type=float, default=60.0)
    ap.add_argument('--reps', type=int, default=3)
    ap.add_argument('--spinners', type=int, default=14)
    ap.add_argument('--check', action='store_true',
                    help='exit 1 if any instance changes a REPRODUCIBLE quantity '
                         '(nodes/verdict/objective) between the two load arms')
    a = ap.parse_args()

    if not os.path.exists(a.solver):
        print('SETUP: census solver not built at %s\n'
              '  CARGO_TARGET_DIR=<own> targo --unverified build --release -p ay-milp '
              '--features dcensus --example mps_solve\n'
              '  (without the Trust toolchain: cargo build with the same arguments)'
              % a.solver,
              file=sys.stderr)
        return 2

    names = [s for s in a.instances.split(',') if s]
    if not names:
        print('SETUP: empty instance selection -- refusing to report a verdict '
              'over nothing measured', file=sys.stderr)
        return 2
    paths = {}
    for n in names:
        p = os.path.join(a.corpus, n + '.mps')
        if not os.path.exists(p):
            print('SETUP: instance %s missing at %s' % (n, p), file=sys.stderr)
            return 2
        paths[n] = p

    # A probe run proves the binary actually carries the probes. A default build
    # prints nothing, and its silence would otherwise read as "no site fired".
    probe = run(a.solver, paths[names[0]], 1)
    if not probe['sites']:
        print('SETUP: %s emitted no `dcensus site=` lines -- it was NOT built '
              'with --features dcensus, and an uninstrumented binary would '
              'report every site quiet' % a.solver, file=sys.stderr)
        return 2

    records = []
    for rep in range(1, a.reps + 1):
        for arm in ('LOW', 'HIGH'):
            procs = []
            if arm == 'HIGH':
                procs = spinners(a.spinners)
                time.sleep(45)          # let the 1-minute average catch up
            try:
                for n in names:
                    ld = load1()
                    r = run(a.solver, paths[n], a.limit)
                    r.update(instance=n, rep=rep, arm=arm, load1=ld)
                    records.append(r)
                    sites = ' '.join(
                        '%s:%d/%d/%d' % (k, v[0], v[1], v[2])
                        for k, v in sorted(r['sites'].items()))
                    print('%-9s rep=%d arm=%-4s load1=%6.2f rc=%d wall=%6.2f '
                          '[%s] %s' % (n, rep, arm, ld, r['rc'], r['wall'],
                                       r['verdict'], sites))
                    sys.stdout.flush()
            finally:
                reap(procs)
            if arm == 'HIGH':
                time.sleep(20)          # and let it fall again

    if not records:
        print('SETUP: no runs completed', file=sys.stderr)
        return 2

    print('\n=== decision census: %d instances, %d solves, limit %g, load %.2f..%.2f ==='
          % (len(names), len(records), a.limit,
             min(r['load1'] for r in records), max(r['load1'] for r in records)))
    fails = 0
    for n in names:
        rs = [r for r in records if r['instance'] == n]
        # DRIFT IS KEYED ON THE PARSED, WALL-FREE TUPLE (see `reproducible`).
        # The full line is still what gets PRINTED, because the wall is useful
        # context; it is simply not allowed to decide the verdict.
        keys = sorted({reproducible(r['verdict']) for r in rs})
        low = {reproducible(r['verdict']) for r in rs if r['arm'] == 'LOW'}
        high = {reproducible(r['verdict']) for r in rs if r['arm'] == 'HIGH'}
        steered = sorted({s for r in rs for s, v in r['sites'].items() if v[1]})
        drift = len(keys) > 1
        fails += 1 if drift else 0
        print('  %-9s %s  D-sites that FIRED: %s'
              % (n, 'DRIFT' if drift else 'stable',
                 ', '.join(steered) if steered else '<none>'))
        if drift:
            for k in keys:
                where = []
                if k in low:
                    where.append('LOW')
                if k in high:
                    where.append('HIGH')
                lines = sorted({r['verdict'] for r in rs
                                if reproducible(r['verdict']) == k})
                print('      %s   [%s]' % (' '.join(k), '+'.join(where)))
                for line in lines:
                    print('          seen as: %s' % line)
    print('=== %d drift ===' % fails)
    return 1 if (a.check and fails) else 0


if __name__ == '__main__':
    sys.exit(main())
