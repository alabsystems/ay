#!/usr/bin/env python3
"""
CORPUS GUARD — re-measure ay-milp's shipped defaults and fail on drift.

WHY THIS EXISTS. Nothing in this repository re-measured shipped defaults, and it
cost three separate silent regressions that were only found by hand, days later:

  * `rout` sat on the scoreboard as the WORST instance (FEASIBLE, 22.1x behind
    Gurobi) while it was actually solving at the root in 0.39s and BEATING
    Gurobi 6.9x. The board was wrong in AY's favour and nobody noticed.
  * `gt2` went from 272 nodes to 56,670 -- a 208x node explosion -- and sat that
    way for four days.
  * `dcmulti`'s campaign headline (19.5x -> 6.1x) silently decayed back to 18.1x.
  * A shipped default (conditional big-M tightening) INVERTED within three days
    of being merged as "strict improvement where it fires, inert elsewhere".

A performance regression that nothing watches for is indistinguishable from the
solver simply being slow.

WHAT IT CHECKS, and why each tripwire is the shape it is:

  1. ANSWER      -- objective must equal the known optimum exactly (rel 1e-9).
                    A wrong answer fails immediately and unconditionally.
  2. STATUS      -- OPTIMAL must not decay to FEASIBLE (or vice versa: `rout`
                    IMPROVING from FEASIBLE to OPTIMAL is also reported, because
                    an unnoticed improvement is how the board got stale).
  3. NODES       -- the PRIMARY tripwire, because node counts are LOAD-INVARIANT
                    and wall time is not. This repo has already published a
                    load-biased number once; nodes cannot be biased by a busy
                    machine. Tight threshold.
  4. WALL        -- secondary, wide threshold, because a loaded CI box will move
                    it. A wall regression with UNCHANGED nodes is the signature
                    of the prelude-tax/pump-budget class of defect and is called
                    out separately.
  5. LIMIT-INVARIANCE -- solve twice, at a short and a long --time-limit. If the
                    wall grows with the deadline the solver is spending the
                    user's patience rather than the model's work. This is a real
                    defect class here: gen was 0.597s at limit 2 and 1.154s at
                    limit 60 on a BYTE-IDENTICAL nine-node tree.

USAGE
  corpus_guard.py --baseline          capture the current state as the baseline
  corpus_guard.py --check             compare against it; exit 1 on any FAIL
  corpus_guard.py --check --json OUT  also write the full measurement

Exit codes: 0 clean (warnings allowed), 1 regression, 2 harness/setup problem.
"""
import argparse, json, math, os, subprocess, sys, time
from datetime import datetime, timezone

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BASELINE = os.path.join(REPO, 'reports', 'corpus-baseline.json')
HISTORY = os.path.join(REPO, 'reports', 'corpus-history.jsonl')
SOLVER = os.path.join(REPO, 'target', 'release', 'examples', 'mps_solve')

# Known optima. An answer that does not match one of these is a CORRECTNESS
# failure, not a performance one, and is never downgraded to a warning.
OPTIMA = {
    'blend2': 7.598985, 'dcmulti': 188182.0, 'flugpl': 1201500.0,
    'gen': 112313.362718, 'gt2': 21166.0, 'khb05250': 106940226.0,
    'mas76': 40005.054142, 'misc07': 2810.0, 'mod010': 6548.0,
    'p0201': 7615.0, 'pk1': 11.0, 'qiu': -132.873136947,
    'qnet1': 16029.692681, 'rout': 1077.56, 'air03': 340160.0,
    'markshare1': 1.0, 'markshare2': 1.0,
}
# Unsolved residuals: tracked for INCUMBENT QUALITY, never expected OPTIMAL.
RESIDUALS = {'air05': 26374.0, 'mas74': 11801.185729}

NODE_TOL = 0.05     # tight DEFAULT: 17 of 19 instances are bit-stable across repeats

# PER-INSTANCE NODE TOLERANCE. The flat 5% above rested on "node counts are
# load-invariant, so this can be tight". That is FALSE for two instances, and the
# guard proved it against itself: on 2026-08-08 it emitted two FAILs in three
# consecutive runs with NO code change in between (air05 109->115, misc07
# 7833->8336). A tripwire that cries wolf is worse than no tripwire.
#
# Measured, 5 repeats at fixed config on an idle machine:
#   misc07   8335 8227 6651 7109 8675   spread 30.4%   <- root cut loop is
#   air05      65   44   65   65   65   spread 47.7%      wall-deadline bounded,
#   gen         9    9    9    9    9   stable            so how many rounds run
#   mod010   2381 2381 2381 2381 2381   stable            is partly temporal
#   qnet1    2058 2058 2058 2058 2058   stable
#   blend2   3882 3882 3882 3882 3882   stable
#
# The bands below exceed the measured spread with margin. This is a REAL LOSS of
# sensitivity on those two instances and is stated rather than hidden: a regression
# smaller than the band is undetectable there. The alternative -- loosening
# NODE_TOL globally -- would forfeit detection on the 17 instances that ARE stable,
# which is where this guard earns its keep. If misc07/air05 sensitivity ever
# matters, take a median of 3 repeats for them instead of widening the band.
NODE_TOL_BY_INSTANCE = {
    'misc07': 0.40,   # measured spread 30.4%
    'air05': 0.60,    # measured spread 47.7%
}
WALL_TOL = 0.30     # load-sensitive, so this is deliberately loose
LIMIT_TOL = 1.25    # wall(long) / wall(short) above this = deadline-denominated


def run(solver, mps, secs, threads=1):
    env = dict(os.environ, AY_MILP_THREADS=str(threads))
    t = time.time()
    try:
        out = subprocess.run([solver, mps, str(secs)], capture_output=True,
                             text=True, env=env, timeout=secs * 3 + 60)
    except subprocess.TimeoutExpired:
        return {'status': 'HARNESS_TIMEOUT', 'obj': None, 'wall': None, 'nodes': None}
    line = (out.stdout.strip().splitlines() or [''])[-1].split()
    if len(line) < 4:
        return {'status': 'NO_OUTPUT', 'obj': None, 'wall': None, 'nodes': None,
                'raw': out.stdout[-400:] + out.stderr[-400:]}
    try:
        return {'status': line[0], 'obj': float(line[1]),
                'wall': float(line[-2]), 'nodes': int(line[-1]),
                'harness_wall': round(time.time() - t, 3)}
    except ValueError:
        return {'status': 'PARSE_ERROR', 'obj': None, 'wall': None, 'nodes': None,
                'raw': ' '.join(line)}


def measure(corpus, solver, limit, short_limit, only=None):
    res = {}
    names = sorted(set(OPTIMA) | set(RESIDUALS))
    for name in names:
        if only and name not in only:
            continue
        mps = os.path.join(corpus, name + '.mps')
        if not os.path.exists(mps):
            continue
        rec = run(solver, mps, limit)
        # Limit-invariance probe: only for instances that finish well inside the
        # short limit, otherwise a short limit merely truncates and tells us
        # nothing (qnet1/misc07/pk1/blend2 all truncate at a tight budget).
        if rec.get('wall') is not None and rec['status'] == 'OPTIMAL' and rec['wall'] < short_limit * 0.5:
            rec['short'] = run(solver, mps, short_limit)
        res[name] = rec
    return res


def compare(base, cur):
    fails, warns, notes = [], [], []
    for name, c in sorted(cur.items()):
        b = base.get(name)
        opt = OPTIMA.get(name)

        # 1. ANSWER -- unconditional
        if opt is not None and c['status'] == 'OPTIMAL' and c['obj'] is not None:
            if abs(c['obj'] - opt) > 1e-9 * max(1.0, abs(opt)):
                fails.append('%s: WRONG ANSWER %r, known optimum %r' % (name, c['obj'], opt))
                continue
        if c['status'] in ('NO_OUTPUT', 'PARSE_ERROR', 'HARNESS_TIMEOUT'):
            fails.append('%s: harness could not measure it (%s)' % (name, c['status']))
            continue

        if b is None:
            notes.append('%s: new instance, no baseline' % name)
            continue

        # 2. STATUS -- both directions. An unnoticed IMPROVEMENT is how the
        #    scoreboard went stale in AY's favour on rout.
        if b['status'] != c['status']:
            if name in RESIDUALS or c['status'] != 'OPTIMAL':
                fails.append('%s: STATUS %s -> %s' % (name, b['status'], c['status']))
            else:
                notes.append('%s: STATUS IMPROVED %s -> %s -- update the baseline and the scoreboard'
                             % (name, b['status'], c['status']))
            continue

        # 3. NODES -- primary, load-invariant
        # `nodes_grew` -- NOT "nodes changed". A wall regression is only EXPLAINED
        # by the search doing more work; if the node count is flat or better and
        # the wall still went up, that is pure overhead and must not be softened
        # to a warning. gen was exactly this shape: 11 -> 9 nodes (better!) while
        # the wall went 0.348s -> 0.550s, and an earlier version of this file
        # downgraded it because it only asked whether nodes had MOVED.
        nodes_grew = False
        if b.get('nodes') and c.get('nodes') is not None and b['nodes'] > 0:
            r = c['nodes'] / b['nodes']
            tol = NODE_TOL_BY_INSTANCE.get(name, NODE_TOL)
            if r > 1 + tol:
                fails.append('%s: NODES %d -> %d (%.2fx, tol %.0f%%)'
                             % (name, b['nodes'], c['nodes'], r, tol * 100))
                nodes_grew = True
            elif r < 1 - tol:
                notes.append('%s: nodes IMPROVED %d -> %d (%.2fx)' % (name, b['nodes'], c['nodes'], r))

        # 4. WALL -- secondary, loose. Same nodes + more wall is the budget-defect
        #    signature and is named as such.
        if b.get('wall') and c.get('wall') is not None and b['wall'] > 0.05:
            r = c['wall'] / b['wall']
            if r > 1 + WALL_TOL:
                if not nodes_grew:
                    fails.append('%s: WALL %.3fs -> %.3fs (%.2fx) at UNCHANGED node count '
                                 '-- overhead regression, not search'
                                 % (name, b['wall'], c['wall'], r))
                else:
                    warns.append('%s: wall %.3fs -> %.3fs (%.2fx)' % (name, b['wall'], c['wall'], r))

        # 5. LIMIT-INVARIANCE
        s = c.get('short')
        if s and s.get('wall') and s['status'] == 'OPTIMAL' and c.get('wall'):
            r = c['wall'] / s['wall']
            if r > LIMIT_TOL:
                fails.append('%s: NOT LIMIT-INVARIANT -- %.3fs at the short limit vs %.3fs at the '
                             'long one (%.2fx). The budget is denominated in the caller\'s '
                             'deadline, not the model.' % (name, s['wall'], c['wall'], r))

    # residual incumbent quality
    for name, opt in RESIDUALS.items():
        b, c = base.get(name), cur.get(name)
        if not b or not c or c.get('obj') is None or b.get('obj') is None:
            continue
        if c['obj'] > b['obj'] * (1 + 1e-6):
            fails.append('%s: RESIDUAL INCUMBENT WORSE %r -> %r (optimum %r)'
                         % (name, b['obj'], c['obj'], opt))
    return fails, warns, notes


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--corpus', default=os.path.expanduser('~/ay-corpus'))
    ap.add_argument('--solver', default=SOLVER)
    ap.add_argument('--limit', type=float, default=120.0)
    ap.add_argument('--short-limit', type=float, default=3.0)
    ap.add_argument('--baseline', action='store_true')
    ap.add_argument('--check', action='store_true')
    ap.add_argument('--json')
    ap.add_argument('--only', nargs='*')
    a = ap.parse_args()

    if not os.path.isdir(a.corpus):
        print('SETUP: corpus not found at %s' % a.corpus, file=sys.stderr); return 2
    if not os.path.exists(a.solver):
        print('SETUP: solver not built at %s' % a.solver, file=sys.stderr); return 2

    cur = measure(a.corpus, a.solver, a.limit, a.short_limit, a.only)
    if not cur:
        print('SETUP: measured nothing -- is the corpus empty?', file=sys.stderr); return 2

    stamp = datetime.now(timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ')
    head = subprocess.run(['git', '-C', REPO, 'rev-parse', '--short', 'HEAD'],
                          capture_output=True, text=True).stdout.strip()
    payload = {'when': stamp, 'head': head, 'limit': a.limit,
               'short_limit': a.short_limit, 'results': cur}

    if a.json:
        with open(a.json, 'w') as f:
            json.dump(payload, f, indent=2, sort_keys=True)

    if a.baseline:
        os.makedirs(os.path.dirname(BASELINE), exist_ok=True)
        with open(BASELINE, 'w') as f:
            json.dump(payload, f, indent=2, sort_keys=True)
        print('baseline written: %d instances at %s (HEAD %s)' % (len(cur), stamp, head))
        return 0

    if not os.path.exists(BASELINE):
        print('SETUP: no baseline; run --baseline first', file=sys.stderr); return 2
    base = json.load(open(BASELINE))

    fails, warns, notes = compare(base['results'], cur)

    with open(HISTORY, 'a') as f:
        f.write(json.dumps({'when': stamp, 'head': head,
                            'fails': len(fails), 'warns': len(warns),
                            'results': cur}, sort_keys=True) + '\n')

    print('=== corpus guard: HEAD %s vs baseline %s (%s) ==='
          % (head, base.get('head', '?'), base.get('when', '?')))
    for n in notes: print('  NOTE  %s' % n)
    for w in warns: print('  WARN  %s' % w)
    for x in fails: print('  FAIL  %s' % x)
    if not (fails or warns or notes):
        print('  clean: %d instances, no drift' % len(cur))
    print('=== %d fail, %d warn, %d note ===' % (len(fails), len(warns), len(notes)))
    return 1 if fails else 0


if __name__ == '__main__':
    sys.exit(main())
