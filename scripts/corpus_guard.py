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

WHAT IT IS *NOT*, since 2026-08-20 — and why it was kept anyway.

`scripts/milp_node_gate.py` now pins EXACT node counts for twenty deterministic
instances and runs pre-push. It is strictly sharper than this file's node
tripwire on the ELEVEN instances they share (air03 blend2 dcmulti gt2 mas76
mod010 p0201 pk1 qiu qnet1 rout), so the temptation was to retire this one. Four
things here have no equivalent there, and each of them is a defect class this
repo has actually shipped:

  * the WALL tripwire at UNCHANGED node count — the prelude-tax/pump-budget
    signature. The ratchet RECORDS `wall_s` and deliberately does not gate it.
  * LIMIT-INVARIANCE — `gen` was 0.597 s at limit 2 and 1.154 s at limit 60 on a
    BYTE-IDENTICAL nine-node tree. No node count can see that.
  * RESIDUAL INCUMBENT QUALITY on instances that never prove optimal (air05).
    The ratchet pins only instances that terminate.
  * EIGHT instances the ratchet does not or cannot carry: air05 flugpl gen
    khb05250 markshare1 markshare2 are simply not in it, and misc07 mas74 are
    in its [flaky] list BY NAME because they move run-to-run at a fixed
    configuration. (qiu was a ninth until 2026-08-26; it is a ratchet pin now —
    28 runs at 2,831 nodes across load 2.5..19.7 settled it, and this file's own
    baseline had read 2,831 the whole time.)
    misc07 is the sharp one — its root cut loop is wall-deadline
    bounded (measured spread 30.4 %), so an exact pin would cry wolf, but a 40 %
    band still catches a 208x explosion of the `gt2` kind. A banded gate is the
    only kind that can watch a non-deterministic instance at all, and that is
    precisely what the exact ratchet gives up in exchange for its sharpness.

So: NARROW, exact, seconds, pre-push = the ratchet. BROAD, banded, minutes,
nightly = this. The two overlap on purpose; neither subsumes the other.

BASELINE PROVENANCE. `head` and `when` name the last full-corpus capture. A
hand-measured row must not silently inherit that identity: it belongs in the
top-level `provenance_overrides` map with the source revision that was measured
and the commit that recorded it. An unknown capture time is `null`, not an
invented timestamp. A fresh `--baseline` capture clears the override map.

TWO THINGS ABOUT THIS FILE WERE FALSE UNTIL 2026-08-20, and both are the reason
it caught none of the above in practice:

  1. `--corpus` defaulted to `~/ay-corpus`, which HAS NEVER EXISTED on this box.
     Every default invocation exited 2 (SETUP) and nobody noticed, because
     nothing invoked it. It now defaults to the canonical corpus that
     `scripts/milp_gate_corpus.py` owns and `.milp_gate_corpus.tsv` pins.
  2. the development design notes was stale by two generations — blend2 3,882
     is the PRE-REGRESSION value (the real, bisected 3,882 -> 9,070 regression at
     dd591eb1b is unfixed and deliberately not reverted, so 9,070 is the current
     truth), gt2 5,094 and dcmulti 763 likewise. A baseline nobody can pass is
     indistinguishable from a baseline nobody runs.

     RE-BASELINED 2026-08-20 (stamped 2026-08-21T01:07:33Z) at HEAD 814b23485,
     deliberately, from one full 5m09s run. What moved, in nodes, in the eight
     days from 37314be67:

         blend2   3,882 -> 9,070   the dd591eb1b regression. UNFIXED, and now the
                                   pin, because pretending 3,882 is current makes
                                   the gate permanently red and a permanently red
                                   gate is a muted gate.
         mas76  490,992 -> 273,252 an unratcheted IMPROVEMENT (0.56x). It is the
                                   ratchet's pin already.
         misc07   7,579 -> 6,101   inside its own 40% band; misc07 moves anyway.
         air05       65 -> 104     residual, incumbent NOT worse. 1.60x, which is
                                   exactly its 60% band edge and did not fail by
                                   a hair -- if it moves again, widen the band on
                                   evidence or take a median of 3, do not shave it.
         gt2      5,094 -> 4,954   dcmulti 763 -> 761, qiu 4,111 -> 4,121,
                                   mas74 2,520,696 -> 2,522,802: all inside band.
         (unchanged: air03 flugpl gen khb05250 markshare1 markshare2 mod010
          p0201 pk1 qnet1 rout)

  OPEN LEAD, CARRIED FORWARD SO THE RE-BASELINE DOES NOT SWALLOW IT: `gen` went
  0.530s -> 0.703s at a BYTE-IDENTICAL nine-node tree, i.e. 1.31x of pure
  overhead, and it is not noise -- five repeats on a quiet box read 0.694 0.696
  0.698 0.697 0.691 (spread 1.0%), same objective, same 9 nodes. That is this
  file's tripwire #4 firing correctly on its first real run, and it is exactly
  the shape (`gen`, unchanged nodes, more wall) that motivated the tripwire. It
  is UNBISECTED. The re-baseline pins 0.703, so the next occurrence will be
  measured from there. THIS COMMENT IS WHERE THE OLD 0.530s IS PRESERVED —
  the development design notes is gitignored (.gitignore:392), never ships
  with a commit, and holds only the new record, so it cannot serve as the
  historical trail. If you move this number, move it here.
  (`gen` is the ONLY instance whose wall moved without its node count. Every
  other wall delta in the same run tracked a node delta or was inside the 30%
  band.)

IT REFUSES TO RUN ON A BUSY BOX, since 2026-08-26 and not before. Three of the
five tripwires above are WALL RATIOS (#4 at 30%, #5 at 1.25x, and #2 reads a
120 s deadline an instance can be pushed past), so this guard is MORE
load-coupled than the node ratchet next door -- which has refused above
0.35 x cpu_count since it was written, while this file had no such check at all.
The bill, as REPORTED BY TWO AUDITORS and not re-derived here: 18 FAILs at load
~30, 12 at ~25, 8 at ~3.4 and a mas74 OPTIMAL -> FEASIBLE flake, all on diffs
that could not have caused them, all wall-only at UNCHANGED node counts. The
MECHANISM was reproduced on demand and is in `quiet_box_ok`, which also records
why the threshold is the ratchet's rather than a tighter one invented here, and
why that makes this a PARTIAL fix.

USAGE
  corpus_guard.py --baseline          capture the current state as the baseline
  corpus_guard.py --check             compare against it; exit 1 on any FAIL
  corpus_guard.py --check --json OUT  also write the full measurement
  corpus_guard.py --check --allow-busy   measure anyway (only to reproduce a
                                      failure you already have in hand)

Exit codes: 0 clean (warnings allowed), 1 regression, 2 harness/setup problem.
"""
import argparse, json, math, os, subprocess, sys, time
from datetime import datetime, timezone

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BASELINE = os.path.join(REPO, 'reports', 'corpus-baseline.json')
HISTORY = os.path.join(REPO, 'reports', 'corpus-history.jsonl')
SOLVER = os.path.join(REPO, 'target', 'release', 'examples', 'mps_solve')

# ONE definition of where the corpus lives, imported rather than re-typed.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from milp_gate_corpus import DEFAULT_CORPUS  # noqa: E402
# ...and ONE definition of the quiet-box precondition, for the same reason. This
# file had NO load guard at all until 2026-08-26 while the ratchet next door
# refused above 0.35 x cpu_count, so the BROADER and MORE load-coupled of the two
# gates was the unguarded one. See `quiet_box_ok` below.
from milp_node_gate import busy_box  # noqa: E402

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
# The blend2 VALUE above is superseded (it is 9,070 since dd591eb1b, re-baselined
# 2026-08-20) but the OBSERVATION -- bit-stable across five repeats -- still holds
# and is why it can be pinned EXACTLY by `scripts/milp_node_gate.py`. The row is
# left as measured rather than edited, because a measurement table that gets
# quietly updated to whatever is current stops being evidence of anything.
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


def quiet_box_ok(allow_busy):
    """False on a busy box -- the caller's cue for SETUP (2), never FAIL (1).

    Exactly the precondition `scripts/milp_node_gate.py` has always had, imported
    from it rather than re-typed.

    THIS FILE HAD NO LOAD GUARD FOR SIX DAYS AFTER IT STARTED BEING RUN, and it
    is the gate that needs one MOST -- the ratchet next door pins only nodes and
    explicitly does not gate `wall_s`, whereas tripwires #4 (WALL at 30%) and #5
    (LIMIT-INVARIANCE at 1.25x) here are wall ratios, and tripwire #2 (STATUS)
    reads a 120 s deadline that contention can push an instance past. Every one
    of those is a ratio the machine's neighbours can move without a commit.

    WHAT IT COST, reported by two independent auditors of this file's output and
    NOT re-derived here (their run logs are not in the tree; the counts are
    theirs, the mechanism below is reproduced): 18 FAILs at load ~30, 12 at load
    ~25, 8 at load ~3.4, plus a `mas74` OPTIMAL -> FEASIBLE flake -- every
    node-bearing one wall-only at an UNCHANGED node count, on diffs that could
    not have caused them. One of them nearly filed a phantom regression.

    THE THRESHOLD IS DELIBERATELY THE RATCHET'S, imported and not re-tuned, and
    that is a partial fix stated as such: 0.35 x cpu_count is 4.9 on this
    14-core box, so the recorded 8-FAIL run at load ~3.4 would still have gone
    through. Tightening it here alone would fork the two gates' notion of
    "quiet" on no evidence. If a quiet-box run ever produces wall-only FAILs
    again, the fix is a MEDIAN OF THREE for the wall tripwire, not a lower
    number here -- a threshold shaved to fit one observation is folklore.

    THE PHANTOM, REPRODUCED ON DEMAND. Same box, 14 cpus, HEAD c7462bd40, the
    UNMODIFIED release binary, the committed baseline, `--only gen mod010 qnet1
    dcmulti p0201`, under 16 synthetic spinners at 1-minute load 27.9:

        guard ON      -> exit 2, SETUP, nothing measured
        --allow-busy  -> exit 1, FOUR FAILs, every one wall-only at an
                         UNCHANGED node count:
                           dcmulti  0.280s -> 0.367s (1.31x)
                           mod010   1.544s -> 2.506s (1.62x)
                           p0201    0.317s -> 0.444s (1.40x)
                           qnet1    4.663s -> 8.482s (1.82x)

    Four regressions with no commit behind them, from nothing but neighbours.
    That is the run that gets a gate muted, and `--allow-busy` is now the only
    way to produce it.

    AND IT IS NOT A MUTE BUTTON -- the failure mode of adding a guard like this
    is that it swallows REAL regressions too, which would be strictly worse than
    the status quo. Both halves were measured on the same quiet box, with the
    guard ON and no override:

        `--only qiu`, shipped default, load 4.5   -> 0 fail, exit 0
        `--only qiu`, same binary with the tall-cold-dual rescue disarmed,
        load 3.1                                  -> exit 1,
            `FAIL qiu: NODES 2831 -> 6529 (2.31x, tol 5%)`

    A genuine 2.31x node regression is still a FAIL. Only the wall-ratio
    phantoms are gone, and only because they are no longer measured at all.
    `--baseline` is behind the same check and was verified to refuse too (exit 2
    at load 12.3, the development design notes untouched): a baseline captured
    under contention is the same defect one release later and harder to see.

    ONE PRACTICAL CONSEQUENCE, stated because it will bite someone: this guard's
    OWN sweep is minutes of single-threaded solving and contributes ~1.0 to the
    1-minute average, so back-to-back runs can push themselves over the line.
    Observed here: a run that started at load 4.5 left the box at 5.3 and the
    next invocation refused. Start below ~3.9, or wait between runs.
    """
    busy, load, cpus = busy_box()
    if not busy or allow_busy:
        return True
    print('SETUP: load average %.1f on %d cpus -- this guard is only valid on a '
          'quiet box.\n       Its WALL (30%%), LIMIT-INVARIANCE (1.25x) and STATUS '
          'tripwires are ratios a\n       busy neighbour moves on its own. At load '
          '27.9 on this box an UNMODIFIED\n       binary produced FOUR FAILs -- '
          'dcmulti 1.31x, mod010 1.62x, p0201 1.40x,\n       qnet1 1.82x -- every one '
          'wall-only at an UNCHANGED node count.\n'
          '       Wait, or pass --allow-busy to reproduce a failure you already have.'
          % (load, cpus), file=sys.stderr)
    return False


def validate_provenance_overrides(payload):
    """Return a validated per-row provenance map for a baseline payload."""
    overrides = payload.get('provenance_overrides', {})
    if not isinstance(overrides, dict):
        raise ValueError('provenance_overrides must be an object')
    results = payload.get('results', {})
    for name, provenance in overrides.items():
        if name not in results:
            raise ValueError('provenance override names missing result %r' % name)
        if not isinstance(provenance, dict):
            raise ValueError('provenance override for %r must be an object' % name)
        for field in ('measured_head', 'recorded_in'):
            value = provenance.get(field)
            if not isinstance(value, str) or not value:
                raise ValueError('%s for %r must be a nonempty string' % (field, name))
        measured_when = provenance.get('measured_when')
        if measured_when is not None and not isinstance(measured_when, str):
            raise ValueError('measured_when for %r must be a string or null' % name)
    return overrides


def format_provenance_overrides(overrides):
    """Render deterministic, explicit provenance for hand-measured rows."""
    return ', '.join(
        '%s@%s [recorded %s]' %
        (name, provenance['measured_head'], provenance['recorded_in'])
        for name, provenance in sorted(overrides.items())
    )


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--corpus', default=DEFAULT_CORPUS,
                    help='directory of .mps models (default %(default)s)')
    ap.add_argument('--solver', default=SOLVER)
    ap.add_argument('--limit', type=float, default=120.0)
    ap.add_argument('--short-limit', type=float, default=3.0)
    ap.add_argument('--baseline', action='store_true')
    ap.add_argument('--check', action='store_true')
    ap.add_argument('--json')
    ap.add_argument('--only', nargs='*')
    ap.add_argument('--allow-busy', action='store_true',
                    help='skip the load-average precondition (see quiet_box_ok: '
                         'the wall and limit-invariance tripwires are ratios that '
                         'contention moves on their own)')
    a = ap.parse_args()

    if not os.path.isdir(a.corpus):
        print('SETUP: corpus not found at %s\n'
              '       rebuild it: scripts/milp_gate_corpus.py --build'
              % a.corpus, file=sys.stderr); return 2
    if not os.path.exists(a.solver):
        print('SETUP: solver not built at %s' % a.solver, file=sys.stderr); return 2
    # Before ANY solve, and before `--baseline` too: a baseline captured on a busy
    # box bakes the contention into the pin, which is the same defect one release
    # later and harder to see.
    if not quiet_box_ok(a.allow_busy):
        return 2

    cur = measure(a.corpus, a.solver, a.limit, a.short_limit, a.only)
    if not cur:
        print('SETUP: measured nothing -- is the corpus empty?', file=sys.stderr); return 2

    stamp = datetime.now(timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ')
    head = subprocess.run(['git', '-C', REPO, 'rev-parse', '--short', 'HEAD'],
                          capture_output=True, text=True).stdout.strip()
    payload = {'when': stamp, 'head': head, 'limit': a.limit,
               'short_limit': a.short_limit, 'results': cur,
               'provenance_overrides': {}}

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
    try:
        provenance_overrides = validate_provenance_overrides(base)
    except ValueError as error:
        print('SETUP: invalid baseline provenance: %s' % error, file=sys.stderr)
        return 2

    fails, warns, notes = compare(base['results'], cur)

    with open(HISTORY, 'a') as f:
        f.write(json.dumps({'when': stamp, 'head': head,
                            'fails': len(fails), 'warns': len(warns),
                            'results': cur}, sort_keys=True) + '\n')

    print('=== corpus guard: HEAD %s vs full-capture baseline %s (%s) ==='
          % (head, base.get('head', '?'), base.get('when', '?')))
    if provenance_overrides:
        print('  baseline row overrides: %s' %
              format_provenance_overrides(provenance_overrides))
    for n in notes: print('  NOTE  %s' % n)
    for w in warns: print('  WARN  %s' % w)
    for x in fails: print('  FAIL  %s' % x)
    if not (fails or warns or notes):
        print('  clean: %d instances, no drift' % len(cur))
    print('=== %d fail, %d warn, %d note ===' % (len(fails), len(warns), len(notes)))
    return 1 if fails else 0


if __name__ == '__main__':
    sys.exit(main())
