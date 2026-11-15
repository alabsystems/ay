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

WHAT IT CHECKS, and why each tripwire is the shape it is. Every verdict is a
COUNT, since 2026-10-15 (the development design notes DR-37's rule, Trust BUDGET-1): a
wall time is recorded (--json, the history) and decides nothing. A run that its
wall limit ended is COULD NOT RUN (exit 2), never a pass, unless the counts it
had reached are already past the baseline's whole search by more than the
tolerance: counts only grow, and load can only lower what a run reaches before
its limit, so that is a FAIL however the run would have ended.

  1. ANSWER      -- objective must equal the known optimum exactly (rel 1e-9).
                    A wrong answer fails immediately and unconditionally.
  2. STATUS      -- OPTIMAL must not decay to FEASIBLE (or vice versa: `rout`
                    IMPROVING from FEASIBLE to OPTIMAL is also reported, because
                    an unnoticed improvement is how the board got stale). A run
                    that ended at its --limit had its status set by the clock,
                    not the model: it decides by the counts it reached (above),
                    or it is COULD NOT RUN.
  3. NODES       -- the PRIMARY tripwire, because node counts are LOAD-INVARIANT
                    and wall time is not. This repo has already published a
                    load-biased number once; nodes cannot be biased by a busy
                    machine. Tight threshold. A run the limit ended with more
                    nodes than that already FAILs: gt2's 208x explosion is a
                    FAIL whether or not it reaches the limit.
  4. WORK        -- the solver's simplex iterations (`mps_solve --iter-ledger`,
                    its `engine=` count). A count, but not yet shown to hold
                    still the way nodes do: two captures at identical nodes
                    (cbf34d8ce8) differed by up to 2.3 % on the rows with
                    thousands of iterations (air03 28,565 -> 27,925, qnet1
                    108,916 -> 106,935, gen 26,847 -> 26,562) and by one
                    iteration on markshare2 (22 -> 21, 4.8 %), all well inside
                    WORK_TOL. They differed in more than the load (1-minute
                    load 27-35 for the 2026-10-17 13:55 capture, 6-11 for the
                    baseline): they ran different binaries, an mps_solve built
                    before f4f3d585eb and one built on 75f044f480 (f4f3d585eb
                    merged onto main). Which difference moved the work is not
                    measured. More work at an UNCHANGED node count is
                    the signature of the prelude-tax/pump-budget class of defect
                    and is called out separately. Until 2026-10-15 this was a
                    WALL ratio, which a busy neighbour moved on its own. A
                    slowdown that is the same work done slower is not caught
                    here any more: no count sees it, and the wall that did is
                    the neighbours' as much as the solver's.
  5. LIMIT-INVARIANCE -- solve twice, at a short and a long --time-limit, the
                    LIMIT_PROBES (a fixed set: the instances that finish far
                    inside the short limit on a quiet box, as the 2026-08-21
                    baseline measured them, so no wall picks them). Each must
                    run the same search at both: a node count that differs, a
                    status the short run reached before its limit that the long
                    one did not, or work more than LIMIT_TOL higher at the long
                    limit, is the solver spending the user's patience rather
                    than the model's work. A short run its limit ended is COULD
                    NOT RUN, unless it already counted more nodes than the long
                    run's whole search. This is a real defect class here: gen
                    was 0.597s at limit 2 and 1.154s at limit 60 on a
                    BYTE-IDENTICAL nine-node tree.

A CLOCK-STEERED INSTANCE decides only its answer and its status: misc07, whose
root cut loop is wall-deadline bounded (a node spread of 30% at a fixed
configuration, measured below), so its nodes and work are the clock's and are
not checked. If its wall limit ends it short of OPTIMAL, its answer did not
decide, and it is COULD NOT RUN. The RESIDUALS that were measured here until
2026-10-15 (air05, which never proves optimality, and mas74, 109 s of a 120 s
limit on a quiet box) are not measured any more: every verdict they gave (a
status at the limit, nodes, an incumbent) was the wall's, and nothing they
could decide was worth four minutes of solving per run.

WHAT IT IS *NOT*, since 2026-08-20 — and why it was kept anyway.

`scripts/milp_node_gate.py` now pins EXACT node counts for twenty deterministic
instances and runs at every landing that reaches ay-milp (land.sh's milp-node
leg). It is strictly sharper than this file's node
tripwire on the ELEVEN instances they share (air03 blend2 dcmulti gt2 mas76
mod010 p0201 pk1 qiu qnet1 rout), so the temptation was to retire this one. Four
things here had no equivalent there, three of them still do, and each of them
is a defect class this repo has actually shipped:

  * the WORK tripwire at UNCHANGED node count — the prelude-tax/pump-budget
    signature, in simplex iterations (until 2026-10-15 a WALL ratio). The
    ratchet RECORDS `wall_s` and deliberately does not gate it.
  * LIMIT-INVARIANCE — `gen` was 0.597 s at limit 2 and 1.154 s at limit 60 on a
    BYTE-IDENTICAL nine-node tree. No node count can see that; its work count
    can, where the extra time is extra work.
  * RESIDUAL INCUMBENT QUALITY on instances that never prove optimal (air05)
    was a fourth until 2026-10-15, and is DROPPED: a residual runs to the wall
    limit, so its incumbent is what that much time found, which is a clock
    verdict, not a count.
  * SIX instances the ratchet does not or cannot carry: flugpl gen khb05250
    markshare1 markshare2 are simply not in it, and misc07 is in its [flaky]
    list BY NAME because it moves run-to-run at a fixed configuration (here it
    decides its answer and status only). air05 and mas74 were two more until
    2026-10-15. (qiu was another until 2026-08-26; it is a ratchet pin now —
    28 runs at 2,831 nodes across load 2.5..19.7 settled it, and this file's own
    baseline had read 2,831 the whole time.)
    misc07 is the sharp one — its root cut loop is wall-deadline
    bounded (measured spread 30.4 %), so an exact pin would cry wolf. A 40 %
    band watched it until 2026-10-15; since then its nodes are not checked,
    because a band is no count verdict when the clock moves the count, so a
    208x explosion of the `gt2` kind on misc07 is not caught here (that check
    is DROPPED). gt2 itself, and every other instance whose nodes hold still,
    is held at 5 %.

So: NARROW, exact, seconds = the ratchet. BROAD, counted, minutes, nightly and
at a landing that reaches it = this. The two overlap on purpose; neither
subsumes the other.

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
  2. `reports/corpus-baseline.json` was stale by two generations — blend2 3,882
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
  band.) Since 2026-10-15 no tripwire reads the wall, so a recurrence of this
  shape is caught only if it is also more simplex iterations (WORK); the lead
  itself stays open.

IT RUNS ON A BUSY BOX, since 2026-10-15. From 2026-08-26 it refused above
0.35 x cpu_count, because three of its five tripwires were WALL RATIOS (WALL at
30%, LIMIT-INVARIANCE at 1.25x, and STATUS read a 120 s deadline an instance
can be pushed past). The bill, as REPORTED BY TWO AUDITORS and not re-derived
here: 18 FAILs at load ~30, 12 at ~25, 8 at ~3.4 and a mas74 OPTIMAL ->
FEASIBLE flake, all on diffs that could not have caused them, all wall-only at
UNCHANGED node counts; and on 2026-10-14 six wall-clock FAILs at load ~13 on a
landing that could not reach them (the development design notes). On a shared host the
refusal made the gate NOT RUN at every landing. The tripwires are counts now,
the deadline that ends a run is COULD NOT RUN unless its counts already
decided, misc07 decides only its answer and the residuals are gone, so no
verdict moves with the load and the refusal is gone. The
phantom it guarded against is kept below, beside main(), as the measurement
that motivated both changes.

USAGE
  corpus_guard.py --baseline          capture the current state as the baseline
  corpus_guard.py --check             compare against it; exit 1 on any FAIL
  corpus_guard.py --check --json OUT  also write the full measurement

A baseline captured before 2026-10-15 holds no work counts: --check then names
each row's WORK tripwire COULD NOT RUN until --baseline captures them. Stable
rows' nodes are load-invariant, and work moved by at most 4.8 % (markshare2's
one iteration) between two captures (WORK, above), so any host with the
corpus can capture it, but --baseline writes nothing (exit 2) when a row its
counts would hold was decided by the clock: a solve its wall limit ended, a
status short of OPTIMAL or a wrong answer, or a stable instance with no work
count (no ITERLEDGER line).

Exit codes: 0 clean (warnings and notes allowed), 1 regression, 2 COULD NOT
RUN (a harness or setup problem, a run its wall limit ended before its counts
decided, or a --baseline capture the clock decided).
"""
import argparse, json, math, os, re, subprocess, sys, time
from datetime import datetime, timezone

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BASELINE = os.path.join(REPO, 'reports', 'corpus-baseline.json')
HISTORY = os.path.join(REPO, 'reports', 'corpus-history.jsonl')
SOLVER = os.path.join(REPO, 'target', 'release', 'examples', 'mps_solve')

# ONE definition of where the corpus lives, imported rather than re-typed.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from milp_gate_corpus import DEFAULT_CORPUS  # noqa: E402

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
# Those two once had their own bands (40% and 60%), wide enough for the spread
# measured on an idle machine. A band is not a count verdict: the spread is the
# root cut loop's wall deadline, so a loaded host moves it further, by an amount
# nobody measured. Since 2026-10-15 misc07 decides only its answer and its
# status, and air05 (a residual) is not measured. The 16 stable instances keep
# the tight NODE_TOL, which is where this guard earns its keep.
CLOCK_STEERED = ('misc07',)
WORK_TOL = 0.30     # work(now) / work(baseline) above 1 + this, at unchanged nodes
LIMIT_TOL = 1.25    # work(long) / work(short) above this = deadline-denominated
# The limit-invariance probes: every instance the 2026-08-21 baseline solved in
# under half the 3 s short limit (0.02 s to 0.99 s, measured there), named
# once rather than picked by a wall time on whatever host runs the guard.
LIMIT_PROBES = ('dcmulti', 'flugpl', 'gen', 'gt2', 'khb05250', 'markshare1', 'p0201', 'rout')
# A run whose wall reached this share of its --limit, short of OPTIMAL, was
# ended by the clock (a deadline end lands at the limit, not before it).
CLOCK_END = 0.95
ITERLEDGER = re.compile(r'^ITERLEDGER total=\d+ engine=(\d+)', re.MULTILINE)


def run(solver, mps, secs, threads=1):
    """One solve: its status, objective, nodes and work (the ITERLEDGER line's
    `engine=` simplex iterations, which mps_solve prints under --iter-ledger at
    the end of a solve, `total=0 engine=0` when no simplex walk served it; no
    line is no count, `None`, never 0),
    its wall time (recorded, never a verdict), and the --limit it ran under."""
    env = dict(os.environ, AY_MILP_THREADS=str(threads))
    t = time.time()
    try:
        out = subprocess.run([solver, mps, str(secs), '--iter-ledger'], capture_output=True,
                             text=True, env=env, timeout=secs * 3 + 60)
    except subprocess.TimeoutExpired:
        return {'status': 'HARNESS_TIMEOUT', 'obj': None, 'wall': None, 'nodes': None,
                'work': None, 'limit': secs}
    line = (out.stdout.strip().splitlines() or [''])[-1].split()
    if len(line) < 4:
        return {'status': 'NO_OUTPUT', 'obj': None, 'wall': None, 'nodes': None,
                'work': None, 'limit': secs, 'raw': out.stdout[-400:] + out.stderr[-400:]}
    ledger = ITERLEDGER.search(out.stderr)
    try:
        return {'status': line[0], 'obj': float(line[1]),
                'wall': float(line[-2]), 'nodes': int(line[-1]),
                'work': int(ledger.group(1)) if ledger else None, 'limit': secs,
                'harness_wall': round(time.time() - t, 3)}
    except ValueError:
        return {'status': 'PARSE_ERROR', 'obj': None, 'wall': None, 'nodes': None,
                'work': None, 'limit': secs, 'raw': ' '.join(line)}


def ended_on_clock(rec, limit=None):
    """The wall limit, not the model, ended this run: a harness timeout, or a
    status short of OPTIMAL reached at the limit. `limit` stands in for a
    record that does not carry its own (one captured before 2026-10-15)."""
    if rec.get('status') == 'HARNESS_TIMEOUT':
        return True
    wall, secs = rec.get('wall'), rec.get('limit', limit)
    return (rec.get('status') != 'OPTIMAL' and wall is not None and secs is not None
            and wall >= CLOCK_END * secs)


def measure(corpus, solver, limit, short_limit, only=None):
    res = {}
    for name in sorted(OPTIMA):
        if only and name not in only:
            continue
        mps = os.path.join(corpus, name + '.mps')
        if not os.path.exists(mps):
            continue
        rec = run(solver, mps, limit)
        # The limit-invariance probe, for the fixed LIMIT_PROBES only: a long
        # solve that did not reach OPTIMAL decides by its own counts first.
        if name in LIMIT_PROBES and rec['status'] == 'OPTIMAL':
            rec['short'] = run(solver, mps, short_limit)
        res[name] = rec
    return res


def past_the_baseline(name, b, c):
    """The FAILs a run its wall limit ended still decides. Against a baseline
    that finished (OPTIMAL), the nodes and the work a cut-short run reached are
    lower bounds on its whole search: they only grow, and load can only lower
    what a run reaches before its limit. Past the tolerance, the whole search
    is past it too, however the run would have ended."""
    if b is None or b.get('status') != 'OPTIMAL':
        return []
    out = []
    if b.get('nodes') and c.get('nodes') is not None and c['nodes'] > b['nodes'] * (1 + NODE_TOL):
        out.append('%s: NODES %d -> at least %d (%.2fx or more, tol %.0f%%), counted before the wall '
                   'limit ended the solve' % (name, b['nodes'], c['nodes'], c['nodes'] / b['nodes'],
                                              NODE_TOL * 100))
    if b.get('work') and c.get('work') is not None and c['work'] > b['work'] * (1 + WORK_TOL):
        out.append('%s: WORK %d -> at least %d simplex iterations (%.2fx or more), counted before the '
                   'wall limit ended the solve' % (name, b['work'], c['work'], c['work'] / b['work']))
    return out


def compare(base, cur, limit=None):
    """(fails, warns, notes, could_not_run) for the current run against the
    baseline. Every FAIL is decided by a count or an exact value; the wall
    decides nothing. A run its wall limit ended is COULD NOT RUN, unless the
    counts it reached are already past the baseline's (past_the_baseline)."""
    fails, warns, notes, cnr = [], [], [], []
    for name, c in sorted(cur.items()):
        b = base.get(name)
        opt = OPTIMA.get(name)
        steered = name in CLOCK_STEERED

        # 1. ANSWER -- unconditional
        if opt is not None and c['status'] == 'OPTIMAL' and c['obj'] is not None:
            if abs(c['obj'] - opt) > 1e-9 * max(1.0, abs(opt)):
                fails.append('%s: WRONG ANSWER %r, known optimum %r' % (name, c['obj'], opt))
                continue
        if c['status'] == 'HARNESS_TIMEOUT':
            cnr.append('%s: the harness timeout, the far wall backstop, ended the solve before its '
                       'counts decided' % name)
            continue
        if c['status'] in ('NO_OUTPUT', 'PARSE_ERROR'):
            fails.append('%s: harness could not measure it (%s)' % (name, c['status']))
            continue

        if b is None:
            notes.append('%s: new instance, no baseline' % name)
            continue

        # A run the wall limit ended: its status, and for a clock-steered
        # instance its answer, are the clock's. A stable instance's counts
        # may still decide (past_the_baseline).
        if ended_on_clock(c, limit):
            bound = [] if steered else past_the_baseline(name, b, c)
            if bound:
                fails.extend(bound)
            else:
                cnr.append('%s: the wall limit ended the solve (%s at %ss, baseline %s) before its '
                           '%s decided' % (name, c['status'], c.get('wall'), b.get('status'),
                                           'answer' if steered else 'counts'))
            continue

        # 2. STATUS -- both directions, and the solver's own: the limit did
        #    not end this run. An unnoticed IMPROVEMENT is how the scoreboard
        #    went stale in AY's favour on rout.
        if b['status'] != c['status']:
            if c['status'] == 'OPTIMAL':
                notes.append('%s: STATUS IMPROVED %s -> %s -- update the baseline and the scoreboard'
                             % (name, b['status'], c['status']))
            else:
                fails.append('%s: STATUS %s -> %s' % (name, b['status'], c['status']))
            continue

        # A clock-steered instance decides nothing more: its nodes and work are
        # its root cut loop's wall deadline (CLOCK_STEERED).
        if steered:
            continue

        # 3. NODES -- primary, load-invariant
        # `nodes_grew` -- NOT "nodes changed". More work is only EXPLAINED by
        # the search growing; if the node count is flat or better and the work
        # still went up, that is pure overhead and must not be softened to a
        # warning. gen was exactly this shape: 11 -> 9 nodes (better!) while
        # the wall went 0.348s -> 0.550s, and an earlier version of this file
        # downgraded it because it only asked whether nodes had MOVED.
        nodes_grew = False
        if b.get('nodes') and c.get('nodes') is not None and b['nodes'] > 0:
            r = c['nodes'] / b['nodes']
            if r > 1 + NODE_TOL:
                fails.append('%s: NODES %d -> %d (%.2fx, tol %.0f%%)'
                             % (name, b['nodes'], c['nodes'], r, NODE_TOL * 100))
                nodes_grew = True
            elif r < 1 - NODE_TOL:
                notes.append('%s: nodes IMPROVED %d -> %d (%.2fx)' % (name, b['nodes'], c['nodes'], r))

        # 4. WORK -- secondary, loose. Same nodes + more simplex iterations is the
        #    budget-defect signature and is named as such.
        if b.get('work') is None:
            cnr.append('%s: WORK: the baseline holds no work count for it; capture one with --baseline'
                       % name)
        elif c.get('work') is None:
            cnr.append('%s: WORK: the solver printed no ITERLEDGER line, so its work was not counted' % name)
        elif c['work'] > b['work'] * (1 + WORK_TOL):
            grew = '%.2fx' % (c['work'] / b['work']) if b['work'] else 'from none'
            if not nodes_grew:
                fails.append('%s: WORK %d -> %d simplex iterations (%s) at UNCHANGED node count '
                             '-- overhead regression, not search' % (name, b['work'], c['work'], grew))
            else:
                warns.append('%s: work %d -> %d (%s)' % (name, b['work'], c['work'], grew))

        # 5. LIMIT-INVARIANCE -- the same search at both limits, by its counts.
        if name in LIMIT_PROBES:
            fails_s, cnr_s = limit_invariance(name, c)
            fails.extend(fails_s)
            cnr.extend(cnr_s)
    return fails, warns, notes, cnr


def limit_invariance(name, c):
    """(fails, could_not_run) for one probe: its long solve `c`, OPTIMAL, and
    the short-limit solve beside it."""
    s = c.get('short')
    if s is None:
        return [], ['%s: LIMIT-INVARIANCE: no short-limit solve was run' % name]
    if s['status'] in ('NO_OUTPUT', 'PARSE_ERROR'):
        return ['%s: LIMIT-INVARIANCE: harness could not measure the short-limit solve (%s)'
                % (name, s['status'])], []
    if ended_on_clock(s):
        if s.get('nodes') is not None and c.get('nodes') is not None and s['nodes'] > c['nodes']:
            return ['%s: NOT LIMIT-INVARIANT -- at least %d nodes at the short limit, %d in the long '
                    'run\'s whole search' % (name, s['nodes'], c['nodes'])], []
        return [], ['%s: LIMIT-INVARIANCE: the short-limit solve ended %s at its limit, before its '
                    'counts decided' % (name, s['status'])]
    if s['status'] != 'OPTIMAL':
        return ['%s: NOT LIMIT-INVARIANT -- the short-limit solve stopped %s before its limit, the '
                'long one ended OPTIMAL. The search is steered by the caller\'s deadline, not the '
                'model.' % (name, s['status'])], []
    if s.get('nodes') != c.get('nodes'):
        return ['%s: NOT LIMIT-INVARIANT -- %s nodes at the short limit vs %s at the long one. The '
                'search is steered by the caller\'s deadline, not the model.'
                % (name, s.get('nodes'), c.get('nodes'))], []
    if s.get('work') is None or c.get('work') is None:
        return [], ['%s: LIMIT-INVARIANCE: a solve printed no ITERLEDGER line' % name]
    if c['work'] > s['work'] * LIMIT_TOL:
        return ['%s: NOT LIMIT-INVARIANT -- %d simplex iterations at the short limit vs %d at the '
                'long one on the same %s nodes. The budget is denominated in the caller\'s deadline, '
                'not the model.' % (name, s['work'], c['work'], c.get('nodes'))], []
    return [], []


def baseline_refusals(cur):
    """Why a --baseline capture must not be written, one line per row: a row
    whose status the clock set, or whose counts the guard reads are absent,
    would hold the clock's numbers as the model's, and --check would then
    measure against them (a FEASIBLE row's next OPTIMAL is a STATUS IMPROVED
    note, and its nodes and work are never compared again)."""
    out = []
    for name, rec in sorted(cur.items()):
        opt = OPTIMA.get(name)
        if rec['status'] in ('HARNESS_TIMEOUT', 'NO_OUTPUT', 'PARSE_ERROR'):
            out.append('%s: %s' % (name, rec['status']))
        elif rec['status'] != 'OPTIMAL':
            out.append('%s: %s at %ss of its %ss limit, not OPTIMAL' % (name, rec['status'], rec.get('wall'),
                                                                      rec.get('limit')))
        elif opt is not None and abs(rec['obj'] - opt) > 1e-9 * max(1.0, abs(opt)):
            out.append('%s: OPTIMAL at %r, known optimum %r' % (name, rec['obj'], opt))
        elif name not in CLOCK_STEERED and rec.get('work') is None:
            out.append('%s: no work count (no ITERLEDGER line)' % name)
    return out


# THE LOAD PHANTOM: the measurement that put a quiet-box refusal in front of this
# guard (2026-08-26) and that, with its tripwires turned into counts, took it out
# again (2026-10-15). From the refusal's docstring, as written:
#
# THE PHANTOM, REPRODUCED ON DEMAND. Same box, 14 cpus, HEAD c7462bd40, the
# UNMODIFIED release binary, the committed baseline, `--only gen mod010 qnet1
# dcmulti p0201`, under 16 synthetic spinners at 1-minute load 27.9:
#
#     guard ON      -> exit 2, SETUP, nothing measured
#     --allow-busy  -> exit 1, FOUR FAILs, every one wall-only at an
#                      UNCHANGED node count:
#                        dcmulti  0.280s -> 0.367s (1.31x)
#                        mod010   1.544s -> 2.506s (1.62x)
#                        p0201    0.317s -> 0.444s (1.40x)
#                        qnet1    4.663s -> 8.482s (1.82x)
#
# Four regressions with no commit behind them, from nothing but neighbours.
# That is the run that gets a gate muted, and `--allow-busy` is now the only
# way to produce it.
#
# AND IT IS NOT A MUTE BUTTON -- the failure mode of adding a guard like this
# is that it swallows REAL regressions too, which would be strictly worse than
# the status quo. Both halves were measured on the same quiet box, with the
# guard ON and no override:
#
#     `--only qiu`, shipped default, load 4.5   -> 0 fail, exit 0
#     `--only qiu`, same binary with the tall-cold-dual rescue disarmed,
#     load 3.1                                  -> exit 1,
#         `FAIL qiu: NODES 2831 -> 6529 (2.31x, tol 5%)`
#
# A genuine 2.31x node regression is still a FAIL. Only the wall-ratio
# phantoms are gone, and only because they are no longer measured at all.
# `--baseline` is behind the same check and was verified to refuse too (exit 2
# at load 12.3, `reports/corpus-baseline.json` untouched): a baseline captured
# under contention is the same defect one release later and harder to see.
#
# ONE PRACTICAL CONSEQUENCE, stated because it will bite someone: this guard's
# OWN sweep is minutes of single-threaded solving and contributes ~1.0 to the
# 1-minute average, so back-to-back runs can push themselves over the line.
# Observed here: a run that started at load 4.5 left the box at 5.3 and the
# next invocation refused. Start below ~3.9, or wait between runs.
#

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
    a = ap.parse_args()

    if not os.path.isdir(a.corpus):
        print('SETUP: corpus not found at %s\n'
              '       rebuild it: scripts/milp_gate_corpus.py --build'
              % a.corpus, file=sys.stderr); return 2
    if not os.path.exists(a.solver):
        print('SETUP: solver not built at %s' % a.solver, file=sys.stderr); return 2
    # No quiet-box refusal: every verdict is a count, which a busy neighbour
    # cannot move, and a run its wall limit ends is COULD NOT RUN unless its
    # counts already decided (see the load phantom above main()). A --baseline
    # the clock decided is refused below (baseline_refusals).

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
        refused = baseline_refusals(cur)
        if refused:
            print('COULD NOT RUN: --baseline writes nothing; the clock, not the model, decided these '
                  'rows (re-run it on a host where they finish):', file=sys.stderr)
            for row in refused:
                print('  %s' % row, file=sys.stderr)
            return 2
        os.makedirs(os.path.dirname(BASELINE), exist_ok=True)
        with open(BASELINE, 'w') as f:
            json.dump(payload, f, indent=2, sort_keys=True)
        print('baseline written: %d instances at %s (HEAD %s)' % (len(cur), stamp, head))
        return 0

    if not os.path.exists(BASELINE):
        print('SETUP: no baseline; run --baseline first', file=sys.stderr); return 2
    with open(BASELINE) as baseline_file:
        base = json.load(baseline_file)
    try:
        provenance_overrides = validate_provenance_overrides(base)
    except ValueError as error:
        print('SETUP: invalid baseline provenance: %s' % error, file=sys.stderr)
        return 2

    fails, warns, notes, cnr = compare(base['results'], cur, base.get('limit'))

    with open(HISTORY, 'a') as f:
        f.write(json.dumps({'when': stamp, 'head': head,
                            'fails': len(fails), 'warns': len(warns), 'could_not_run': len(cnr),
                            'results': cur}, sort_keys=True) + '\n')

    print('=== corpus guard: HEAD %s vs full-capture baseline %s (%s) ==='
          % (head, base.get('head', '?'), base.get('when', '?')))
    if provenance_overrides:
        print('  baseline row overrides: %s' %
              format_provenance_overrides(provenance_overrides))
    for n in notes: print('  NOTE  %s' % n)
    for w in warns: print('  WARN  %s' % w)
    for x in cnr: print('  COULD NOT RUN  %s' % x)
    for x in fails: print('  FAIL  %s' % x)
    if not (fails or warns or notes or cnr):
        print('  clean: %d instances, no drift' % len(cur))
    print('=== %d fail, %d could not run, %d warn, %d note ===' % (len(fails), len(cnr), len(warns), len(notes)))
    # A drift a count decided is the finding; otherwise a tripwire that did not
    # decide is COULD NOT RUN, never a pass.
    if fails:
        return 1
    return 2 if cnr else 0


if __name__ == '__main__':
    sys.exit(main())
