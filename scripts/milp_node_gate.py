#!/usr/bin/env python3
# ay-script: milp-node-gate
"""
THE DETERMINISTIC NODE RATCHET -- exact node-count pins for the MILP corpus.

WHY THIS EXISTS, in one sentence: a deterministic 2.34x node regression on
blend2 (3,882 -> 9,070, bisected to dd591eb1b "big-M indicator cut economy")
landed on main and cleared the standing gate UNTOUCHED, because the standing
gate was four instances (gt2 / mas76 / pk1 / p0548) re-measured by hand and
blend2 was not one of them.

That is the whole failure. The four are not a corpus; they are the four somebody
happened to type. Fifteen more instances are just as deterministic on this box
and were watching nothing.

  WHAT IT PINS.  Twenty instances, EXACT node counts, EXACT objective, EXACT
                 status. No tolerance band. These twenty are bit-stable across
                 repeats on a quiet machine, so a band would only buy the right
                 to miss a regression smaller than the band -- and it would also
                 hide IMPROVEMENTS, which have to be ratcheted deliberately or
                 the pin decays into folklore.

  WHAT IT WILL NOT PIN, and why the exclusion is the load-bearing half:

     mas74 misc07 p2756 nw04

                 all four move run-to-run at a fixed configuration. misc07's
                 root cut loop is WALL-DEADLINE bounded (measured spread 30.4%
                 over five repeats), and nw04 is budget-coupled at short limits
                 -- it fooled a prior round by agreeing across two quiet runs and
                 then moving. A gate that cries wolf gets muted, and a muted gate
                 is worse than no gate. They stay OUT, by name, in
                 `.milp_node_baseline.toml`'s `[flaky]` section so that "why
                 isn't misc07 here" has an answer in the file itself.

  qiu WAS A FIFTH, AND THE EXCLUSION HAD GONE STALE -- which cost this gate its
                 only view of a shipped disjunct. Two facts, both measured here
                 on 2026-08-26:

                 1. IT IS DETERMINISTIC NOW. 29 solves at the shipped default, 28
                    completed (the 29th killed by an external SIGTERM, rc 143,
                    and recorded as killed rather than counted); 28 of 28 gave
                    2,831 nodes / -132.873136947 / OPTIMAL and the same GMICUTS
                    separation digest (n=16, fc7d711a3895b1ff). Spanning
                    1-minute load 2.5..19.7 on 14 cpus and spanning --limit
                    60/120/300 interleaved, so unlike blend2 and mod010 its tree
                    is not deadline-coupled either. The old entry ("moves
                    run-to-run") was recorded on an OLDER engine, when qiu drifted
                    3,946..4,121 across six runs; 6715ed282 later took it 4,121 ->
                    2,831 and nobody re-opened the exclusion.

                 2. IT WAS THE ONLY WITNESS TO A SHIPPED CODE PATH. qiu (1,192 x
                    840) is the only one of the 30 canonical instances whose shape
                    satisfies `m >= 1,000 && n < m` and therefore the only one that
                    arms `FloatLp::tall_cold_dual` -- the warm-failure cold-dual
                    disjunct in simplex.rs. With qiu excluded this gate reported
                    `0 fail` at --tier all against a build with that disjunct
                    disarmed; with qiu pinned the same build FAILS on qiu --
                    `NODES expected 2831 actual 6506 (2.30x, REGRESSION)`. A gate
                    that cannot see a disjunct must not be cited as safety
                    evidence for it.

                    That the DISARMED arm spans a range while the default does not
                    is the point, not a caveat: interleaved A,B,A,B on one binary
                    gave 2831/2831/2831/2831 against 6511/6499/6504, and across
                    every disarmed run taken here (seven) the answer was one of
                    FIVE distinct values in 6,499..6,529. Whatever the old "qiu
                    moves" note was watching, it was not the shipped default.

                 The cost is real and is stated rather than buried: qiu is ~35 s,
                 so `--tier all` roughly doubles -- 42.0/42.7 s at nineteen
                 instances against 73.6/75.9/76.3/81.1 s at twenty, same binary,
                 same quiet box. It is tier "slow" for that reason and stays out
                 of the pre-merge lane, which is unchanged at 7.0 s / 14.

  IT REFUSES TO RUN ON A BUSY BOX, and this is not decoration. "Node counts are
                 load-invariant" is the premise the whole gate rests on and it is
                 only APPROXIMATELY true: two of the twenty have a root cut loop
                 whose round count is bounded by a SHARE of the wall deadline, so
                 contention silently buys fewer rounds and a different tree.
                 Measured here, same binary, same corpus, `--tier fast`:

                     quiet box            blend2 9,070   mod010 2,381
                     under a concurrent   blend2 8,995   mod010 2,291
                     `cargo test` (load
                     avg 43 on 14 cores)

                 Both would have been reported as REGRESSIONS-with-no-commit --
                 the exact way a gate earns its way into everyone's ignore list.
                 So the gate reads the 1-minute load average first and exits 2
                 (SETUP, not clean, not fail) above 0.35 x cpu_count. Override
                 with `--allow-busy` only to reproduce a failure you already have.

                 SHARED, since 2026-08-26: `busy_box()` and `LOAD_FRACTION` below
                 are imported by `scripts/corpus_guard.py`, which had NO load
                 guard at all while being the more load-coupled of the two (it
                 gates WALL ratios; this file records `wall_s` and gates only
                 nodes). One definition, one threshold, one idiom.

  THE PIN IS A RATCHET, NOT A SNAPSHOT.  `--check` NEVER writes. A legitimate
                 improvement updates `.milp_node_baseline.toml` with `--ratchet`,
                 which is a separate, deliberate, reviewable command whose diff
                 states old -> new per instance. This is the same contract as the
                 repo's `.code_quality_*_baseline.toml` ratchets, for the same
                 reason: a value a passing change can silently rewrite is not a
                 pin.

  RELATIONSHIP TO scripts/corpus_guard.py.  Different jobs, both wanted, and
                 the instance sets only partly overlap (corpus_guard carries
                 air05/flugpl/gen/khb05250/markshare*/misc07 and none of the nine
                 witness models pinned here). corpus_guard is the BROAD nightly
                 watcher: a 120 s limit, 5%/40%/60% tolerance BANDS, plus
                 wall-time and limit-invariance tripwires that no node count can
                 see. This is the NARROW pre-push ratchet: deterministic
                 instances only, exact equality, seconds not minutes.

                 corpus_guard did not catch blend2 either, for three reasons all
                 fixed on 2026-08-20: its committed baseline read 3,882 (the
                 PRE-regression value), it defaulted to a ~/ay-corpus that does
                 not exist on this box, and nothing ran it. Both now default to
                 the same canonical corpus, and both now run -- this one
                 pre-push and in the nightly, that one in the nightly.

COST (measured, quiet box, aarch64-apple-darwin, release + target-cpu=native;
see the `wall_s` field in the ratchet file for the per-instance number):

    --tier fast    7.0s     14 instances    <- fallback lane
    --tier all    73.6-81.1s  20 instances  <- pre-push AND nightly (wired)

(44.8s is the sum of the recorded per-instance `wall_s`; 46.9s was the harness
wall of a whole `--check --tier all` run at nineteen instances, which also pays
process startup and MPS parsing per instance. Both are quiet-box numbers on the
same box.)

RE-MEASURED 2026-08-26 on the same box when qiu was pinned, quiet (load 2.7-3.8):
42.0s and 42.7s at nineteen instances; 73.6 / 75.9 / 76.3 / 81.1s at twenty over
four runs. qiu alone is ~34.4s, i.e. this gate roughly DOUBLED to buy the only
view anyone has of `FloatLp::tall_cold_dual`. That is the trade, priced: the
pre-merge `fast` lane is untouched (7.0s, 14 instances, re-measured), and
`--tier all` is a pre-push/nightly lane where ~35 extra seconds is cheaper than
the fortnight the disjunct spent ungated. The spread across those four runs is
10%% and is why this is quoted as a RANGE: it is a wall number on a shared box.

measured 2026-08-20, aarch64-apple-darwin, quiet box, serial (AY_MILP_THREADS=1).
The five slow ones are air03, mas76, pk1, qnet1, stein45 -- together 37.6s of
the 44.8s, and pk1 alone is 13.2s. Splitting them out is what makes a pre-merge
lane possible at all; folding them back in makes the gate something people skip.

SENSITIVITY, measured against a deliberate scratch regression (MAX_GMI_ROUNDS
2 -> 1, release rebuild, --tier fast): 8 of the 14 pinned instances moved and
were named -- blend2 9,070 -> 5,218, dcmulti 761 -> 2,948, enigma 16,765 ->
26,126, gt2 4,954 -> 776, lseu 1,978 -> 2,358, misc03 162 -> 178, p0201 110 ->
88, p0548 2,380 -> 9,575. The standing four would have reported two of those
eight. Reverting the scratch change returns the gate to clean at both tiers.

NEITHER TIER BELONGS IN `cargo test`. The twenty models are MIPLIB files;
this repository contains seven .mps files in total, all tiny fixtures, and
shipping MIPLIB into the tree is not on the table. `cargo test -p ay-milp` can
therefore never measure them, and a test that silently skips when a corpus
directory is absent is a DEAD GATE of exactly the family this round is cleaning
up. What the in-tree test `crates/ay-milp/tests/node_ratchet.rs` does instead is
guard the RATCHET FILE for free (set completeness, no flaky instance smuggled
in, no pin deleted rather than updated); what measures the models is this
script, run against a corpus directory.

WHERE THE MODELS LIVE. `~/ay-bench/milp-gate/instances`, by default and without
being told -- see `scripts/milp_gate_corpus.py`, which owns that directory, and
`.milp_gate_corpus.tsv`, which pins a sha256 and an upstream URL per instance so
the corpus is rebuildable from this repository alone. Until 2026-08-20 the
nineteen models lived in two per-session scratch directories and `--corpus` was
MANDATORY, which made the gate runnable only by the session that had made them.
`--corpus` still overrides, and is still repeatable.

USAGE
    milp_node_gate.py --check   [--corpus DIR ...] [--tier fast|all]
    milp_node_gate.py --ratchet [--corpus DIR ...] [--tier fast|all]
    milp_node_gate.py --list

Exit codes: 0 clean, 1 regression/drift, 2 harness or setup problem.
"""
from __future__ import annotations

import argparse
import os
import subprocess
import sys
import time

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RATCHET = os.path.join(REPO, '.milp_node_baseline.toml')
SOLVER = os.path.join(REPO, 'target', 'release', 'examples', 'mps_solve')

# ONE definition of where the corpus lives, imported rather than re-typed: two
# scripts with the same default path spelled twice is how the path drifts.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from milp_gate_corpus import DEFAULT_CORPUS  # noqa: E402

# THE QUIET-BOX THRESHOLD, defined ONCE and imported by `scripts/corpus_guard.py`
# rather than re-typed there. Same reason as DEFAULT_CORPUS above: a constant
# spelled in two gates is a constant that drifts, and both gates are wrong in the
# SAME way on a busy box.
LOAD_FRACTION = 0.35


def busy_box(fraction=LOAD_FRACTION):
    """`(busy, load, cpus)` for the quiet-box precondition.

    `busy` is None -- not False -- when the platform has no load average, so a
    caller can tell "measured quiet" from "could not measure"; both proceed,
    because blocking every gate on a platform that cannot report load would be
    worse than the drift it prevents.
    """
    cpus = os.cpu_count() or 1
    try:
        load = os.getloadavg()[0]
    except (OSError, AttributeError):
        return None, None, cpus
    return load > fraction * cpus, load, cpus


# ---------------------------------------------------------------------------
# the ratchet file
# ---------------------------------------------------------------------------

def parse_ratchet(path):
    """Minimal reader for the fixed shape this file is written in.

    Deliberately NOT a general TOML parser: the file is machine-written by
    `--ratchet` and its grammar is `[[instance]]` tables of `key = value` plus
    one `[flaky]` table of `name = "reason"`. A hand-rolled reader keeps the
    in-tree Rust test (which has no `toml` dependency) and this script reading
    the SAME grammar, so the two cannot drift.
    """
    instances, flaky, section, cur = [], {}, None, None
    with open(path) as f:
        for lineno, raw in enumerate(f, 1):
            # WHOLE-LINE comments only, exactly like the Rust reader in
            # `tests/node_ratchet.rs`. Stripping a trailing `# ...` here and not
            # there would be a grammar fork between the two readers, and it would
            # also truncate any `[flaky]` reason containing a `#`.
            line = raw.strip()
            if not line or line.startswith('#'):
                continue
            if line == '[[instance]]':
                cur = {}
                instances.append(cur)
                section = 'instance'
                continue
            if line == '[flaky]':
                section = 'flaky'
                cur = None
                continue
            if line.startswith('['):
                raise ValueError('%s:%d: unexpected table %r' % (path, lineno, line))
            if '=' not in line:
                raise ValueError('%s:%d: not a key = value line: %r' % (path, lineno, line))
            key, val = (s.strip() for s in line.split('=', 1))
            if val.startswith('"'):
                val = val.strip('"')
            elif '.' in val:
                val = float(val)
            else:
                val = int(val)
            if section == 'flaky':
                flaky[key] = val
            elif cur is not None:
                cur[key] = val
            else:
                raise ValueError('%s:%d: key outside any table' % (path, lineno))
    return instances, flaky


HEADER = '''# Copyright 2026 Andrew Yates
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0

# EXACT node-count pins for the deterministic MILP corpus. Written by
# `scripts/milp_node_gate.py --ratchet`, checked by `--check`, and validated for
# shape/completeness by `crates/ay-milp/tests/node_ratchet.rs` in the default
# test run.
#
# A CHANGE THAT MOVES ANY NUMBER BELOW MUST UPDATE IT DELIBERATELY, in the same
# commit, with the measurement in the message. That includes IMPROVEMENTS: an
# unratcheted improvement is how a pin rots into folklore, and it is also how a
# later regression gets to hide inside slack that nobody meant to grant.
#
# `nodes` is the load-invariant currency and the primary tripwire; `obj` and
# `status` are correctness pins that are never downgraded to warnings. `wall_s`
# is RECORDED, not gated -- a busy box moves it and the gate must not care.
#
# tier = "fast"  -- the pre-merge lane (`--tier fast`)
# tier = "slow"  -- pre-push / nightly only (`--tier all`)
#
# QUIET BOX ONLY, and blend2/mod010 are why. Both have a root cut loop whose
# round count is bounded by a SHARE of the wall deadline, so contention buys
# fewer rounds and a slightly different tree. Measured on the same binary and
# corpus: quiet, blend2 = 9,070 and mod010 = 2,381 (reproduced three times);
# under a concurrent `cargo test` at load average 43 on 14 cores, 8,995 and
# 2,291. The gate refuses to run above 0.35 x cpu_count for exactly this reason.
# IF YOU EVER SEE 8,995 HERE, THE FIX IS TO RE-RUN ON AN IDLE BOX -- not to
# ratchet the loaded number in.
'''

FLAKY_NOTE = '''
# NOT GATED, BY NAME. These move run-to-run at a FIXED configuration on a quiet
# box, so pinning them would produce failures with no code change behind them.
# Listed here rather than merely omitted so the question "why isn't misc07 in
# the gate" is answered by the file instead of by archaeology.
[flaky]
'''


def write_ratchet(path, rows, flaky, prev=None):
    # PRESERVE THE HAND-WRITTEN HEADER. `--ratchet` is the remedy the pre-push
    # hook prints, so it gets run routinely and by people who are not thinking
    # about this file's prose. Regenerating HEADER from the template silently
    # deleted a deliberately-recorded caveat once (a note that an independent
    # auditor could NOT reproduce the load-coupling numbers, replaced by text
    # asserting them as fact). Everything above the first [[instance]] is the
    # human's, not the generator's.
    head = HEADER
    if os.path.exists(path):
        existing = open(path).read()
        cut = existing.find('\n[[instance]]')
        if cut != -1:
            head = existing[:cut]
    with open(path, 'w') as f:
        f.write(head)
        for r in sorted(rows, key=lambda r: r['name']):
            # wall_s is informational; rewriting it when no node count moved
            # puts 18 lines of noise in every ratchet commit and buries the one
            # line that matters. Keep the recorded wall unless the tree moved.
            wall = r['wall_s']
            if prev is not None:
                old = prev.get(r['name'])
                if old is not None and old.get('nodes') == r['nodes']:
                    wall = old.get('wall_s', wall)
            f.write('\n[[instance]]\n')
            f.write('name = "%s"\n' % r['name'])
            f.write('nodes = %d\n' % r['nodes'])
            f.write('obj = %r\n' % r['obj'])
            f.write('status = "%s"\n' % r['status'])
            f.write('tier = "%s"\n' % r['tier'])
            f.write('wall_s = %.3f\n' % wall)
        f.write(FLAKY_NOTE)
        for name in sorted(flaky):
            f.write('%s = "%s"\n' % (name, flaky[name]))


# ---------------------------------------------------------------------------
# measurement
# ---------------------------------------------------------------------------

def find_model(name, corpora):
    for d in corpora:
        for ext in ('.mps', '.mps.gz'):
            p = os.path.join(d, name + ext)
            if os.path.exists(p):
                return p
    return None


def run(solver, mps, secs):
    """One solve. `mps_solve` prints `status value wall nodes` as its last line."""
    env = dict(os.environ, AY_MILP_THREADS='1')
    t = time.time()
    try:
        out = subprocess.run([solver, mps, str(secs)], capture_output=True,
                             text=True, env=env, timeout=secs * 3 + 60)
    except subprocess.TimeoutExpired:
        return {'status': 'HARNESS_TIMEOUT'}
    if out.returncode != 0:
        # STRICT FLAG PARSING exits 2 with EMPTY stdout. A harness that reads
        # the last stdout line records that as a missing datum; this one does
        # not, because that exact confusion has already cost this campaign a
        # round of measurement.
        return {'status': 'EXIT_%d' % out.returncode,
                'raw': (out.stdout[-300:] + out.stderr[-300:]).strip()}
    line = (out.stdout.strip().splitlines() or [''])[-1].split()
    if len(line) < 4:
        return {'status': 'NO_OUTPUT', 'raw': out.stdout[-300:] + out.stderr[-300:]}
    try:
        return {'status': line[0], 'obj': float(line[1]),
                'nodes': int(line[-1]), 'wall_s': round(time.time() - t, 3)}
    except ValueError:
        return {'status': 'PARSE_ERROR', 'raw': ' '.join(line)}


def measure(rows, solver, corpora, limit):
    out, missing = [], []
    for r in rows:
        mps = find_model(r['name'], corpora)
        if mps is None:
            missing.append(r['name'])
            continue
        rec = run(solver, mps, limit)
        rec['name'] = r['name']
        rec['tier'] = r['tier']
        out.append(rec)
    return out, missing


def compare(pins, cur):
    """Exact comparison. Every mismatch is a FAIL and names expected vs actual."""
    fails = []
    by_name = {r['name']: r for r in pins}
    for c in cur:
        p = by_name[c['name']]
        if c['status'] != p['status']:
            fails.append('%-9s STATUS  expected %-8s actual %-8s%s'
                         % (c['name'], p['status'], c['status'],
                            '   (' + c['raw'] + ')' if c.get('raw') else ''))
            continue
        if abs(c['obj'] - p['obj']) > 1e-9 * max(1.0, abs(p['obj'])):
            fails.append('%-9s ANSWER  expected %r actual %r  <- CORRECTNESS'
                         % (c['name'], p['obj'], c['obj']))
            continue
        if c['nodes'] != p['nodes']:
            ratio = c['nodes'] / p['nodes'] if p['nodes'] else float('inf')
            direction = 'REGRESSION' if c['nodes'] > p['nodes'] else 'improvement'
            fails.append('%-9s NODES   expected %-8d actual %-8d (%.2fx, %s) '
                         '-- update .milp_node_baseline.toml with --ratchet if intended'
                         % (c['name'], p['nodes'], c['nodes'], ratio, direction))
    return fails


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--corpus', action='append', default=[],
                    help='directory of .mps/.mps.gz models; repeatable. '
                         'Default: %s' % DEFAULT_CORPUS)
    ap.add_argument('--solver', default=SOLVER)
    ap.add_argument('--limit', type=float, default=300.0,
                    help='per-instance time limit; every pinned instance proves '
                         'optimality well inside it, so it only bounds a hang')
    ap.add_argument('--tier', choices=('fast', 'all'), default='fast')
    ap.add_argument('--check', action='store_true')
    ap.add_argument('--ratchet', action='store_true')
    ap.add_argument('--list', action='store_true')
    ap.add_argument('--allow-busy', action='store_true',
                    help='skip the load-average precondition (see the header: two '
                         'instances are wall-deadline coupled and drift under load)')
    a = ap.parse_args()

    try:
        pins, flaky = parse_ratchet(RATCHET)
    except (OSError, ValueError) as e:
        print('SETUP: %s' % e, file=sys.stderr)
        return 2

    wanted = [r for r in pins if a.tier == 'all' or r['tier'] == 'fast']

    if a.list or not (a.check or a.ratchet):
        print('%-9s %-6s %8s %14s %8s' % ('instance', 'tier', 'nodes', 'obj', 'wall_s'))
        for r in sorted(pins, key=lambda r: (r['tier'], r['name'])):
            print('%-9s %-6s %8d %14g %8.3f'
                  % (r['name'], r['tier'], r['nodes'], r['obj'], r['wall_s']))
        print('\nnot gated (measured non-deterministic at fixed config):')
        for name in sorted(flaky):
            print('  %-9s %s' % (name, flaky[name]))
        if not (a.check or a.ratchet):
            print('\n(nothing measured: pass --check or --ratchet)')
        return 0

    corpora = a.corpus or [DEFAULT_CORPUS]
    for d in corpora:
        if not os.path.isdir(d):
            print('SETUP: corpus not found at %s\n'
                  '       rebuild it: scripts/milp_gate_corpus.py --build'
                  % d, file=sys.stderr)
            return 2
    if not os.path.exists(a.solver):
        print('SETUP: solver not built at %s\n'
              '       cargo build --release -p ay-milp --example mps_solve'
              % a.solver, file=sys.stderr)
        return 2

    # THE QUIET-BOX PRECONDITION. Not a nicety: measured on this machine, a
    # concurrent `cargo test` moved blend2 9,070 -> 8,995 and mod010 2,381 ->
    # 2,291 with NO code change, because both instances' root cut loops are
    # bounded by a share of the wall deadline. Reporting that as drift is how a
    # gate gets muted. SETUP (2), never a FAIL (1) and never a clean (0).
    busy, load, cpus = busy_box()
    if busy and not a.allow_busy:
        print('SETUP: load average %.1f on %d cpus -- this gate is only valid on a '
              'quiet box.\n       Two pinned instances are wall-deadline coupled '
              '(blend2, mod010) and drift\n       ~1%% under contention, which would '
              'read as a regression with no commit behind it.\n'
              '       Wait, or pass --allow-busy to reproduce a known failure.'
              % (load, cpus), file=sys.stderr)
        return 2

    t0 = time.time()
    cur, missing = measure(wanted, a.solver, corpora, a.limit)
    wall = time.time() - t0

    # A MISSING MODEL IS A SETUP FAILURE, NOT A PASS. The gate measured less
    # than it claims to; reporting that as clean is how a gate goes quietly dead.
    if missing:
        print('SETUP: %d of %d models not found in %s: %s'
              % (len(missing), len(wanted), ', '.join(corpora), ' '.join(missing)),
              file=sys.stderr)
        return 2

    if a.ratchet:
        keep = {r['name'] for r in cur}
        rows = [r for r in pins if r['name'] not in keep]
        for c in cur:
            if 'nodes' not in c:
                print('SETUP: %s did not measure (%s)' % (c['name'], c['status']),
                      file=sys.stderr)
                return 2
            rows.append({'name': c['name'], 'nodes': c['nodes'], 'obj': c['obj'],
                         'status': c['status'], 'tier': c['tier'],
                         'wall_s': c['wall_s']})
        prev_rows, _prev_flaky = parse_ratchet(RATCHET)
        prev_by_name = {r['name']: r for r in prev_rows}
        write_ratchet(RATCHET, rows, flaky, prev_by_name)
        print('ratcheted %d instance(s) in %s (%.1fs of solving)'
              % (len(cur), os.path.relpath(RATCHET, REPO), wall))
        return 0

    fails = compare(wanted, cur)
    print('=== milp node gate: tier %s, %d instances, %.1fs wall ==='
          % (a.tier, len(cur), wall))
    for f in fails:
        print('  FAIL  %s' % f)
    if not fails:
        print('  clean: every pinned node count, objective and status is exact')
    print('=== %d fail ===' % len(fails))
    return 1 if fails else 0


if __name__ == '__main__':
    sys.exit(main())
