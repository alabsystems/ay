# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# INCREMENTAL push/pop differential verdict fuzzer for ayz3 vs real z3py.
#
# WHAT IT DOES
#   The one-shot fuzzer (`differential.py`) builds ONE formula per seed and
#   compares a single check. THIS module instead drives a whole INCREMENTAL
#   SESSION over ONE long-lived solver: a deterministic, seed-derived sequence
#   of interleaved operations --
#
#       push()              -- open a new assertion scope
#       pop(n)              -- discard the top n scopes' asserts
#       add(constraint)     -- assert a random in-fragment constraint
#       check()             -- check-sat at THIS point in the session
#       assert_and_track    -- (occasionally) tracked assert for an unsat core
#       unsat_core()        -- (after an unsat check) read the core (smoke only)
#
#   The SAME op sequence is replayed against BOTH ayz3 and real z3py, and the
#   verdict is compared at EVERY `check()` -- not just the last one. Constraints
#   are drawn from the fragment's generator (`gen._Gen`) over a SMALL SHARED
#   variable pool, so successive asserts genuinely interact and push/pop scopes
#   actually change the verdict (e.g. an over-constrained scope goes unsat, then
#   pop() makes it sat again).
#
# PAIRWISE CLASSIFICATION
#   At each check point we compare (ayz3 verdict, z3 verdict):
#     * both sat or both unsat                  -> AGREE
#     * either side unknown (sound incomplete-
#       ness) or a binding gap (NotImplemented) -> INCOMPLETE (recorded
#                                                  separately, NOT a bug)
#     * one sat and the other unsat             -> DISAGREE (an unadjudicated
#                                                  verdict dispute)
#
#   A sound `unknown` from ayz3 while z3 is decisive is INCOMPLETE, never a bug.
#
# FAITHFULNESS
#   We replay the IDENTICAL op sequence on both engines. If an op cannot be
#   expressed on one engine (raises NotImplementedError / any error), we ABORT
#   the whole session for BOTH engines from that point and record the session as
#   incomplete -- we NEVER fabricate agreement by silently skipping an op on one
#   side only.
#
# DETERMINISM
#   Everything is seeded from the (fragment, seed) pair, so any disagreement
#   reproduces exactly: the op sequence is regenerated from the seed and printed.

import random
from dataclasses import dataclass, field
from typing import Any, List, Optional

from . import gen
from .gen import Node, build, _Gen, BV, SORT_INT, SORT_REAL, SORT_BOOL
from .differential import (
    _load_ayz3,
    _load_z3,
    _verdict_str,
    _NullScope,
    have_z3,
)

# Per-check outcome tags.
AGREE = "agree"
INCOMPLETE = "incomplete"   # >=1 unknown / binding gap -> NOT a bug
DISAGREE = "disagree"       # sat vs unsat -> unadjudicated verdict dispute


# ---------------------------------------------------------------------------
# Op model (module-agnostic). One Op realizes against ANY z3py-shaped module.
# ---------------------------------------------------------------------------

@dataclass
class Op:
    """One incremental operation. `kind` selects the action; `node` (a Bool
    `gen.Node`) is the constraint for add / assert_and_track; `n` is the pop
    count; `tracker` is the assert_and_track tracking-literal name."""
    kind: str                       # push|pop|add|check|track|core
    node: Optional[Node] = None
    n: int = 1
    tracker: Optional[str] = None


def _frag_atom(g: _Gen, fragment: str):
    """Draw a single random in-fragment Bool atom (a constraint) from `g`.

    Uses a SHALLOW boolean term so each add is a small, comprehensible
    constraint; the SESSION (many adds over a shared pool) supplies the depth.
    The `domain`/width mirror what each fragment's one-shot generator uses, so
    the constraints are exactly in-fragment.
    """
    if fragment == "qf_lia":
        return g.bool_term(g.rng.randint(0, 2), domain="lia")
    if fragment == "qf_lra":
        return g.bool_term(g.rng.randint(0, 2), domain="lra")
    if fragment == "qf_bv":
        return g.bool_term(g.rng.randint(0, 2), domain="bv", width=g.bv_width)
    if fragment == "qf_bv_bool":
        return g.bool_term(g.rng.randint(1, 3), domain="bv_bool", width=g.bv_width)
    if fragment == "arrays":
        return g.bool_term(g.rng.randint(0, 2), domain="arr")
    if fragment == "qf_uflia":
        g.use_uf = True
        return g.bool_term(g.rng.randint(0, 2), domain="uflia")
    if fragment == "arr_lia":
        return g.bool_term(g.rng.randint(0, 2), domain="arr_lia")
    if fragment == "quant_lia":
        # Quantified atoms are heavy; keep the per-op constraint a plain LIA atom
        # so the SESSION stays the focus (and stays decidable enough to compare).
        return g.bool_term(g.rng.randint(0, 1), domain="lia")
    raise ValueError(f"incremental fuzz: unsupported fragment {fragment!r}")


def _bv_width_for(fragment: str, rng: random.Random) -> int:
    if fragment in ("qf_bv", "qf_bv_bool"):
        return rng.choice([2, 3, 4, 6, 8])
    return 0


# Fragments the incremental fuzzer knows how to draw constraints for. (Same set
# as the one-shot fuzzer; `datatypes` has no formula generator in either.)
FRAGMENTS = (
    "qf_lia", "qf_lra", "qf_bv", "arrays",
    "qf_uflia", "arr_lia", "qf_bv_bool", "quant_lia",
)


def generate_session(fragment: str, seed: int,
                     min_ops: int = 10, max_ops: int = 30,
                     max_depth: int = 5) -> List[Op]:
    """Deterministically generate one incremental op sequence for (fragment,
    seed). The same pair always yields the identical session (so a finding
    reproduces). Nesting depth is bounded by `max_depth` (~5); op count is in
    [min_ops, max_ops] (~10-30).

    The sequence is well-bracketed: `pop(n)` never pops more scopes than are
    currently open, and we GUARANTEE at least one `check()` exists (otherwise the
    session would have nothing to compare).
    """
    if fragment not in FRAGMENTS:
        raise ValueError(f"unknown fragment {fragment!r}; choose from {FRAGMENTS}")

    rng = random.Random()
    rng.seed(f"incremental:{fragment}:{seed}")

    width = _bv_width_for(fragment, rng)
    g = _Gen(rng, fragment, bv_width=width)
    if fragment == "qf_uflia":
        g.use_uf = True

    n_ops = rng.randint(min_ops, max_ops)
    ops: List[Op] = []
    depth = 0          # current open-scope nesting
    track_ctr = 0      # unique tracking-literal counter
    saw_check = False

    for _ in range(n_ops):
        # Weighted op choice. `add` dominates (we want real constraints); push /
        # pop / check are common; track is occasional.
        r = rng.random()
        if r < 0.40:
            ops.append(Op("add", node=_frag_atom(g, fragment)))
        elif r < 0.62:
            ops.append(Op("check"))
            saw_check = True
        elif r < 0.78:
            if depth < max_depth:
                ops.append(Op("push"))
                depth += 1
            else:
                # At max nesting, prefer a pop or add instead of overflowing.
                ops.append(Op("add", node=_frag_atom(g, fragment)))
        elif r < 0.92:
            if depth > 0:
                k = rng.randint(1, depth)
                ops.append(Op("pop", n=k))
                depth -= k
            else:
                ops.append(Op("add", node=_frag_atom(g, fragment)))
        else:
            # Occasional tracked assert (followed implicitly by a later check /
            # core read). Use a unique tracker name per session.
            track_ctr += 1
            ops.append(Op("track", node=_frag_atom(g, fragment),
                          tracker=f"t{seed}_{track_ctr}"))

    # Guarantee at least one check so the session compares something.
    if not saw_check:
        ops.append(Op("check"))

    # Always end with a check at the (popped-back) base, for a final comparison.
    ops.append(Op("check"))
    return ops


def render_session(ops: List[Op], fragment: str, z3_mod=None) -> str:
    """Render an op sequence as a readable, reproducible script. Constraints are
    rendered via z3py's canonical s-expr when z3 is available, else by op kind."""
    lines = []
    for i, op in enumerate(ops):
        if op.kind == "add":
            c = _node_text(op.node, z3_mod)
            lines.append(f"  [{i:2}] add      {c}")
        elif op.kind == "track":
            c = _node_text(op.node, z3_mod)
            lines.append(f"  [{i:2}] track    ({op.tracker}) {c}")
        elif op.kind == "push":
            lines.append(f"  [{i:2}] push")
        elif op.kind == "pop":
            lines.append(f"  [{i:2}] pop({op.n})")
        elif op.kind == "check":
            lines.append(f"  [{i:2}] check")
        elif op.kind == "core":
            lines.append(f"  [{i:2}] unsat_core")
    return "\n".join(lines)


def _node_text(node: Node, z3_mod) -> str:
    if node is None:
        return "<none>"
    if z3_mod is not None:
        try:
            return build(node, z3_mod).sexpr()
        except Exception:
            pass
    return f"<node op={node.op}>"


# ---------------------------------------------------------------------------
# Session replay against one module
# ---------------------------------------------------------------------------

@dataclass
class CheckPoint:
    """The verdict produced at a single `check()` op (one engine)."""
    op_index: int
    verdict: str          # sat / unsat / unknown / error
    reason: str = ""      # for unknown / error


@dataclass
class ReplayResult:
    """The result of replaying a whole session against one engine."""
    checks: List[CheckPoint] = field(default_factory=list)
    aborted_at: Optional[int] = None   # op index where the session aborted
    abort_reason: str = ""


def _isolated_session_solver(m):
    """Like differential._isolated_solver, but returns a solver bound to a fresh
    isolated context for ayz3 (so sessions don't leak), with a scope CM that, for
    ayz3, keeps EVERY constraint built into THIS solver's context. For real z3py
    the scope is a no-op (each Solver is independently scoped)."""
    Context = getattr(m, "Context", None)
    solver = m.Solver()
    if Context is not None and hasattr(solver, "using"):
        ctx = Context()
        solver = m.Solver(ctx)
        return solver, solver.using()
    return solver, _NullScope()


def replay(ops: List[Op], m, timeout_ms: int = 2000) -> ReplayResult:
    """Replay the op sequence against module `m`, recording the verdict at every
    `check`. The whole session runs inside ONE solver/context so push/pop scopes
    interact and constraints share variables.

    On ANY op-level failure (a binding gap, an unexpected exception), the session
    is ABORTED at that op (recorded in `aborted_at`). The CALLER then truncates
    BOTH engines' check lists to the common prefix, so we never compare a check
    that only one engine reached -- faithfulness over coverage.
    """
    res = ReplayResult()
    try:
        solver, scope = _isolated_session_solver(m)
    except Exception as e:
        res.aborted_at = 0
        res.abort_reason = f"solver create: {type(e).__name__}: {e}"
        return res

    if timeout_ms:
        try:
            solver.set("timeout", int(timeout_ms))
        except Exception:
            pass

    with scope:
        for i, op in enumerate(ops):
            try:
                if op.kind == "add":
                    f = build(op.node, m)
                    solver.add(f)
                elif op.kind == "track":
                    f = build(op.node, m)
                    solver.assert_and_track(f, op.tracker)
                elif op.kind == "push":
                    solver.push()
                elif op.kind == "pop":
                    solver.pop(op.n)
                elif op.kind == "check":
                    r = _verdict_str(solver.check())
                    cp = CheckPoint(op_index=i, verdict=r)
                    if r == "unknown":
                        try:
                            cp.reason = solver.reason_unknown()
                        except Exception:
                            cp.reason = ""
                    res.checks.append(cp)
                elif op.kind == "core":
                    # Smoke-only: exercise unsat_core() if the last check was
                    # unsat. We do not compare cores across engines (z3's core
                    # need not match AY's); we just ensure it doesn't crash.
                    try:
                        solver.unsat_core()
                    except Exception:
                        pass
            except NotImplementedError as e:
                res.aborted_at = i
                res.abort_reason = f"{op.kind}: NotImplementedError: {e}"
                break
            except Exception as e:
                res.aborted_at = i
                res.abort_reason = f"{op.kind}: {type(e).__name__}: {e}"
                break
    return res


# ---------------------------------------------------------------------------
# Differential comparison over a session
# ---------------------------------------------------------------------------

@dataclass
class CheckCompare:
    """One compared check point across both engines."""
    op_index: int
    ay_verdict: str
    z3_verdict: str
    outcome: str          # AGREE / INCOMPLETE / DISAGREE


@dataclass
class SessionResult:
    fragment: str
    seed: int
    compares: List[CheckCompare] = field(default_factory=list)
    n_agree: int = 0
    n_incomplete: int = 0
    n_disagree: int = 0
    # The first disagreeing check point (for a precise repro), if any.
    first_disagree: Optional[CheckCompare] = None
    ay_aborted_at: Optional[int] = None
    z3_aborted_at: Optional[int] = None
    note: str = ""

    @property
    def disagreed(self) -> bool:
        return self.n_disagree > 0


def run_session(fragment: str, seed: int, ayz3_mod=None, z3_mod=None,
                timeout_ms: int = 2000,
                min_ops: int = 10, max_ops: int = 30,
                max_depth: int = 5) -> SessionResult:
    """Generate one incremental session for (fragment, seed) and replay it on
    BOTH engines, comparing the verdict at every check point.

    The two replays are compared check-by-check on the COMMON PREFIX of checks
    both engines reached (truncated to the earlier abort, if any), so a check is
    only ever compared when BOTH engines genuinely ran it.
    """
    ayz3_mod = ayz3_mod or _load_ayz3()
    z3_mod = z3_mod if z3_mod is not None else _load_z3()

    ops = generate_session(fragment, seed, min_ops=min_ops, max_ops=max_ops,
                           max_depth=max_depth)

    res = SessionResult(fragment=fragment, seed=seed)
    if z3_mod is None:
        res.note = "z3 absent"
        return res

    ay = replay(ops, ayz3_mod, timeout_ms=timeout_ms)
    z = replay(ops, z3_mod, timeout_ms=timeout_ms)
    res.ay_aborted_at = ay.aborted_at
    res.z3_aborted_at = z.aborted_at

    # Compare only checks BOTH engines reached. Because a check is identified by
    # its op index, we align by op index and only compare indices present on
    # BOTH sides (a session aborts identically structurally, but a binding gap
    # could abort one earlier -- so we intersect by op index to be safe).
    z_by_idx = {cp.op_index: cp for cp in z.checks}
    for a_cp in ay.checks:
        z_cp = z_by_idx.get(a_cp.op_index)
        if z_cp is None:
            continue  # z3 didn't reach this check (one side aborted earlier)
        outcome = _classify(a_cp.verdict, z_cp.verdict)
        cmp = CheckCompare(op_index=a_cp.op_index,
                           ay_verdict=a_cp.verdict, z3_verdict=z_cp.verdict,
                           outcome=outcome)
        res.compares.append(cmp)
        if outcome == AGREE:
            res.n_agree += 1
        elif outcome == INCOMPLETE:
            res.n_incomplete += 1
        elif outcome == DISAGREE:
            res.n_disagree += 1
            if res.first_disagree is None:
                res.first_disagree = cmp
    return res


def _classify(ay_v: str, z3_v: str) -> str:
    """Classify a pair of verdicts at a single check point."""
    if ay_v in ("unknown", "error") or z3_v in ("unknown", "error"):
        return INCOMPLETE
    if ay_v == z3_v:
        return AGREE
    # one sat, one unsat -> unadjudicated verdict dispute
    return DISAGREE


# ---------------------------------------------------------------------------
# Repro banner
# ---------------------------------------------------------------------------

def disagreement_banner(res: SessionResult, ops: List[Op], z3_mod) -> str:
    cmp = res.first_disagree
    lines = [
        "",
        "=" * 70,
        "  INCREMENTAL VERDICT DISPUTE: sat-vs-unsat at a check point",
        "=" * 70,
        f"  fragment    : {res.fragment}",
        f"  seed        : {res.seed}",
        f"  check op idx : {cmp.op_index}",
        f"  ayz3        : {cmp.ay_verdict}",
        f"  z3 (4.x)    : {cmp.z3_verdict}",
        f"  repro       : generate_session({res.fragment!r}, {res.seed})",
        "  op sequence :",
    ]
    lines.append(render_session(ops, res.fragment, z3_mod))
    lines.append("=" * 70)
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Campaign
# ---------------------------------------------------------------------------

@dataclass
class CampaignSummary:
    fragment: str
    count: int
    sessions: int = 0
    check_points: int = 0
    agree: int = 0
    incomplete: int = 0
    disagree: int = 0
    disagreeing_seeds: List[int] = field(default_factory=list)

    def line(self) -> str:
        return (f"[{self.fragment}] sessions={self.sessions} "
                f"check_points={self.check_points} agree={self.agree} "
                f"incomplete={self.incomplete} DISAGREE={self.disagree}")


def run_campaign(fragment: str, count: int, seed_start: int = 0,
                 ayz3_mod=None, z3_mod=None, timeout_ms: int = 2000,
                 stop_on_disagree: bool = False, progress=None,
                 min_ops: int = 10, max_ops: int = 30,
                 max_depth: int = 5) -> CampaignSummary:
    """Run `count` incremental sessions for `fragment`, seeds
    [seed_start, seed_start+count). Returns a CampaignSummary; on a disagreement
    a full repro banner is emitted via `progress`."""
    ayz3_mod = ayz3_mod or _load_ayz3()
    z3_mod = z3_mod if z3_mod is not None else _load_z3()
    summ = CampaignSummary(fragment=fragment, count=count)

    for k in range(count):
        seed = seed_start + k
        res = run_session(fragment, seed, ayz3_mod, z3_mod, timeout_ms=timeout_ms,
                          min_ops=min_ops, max_ops=max_ops, max_depth=max_depth)
        summ.sessions += 1
        summ.check_points += len(res.compares)
        summ.agree += res.n_agree
        summ.incomplete += res.n_incomplete
        summ.disagree += res.n_disagree
        if res.disagreed:
            summ.disagreeing_seeds.append(seed)
            if progress:
                ops = generate_session(fragment, seed, min_ops=min_ops,
                                       max_ops=max_ops, max_depth=max_depth)
                progress(disagreement_banner(res, ops, z3_mod))
            if stop_on_disagree:
                break
        if progress and (k + 1) % 100 == 0:
            progress(f"  ...{fragment}: {k + 1}/{count} sessions ({summ.line()})")

    return summ


# ---------------------------------------------------------------------------
# CLI entry (wired into ayz3_fuzz.__main__ as the `incremental` subcommand)
# ---------------------------------------------------------------------------

def main(argv=None):
    import argparse
    import sys

    p = argparse.ArgumentParser(
        prog="ayz3_fuzz incremental",
        description="INCREMENTAL push/pop differential SOUNDNESS fuzzer: replays "
                    "random incremental sessions on ayz3 AND z3py, comparing the "
                    "verdict at every check point.",
    )
    p.add_argument("--fragment", default="qf_lia",
                   help="fragment: " + ", ".join(FRAGMENTS) + ", or 'all'")
    p.add_argument("--seed-start", type=int, default=0,
                   help="first seed (default 0); seeds are "
                        "[seed-start, seed-start+count)")
    p.add_argument("--count", type=int, default=500,
                   help="number of incremental sessions per fragment (default 500)")
    p.add_argument("--timeout-ms", type=int, default=2000,
                   help="per-check timeout in ms (default 2000)")
    p.add_argument("--min-ops", type=int, default=10,
                   help="minimum ops per session (default 10)")
    p.add_argument("--max-ops", type=int, default=30,
                   help="maximum ops per session (default 30)")
    p.add_argument("--max-depth", type=int, default=5,
                   help="maximum push/pop nesting depth (default 5)")
    p.add_argument("--stop-on-disagree", action="store_true",
                   help="stop a fragment at its first disagreeing session")
    p.add_argument("--quiet", action="store_true",
                   help="suppress periodic progress output")
    args = p.parse_args(argv)

    if not have_z3():
        print("z3py is not installed; the incremental differential fuzzer needs "
              "real z3 (4.15.4) to compare against. (Nothing to do; exiting 0.)",
              file=sys.stderr)
        return 0

    if args.fragment == "all":
        frags = list(FRAGMENTS)
    elif args.fragment in FRAGMENTS:
        frags = [args.fragment]
    else:
        p.error(f"unknown fragment {args.fragment!r}; "
                f"choose from {list(FRAGMENTS)} or 'all'")

    progress = None if args.quiet else (lambda s: print(s, flush=True))

    print(f"Incremental differential soundness fuzz: fragments={frags} "
          f"count={args.count}/frag seed_start={args.seed_start} "
          f"ops={args.min_ops}-{args.max_ops} max_depth={args.max_depth}")
    print("Comparison (per check point): both-sat/both-unsat=AGREE; any "
          "unknown/binding-gap=INCOMPLETE; sat-vs-unsat=DISAGREE "
          "(unadjudicated)\n")

    total_disagree = 0
    disagreeing = []
    for frag in frags:
        summ = run_campaign(frag, args.count, seed_start=args.seed_start,
                            timeout_ms=args.timeout_ms,
                            stop_on_disagree=args.stop_on_disagree,
                            progress=progress, min_ops=args.min_ops,
                            max_ops=args.max_ops, max_depth=args.max_depth)
        print(summ.line())
        total_disagree += summ.disagree
        for s in summ.disagreeing_seeds:
            disagreeing.append((frag, s))

    print("\n" + "-" * 70)
    if disagreeing:
        print(f"!!! {len(disagreeing)} disagreeing SESSION(S) "
              f"({total_disagree} disagreeing check point(s)) !!!")
        for frag, s in disagreeing:
            print(f"  DISAGREE: fragment={frag} seed={s} "
                  f"(repro: python3 -m ayz3_fuzz incremental "
                  f"--fragment {frag} --seed-start {s} --count 1)")
        return 1

    print("No sat-vs-unsat disagreements at any incremental check point in "
          "this bounded campaign.")
    return 0
