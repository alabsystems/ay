# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# Differential cross-check: build a generated formula through BOTH
# `ayz3` and real `z3`, check each, and classify the pair of verdicts.

from dataclasses import dataclass, field
from typing import List, Optional

from . import gen
from .gen import Node, build, generate

# Outcome tags for a single differential case.
AGREE = "agree"          # both sat or both unsat
SKIP = "skip"            # >=1 unknown, or a binding gap / build error -> not a bug
DISAGREE = "disagree"    # one sat, one unsat -> unadjudicated verdict dispute

# Differential-finding categories for the inventory:
#   CAT_A  sat-vs-unsat disagreement (one side sat, other unsat); resolving
#          which side is wrong requires independent evidence.
#   CAT_B  genuinely-wrong model: a side reports `sat` and hands back a fully
#          concrete model whose ASSIGNED values FALSIFY the formula -- confirmed
#          by re-checking the pinned model in z3 (which returns unsat). A real
#          soundness-adjacent bug: the verdict may be right but the witness lies.
#   CAT_C  partial / unreduced model: the model could not be conclusively
#          validated by pinning (an array interpretation, an unconstrained var
#          omitted, or an opaque/unreduced value). This is EXPLICITLY NOT a bug
#          -- it is a model-readout limitation, counted separately.
CAT_A = "A:sat-vs-unsat"
CAT_B = "B:wrong-model"
CAT_C = "C:partial-or-unreduced-model"


# ---------------------------------------------------------------------------
# Module loading (ayz3 is required; z3 is optional -> graceful skip)
# ---------------------------------------------------------------------------

def _load_ayz3():
    import ayz3
    return ayz3


def _load_z3():
    try:
        import z3
        return z3
    except Exception:
        return None


def have_z3():
    return _load_z3() is not None


# ---------------------------------------------------------------------------
# Verdicts
# ---------------------------------------------------------------------------

# A per-side check result. `verdict` is one of "sat"/"unsat"/"unknown"/"skip".
@dataclass
class SideResult:
    verdict: str
    reason: str = ""          # for unknown/skip: why
    model_ok: Optional[bool] = None  # for sat: did the model satisfy the formula
    # Fully-concrete scalar model assignment (for sat), and whether it was
    # complete (all consts read as concrete scalars). Used to validate the model.
    assignment: dict = field(default_factory=dict)
    model_complete: bool = False
    model_repr: str = ""      # the model's text form (for the inventory)
    # This side's OWN model.eval(formula): True / False / None (not reducible).
    # Captured cheaply at check time (reusing the already-solved model) so the
    # categorizer doesn't have to re-solve to ask "does your own model hold?".
    own_eval: Optional[bool] = None


def _verdict_str(result_obj) -> str:
    """Normalize a z3py / ayz3 CheckSatResult to 'sat'/'unsat'/'unknown'.

    Both modules expose sat/unsat/unknown singletons whose str() is the name;
    comparing across modules by identity is unsafe, so we compare by name.
    """
    s = str(result_obj).strip().lower()
    if s in ("sat", "unsat", "unknown"):
        return s
    return "unknown"


class _NullScope:
    """A no-op context manager (for modules without per-solver contexts)."""
    def __enter__(self):
        return None

    def __exit__(self, *exc):
        return False


def _isolated_solver(m):
    """Return (solver, scope) where `scope` is a context manager that, while
    active, makes bare constructors build into THIS solver's context.

    CRITICAL for ayz3: in ayz3 a `Z3_solver` is a thin alias for its context's
    single shared assertion stack, and two Solvers over the *same* context share
    that stack. If every case reused the main context, asserts would LEAK across
    cases and ayz3 would spuriously turn unsat -- a fuzzer artifact, not a
    solver bug. So for ayz3 we give every case its OWN fresh Context and build
    inside `solver.using()`, which AY exposes for exactly this isolation.

    Real z3py has independent Solver objects natively (each `Solver()` is its
    own assertion stack) and has no `using()`; its scope is a no-op. We detect
    ayz3 by the presence of `Solver.using`, not by module name.
    """
    Context = getattr(m, "Context", None)
    solver = m.Solver()
    if Context is not None and hasattr(solver, "using"):
        # ayz3: rebuild on a fresh, isolated context.
        ctx = Context()
        solver = m.Solver(ctx)
        return solver, solver.using()
    return solver, _NullScope()


def _check_one(node: Node, m, timeout_ms: int = 2000,
               smt2_text: str = None) -> SideResult:
    """Build + check `node` through module `m` in an ISOLATED solver/context, so
    no state leaks between cases. Any build/check failure that is NOT a clean
    verdict is treated as SKIP (binding gap / unsupported op).

    A per-check `timeout_ms` bounds runtime: a check that exceeds it returns the
    solver's `unknown`, which the comparison treats as SKIP (incompleteness),
    so the fuzzer never hangs on a hard instance.

    When `smt2_text` is given (used by SMT2_FRAGMENTS such as `sequences`), the
    formula is loaded by PARSING that canonical SMT-LIB text through the module's
    `from_string` instead of building the Node in-memory -- the ONLY faithful way
    to exercise AY's (Seq Int)/(Seq Bool) theory, whose in-memory ayz3 builders
    accept only the String sort. BOTH modules parse the IDENTICAL text, so they
    decide the identical formula. (Own-model eval is skipped in this mode, since
    there is no per-module built `f` to eval; seq models are non-scalar anyway.)
    """
    try:
        solver, scope = _isolated_solver(m)
    except Exception as e:
        return SideResult("skip", reason=f"solver create error: {type(e).__name__}: {e}")

    if timeout_ms:
        try:
            solver.set("timeout", int(timeout_ms))
        except Exception:
            pass  # module without timeout support -> best effort

    with scope:
        f = None
        if smt2_text is not None:
            try:
                solver.from_string(smt2_text)
            except NotImplementedError as e:
                return SideResult("skip", reason=f"from_string NotImplementedError: {e}")
            except Exception as e:  # parser gap -> skip, not a bug
                return SideResult("skip", reason=f"from_string error: {type(e).__name__}: {e}")
        else:
            try:
                f = build(node, m)
            except NotImplementedError as e:
                return SideResult("skip", reason=f"build NotImplementedError: {e}")
            except Exception as e:  # binding gap building the term -> skip, not a bug
                return SideResult("skip", reason=f"build error: {type(e).__name__}: {e}")

            try:
                solver.add(f)
            except NotImplementedError as e:
                return SideResult("skip", reason=f"add NotImplementedError: {e}")
            except Exception as e:
                return SideResult("skip", reason=f"add error: {type(e).__name__}: {e}")

        try:
            r = solver.check()
        except NotImplementedError as e:
            return SideResult("skip", reason=f"check NotImplementedError: {e}")
        except Exception as e:
            return SideResult("skip", reason=f"check error: {type(e).__name__}: {e}")

        v = _verdict_str(r)
        side = SideResult(v)
        if v == "unknown":
            try:
                side.reason = solver.reason_unknown()
            except Exception:
                side.reason = ""
        if v == "sat":
            side.assignment, side.model_complete = _scalar_model_assignment(solver)
            try:
                model = solver.model()
                side.model_repr = repr(model)
                # Cheap own-eval: reuse the model + already-built `f` (only in the
                # in-memory path; smt2 mode has no per-module `f`).
                if f is not None:
                    try:
                        ev = model.eval(f, model_completion=True)
                        b = ev.as_bool()
                        side.own_eval = None if b is None else bool(b)
                    except Exception:
                        try:
                            side.own_eval = bool(m.is_true(
                                model.eval(f, model_completion=True)))
                        except Exception:
                            side.own_eval = None
            except Exception:
                side.model_repr = ""
        return side


def _scalar_model_assignment(solver):
    """Extract a fully-concrete scalar (Int/Real/Bool/BitVec) assignment from a
    `sat` model as {name: ('int'|'real'|'bool'|'bv', value, width?)}.

    Returns (assignment, complete) where `complete` is False if the model has
    any constant we could NOT read as a concrete scalar (e.g. an Array
    interpretation, or a None/unnamed entry). Such models can't be completely
    validated by pinning -- the caller treats that as INCONCLUSIVE (None), not a
    failure: it is the binding's documented non-scalar model-readout gap, not a
    wrong sat/unsat verdict.
    """
    out = {}
    try:
        model = solver.model()
        decls = model.decls()
    except Exception:
        return {}, False
    for d in decls:
        try:
            name = d.name()
        except Exception:
            return out, False
        if not name:
            return out, False  # unnamed entry (e.g. array interp) -> incomplete
        val = model[d]
        if val is None:
            return out, False
        kind = _scalar_kind(val)
        if kind is None:
            return out, False  # non-scalar / unreadable -> incomplete
        out[name] = kind
    return out, True


def _scalar_kind(val):
    """Classify a model VALUE AstRef as a concrete scalar, or None if it is not
    a readable scalar literal (array, symbolic, etc.)."""
    # Floating-point values are NOT scalar-pinnable through the Int/Real/BV/Bool
    # pin logic below (there is no FP case in `_validate_model_via_z3`; pinning an
    # FP const as a like-named Real const is a DIFFERENT variable -> a bogus,
    # untimed FP re-solve). An FP value's `as_fraction()` would otherwise
    # misclassify it as ("real", ...), so treat it as non-scalar here: the qf_fp
    # model becomes an honest CAT_C partial (no wrong-model claim), and no slow
    # untimed re-solve is triggered. FP values expose `ebits()` on both modules;
    # nothing else does, so this leaves every other fragment's classification
    # byte-for-byte unchanged.
    if hasattr(val, "ebits"):
        return None
    # Bool
    try:
        b = val.as_bool()
        if b is not None:
            return ("bool", b, None)
    except Exception:
        pass
    s = str(val).strip()
    # BitVec literal (binding renders as e.g. #x0a / #b0101, or numeric).
    width = None
    try:
        width = val.size  # BitVecRef has .size
    except Exception:
        width = None
    try:
        n = val.as_long()
        if width is not None:
            return ("bv", n, width)
        return ("int", n, None)
    except Exception:
        pass
    # Rational / Real
    try:
        fr = val.as_fraction()
        return ("real", fr, None)
    except Exception:
        pass
    return None


def _validate_model_via_z3(node, assignment, z3_mod) -> Optional[bool]:
    """Cross-check whether `assignment` (a fully-concrete scalar model)
    satisfies `node`, by pinning the values in z3 and asking
    for sat. Returns True (satisfies), False (does NOT satisfy -> a genuine BAD
    model), or None if it can't be pinned."""
    try:
        f = build(node, z3_mod)
        s = z3_mod.Solver()
        s.add(f)
        for name, (kind, value, width) in assignment.items():
            if kind == "bool":
                v = z3_mod.Bool(name)
                s.add(v == z3_mod.BoolVal(value))
            elif kind == "int":
                s.add(z3_mod.Int(name) == z3_mod.IntVal(value))
            elif kind == "bv":
                s.add(z3_mod.BitVec(name, width) == z3_mod.BitVecVal(value, width))
            elif kind == "real":
                s.add(z3_mod.Real(name) ==
                      z3_mod.RealVal(value.numerator) / z3_mod.RealVal(value.denominator))
            else:
                return None
        r = str(s.check()).strip().lower()
        if r == "sat":
            return True
        if r == "unsat":
            return False
        return None
    except Exception:
        return None


def _assignment_to_smt2(assignment) -> str:
    """Render a scalar assignment as SMT-LIB equality assertions (for the
    inventory's reproducible model pin)."""
    lines = []
    for name, (kind, value, width) in sorted(assignment.items()):
        if kind == "bool":
            lines.append(f"(assert (= {name} {str(bool(value)).lower()}))")
        elif kind == "int":
            v = f"(- {-value})" if value < 0 else str(value)
            lines.append(f"(assert (= {name} {v}))")
        elif kind == "bv":
            lines.append(f"(assert (= {name} (_ bv{value % (1 << width)} {width})))")
        elif kind == "real":
            num, den = value.numerator, value.denominator
            nstr = f"(- {-num})" if num < 0 else f"{num}.0"
            if num < 0:
                nstr = f"(- {-num}.0)"
            lines.append(f"(assert (= {name} (/ {nstr} {den}.0)))")
    return "\n".join(lines)


def _reconfirm_wrong_model_via_smtlib(node, assignment, z3_mod) -> Optional[bool]:
    """SECOND, INDEPENDENT confirmation that `assignment` falsifies `node`.

    Where `_validate_model_via_z3` pins the model on the in-memory builder, this
    path renders the formula to canonical SMT-LIB text, appends the model as
    SMT-LIB equality assertions, re-parses the whole thing in a FRESH z3 solver,
    and checks. If BOTH the in-memory pin and this rendered-and-reparsed pin
    return unsat, the wrong-model finding is double-confirmed and can go in the
    inventory with zero risk of being a builder artifact.

    Returns True (model satisfies), False (model falsifies -> confirmed bad), or
    None (could not confirm either way; treat as inconclusive).
    """
    try:
        f = build(node, z3_mod)
        s = z3_mod.Solver()
        s.add(f)
        smt2 = s.sexpr().strip() + "\n" + _assignment_to_smt2(assignment) + "\n(check-sat)\n"
        s2 = z3_mod.Solver()
        s2.from_string(smt2)
        r = str(s2.check()).strip().lower()
        if r == "sat":
            return True
        if r == "unsat":
            return False
        return None
    except Exception:
        return None


def _scalars_pinned_array_free_sat(node, assignment, z3_mod) -> Optional[bool]:
    """Pin ONLY the scalar (Int/Real/Bool/BitVec) consts from `assignment` in z3
    and leave any array (or other un-pinnable) decls FREE, then check sat. If sat,
    SOME completion of the free parts satisfies AY's scalar choices -- so when
    AY's own model (with its specific array) falsifies the formula, AY's array
    choice is provably wrong. Independent of AY's evaluator.

    Returns True/False/None (inconclusive)."""
    try:
        f = build(node, z3_mod)
        s = z3_mod.Solver()
        s.add(f)
        for name, (kind, value, width) in assignment.items():
            if kind == "bool":
                s.add(z3_mod.Bool(name) == z3_mod.BoolVal(value))
            elif kind == "int":
                s.add(z3_mod.Int(name) == z3_mod.IntVal(value))
            elif kind == "bv":
                s.add(z3_mod.BitVec(name, width) == z3_mod.BitVecVal(value, width))
            elif kind == "real":
                s.add(z3_mod.Real(name) ==
                      z3_mod.RealVal(value.numerator) / z3_mod.RealVal(value.denominator))
            # non-scalar entries are simply left free
        r = str(s.check()).strip().lower()
        if r == "sat":
            return True
        if r == "unsat":
            return False
        return None
    except Exception:
        return None


def _own_eval_satisfies(node, m, timeout_ms=2000) -> Optional[bool]:
    """Ask module `m` itself whether its OWN model satisfies the formula, by
    re-solving and calling `model.eval(f, model_completion=True)`. This is the
    strongest evidence a wrong model is the SOLVER's fault (not our scalar
    readout): if AY says `sat` but AY's own `eval` of the formula in AY's own
    model returns False, the model genuinely contradicts the formula.

    Returns True / False (eval result as bool) or None if eval is unavailable or
    not reducible to a Bool literal (an honest 'inconclusive')."""
    try:
        solver, scope = _isolated_solver(m)
    except Exception:
        return None
    if timeout_ms:
        try:
            solver.set("timeout", int(timeout_ms))
        except Exception:
            pass
    with scope:
        try:
            f = build(node, m)
            solver.add(f)
            if _verdict_str(solver.check()) != "sat":
                return None
            model = solver.model()
            ev = model.eval(f, model_completion=True)
        except Exception:
            return None
        try:
            b = ev.as_bool()
            if b is None:
                return None
            return bool(b)
        except Exception:
            # Last resort: textual is_true.
            try:
                return bool(m.is_true(ev))
            except Exception:
                return None


# ---------------------------------------------------------------------------
# Case + summary records
# ---------------------------------------------------------------------------

@dataclass
class CaseResult:
    fragment: str
    seed: int
    outcome: str               # AGREE / SKIP / DISAGREE
    ay: SideResult
    z3: SideResult
    note: str = ""


@dataclass
class Disagreement:
    fragment: str
    seed: int
    ay_verdict: str
    z3_verdict: str
    smtlib: str
    model_note: str = ""

    def banner(self) -> str:
        lines = [
            "",
            "=" * 70,
            "  VERDICT DISPUTE: sat-vs-unsat DISAGREEMENT",
            "=" * 70,
            f"  fragment : {self.fragment}",
            f"  seed     : {self.seed}",
            f"  ayz3     : {self.ay_verdict}",
            f"  z3 (4.x) : {self.z3_verdict}",
        ]
        if self.model_note:
            lines.append(f"  model    : {self.model_note}")
        lines += [
            f"  repro    : generate({self.fragment!r}, {self.seed})",
            "  SMT-LIB  :",
        ]
        for ln in self.smtlib.splitlines():
            lines.append(f"      {ln}")
        lines.append("=" * 70)
        return "\n".join(lines)


@dataclass
class Finding:
    """A single categorized inventory entry (one distinct finding class)."""
    category: str           # CAT_A / CAT_B / CAT_C
    fragment: str
    seed: int
    ay_verdict: str
    z3_verdict: str
    smtlib: str
    model_repr: str = ""        # the offending side's model, as text
    reconfirmed: bool = False   # re-verified against z3 (for A/B)
    own_eval: Optional[bool] = None  # AY's own model.eval(formula) result (B)
    note: str = ""

    def banner(self) -> str:
        head = {
            CAT_A: "VERDICT DISPUTE: sat-vs-unsat DISAGREEMENT",
            CAT_B: "WRONG MODEL: sat reported, model FALSIFIES formula",
            CAT_C: "PARTIAL/UNREDUCED MODEL (NOT A BUG)",
        }.get(self.category, self.category)
        lines = [
            "", "=" * 70, f"  [{self.category}] {head}", "=" * 70,
            f"  fragment : {self.fragment}",
            f"  seed     : {self.seed}",
            f"  ayz3     : {self.ay_verdict}",
            f"  z3 (4.x) : {self.z3_verdict}",
        ]
        if self.model_repr:
            lines.append(f"  ay model : {self.model_repr}")
        if self.own_eval is not None:
            lines.append(f"  AY own model.eval(formula) = {self.own_eval}")
        if self.category in (CAT_A, CAT_B):
            lines.append(f"  re-confirmed vs z3 = {self.reconfirmed}")
        if self.note:
            lines.append(f"  note     : {self.note}")
        lines += [f"  repro    : generate({self.fragment!r}, {self.seed})",
                  "  SMT-LIB  :"]
        for ln in self.smtlib.splitlines():
            lines.append(f"      {ln}")
        lines.append("=" * 70)
        return "\n".join(lines)


@dataclass
class RunSummary:
    fragment: str
    count: int
    agree: int = 0
    skip: int = 0
    disagree: int = 0
    agree_sat: int = 0
    agree_unsat: int = 0
    model_validated: int = 0
    model_invalid: int = 0   # sat reported but model FAILED to satisfy (own-side bug)
    model_partial: int = 0   # CAT_C: sat with a model we couldn't pin (NOT a bug)
    disagreements: List[Disagreement] = field(default_factory=list)
    self_model_bugs: List[CaseResult] = field(default_factory=list)
    findings: List[Finding] = field(default_factory=list)  # categorized inventory

    def line(self) -> str:
        return (f"[{self.fragment}] checked={self.count} "
                f"agree={self.agree} (sat={self.agree_sat} unsat={self.agree_unsat}) "
                f"skip={self.skip} DISAGREE={self.disagree} "
                f"model_ok={self.model_validated} model_BAD={self.model_invalid} "
                f"model_partial={self.model_partial}")

    def findings_by_cat(self):
        out = {CAT_A: [], CAT_B: [], CAT_C: []}
        for f in self.findings:
            out.setdefault(f.category, []).append(f)
        return out


# ---------------------------------------------------------------------------
# Single-case comparison
# ---------------------------------------------------------------------------

def _render_smt2(node: Node, z3_mod) -> Optional[str]:
    """Render `node` to canonical SMT-LIB text via z3py (the reference renderer),
    or None if it cannot be rendered. Used by SMT2_FRAGMENTS to feed the IDENTICAL
    text to both modules' `from_string`."""
    smt = _smtlib_for(node, z3_mod)
    if not isinstance(smt, str) or smt.startswith("<"):
        return None
    return smt


def run_case(fragment: str, seed: int, ayz3_mod=None, z3_mod=None,
             timeout_ms: int = 2000) -> CaseResult:
    """Generate one formula and compare the two modules on it."""
    ayz3_mod = ayz3_mod or _load_ayz3()
    z3_mod = z3_mod or _load_z3()

    node = generate(fragment, seed)

    # SMT2 fragments (e.g. sequences): render the formula ONCE to canonical
    # SMT-LIB and PARSE the same text through both modules, rather than building
    # the Node in-memory. This needs z3 (the reference renderer) present.
    smt2_text = None
    if fragment in gen.SMT2_FRAGMENTS:
        if z3_mod is None:
            return CaseResult(fragment, seed, SKIP,
                              SideResult("skip", reason="z3 required to render SMT-LIB"),
                              SideResult("skip", reason="z3 not installed"),
                              note="z3 absent")
        smt2_text = _render_smt2(node, z3_mod)
        if smt2_text is None:
            return CaseResult(fragment, seed, SKIP,
                              SideResult("skip", reason="SMT-LIB render failed"),
                              SideResult("skip", reason="SMT-LIB render failed"),
                              note="render failed")

    ay = _check_one(node, ayz3_mod, timeout_ms=timeout_ms, smt2_text=smt2_text)

    if z3_mod is None:
        return CaseResult(fragment, seed, SKIP, ay,
                          SideResult("skip", reason="z3 not installed"),
                          note="z3 absent")

    z = _check_one(node, z3_mod, timeout_ms=timeout_ms, smt2_text=smt2_text)

    # Model-validation strengthening (ayz3 side): when ayz3 returns sat with a
    # FULLY-CONCRETE scalar model, cross-check via z3 that the model
    # actually satisfies the formula. Incomplete models (e.g. arrays, where the
    # binding's model readout omits array interpretations) are left as None =
    # INCONCLUSIVE -- a documented readout gap, NOT a wrong model.
    if ay.verdict == "sat":
        if ay.model_complete and ay.assignment:
            ay.model_ok = _validate_model_via_z3(node, ay.assignment, z3_mod)
        else:
            ay.model_ok = None
    if z.verdict == "sat" and z.model_complete and z.assignment:
        z.model_ok = _validate_model_via_z3(node, z.assignment, z3_mod)

    # Pairwise classification. Agreement is corroboration, not proof; a split
    # is a dispute and does not identify which implementation is wrong.
    if ay.verdict == "skip" or z.verdict == "skip":
        return CaseResult(fragment, seed, SKIP, ay, z)
    if ay.verdict == "unknown" or z.verdict == "unknown":
        return CaseResult(fragment, seed, SKIP, ay, z)
    if ay.verdict == z.verdict:
        return CaseResult(fragment, seed, AGREE, ay, z)
    # sat vs unsat -> unadjudicated verdict dispute.
    return CaseResult(fragment, seed, DISAGREE, ay, z)


# ---------------------------------------------------------------------------
# Shrinking: minimize a disagreeing formula while preserving the disagreement.
# ---------------------------------------------------------------------------

def _disagrees(node: Node, ayz3_mod, z3_mod, timeout_ms: int = 2000) -> bool:
    ay = _check_one(node, ayz3_mod, timeout_ms=timeout_ms)
    z = _check_one(node, z3_mod, timeout_ms=timeout_ms)
    if ay.verdict in ("skip", "unknown") or z.verdict in ("skip", "unknown"):
        return False
    return ay.verdict != z.verdict


def _children_candidates(node: Node):
    """Yield smaller replacement nodes for `node` that keep it Bool-typed.

    We try replacing a boolean node with one of its boolean children (collapsing
    And/Or/Not/Implies/Xor/ite structure), which monotonically shrinks the tree.
    """
    if node.sort != gen.SORT_BOOL:
        return
    for c in node.children:
        if c.sort == gen.SORT_BOOL:
            yield c


def _replace_subtree(root: Node, target: Node, replacement: Node) -> Node:
    """Return a copy of `root` with the first occurrence (by identity) of
    `target` replaced by `replacement`."""
    if root is target:
        return replacement
    new_children = [_replace_subtree(c, target, replacement) for c in root.children]
    return Node(root.op, root.sort, new_children, root.payload)


def _iter_bool_subtrees(node: Node):
    if node.sort == gen.SORT_BOOL:
        yield node
    for c in node.children:
        yield from _iter_bool_subtrees(c)


def _shrink_while(node: Node, pred, max_iters: int = 400,
                  time_budget_s: float = None) -> Node:
    """Greedily replace boolean subtrees with smaller boolean children as long as
    `pred(trial)` still holds. Returns the smallest formula found.

    `time_budget_s` (optional) caps total wall-clock: shrinking is a best-effort
    minimization, so on slow theories (e.g. arrays, where each predicate call
    re-solves) we stop early and return the smallest form found so far rather
    than burn minutes chasing a marginally smaller repro."""
    import time
    deadline = (time.time() + time_budget_s) if time_budget_s else None
    current = node
    changed = True
    iters = 0
    while changed and iters < max_iters:
        if deadline and time.time() > deadline:
            break
        changed = False
        for sub in list(_iter_bool_subtrees(current)):
            for cand in _children_candidates(sub):
                iters += 1
                if iters >= max_iters or (deadline and time.time() > deadline):
                    break
                trial = _replace_subtree(current, sub, cand)
                if trial is current:
                    continue
                if pred(trial):
                    current = trial
                    changed = True
                    break
            if changed or (deadline and time.time() > deadline):
                break
    return current


def shrink(node: Node, ayz3_mod, z3_mod, max_iters: int = 400,
           timeout_ms: int = 2000, time_budget_s: float = 20.0) -> Node:
    """Greedily replace boolean subtrees with smaller boolean subtrees as long
    as the disagreement is preserved. Returns the smallest formula found."""
    return _shrink_while(
        node, lambda t: _disagrees(t, ayz3_mod, z3_mod, timeout_ms=timeout_ms),
        max_iters=max_iters, time_budget_s=time_budget_s,
    )


def _has_wrong_model(node: Node, ayz3_mod, z3_mod, timeout_ms: int = 2000) -> bool:
    """True iff AY reports `sat` for `node` but AY's OWN model.eval(formula) is
    False -- the invariant the wrong-model shrinker must preserve. Using AY's own
    eval (not our scalar pin) keeps the shrinker faithful to the actual bug even
    on formulas whose model we couldn't otherwise pin."""
    own = _own_eval_satisfies(node, ayz3_mod, timeout_ms=timeout_ms)
    return own is False


def shrink_wrong_model(node: Node, ayz3_mod, z3_mod, max_iters: int = 80,
                       timeout_ms: int = 2000, time_budget_s: float = 8.0) -> Node:
    """Minimize a CAT_B (wrong-model) formula while AY keeps producing a model
    that falsifies it (per AY's own eval). Bounded by `time_budget_s` because each
    predicate call re-solves -- on array theories an unbounded shrink can take
    minutes; a bounded one still yields a usefully-small, valid repro."""
    return _shrink_while(
        node,
        lambda t: _has_wrong_model(t, ayz3_mod, z3_mod, timeout_ms=timeout_ms),
        max_iters=max_iters, time_budget_s=time_budget_s,
    )


# ---------------------------------------------------------------------------
# SMT-LIB rendering (via real z3py, which produces canonical SMT-LIB)
# ---------------------------------------------------------------------------

def _smtlib_for(node: Node, z3_mod) -> str:
    try:
        f = build(node, z3_mod)
        s = z3_mod.Solver()
        s.add(f)
        return s.sexpr().strip()
    except Exception as e:
        return f"<could not render SMT-LIB: {type(e).__name__}: {e}>"


# ---------------------------------------------------------------------------
# Campaign runner
# ---------------------------------------------------------------------------

def run_campaign(fragment: str, count: int, seed_start: int = 0,
                 ayz3_mod=None, z3_mod=None, stop_on_disagree: bool = False,
                 progress=None, timeout_ms: int = 2000,
                 max_findings_per_cat: int = 0) -> RunSummary:
    """Run `count` differential cases for `fragment`, seeds [seed_start, ...).

    Returns a RunSummary. On a disagreement the formula is shrunk to a minimal
    repro and its SMT-LIB captured. `timeout_ms` bounds each individual check so
    a hard instance becomes `unknown` (a SKIP) rather than hanging the run.

    `max_findings_per_cat` (0 = unlimited) caps how many CAT_A / CAT_B findings
    are FULLY constructed (each involves an expensive shrink + render). The
    COUNTS (disagree / model_invalid / model_partial) remain exact regardless --
    only the number of detailed, shrunk repros captured is bounded, which keeps a
    big inventory campaign fast while still capturing the distinct classes.
    """
    ayz3_mod = ayz3_mod or _load_ayz3()
    z3_mod = z3_mod if z3_mod is not None else _load_z3()
    summ = RunSummary(fragment=fragment, count=count)
    n_a = n_b = 0  # findings built per category (for the cap)

    for k in range(count):
        seed = seed_start + k
        case = run_case(fragment, seed, ayz3_mod, z3_mod, timeout_ms=timeout_ms)
        if case.outcome == AGREE:
            summ.agree += 1
            if case.ay.verdict == "sat":
                summ.agree_sat += 1
                # model-validation accounting (ayz3 side)
                if case.ay.model_ok is True:
                    summ.model_validated += 1
                elif case.ay.model_ok is False:
                    # CAT_B candidate: our scalar pin made the formula unsat. But
                    # a scalar pin is only applicable when the model is TRULY
                    # complete -- if the formula has an uninterpreted function (or
                    # other structure) whose interpretation the model omits,
                    # pinning just the scalar consts can spuriously force unsat.
                    # ARBITER: ask AY itself whether its OWN (full) model
                    # satisfies the formula. If AY's own eval says True, the pin
                    # was incomplete -> this is a PARTIAL model (CAT_C), NOT a
                    # bug. Only when AY's own eval ALSO says False (or is
                    # inconclusive but the pin holds) is it a real wrong model.
                    own = case.ay.own_eval  # captured cheaply at check time
                    if own is True:
                        # AY's full model satisfies it; the scalar pin was partial
                        # (e.g. an uninterpreted function interp was omitted).
                        summ.model_partial += 1
                    else:
                        summ.model_invalid += 1
                        summ.self_model_bugs.append(case)
                        if not max_findings_per_cat or n_b < max_findings_per_cat:
                            summ.findings.append(
                                _build_wrong_model_finding(fragment, seed, case,
                                                           z3_mod, ayz3_mod, timeout_ms)
                            )
                            n_b += 1
                elif case.ay.model_ok is None and not case.ay.model_complete:
                    # The scalar pin was inconclusive (an array interp or other
                    # non-scalar value we can't pin). This is USUALLY CAT_C (a
                    # readout gap, not a bug) -- but we must still catch the case
                    # where AY's OWN model is self-contradictory. ARBITER: ask AY
                    # to eval the formula in its own (full) model.
                    #   own == True  -> sound partial model (CAT_C, not a bug).
                    #   own == False -> AY claims `sat` yet its OWN model
                    #                   FALSIFIES the formula: a genuine wrong
                    #                   model (CAT_B), confirmed by AY itself.
                    #   own == None  -> eval not reducible -> stay CAT_C.
                    own = case.ay.own_eval  # captured cheaply at check time
                    if own is False:
                        summ.model_invalid += 1
                        summ.self_model_bugs.append(case)
                        if not max_findings_per_cat or n_b < max_findings_per_cat:
                            summ.findings.append(
                                _build_wrong_model_finding(
                                    fragment, seed, case, z3_mod, ayz3_mod,
                                    timeout_ms, scalar_pinnable=False)
                            )
                            n_b += 1
                    else:
                        summ.model_partial += 1
            else:
                summ.agree_unsat += 1
        elif case.outcome == SKIP:
            summ.skip += 1
        elif case.outcome == DISAGREE:
            summ.disagree += 1
            node = generate(fragment, seed)
            # Shrinking re-checks via the in-memory build path; SMT2 fragments
            # (sequences) can't reproduce through it on ayz3 (the seq theory is
            # only reachable via the parser), so keep the unshrunk repro. The
            # generator already bounds formula depth, so the repro stays small.
            if z3_mod is not None and fragment not in gen.SMT2_FRAGMENTS:
                node = shrink(node, ayz3_mod, z3_mod, timeout_ms=timeout_ms)
            smt = _smtlib_for(node, z3_mod) if z3_mod is not None else "<no z3>"
            model_note = ""
            if case.ay.verdict == "sat" and case.ay.model_ok is not None:
                model_note = (f"ayz3 model satisfies formula = {case.ay.model_ok}")
            elif case.z3.verdict == "sat" and case.z3.model_ok is not None:
                model_note = (f"z3 model satisfies formula = {case.z3.model_ok}")
            dis = Disagreement(
                fragment=fragment, seed=seed,
                ay_verdict=case.ay.verdict, z3_verdict=case.z3.verdict,
                smtlib=smt, model_note=model_note,
            )
            summ.disagreements.append(dis)
            # CAT_A finding (shrunk repro), with the winning side's model
            # independently re-confirmed against the SHRUNK formula.
            if not max_findings_per_cat or n_a < max_findings_per_cat:
                summ.findings.append(
                    _build_disagreement_finding(fragment, seed, case, node, smt,
                                                z3_mod, ayz3_mod=ayz3_mod)
                )
                n_a += 1
            if progress:
                progress(dis.banner())
            if stop_on_disagree:
                break
        if progress and (k + 1) % 200 == 0:
            progress(f"  ...{fragment}: {k + 1}/{count} done ({summ.line()})")

    return summ


def _ay_parse_path_verdict(smt, ayz3_mod, timeout_ms=2000) -> Optional[str]:
    """Re-check `smt` (SMT-LIB text) through AY's OWN PARSER (`from_string`)
    instead of the in-memory builder. Returns 'sat'/'unsat'/'unknown' or None.

    This distinguishes a binding-builder-path bug (wrong only when the term is
    built in-memory via the C ABI) from a core-decision-procedure bug (wrong even
    when the equivalent SMT-LIB is parsed). It is the same distinction AY's
    NATIVE CLI exposes on the rendered repro file."""
    try:
        Context = getattr(ayz3_mod, "Context", None)
        if Context is None:
            s = ayz3_mod.Solver()
            s.from_string(smt)
            return _verdict_str(s.check())
        ctx = Context()
        s = ayz3_mod.Solver(ctx)
        with s.using():
            if timeout_ms:
                try:
                    s.set("timeout", int(timeout_ms))
                except Exception:
                    pass
            s.from_string(smt)
            return _verdict_str(s.check())
    except Exception:
        return None


def _build_disagreement_finding(fragment, seed, case, shrunk_node, smt, z3_mod,
                                ayz3_mod=None):
    """Build a CAT_A Finding, re-confirming the wrong verdict against z3 on the
    SHRUNK formula: whichever side said `sat`, we re-solve the shrunk formula in
    z3 and confirm z3's own model satisfies it -- so the wrong `unsat` (or wrong
    `sat`) is unambiguously the OTHER side's. Also probes AY's PARSE path to label
    the bug as builder-path-only vs core-level (reproduces via SMT-LIB too)."""
    reconfirmed = False
    note = ""
    if z3_mod is not None and shrunk_node is not None:
        try:
            f = build(shrunk_node, z3_mod)
            s = z3_mod.Solver()
            s.add(f)
            r = str(s.check()).strip().lower()
            if r == "sat":
                # z3 finds the shrunk formula sat -> if AY said unsat, AY is
                # wrong. Confirm z3's model genuinely satisfies it.
                ok = z3_mod.is_true(s.model().eval(f, model_completion=True))
                reconfirmed = bool(ok) and case.ay.verdict == "unsat"
                note = "z3 sat + model-validated; AY's unsat is the wrong answer"
            elif r == "unsat":
                reconfirmed = case.z3.verdict == "sat" and case.ay.verdict == "unsat"
                note = "z3 re-check unsat on shrunk form (verdict still differs unshrunk)"
        except Exception as e:
            note = f"reconfirm error: {type(e).__name__}: {e}"
    # Path-dependence probe: does AY's PARSER reproduce the wrong verdict?
    if ayz3_mod is not None and isinstance(smt, str) and not smt.startswith("<"):
        parse_v = _ay_parse_path_verdict(smt, ayz3_mod)
        if parse_v is not None:
            if parse_v == case.ay.verdict:
                note += (f"; CORE-LEVEL: AY's parse path ALSO returns "
                         f"{parse_v} (wrong via SMT-LIB too)")
            else:
                note += (f"; BUILDER-PATH-ONLY: AY's parse path returns "
                         f"{parse_v} (correct) -- the wrong "
                         f"{case.ay.verdict} comes from the in-memory build path")
    return Finding(
        category=CAT_A, fragment=fragment, seed=seed,
        ay_verdict=case.ay.verdict, z3_verdict=case.z3.verdict,
        smtlib=smt, model_repr=case.z3.model_repr or case.ay.model_repr,
        reconfirmed=reconfirmed, note=note,
    )


def _build_wrong_model_finding(fragment, seed, case, z3_mod, ayz3_mod, timeout_ms,
                               scalar_pinnable=True):
    """Build a CAT_B Finding (AY said sat, model falsifies the formula).

    Two confirmation regimes, depending on whether the model is scalar-pinnable:

    SCALAR-PINNABLE (Int/Real/Bool/BitVec model -- `scalar_pinnable=True`):
      1. in-memory pin (case.ay.model_ok is False -- already computed),
      2. rendered-SMT-LIB reparse-and-pin in a fresh z3 solver,
      3. AY's OWN model.eval(formula) == False.
      A finding is `reconfirmed` only if (2) also says the model is bad.

    NON-SCALAR (e.g. an array interp we cannot pin in z3 --
    `scalar_pinnable=False`): the confirmation is AY's SELF-CONTRADICTION -- AY
    returns `sat` AND AY's own `model.eval(formula)` returns False, while z3
    independently proves the formula sat (so the verdict is sound but the witness
    is broken). `reconfirmed` is True iff AY's own eval is False (the
    self-contradiction is the proof)."""
    node = generate(fragment, seed)
    # Shrink to a minimal formula that STILL exhibits the wrong model (per AY's
    # own eval), then recompute the model + confirmations on the shrunk form.
    shrunk = node
    if z3_mod is not None:
        shrunk = shrink_wrong_model(node, ayz3_mod, z3_mod, timeout_ms=timeout_ms)
    # Re-extract AY's model + scalar assignment on the shrunk formula.
    sh_side = _check_one(shrunk, ayz3_mod, timeout_ms=timeout_ms)
    node = shrunk
    model_repr = sh_side.model_repr or case.ay.model_repr
    assignment = sh_side.assignment or case.ay.assignment
    smt = _smtlib_for(node, z3_mod) if z3_mod is not None else "<no z3>"
    own = _own_eval_satisfies(node, ayz3_mod, timeout_ms=timeout_ms)
    # Independent z3 verdict on the shrunk form (formula really is sat).
    z3_sat = None
    if z3_mod is not None:
        try:
            fz = build(node, z3_mod)
            sz = z3_mod.Solver()
            sz.add(fz)
            z3_sat = str(sz.check()).strip().lower() == "sat"
        except Exception:
            z3_sat = None

    if scalar_pinnable:
        reconfirm = None
        if z3_mod is not None:
            reconfirm = _reconfirm_wrong_model_via_smtlib(node, assignment, z3_mod)
        parts = ["in-memory pin: model falsifies formula (unsat when pinned)"]
        if reconfirm is False:
            parts.append("rendered-SMT-LIB reparse: also unsat when pinned")
        elif reconfirm is True:
            parts.append("WARNING: rendered reparse said SAT (pin path mismatch)")
        if own is False:
            parts.append("AY's own model.eval(formula) = False")
        elif own is True:
            parts.append("AY's own model.eval(formula) = True (inconsistent!)")
        reconfirmed = (reconfirm is False)
    else:
        # Non-scalar (array) model: we cannot pin the array interp in z3, but we
        # CAN confirm AY's model is wrong WITHOUT trusting AY's eval: pin only
        # the scalar consts in z3 and leave the array FREE. If that is still sat,
        # then SOME array completes AY's scalars into a satisfying model -- so the
        # specific array AY chose (which makes its own eval False) is wrong.
        scalars_free_array = _scalars_pinned_array_free_sat(node, assignment, z3_mod)
        parts = ["non-scalar (array) model: cannot pin array interp in z3"]
        if own is False:
            parts.append("AY's own model.eval(formula) = False (AY self-contradicts)")
        if scalars_free_array is True:
            parts.append("z3 with AY's scalars pinned + array FREE is SAT "
                         "(a valid array exists; AY chose a wrong one)")
        if z3_sat is True:
            parts.append("z3 independently proves the formula SAT (verdict sound, "
                         "witness broken)")
        # Confirmed when AY self-contradicts AND an array-free pin shows a valid
        # completion exists (independent of AY's eval).
        reconfirmed = (own is False) and (scalars_free_array is True)

    return Finding(
        category=CAT_B, fragment=fragment, seed=seed,
        ay_verdict=case.ay.verdict, z3_verdict=case.z3.verdict,
        smtlib=smt, model_repr=model_repr,
        reconfirmed=reconfirmed, own_eval=own,
        note="; ".join(parts),
    )
