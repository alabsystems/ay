// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Finite domain quantifier expansion.
//!
//! Eliminates quantifiers over finite domains (Bool, small BitVec, bounded Int)
//! by enumerating all values and conjoining/disjoining the instantiated body.
//!
//! Extracted from `skolemize.rs` for code health (#5970).

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::{Constant, Symbol};
use ay_core::{Sort, TermData, TermId, TermStore};
use num_bigint::BigInt;
use num_traits::ToPrimitive;

use crate::cegqi::has_bound_dependent_bool_uf;
use crate::ematching::{contains_quantifier, subst_vars};

/// Maximum total combinations for finite domain expansion.
/// Beyond this threshold, fall back to E-matching to avoid exponential blowup.
const MAX_FINITE_DOMAIN_COMBOS: u64 = 256;

/// Extended single-Int-binder expansion budget for the shapes NOTHING
/// downstream can decide (rank-9 step 1, witness-directed discharge for
/// verification-consumer existential preconditions).
///
/// A triggerless single-Int-binder quantifier whose body applies a Bool UF to
/// the binder is exactly the class that (a) arithmetic CEGQI must refuse
/// (`has_bound_dependent_bool_uf` — no bound extraction through an opaque
/// predicate), (b) E-matching cannot cover completely (infinite domain), and
/// (c) MBQI cannot evaluate (UF atoms have no model value at fresh points), so
/// past the default 256-combo budget it always fails closed to
/// `Unknown(QuantifierUnhandled)`. When its guard atoms pin the binder to a
/// PROVABLY-complete constant range, full expansion is an exact logical
/// equivalence (the guard disjuncts/conjuncts make the body vacuous outside
/// the range), so spending a larger budget converts those Unknowns into
/// decided verdicts in both directions: a satisfiable instance found by the
/// ground solve is a verified witness (the model is validated downstream as
/// usual), and a refuted expansion is a sound refutation of the existential
/// (the expansion is equivalent, not merely an under-approximation).
/// Restricted to bodies with no nested quantifier so recursive expansion
/// cannot multiply budgets.
///
/// BUDGET COUPLING: the expansion's ground instances become E-matching
/// candidates for every OTHER quantifier over the same predicate (e.g. a
/// pointwise `forall v. P(v) = rhs` definition instantiates once per expanded
/// `P(i)`), and E-matching caps instances per quantifier at 1000
/// (`EMatchingConfig::max_per_quantifier`) — tripping that cap sets
/// `reached_limit`, which soundly FORFEITS the model-backed UF-completion
/// certificate and turns a decidable problem back into Unknown. 512 keeps a
/// single expansion safely under that budget; ranges past it stay with
/// Skolemization (positive exists) / enumerative instantiation (negated
/// exists), where the certificate route decides the definitional cases
/// without any expansion.
const MAX_BOUND_BOOL_UF_INT_COMBOS: u64 = 512;

/// Info about a bounded integer quantifier: the variable's range and the
/// inner body with the guard stripped (for forall) or kept (for exists).
struct BoundedIntInfo {
    /// Lower bound (inclusive)
    lo: i64,
    /// Upper bound (inclusive)
    hi: i64,
    /// The body to instantiate. For forall, this is the inner body with the
    /// guard stripped. For exists, this is the full body (guard kept).
    body: TermId,
}

/// Check if a term is a reference to the named bound variable.
fn is_bound_var(terms: &TermStore, term: TermId, var_name: &str) -> bool {
    matches!(terms.get(term), TermData::Var(name, _) if name == var_name)
}

// #entailed-bound-expansion: the table of integer constants the problem's
// quantifier-free consequences ENTAIL (see quantifier_loop::entailed_consts).
//
// Scoped, not ambient: `process_quantifiers` installs it immediately before its
// single `expand_finite_domains()` call.  The RAII scope below restores the
// predecessor even if expansion unwinds, so it is never leaked into a nested
// sub-solve (which runs on a SUBSET of the assertions that need not entail these
// constants).
thread_local! {
    static DERIVED: std::cell::RefCell<HashMap<TermId, BigInt>> =
        std::cell::RefCell::new(Default::default());
}

// #bool-ground-inst: ground Bool-sorted UF-argument terms of the CURRENT
// assertion set, used as EXTRA instantiation points for Bool binders in the
// generic finite-domain path below.
//
// Why this is sound AT ANY POLARITY (unlike DERIVED, no entailment is needed):
// for a Bool binder x, every model interprets a ground Bool term `c` as `true`
// or `false`, so `P(c)` is semantically REDUNDANT given `P(true) /\ P(false)`
// (forall) and `P(c) -> P(true) \/ P(false)` (exists). Adding the instance
// therefore preserves EQUIVALENCE of the expansion — it changes nothing
// semantically, but hands the ground solver the syntactic congruence link
// `f(c) = ...` that the two-point expansion destroys. That link is exactly the
// #bool-arg-congruence gap: the opaque Bool const `c` never appears as a SAT
// atom, so EUF never merges it with the true/false class, and `f(c)` floats
// free of `f(true)`/`f(false)` (incremental mode has no congruence lemma — see
// executor/theories/euf.rs — so a `forall x:Bool {f(x)}. f(x)=true` axiom with
// a pushed `f(c)=false` came back Unknown instead of UNSAT).
//
// Scoped like DERIVED: `expand_finite_domains()` (quantifier_loop/preprocess)
// installs it from its own assertion set immediately before expanding.  RAII
// restoration prevents a panic or early return from leaking candidates into a
// later solve. (Even a stale
// candidate would be sound — any ground Bool term denotes true or false — but
// scoping keeps the instantiation set intentional and bounded.)
thread_local! {
    static BOOL_GROUND: std::cell::RefCell<Vec<TermId>> = const { std::cell::RefCell::new(Vec::new()) };
}

/// Panic-safe owner of one temporary finite-domain ambient-state replacement.
///
/// The fields are optional so production can scope DERIVED and BOOL_GROUND
/// independently, while certificate replay can atomically replace both with
/// empty state.  This type never escapes the module; callers receive an opaque
/// `impl Drop` and therefore cannot forget restoration on an early return.
struct FiniteDomainAmbientScope {
    previous_derived: Option<HashMap<TermId, BigInt>>,
    previous_bool_ground: Option<Vec<TermId>>,
}

impl Drop for FiniteDomainAmbientScope {
    fn drop(&mut self) {
        if let Some(previous) = self.previous_bool_ground.take() {
            BOOL_GROUND.with(|state| *state.borrow_mut() = previous);
        }
        if let Some(previous) = self.previous_derived.take() {
            DERIVED.with(|state| *state.borrow_mut() = previous);
        }
    }
}

fn replace_finite_domain_ambient(
    derived: Option<HashMap<TermId, BigInt>>,
    bool_ground: Option<Vec<TermId>>,
) -> FiniteDomainAmbientScope {
    let previous_derived = derived.map(|replacement| {
        DERIVED.with(|state| std::mem::replace(&mut *state.borrow_mut(), replacement))
    });
    let previous_bool_ground = bool_ground.map(|replacement| {
        BOOL_GROUND.with(|state| std::mem::replace(&mut *state.borrow_mut(), replacement))
    });
    FiniteDomainAmbientScope {
        previous_derived,
        previous_bool_ground,
    }
}

/// Install derived integer constants for one expansion call and restore the
/// predecessor on normal return or unwind.
pub(crate) fn scoped_derived_consts(m: HashMap<TermId, BigInt>) -> impl Drop {
    replace_finite_domain_ambient(Some(m), None)
}

/// Install the current assertion window's Bool instantiation candidates for
/// one expansion call and restore the predecessor on normal return or unwind.
pub(crate) fn scoped_bool_ground_instantiation_candidates(v: Vec<TermId>) -> impl Drop {
    replace_finite_domain_ambient(None, Some(v))
}

/// Make certificate replay independent of every producer-side ambient hint.
///
/// Exact replay is a source theorem, so it must use only literal bounds and the
/// canonical finite carriers.  Emptying both tables in one RAII scope prevents
/// stale DERIVED facts or producer-selected Bool terms from influencing it.
pub(crate) fn scoped_standalone_finite_domain_replay() -> impl Drop {
    replace_finite_domain_ambient(Some(Default::default()), Some(Vec::new()))
}
/// A term's integer value: a syntactic literal, OR a value the problem's
/// quantifier-free consequences PROVABLY ENTAIL (see
/// `quantifier_loop::entailed_consts`).
fn const_value(terms: &TermStore, t: TermId) -> Option<BigInt> {
    if let Some(c) = terms.extract_integer_constant(t) {
        return Some(c);
    }
    DERIVED.with(|d| d.borrow().get(&t).cloned())
}

/// Bounds contributed by ONE guard atom `(op lhs rhs)` on `var_name`.
fn bounds_from_guard(
    terms: &TermStore,
    op: &str,
    lhs: TermId,
    rhs: TermId,
    var_name: &str,
) -> (Option<i64>, Option<i64>) {
    let mut lo = None;
    let mut hi = None;
    match op {
        "<=" => {
            if is_bound_var(terms, rhs, var_name) {
                // (<= c x) → lower bound c
                lo = const_value(terms, lhs).and_then(|c| i64::try_from(&c).ok());
            } else if is_bound_var(terms, lhs, var_name) {
                // (<= x c) → upper bound c
                hi = const_value(terms, rhs).and_then(|c| i64::try_from(&c).ok());
            }
        }
        "<" => {
            if is_bound_var(terms, rhs, var_name) {
                // (< c x) → lower bound c+1
                lo = const_value(terms, lhs)
                    .and_then(|c| i64::try_from(&c).ok())
                    .and_then(|c| c.checked_add(1));
            } else if is_bound_var(terms, lhs, var_name) {
                // (< x c) → upper bound c-1
                hi = const_value(terms, rhs)
                    .and_then(|c| i64::try_from(&c).ok())
                    .and_then(|c| c.checked_sub(1));
            }
        }
        _ => {}
    }
    (lo, hi)
}

/// NNF-AWARE guard extraction for a `forall` OR-body (#nnf-trap).
///
/// `(=> (and G1 G2) B)` reaches us as `(or ¬G1 ¬G2 B)`, and the negations are
/// PUSHED INTO the comparisons — there is NO `Not` node:
///   `(=> (and (>= i 0) (< i B)) P)`  ==>  `(or (< i 0) (<= B i) P)`
/// So a bare comparison DISJUNCT mentioning the binder IS a negated guard.
/// `D` a disjunct ⇒ the guard is `¬D`:  ¬(a <= b) ≡ (b < a),  ¬(a < b) ≡ (b <= a).
fn bounds_from_forall_disjunct(
    terms: &TermStore,
    disjunct: TermId,
    var_name: &str,
) -> Option<(Option<i64>, Option<i64>)> {
    // Form 1: `(not cmp)` — the guard is `cmp` itself.
    if let TermData::Not(inner) = terms.get(disjunct).clone() {
        if let TermData::App(Symbol::Named(op), args) = terms.get(inner).clone() {
            if (op == "<=" || op == "<") && args.len() == 2 {
                let (l, r) = (args[0], args[1]);
                if is_bound_var(terms, l, var_name) || is_bound_var(terms, r, var_name) {
                    return Some(bounds_from_guard(terms, op.as_str(), l, r, var_name));
                }
            }
        }
        return None;
    }
    // Form 2 (#nnf-trap): a BARE comparison disjunct — the guard is its negation.
    if let TermData::App(Symbol::Named(op), args) = terms.get(disjunct).clone() {
        if (op == "<=" || op == "<") && args.len() == 2 {
            let (l, r) = (args[0], args[1]);
            if is_bound_var(terms, l, var_name) || is_bound_var(terms, r, var_name) {
                // ¬(l <= r) ≡ (r < l);  ¬(l < r) ≡ (r <= l)
                let (nop, nl, nr) = if op == "<=" {
                    ("<", r, l)
                } else {
                    ("<=", r, l)
                };
                return Some(bounds_from_guard(terms, nop, nl, nr, var_name));
            }
        }
    }
    None
}

/// READ-ONLY (`&TermStore`, mints nothing): would `consts` unlock a bounded-Int
/// `forall` expansion that the *literal-only* reading cannot already do?
///
/// The re-expansion pass rewrites terms and therefore PERTURBS the solve, so it
/// must run ONLY when a derived constant is genuinely load-bearing. On
/// `tseitin`/`pp` — where `(seq_len vec)` is NOT entailed to any constant — this
/// returns false and the pass is skipped entirely (zero perturbation).
pub(crate) fn derived_bound_unlocks_expansion(
    terms: &TermStore,
    assertions: &[TermId],
    consts: &HashMap<TermId, BigInt>,
) -> bool {
    fn walk(
        terms: &TermStore,
        t: TermId,
        consts: &HashMap<TermId, BigInt>,
        seen: &mut ay_core::kani_compat::DetHashSet<TermId>,
    ) -> bool {
        if !seen.insert(t) {
            return false;
        }
        if let TermData::Forall(vars, body, _) = terms.get(t).clone() {
            if vars.len() == 1 && vars[0].1 == Sort::Int {
                if let TermData::App(Symbol::Named(op), or_args) = terms.get(body).clone() {
                    if op == "or" {
                        // Range with derived consts vs. with literals only.
                        let with = probe_range(terms, &or_args, &vars[0].0, Some(consts));
                        let without = probe_range(terms, &or_args, &vars[0].0, None);
                        if with.is_some() && without.is_none() {
                            return true;
                        }
                    }
                }
            }
        }
        match terms.get(t).clone() {
            TermData::App(_, args) => args.iter().any(|&a| walk(terms, a, consts, seen)),
            TermData::Not(i) => walk(terms, i, consts, seen),
            TermData::Ite(c, a, b) => {
                walk(terms, c, consts, seen)
                    || walk(terms, a, consts, seen)
                    || walk(terms, b, consts, seen)
            }
            TermData::Forall(_, b, _) | TermData::Exists(_, b, _) => walk(terms, b, consts, seen),
            _ => false,
        }
    }
    let mut seen = ay_core::kani_compat::DetHashSet::default();
    assertions
        .iter()
        .any(|&a| walk(terms, a, consts, &mut seen))
}

/// Range an OR-body's guard disjuncts pin the binder to, reading bounds either
/// with `consts` (derived) or literal-only (`None`). Read-only.
fn probe_range(
    terms: &TermStore,
    or_args: &[TermId],
    var: &str,
    consts: Option<&HashMap<TermId, BigInt>>,
) -> Option<(i64, i64)> {
    let _derived_scope = scoped_derived_consts(consts.cloned().unwrap_or_default());
    let mut lo: Option<i64> = None;
    let mut hi: Option<i64> = None;
    let mut any = false;
    for &arg in or_args {
        if let Some((l, h)) = bounds_from_forall_disjunct(terms, arg, var) {
            any = true;
            if let Some(l) = l {
                lo = Some(lo.map_or(l, |p: i64| p.max(l)));
            }
            if let Some(h) = h {
                hi = Some(hi.map_or(h, |p: i64| p.min(h)));
            }
        }
    }
    match (any, lo, hi) {
        (true, Some(l), Some(h))
            if interval_width(l, h) <= u128::from(MAX_FINITE_DOMAIN_COMBOS) =>
        {
            Some((l, h))
        }
        _ => None,
    }
}

/// Extract integer bounds for a single quantified variable from a guard
/// conjunction. Returns `(lo, hi)` if tight bounds are found.
///
/// Recognizes these patterns (after `>=`/`>` normalization to `<=`/`<`):
/// - `(<= c x)` → lower bound `c`
/// - `(< c x)` → lower bound `c + 1`
/// - `(<= x c)` → upper bound `c`
/// - `(< x c)` → upper bound `c - 1`
fn extract_bounds_from_atoms(
    terms: &TermStore,
    atoms: &[TermId],
    var_name: &str,
) -> Option<(i64, i64)> {
    let mut lo: Option<i64> = None;
    let mut hi: Option<i64> = None;

    for &atom in atoms {
        match terms.get(atom).clone() {
            TermData::App(Symbol::Named(op), ref args) if args.len() == 2 => {
                let lhs = args[0];
                let rhs = args[1];
                match op.as_str() {
                    "<=" => {
                        if is_bound_var(terms, rhs, var_name) {
                            // (<= c x) → x >= c → lower bound c
                            if let Some(c) = terms.extract_integer_constant(lhs) {
                                let c = i64::try_from(&c).ok()?;
                                lo = Some(lo.map_or(c, |prev: i64| prev.max(c)));
                            }
                        } else if is_bound_var(terms, lhs, var_name) {
                            // (<= x c) → upper bound c
                            if let Some(c) = terms.extract_integer_constant(rhs) {
                                let c = i64::try_from(&c).ok()?;
                                hi = Some(hi.map_or(c, |prev: i64| prev.min(c)));
                            }
                        }
                    }
                    "<" => {
                        if is_bound_var(terms, rhs, var_name) {
                            // (< c x) → x > c → lower bound c+1
                            if let Some(c) = terms.extract_integer_constant(lhs) {
                                let c = i64::try_from(&c).ok()?.checked_add(1)?;
                                lo = Some(lo.map_or(c, |prev: i64| prev.max(c)));
                            }
                        } else if is_bound_var(terms, lhs, var_name) {
                            // (< x c) → upper bound c-1
                            if let Some(c) = terms.extract_integer_constant(rhs) {
                                let c = i64::try_from(&c).ok()?.checked_sub(1)?;
                                hi = Some(hi.map_or(c, |prev: i64| prev.min(c)));
                            }
                        }
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }

    // NOTE: an EMPTY interval (l > h) is returned as-is. Callers either fold
    // it to the quantifier's vacuous truth value (single-Int-binder paths —
    // over an empty recognized-guard range a `forall` is trivially true and an
    // `exists` trivially false, an exact equivalence) or reject it explicitly
    // (multi-var combination path).
    match (lo, hi) {
        (Some(l), Some(h)) => Some((l, h)),
        _ => None,
    }
}

/// Width of the inclusive integer interval `[lo, hi]` (0 when empty),
/// computed in i128 so extreme i64 bounds (e.g. verification-consumer's i64::MIN/MAX range
/// guards) cannot overflow the subtraction.
fn interval_width(lo: i64, hi: i64) -> u128 {
    if hi < lo {
        0
    } else {
        (i128::from(hi) - i128::from(lo) + 1) as u128
    }
}

/// Collect the atoms from a conjunction, flattening nested `and` nodes.
fn collect_and_atoms(terms: &TermStore, term: TermId) -> Vec<TermId> {
    match terms.get(term).clone() {
        TermData::App(Symbol::Named(op), args) if op == "and" => args
            .iter()
            .flat_map(|&a| collect_and_atoms(terms, a))
            .collect(),
        _ => vec![term],
    }
}

/// Try to extract bounded integer info from a forall body.
///
/// After De Morgan normalization, `(=> (and G1 G2) body)` becomes:
///   `(or (not G1) (not G2) body)`
/// So we look for negated comparison atoms in the Or that provide bounds
/// on the quantified variable. The remaining disjuncts form the inner body.
fn extract_bounded_int_forall(
    terms: &mut TermStore,
    body: TermId,
    var_name: &str,
    max_combos: u64,
) -> Option<BoundedIntInfo> {
    let (lo, hi, body_parts) = analyze_bounded_int_forall(terms, body, var_name, max_combos)?;
    if hi < lo {
        // Provably-empty recognized-guard range: for every value some guard
        // disjunct `(not g_i)` is true, so the forall is vacuously TRUE. The
        // caller folds on `hi < lo`; `body` is unused there.
        return Some(BoundedIntInfo { lo, hi, body });
    }

    // Reconstruct inner body from remaining parts
    let inner_body = if body_parts.len() == 1 {
        body_parts[0]
    } else {
        terms.mk_or(body_parts)
    };

    Some(BoundedIntInfo {
        lo,
        hi,
        body: inner_body,
    })
}

/// READ-ONLY analysis half of [`extract_bounded_int_forall`] (`&TermStore`,
/// mints nothing): the recognized guard range plus the non-guard disjuncts.
/// `hi < lo` reports a provably-empty recognized-guard range (vacuous truth);
/// `body_parts` is empty ONLY in that case. Shared verbatim by the expansion
/// itself and by the [`bounded_expansion_grounds_all_quantifiers`] probe so
/// the probe can never accept a shape the expansion later refuses.
fn analyze_bounded_int_forall(
    terms: &TermStore,
    body: TermId,
    var_name: &str,
    max_combos: u64,
) -> Option<(i64, i64, Vec<TermId>)> {
    let or_args = match terms.get(body).clone() {
        TermData::App(Symbol::Named(op), args) if op == "or" => args,
        _ => return None,
    };

    if or_args.len() < 2 {
        return None;
    }

    // Split the OR-body into NEGATED-GUARD disjuncts and body parts. A negated
    // guard arrives either as `Not(cmp)` or — after NNF pushes the negation into
    // the comparison — as a BARE `cmp` on the binder (#nnf-trap).
    let mut lo: Option<i64> = None;
    let mut hi: Option<i64> = None;
    let mut any_guard = false;
    let mut body_parts: Vec<TermId> = Vec::new();

    for &arg in &or_args {
        match bounds_from_forall_disjunct(terms, arg, var_name) {
            Some((l, h)) => {
                any_guard = true;
                // #guard-must-bind (FALSE-UNSAT GUARD). A disjunct RECOGNIZED as a
                // negated guard on the binder but whose bound we cannot evaluate
                // contributes NOTHING to lo/hi. Carrying on with the bounds the
                // OTHER guards supply would expand over a SUPERSET of the region
                // the guard actually constrains, and
                //     AND_{i in [lo,hi]} body(i)
                // is then STRICTLY STRONGER than the quantifier — it demands `body`
                // at points the dropped guard exempts. That turns a satisfiable
                // problem UNSAT.
                //
                // e.g. `(=> (and (>= i 0) (< i 5) (< i n)) P)` with `n` a term:
                // lo=0, hi=4 from the literals, `(< i n)` silently dropped, and we
                // would demand P(i) for i >= n.
                //
                // The pre-existing `extract_bounds_from_atoms` has exactly this
                // hole, but it was UNREACHABLE because the `Not(..)`-only matcher
                // never recognized a guard in the first place (#nnf-trap — that
                // branch is dead for any `(=> (and (>= i lo) (< i hi)) body)`).
                // Widening the matcher makes it live, so it is closed HERE, in the
                // same change that opens the path.
                if l.is_none() && h.is_none() {
                    return None;
                }
                if let Some(l) = l {
                    lo = Some(lo.map_or(l, |p: i64| p.max(l)));
                }
                if let Some(h) = h {
                    hi = Some(hi.map_or(h, |p: i64| p.min(h)));
                }
            }
            None => body_parts.push(arg),
        }
    }

    if !any_guard {
        return None;
    }

    // Both ends must be pinned or there is no finite range — fall back to
    // E-matching. Never guess a bound.
    let (lo, hi) = match (lo, hi) {
        (Some(l), Some(h)) => (l, h),
        _ => return None,
    };
    if hi < lo {
        // Provably-empty recognized-guard range (vacuous truth; see wrapper).
        return Some((lo, hi, Vec::new()));
    }
    if interval_width(lo, hi) > u128::from(max_combos) {
        return None;
    }

    if body_parts.is_empty() {
        return None; // No body parts → degenerate case
    }

    Some((lo, hi, body_parts))
}

/// #quantprod-f: extended budget for the MULTI-Int-binder guarded-box
/// `forall` expansion (`analyze_bounded_int_box_forall`). The measured
/// monotonicity family `forall x,y. 0<=x ∧ x<y ∧ y<=N => f(x) <= f(y)` with
/// endpoint pins needs N=60 (60x60 = 3600 grid points) to decide; each grid
/// instance is a short ground clause, so the ground solve cost is trivial.
/// Granted only to triggerless, nested-quantifier-free bodies (the same
/// discipline as [`MAX_BOUND_BOOL_UF_INT_COMBOS`]); every other multi-var
/// shape keeps the historical 256 budget. The expansion is an exact logical
/// equivalence either way (see `analyze_bounded_int_box_forall`), so the
/// budget only chooses HOW MUCH exact grounding is attempted, never a
/// verdict.
const MAX_GUARDED_INT_BOX_COMBOS: u64 = 4096;

/// The operand of a recognized guard comparison: a bound variable of THIS
/// quantifier (by binder index) or an evaluable integer constant.
enum BoxOperand {
    Var(usize),
    Const(i128),
}

/// Classify one side of a guard comparison against the binder list.
/// `None` = neither a binder variable nor an evaluable integer constant.
fn box_operand(terms: &TermStore, t: TermId, vars: &[(String, Sort)]) -> Option<BoxOperand> {
    if let TermData::Var(name, _) = terms.get(t) {
        if let Some(idx) = vars.iter().position(|(n, _)| n == name) {
            return Some(BoxOperand::Var(idx));
        }
        return None;
    }
    let c = const_value(terms, t)?;
    let c = i64::try_from(&c).ok()?;
    Some(BoxOperand::Const(i128::from(c)))
}

/// Does `t`'s DAG contain a disequality — a `distinct` application or a
/// negated `=` (the form `distinct` normalizes to)? (Engine-routing screen
/// for the guarded-box expansion; see its caller.)
fn term_contains_disequality(terms: &TermStore, t: TermId) -> bool {
    fn walk(
        terms: &TermStore,
        t: TermId,
        seen: &mut ay_core::kani_compat::DetHashSet<TermId>,
    ) -> bool {
        if !seen.insert(t) {
            return false;
        }
        match terms.get(t) {
            TermData::App(Symbol::Named(name), args) => {
                name == "distinct" || args.iter().any(|&a| walk(terms, a, seen))
            }
            TermData::App(_, args) => args.iter().any(|&a| walk(terms, a, seen)),
            TermData::Not(inner) => {
                matches!(terms.get(*inner), TermData::App(Symbol::Named(n), _) if n == "=")
                    || walk(terms, *inner, seen)
            }
            TermData::Ite(c, a, b) => {
                walk(terms, *c, seen) || walk(terms, *a, seen) || walk(terms, *b, seen)
            }
            TermData::Let(bindings, body) => {
                bindings.iter().any(|(_, v)| walk(terms, *v, seen)) || walk(terms, *body, seen)
            }
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => walk(terms, *body, seen),
            _ => false,
        }
    }
    let mut seen = ay_core::kani_compat::DetHashSet::default();
    walk(terms, t, &mut seen)
}

/// READ-ONLY box analysis for a MULTI-Int-binder guarded `forall`
/// (#quantprod-f). Returns the per-binder inclusive ranges `[lo_i, hi_i]`
/// (binder order) that the recognized guard disjuncts ENTAIL, or `None` when
/// no complete finite box within `max_combos` can be derived.
///
/// The body must be the NNF `or` of an implication: disjuncts that are
/// (possibly `Not`-wrapped) `<`/`<=` comparisons whose operands are each a
/// binder variable or an integer constant are NEGATED GUARDS; everything else
/// is body. Guard atoms yield difference constraints `a <= b - δ`
/// (δ=1 for `<`), closed transitively over binder-binder chains
/// (`0<=x ∧ x<y ∧ y<=N ⊢ x<=N-1 ∧ 1<=y` — the closure the flat per-var
/// extractor cannot see).
///
/// # Soundness (exact equivalence of the caller's expansion)
///
/// The caller instantiates the FULL or-body (guards included) at every box
/// point, so no disjunct is ever dropped (`#guard-must-bind` cannot arise):
/// * `forall ⟹ AND-over-box` is universal instantiation.
/// * `AND-over-box ⟹ forall`: every derived bound is a logical consequence
///   of the conjunction of the recognized guard atoms, so any point OUTSIDE
///   the box falsifies some guard atom `g_i`, making its disjunct `¬g_i` —
///   hence the whole body — true there.
/// * An EMPTY derived range certifies the guard atoms jointly unsatisfiable,
///   so the forall is vacuously true (caller folds to `true`).
///
/// Nested quantifiers are refused up front: binder matching is name-based
/// and an inner binder could shadow an outer name.
fn analyze_bounded_int_box_forall(
    terms: &TermStore,
    body: TermId,
    vars: &[(String, Sort)],
    max_combos: u64,
) -> Option<Vec<(i64, i64)>> {
    if vars.len() < 2 || !vars.iter().all(|(_, s)| *s == Sort::Int) {
        return None;
    }
    // Distinct binder names (a duplicate would make index matching ambiguous).
    for i in 0..vars.len() {
        for j in (i + 1)..vars.len() {
            if vars[i].0 == vars[j].0 {
                return None;
            }
        }
    }
    if contains_quantifier(terms, body) {
        return None; // Shadowing hazard for name-based binder matching.
    }
    // ENGINE ROUTING, not soundness: a disequality-bearing body (`distinct`
    // or its normalized `(not (= …))` form) expands into a ground pairwise-
    // disequality grid — the pigeonhole class, which the ground UF+LIA lane
    // cannot refute in reasonable time (measured: D13's 8-into-7 injection
    // as a ground grid burns >60s without an answer). Expanding buys nothing
    // over the pre-existing quantifier lane there, so keep the status quo
    // byte-identical for that class; order-comparison bodies (the
    // monotonicity family this path exists for) expand into chain
    // constraints the ground lane decides instantly.
    if term_contains_disequality(terms, body) {
        return None;
    }
    let or_args = match terms.get(body).clone() {
        TermData::App(Symbol::Named(op), args) if op == "or" => args,
        _ => return None,
    };
    if or_args.len() < 2 {
        return None;
    }

    // A recognized POSITIVE guard atom `a (< | <=) b` from one disjunct.
    // Form 1 `(not cmp)`: the guard is `cmp` itself. Form 2 bare `cmp`
    // (#nnf-trap): the guard is its negation `¬(a<=b) ≡ (b<a)`,
    // `¬(a<b) ≡ (b<=a)`.
    let guard_of = |disjunct: TermId| -> Option<(BoxOperand, BoxOperand, i128)> {
        let (op, l, r, negated) = match terms.get(disjunct).clone() {
            TermData::Not(inner) => match terms.get(inner).clone() {
                TermData::App(Symbol::Named(op), args)
                    if (op == "<" || op == "<=") && args.len() == 2 =>
                {
                    (op, args[0], args[1], false)
                }
                _ => return None,
            },
            TermData::App(Symbol::Named(op), args)
                if (op == "<" || op == "<=") && args.len() == 2 =>
            {
                (op, args[0], args[1], true)
            }
            _ => return None,
        };
        let a = box_operand(terms, l, vars)?;
        let b = box_operand(terms, r, vars)?;
        // Ground comparisons carry no binder information.
        if matches!((&a, &b), (BoxOperand::Const(_), BoxOperand::Const(_))) {
            return None;
        }
        // Positive guard `x (op) y`; negation flips operands and strictness.
        Some(if negated {
            // ¬(l <= r) ≡ r < l ; ¬(l < r) ≡ r <= l
            let delta = if op == "<=" { 1 } else { 0 };
            (b, a, delta)
        } else {
            let delta = if op == "<" { 1 } else { 0 };
            (a, b, delta)
        })
    };

    let mut lo: Vec<Option<i128>> = vec![None; vars.len()];
    let mut hi: Vec<Option<i128>> = vec![None; vars.len()];
    let mut edges: Vec<(usize, usize, i128)> = Vec::new(); // var_i <= var_j - δ
    let mut any_guard = false;
    let mut body_parts = 0usize;
    for &arg in &or_args {
        // Guard atom `a <= b - δ`.
        let Some((a, b, delta)) = guard_of(arg) else {
            // Body part: kept verbatim by the caller's instantiation.
            body_parts += 1;
            continue;
        };
        any_guard = true;
        match (a, b) {
            (BoxOperand::Const(c), BoxOperand::Var(j)) => {
                let l = c.checked_add(delta)?;
                lo[j] = Some(lo[j].map_or(l, |p| p.max(l)));
            }
            (BoxOperand::Var(i), BoxOperand::Const(c)) => {
                let h = c.checked_sub(delta)?;
                hi[i] = Some(hi[i].map_or(h, |p| p.min(h)));
            }
            (BoxOperand::Var(i), BoxOperand::Var(j)) => edges.push((i, j, delta)),
            (BoxOperand::Const(_), BoxOperand::Const(_)) => unreachable!(),
        }
    }
    if !any_guard {
        return None;
    }
    // ENGINE ROUTING, not soundness: only the SINGLE-obligation implication
    // shape expands — guards plus exactly ONE non-guard disjunct (the
    // monotonicity family's `f(x) <op> f(y)` atom). Multiple body disjuncts
    // are the disjunctive-branching class: `distinct` normalizes to an OR of
    // strict comparisons, so an injectivity grid (D02/D13 pigeonhole family)
    // presents as guards + 2 body disjuncts here, and its expansion turns a
    // problem the quantifier lane decides in seconds into a ground
    // branch-blowup the combined solver grinds on (measured: D02 sat 2.8s
    // via the quantifier lane, >90s ground-expanded). Refusing keeps the
    // status quo byte-identical for that whole class.
    if body_parts != 1 {
        return None;
    }

    // Transitive closure over binder-binder chains: `x <= y - δ` propagates a
    // lower bound forward and an upper bound backward. `vars.len()` rounds
    // reach any acyclic chain's fixpoint; a (contradictory) cyclic chain just
    // stops tightening — every derived bound is still an entailed consequence.
    for _ in 0..vars.len() {
        for &(i, j, delta) in &edges {
            if let Some(li) = lo[i] {
                let l = li.checked_add(delta)?;
                if lo[j].is_none_or(|p| l > p) {
                    lo[j] = Some(l);
                }
            }
            if let Some(hj) = hi[j] {
                let h = hj.checked_sub(delta)?;
                if hi[i].is_none_or(|p| h < p) {
                    hi[i] = Some(h);
                }
            }
        }
    }

    // Every binder needs both ends pinned; convert and cap the box volume.
    let mut ranges: Vec<(i64, i64)> = Vec::with_capacity(vars.len());
    let mut total: u128 = 1;
    for idx in 0..vars.len() {
        let (l, h) = (lo[idx]?, hi[idx]?);
        let l = i64::try_from(l).ok()?;
        let h = i64::try_from(h).ok()?;
        if h < l {
            // Provably-empty range: guards jointly unsatisfiable — vacuous
            // truth. Report as-is; the caller folds to `true`.
            return Some(vec![(1, 0); vars.len()]);
        }
        total = total.saturating_mul(interval_width(l, h));
        if total > u128::from(max_combos) {
            return None;
        }
        ranges.push((l, h));
    }
    Some(ranges)
}

/// Bounded-BV forall info: the binder's inclusive unsigned range and the
/// guard-stripped inner body (mirrors [`BoundedIntInfo`], values in `i128` so
/// `c - 1` underflow at 0 and `c + 1` at `2^w - 1` fold naturally into an
/// empty / unchanged range for widths up to 64).
struct BoundedBvInfo {
    lo: i128,
    hi: i128,
    body: TermId,
}

/// Unsigned-BV constant value of `t` as `i128` (widths <= 64 only).
fn bv_const_value(terms: &TermStore, t: TermId) -> Option<i128> {
    if let TermData::Const(Constant::BitVec { value, width }) = terms.get(t) {
        if *width <= 64 {
            return value.to_i128();
        }
    }
    None
}

/// Bounds contributed by ONE POSITIVE unsigned-BV guard `(op lhs rhs)` on the
/// binder (the guard must be TRUE for the body to be required). Exactly one
/// side must be the binder and the other a BV literal; anything else yields
/// `(None, None)` and the caller REJECTS the expansion (#guard-must-bind —
/// dropping an unevaluable guard would demand the body at exempted points, a
/// false-UNSAT).
fn bounds_from_bv_guard(
    terms: &TermStore,
    op: &str,
    lhs: TermId,
    rhs: TermId,
    var_name: &str,
) -> (Option<i128>, Option<i128>) {
    let mut lo = None;
    let mut hi = None;
    match op {
        // lhs <u rhs
        "bvult" => {
            if is_bound_var(terms, lhs, var_name) {
                hi = bv_const_value(terms, rhs).map(|c| c - 1);
            } else if is_bound_var(terms, rhs, var_name) {
                lo = bv_const_value(terms, lhs).map(|c| c + 1);
            }
        }
        // lhs <=u rhs
        "bvule" => {
            if is_bound_var(terms, lhs, var_name) {
                hi = bv_const_value(terms, rhs);
            } else if is_bound_var(terms, rhs, var_name) {
                lo = bv_const_value(terms, lhs);
            }
        }
        // lhs >u rhs
        "bvugt" => {
            if is_bound_var(terms, lhs, var_name) {
                lo = bv_const_value(terms, rhs).map(|c| c + 1);
            } else if is_bound_var(terms, rhs, var_name) {
                hi = bv_const_value(terms, lhs).map(|c| c - 1);
            }
        }
        // lhs >=u rhs
        "bvuge" => {
            if is_bound_var(terms, lhs, var_name) {
                lo = bv_const_value(terms, rhs);
            } else if is_bound_var(terms, rhs, var_name) {
                hi = bv_const_value(terms, lhs);
            }
        }
        _ => {}
    }
    (lo, hi)
}

/// NNF-aware negated-guard extraction for a BV `forall` OR-disjunct (the BV
/// analogue of [`bounds_from_forall_disjunct`], #nnf-trap): a disjunct `D`
/// contributes the guard `¬D`.
///
/// * `(not cmp)` — the guard is `cmp` itself.
/// * a BARE unsigned comparison on the binder — the guard is its negation:
///   `¬(bvult a b) ≡ (bvuge a b)`, `¬(bvule a b) ≡ (bvugt a b)`, and dually.
///
/// Returns `Some((lo, hi))` when the disjunct IS a recognized comparison on
/// the binder (a `(None, None)` payload then means the bound is unevaluable —
/// the caller must reject, never expand over a superset), `None` when the
/// disjunct is not a guard at all (body part).
fn bounds_from_bv_forall_disjunct(
    terms: &TermStore,
    disjunct: TermId,
    var_name: &str,
) -> Option<(Option<i128>, Option<i128>)> {
    const BV_CMP: [&str; 4] = ["bvult", "bvule", "bvugt", "bvuge"];
    // Form 1: `(not cmp)` — the guard is `cmp` itself.
    if let TermData::Not(inner) = terms.get(disjunct).clone() {
        if let TermData::App(Symbol::Named(op), args) = terms.get(inner).clone() {
            if BV_CMP.contains(&op.as_str()) && args.len() == 2 {
                let (l, r) = (args[0], args[1]);
                if is_bound_var(terms, l, var_name) || is_bound_var(terms, r, var_name) {
                    return Some(bounds_from_bv_guard(terms, op.as_str(), l, r, var_name));
                }
            }
        }
        return None;
    }
    // Form 2 (#nnf-trap): a BARE comparison disjunct — the guard is its
    // negation: ¬(a <u b) ≡ (a >=u b), ¬(a <=u b) ≡ (a >u b), and dually.
    if let TermData::App(Symbol::Named(op), args) = terms.get(disjunct).clone() {
        if BV_CMP.contains(&op.as_str()) && args.len() == 2 {
            let (l, r) = (args[0], args[1]);
            if is_bound_var(terms, l, var_name) || is_bound_var(terms, r, var_name) {
                let nop = match op.as_str() {
                    "bvult" => "bvuge",
                    "bvule" => "bvugt",
                    "bvugt" => "bvule",
                    _ => "bvult", // bvuge
                };
                return Some(bounds_from_bv_guard(terms, nop, l, r, var_name));
            }
        }
    }
    None
}

/// Try to extract a guard-bounded range for a single-BV-binder `forall`
/// (#seq-from-fn bounded discharge). The BV analogue of
/// [`extract_bounded_int_forall`]: the body is `(or D1 … Dn)` (the NNF of
/// `(=> guard body)`), some `Di` are negated unsigned-comparison guards on the
/// binder pinning it to a LITERAL range, and the rest form the inner body.
/// Unlike Int, the BV domain supplies missing ends itself: `lo` defaults to
/// `0` and `hi` to `2^w - 1`, so a single `(bvult i c)` guard is already a
/// complete range — but at least one guard must contribute a bound within the
/// combo budget or we fall back to E-matching.
///
/// SOUNDNESS: `forall i:(_ BitVec w). (or ¬G(i) B(i))` with `G` pinning `i`
/// to `[lo, hi]` is EQUIVALENT to `AND_{v in [lo, hi]} B(v)` — outside the
/// range some guard disjunct is true, inside it the body disjuncts must hold —
/// so the expansion is an exact equivalence (never an under/over-
/// approximation) and cannot flip a verdict in either direction.
fn extract_bounded_bv_forall(
    terms: &mut TermStore,
    body: TermId,
    var_name: &str,
    width: u32,
    max_combos: u64,
) -> Option<BoundedBvInfo> {
    if width > 64 {
        return None;
    }
    // Internal producers may keep the raw `(=> guard body)` form: treat it as
    // its NNF `(or ¬g1 … ¬gk body)` by rewriting each guard conjunct into the
    // `Not(cmp)` disjunct shape the loop below already understands.
    let or_args = match terms.get(body).clone() {
        TermData::App(Symbol::Named(op), args) if op == "or" => args,
        TermData::App(Symbol::Named(op), args) if op == "=>" && args.len() == 2 => {
            let mut disjuncts: Vec<TermId> = collect_and_atoms(terms, args[0])
                .into_iter()
                .map(|g| terms.mk_not(g))
                .collect();
            disjuncts.push(args[1]);
            disjuncts
        }
        _ => return None,
    };
    if or_args.len() < 2 {
        return None;
    }

    let domain_max: i128 = if width == 64 {
        i128::from(u64::MAX)
    } else {
        (1i128 << width) - 1
    };
    let mut lo: Option<i128> = None;
    let mut hi: Option<i128> = None;
    let mut any_bound = false;
    let mut body_parts: Vec<TermId> = Vec::new();

    for &arg in &or_args {
        match bounds_from_bv_forall_disjunct(terms, arg, var_name) {
            Some((l, h)) => {
                // #guard-must-bind: a recognized guard whose literal we cannot
                // evaluate exempts points we cannot enumerate — expanding over
                // the remaining bounds would be STRICTLY STRONGER than the
                // quantifier (false-UNSAT). Reject the whole expansion.
                if l.is_none() && h.is_none() {
                    return None;
                }
                any_bound = true;
                if let Some(l) = l {
                    lo = Some(lo.map_or(l, |p: i128| p.max(l)));
                }
                if let Some(h) = h {
                    hi = Some(hi.map_or(h, |p: i128| p.min(h)));
                }
            }
            None => body_parts.push(arg),
        }
    }

    if !any_bound {
        return None;
    }
    // The BV domain itself supplies the missing ends (unsigned).
    let lo = lo.unwrap_or(0).max(0);
    let hi = hi.unwrap_or(domain_max).min(domain_max);
    if hi < lo {
        // Provably-empty guard range: vacuously TRUE (caller folds on hi < lo).
        return Some(BoundedBvInfo { lo, hi, body });
    }
    if (hi - lo + 1) as u128 > u128::from(max_combos) {
        return None;
    }

    let inner_body = if body_parts.len() == 1 {
        body_parts[0]
    } else if body_parts.len() > 1 {
        terms.mk_or(body_parts)
    } else {
        return None; // Degenerate: guard-only body.
    };

    Some(BoundedBvInfo {
        lo,
        hi,
        body: inner_body,
    })
}

/// Try to extract bounded integer info from an exists body.
///
/// Matches: `(and bound_atoms... body_parts...)` where some atoms
/// are bounds for the quantified variable.
fn extract_bounded_int_exists(
    terms: &TermStore,
    body: TermId,
    var_name: &str,
    max_combos: u64,
) -> Option<BoundedIntInfo> {
    let atoms = collect_and_atoms(terms, body);
    if let Some((lo, hi)) = extract_bounds_from_atoms(terms, &atoms, var_name) {
        if hi < lo {
            // Provably-empty range: the bound conjuncts are jointly
            // unsatisfiable, so the exists is vacuously FALSE. The caller
            // folds on `hi < lo`.
            return Some(BoundedIntInfo { lo, hi, body });
        }
        if interval_width(lo, hi) > u128::from(max_combos) {
            return None;
        }
        // For exists, keep the full body (each disjunct must be independently satisfiable)
        return Some(BoundedIntInfo { lo, hi, body });
    }
    None
}

/// READ-ONLY probe (#quantprod-a, expansion-over-mod-adoption): will the
/// bounded-Int finite-domain expansion GROUND every quantifier in `t`?
///
/// The deep-QE prepass runs BEFORE the quantifier loop's finite-domain
/// expansion, and Cooper's elimination of a guard-bounded `forall` over a
/// constant-coefficient linear bound adopts a rewrite full of constant-
/// divisor divisibility atoms (`(not (= 0 (mod …)))`) that the ground LIA
/// lane cannot decide (`UnsupportedArithmetic`) — pre-empting the exact
/// bounded expansion that DOES decide the same assertion with a
/// gate-validated model. `deep_qe` consults this probe ONLY when an adopted
/// rewrite minted such divisibility atoms, and then keeps the original
/// assertion for the expansion instead (every clean adoption — including the
/// pure-arithmetic nested-solve obligations Cooper decides instantly —
/// proceeds byte-identically; an unconditional skip was measured to regress
/// those nested legs).
///
/// Fail-closed both ways: `false` keeps the deep-QE status quo; `true` only
/// defers to the expansion, which is an exact equivalence whose ground
/// verdict is model-gated / proof-backed as usual — the probe chooses an
/// ENGINE, never a verdict. To guarantee "accepted ⟹ fully grounded", each
/// leg calls the SAME analysis the expansion itself uses, and nested
/// quantifiers are refused outright (the recursive-expansion path could
/// leave an inner non-expandable quantifier behind).
pub(crate) fn bounded_expansion_grounds_all_quantifiers(terms: &TermStore, t: TermId) -> bool {
    fn walk(terms: &TermStore, t: TermId, found: &mut bool) -> bool {
        match terms.get(t).clone() {
            TermData::Forall(vars, body, triggers) => {
                *found = true;
                if contains_quantifier(terms, body) {
                    return false;
                }
                let triggerless = triggers.is_empty();
                if vars.len() == 1 && vars[0].1 == Sort::Int {
                    // Mirror of `finite_domain_expand`'s single-Int budget.
                    let max_combos = if triggerless
                        && !terms.is_no_mbqi(t)
                        && has_bound_dependent_bool_uf(terms, body, &vars)
                    {
                        MAX_BOUND_BOOL_UF_INT_COMBOS
                    } else {
                        MAX_FINITE_DOMAIN_COMBOS
                    };
                    analyze_bounded_int_forall(terms, body, &vars[0].0, max_combos).is_some()
                } else if vars.len() >= 2 && vars.iter().all(|(_, s)| *s == Sort::Int) {
                    // Mirror of the #quantprod-f box path.
                    let max_combos = if triggerless && !terms.is_no_mbqi(t) {
                        MAX_GUARDED_INT_BOX_COMBOS
                    } else {
                        MAX_FINITE_DOMAIN_COMBOS
                    };
                    analyze_bounded_int_box_forall(terms, body, &vars, max_combos).is_some()
                } else {
                    false
                }
            }
            TermData::Exists(vars, body, triggers) => {
                *found = true;
                if contains_quantifier(terms, body) {
                    return false;
                }
                if vars.len() == 1 && vars[0].1 == Sort::Int {
                    let max_combos = if triggers.is_empty()
                        && !terms.is_no_mbqi(t)
                        && has_bound_dependent_bool_uf(terms, body, &vars)
                    {
                        MAX_BOUND_BOOL_UF_INT_COMBOS
                    } else {
                        MAX_FINITE_DOMAIN_COMBOS
                    };
                    extract_bounded_int_exists(terms, body, &vars[0].0, max_combos).is_some()
                } else {
                    false
                }
            }
            TermData::App(_, args) => args.iter().all(|&a| walk(terms, a, found)),
            TermData::Not(inner) => walk(terms, inner, found),
            TermData::Ite(c, a, b) => {
                walk(terms, c, found) && walk(terms, a, found) && walk(terms, b, found)
            }
            // A quantifier hidden under an unrecognized node (Let bindings,
            // future variants) must refuse the skip — `contains_quantifier`
            // over-approximates in exactly the safe direction here.
            _ => !contains_quantifier(terms, t),
        }
    }
    let mut found = false;
    walk(terms, t, &mut found) && found
}

/// Expand a quantifier with finite-domain variables into a conjunction (forall)
/// or disjunction (exists) of ground instances (#5848).
///
/// For `(forall ((b Bool)) (P b))` → `(and (P true) (P false))`
/// For `(exists ((b Bool)) (P b))` → `(or (P true) (P false))`
///
/// Also handles bounded integer quantifiers (#5848):
/// - `(forall ((i Int)) (=> (and (<= 0 i) (< i 5)) (P i)))` → `(and (P 0) ... (P 4))`
/// - `(exists ((i Int)) (and (<= 0 i) (<= i 2) (P i)))` → `(or (and ...) ...)`
///
/// Finite sorts: `Sort::Bool` (2 values), `Sort::BitVec(w<=8)` (up to 256).
/// Bounded integers: range ≤ 256, single Int variable with guard pattern.
///
/// Returns `None` if the term is not a quantifier, has non-finite variables,
/// or the total combination count exceeds `MAX_FINITE_DOMAIN_COMBOS`.
pub(crate) fn finite_domain_expand(terms: &mut TermStore, term: TermId) -> Option<TermId> {
    finite_domain_expand_impl(terms, term, &mut None)
}

/// One recorded finite-domain instantiation: the binder values (in binder
/// order) and the constructor-folded instantiated body they contributed to
/// the expansion (#quant-expansion-proof).
pub(crate) type FiniteDomainInstance = (Vec<TermId>, TermId);

/// [`finite_domain_expand`] with per-instance provenance: alongside the
/// expansion it returns, for every enumerated binder-value combination, the
/// substitution tuple (in binder order) and the instance term it produced.
/// The proof exporter uses these records to re-derive each surviving
/// conjunct of the expansion from the ORIGINAL `forall` premise via Alethe
/// `forall_inst` steps instead of assuming the merged ground conjunction
/// (which no external checker can match to a problem premise).
///
/// Byte-identical to [`finite_domain_expand`] in the returned expansion term
/// (both delegate to the same implementation; the recorder only observes).
pub(crate) fn finite_domain_expand_with_instances(
    terms: &mut TermStore,
    term: TermId,
) -> Option<(TermId, Vec<FiniteDomainInstance>)> {
    let mut recorder = Some(Vec::new());
    let expanded = finite_domain_expand_impl(terms, term, &mut recorder)?;
    Some((expanded, recorder.unwrap_or_default()))
}

fn finite_domain_expand_impl(
    terms: &mut TermStore,
    term: TermId,
    recorder: &mut Option<Vec<FiniteDomainInstance>>,
) -> Option<TermId> {
    let (vars, body, is_forall, triggerless) = match terms.get(term).clone() {
        TermData::Forall(v, b, triggers) => (v, b, true, triggers.is_empty()),
        TermData::Exists(v, b, triggers) => (v, b, false, triggers.is_empty()),
        _ => return None,
    };

    // Special case: single Int variable with bounded guard pattern (#5848)
    if vars.len() == 1 && vars[0].1 == Sort::Int {
        // Rank-9 step 1: grant the extended budget ONLY to the class that
        // otherwise fails closed to `Unknown(QuantifierUnhandled)` — a
        // triggerless, non-`no_mbqi`, nested-quantifier-free body applying a
        // Bool UF to the binder (see `MAX_BOUND_BOOL_UF_INT_COMBOS`). Every
        // other shape keeps the historical 256 budget, byte-identically.
        let max_combos = if triggerless
            && !terms.is_no_mbqi(term)
            && !contains_quantifier(terms, body)
            && has_bound_dependent_bool_uf(terms, body, &vars)
        {
            MAX_BOUND_BOOL_UF_INT_COMBOS
        } else {
            MAX_FINITE_DOMAIN_COMBOS
        };
        let (ref var_name, _) = vars[0];
        let bounded_info = if is_forall {
            extract_bounded_int_forall(terms, body, var_name, max_combos)
        } else {
            extract_bounded_int_exists(terms, body, var_name, max_combos)
        };
        if let Some(info) = bounded_info {
            if info.hi < info.lo {
                // Provably-empty recognized range: the quantifier is vacuously
                // true (forall — some negated guard disjunct holds everywhere)
                // or vacuously false (exists — the guard conjuncts are jointly
                // unsatisfiable). Exact equivalence, sound in any polarity.
                return Some(terms.mk_bool(is_forall));
            }
            let range = interval_width(info.lo, info.hi) as usize;
            let mut instances: Vec<TermId> = Vec::with_capacity(range);
            for v in info.lo..=info.hi {
                let value = terms.mk_int(BigInt::from(v));
                let mut subst: HashMap<String, TermId> = Default::default();
                subst.insert(var_name.clone(), value);
                let instance = subst_vars(terms, info.body, &subst);
                // Recursively expand any finite-domain quantifier left in the
                // instantiated body (#quant-alternation): an outer quantifier
                // whose body contains an INNER finite-domain quantifier must be
                // fully expanded, or the inner quantifier survives in a
                // disjunctive position and is later (unsoundly) treated as a
                // conjunctive obligation.
                let expanded = expand_finite_domain_subterms(terms, instance);
                if let Some(rec) = recorder.as_mut() {
                    rec.push((vec![value], expanded));
                }
                instances.push(expanded);
            }
            return if is_forall {
                Some(terms.mk_and(instances))
            } else {
                Some(terms.mk_or(instances))
            };
        }
        return None; // Int without bounds → fall back to E-matching
    }

    // #quantprod-f: MULTI-Int-binder guarded-box forall. The generic
    // multi-var path below only reads bounds from a CONJUNCTIVE body, so the
    // NNF or-body of `forall x⃗. (=> guard body)` never expanded — and the
    // per-var flat extractor cannot see bounds that only hold TRANSITIVELY
    // through binder-binder guards (`0<=x ∧ x<y ∧ y<=N`). The box analysis
    // derives the entailed per-binder ranges (with closure over the chains)
    // and the FULL or-body is instantiated at every box point — an exact
    // equivalence (see `analyze_bounded_int_box_forall` for the two-direction
    // argument, including the `#guard-must-bind` non-hazard: nothing is ever
    // stripped). Vacuously-true on a provably-empty derived range. Refusal
    // falls through to the pre-existing generic path unchanged.
    if is_forall && vars.len() >= 2 && vars.iter().all(|(_, s)| *s == Sort::Int) {
        let max_combos =
            if triggerless && !terms.is_no_mbqi(term) && !contains_quantifier(terms, body) {
                MAX_GUARDED_INT_BOX_COMBOS
            } else {
                MAX_FINITE_DOMAIN_COMBOS
            };
        if let Some(ranges) = analyze_bounded_int_box_forall(terms, body, &vars, max_combos) {
            if ranges.iter().any(|(l, h)| h < l) {
                // Provably-empty guard box: vacuously true (exact).
                return Some(terms.mk_bool(true));
            }
            let total: u128 = ranges.iter().map(|&(l, h)| interval_width(l, h)).product();
            let total = total as usize; // <= max_combos <= 4096
            let mut instances: Vec<TermId> = Vec::with_capacity(total);
            for mut combo_idx in 0..total {
                let mut subst: HashMap<String, TermId> = Default::default();
                let mut values: Vec<TermId> = Vec::with_capacity(ranges.len());
                for (var_idx, &(l, h)) in ranges.iter().enumerate() {
                    let size = interval_width(l, h) as usize;
                    let v = l + (combo_idx % size) as i64;
                    combo_idx /= size;
                    let value = terms.mk_int(BigInt::from(v));
                    values.push(value);
                    subst.insert(vars[var_idx].0.clone(), value);
                }
                // FULL body: guard disjuncts fold to concrete truth values at
                // ground preprocessing; nothing is dropped. The body was
                // verified nested-quantifier-free by the analysis, so no
                // recursive expansion is needed.
                let instance = subst_vars(terms, body, &subst);
                if let Some(rec) = recorder.as_mut() {
                    rec.push((values, instance));
                }
                instances.push(instance);
            }
            return Some(terms.mk_and(instances));
        }
        // Fall through: the generic conjunctive-body multi-var path below.
    }

    // Single BV binder pinned to a small range by unsigned-comparison guards
    // (#seq-from-fn bounded discharge): `forall i:(_ BitVec w). (=> (bvult i
    // c) B(i))` with literal `c` is EQUIVALENT to `AND_{v<c} B(v)`, so the
    // quantifier is discharged exactly — the deductive-checks `seq_from_fn` guarded
    // pointwise array axioms (len <= 256) become quantifier-free and the
    // ground solve decides them with a validated model. Forall-only: the
    // exists dual falls through to Skolemization as before. Widths <= 8 with
    // no recognized guard still take the full-domain path below.
    if vars.len() == 1 && is_forall {
        if let Sort::BitVec(bv) = &vars[0].1 {
            let (ref var_name, _) = vars[0];
            if let Some(info) =
                extract_bounded_bv_forall(terms, body, var_name, bv.width, MAX_FINITE_DOMAIN_COMBOS)
            {
                if info.hi < info.lo {
                    // Provably-empty guard range: vacuously true.
                    return Some(terms.mk_bool(true));
                }
                let width = bv.width;
                let mut instances: Vec<TermId> =
                    Vec::with_capacity((info.hi - info.lo + 1) as usize);
                for v in info.lo..=info.hi {
                    let value = terms.mk_bitvec(BigInt::from(v), width);
                    let mut subst: HashMap<String, TermId> = Default::default();
                    subst.insert(var_name.clone(), value);
                    let instance = subst_vars(terms, info.body, &subst);
                    // Recursively expand nested finite-domain quantifiers
                    // (#quant-alternation, same as the Int path).
                    let expanded = expand_finite_domain_subterms(terms, instance);
                    if let Some(rec) = recorder.as_mut() {
                        rec.push((vec![value], expanded));
                    }
                    instances.push(expanded);
                }
                return Some(terms.mk_and(instances));
            }
        }
    }

    // A conjunctively bounded-looking `forall` does NOT make Int a finite
    // carrier. Enumerating only the points satisfying those conjuncts drops
    // every outside-domain obligation and is not equivalent:
    //
    //   forall x,y:Int. 0<=x /\ x<=0 /\ 0<=y /\ y<=0
    //
    // is false, while the old generic box enumerated only `(0,0)` and folded
    // the replacement to true. Exact guarded universal expansion is handled by
    // the dedicated single-Int OR/implication path and the proved multi-Int
    // guarded-box path above; if either refuses, fail closed to ordinary
    // quantifier reasoning. This also excludes mixed Bool/BV+Int products.
    if is_forall && vars.iter().any(|(_, sort)| *sort == Sort::Int) {
        return None;
    }

    // Check all vars have finite sorts and compute total combinations. An Int var
    // reaches this generic path only for `exists`, where a conjunctive guard is
    // false outside the extracted interval and enumeration is exact. For
    // `forall`, every Int-bearing case returned through a proved guarded route
    // above or was rejected by the fail-closed check immediately above.
    let atoms = collect_and_atoms(terms, body);
    let mut domain_sizes: Vec<(String, Sort, i64, u64)> = Vec::with_capacity(vars.len());
    let mut total_combos: u64 = 1;
    for (name, sort) in &vars {
        let (lo, size) = match sort {
            Sort::Bool => (0i64, 2u64),
            Sort::BitVec(bv) if bv.width <= 8 => (0i64, 1u64 << bv.width),
            Sort::Int => {
                let (lo, hi) = extract_bounds_from_atoms(terms, &atoms, name)?;
                if hi < lo {
                    return None;
                }
                let width = interval_width(lo, hi);
                if width > u128::from(MAX_FINITE_DOMAIN_COMBOS) {
                    return None; // i128-safe width check (extreme i64 bounds)
                }
                (lo, width as u64)
            }
            _ => return None, // Non-finite sort (or unbounded Int → E-matching)
        };
        total_combos = total_combos.saturating_mul(size);
        if total_combos > MAX_FINITE_DOMAIN_COMBOS {
            return None; // Too many combinations
        }
        domain_sizes.push((name.clone(), sort.clone(), lo, size));
    }

    if total_combos == 0 {
        return None;
    }

    // #bool-ground-inst: build per-var value lists. Bool binders get the
    // two-point base domain PLUS the scoped ground Bool candidates (see the
    // BOOL_GROUND soundness note above: the augmented expansion is EQUIVALENT
    // to the two-point one, so this is sound at any polarity). The augmented
    // cross product must still respect MAX_FINITE_DOMAIN_COMBOS; if it does
    // not, the extras are dropped wholesale and the expansion proceeds with
    // the base domains exactly as before (never refuse an expansion the base
    // budget admits because of optional extras).
    let bool_extras: Vec<TermId> = BOOL_GROUND.with(|b| b.borrow().clone());
    let bool_extras: Vec<TermId> = {
        let t_true = terms.mk_bool(true);
        let t_false = terms.mk_bool(false);
        bool_extras
            .into_iter()
            .filter(|&c| c != t_true && c != t_false)
            .collect()
    };
    let mut use_extras = !bool_extras.is_empty();
    if use_extras {
        let mut augmented: u64 = 1;
        for (_, sort, _, size) in &domain_sizes {
            let s = if matches!(sort, Sort::Bool) {
                size.saturating_add(bool_extras.len() as u64)
            } else {
                *size
            };
            augmented = augmented.saturating_mul(s);
        }
        if augmented > MAX_FINITE_DOMAIN_COMBOS {
            use_extras = false;
        }
    }
    let mut values_per_var: Vec<(String, Vec<TermId>)> = Vec::with_capacity(domain_sizes.len());
    for (name, sort, lo, size) in &domain_sizes {
        let mut vals: Vec<TermId> = Vec::with_capacity(*size as usize);
        for val_idx in 0..*size {
            let val_term = match sort {
                Sort::Bool => terms.mk_bool(val_idx != 0),
                Sort::BitVec(bv) => terms.mk_bitvec(BigInt::from(val_idx), bv.width),
                Sort::Int => terms.mk_int(BigInt::from(lo + val_idx as i64)),
                _ => unreachable!(),
            };
            vals.push(val_term);
        }
        if use_extras && matches!(sort, Sort::Bool) {
            vals.extend(bool_extras.iter().copied());
        }
        values_per_var.push((name.clone(), vals));
    }
    let total_combos: u64 = values_per_var.iter().map(|(_, v)| v.len() as u64).product();

    // Generate all combinations and instantiate
    let mut instances: Vec<TermId> = Vec::with_capacity(total_combos as usize);
    let mut combo_idx = 0u64;
    while combo_idx < total_combos {
        let mut subst: HashMap<String, TermId> = Default::default();
        let mut values: Vec<TermId> = Vec::with_capacity(values_per_var.len());
        let mut remaining = combo_idx;
        for (name, vals) in &values_per_var {
            let val_idx = (remaining % vals.len() as u64) as usize;
            remaining /= vals.len() as u64;
            let val_term = vals[val_idx];
            values.push(val_term);
            subst.insert(name.clone(), val_term);
        }
        let instance = subst_vars(terms, body, &subst);
        // Recursively expand nested finite-domain quantifiers (see above).
        let expanded = expand_finite_domain_subterms(terms, instance);
        if let Some(rec) = recorder.as_mut() {
            rec.push((values, expanded));
        }
        instances.push(expanded);
        combo_idx += 1;
    }

    // Combine: forall → and, exists → or
    if is_forall {
        Some(terms.mk_and(instances))
    } else {
        Some(terms.mk_or(instances))
    }
}

/// Return `true` iff `term` references any of the bound-variable names in
/// `var_names` (by name, ignoring shadowing). Used to decide whether a body
/// conjunct depends on the quantified variables. A name-based test can only
/// OVER-report (a shadowed inner binder of the same name counts as a mention),
/// which conservatively KEEPS such a conjunct inside the quantifier — sound
/// (no miniscoping) — and never UNDER-reports an outer-variable occurrence, so
/// a pulled-out conjunct is genuinely free of the quantified variables.
fn term_mentions_any_name(terms: &TermStore, term: TermId, var_names: &[&str]) -> bool {
    match terms.get(term) {
        TermData::Var(name, _) => var_names.contains(&name.as_str()),
        TermData::App(_, args) => args
            .iter()
            .any(|&arg| term_mentions_any_name(terms, arg, var_names)),
        TermData::Not(inner) => term_mentions_any_name(terms, *inner, var_names),
        TermData::Ite(c, t, e) => {
            term_mentions_any_name(terms, *c, var_names)
                || term_mentions_any_name(terms, *t, var_names)
                || term_mentions_any_name(terms, *e, var_names)
        }
        TermData::Let(bindings, body) => {
            bindings
                .iter()
                .any(|(_, v)| term_mentions_any_name(terms, *v, var_names))
                || term_mentions_any_name(terms, *body, var_names)
        }
        TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
            term_mentions_any_name(terms, *body, var_names)
        }
        TermData::Const(_) => false,
        _ => false,
    }
}

/// Fold a HALF-BOUNDED (or otherwise trivially-satisfiable) single-binder
/// existential over Int/Real to `true`.
///
/// `(exists ((X S)) atom)` is VALID — equal to `true` — when `S` is `Int` or
/// `Real` and `atom` is a single comparison (`<`, `<=`, `>`, `>=`, `=`) one of
/// whose operands is exactly the bound variable `X` and whose OTHER operand does
/// not mention `X`. For any such atom the witness set is a non-empty half-line
/// (`X </<=/>/>= rhs`) or a single point (`X = rhs`), both of which are
/// inhabited over the unbounded Int/Real domains, so an `X` satisfying the atom
/// always exists. (The reflexive degenerate shapes `(< X X)` / `(> X X)`, which
/// are UNSATISFIABLE, are excluded because they require the non-`X` operand to
/// be `X`-free.)
///
/// This is the residue that survives miniscoping a half-bounded negated
/// existential: `(not (exists X. (and (<= X 4) p)))` is normalized upstream to
/// `(or (not p) (not (exists X. (<= X 4))))`; folding the inner half-bounded
/// existential to `true` collapses the disjunct to `(not p)` (the sound SAT)
/// instead of leaving an unbounded `exists`/Skolem `forall` whose
/// counterexample-instantiation, conjoined into the problem, manufactures a
/// spurious UNSAT.
///
/// SOUNDNESS: `(exists X. atom) ≡ true` is a logical EQUIVALENCE for these
/// always-satisfiable atoms (the witness is exhibited above), so replacing the
/// existential with `true` preserves the model set exactly and cannot flip a
/// verdict. Returns `None` (no change) for any quantifier that is not one of
/// these provably-true single-binder Int/Real existentials.
fn fold_trivially_true_int_exists(terms: &mut TermStore, term: TermId) -> Option<TermId> {
    let (vars, body, triggers) = match terms.get(term).clone() {
        TermData::Exists(v, b, t) => (v, b, t),
        _ => return None,
    };
    if !triggers.is_empty() {
        return None;
    }
    // Single binder of an unbounded arithmetic sort.
    let [(name, sort)] = vars.as_slice() else {
        return None;
    };
    if !matches!(sort, Sort::Int | Sort::Real) {
        return None;
    }
    // Body must be a single comparison atom.
    let (op, args) = match terms.get(body).clone() {
        TermData::App(Symbol::Named(op), args) if args.len() == 2 => (op, args),
        _ => return None,
    };
    if !matches!(op.as_str(), "<" | "<=" | ">" | ">=" | "=") {
        return None;
    }
    let lhs = args[0];
    let rhs = args[1];
    let lhs_is_x = is_bound_var(terms, lhs, name);
    let rhs_is_x = is_bound_var(terms, rhs, name);
    // Exactly one operand is the bare bound variable, and the OTHER operand does
    // not mention it (so the atom is `X op (X-free)` or `(X-free) op X` — always
    // satisfiable). This rejects `(< X X)` / `(= X X)` etc. where both operands
    // mention `X`.
    let other = if lhs_is_x && !rhs_is_x {
        rhs
    } else if rhs_is_x && !lhs_is_x {
        lhs
    } else {
        return None;
    };
    if term_mentions_any_name(terms, other, &[name.as_str()]) {
        return None;
    }
    Some(terms.mk_bool(true))
}

/// MINISCOPE a quantifier over an `and`-body: pull every conjunct that does not
/// mention any bound variable OUT of the quantifier.
///
/// `(forall X. (and A(X) B)) ≡ (and (forall X. A(X)) B)` and
/// `(exists X. (and A(X) B)) ≡ (and (exists X. A(X)) B)` whenever `B` is free of
/// `X` (the quantifier distributes over `and`, and a quantifier-free conjunct is
/// constant w.r.t. the bound variables). Both are first-order EQUIVALENCES, so
/// the rewrite preserves the model set exactly — it can neither add nor remove a
/// satisfying assignment, hence cannot flip a verdict.
///
/// Returns `Some(rewritten)` when at least one X-free conjunct was pulled out;
/// `None` (no rewrite) when the body is not an `and`, when every conjunct
/// mentions a bound variable, or when the quantifier carries user triggers
/// (whose patterns are defined against the un-split body — we conservatively
/// leave those untouched).
///
/// This is DELIBERATELY restricted to `and`-bodies for BOTH quantifiers. It
/// never rewrites a `forall`/`exists` over `or`: the dual `forall`-over-`or`
/// rewrite is a separate, error-prone transformation and is intentionally NOT
/// performed here (a prior unsound implementation of it produced spurious
/// UNSATs).
fn miniscope_quantifier_over_and(terms: &mut TermStore, term: TermId) -> Option<TermId> {
    let (vars, body, is_forall, triggers) = match terms.get(term).clone() {
        TermData::Forall(v, b, t) => (v, b, true, t),
        TermData::Exists(v, b, t) => (v, b, false, t),
        _ => return None,
    };

    // Conservatively skip trigger-annotated quantifiers: their trigger patterns
    // are written against the whole body and may no longer match after a split.
    if !triggers.is_empty() {
        return None;
    }

    // Body must be a (flattened) conjunction.
    let conjuncts = match terms.get(body).clone() {
        TermData::App(Symbol::Named(op), _) if op == "and" => collect_and_atoms(terms, body),
        _ => return None,
    };
    if conjuncts.len() < 2 {
        return None;
    }

    let var_names: Vec<&str> = vars.iter().map(|(n, _)| n.as_str()).collect();
    let mut dependent: Vec<TermId> = Vec::new();
    let mut free: Vec<TermId> = Vec::new();
    for &c in &conjuncts {
        if term_mentions_any_name(terms, c, &var_names) {
            dependent.push(c);
        } else {
            free.push(c);
        }
    }

    // Nothing X-free to pull out → leave the quantifier intact.
    if free.is_empty() {
        return None;
    }

    // Rebuild the quantified core over the X-DEPENDENT conjuncts. When every
    // conjunct was X-free (no dependent part), the quantifier ranges over a
    // body that ignores the bound variable: SMT-LIB sorts are all non-empty, so
    // both `(forall X. true)` and `(exists X. true)` are `true`; the core
    // contributes nothing and the result is just the conjunction of the freed
    // conjuncts.
    let mut result_conjuncts: Vec<TermId> = Vec::with_capacity(free.len() + 1);
    if !dependent.is_empty() {
        let core_body = if dependent.len() == 1 {
            dependent[0]
        } else {
            terms.mk_and(dependent)
        };
        let core = if is_forall {
            terms.mk_forall(vars, core_body)
        } else {
            terms.mk_exists(vars, core_body)
        };
        result_conjuncts.push(core);
    }
    result_conjuncts.extend(free);
    Some(terms.mk_and(result_conjuncts))
}

/// Recursively expand every finite-domain quantifier that occurs ANYWHERE in
/// `term`, returning the rewritten term (or `term` unchanged when nothing is
/// expandable).
///
/// `finite_domain_expand` only rewrites a term that *is itself* a quantifier.
/// When an outer finite-domain quantifier is expanded, its instantiated body
/// may still contain inner finite-domain quantifiers in arbitrary positions
/// (commonly a DISJUNCTION of inner `forall`s produced by expanding an outer
/// `exists`, e.g. `(exists x. forall y. (= x c))` -> `(or (forall y. (= 0 c))
/// (forall y. (= 1 c)) ...)`). Those inner quantifiers must be expanded too;
/// otherwise they survive into the post-expansion problem and the downstream
/// pipeline (enumerative instantiation / strip / MBQI) treats them as
/// conjunctive obligations even though they sit in a disjunction — the
/// quantifier-alternation wrong-UNSAT family. Bottom-up: expand subterms first,
/// then the node itself, so a fully finite-domain alternating prefix collapses
/// to a quantifier-free formula.
pub(crate) fn expand_finite_domain_subterms(terms: &mut TermStore, term: TermId) -> TermId {
    match terms.get(term).clone() {
        TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => {
            // (#classA-residual) FOLD a trivially-true half-bounded single-binder
            // Int/Real existential (e.g. `(exists X. (<= X 4))`) to `true`. This
            // is the surviving residue after a half-bounded negated existential
            // is miniscoped/normalized upstream to
            // `(or (not p) (not (exists X. (<= X 4))))`: folding the inner
            // existential to `true` collapses the disjunct to `(not p)` (the
            // sound SAT) instead of leaving an unbounded exists/Skolem-`forall`
            // whose counterexample instances, conjoined into the problem, would
            // manufacture a spurious UNSAT.
            if let Some(folded) = fold_trivially_true_int_exists(terms, term) {
                return folded;
            }
            // (#classA-residual) MINISCOPE: pull the conjuncts of the
            // quantifier body that do NOT mention any bound variable OUT of the
            // quantifier — `(Q X. (and A(X) B)) ≡ (and (Q X. A(X)) B)` for `B`
            // free of `X` and `Q ∈ {forall, exists}` (the quantifier distributes
            // over `and`, and a `Q`-free conjunct is constant w.r.t. `X`). This
            // is a first-order EQUIVALENCE (no model added or removed), and it
            // only ever fires on an `and`-bodied quantifier, so it never rewrites
            // a `forall`/`exists` over `or` (the unsound forall-over-or direction
            // is NOT done here). Without it, a half-bounded negated existential
            // `(not (exists X. (and (<= X 4) p)))` leaves `p` trapped inside the
            // exists; after Skolemization the residual is consumed by the CEGQI
            // selection/counterexample machinery and dropped, yielding a spurious
            // UNSAT (the formula is SAT with `p = false`). Miniscoping frees `p`
            // as a plain ground assertion so the SAT layer decides it. We then
            // recurse so the freed conjuncts and the (possibly still-quantified,
            // possibly now finite-domain-expandable) `(Q X. A(X))` core are
            // handled by the normal walk.
            if let Some(miniscoped) = miniscope_quantifier_over_and(terms, term) {
                return expand_finite_domain_subterms(terms, miniscoped);
            }
            // Try to expand this quantifier (which already recurses into the
            // instantiated body). If it is not finite-domain expandable, leave
            // it intact so the normal E-matching/CEGQI/MBQI path handles it.
            finite_domain_expand(terms, term).unwrap_or(term)
        }
        TermData::App(sym, args) => {
            let new_args: Vec<TermId> = args
                .iter()
                .map(|&a| expand_finite_domain_subterms(terms, a))
                .collect();
            if new_args == args {
                term
            } else {
                let sort = terms.sort(term).clone();
                terms.mk_app(sym, new_args, sort)
            }
        }
        TermData::Not(inner) => {
            let new_inner = expand_finite_domain_subterms(terms, inner);
            if new_inner == inner {
                term
            } else {
                terms.mk_not(new_inner)
            }
        }
        TermData::Ite(c, t, e) => {
            let nc = expand_finite_domain_subterms(terms, c);
            let nt = expand_finite_domain_subterms(terms, t);
            let ne = expand_finite_domain_subterms(terms, e);
            if nc == c && nt == t && ne == e {
                term
            } else {
                terms.mk_ite(nc, nt, ne)
            }
        }
        TermData::Let(bindings, body) => {
            let new_bindings: Vec<(String, TermId)> = bindings
                .iter()
                .map(|(n, v)| (n.clone(), expand_finite_domain_subterms(terms, *v)))
                .collect();
            let new_body = expand_finite_domain_subterms(terms, body);
            if new_bindings == bindings && new_body == body {
                term
            } else {
                terms.mk_let(new_bindings, new_body)
            }
        }
        _ => term,
    }
}
