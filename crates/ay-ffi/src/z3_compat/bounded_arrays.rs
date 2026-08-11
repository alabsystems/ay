// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Extensional exactness for arrays indexed by a bounded-Int-lowered sort.
//!
//! # The gap
//!
//! [`Sort::Char`] and [`Sort::FiniteDomain`] are represented by `Int` in the
//! core term store (`Sort::as_term_sort`), so `(Array Char E)` becomes
//! `(Array Int E)` and gains indices (`-1`, `196608`, …) that NO public formula
//! can name: `Z3_mk_select`/`Z3_mk_store` reject a non-`Char` public index, and
//! every `Char`-sorted term carries the standing `0 <= t <= 196607` invariant.
//!
//! Quantifier construction relativizes `forall ch:Char` to that carrier
//! (`guard_bounded_quantifier_body`), which is required for soundness of e.g.
//! `forall c:Char. (char.to_int c) <= 196607`. The two together leave a hole:
//! the engine can satisfy "agrees at every PUBLIC index AND is a different core
//! array" by differing at `-1`, reporting `unknown`/`sat` where z3 reports
//! `unsat`.
//!
//! Measured against the pinned oracle (z3 5.0.0):
//!
//! ```text
//! a,b : (Array Char Bool)   ForAll([ch], a[ch] == b[ch]), a != b   => unsat
//! x,y : (Array D3 Bool)     ForAll([d],  x[d]  == y[d]),  x != y   => unsat
//! a != b                                                          => sat
//! a[0] == b[0], a != b                                            => sat
//! ForAll([ch], a[ch] == b[ch]), a[0] != b[0]                      => unsat
//! ```
//!
//! # The lemma, and exactly when it is entailed
//!
//! [`record_bounded_array_ext_lemma`] recognizes a public extensionality
//! formula
//!
//! ```text
//! Q  =  forall i:BoundedIndex. select(a, i) = select(b, i)
//! ```
//!
//! and registers the CORE equality `a = b` as a lemma keyed by `Q`. The lemma
//! is injected into a check only when (1) that check's goal actually asserts
//! `Q` at top level, and (2) the check's whole term set passes
//! [`goal_admits_canonical_extension`].
//!
//! SOUNDNESS (no spurious unsat). Let `P` be the public problem the check
//! encodes and suppose `P` has a public model `M`. Public arrays over a bounded
//! index sort are functions from the finite CARRIER `[0, hi]`; build a core
//! model `M'` by interpreting every free array symbol `a` of that sort as its
//! CANONICAL EXTENSION
//!
//! ```text
//! a'(i) = a(i)  for i in [0, hi],        a'(i) = a(0)  otherwise
//! ```
//!
//! (index `0` is always a carrier member: `Char` and finite-domain carriers are
//! non-empty and begin at zero), leaving every other symbol at its `M` value.
//! Two canonical extensions are core-equal EXACTLY when they agree on the
//! carrier, i.e. exactly when they are publicly equal — so under `M'` every
//! core array (dis)equality of the goal has the same truth value it has under
//! `M`, and every `select` is at a carrier index and reads the same value.
//! Hence `M' |= P_core`, and since `Q` says `a` and `b` agree on the whole
//! carrier, `M' |= a = b` as well. The lemma therefore removes no public model.
//!
//! THAT ARGUMENT NEEDS EVERY ARRAY TERM OF THE SORT TO BE A CANONICAL
//! EXTENSION, which is a property of the goal's TERMS, not just of its sorts.
//! It is false for interpreted array terms:
//!
//! ```text
//! D1 = (_ FiniteDomain 1)          carrier = {0}
//! a = const(D1, true)              off-carrier value: true
//! b = store(const(D1, false), 0, true)   off-carrier value: false
//! forall d:D1. a[d] = b[d]         holds: both read `true` at 0
//! ```
//!
//! `a` and `b` are publicly equal and CORE-UNEQUAL, and no reinterpretation of
//! a free symbol can change that — `const-array` pins every core index and
//! `store` inherits its base's off-carrier values. Injecting `a = b` there
//! refutes a satisfiable goal (z3 5.0.0 answers `unknown`). So the guard is on
//! the TERM shape of the whole goal, not on the sort:
//! [`goal_admits_canonical_extension`] demands that every term of the lowered
//! array sort anywhere in the check is a FREE CONSTANT — no `const-array`, no
//! `store`, no `ite`, no `map`, no array-sorted binder, nothing opaque — and
//! that every read of such an array is at an index carrying the carrier
//! invariant. Anything else fails closed: no lemma, and the check behaves
//! exactly as it did before this module existed.

use ay_dpll::api::{Sort, Term, TermKind};

use super::{
    bounded_sort_hi, finite_set_engine_public_sort, lookup_ast_sort, sort_mentions_finite_set,
    term_to_ast, Z3Context,
};

/// Subterm visits allowed to one canonicity scan before it fails closed.
///
/// The scan is linear in the goal's DAG size, so this only ever trips on
/// pathologically large goals — where refusing the lemma (and answering exactly
/// as the pre-lemma solver did) is the correct outcome anyway.
const CANONICITY_SCAN_BUDGET: usize = 1_000_000;

/// A registered "public array extensionality" lemma: `key |= left = right`,
/// valid only for goals that admit the canonical extension (module docs).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct BoundedArrayExtLemma {
    /// Left array operand — always a free constant.
    pub(crate) left: Term,
    /// Right array operand — always a free constant.
    pub(crate) right: Term,
    /// The core equality this lemma concludes.
    pub(crate) equality: Term,
    /// The LOWERED (engine) array sort shared by both operands.
    pub(crate) core_array_sort: Sort,
    /// Inclusive upper bound of the public index sort's carrier.
    pub(crate) carrier_hi: i64,
}

/// Whether `sort` contains a bounded sort along an `Array` lowering path.
///
/// `Sort::as_term_sort` recursively lowers array domains/ranges, so an array
/// nested inside another array index is relevant here.
fn contains_bounded_array_lowering(sort: &Sort) -> bool {
    match sort {
        Sort::Char | Sort::FiniteDomain(_, _) => true,
        Sort::Array(array) => {
            contains_bounded_array_lowering(&array.index_sort)
                || contains_bounded_array_lowering(&array.element_sort)
        }
        _ => false,
    }
}

/// Whether the canonical-extension model construction of the module docs exists
/// for a public array sort.
///
/// The index must be DIRECTLY bounded (`Char`, finite domain): its carrier is
/// then a finite prefix of the `Int` lowering. The ELEMENT sort must contain no
/// further bounded lowering — an element that is itself a bounded-carrier array
/// would need its own (recursive) canonicalization, whose terms this module
/// does not inspect, so those shapes are refused outright.
pub(crate) fn bounded_array_sort_supported(sort: &Sort) -> bool {
    match sort {
        Sort::Array(array) => {
            bounded_sort_hi(&array.index_sort).is_some()
                && !contains_bounded_array_lowering(&array.element_sort)
        }
        _ => false,
    }
}

/// The sort `term` actually carries IN THE ENGINE.
///
/// `Solver::term_sort` reports the PUBLIC sort for a declared constant (it
/// prefers `var_sorts`), so `a : (Array Char Bool)` answers `(Array Char Bool)`
/// while the `const-array` term the same goal builds answers its interned
/// `(Array Int Bool)`. Comparing those two directly would let an interpreted
/// array slip past the canonicity scan — exactly the shape the scan exists to
/// catch — so every comparison in this module goes through the same lowering
/// `Z3_mk_const` applies (`finite_set_engine_public_sort` then
/// `Sort::as_term_sort`), which is idempotent on an already-lowered sort.
fn engine_sort_of(ctx: &Z3Context, term: Term) -> Sort {
    finite_set_engine_public_sort(ctx, &ctx.solver.term_sort(term)).as_term_sort()
}

/// Whether `term` is an uninterpreted 0-ary symbol (a free constant).
///
/// NOTE: a quantifier binder is represented by the SAME `Var` node as the
/// public constant it abstracts (`Solver::try_forall` binds by name), so this
/// predicate alone does not distinguish a free constant from a bound
/// occurrence. [`goal_admits_canonical_extension`] rejects any goal whose
/// quantifiers bind a variable of the array sort, which closes that gap.
fn is_free_constant(ctx: &Z3Context, term: Term) -> bool {
    matches!(ctx.solver.term_kind(term), TermKind::Var { .. })
        && ctx.solver.term_children(term).is_empty()
}

/// Whether `needle` occurs anywhere inside `root` (used as the binder-escape
/// check). Budget-bounded; an exhausted budget reports `true` (fail closed).
fn term_contains(ctx: &Z3Context, root: Term, needle: Term) -> bool {
    let mut seen = std::collections::HashSet::new();
    let mut stack = vec![root];
    let mut budget = CANONICITY_SCAN_BUDGET;
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if budget == 0 {
            return true;
        }
        budget -= 1;
        if term == needle {
            return true;
        }
        stack.extend(ctx.solver.term_children(term));
    }
    false
}

/// Recognize `select(_, index)` and return the array it reads.
fn selected_array_at(ctx: &Z3Context, term: Term, index: Term) -> Option<Term> {
    let TermKind::App { name, num_args: 2 } = ctx.solver.term_kind(term) else {
        return None;
    };
    if name != "select" {
        return None;
    }
    let children = ctx.solver.term_children(term);
    (children.len() == 2 && children[1] == index).then_some(children[0])
}

/// Public sort of an array operand, preferring the recorded public sort over
/// the (Char-erased) engine sort.
fn public_array_sort(ctx: &Z3Context, array: Term) -> Option<Sort> {
    lookup_ast_sort(ctx, term_to_ast(ctx, array)).cloned()
}

/// Whether `index` provably ranges inside `[0, hi]`.
///
/// `record_ast_sort` attaches that standing invariant to every term whose
/// PUBLIC sort is `Char` / a finite domain, and records the pair here, so
/// membership is exactly "this term carries the carrier invariant". A term that
/// does not is treated as a possible off-carrier read and fails the scan.
fn index_is_carrier_bounded(ctx: &Z3Context, index: Term, hi: i64) -> bool {
    ctx.range_bounded.contains(&(index, hi))
}

/// Whether the canonical extension of the module docs can be built for every
/// array of `lemma.core_array_sort` occurring in `roots`.
///
/// `roots` must cover EVERYTHING the engine will see for this check (goal,
/// assumptions, extra lemmas, background axioms). The scan is deliberately
/// blunt — it demands that every term of that lowered sort is a free constant —
/// because any interpreted array term (`const-array`, `store`, `ite`, a `map`,
/// a `lambda`, an array-sorted binder or let-name) can pin or inherit
/// off-carrier values that no reinterpretation of a free symbol can repair.
pub(crate) fn goal_admits_canonical_extension(
    ctx: &Z3Context,
    lemma: &BoundedArrayExtLemma,
    roots: &[Term],
) -> bool {
    let mut seen = std::collections::HashSet::new();
    let mut stack: Vec<Term> = roots.to_vec();
    let mut budget = CANONICITY_SCAN_BUDGET;
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if budget == 0 {
            return false;
        }
        budget -= 1;

        let kind = ctx.solver.term_kind(term);
        match &kind {
            // A `let` can name an array-sorted term; the name is indistinguishable
            // from a free constant here, so refuse the whole goal.
            TermKind::Let => return false,
            // A binder of the array sort ranges over ALL core arrays, including
            // the non-canonical ones the extension argument excludes.
            TermKind::Forall | TermKind::Exists => {
                let Some(vars) = ctx.solver.quantifier_bound_vars(term) else {
                    return false;
                };
                if vars
                    .iter()
                    .any(|(_, sort)| sort.as_term_sort() == lemma.core_array_sort)
                {
                    return false;
                }
            }
            // Every read of a candidate-sorted array must be at a carrier index,
            // else `M'` and the public model can disagree on it.
            TermKind::App { name, num_args: 2 } if name == "select" => {
                let children = ctx.solver.term_children(term);
                if children.len() == 2
                    && engine_sort_of(ctx, children[0]) == lemma.core_array_sort
                    && !index_is_carrier_bounded(ctx, children[1], lemma.carrier_hi)
                {
                    return false;
                }
            }
            _ => {}
        }

        if engine_sort_of(ctx, term) == lemma.core_array_sort && !is_free_constant(ctx, term) {
            return false;
        }

        stack.extend(ctx.solver.term_children(term));
    }
    true
}

/// Register `a = b` as a lemma of a public array-extensionality formula.
///
/// `public_body` is the body EXACTLY as the caller wrote it, before
/// `guard_bounded_quantifier_body` relativizes it to the carrier.
///
/// Nothing is registered unless every syntactic hypothesis holds: the binder's
/// public sort has a finite carrier, the body is pointwise agreement of two
/// reads AT that binder, both operands are FREE CONSTANTS (so no `const-array`
/// / `store` / `ite` can pin their off-carrier values) that do not capture the
/// binder, both carry the same public array sort indexed by exactly the binder
/// sort, and that sort admits the canonical extension
/// ([`bounded_array_sort_supported`]). The remaining, goal-dependent hypothesis
/// is re-checked at solve time by [`goal_admits_canonical_extension`].
pub(crate) fn record_bounded_array_ext_lemma(
    ctx: &mut Z3Context,
    quantifier: Term,
    bound: Term,
    bound_sort: &Sort,
    public_body: Term,
) {
    let Some(carrier_hi) = bounded_sort_hi(bound_sort) else {
        return;
    };
    let TermKind::App { name, num_args: 2 } = ctx.solver.term_kind(public_body) else {
        return;
    };
    if name != "=" {
        return;
    }
    let sides = ctx.solver.term_children(public_body);
    if sides.len() != 2 {
        return;
    }
    let Some(left) = selected_array_at(ctx, sides[0], bound) else {
        return;
    };
    let Some(right) = selected_array_at(ctx, sides[1], bound) else {
        return;
    };
    if left == right {
        return; // `a = a` carries no information
    }
    // TERM shape, not just sort shape: only a free symbol's off-carrier values
    // are free to be reinterpreted by the canonical extension.
    if !is_free_constant(ctx, left) || !is_free_constant(ctx, right) {
        return;
    }
    // Binder capture: `forall ch. a[ch] = (store b (f ch) true)[ch]` would
    // otherwise record `a = store(b, f(ch), true)` with `ch` ESCAPING as a free
    // constant — a strictly different, unentailed claim. A free constant cannot
    // contain the binder, so this is belt-and-braces; it is kept because it is
    // the property the lemma actually needs.
    if term_contains(ctx, left, bound) || term_contains(ctx, right, bound) {
        return;
    }
    let (Some(left_sort), Some(right_sort)) =
        (public_array_sort(ctx, left), public_array_sort(ctx, right))
    else {
        return;
    };
    if left_sort != right_sort {
        return;
    }
    let Sort::Array(array) = &left_sort else {
        return;
    };
    if array.index_sort != *bound_sort {
        return;
    }
    // No canonical representative for this shape => no lemma.
    if !bounded_array_sort_supported(&left_sort) {
        return;
    }
    // FiniteSet-backed sorts are themselves re-encoded as arrays; keep them out.
    if sort_mentions_finite_set(ctx, &left_sort) {
        return;
    }
    let core_array_sort = engine_sort_of(ctx, left);
    if engine_sort_of(ctx, right) != core_array_sort {
        return;
    }
    let Sort::Array(_) = &core_array_sort else {
        return;
    };

    let equality = ctx.solver.eq(left, right);
    let lemma = BoundedArrayExtLemma {
        left,
        right,
        equality,
        core_array_sort,
        carrier_hi,
    };
    if ctx.bounded_array_ext_lemmas.get(&quantifier) == Some(&lemma) {
        return;
    }
    ctx.bounded_array_ext_lemmas.insert(quantifier, lemma);
    ctx.clear_decision_check_artifacts();
}

/// The extensionality equalities entailed by this check.
///
/// `keys` are terms known to hold at TOP LEVEL for this check (the handle's
/// assertion list and the goal it was transformed into) — a lemma is a
/// consequence of its key, so keying on a top-level fact is what makes the
/// injection conditional rather than context-global. `roots` must cover every
/// term the engine will see, and is what the canonicity scan inspects.
pub(crate) fn bounded_array_ext_consequences(
    ctx: &Z3Context,
    keys: &[Term],
    roots: &[Term],
) -> Vec<Term> {
    if ctx.bounded_array_ext_lemmas.is_empty() {
        return Vec::new();
    }
    let mut out: Vec<Term> = Vec::new();
    let mut considered = std::collections::HashSet::new();
    // The scan's verdict depends only on `(core_array_sort, carrier_hi)`, so
    // several lemmas over the same sort share one walk of the goal.
    let mut scanned: Vec<((Sort, i64), bool)> = Vec::new();
    for key in keys {
        if !considered.insert(*key) {
            continue;
        }
        let Some(lemma) = ctx.bounded_array_ext_lemmas.get(key) else {
            continue;
        };
        if out.contains(&lemma.equality) {
            continue;
        }
        let shape = (lemma.core_array_sort.clone(), lemma.carrier_hi);
        let admits = match scanned.iter().find(|(seen, _)| *seen == shape) {
            Some((_, verdict)) => *verdict,
            None => {
                let verdict = goal_admits_canonical_extension(ctx, lemma, roots);
                scanned.push((shape, verdict));
                verdict
            }
        };
        if !admits {
            continue;
        }
        out.push(lemma.equality);
    }
    out
}
