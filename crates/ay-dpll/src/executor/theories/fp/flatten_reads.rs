// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Constant-index array-read elimination for the ABVFP lane.
//!
//! # What this does
//!
//! Replaces every `(select A k)` with `k` a *bitvector literal* and `A` a
//! declared 1-D `(Array (_ BitVec i) (_ BitVec e))` symbol by a fresh
//! `(_ BitVec e)` constant, keyed by **(array symbol, numeric index value)**.
//! The result is an array-free QF_BVFP formula, which the existing FP/BV
//! bit-blaster decides.
//!
//! This is exactly the transformation the SMT-LIB `20170428-Liew-KLEE`
//! benchmark authors performed themselves: every QF_ABVFP file in that family
//! carries
//!
//! ```text
//! Corresponding query: An equisatisfiable query (arrays replaced with
//! bitvectors) is available at QF_BVFP/.../query.NN.smt2
//! ```
//!
//! and AY already decides that QF_BVFP encoding. This pre-pass closes the gap
//! between the two encodings of the same benchmark.
//!
//! # Soundness: this is an EQUIVALENCE, not an approximation
//!
//! Let `φ` be the assertions and `φ'` the rewrite, `fresh_{A,k}` the constant
//! introduced for cell `(A, k)`.
//!
//! * **Forward (`φ` sat ⟹ `φ'` sat).** Take any model `M` of `φ`. `M`
//!   interprets `A` as a total function; set `fresh_{A,k} := M(A)[k]` and keep
//!   every other symbol. Each rewritten atom is *syntactically* the original
//!   atom under that substitution, so it evaluates identically.
//! * **Backward (`φ'` sat ⟹ `φ` sat) — the direction that matters.** Arrays
//!   are TOTAL functions, so for any assignment to the (finitely many,
//!   pairwise-distinct-by-numeric-value) fresh constants there EXISTS an array
//!   agreeing with it at those indices and arbitrary elsewhere. The array's
//!   behaviour off those indices is unobservable *because the side conditions
//!   enforce it*:
//!   - no `store` anywhere ⇒ no positional dependence on other cells;
//!   - no array-sorted `=` / `distinct` / `ite` ⇒ no extensional comparison;
//!   - every array symbol occurs ONLY as `args[0]` of a `select` ⇒ there is no
//!     other way to observe it;
//!   - no quantifier ⇒ no universal claim over indices.
//!
//! Remove any one of those conditions and the backward direction fails, which
//! is why each is *checked on the term DAG* (where array structure is still
//! visible) rather than assumed. Both directions hold, so `sat ↔ sat` and
//! `unsat ↔ unsat`: nothing is relaxed and nothing is degraded.
//!
//! # Why this is not the #8728 shape
//!
//! #8728 was a *routing* decision: DT+FP was sent to a solver that could not
//! see the FP theory, the FP constraints were silently DROPPED, and the
//! resulting `sat` was published. Dropping a theory enlarges the model set —
//! sound for `unsat`, unsound for `sat` — and it had no side conditions to stop
//! it. Here (a) the FP theory is untouched: nothing FP-sorted is abstracted,
//! only the ARRAY theory is affected and it is *eliminated by a validated
//! rewrite*; (b) the validity conditions are checked on the term DAG, where
//! array structure is still visible (a `select` arm inside the bit-blaster
//! could not see them); (c) anything outside the conditions ABSTAINS, keeping
//! today's `unknown`.
//!
//! If a side condition is ever loosened into an approximation it may only be
//! loosened in the direction that keeps *refutation* sound, and `sat` must then
//! degrade — see the existing template at the `congruence_incomplete && Sat`
//! site in `fp.rs`.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};
use num_bigint::BigInt;

/// Stack red zone / growth for the DAG rewrite (KLEE queries nest deeply).
const FLATTEN_STACK_RED_ZONE: usize = 128 * 1024;
const FLATTEN_STACK_SIZE: usize = 16 * 1024 * 1024;

/// Why the pre-pass declined to fire. Each variant maps to a DISTINCT
/// `unknown.detail` string so the abstaining population is attributable
/// instead of joining the "no specific reason" bucket.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum FlattenAbstain {
    /// No array-sorted term occurs at all — nothing for this pass to do.
    NoArrays,
    /// A `store` occurs somewhere: cells become positionally dependent.
    Store,
    /// A quantifier occurs: a universal claim over indices is not covered.
    Quantifier,
    /// A `let` binding survived elaboration; its body is not walked here.
    LetBinding,
    /// An array sort other than 1-D `(Array (_ BitVec i) (_ BitVec e))`.
    ArraySortUnsupported,
    /// An array-sorted term that is not a declared symbol (`ite`, `store`,
    /// const-array, array-valued UF application, ...).
    ArrayTermNotSymbol,
    /// An array symbol occurs somewhere other than `args[0]` of a `select`
    /// (array `=` / `distinct` / `ite`, or an array passed to a UF).
    ArrayNotOnlySelected,
    /// A `select` index is not a bitvector literal.
    SymbolicIndex,
    /// FAIL-CLOSED BACKSTOP: the rewrite left array structure behind.
    ResidualArray,
}

impl FlattenAbstain {
    /// The `unknown.detail` text for this abstention (abstention telemetry).
    pub(super) fn detail(self) -> &'static str {
        match self {
            Self::NoArrays => {
                "ABVFP constant-index read elimination: no eliminable array read in the assertions"
            }
            Self::Store => {
                "ABVFP constant-index read elimination abstained: the assertions contain `store`, \
                 so array cells are positionally dependent"
            }
            Self::Quantifier => {
                "ABVFP constant-index read elimination abstained: the assertions are quantified, \
                 so an index claim need not be finite"
            }
            Self::LetBinding => {
                "ABVFP constant-index read elimination abstained: a `let` binding survived \
                 elaboration"
            }
            Self::ArraySortUnsupported => {
                "ABVFP constant-index read elimination abstained: array sort is not 1-D \
                 (Array (_ BitVec i) (_ BitVec e))"
            }
            Self::ArrayTermNotSymbol => {
                "ABVFP constant-index read elimination abstained: an array-sorted term is not a \
                 declared array symbol"
            }
            Self::ArrayNotOnlySelected => {
                "ABVFP constant-index read elimination abstained: an array symbol occurs outside \
                 `select` position (extensional `=`/`distinct`/`ite` or a UF argument)"
            }
            Self::SymbolicIndex => {
                "ABVFP constant-index read elimination abstained: a `select` index is not a \
                 bitvector literal"
            }
            Self::ResidualArray => {
                "ABVFP constant-index read elimination abstained: the rewrite left array \
                 structure behind (fail-closed backstop)"
            }
        }
    }
}

/// One eliminated array cell: which symbol, which numeric index, and the fresh
/// constant standing for it. Retained so a `sat` can be published against the
/// ORIGINAL array symbol rather than the internal cell constants.
#[derive(Debug, Clone)]
pub(super) struct FlatCell {
    /// The declared array symbol's term.
    pub(super) array: TermId,
    /// The index's numeric value — the KEY. `(_ bv4 64)` and
    /// `#x0000000000000004` must collapse to ONE cell; keying on index SYNTAX
    /// would split a single array cell into two independent variables and
    /// manufacture a false `sat`.
    pub(super) index_value: BigInt,
    /// The fresh element-sorted constant substituted for the read.
    pub(super) fresh: TermId,
}

/// A successful plan: the rewritten assertions plus the cell map needed to
/// reconstitute the arrays in the published model.
#[derive(Debug, Clone)]
pub(super) struct FlattenPlan {
    /// Rewritten, array-free assertions.
    pub(super) assertions: Vec<TermId>,
    /// The eliminated cells, in deterministic discovery order.
    pub(super) cells: Vec<FlatCell>,
}

/// What `plan_cells` collected before any term is built.
struct CellScan {
    /// Unique cells in discovery order: (array symbol, index value).
    cells: Vec<(TermId, BigInt)>,
    /// Every qualifying `select` term paired with its cell index. Keyed by the
    /// ORIGINAL interned `select` TermId — never by a reconstructed one, since
    /// `mk_select` is allowed to simplify and could hand back a different term.
    reads: Vec<(TermId, usize)>,
}

/// Numeric value of a bitvector literal, or `None` for anything symbolic.
fn bv_literal_value(terms: &TermStore, term: TermId) -> Option<BigInt> {
    match terms.get(term) {
        TermData::Const(Constant::BitVec { value, .. }) => Some(value.clone()),
        _ => None,
    }
}

/// Is `sort` a 1-D `(Array (_ BitVec i) (_ BitVec e))`?
fn is_bv_to_bv_array(sort: &Sort) -> bool {
    match sort {
        Sort::Array(arr) => {
            matches!(arr.index_sort, Sort::BitVec(_)) && matches!(arr.element_sort, Sort::BitVec(_))
        }
        _ => false,
    }
}

/// A `(select A i)` application, if `term` is one.
fn as_select(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) if name == "select" && args.len() == 2 => {
            Some((args[0], args[1]))
        }
        _ => None,
    }
}

/// Validate the side conditions and collect the qualifying cells.
///
/// Walks the whole DAG reachable from `assertions`. Every array-sorted term
/// must be a declared symbol of a supported sort, and must occur ONLY as
/// `args[0]` of a `select` whose index is a BV literal. Any other shape is an
/// abstention, never a guess.
fn plan_cells(terms: &TermStore, assertions: &[TermId]) -> Result<CellScan, FlattenAbstain> {
    let mut visited: HashSet<TermId> = HashSet::default();
    let mut stack: Vec<TermId> = assertions.to_vec();
    let mut cells: Vec<(TermId, BigInt)> = Vec::new();
    let mut reads: Vec<(TermId, usize)> = Vec::new();
    // (array term, numeric index value as bytes) -> cell slot.
    let mut cell_index: HashMap<(TermId, Vec<u8>), usize> = HashMap::default();
    let mut saw_array = false;

    while let Some(term) = stack.pop() {
        if !visited.insert(term) {
            continue;
        }
        if matches!(terms.sort(term), Sort::Array(_)) {
            // An array-sorted term reached NOT through the `select` arm below,
            // i.e. used in a position that can observe cells other than the
            // eliminated ones (array `=`/`distinct`/`ite`, a UF argument, a
            // `store` base). The backward direction of the equivalence needs
            // the array to be unobservable off the eliminated cells, so refuse.
            let sort = terms.sort(term).clone();
            if !is_bv_to_bv_array(&sort) {
                return Err(FlattenAbstain::ArraySortUnsupported);
            }
            if !matches!(terms.get(term), TermData::Var(_, _)) {
                return Err(FlattenAbstain::ArrayTermNotSymbol);
            }
            return Err(FlattenAbstain::ArrayNotOnlySelected);
        }
        match terms.get(term) {
            TermData::App(sym, args) => {
                if sym.name() == "store" {
                    return Err(FlattenAbstain::Store);
                }
                if let Some((array, index)) = as_select(terms, term) {
                    saw_array = true;
                    let array_sort = terms.sort(array).clone();
                    if !matches!(array_sort, Sort::Array(_)) {
                        return Err(FlattenAbstain::ArrayTermNotSymbol);
                    }
                    if !is_bv_to_bv_array(&array_sort) {
                        return Err(FlattenAbstain::ArraySortUnsupported);
                    }
                    if !matches!(terms.get(array), TermData::Var(_, _)) {
                        return Err(FlattenAbstain::ArrayTermNotSymbol);
                    }
                    let Some(value) = bv_literal_value(terms, index) else {
                        return Err(FlattenAbstain::SymbolicIndex);
                    };
                    // Key on the NUMERIC value, never on index syntax.
                    let key = (array, value.to_signed_bytes_le());
                    let slot = match cell_index.get(&key) {
                        Some(&slot) => slot,
                        None => {
                            let slot = cells.len();
                            cells.push((array, value));
                            cell_index.insert(key, slot);
                            slot
                        }
                    };
                    reads.push((term, slot));
                    // Deliberately do NOT push `array` — that is the one legal
                    // occurrence. The index is a literal with no children.
                    continue;
                }
                stack.extend_from_slice(args);
            }
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, t, e) => {
                stack.push(*c);
                stack.push(*t);
                stack.push(*e);
            }
            TermData::Let(bindings, body) => {
                if !bindings.is_empty() {
                    return Err(FlattenAbstain::LetBinding);
                }
                stack.push(*body);
            }
            TermData::Forall(..) | TermData::Exists(..) => {
                return Err(FlattenAbstain::Quantifier);
            }
            TermData::Const(_) | TermData::Var(_, _) => {}
            // `TermData` is `#[non_exhaustive]`: an unclassified future variant
            // could hide an array occurrence, so refuse rather than guess.
            _ => return Err(FlattenAbstain::ArrayTermNotSymbol),
        }
    }

    if !saw_array || cells.is_empty() {
        return Err(FlattenAbstain::NoArrays);
    }
    Ok(CellScan { cells, reads })
}

/// Rewrite `term`, replacing each planned `select` with its fresh constant.
/// Structure-preserving everywhere else.
fn rewrite(
    terms: &mut TermStore,
    term: TermId,
    subst: &HashMap<TermId, TermId>,
    memo: &mut HashMap<TermId, TermId>,
) -> TermId {
    stacker::maybe_grow(FLATTEN_STACK_RED_ZONE, FLATTEN_STACK_SIZE, || {
        if let Some(&hit) = memo.get(&term) {
            return hit;
        }
        if let Some(&fresh) = subst.get(&term) {
            memo.insert(term, fresh);
            return fresh;
        }
        let result = match terms.get(term).clone() {
            TermData::App(sym, args) => {
                let new_args: Vec<TermId> = args
                    .iter()
                    .map(|&a| rewrite(terms, a, subst, memo))
                    .collect();
                if new_args == args {
                    term
                } else {
                    let sort = terms.sort(term).clone();
                    terms.mk_app(sym, new_args, sort)
                }
            }
            TermData::Not(inner) => {
                let new_inner = rewrite(terms, inner, subst, memo);
                if new_inner == inner {
                    term
                } else {
                    terms.mk_not_raw(new_inner)
                }
            }
            TermData::Ite(c, t, e) => {
                let nc = rewrite(terms, c, subst, memo);
                let nt = rewrite(terms, t, subst, memo);
                let ne = rewrite(terms, e, subst, memo);
                if nc == c && nt == t && ne == e {
                    term
                } else {
                    terms.mk_ite_raw(nc, nt, ne)
                }
            }
            // Everything else is a leaf for this rewrite. `plan_cells` already
            // refused `let`/quantifier shapes, so nothing reachable can hide a
            // `select` here; `is_array_free` re-verifies it anyway.
            _ => term,
        };
        memo.insert(term, result);
        result
    })
}

/// FAIL-CLOSED BACKSTOP: no array-sorted term, `select` or `store` may survive.
///
/// This is not decoration. `plan_cells` and `rewrite` walk the DAG
/// independently; if they ever disagree (a future `TermData` variant, a shape
/// the rewriter treats as a leaf) the residue would be an array term handed to
/// a solver that cannot see the array theory — the #8728 failure mode.
/// Detecting it here converts that into an abstention.
fn is_array_free(terms: &TermStore, assertions: &[TermId]) -> bool {
    let mut visited: HashSet<TermId> = HashSet::default();
    let mut stack: Vec<TermId> = assertions.to_vec();
    while let Some(term) = stack.pop() {
        if !visited.insert(term) {
            continue;
        }
        if matches!(terms.sort(term), Sort::Array(_)) {
            return false;
        }
        match terms.get(term) {
            TermData::App(sym, args) => {
                if matches!(
                    sym.name(),
                    "select" | "store" | "const-array" | "lambda-array"
                ) {
                    return false;
                }
                stack.extend_from_slice(args);
            }
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, t, e) => {
                stack.push(*c);
                stack.push(*t);
                stack.push(*e);
            }
            TermData::Let(bindings, body) => {
                stack.extend(bindings.iter().map(|(_, v)| *v));
                stack.push(*body);
            }
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
            _ => {}
        }
    }
    true
}

/// Build the flattening plan for `assertions`, or say why not.
///
/// Verdict-neutral on `Err`: the caller leaves `ctx.assertions` untouched and
/// behaves exactly as before this pass existed.
pub(super) fn plan(
    terms: &mut TermStore,
    assertions: &[TermId],
) -> Result<FlattenPlan, FlattenAbstain> {
    let scan = plan_cells(terms, assertions)?;

    let mut cells: Vec<FlatCell> = Vec::with_capacity(scan.cells.len());
    for (array, index_value) in scan.cells {
        let Sort::Array(arr) = terms.sort(array).clone() else {
            return Err(FlattenAbstain::ArraySortUnsupported);
        };
        // Name the cell constant by the array's INTERNED TERM ID, not by its
        // visible name: two distinct array symbols may share a user-facing name
        // (`mk_fresh_named_var` after a `pop`), and keying by name would alias
        // two independent arrays into one variable — a false `sat`. The `__ay_`
        // prefix cannot collide with a user symbol (the frontend rejects it).
        let name = format!("__ay_arrflat!{}_{}", array.index(), index_value);
        // `mk_var` returns the EXISTING term when name+sort already exist, which
        // makes the pass idempotent across repeated `check-sat` calls.
        let fresh = terms.mk_var(name, arr.element_sort.clone());
        cells.push(FlatCell {
            array,
            index_value,
            fresh,
        });
    }

    let mut subst: HashMap<TermId, TermId> = HashMap::default();
    for (select_term, slot) in scan.reads {
        subst.insert(select_term, cells[slot].fresh);
    }

    let mut memo: HashMap<TermId, TermId> = HashMap::default();
    let rewritten: Vec<TermId> = assertions
        .iter()
        .map(|&a| rewrite(terms, a, &subst, &mut memo))
        .collect();

    if !is_array_free(terms, &rewritten) {
        return Err(FlattenAbstain::ResidualArray);
    }
    Ok(FlattenPlan {
        assertions: rewritten,
        cells,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bv_array(index_w: u32, elem_w: u32) -> Sort {
        Sort::array(Sort::bitvec(index_w), Sort::bitvec(elem_w))
    }

    #[test]
    fn collapses_equal_index_values_into_one_cell() {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", bv_array(32, 8));
        // Two spellings of index 4 at the same width must map to ONE cell; a
        // second numeric index must get its own.
        let i1 = terms.mk_bitvec(BigInt::from(4), 32);
        let i2 = terms.mk_bitvec(BigInt::from(4u64), 32);
        let j = terms.mk_bitvec(BigInt::from(5), 32);
        let s1 = terms.mk_select(a, i1);
        let s2 = terms.mk_select(a, i2);
        let s3 = terms.mk_select(a, j);
        let eq = terms.mk_eq(s1, s2);
        let eq2 = terms.mk_eq(s1, s3);
        let ne = terms.mk_not(eq2);
        let plan = plan(&mut terms, &[eq, ne]).expect("plan should fire");
        assert_eq!(plan.cells.len(), 2, "cells: {:?}", plan.cells);
        assert!(is_array_free(&terms, &plan.assertions));
    }

    #[test]
    fn distinct_arrays_never_share_a_cell_constant() {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", bv_array(32, 8));
        let b = terms.mk_var("b", bv_array(32, 8));
        let i = terms.mk_bitvec(BigInt::from(0), 32);
        let sa = terms.mk_select(a, i);
        let sb = terms.mk_select(b, i);
        let eq = terms.mk_eq(sa, sb);
        let plan = plan(&mut terms, &[eq]).expect("plan should fire");
        assert_eq!(plan.cells.len(), 2);
        assert_ne!(plan.cells[0].fresh, plan.cells[1].fresh);
    }

    #[test]
    fn abstains_on_store() {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", bv_array(32, 8));
        let i = terms.mk_bitvec(BigInt::from(0), 32);
        let v = terms.mk_bitvec(BigInt::from(7), 8);
        let st = terms.mk_store(a, i, v);
        let rd = terms.mk_select(st, i);
        let lit = terms.mk_bitvec(BigInt::from(9), 8);
        let eq = terms.mk_eq(rd, lit);
        assert!(matches!(
            plan(&mut terms, &[eq]),
            Err(FlattenAbstain::Store | FlattenAbstain::NoArrays)
        ));
    }

    #[test]
    fn abstains_on_symbolic_index() {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", bv_array(32, 8));
        let i = terms.mk_var("i", Sort::bitvec(32));
        let rd = terms.mk_select(a, i);
        let lit = terms.mk_bitvec(BigInt::from(7), 8);
        let eq = terms.mk_eq(rd, lit);
        assert!(matches!(
            plan(&mut terms, &[eq]),
            Err(FlattenAbstain::SymbolicIndex)
        ));
    }

    #[test]
    fn abstains_on_array_equality() {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", bv_array(32, 8));
        let b = terms.mk_var("b", bv_array(32, 8));
        let eq = terms.mk_eq(a, b);
        assert!(matches!(
            plan(&mut terms, &[eq]),
            Err(FlattenAbstain::ArrayNotOnlySelected)
        ));
    }

    #[test]
    fn abstains_on_non_bv_array_sort() {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", Sort::array(Sort::Int, Sort::bitvec(8)));
        let i = terms.mk_int(BigInt::from(0));
        let rd = terms.mk_select(a, i);
        let lit = terms.mk_bitvec(BigInt::from(7), 8);
        let eq = terms.mk_eq(rd, lit);
        assert!(matches!(
            plan(&mut terms, &[eq]),
            Err(FlattenAbstain::ArraySortUnsupported)
        ));
    }

    #[test]
    fn abstains_when_no_array_present() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::bitvec(8));
        let lit = terms.mk_bitvec(BigInt::from(7), 8);
        let eq = terms.mk_eq(x, lit);
        assert!(matches!(
            plan(&mut terms, &[eq]),
            Err(FlattenAbstain::NoArrays)
        ));
    }
}
