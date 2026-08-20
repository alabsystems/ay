// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact strict theorems for two intrinsic term-`ite` tautology shapes that
//! ite/store clausification emits as pedigree-free original clauses.
//!
//! **Branch projection** ([`validate_ite_branch_projection`]): the clause
//! `(cl C (= (ite C a b) b))` or `(cl (not C) (= (ite C a b) a))` — either
//! equality orientation, either literal order, or-packed unit accepted.
//! Falsifying the first requires `C` false AND the equality false, but `C`
//! false forces the `ite` to its else branch, where the equality holds by
//! reflexivity; dually for the second. Valid for ANY branch sorts — no theory
//! content is consulted.
//!
//! **Guarded ROW expansion** ([`validate_array_guarded_row_expansion`]): the
//! clause `(cl (not (= E (store A i v))) F)` where
//! `F = (ite (= i j) (= v (select E j)) (= (select A j) (select E j)))` —
//! equality orientations and the `(= j i)` condition spelling accepted.
//! Falsifying it requires `E = store A i v`, under which
//! `select E j = select (store A i v) j`, and the read-over-write axiom makes
//! `F` true in both `ite` branches. This is the ROW axiom routed through one
//! authored array equality — the shape ite-lowering of `select`-over-`store`
//! leaves behind after definition substitution.

use ay_core::{ProofId, Sort, Symbol, TermData, TermId, TermStore};

use super::ProofCheckError;

fn invalid(step: ProofId, rule: &str, reason: &str) -> ProofCheckError {
    ProofCheckError::InvalidTheoryLemma {
        step,
        reason: format!("{rule}: {reason}"),
    }
}

/// Flatten a single-literal `(cl (or L1 .. Ln))` clause into `[L1, .., Ln]`;
/// every other clause is returned unchanged (same packed-`or` reading as the
/// seq/array/euf lanes).
fn flatten_clause_literals(terms: &TermStore, clause: &[TermId]) -> Vec<TermId> {
    if clause.len() == 1 {
        if let TermData::App(Symbol::Named(sym), args) = terms.get(clause[0]) {
            if sym == "or" && args.len() >= 2 {
                return args.clone();
            }
        }
    }
    clause.to_vec()
}

fn strip_not(terms: &TermStore, term: TermId) -> (TermId, bool) {
    match terms.get(term) {
        TermData::Not(inner) => (*inner, true),
        _ => (term, false),
    }
}

fn decode_eq(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
            Some((args[0], args[1]))
        }
        _ => None,
    }
}

/// `(= x y)` matches `target` on either side; returns the OTHER side.
fn eq_other_side(terms: &TermStore, eq: TermId, target: TermId) -> Option<TermId> {
    let (left, right) = decode_eq(terms, eq)?;
    if left == target {
        Some(right)
    } else if right == target {
        Some(left)
    } else {
        None
    }
}

/// Validate a [`ay_core::TheoryLemmaKind::IteBranchProjection`] clause.
pub(crate) fn validate_ite_branch_projection(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    let literals = flatten_clause_literals(terms, clause);
    let [first, second] = literals.as_slice() else {
        return Err(invalid(
            step_id,
            "IteBranchProjection",
            "clause must have exactly 2 literals",
        ));
    };
    for (cond_lit, eq_lit) in [(*first, *second), (*second, *first)] {
        let (cond_atom, cond_negated) = strip_not(terms, cond_lit);
        let Some((eq_left, eq_right)) = decode_eq(terms, eq_lit) else {
            continue;
        };
        for (ite_term, other) in [(eq_left, eq_right), (eq_right, eq_left)] {
            let TermData::Ite(condition, then_branch, else_branch) = terms.get(ite_term) else {
                continue;
            };
            if *condition != cond_atom {
                continue;
            }
            // `C ∨ (ite C a b) = b`  /  `¬C ∨ (ite C a b) = a`.
            let projected = if cond_negated {
                *then_branch
            } else {
                *else_branch
            };
            if other == projected {
                return Ok(());
            }
        }
    }
    Err(invalid(
        step_id,
        "IteBranchProjection",
        "no condition literal projects the ite equality onto its selected branch",
    ))
}

/// Declaration-free recognizer: `true` exactly when
/// [`validate_ite_branch_projection`] accepts the clause.
#[must_use]
pub fn recognize_ite_branch_projection(terms: &TermStore, clause: &[TermId]) -> bool {
    validate_ite_branch_projection(terms, ProofId(0), clause).is_ok()
}

fn decode_store(terms: &TermStore, term: TermId) -> Option<(TermId, TermId, TermId)> {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) if name == "store" && args.len() == 3 => {
            Some((args[0], args[1], args[2]))
        }
        _ => None,
    }
}

fn decode_select(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) if name == "select" && args.len() == 2 => {
            Some((args[0], args[1]))
        }
        _ => None,
    }
}

/// Validate a [`ay_core::TheoryLemmaKind::ArrayGuardedRowExpansion`] clause.
pub(crate) fn validate_array_guarded_row_expansion(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    let literals = flatten_clause_literals(terms, clause);
    // Three-literal spellings: the same expansion with the `ite` clausified
    // away. Shape B (row-neg): `(cl (not (= E (store A i v))) (= i j)
    // (= (select A j) (select E j)))` — under the guard, `i ≠ j` forces the
    // untouched-cell equality. Shape C (row-pos):
    // `(cl (not (= E (store A i v))) (not (= i j)) (= v (select E j)))` —
    // under the guard, `i = j` reads the stored value back.
    if literals.len() == 3 {
        if validate_three_literal_guarded_row(terms, &literals) {
            return Ok(());
        }
        return Err(invalid(
            step_id,
            "ArrayGuardedRowExpansion",
            "3-literal clause is not a guarded read-over-write case",
        ));
    }
    let [first, second] = literals.as_slice() else {
        return Err(invalid(
            step_id,
            "ArrayGuardedRowExpansion",
            "clause must have exactly 2 literals",
        ));
    };
    for (guard_lit, formula) in [(*first, *second), (*second, *first)] {
        let (guard_atom, guard_negated) = strip_not(terms, guard_lit);
        if !guard_negated {
            continue;
        }
        let Some((guard_left, guard_right)) = decode_eq(terms, guard_atom) else {
            continue;
        };
        for (read_array, store_term) in [(guard_left, guard_right), (guard_right, guard_left)] {
            let Some((base_array, store_index, stored_value)) = decode_store(terms, store_term)
            else {
                continue;
            };
            if terms.sort(read_array) != terms.sort(store_term) {
                continue;
            }
            let TermData::Ite(condition, then_branch, else_branch) = terms.get(formula) else {
                continue;
            };
            let (condition, then_branch, else_branch) = (*condition, *then_branch, *else_branch);
            // The condition names the probe index against the store index.
            let Some(probe_index) = eq_other_side(terms, condition, store_index) else {
                continue;
            };
            if terms.sort(probe_index) != terms.sort(store_index) {
                continue;
            }
            // Both branches must read `(select E j)`; the term is decoded
            // from each branch rather than looked up, so shared subterm ids
            // are not required.
            let is_read = |term: TermId| {
                decode_select(terms, term)
                    .is_some_and(|(array, index)| array == read_array && index == probe_index)
            };
            // then: `(= v (select E j))` — the stored value read back.
            let then_ok = decode_eq(terms, then_branch).is_some_and(|(left, right)| {
                (left == stored_value && is_read(right)) || (right == stored_value && is_read(left))
            });
            // else: `(= (select A j) (select E j))` — the untouched cell.
            let is_base_read = |term: TermId| {
                decode_select(terms, term)
                    .is_some_and(|(array, index)| array == base_array && index == probe_index)
            };
            let else_ok = decode_eq(terms, else_branch).is_some_and(|(left, right)| {
                (is_base_read(left) && is_read(right)) || (is_base_read(right) && is_read(left))
            });
            if then_ok && else_ok {
                return Ok(());
            }
        }
    }
    Err(invalid(
        step_id,
        "ArrayGuardedRowExpansion",
        "clause is not a store-equality-guarded read-over-write expansion",
    ))
}

/// Shape D: the guard equates TWO stores at the SAME index —
/// `(cl (not (= (store A i v) (store B i w))) P (= i j))` where `P` is either
/// the base-select equality `(= (select A j) (select B j))` outright, or an
/// `ite` whose CONDITION is the same index equality as the escape literal and
/// whose ELSE branch is that base-select equality (the then-branch is
/// shadowed: whenever the condition holds, the escape literal already
/// satisfies the clause). Falsifying the clause forces the stores equal and
/// `i ≠ j`, under which both stores read their own base at `j` —
/// contradiction with the failed select equality. The stored VALUES need not
/// match; the argument never inspects them.
fn validate_store_pair_guarded_row(terms: &TermStore, literals: &[TermId]) -> bool {
    for guard_position in 0..3 {
        let guard_lit = literals[guard_position];
        let (guard_atom, guard_negated) = strip_not(terms, guard_lit);
        if !guard_negated {
            continue;
        }
        let Some((guard_left, guard_right)) = decode_eq(terms, guard_atom) else {
            continue;
        };
        let Some((array_a, index_a, _value_a)) = decode_store(terms, guard_left) else {
            continue;
        };
        let Some((array_b, index_b, _value_b)) = decode_store(terms, guard_right) else {
            continue;
        };
        if index_a != index_b || terms.sort(guard_left) != terms.sort(guard_right) {
            continue;
        }
        let store_index = index_a;
        let mut rest = literals
            .iter()
            .enumerate()
            .filter(|&(position, _)| position != guard_position)
            .map(|(_, &lit)| lit);
        let (other_a, other_b) = (rest.next().unwrap(), rest.next().unwrap());
        for (index_lit, payload) in [(other_a, other_b), (other_b, other_a)] {
            // Escape literal: POSITIVE `(= i j)` naming the probe.
            if matches!(terms.get(index_lit), TermData::Not(_)) {
                continue;
            }
            let Some(probe_index) = eq_other_side(terms, index_lit, store_index) else {
                continue;
            };
            if terms.sort(probe_index) != terms.sort(store_index) {
                continue;
            }
            // Payload: the base-select equality, or an ite over the SAME
            // index equality whose else branch is that equality.
            let select_eq = match terms.get(payload) {
                TermData::Ite(condition, _then_branch, else_branch) => {
                    let same_probe = eq_other_side(terms, *condition, store_index)
                        .is_some_and(|other| other == probe_index);
                    if !same_probe {
                        continue;
                    }
                    *else_branch
                }
                _ => payload,
            };
            let Some((sel_left, sel_right)) = decode_eq(terms, select_eq) else {
                continue;
            };
            let reads = |term: TermId, array: TermId| {
                decode_select(terms, term)
                    .is_some_and(|(read, index)| read == array && index == probe_index)
            };
            let ok = (reads(sel_left, array_a) && reads(sel_right, array_b))
                || (reads(sel_left, array_b) && reads(sel_right, array_a));
            if ok {
                return true;
            }
        }
    }
    false
}

/// The 3-literal guarded read-over-write cases (shapes B and C above).
fn validate_three_literal_guarded_row(terms: &TermStore, literals: &[TermId]) -> bool {
    if validate_store_pair_guarded_row(terms, literals) {
        return true;
    }
    for guard_position in 0..3 {
        let guard_lit = literals[guard_position];
        let (guard_atom, guard_negated) = strip_not(terms, guard_lit);
        if !guard_negated {
            continue;
        }
        let Some((guard_left, guard_right)) = decode_eq(terms, guard_atom) else {
            continue;
        };
        let mut rest = literals
            .iter()
            .enumerate()
            .filter(|&(position, _)| position != guard_position)
            .map(|(_, &lit)| lit);
        let (other_a, other_b) = (rest.next().unwrap(), rest.next().unwrap());
        for (read_array, store_term) in [(guard_left, guard_right), (guard_right, guard_left)] {
            let Some((base_array, store_index, stored_value)) = decode_store(terms, store_term)
            else {
                continue;
            };
            if terms.sort(read_array) != terms.sort(store_term) {
                continue;
            }
            let is_read = |term: TermId, probe: TermId| {
                decode_select(terms, term)
                    .is_some_and(|(array, index)| array == read_array && index == probe)
            };
            let is_base_read = |term: TermId, probe: TermId| {
                decode_select(terms, term)
                    .is_some_and(|(array, index)| array == base_array && index == probe)
            };
            for (index_lit, select_lit) in [(other_a, other_b), (other_b, other_a)] {
                let (index_atom, index_negated) = strip_not(terms, index_lit);
                let Some(probe_index) = eq_other_side(terms, index_atom, store_index) else {
                    continue;
                };
                if terms.sort(probe_index) != terms.sort(store_index) {
                    continue;
                }
                let Some((sel_left, sel_right)) = decode_eq(terms, select_lit) else {
                    continue;
                };
                if index_negated {
                    // Shape C: `¬(= i j)` + `(= v (select E j))`.
                    let ok = (sel_left == stored_value && is_read(sel_right, probe_index))
                        || (sel_right == stored_value && is_read(sel_left, probe_index));
                    if ok {
                        return true;
                    }
                } else {
                    // Shape B: `(= i j)` + `(= (select A j) (select E j))`.
                    let ok = (is_base_read(sel_left, probe_index)
                        && is_read(sel_right, probe_index))
                        || (is_base_read(sel_right, probe_index) && is_read(sel_left, probe_index));
                    if ok {
                        return true;
                    }
                }
            }
        }
    }
    false
}

/// Declaration-free recognizer: `true` exactly when
/// [`validate_array_guarded_row_expansion`] accepts the clause.
#[must_use]
pub fn recognize_array_guarded_row_expansion(terms: &TermStore, clause: &[TermId]) -> bool {
    validate_array_guarded_row_expansion(terms, ProofId(0), clause).is_ok()
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;

    const BV64: Sort = Sort::BitVec(ay_core::BitVecSort { width: 64 });
    const BV8: Sort = Sort::BitVec(ay_core::BitVecSort { width: 8 });

    pub(crate) fn array_sort_for_tests() -> Sort {
        array_sort()
    }

    pub(crate) fn eq_for_tests(terms: &mut TermStore, left: TermId, right: TermId) -> TermId {
        eq(terms, left, right)
    }

    fn array_sort() -> Sort {
        Sort::Array(Box::new(ay_core::ArraySort {
            index_sort: BV64,
            element_sort: BV8,
        }))
    }

    fn setup() -> (TermStore, TermId, TermId, TermId, TermId, TermId) {
        let mut terms = TermStore::new();
        let e = terms.mk_var("e", array_sort());
        let a = terms.mk_var("a", array_sort());
        let idx = terms.mk_var("idx", BV64);
        let zero = terms.mk_bitvec(0u32.into(), 64);
        let one = terms.mk_bitvec(1u32.into(), 8);
        (terms, e, a, idx, zero, one)
    }

    fn eq(terms: &mut TermStore, left: TermId, right: TermId) -> TermId {
        terms.mk_app(Symbol::named("="), vec![left, right], Sort::Bool)
    }

    #[test]
    fn accepts_else_branch_projection_packed() {
        // `(or (= 0 idx) (= (ite (= 0 idx) 1 (select e idx)) (select e idx)))`
        let (mut terms, e, _a, idx, zero, one) = setup();
        let cond = eq(&mut terms, zero, idx);
        let sel = terms.mk_app(Symbol::named("select"), vec![e, idx], BV8);
        let ite = terms.mk_ite_raw(cond, one, sel);
        let ite_eq = eq(&mut terms, ite, sel);
        let unit = terms.mk_app(Symbol::named("or"), vec![cond, ite_eq], Sort::Bool);
        assert!(recognize_ite_branch_projection(&terms, &[unit]));
    }

    #[test]
    fn accepts_then_branch_projection_two_literals() {
        // `(cl (not C) (= a (ite C a b)))`
        let (mut terms, e, _a, idx, zero, one) = setup();
        let cond = eq(&mut terms, zero, idx);
        let not_cond = terms.mk_not(cond);
        let sel = terms.mk_app(Symbol::named("select"), vec![e, idx], BV8);
        let ite = terms.mk_ite_raw(cond, one, sel);
        let ite_eq = eq(&mut terms, one, ite);
        assert!(recognize_ite_branch_projection(&terms, &[not_cond, ite_eq]));
    }

    #[test]
    fn rejects_wrong_branch_projection() {
        // `C ∨ ite = a` picks the THEN branch under ¬C — falsifiable.
        let (mut terms, e, _a, idx, zero, one) = setup();
        let cond = eq(&mut terms, zero, idx);
        let sel = terms.mk_app(Symbol::named("select"), vec![e, idx], BV8);
        let ite = terms.mk_ite_raw(cond, one, sel);
        let ite_eq = eq(&mut terms, ite, one);
        assert!(!recognize_ite_branch_projection(&terms, &[cond, ite_eq]));
    }

    #[test]
    fn accepts_guarded_row_expansion() {
        // `(or (ite (= 0 idx) (= 1 (select e idx)) (= (select a idx) (select e idx)))
        //      (not (= e (store a 0 1))))`
        let (mut terms, e, a, idx, zero, one) = setup();
        let store = terms.mk_app(Symbol::named("store"), vec![a, zero, one], array_sort());
        let guard = eq(&mut terms, e, store);
        let not_guard = terms.mk_not(guard);
        let cond = eq(&mut terms, zero, idx);
        let sel_e = terms.mk_app(Symbol::named("select"), vec![e, idx], BV8);
        let sel_a = terms.mk_app(Symbol::named("select"), vec![a, idx], BV8);
        let then_eq = eq(&mut terms, one, sel_e);
        let else_eq = eq(&mut terms, sel_a, sel_e);
        let formula = terms.mk_ite_raw(cond, then_eq, else_eq);
        let unit = terms.mk_app(Symbol::named("or"), vec![formula, not_guard], Sort::Bool);
        assert!(recognize_array_guarded_row_expansion(&terms, &[unit]));
    }

    #[test]
    fn rejects_row_expansion_with_wrong_stored_value() {
        let (mut terms, e, a, idx, zero, one) = setup();
        let two = terms.mk_bitvec(2u32.into(), 8);
        let store = terms.mk_app(Symbol::named("store"), vec![a, zero, two], array_sort());
        let guard = eq(&mut terms, e, store);
        let not_guard = terms.mk_not(guard);
        let cond = eq(&mut terms, zero, idx);
        let sel_e = terms.mk_app(Symbol::named("select"), vec![e, idx], BV8);
        let sel_a = terms.mk_app(Symbol::named("select"), vec![a, idx], BV8);
        // then-branch claims value ONE was stored, but the store wrote TWO.
        let then_eq = eq(&mut terms, one, sel_e);
        let else_eq = eq(&mut terms, sel_a, sel_e);
        let formula = terms.mk_ite_raw(cond, then_eq, else_eq);
        assert!(!recognize_array_guarded_row_expansion(
            &terms,
            &[formula, not_guard]
        ));
    }

    #[test]
    fn rejects_row_expansion_with_positive_guard() {
        // A POSITIVE store equality cannot license the expansion.
        let (mut terms, e, a, idx, zero, one) = setup();
        let store = terms.mk_app(Symbol::named("store"), vec![a, zero, one], array_sort());
        let guard = eq(&mut terms, e, store);
        let cond = eq(&mut terms, zero, idx);
        let sel_e = terms.mk_app(Symbol::named("select"), vec![e, idx], BV8);
        let sel_a = terms.mk_app(Symbol::named("select"), vec![a, idx], BV8);
        let then_eq = eq(&mut terms, one, sel_e);
        let else_eq = eq(&mut terms, sel_a, sel_e);
        let formula = terms.mk_ite_raw(cond, then_eq, else_eq);
        assert!(!recognize_array_guarded_row_expansion(
            &terms,
            &[formula, guard]
        ));
    }
}

#[cfg(test)]
mod three_literal_guarded_row_tests {
    use super::*;
    use crate::checker::ite_branch::tests::{array_sort_for_tests, eq_for_tests};

    #[test]
    fn accepts_row_neg_shape() {
        // `(or (not (= a (store e 0 1))) (= 0 d) (= (select e d) (select a d)))`
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", array_sort_for_tests());
        let e = terms.mk_var("e", array_sort_for_tests());
        let d = terms.mk_var("d", Sort::BitVec(ay_core::BitVecSort { width: 64 }));
        let zero = terms.mk_bitvec(0u32.into(), 64);
        let one = terms.mk_bitvec(1u32.into(), 8);
        let bv8 = Sort::BitVec(ay_core::BitVecSort { width: 8 });
        let store = terms.mk_app(
            Symbol::named("store"),
            vec![e, zero, one],
            array_sort_for_tests(),
        );
        let guard = eq_for_tests(&mut terms, a, store);
        let not_guard = terms.mk_not(guard);
        let index_eq = eq_for_tests(&mut terms, zero, d);
        let sel_e = terms.mk_app(Symbol::named("select"), vec![e, d], bv8.clone());
        let sel_a = terms.mk_app(Symbol::named("select"), vec![a, d], bv8);
        let select_eq = eq_for_tests(&mut terms, sel_e, sel_a);
        let unit = terms.mk_app(
            Symbol::named("or"),
            vec![not_guard, index_eq, select_eq],
            Sort::Bool,
        );
        assert!(recognize_array_guarded_row_expansion(&terms, &[unit]));
    }

    #[test]
    fn accepts_row_pos_shape() {
        // `(cl (not (= a (store e 0 1))) (not (= 0 d)) (= 1 (select a d)))`
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", array_sort_for_tests());
        let e = terms.mk_var("e", array_sort_for_tests());
        let d = terms.mk_var("d", Sort::BitVec(ay_core::BitVecSort { width: 64 }));
        let zero = terms.mk_bitvec(0u32.into(), 64);
        let one = terms.mk_bitvec(1u32.into(), 8);
        let bv8 = Sort::BitVec(ay_core::BitVecSort { width: 8 });
        let store = terms.mk_app(
            Symbol::named("store"),
            vec![e, zero, one],
            array_sort_for_tests(),
        );
        let guard = eq_for_tests(&mut terms, a, store);
        let not_guard = terms.mk_not(guard);
        let index_eq = eq_for_tests(&mut terms, zero, d);
        let not_index_eq = terms.mk_not(index_eq);
        let sel_a = terms.mk_app(Symbol::named("select"), vec![a, d], bv8);
        let select_eq = eq_for_tests(&mut terms, one, sel_a);
        assert!(recognize_array_guarded_row_expansion(
            &terms,
            &[not_guard, not_index_eq, select_eq]
        ));
    }

    #[test]
    fn rejects_row_neg_reading_untouched_cell_from_wrong_array() {
        // else-equality over TWO base reads (never the read array) is not the
        // expansion — falsifiable, must reject.
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", array_sort_for_tests());
        let e = terms.mk_var("e", array_sort_for_tests());
        let d = terms.mk_var("d", Sort::BitVec(ay_core::BitVecSort { width: 64 }));
        let zero = terms.mk_bitvec(0u32.into(), 64);
        let one = terms.mk_bitvec(1u32.into(), 8);
        let bv8 = Sort::BitVec(ay_core::BitVecSort { width: 8 });
        let store = terms.mk_app(
            Symbol::named("store"),
            vec![e, zero, one],
            array_sort_for_tests(),
        );
        let guard = eq_for_tests(&mut terms, a, store);
        let not_guard = terms.mk_not(guard);
        let index_eq = eq_for_tests(&mut terms, zero, d);
        let sel_e = terms.mk_app(Symbol::named("select"), vec![e, d], bv8);
        let select_eq = eq_for_tests(&mut terms, sel_e, sel_e);
        assert!(!recognize_array_guarded_row_expansion(
            &terms,
            &[not_guard, index_eq, select_eq]
        ));
    }
}

#[cfg(test)]
mod store_pair_guarded_row_tests {
    use super::*;
    use crate::checker::ite_branch::tests::{array_sort_for_tests, eq_for_tests};

    fn common(terms: &mut TermStore) -> (TermId, TermId, TermId, TermId, TermId, TermId, TermId) {
        let e = terms.mk_var("e", array_sort_for_tests());
        let a = terms.mk_var("a", array_sort_for_tests());
        let d = terms.mk_var("d", Sort::BitVec(ay_core::BitVecSort { width: 64 }));
        let zero = terms.mk_bitvec(0u32.into(), 64);
        let one = terms.mk_bitvec(1u32.into(), 8);
        let store_e = terms.mk_app(
            Symbol::named("store"),
            vec![e, zero, one],
            array_sort_for_tests(),
        );
        let store_a = terms.mk_app(
            Symbol::named("store"),
            vec![a, zero, one],
            array_sort_for_tests(),
        );
        (e, a, d, zero, one, store_e, store_a)
    }

    #[test]
    fn accepts_store_pair_with_shadowed_ite_payload() {
        // The clause 59 shape: `(or (not (= (store e 0 1) (store a 0 1)))
        //   (ite (= 0 d) (= 1 (select e d)) (= (select e d) (select a d)))
        //   (= 0 d))`
        let mut terms = TermStore::new();
        let (e, a, d, zero, one, store_e, store_a) = common(&mut terms);
        let bv8 = Sort::BitVec(ay_core::BitVecSort { width: 8 });
        let guard = eq_for_tests(&mut terms, store_e, store_a);
        let not_guard = terms.mk_not(guard);
        let cond = eq_for_tests(&mut terms, zero, d);
        let sel_e = terms.mk_app(Symbol::named("select"), vec![e, d], bv8.clone());
        let sel_a = terms.mk_app(Symbol::named("select"), vec![a, d], bv8);
        let then_eq = eq_for_tests(&mut terms, one, sel_e);
        let else_eq = eq_for_tests(&mut terms, sel_e, sel_a);
        let payload = terms.mk_ite_raw(cond, then_eq, else_eq);
        let unit = terms.mk_app(
            Symbol::named("or"),
            vec![not_guard, payload, cond],
            Sort::Bool,
        );
        assert!(recognize_array_guarded_row_expansion(&terms, &[unit]));
    }

    #[test]
    fn rejects_store_pair_at_different_indices() {
        // Stores at DIFFERENT indices do not entail base equality at j != i.
        let mut terms = TermStore::new();
        let (e, a, d, zero, one, store_e, _) = common(&mut terms);
        let bv8 = Sort::BitVec(ay_core::BitVecSort { width: 8 });
        let five = terms.mk_bitvec(5u32.into(), 64);
        let store_a5 = terms.mk_app(
            Symbol::named("store"),
            vec![a, five, one],
            array_sort_for_tests(),
        );
        let guard = eq_for_tests(&mut terms, store_e, store_a5);
        let not_guard = terms.mk_not(guard);
        let cond = eq_for_tests(&mut terms, zero, d);
        let sel_e = terms.mk_app(Symbol::named("select"), vec![e, d], bv8.clone());
        let sel_a = terms.mk_app(Symbol::named("select"), vec![a, d], bv8);
        let else_eq = eq_for_tests(&mut terms, sel_e, sel_a);
        assert!(!recognize_array_guarded_row_expansion(
            &terms,
            &[not_guard, cond, else_eq]
        ));
    }

    #[test]
    fn rejects_ite_payload_over_a_different_condition() {
        // The ite condition must BE the escape literal's index equality;
        // otherwise the then-branch is not shadowed and the else projection
        // is unsound.
        let mut terms = TermStore::new();
        let (e, a, d, zero, one, store_e, store_a) = common(&mut terms);
        let bv8 = Sort::BitVec(ay_core::BitVecSort { width: 8 });
        let five = terms.mk_bitvec(5u32.into(), 64);
        let guard = eq_for_tests(&mut terms, store_e, store_a);
        let not_guard = terms.mk_not(guard);
        let escape = eq_for_tests(&mut terms, zero, d);
        let other_cond = eq_for_tests(&mut terms, five, d);
        let sel_e = terms.mk_app(Symbol::named("select"), vec![e, d], bv8.clone());
        let sel_a = terms.mk_app(Symbol::named("select"), vec![a, d], bv8);
        let then_eq = eq_for_tests(&mut terms, one, sel_e);
        let else_eq = eq_for_tests(&mut terms, sel_e, sel_a);
        let payload = terms.mk_ite_raw(other_cond, then_eq, else_eq);
        assert!(!recognize_array_guarded_row_expansion(
            &terms,
            &[not_guard, payload, escape]
        ));
    }
}
