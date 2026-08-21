// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

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
