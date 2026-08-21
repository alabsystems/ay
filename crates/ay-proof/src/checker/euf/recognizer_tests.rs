// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[cfg(test)]
mod euf_recognizer_tests {
    use ay_core::{Sort, Symbol, TermStore};

    /// The C3 recognizers ARE the validators: the canonical order is accepted
    /// and — because the EUF validators are ORDER-SENSITIVE — the same literal
    /// set with the conclusion moved off its mandated position is rejected.
    #[test]
    fn euf_recognizers_are_order_sensitive_validators() {
        let mut terms = TermStore::new();
        let u = Sort::Uninterpreted("U".to_string());
        let a = terms.mk_var("a", u.clone());
        let b = terms.mk_var("b", u.clone());
        let c = terms.mk_var("c", u.clone());
        let eq_ab = terms.mk_eq(a, b);
        let eq_bc = terms.mk_eq(b, c);
        let eq_ac = terms.mk_eq(a, c);
        let not_ab = terms.mk_not(eq_ab);
        let not_bc = terms.mk_not(eq_bc);

        // eq_transitive: premises-then-conclusion accepted, conclusion-first
        // rejected.
        assert!(super::recognize_euf_transitive(
            &terms,
            &[not_ab, not_bc, eq_ac]
        ));
        assert!(!super::recognize_euf_transitive(
            &terms,
            &[eq_ac, not_ab, not_bc]
        ));

        // eq_congruent: (not (= a b)) (= (f a) (f b)) accepted; swapped order
        // rejected.
        let f_a = terms.mk_app(Symbol::named("f"), [a], u.clone());
        let f_b = terms.mk_app(Symbol::named("f"), [b], u.clone());
        let eq_fafb = terms.mk_eq(f_a, f_b);
        assert!(super::recognize_euf_congruent(&terms, &[not_ab, eq_fafb]));
        assert!(!super::recognize_euf_congruent(&terms, &[eq_fafb, not_ab]));

        // eq_congruent_pred: (not (= a b)) (not (p a)) (p b) accepted;
        // predicate literals swapped rejected.
        let p_a = terms.mk_app(Symbol::named("p"), [a], Sort::Bool);
        let p_b = terms.mk_app(Symbol::named("p"), [b], Sort::Bool);
        let not_p_a = terms.mk_not(p_a);
        assert!(super::recognize_euf_congruent_pred(
            &terms,
            &[not_ab, not_p_a, p_b]
        ));
        assert!(!super::recognize_euf_congruent_pred(
            &terms,
            &[not_ab, p_b, not_p_a]
        ));

        // eq_reflexive: unit `(= a a)` (built raw — `mk_eq` folds it to
        // `true`) accepted; a two-literal clause rejected.
        let raw_eq_aa = terms.mk_app(Symbol::named("="), [a, a], Sort::Bool);
        assert!(super::recognize_euf_reflexive(&terms, &[raw_eq_aa]));
        assert!(!super::recognize_euf_reflexive(
            &terms,
            &[not_ab, raw_eq_aa]
        ));
    }
}

#[cfg(test)]
mod congruent_identical_argument_tests {
    use super::*;
    use ay_core::{ArraySort, BitVecSort, Sort};

    #[test]
    fn accepts_congruence_with_shared_argument_omitted() {
        // `(or (not (= a e)) (= (select a d) (select e d)))` — the array
        // extensionality-instance shape; position 1 (the index) is shared.
        let mut terms = TermStore::new();
        let array_sort = Sort::Array(Box::new(ArraySort {
            index_sort: Sort::BitVec(BitVecSort { width: 64 }),
            element_sort: Sort::BitVec(BitVecSort { width: 8 }),
        }));
        let a = terms.mk_var("a", array_sort.clone());
        let e = terms.mk_var("e", array_sort);
        let d = terms.mk_var("d", Sort::BitVec(BitVecSort { width: 64 }));
        let bv8 = Sort::BitVec(BitVecSort { width: 8 });
        let sel_a = terms.mk_app(Symbol::named("select"), vec![a, d], bv8.clone());
        let sel_e = terms.mk_app(Symbol::named("select"), vec![e, d], bv8);
        let arrays_eq = terms.mk_app(Symbol::named("="), vec![a, e], Sort::Bool);
        let not_arrays_eq = terms.mk_not(arrays_eq);
        let selects_eq = terms.mk_app(Symbol::named("="), vec![sel_a, sel_e], Sort::Bool);
        let packed = terms.mk_app(
            Symbol::named("or"),
            vec![not_arrays_eq, selects_eq],
            Sort::Bool,
        );
        assert!(recognize_euf_congruent(&terms, &[packed]));
        assert!(recognize_euf_congruent(
            &terms,
            &[not_arrays_eq, selects_eq]
        ));
    }

    #[test]
    fn rejects_congruence_whose_differing_position_has_no_premise() {
        // `(= (select a d1) (select e d2))` with d1 != d2 and only the array
        // premise — falsifiable, must stay rejected.
        let mut terms = TermStore::new();
        let array_sort = Sort::Array(Box::new(ArraySort {
            index_sort: Sort::Int,
            element_sort: Sort::Int,
        }));
        let a = terms.mk_var("a", array_sort.clone());
        let e = terms.mk_var("e", array_sort);
        let d1 = terms.mk_var("d1", Sort::Int);
        let d2 = terms.mk_var("d2", Sort::Int);
        let sel_a = terms.mk_app(Symbol::named("select"), vec![a, d1], Sort::Int);
        let sel_e = terms.mk_app(Symbol::named("select"), vec![e, d2], Sort::Int);
        let arrays_eq = terms.mk_app(Symbol::named("="), vec![a, e], Sort::Bool);
        let not_arrays_eq = terms.mk_not(arrays_eq);
        let selects_eq = terms.mk_app(Symbol::named("="), vec![sel_a, sel_e], Sort::Bool);
        assert!(!recognize_euf_congruent(
            &terms,
            &[not_arrays_eq, selects_eq]
        ));
    }
}
