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

    /// `(E, store-over-const-array, probe j, fill 0, stored v)` as RAW terms —
    /// deliberately built with `mk_app`, never `mk_select`, so the fold the
    /// producer performs is spelled explicitly and not re-performed here.
    fn const_array_base_setup() -> (TermStore, TermId, TermId, TermId, TermId, TermId, TermId) {
        let int_array = Sort::Array(Box::new(ay_core::ArraySort {
            index_sort: Sort::Int,
            element_sort: Sort::Int,
        }));
        let mut terms = TermStore::new();
        let e = terms.mk_var("e", int_array.clone());
        let j = terms.mk_var("j", Sort::Int);
        let v = terms.mk_var("v", Sort::Int);
        let zero = terms.mk_int(0.into());
        let base = terms.mk_const_array(Sort::Int, zero);
        let store = terms.mk_app(Symbol::named("store"), vec![base, zero, v], int_array);
        let guard = eq_for_tests(&mut terms, e, store);
        let not_guard = terms.mk_not(guard);
        let cond = eq_for_tests(&mut terms, zero, j);
        let sel_e = terms.mk_app(Symbol::named("select"), vec![e, j], Sort::Int);
        (terms, not_guard, cond, sel_e, zero, v, j)
    }

    #[test]
    fn accepts_const_array_base_fill_in_else_branch() {
        // `(cl (not (= E (store ((as const ..) 0) 0 v)))
        //      (ite (= 0 j) (= v (select E j)) (= 0 (select E j))))`
        // The else branch names the FILL because `mk_select` folded
        // `(select ((as const ..) 0) j)` to `0`.
        let (mut terms, not_guard, cond, sel_e, zero, v, _j) = const_array_base_setup();
        let then_eq = eq_for_tests(&mut terms, v, sel_e);
        let else_eq = eq_for_tests(&mut terms, zero, sel_e);
        let formula = terms.mk_ite_raw(cond, then_eq, else_eq);
        assert!(recognize_array_guarded_row_expansion(
            &terms,
            &[not_guard, formula]
        ));
    }

    #[test]
    fn refuses_const_array_base_with_branches_swapped() {
        // Fill and stored value EXCHANGED. NOT a tautology: with j = 0 and
        // v = 1, `E = store(const-array(0), 0, 1)` so `(select E 0) = 1`, the
        // condition `0 = j` holds, and the then-branch `(= 0 1)` is FALSE.
        // This is precisely the confusion the new disjunct could introduce,
        // since fill and stored value are now both bare element-sorted terms.
        let (mut terms, not_guard, cond, sel_e, zero, v, _j) = const_array_base_setup();
        let then_eq = eq_for_tests(&mut terms, zero, sel_e);
        let else_eq = eq_for_tests(&mut terms, v, sel_e);
        let formula = terms.mk_ite_raw(cond, then_eq, else_eq);
        assert!(!recognize_array_guarded_row_expansion(
            &terms,
            &[not_guard, formula]
        ));
    }

    #[test]
    fn refuses_const_array_base_with_wrong_fill() {
        // Else branch names a constant that is NOT this const-array's fill.
        // NOT a tautology: with j = 1, `(select E 1) = 0`, so `(= 7 0)` is
        // FALSE. Pins that the accepted fill is anchored to the clause's own
        // `base_array`, never to an arbitrary constant of the right sort.
        let (mut terms, not_guard, cond, sel_e, _zero, v, _j) = const_array_base_setup();
        let seven = terms.mk_int(7.into());
        let then_eq = eq_for_tests(&mut terms, v, sel_e);
        let else_eq = eq_for_tests(&mut terms, seven, sel_e);
        let formula = terms.mk_ite_raw(cond, then_eq, else_eq);
        assert!(!recognize_array_guarded_row_expansion(
            &terms,
            &[not_guard, formula]
        ));
    }

    #[test]
    fn refuses_const_array_fill_from_an_unrelated_array() {
        // The store's base is a PLAIN array; the else branch names the fill of
        // a DIFFERENT const-array in the same store. NOT a tautology, and the
        // new disjunct must not reach past `base_array` to find it.
        let int_array = Sort::Array(Box::new(ay_core::ArraySort {
            index_sort: Sort::Int,
            element_sort: Sort::Int,
        }));
        let mut terms = TermStore::new();
        let e = terms.mk_var("e", int_array.clone());
        let a = terms.mk_var("a", int_array.clone());
        let j = terms.mk_var("j", Sort::Int);
        let v = terms.mk_var("v", Sort::Int);
        let zero = terms.mk_int(0.into());
        let _unrelated = terms.mk_const_array(Sort::Int, zero);
        let store = terms.mk_app(Symbol::named("store"), vec![a, zero, v], int_array);
        let guard = eq_for_tests(&mut terms, e, store);
        let not_guard = terms.mk_not(guard);
        let cond = eq_for_tests(&mut terms, zero, j);
        let sel_e = terms.mk_app(Symbol::named("select"), vec![e, j], Sort::Int);
        let then_eq = eq_for_tests(&mut terms, v, sel_e);
        let else_eq = eq_for_tests(&mut terms, zero, sel_e);
        let formula = terms.mk_ite_raw(cond, then_eq, else_eq);
        assert!(!recognize_array_guarded_row_expansion(
            &terms,
            &[not_guard, formula]
        ));
    }

    #[test]
    fn refuses_three_literal_const_array_base_with_wrong_fill() {
        // Shape B (clausified) with a wrong fill: `(cl (not (= E (store
        // ((as const ..) 0) 0 v))) (= 0 j) (= 7 (select E j)))`. Falsified at
        // j = 1: `(select E 1) = 0 != 7`.
        let (mut terms, not_guard, cond, sel_e, _zero, _v, _j) = const_array_base_setup();
        let seven = terms.mk_int(7.into());
        let select_eq = eq_for_tests(&mut terms, seven, sel_e);
        assert!(!recognize_array_guarded_row_expansion(
            &terms,
            &[not_guard, cond, select_eq]
        ));
    }

    #[test]
    fn accepts_three_literal_const_array_base_fill() {
        // Shape B (clausified) positive control: `(cl (not (= E (store
        // ((as const ..) 0) 0 v))) (= 0 j) (= 0 (select E j)))`.
        let (mut terms, not_guard, cond, sel_e, zero, _v, _j) = const_array_base_setup();
        let select_eq = eq_for_tests(&mut terms, zero, sel_e);
        assert!(recognize_array_guarded_row_expansion(
            &terms,
            &[not_guard, cond, select_eq]
        ));
    }
}
