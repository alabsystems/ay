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
