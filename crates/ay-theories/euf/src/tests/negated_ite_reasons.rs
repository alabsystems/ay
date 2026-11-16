// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! ITE explanations name the SAT-owned guard atom with its actual polarity.

use super::*;

#[test]
fn negated_ite_reasons_preserve_guard_polarity_and_incremental_scope() {
    for assigned in [false, true] {
        let mut terms = TermStore::new();
        let p = terms.mk_var("p", Sort::Bool);
        let not_p = terms.mk_not_raw(p);
        let sort = Sort::Uninterpreted("U".into());
        let a = terms.mk_var("a", sort.clone());
        let b = terms.mk_var("b", sort);
        let choice = terms.mk_ite_raw(not_p, a, b);
        let selected = if assigned { b } else { a };
        let other = if assigned { a } else { b };
        let target = terms.mk_app(Symbol::named("="), [choice, selected], Sort::Bool);
        let wrong = terms.mk_app(Symbol::named("="), [choice, other], Sort::Bool);
        let mut euf = new_incremental_euf(&terms);
        euf.register_atom(target);
        euf.register_atom(wrong);
        euf.push();
        euf.assert_literal(p, assigned);
        assert!(matches!(euf.check(), TheoryResult::Sat));
        assert_eq!(
            euf.explain(choice, selected),
            vec![TheoryLit::new(p, assigned)]
        );
        let propagations = euf.propagate();
        assert!(propagations.iter().any(|propagation| {
            propagation.literal == TheoryLit::new(target, true)
                && propagation.reason == vec![TheoryLit::new(p, assigned)]
        }));
        assert!(!propagations
            .iter()
            .any(|propagation| { propagation.literal == TheoryLit::new(wrong, true) }));
        assert!(euf.pending_propagations.iter().all(|(_, _, reason)| {
            reason
                .iter()
                .all(|literal| literal.term == p && literal.value == assigned)
        }));
        euf.pop();
        assert!(matches!(euf.check(), TheoryResult::Sat));
        assert_eq!(euf.explain(choice, selected), Vec::<TheoryLit>::new());
    }
}
