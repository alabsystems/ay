// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Child of installed_row2: the same real combined solver has an intentionally
//! provisional BCP result and a contradictory full consistency check. This is
//! prepared source only, not an observed native query result.

use super::*;
use crate::combined_solvers::combiner::TheoryCombiner;
use crate::executor::theories::split_incremental::recheck_installed_theory_lemmas_with;
use ay_core::Symbol;

#[test]
fn installed_row2_recheck_uses_bcp_operation_without_consuming_the_mandatory_full_check() {
    let mut fixture = rows(1);
    // The real UFLIA interface-bridge discriminator already maintained in
    // combined_solvers/tests.rs: x=2, f(3)=10, f(x+1)!=10. BCP intentionally
    // defers the arithmetic-to-EUF contradiction; the final check must find it.
    let x = fixture.terms.mk_fresh_var("phase_x", Sort::Int);
    let one = fixture.terms.mk_int(BigInt::from(1));
    let two = fixture.terms.mk_int(BigInt::from(2));
    let three = fixture.terms.mk_int(BigInt::from(3));
    let ten = fixture.terms.mk_int(BigInt::from(10));
    let x_plus_one = fixture
        .terms
        .mk_app(Symbol::named("+"), vec![x, one], Sort::Int);
    let f_x_plus_one = fixture
        .terms
        .mk_app(Symbol::named("phase_f"), vec![x_plus_one], Sort::Int);
    let f_three = fixture
        .terms
        .mk_app(Symbol::named("phase_f"), vec![three], Sort::Int);
    let x_eq_two = fixture.terms.mk_eq(x, two);
    let f_three_eq_ten = fixture.terms.mk_eq(f_three, ten);
    let f_x_plus_one_eq_ten = fixture.terms.mk_eq(f_x_plus_one, ten);
    let negations = IncrementalNegationCache::seed(&mut fixture.terms, [], false);
    let mut installed = Installed::new(&fixture.terms, negations);
    installed.sat.push();
    installed.install(&fixture.clauses[0]);
    let ledger = vec![TheoryLemma::new(fixture.clauses[0].clone())];

    let mut theory = TheoryCombiner::auf_lia(&fixture.terms);
    for lit in &fixture.clauses[0] {
        theory.register_atom(lit.term);
    }
    for atom in [x_eq_two, f_three_eq_ten, f_x_plus_one_eq_ten] {
        theory.register_atom(atom);
    }
    theory.assert_literal(x_eq_two, true);
    theory.assert_literal(f_three_eq_ten, true);
    theory.assert_literal(f_x_plus_one_eq_ten, false);
    theory.set_search_phase(true);
    assert!(theory.needs_final_check_after_sat());
    let initial = theory.check_during_propagate();
    let TheoryResult::NeedLemmas(requested) = &initial else {
        panic!("the real BCP array lane must first derive the installed row: {initial:?}");
    };
    assert_ne!(requested.as_slice(), []);
    assert!(requested.iter().all(|lemma| installed.owns(&lemma.clause)));
    let original_max = installed.sat.issued_original_clause_id_max();
    let clause_count = installed.sat.num_clauses();
    let calls = std::cell::Cell::new(0usize);
    let provisional =
        recheck_installed_theory_lemmas_with(&mut theory, initial, &ledger, &|| false, |same| {
            calls.set(calls.get() + 1);
            same.check_during_propagate()
        });
    assert!(
        calls.get() > 0,
        "the actual phase callback must run, not a duplicate-to-Sat shortcut"
    );
    assert!(
        matches!(provisional, TheoryResult::Sat),
        "BCP replay must not silently invoke the stronger full check: {provisional:?}"
    );
    assert!(
        theory.needs_final_check_after_sat(),
        "provisional Sat has no final-consistency authority"
    );
    assert_eq!(installed.sat.issued_original_clause_id_max(), original_max);
    assert_eq!(installed.sat.num_clauses(), clause_count);

    theory.set_search_phase(false);
    let definitive = theory.check();
    assert!(matches!(definitive, TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)),
        "the same live solver must retain the real interface conflict for the mandatory full check: {definitive:?}");
}
