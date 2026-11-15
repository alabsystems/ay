// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! D2 (2026-09-23 hunt): the Diophantine caches are keyed on the equality set
//! AND the bounds folded into them (`dioph_cache.rs`).
//!
//! `21x + 13y + 5z = 117, 18 <= z <= 20` is satisfiable (`x = -7, y = 13,
//! z = 19`). With `x` pinned to 3 by a pair of bound atoms, the fold leaves
//! `13y + 5z = 54`, whose solutions have `z ≡ 3 (mod 13)` — none in
//! `[18, 20]`, a correct refutation of THAT scope. Once the pin is popped the
//! equality set is unchanged, and a modulus kept from the folded system turns
//! the satisfiable base into `unsat`.

use super::*;
use num_bigint::BigInt;

struct Fixture {
    terms: TermStore,
    eq: TermId,
    z_ge: TermId,
    z_le: TermId,
    x_ge: TermId,
    x_le: TermId,
    z: TermId,
}

fn fixture() -> Fixture {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let c21 = terms.mk_int(BigInt::from(21));
    let c13 = terms.mk_int(BigInt::from(13));
    let c5 = terms.mk_int(BigInt::from(5));
    let t21x = terms.mk_mul(vec![c21, x]);
    let t13y = terms.mk_mul(vec![c13, y]);
    let t5z = terms.mk_mul(vec![c5, z]);
    let sum = terms.mk_add(vec![t21x, t13y, t5z]);
    let c117 = terms.mk_int(BigInt::from(117));
    let eq = terms.mk_eq(sum, c117);
    let c18 = terms.mk_int(BigInt::from(18));
    let c20 = terms.mk_int(BigInt::from(20));
    let c3 = terms.mk_int(BigInt::from(3));
    let z_ge = terms.mk_ge(z, c18);
    let z_le = terms.mk_le(z, c20);
    let x_ge = terms.mk_ge(x, c3);
    let x_le = terms.mk_le(x, c3);
    Fixture {
        terms,
        eq,
        z_ge,
        z_le,
        x_ge,
        x_le,
        z,
    }
}

fn is_unsat(result: &TheoryResult) -> bool {
    matches!(
        result,
        TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
    )
}

/// Assert the base, then pin `x = 3` in a scope and check there, so the
/// Diophantine caches are built from the folded system.
fn solve_pinned_scope(solver: &mut LiaSolver<'_>, f: &Fixture) {
    solver.assert_literal(f.eq, true);
    solver.assert_literal(f.z_ge, true);
    solver.assert_literal(f.z_le, true);
    solver.push();
    solver.assert_literal(f.x_ge, true);
    solver.assert_literal(f.x_le, true);
    let pinned = solver.check();
    assert!(
        is_unsat(&pinned),
        "x = 3 leaves 13y + 5z = 54, infeasible for z in [18, 20]; got {pinned:?}"
    );
    // The first check solved the equalities before the simplex had seen x's
    // bounds. Re-run the analysis with them in force, as the periodic
    // BCP-time re-check (65c1831dc3) does mid-search: this solve folds x.
    let _ = solver.try_diophantine_solve();
    assert!(
        !solver.dioph_cached_fold_reasons.is_empty(),
        "the pinned check must fold x and record the fold's reasons"
    );
    assert!(
        solver
            .dioph_cached_modular_gcds
            .iter()
            .any(|(t, g, r)| *t == f.z && *g == BigInt::from(13) && *r == BigInt::from(3)),
        "the folded system yields z ≡ 3 (mod 13); got {:?}",
        solver.dioph_cached_modular_gcds
    );
}

#[test]
fn d2_folded_modulus_does_not_survive_the_pop_of_its_pin() {
    let f = fixture();
    let mut solver = LiaSolver::new(&f.terms);
    solve_pinned_scope(&mut solver, &f);
    solver.pop();
    let result = solver.check();
    assert!(
        !is_unsat(&result),
        "21x + 13y + 5z = 117 with z in [18, 20] is satisfiable (x=-7, y=13, z=19); got {result:?}"
    );
    assert!(
        !solver
            .dioph_cached_modular_gcds
            .iter()
            .any(|(t, g, _)| *t == f.z && *g == BigInt::from(13)),
        "the folded modulus must be gone after its pin was popped"
    );
}

#[test]
fn d2_folded_modulus_does_not_survive_the_pop_at_bcp_time() {
    let f = fixture();
    let mut solver = LiaSolver::new(&f.terms);
    solve_pinned_scope(&mut solver, &f);
    solver.pop();
    let result = solver.check_during_propagate();
    assert!(
        !is_unsat(&result),
        "BCP-time check after the pop must not reuse the folded modulus; got {result:?}"
    );
}

#[test]
fn d2_caches_survive_a_pop_that_keeps_their_fold() {
    // Capability: a pop that leaves the pin in force keeps the caches (#C8).
    let f = fixture();
    let mut solver = LiaSolver::new(&f.terms);
    solve_pinned_scope(&mut solver, &f);
    let gcds_before = solver.dioph_cached_modular_gcds.clone();
    // An inner scope that adds nothing the caches depend on.
    solver.push();
    solver.pop();
    assert!(solver.dioph_needs_revalidation);
    assert!(solver.dioph_fold_reasons_live());
    solver.revalidate_dioph_caches(false);
    assert_eq!(solver.dioph_cached_modular_gcds, gcds_before);
    assert!(!solver.dioph_cached_fold_reasons.is_empty());
}

#[test]
fn d2_folded_modulus_does_not_survive_an_import_without_its_pin() {
    let f = fixture();
    let mut exporter = LiaSolver::new(&f.terms);
    solve_pinned_scope(&mut exporter, &f);
    let state = exporter.take_dioph_state();

    // A fresh instance with the base assertions only, as the split loops
    // rebuild one per round and import the previous round's state.
    let mut solver = LiaSolver::new(&f.terms);
    solver.import_dioph_state(state);
    solver.assert_literal(f.eq, true);
    solver.assert_literal(f.z_ge, true);
    solver.assert_literal(f.z_le, true);
    let result = solver.check();
    assert!(
        !is_unsat(&result),
        "an imported folded modulus must be re-validated against this instance; got {result:?}"
    );
}
