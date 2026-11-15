// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! An assumed equality whose authored operand ORDER is not the interned one.
//!
//! `TermStore::mk_eq` orders its operands by term identity, so
//! `(assert (not (= (select b idx) val)))` interns as
//! `(not (= val (select b idx)))`. Certified reconstruction purges every
//! authored spelling attached to a printed term and then restores the problem
//! file's spelling for the reachable `assume` ROOTS only, so that one literal
//! prints authored wherever the document mentions it while the SAME atom's
//! positive occurrences — a different `TermId`, carrying no override — keep
//! printing canonically. The Tseitin block around a negated assumption
//! resolves exactly those two against each other:
//!
//! ```text
//! (step t18 (cl (= (not (= (select b idx) val)) false)
//!               (not (= (select b idx) val)) false) :rule equiv_neg2)
//! (step t16 (cl (= val (select b idx))) :rule th_resolution ..)
//! (step t19 (cl ..) :rule th_resolution :premises (t18 t16))
//! ```
//!
//! Measured on pinned carcara 1.1.0 before the bridge: `checking failed on
//! step 't19' with rule 'th_resolution': pivot was not eliminated`, and AY's
//! own printed-resolution judgement refused the export outright — `unsat`
//! with no document at all, the row this corpus gate stopped on.
//!
//! The repair states equality symmetry with the checker's own rules rather
//! than inheriting it from a term identity carcara cannot see.

use super::{require_carcara_or_skip, run_carcara_trust_free, solve_unsat_and_get_proof};
use ntest::timeout;

/// `benchmarks/smt/QF_ABV/csplit_repro_indirect_store_unsat.smt2`, inlined so
/// the pin does not depend on a corpus a worktree may not carry.
const INDIRECT_STORE: &str = r#"
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun b () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun idx () (_ BitVec 32))
(declare-fun val () (_ BitVec 8))
(assert (= b (store a idx val)))
(assert (not (= (select b idx) val)))
(check-sat)
"#;

#[test]
#[timeout(60_000)]
fn a_reversed_assume_equality_is_bridged_and_the_document_still_exports() {
    let label = "tseitin_equality_pivot";
    let proof = solve_unsat_and_get_proof(INDIRECT_STORE, label);
    assert!(
        proof.contains("(assume ") && proof.contains("(= (select b idx) val)"),
        "the assumed literal must keep the problem file's own operand order:\n{proof}"
    );
    // The bridge can orient the atom with an equality-symmetry clause or
    // orient an already derived unit before resolving the authored assume.
    assert!(
        proof.contains(":rule eq_symmetric") || proof.contains(":rule symm"),
        "the two printed orientations of one atom must be linked by a real \
         inference, never silently accepted:\n{proof}"
    );
    ay_proof::check_alethe_document_in_dialect(
        &proof,
        &ay_proof::ProblemScope::from_smtlib_source(INDIRECT_STORE),
        ay_proof::AletheDialect::PinnedCarcara,
    )
    .expect("the printed bridge must retain the exact source and valid resolution pivots");
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    assert!(
        run_carcara_trust_free(&carcara, label, INDIRECT_STORE, &proof),
        "the bridged Tseitin resolution must replay in Carcara without trust"
    );
}
