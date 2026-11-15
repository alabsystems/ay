// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::{Symbol, TheoryLemmaKind};

#[test]
fn small_linear_wire_screen_agrees_above_general_promotion_cap() {
    let mut exec = Executor::new();
    let terms = &mut exec.ctx.terms;
    let x = terms.mk_var("linear_wire_x", Sort::bitvec(64));
    let zero = terms.mk_bitvec(0.into(), 64);
    let sum = terms.mk_app(Symbol::named("bvadd"), [x, zero], Sort::bitvec(64));
    let identity = terms.mk_app(Symbol::named("="), [sum, x], Sort::Bool);
    let mut proof = Proof::new();
    for _ in 0..160 {
        proof.add_theory_lemma_with_kind(
            "bv",
            vec![identity],
            TheoryLemmaKind::ArithClauseTautology,
        );
    }
    assert!(!ay_proof::ArithPolySimpPromotionBudget::for_proof(&proof).proof_admitted());
    assert!(!exec.proof_has_known_wire_gap(&proof));
    let mut overrides = DetHashMap::default();
    overrides.insert(x, "(_ bv42 64)".to_owned());
    exec.last_proof_term_overrides = Some(overrides);
    assert!(exec.proof_has_known_wire_gap(&proof));
}

#[test]
fn general_arithmetic_screen_keeps_whole_proof_promotion_refusal() {
    let mut exec = Executor::new();
    let terms = &mut exec.ctx.terms;
    let x = terms.mk_var("general_wire_x", Sort::Int);
    let zero = terms.mk_int(0.into());
    let sum = terms.mk_app(Symbol::named("+"), [x, zero], Sort::Int);
    let identity = terms.mk_app(Symbol::named("="), [sum, x], Sort::Bool);
    let mut proof = Proof::new();
    for _ in 0..17 {
        proof.add_theory_lemma_with_kind(
            "arith",
            vec![identity],
            TheoryLemmaKind::ArithClauseTautology,
        );
    }
    assert!(exec.proof_has_known_wire_gap(&proof));
    let bv = exec.ctx.terms.mk_var("mixed_wire_bv", Sort::bitvec(64));
    let eq = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), [bv, bv], Sort::Bool);
    proof.add_theory_lemma_with_kind("bv", vec![eq], TheoryLemmaKind::ArithClauseTautology);
    assert!(exec.proof_has_known_wire_gap(&proof));
}
