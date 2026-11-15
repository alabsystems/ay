// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_frontend::command::Constant as FrontendConstant;

// Exact CG12c5 original TY ordinal0 CoreToLir Return obligation, SHA256
// 5d786615949b33670102030daec0bf09d1ac36e6d4bfafb0f35818b169312a9f.
const ORIGINAL: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/fixtures/external_codegen_read_only_return.smt2"
));

#[test]
fn original_read_only_return_keeps_a_checked_exact_source_refutation() {
    let mut executor = loaded(ORIGINAL);
    let assertion = executor.ctx.assertions_parsed()[0].clone();
    assert!(bounded_source(&assertion).is_none());
    assert!(executor.raw_intern_ground_bv_surface(&assertion).is_none());
    let raw = executor
        .raw_intern_shared_ground_memory_surface(&assertion)
        .unwrap();
    assert_ne!(raw, executor.ctx.terms.false_term());
    assert!(executor.early_ground_memory_terms_print_faithfully(&[raw]));
    let outputs = executor
        .execute_all(
            &ay_frontend::parse("(set-option :produce-proofs true)(check-sat)(get-proof)").unwrap(),
        )
        .unwrap();
    assert_eq!(outputs.first().map(String::as_str), Some("unsat"));
    let proof = executor
        .last_proof()
        .expect("original-source proof retained");
    executor.check_proof_strict_with_datatypes(proof).unwrap();
    let text = outputs.last().unwrap();
    assert!(!text.starts_with("(error"));
    assert!(text.contains(":rule eq_reflexive"));
    assert!(!text.contains(":rule hole") && !text.contains(":rule trust"));
}

#[test]
fn original_read_only_source_still_requires_the_exact_public_epoch() {
    let mut executor = loaded(ORIGINAL);
    declined_without_authority(&mut executor);
    arm(&mut executor);
    executor.ctx.assertions[0] = executor.ctx.terms.true_term();
    declined_without_authority(&mut executor);
}

#[test]
fn nonreflexive_read_only_twin_cannot_mint_a_refutation() {
    let mut executor = loaded(ORIGINAL);
    let mut assertion = executor.ctx.assertions_parsed()[0].clone();
    make_final_return_nonreflexive(&mut assertion);
    executor
        .execute_all(&ay_frontend::parse("(reset-assertions)").unwrap())
        .unwrap();
    executor.execute_all(&[Command::Assert(assertion)]).unwrap();
    arm(&mut executor);
    declined_without_authority(&mut executor);
    let outputs = executor
        .execute_all(&ay_frontend::parse("(check-sat)").unwrap())
        .unwrap();
    assert_eq!(outputs, ["sat"]);
}

// Exact source uses a right-nested conjunction; its closing `not` is reached
// through the final conjunct spine, rather than assumed to be a direct child.
fn make_final_return_nonreflexive(term: &mut FrontendTerm) {
    let FrontendTerm::App(head, args) = term else {
        panic!("application on final conjunct spine");
    };
    if head == "and" {
        make_final_return_nonreflexive(args.last_mut().unwrap());
        return;
    }
    assert_eq!(head, "not");
    assert_eq!(args.len(), 1);
    let FrontendTerm::App(head, sides) = &mut args[0] else {
        panic!("equality");
    };
    assert_eq!(head, "=");
    assert_eq!(sides.len(), 2);
    sides[1] = FrontendTerm::App(
        "bvadd".into(),
        vec![
            sides[1].clone(),
            FrontendTerm::Const(FrontendConstant::Hexadecimal("#x0000000000000001".into())),
        ],
    );
}
