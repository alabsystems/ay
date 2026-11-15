// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use sha2::{Digest, Sha256};

const ORIGINAL: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/fixtures/external_codegen_consumer_whole_frame.smt2"
));

#[test]
fn original_consumer_whole_has_a_checked_authored_macro_assumption_bridge() {
    assert_eq!(ORIGINAL.len(), 2383);
    assert_eq!(
        format!("{:x}", Sha256::digest(ORIGINAL.as_bytes())),
        "f29f47fafe39b038aa7b06699e45d7eb55abfc75286b016d93e9961ccda0bbc7"
    );
    let _probe =
        ay_core::misc_test_override::set(ay_core::debug_channel::misc_cli_flags_with(|f| {
            f.probe_cert_reject = true
        }));
    let mut exec = Executor::new();
    exec.set_produce_proofs(true);
    exec.set_alethe_dialect(ay_proof::AletheDialect::Clean);
    exec.set_timeout(Some(std::time::Duration::from_secs(30)));
    exec.set_memory_limit(Some(8 * 1024 * 1024 * 1024));
    assert_eq!(
        exec.execute_all(&parse(ORIGINAL).unwrap()).unwrap(),
        ["unsat"]
    );
    let proof = exec.last_proof().unwrap();
    assert!(exec
        .check_proof_strict_derivation_with_datatypes(proof)
        .unwrap()
        .is_complete());
    let definitions = exec.nullary_definition_premises();
    let row = crate::executor::proof_surface_syntax::format_frontend_term(
        &exec.ctx.assertions_parsed()[2],
    );
    assert_eq!(definitions.len(), 2);
    let root = proof
        .steps
        .iter()
        .find_map(|step| {
            let ProofStep::Assume(term) = step else {
                return None;
            };
            matches!(exec.ctx.terms.get(*term),TermData::App(Symbol::Named(name),_) if name=="or")
                .then_some(*term)
        })
        .unwrap();
    let canonical = ay_proof::render_term_canonical(&exec.ctx.terms, root);
    let mut unique = std::collections::HashSet::new();
    let mut pending = vec![(root, 0usize)];
    let mut occurrences = 0usize;
    let mut edges = 0usize;
    let mut max_depth = 0usize;
    let mut max_pending = 0usize;
    while let Some((term, depth)) = pending.pop() {
        occurrences += 1;
        assert!(occurrences <= 8192);
        max_depth = max_depth.max(depth);
        if unique.insert(term) {
            edges += match exec.ctx.terms.get(term) {
                TermData::App(_, a) => a.len(),
                TermData::Not(_) => 1,
                TermData::Ite(..) => 3,
                _ => 0,
            };
        }
        match exec.ctx.terms.get(term) {
            TermData::App(_, a) => pending.extend(a.iter().map(|t| (*t, depth + 1))),
            TermData::Not(t) => pending.push((*t, depth + 1)),
            TermData::Ite(a, b, c) => {
                pending.extend([(*a, depth + 1), (*b, depth + 1), (*c, depth + 1)])
            }
            TermData::Var(..) | TermData::Const(_) => (),
            _ => panic!("unexpected fixture schema"),
        }
        max_pending = max_pending.max(pending.len());
    }
    println!("CONSUMER_WHOLE_GRAPH unique={} edges={edges} expanded={occurrences} depth={max_depth} pending={max_pending}", unique.len());
    let supported = ay_proof::nullary_definition_assume_bridge_is_supported(
        &exec.ctx.terms,
        root,
        &row,
        &definitions,
    );
    println!("CONSUMER_WHOLE_OWNER root={root} canonical_bytes={} authored_bytes={} definitions={} bridge_supported={supported}", canonical.len(), row.len(), definitions.len());
    assert!(supported,"the exact original needs a checked authored definition bridge, with existing bounds intact");
    for missing in ["frame", "saved"] {
        let mut absent = definitions.clone();
        assert!(absent.remove(missing).is_some());
        assert!(
            !ay_proof::nullary_definition_assume_bridge_is_supported(
                &exec.ctx.terms,
                root,
                &row,
                &absent
            ),
            "missing source definition {missing} is not authority"
        );
    }
    let mut wrong = definitions.clone();
    let body = wrong.get_mut("frame").unwrap();
    let original_body = body.clone();
    *body = body.replace("bv16", "bv17");
    assert_ne!(
        *body, original_body,
        "the negative really changes the defining source body"
    );
    assert!(
        !ay_proof::nullary_definition_assume_bridge_is_supported(
            &exec.ctx.terms,
            root,
            &row,
            &wrong
        ),
        "wrong macro body cannot establish the canonical assertion"
    );
    let text = exec.execute_authored(&Command::GetProof).unwrap().unwrap();
    assert!(
        !text.starts_with("(error")
            && !text.contains(":rule hole")
            && !text.contains(":rule trust")
    );
}
