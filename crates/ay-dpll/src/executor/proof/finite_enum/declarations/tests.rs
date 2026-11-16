// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn fixture() -> Executor {
    let source = "
        (declare-datatype Two ((a) (b)))
        (declare-const left Two) (declare-const middle Two) (declare-const right Two)
        (assert true)
        (assert (not (= left middle)))
        (assert (not (= left right)))
        (assert (not (= middle right)))
    ";
    let mut exec = Executor::new();
    // A proof request re-arms parsed retention. Set the explicit memory policy
    // afterwards, before any authored assertion can retain a surface.
    assert_eq!(
        exec.execute_all(&ay_frontend::parse("(set-option :produce-proofs true)").unwrap())
            .unwrap(),
        [] as [String; 0]
    );
    exec.set_retain_parsed_assertions(false);
    assert_eq!(
        exec.execute_all(&ay_frontend::parse(source).unwrap())
            .unwrap(),
        [] as [String; 0]
    );
    assert_eq!(exec.ctx.assertions_parsed(), []);
    exec.begin_public_solve(false);
    exec.bind_unsat_query_assumptions(&[]);
    let left = exec.ctx.symbol_info("left").unwrap().term.unwrap();
    let middle = exec.ctx.symbol_info("middle").unwrap().term.unwrap();
    let right = exec.ctx.symbol_info("right").unwrap().term.unwrap();
    // Singleton constants are eagerly identified with their sole inhabitant.
    // Use a genuine finite pigeonhole, not an already-folded literal false.
    assert_ne!(left, middle);
    assert_ne!(left, right);
    assert_ne!(middle, right);
    assert_eq!(exec.ctx.assertions.len(), 4);
    let mut edges = ay_core::kani_compat::DetHashMap::default();
    for (&source, (left, right)) in
        exec.ctx.assertions[1..]
            .iter()
            .zip([(left, middle), (left, right), (middle, right)])
    {
        let TermData::Not(equality) = exec.ctx.terms.get(source) else {
            panic!("fixture edge must remain an authored disequality");
        };
        let TermData::App(symbol, args) = exec.ctx.terms.get(*equality) else {
            panic!("fixture edge must contain its original equality");
        };
        assert_eq!(symbol, &Symbol::named("="));
        assert_eq!(args.as_slice(), &[left, right]);
        let key = if left.0 < right.0 {
            (left, right)
        } else {
            (right, left)
        };
        assert!(edges.insert(key, source).is_none());
    }
    assert_eq!(edges.len(), 3);
    exec.last_finite_enum_pigeonhole = Some(crate::executor::FiniteEnumPigeonholeWitness {
        k: 2,
        members: vec![left, middle, right],
        edge_sources: edges,
    });
    assert!(exec.try_install_bounded_finite_enum_pigeonhole_proof());
    assert!(exec.last_proof_is_checked_finite_enum());
    exec
}

fn collect(
    exec: &Executor,
    proof: &Proof,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(ProofDeclarationInventories, Vec<TermId>), ProofCheckError> {
    Ok((
        exec.checked_finite_enum_export_declarations_with_progress(proof, progress)?
            .expect("fixture seal is current"),
        exec.finite_enum_scope_for_proof_with_progress(proof, progress)?
            .expect("fixture seal is current"),
    ))
}

#[test]
fn surface_less_seal_copies_exact_inventory_and_selected_direct_roots() {
    let exec = fixture();
    let proof = exec.last_proof.as_ref().unwrap();
    let (decls, scope) = collect(&exec, proof, &mut |_, _| true).unwrap();
    assert_eq!(
        decls,
        exec.checked_finite_enum_export_declarations(proof).unwrap()
    );
    assert_eq!(scope, exec.finite_enum_scope_for_proof(proof).unwrap());
    assert_eq!(scope.len(), 3);
    assert_eq!(exec.ctx.assertions.len(), 4);
    assert_eq!(scope.as_slice(), &exec.ctx.assertions[1..]);
    assert_eq!(exec.ctx.assertions_parsed(), []);
    assert!(exec
        .current_checked_finite_enum_proof()
        .unwrap()
        .surface
        .is_none());
}

#[test]
fn finite_inventory_and_scope_share_exact_allowance_and_every_stop_is_terminal() {
    let exec = fixture();
    let proof = exec.last_proof.as_ref().unwrap();
    let mut trace = Vec::new();
    let expected = collect(&exec, proof, &mut |w, b| {
        trace.push((w, b));
        true
    })
    .unwrap();
    let (work, bytes) = trace
        .iter()
        .fold((0, 0), |(w, b), (dw, db)| (w + dw, b + db));
    for (work_cap, byte_cap, accepted) in [
        (work, bytes, true),
        (work - 1, bytes, false),
        (work, bytes - 1, false),
    ] {
        let (mut w, mut b) = (0, 0);
        let result = collect(&exec, proof, &mut |dw, db| {
            w += dw;
            b += db;
            w <= work_cap && b <= byte_cap
        });
        if accepted {
            assert_eq!(result.unwrap(), expected);
        } else {
            assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
        }
    }
    for stop in 0..trace.len() {
        let mut calls = 0;
        let result = collect(&exec, proof, &mut |w, b| {
            assert_eq!((w, b), trace[calls]);
            calls += 1;
            calls - 1 != stop
        });
        assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
        assert_eq!(calls, stop + 1);
    }
    assert_eq!(collect(&exec, proof, &mut |_, _| true).unwrap(), expected);
}

#[test]
fn stale_or_different_proof_never_inherits_finite_inventory_or_scope() {
    let mut exec = fixture();
    let proof = exec.last_proof.as_ref().unwrap().clone();
    let mut other = proof.clone();
    other.steps.pop();
    for candidate in [&other, &Proof::default()] {
        assert!(exec
            .checked_finite_enum_export_declarations_with_progress(candidate, &mut |_, _| true)
            .unwrap()
            .is_none());
        assert!(exec
            .finite_enum_scope_for_proof_with_progress(candidate, &mut |_, _| true)
            .unwrap()
            .is_none());
    }
    let old_source = exec.ctx.source_context_stamp();
    // Working roots may legitimately change during preprocessing. Mutate the
    // actual source through the public frontend instead, leaving the executor's
    // old sidecar present so its own currency check must reject the evidence.
    for command in
        ay_frontend::parse("(declare-const fresh_root Bool) (assert fresh_root)").unwrap()
    {
        assert!(exec.ctx.process_command(&command).unwrap().is_none());
    }
    let fresh = exec.ctx.symbol_info("fresh_root").unwrap().term.unwrap();
    assert_eq!(exec.ctx.assertions.len(), 5);
    assert_eq!(exec.ctx.assertions.last(), Some(&fresh));
    assert_ne!(exec.ctx.source_context_stamp(), old_source);
    assert!(exec.last_checked_finite_enum_pigeonhole.is_some());
    assert!(exec
        .checked_finite_enum_export_declarations_with_progress(&proof, &mut |_, _| true)
        .unwrap()
        .is_none());
    assert!(exec
        .finite_enum_scope_for_proof_with_progress(&proof, &mut |_, _| true)
        .unwrap()
        .is_none());
}
