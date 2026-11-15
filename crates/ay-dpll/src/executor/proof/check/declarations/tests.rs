// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::{DatatypeConstructor, DatatypeField, DatatypeSort};

fn install(exec: &mut Executor, source: &str) {
    let commands = ay_frontend::parse(source).unwrap();
    assert!(exec.execute_all(&commands).unwrap().is_empty());
}

fn fixture() -> Executor {
    let mut exec = Executor::new();
    install(
        &mut exec,
        "
        (declare-datatype Item ((item (payload (Array (_ BitVec 64) (_ BitVec 129)))) (empty)))
        (declare-datatype Tag ((tag_a) (tag_b)))
    ",
    );
    exec
}

fn collect(
    exec: &Executor,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Collected<ProofDeclarationInventories> {
    Ok((
        exec.datatype_decls_for_strict_proof_with_progress(progress)?,
        exec.ctor_selector_decls_for_strict_proof_with_progress(progress)?,
        exec.datatype_member_signatures_for_strict_proof_with_progress(progress)?
            .expect("fixture has complete sticky metadata"),
    ))
}

#[test]
fn inventories_match_legacy_order_exact_sorts_and_nullary_handles() {
    assert_eq!(
        collect(&Executor::new(), &mut |_, _| true).unwrap(),
        (Vec::new(), Vec::new(), Vec::new())
    );
    let exec = fixture();
    let expected = (
        exec.datatype_decls_for_strict_proof(),
        exec.ctor_selector_decls_for_strict_proof(),
        exec.datatype_member_signatures_for_strict_proof().unwrap(),
    );
    let found = collect(&exec, &mut |_, _| true).unwrap();
    assert_eq!(found, expected);
    assert!(found
        .2
        .iter()
        .any(|s| s.identity == "empty" && s.nullary_term.is_some()));
    assert!(found
        .2
        .iter()
        .any(|s| matches!(&s.result_sort, Sort::Array(a)
        if a.element_sort == Sort::bitvec(129))));
}

#[test]
fn popped_and_redeclared_members_keep_exact_sticky_identities() {
    let mut exec = Executor::new();
    install(
        &mut exec,
        "(push 1) (declare-datatype Item ((item (payload Int))))",
    );
    let original = exec.datatype_member_signatures_for_strict_proof().unwrap();
    install(
        &mut exec,
        "(pop 1) (declare-datatype Item ((item (payload Bool))))",
    );
    let found = collect(&exec, &mut |_, _| true).unwrap();
    assert_eq!(
        found.2,
        exec.datatype_member_signatures_for_strict_proof().unwrap()
    );
    assert!(original.iter().all(|old| found.2.contains(old)));
    assert!(found
        .2
        .iter()
        .any(|s| s.result_sort == Sort::Bool
            && !original.iter().any(|old| old.identity == s.identity)));
    assert!(found.2.len() > original.len());
}

#[test]
fn shared_exact_work_bytes_and_each_checkpoint_refuse_without_partial_output() {
    let exec = fixture();
    let mut trace = Vec::new();
    let expected = collect(&exec, &mut |w, b| {
        trace.push((w, b));
        true
    })
    .unwrap();
    let total = trace
        .iter()
        .fold((0, 0), |(w, b), (dw, db)| (w + dw, b + db));
    assert!(total.0 > 0 && total.1 > 0);
    for (work, bytes, admitted) in [
        (total.0, total.1, true),
        (total.0 - 1, total.1, false),
        (total.0, total.1 - 1, false),
        (0, 0, false),
    ] {
        let (mut w, mut b) = (0, 0);
        let result = collect(&exec, &mut |dw, db| {
            w += dw;
            b += db;
            w <= work && b <= bytes
        });
        if admitted {
            assert_eq!(result.unwrap(), expected);
        } else {
            assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
        }
    }
    for stop in 0..trace.len() {
        let mut calls = 0;
        let result = collect(&exec, &mut |w, b| {
            assert_eq!((w, b), trace[calls]);
            let allow = calls != stop;
            calls += 1;
            allow
        });
        assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
        assert_eq!(calls, stop + 1);
    }
    assert_eq!(collect(&exec, &mut |_, _| true).unwrap(), expected);
}

#[test]
fn nested_payloads_and_depth_are_admitted_before_signature_clone() {
    let nested = Sort::Datatype(DatatypeSort {
        name: "Nested".repeat(400),
        constructors: vec![DatatypeConstructor::new(
            "ctor",
            vec![DatatypeField::new(
                "field",
                Sort::array(
                    Sort::bitvec(64),
                    Sort::Seq(Box::new(Sort::Uninterpreted("Cell".repeat(512)))),
                ),
            )],
        )],
    });
    let signatures = vec![DatatypeMemberSignature {
        identity: "f".to_string(),
        argument_sorts: vec![nested.clone()],
        result_sort: nested,
        nullary_term: None,
    }];
    let mut bytes = 0;
    let copied = Control::new(&mut |_, b| {
        bytes += b;
        true
    })
    .run(|c| copy_signatures(&signatures, c))
    .unwrap();
    assert_eq!(copied, signatures);
    assert!(bytes > 2 * ("Nested".len() * 400 + "Cell".len() * 512));
    let mut used = 0;
    assert!(matches!(
        Control::new(&mut |_, b| {
            used += b;
            used < bytes
        })
        .run(|c| copy_signatures(&signatures, c)),
        Err(ProofCheckError::ResourceLimit)
    ));

    for (depth, accepted) in [(256, true), (257, false)] {
        let mut sort = Sort::Bool;
        for _ in 0..depth {
            sort = Sort::Seq(Box::new(sort));
        }
        let result = Control::new(&mut |_, _| true).run(|c| c.sort(&sort, 0));
        assert_eq!(result.is_ok(), accepted);
    }
}

#[test]
fn local_overflow_and_caught_callback_panic_latch_before_retry() {
    assert!(matches!(
        Control::new(&mut |_, _| true).run(|c| copy_registry(1, std::iter::empty(), c)),
        Err(ProofCheckError::ResourceLimit)
    ));
    let mut calls = 0;
    let mut callback = |_, _| {
        calls += 1;
        true
    };
    let mut control = Control::new(&mut callback);
    assert!(matches!(
        control.run(|c| c.vector::<u64>(usize::MAX)),
        Err(ProofCheckError::ResourceLimit)
    ));
    assert!(control.charge(0, 0).is_err());
    drop(control);
    assert_eq!(calls, 1);

    let mut calls = 0;
    let mut callback = |_, _| {
        calls += 1;
        panic!("injected callback panic")
    };
    let mut control = Control::new(&mut callback);
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| control.charge(0, 0)));
    assert!(result.is_err());
    assert!(control.charge(0, 0).is_err());
    drop(control);
    assert_eq!(calls, 1);
    assert!(collect(&fixture(), &mut |_, _| true).is_ok());
}
