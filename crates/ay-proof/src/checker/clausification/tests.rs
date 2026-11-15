// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::{AletheRule, Proof, ProofStep, Sort, Symbol, TermData};

fn fixture(index: usize) -> (TermStore, Proof, Vec<TermId>) {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let source = terms.mk_app(Symbol::named("and"), [p, q], Sort::Bool);
    let chosen = [p, q][index];
    let denied = terms.mk_not_raw(chosen);
    let arg = terms.mk_int(index.into());
    let mut proof = Proof::new();
    let a = proof.add_assume(source, None);
    let b = proof.add_assume(denied, None);
    let unit = proof.add_rule_step(AletheRule::And, vec![chosen], vec![a], vec![arg]);
    proof.add_resolution(vec![], chosen, b, unit);
    (terms, proof, vec![source, denied])
}
fn artifacts(name: &str, t: &TermStore, p: &Proof, assertions: &[TermId]) {
    let Ok(directory) = std::env::var("AY_STANDARD_AND_ARTIFACT_DIR") else {
        return;
    };
    let directory = std::path::Path::new(&directory);
    std::fs::create_dir_all(directory).unwrap();
    let (wire, notes) = crate::capture_alethe_dialect_report(|| {
        crate::with_alethe_dialect(crate::AletheDialect::PinnedCarcara, || {
            crate::try_export_alethe_with_problem_scope_and_overrides(p, t, assertions, None)
                .unwrap()
        })
    });
    assert!(notes.first_clean_only().is_none());
    assert!(!wire.contains(":rule hole") && !wire.contains(":rule trust"));
    assert!(wire.contains(":rule and :premises (t0) :args ("), "{wire}");
    let mut problem =
        String::from("(set-logic QF_UF)\n(declare-const p Bool)\n(declare-const q Bool)\n");
    for &a in assertions {
        problem.push_str(&format!("(assert {})\n", crate::format_term_alethe(t, a)));
    }
    problem.push_str("(check-sat)\n");
    std::fs::write(directory.join(format!("{name}.json")),serde_json::to_vec_pretty(&serde_json::json!({"type":"alethe_certificate","version":"1.0","problem":problem,"proof":wire})).unwrap()).unwrap();
}

#[test]
fn standard_and_contract_and_wire() {
    for index in [0, 1] {
        let (t, p, a) = fixture(index);
        artifacts(&format!("index-{index}"), &t, &p, &a);
        let (mut work, mut bytes) = (0usize, 0usize);
        let result = crate::check_proof_strict_with_context_and_progress(
            &p,
            &t,
            None,
            None,
            Some(&a),
            &mut |w, b| {
                work = work.checked_add(w).unwrap();
                bytes = bytes.checked_add(b).unwrap();
                work <= 350_000_000 && bytes <= 1_342_177_280
            },
        );
        if let Ok(dir) = std::env::var("AY_STANDARD_AND_ARTIFACT_DIR") {
            std::fs::write(std::path::Path::new(&dir).join(format!("index-{index}-native.json")),serde_json::to_vec_pretty(&serde_json::json!({"result":format!("{result:?}"),"work":work,"bytes":bytes,"envelope_work":350_000_000usize,"envelope_bytes":1_342_177_280usize})).unwrap()).unwrap();
        }
        result.unwrap();
    }
}

fn direct(
    t: &TermStore,
    source: TermId,
    selected: TermId,
    index: TermId,
) -> Result<(), ProofCheckError> {
    validate_and_clausification(
        t,
        ProofId(7),
        &[selected],
        &[&[source]],
        &[index],
        &mut |_, _| true,
    )
}
fn make_proof(
    t: &mut TermStore,
    source: TermId,
    selected: TermId,
    index: usize,
) -> (Proof, Vec<TermId>) {
    let denied = t.mk_not_raw(selected);
    let argument = t.mk_int(index.into());
    let mut p = Proof::new();
    let a = p.add_assume(source, None);
    let b = p.add_assume(denied, None);
    let u = p.add_rule_step(AletheRule::And, vec![selected], vec![a], vec![argument]);
    p.add_resolution(vec![], selected, b, u);
    (p, vec![source, denied])
}
fn bounded(t: &TermStore, p: &Proof, a: &[TermId]) -> (Result<(), ProofCheckError>, usize, usize) {
    let (mut work, mut bytes) = (0usize, 0usize);
    let result = crate::check_proof_strict_with_context_and_progress(
        p,
        t,
        None,
        None,
        Some(a),
        &mut |w, b| {
            work = work.checked_add(w).unwrap();
            bytes = bytes.checked_add(b).unwrap();
            work <= 350_000_000 && bytes <= 1_342_177_280
        },
    );
    (result.map(|_| ()), work, bytes)
}
fn write_certificate(name: &str, problem: &str, wire: &str) {
    if let Ok(dir) = std::env::var("AY_STANDARD_AND_ARTIFACT_DIR") {
        let dir = std::path::Path::new(&dir);
        std::fs::create_dir_all(dir).unwrap();
        std::fs::write(dir.join(format!("{name}.json")),serde_json::to_vec_pretty(&serde_json::json!({"type":"alethe_certificate","version":"1.0","problem":problem,"proof":wire})).unwrap()).unwrap();
    }
}
fn wire(t: &TermStore, p: &Proof, a: &[TermId]) -> String {
    let first = crate::with_alethe_dialect(crate::AletheDialect::PinnedCarcara, || {
        crate::try_export_alethe_with_problem_scope_and_overrides(p, t, a, None).unwrap()
    });
    let (second, notes) = crate::capture_alethe_dialect_report(|| {
        crate::with_alethe_dialect(crate::AletheDialect::Clean, || {
            crate::try_export_alethe_with_problem_scope_and_overrides(p, t, a, None).unwrap()
        })
    });
    assert_eq!(first, second);
    assert!(notes.first_clean_only().is_none());
    assert!(!first.contains(":rule hole"));
    first
}
fn problem(t: &TermStore, a: &[TermId]) -> String {
    let mut source =
        "(set-logic QF_UF)\n(declare-const p Bool)\n(declare-const q Bool)\n".to_owned();
    for &a in a {
        source.push_str(&format!("(assert {})\n", crate::format_term_alethe(t, a)));
    }
    source.push_str("(check-sat)\n");
    source
}

#[test]
fn standard_and_unary_nested_negated_repeated_and_wide_native_exports() {
    for kind in [
        "unary",
        "nested",
        "negated",
        "repeated",
        "wide-1024",
        "opaque-sibling",
    ] {
        let mut t = TermStore::new();
        let p = t.mk_var("p", Sort::Bool);
        let q = t.mk_var("q", Sort::Bool);
        let mut deep = q;
        for _ in 0..256 {
            deep = t.mk_not_raw(deep);
        }
        let not_p = t.mk_not_raw(p);
        let nested = t.mk_app(Symbol::named("and"), [p, q], Sort::Bool);
        let (children, index) = match kind {
            "unary" => (vec![p], 0),
            "nested" => (vec![nested, not_p], 0),
            "negated" => (vec![p, not_p], 1),
            "repeated" => (vec![p, p, p], 2),
            "wide-1024" => {
                let mut a = vec![p; 1024];
                a[1023] = q;
                (a, 1023)
            }
            "opaque-sibling" => (vec![p, deep], 0),
            _ => unreachable!(),
        };
        let selected = children[index];
        let source = t.mk_app(Symbol::named("and"), children, Sort::Bool);
        let (p, a) = make_proof(&mut t, source, selected, index);
        let (result, work, bytes) = bounded(&t, &p, &a);
        result.unwrap();
        let text = wire(&t, &p, &a);
        write_certificate(kind, &problem(&t, &a), &text);
        if let Ok(dir) = std::env::var("AY_STANDARD_AND_ARTIFACT_DIR") {
            std::fs::write(std::path::Path::new(&dir).join(format!("{kind}-native.json")),serde_json::to_vec_pretty(&serde_json::json!({"strict_native":true,"work":work,"bytes":bytes,"proof_steps":p.steps.len(),"no_new_caps":true})).unwrap()).unwrap();
        }
    }
}

#[test]
fn standard_and_malformed_ids_sorts_heads_indices_and_payloads_fail_closed() {
    use ay_core::Constant;
    let (mut t, p, a) = fixture(0);
    let source = a[0];
    let TermData::App(_, children) = t.get(source) else {
        panic!("and")
    };
    let selected = children[0];
    let other = children[1];
    let zero = t.mk_int(0.into());
    let two = t.mk_int(2.into());
    let neg = t.mk_int((-1).into());
    let huge = t.mk_int(num_bigint::BigInt::from(1u8) << 4096u32);
    let bool_index = t.false_term();
    let bv = t.mk_bitvec(0.into(), 8);
    let real = t.mk_rational(num_rational::BigRational::from_integer(0.into()));
    let index_var = t.mk_var("index", Sort::Int);
    let expression = t.mk_app(Symbol::named("+"), [zero, zero], Sort::Int);
    for index in [
        two,
        neg,
        huge,
        bool_index,
        bv,
        real,
        index_var,
        expression,
        TermId(u32::MAX),
    ] {
        assert!(direct(&t, source, selected, index).is_err());
    }
    for selected in [other, t.mk_not_raw(selected), TermId(u32::MAX)] {
        assert!(direct(&t, source, selected, zero).is_err());
    }
    let int = t.mk_int(0.into());
    let not_source = t.mk_not_raw(source);
    let bad = [
        t.mk_app(Symbol::named("and"), [], Sort::Bool),
        t.mk_app(Symbol::named("or"), [selected, other], Sort::Bool),
        t.mk_app(
            Symbol::named("__ay_private_and"),
            [selected, other],
            Sort::Bool,
        ),
        t.mk_app(
            Symbol::indexed("and", vec![]),
            [selected, other],
            Sort::Bool,
        ),
        t.mk_app(Symbol::named("and"), [selected, int], Sort::Bool),
        t.mk_app(
            Symbol::named("and"),
            [selected, TermId(u32::MAX)],
            Sort::Bool,
        ),
        t.mk_app(Symbol::named("and"), [selected, other], Sort::Int),
        not_source,
        TermId(u32::MAX),
    ];
    for source in bad {
        assert!(direct(&t, source, selected, zero).is_err());
    }
    for (conclusion, premises, args) in [
        (vec![], vec![vec![source]], vec![zero]),
        (vec![selected, other], vec![vec![source]], vec![zero]),
        (vec![selected], vec![], vec![zero]),
        (vec![selected], vec![vec![source], vec![source]], vec![zero]),
        (vec![selected], vec![vec![source, source]], vec![zero]),
        (vec![selected], vec![vec![]], vec![zero]),
        (vec![selected], vec![vec![source]], vec![]),
        (vec![selected], vec![vec![source]], vec![zero, zero]),
    ] {
        let views: Vec<_> = premises.iter().map(Vec::as_slice).collect();
        assert!(validate_and_clausification(
            &t,
            ProofId(7),
            &conclusion,
            &views,
            &args,
            &mut |_, _| true
        )
        .is_err());
    }
    for (id, data, sort) in [
        (source, t.get(source).clone(), Sort::Int),
        (selected, t.get(selected).clone(), Sort::Int),
        (zero, TermData::Const(Constant::Int(0.into())), Sort::Bool),
    ] {
        let mut entries = t.entries_snapshot();
        entries[id.index()] = (data, sort);
        let forged = TermStore::from_entries(
            entries,
            Some(t.true_term()),
            Some(t.false_term()),
            t.var_counter(),
        );
        assert!(direct(&forged, source, selected, zero).is_err());
    }
    let mut custom = p.clone();
    let ProofStep::Step { rule, .. } = &mut custom.steps[2] else {
        panic!("and")
    };
    *rule = AletheRule::Custom("and".to_owned());
    assert!(bounded(&t, &custom, &a).0.is_err());
}

#[test]
fn standard_and_actual_shared_work_stop_failure_and_opaque_body_controls() {
    let (mut t, _, a) = fixture(0);
    let source = a[0];
    let TermData::App(_, children) = t.get(source) else {
        panic!("and")
    };
    let selected = children[0];
    let zero = t.mk_int(0.into());
    let mut calls = Vec::new();
    assert!(matches!(
        validate_and_clausification(
            &t,
            ProofId(2),
            &[TermId(u32::MAX)],
            &[],
            &[],
            &mut |w, b| {
                calls.push((w, b));
                false
            }
        ),
        Err(ProofCheckError::ResourceLimit)
    ));
    assert_eq!(calls, [(32, 0)]);
    // A bad unused sibling would be an InvalidAnd if read before admission.
    let invalid = t.mk_app(
        Symbol::named("and"),
        [selected, TermId(u32::MAX)],
        Sort::Bool,
    );
    let mut charges = Vec::new();
    assert!(matches!(
        validate_and_clausification(
            &t,
            ProofId(2),
            &[selected],
            &[&[invalid]],
            &[zero],
            &mut |w, b| {
                charges.push((w, b));
                w == 32
            }
        ),
        Err(ProofCheckError::ResourceLimit)
    ));
    assert_eq!(charges, [(32, 0), (24, 0)]);
    let mut polled = 0;
    assert!(matches!(
        validate_and_clausification(
            &t,
            ProofId(2),
            &[selected],
            &[&[source]],
            &[zero],
            &mut |w, _| {
                if w == 0 {
                    polled += 1;
                }
                polled < 2
            }
        ),
        Err(ProofCheckError::ResourceLimit)
    ));
    assert_eq!(polled, 2);
    let mut total = 0;
    for attempt in 0..3 {
        let result = validate_and_clausification(
            &t,
            ProofId(2),
            &[selected],
            &[&[source]],
            &[zero],
            &mut |w, _| {
                total += w;
                total <= 112
            },
        );
        assert_eq!(result.is_ok(), attempt < 2);
    }
    assert_eq!(total, 144);
    let mut opaque = t.mk_var("q", Sort::Bool);
    for _ in 0..8192 {
        opaque = t.mk_not_raw(opaque);
    }
    let huge_source = t.mk_app(Symbol::named("and"), [selected, opaque], Sort::Bool);
    let mut work = 0;
    let mut bytes = 0;
    validate_and_clausification(
        &t,
        ProofId(2),
        &[selected],
        &[&[huge_source]],
        &[zero],
        &mut |w, b| {
            work += w;
            bytes += b;
            true
        },
    )
    .unwrap();
    assert_eq!((work, bytes), (56, 0));
    let wide = t.mk_app(Symbol::named("and"), vec![selected; 32768], Sort::Bool);
    let mut wide_work = 0;
    validate_and_clausification(
        &t,
        ProofId(2),
        &[selected],
        &[&[wide]],
        &[zero],
        &mut |w, _| {
            wide_work += w;
            true
        },
    )
    .unwrap();
    assert_eq!(wide_work, 32 + 8 * 32768 + 8);
    let _probe =
        ay_core::misc_test_override::set(ay_core::debug_channel::misc_cli_flags_with(|f| {
            f.probe_strict_check = true
        }));
    for (name, source) in [
        ("opaque-8192-default-refused", huge_source),
        ("arity-32768-default-refused", wide),
    ] {
        let (p, a) = make_proof(&mut t, source, selected, 0);
        let (result, work, bytes) = bounded(&t, &p, &a);
        assert!(
            matches!(result, Err(ProofCheckError::ResourceLimit)),
            "{name}: {result:?}"
        );
        if let Ok(dir) = std::env::var("AY_STANDARD_AND_ARTIFACT_DIR") {
            std::fs::create_dir_all(&dir).unwrap();
            std::fs::write(std::path::Path::new(&dir).join(format!("{name}-native.json")),serde_json::to_vec_pretty(&serde_json::json!({"local_projection_valid":true,"full_current_bounded_result":format!("{result:?}"),"work":work,"bytes":bytes,"general_semantic_class_unchanged":true,"no_new_cap_or_budget_reset":true,"local_opaque_work":56,"local_arity32768_work":wide_work})).unwrap()).unwrap();
        }
    }
}

#[test]
fn standard_and_premise_and_source_authority_are_not_synthesized() {
    let (t, p, a) = fixture(0);
    for premise in [ProofId(u32::MAX), ProofId(1), ProofId(2), ProofId(3)] {
        let mut invalid = p.clone();
        let ProofStep::Step { premises, .. } = &mut invalid.steps[2] else {
            panic!("and")
        };
        *premises = vec![premise];
        assert!(bounded(&t, &invalid, &a).0.is_err());
    }
    let source = a[0];
    let TermData::App(_, children) = t.get(source) else {
        panic!("and")
    };
    let target = children[0];
    let other = children[1];
    let argument = match &p.steps[2] {
        ProofStep::Step { args, .. } => args[0],
        _ => unreachable!(),
    };
    let mut unavailable = vec![None];
    assert!(matches!(
        crate::checker::validate_generic_step(
            &t,
            &mut unavailable,
            ProofId(1),
            &AletheRule::And,
            &[target],
            &[ProofId(0)],
            &[argument],
            true,
            false,
            &mut |_, _| true
        ),
        Err(ProofCheckError::PremiseHasNoClause { .. })
    ));
    let mut missing = p.clone();
    let ProofStep::Step { premises, .. } = &mut missing.steps[2] else {
        panic!("and")
    };
    premises.clear();
    assert!(bounded(&t, &missing, &a).0.is_err());
    let mut t = t;
    let foreign = t.mk_app(Symbol::named("or"), [target, other], Sort::Bool);
    let printed = wire(&t, &p, &a);
    for (name, active) in [
        ("source-missing", vec![a[1]]),
        ("source-foreign", vec![foreign, a[1]]),
    ] {
        assert!(matches!(
            bounded(&t, &p, &active).0,
            Err(ProofCheckError::UnauthorizedAssumption { .. })
        ));
        write_certificate(name, &problem(&t, &active), &printed);
    }
    // Native Subproof has no checked implementation in the current owner.
    // This negative must fail there; this component adds no discharge support.
    let mut discharged = Proof::new();
    let s = discharged.add_assume(source, None);
    discharged.add_rule_step(AletheRule::Subproof, vec![source], vec![s], vec![]);
    let n = discharged.add_assume(a[1], None);
    let u = discharged.add_rule_step(
        AletheRule::And,
        vec![target],
        vec![ProofId(1)],
        vec![argument],
    );
    discharged.add_resolution(vec![], target, n, u);
    assert!(matches!(
        bounded(&t, &discharged, &a).0,
        Err(ProofCheckError::UnvalidatedRule { .. })
    ));
}

#[test]
fn standard_and_live_source_pop_is_checked_by_existing_context_owner() {
    let mut ctx = ay_frontend::Context::new();
    for command in ay_frontend::parse("(set-option :produce-proofs true)(set-logic QF_UF)(declare-const p Bool)(declare-const q Bool)(assert (not p))(push 1)(assert (and p q))").unwrap(){ctx.process_command(&command).unwrap();}
    assert_eq!(ctx.assertions.len(), 2);
    let source = ctx.assertions[1];
    let TermData::App(_, children) = ctx.terms.get(source) else {
        panic!("and")
    };
    let selected = children[0];
    let (p, assertions) = make_proof(&mut ctx.terms, source, selected, 0);
    bounded(&ctx.terms, &p, &ctx.assertions).0.unwrap();
    let printed = wire(&ctx.terms, &p, &assertions);
    write_certificate(
        "live-source-present",
        &problem(&ctx.terms, &ctx.assertions),
        &printed,
    );
    for command in ay_frontend::parse("(pop 1)").unwrap() {
        ctx.process_command(&command).unwrap();
    }
    assert_eq!(ctx.assertions.len(), 1);
    let (result, work, bytes) = bounded(&ctx.terms, &p, &ctx.assertions);
    assert!(result.is_err());
    if let Ok(dir) = std::env::var("AY_STANDARD_AND_ARTIFACT_DIR") {
        std::fs::write(std::path::Path::new(&dir).join("live-source-popped-native.json"),serde_json::to_vec_pretty(&serde_json::json!({"result":format!("{result:?}"),"work":work,"bytes":bytes,"actual_frontend_push_pop":true})).unwrap()).unwrap();
    }
    write_certificate(
        "live-source-popped",
        &problem(&ctx.terms, &ctx.assertions),
        &printed,
    );
}

#[test]
fn standard_and_causal_index_boolean_and_source_head_wire_controls() {
    let (mut t, p, a) = fixture(0);
    let text = wire(&t, &p, &a);
    let source = a[0];
    let TermData::App(_, children) = t.get(source) else {
        panic!("and")
    };
    let selected = children[0];
    let other = children[1];
    let index_one = t.mk_int(1.into());
    let wrong_polarity = t.mk_not_raw(selected);
    for (name, conclusion, index) in [
        ("wrong-index", selected, index_one),
        ("wrong-polarity", wrong_polarity, t.mk_int(0.into())),
        ("wrong-selected-child", other, t.mk_int(0.into())),
    ] {
        let mut bad = p.clone();
        let ProofStep::Step { clause, args, .. } = &mut bad.steps[2] else {
            panic!("and")
        };
        *clause = vec![conclusion];
        *args = vec![index];
        assert!(bounded(&t, &bad, &a).0.is_err());
        let needle = "(step t2 (cl p) :rule and :premises (t0) :args (0))";
        let replacement = format!(
            "(step t2 (cl {}) :rule and :premises (t0) :args ({}))",
            crate::format_term_alethe(&t, conclusion),
            crate::format_term_alethe(&t, index)
        );
        assert!(text.contains(needle), "{text}");
        write_certificate(
            name,
            &problem(&t, &a),
            &text.replacen(needle, &replacement, 1),
        );
    }
    // Standard rule semantics cannot project a disjunction, even though its
    // source assumption is authentic. This source instance is SAT.
    let or = t.mk_app(Symbol::named("or"), [selected, other], Sort::Bool);
    let (bad, assertions) = make_proof(&mut t, or, selected, 0);
    assert!(bounded(&t, &bad, &assertions).0.is_err());
    let wrong = crate::with_alethe_dialect(crate::AletheDialect::PinnedCarcara, || {
        crate::try_export_alethe_with_problem_scope_and_overrides(&bad, &t, &assertions, None)
            .unwrap()
    });
    write_certificate("wrong-source-head", &problem(&t, &assertions), &wrong);
}
