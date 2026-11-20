// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn loaded(input: &str) -> Executor {
    // The direct certifier consumes the exact assertion roots; no earlier
    // search is needed to supply a raw candidate or a verdict side channel.
    let commands = ay_frontend::parse(&input.replace("(check-sat)", "")).unwrap();
    let mut exec = Executor::new();
    exec.set_strict_grant_evidence_required(true);
    for command in &commands {
        exec.execute(command).unwrap();
    }
    exec
}

fn certify(exec: &mut Executor) -> Option<()> {
    let _diagnostics = ay_core::debug_channel::misc_test_override::set(
        ay_core::debug_channel::misc_cli_flags_with(|flags| {
            flags.debug_cert = true;
            flags.probe_cert_reject = true;
        }),
    );
    let roots = exec.ctx.assertions.clone();
    exec.try_const_interp_sat_certificate(&roots, LogicCategory::Auflia)
}

#[test]
fn theory_program_checks_native_concat_identities() {
    let mut exec = loaded(
        "(set-logic ALL)
        (declare-fun cat ((Seq Int) (Seq Int)) (Seq Int))
        (declare-const empty (Seq Int))
        (assert (forall ((a (Seq Int)) (b (Seq Int)) (c (Seq Int)))
            (= (cat (cat a b) c) (cat a (cat b c)))))
        (assert (forall ((a (Seq Int))) (= (cat empty a) a)))
        (assert (forall ((a (Seq Int))) (= (cat a empty) a)))",
    );
    assert!(
        certify(&mut exec).is_some(),
        "strict native concatenation identities must certify"
    );
}

const FIXTURES: [(&str, &str); 3] = [
    (
        "has_value_usize",
        include_str!(
            "../../../../tests/fixtures/verification_consumer_9185/slice_index_has_value_usize_sat.smt2"
        ),
    ),
    (
        "in_bounds_usize",
        include_str!(
            "../../../../tests/fixtures/verification_consumer_9185/slice_index_in_bounds_usize_sat.smt2"
        ),
    ),
    (
        "in_bounds_range_inclusive",
        include_str!(
            "../../../../tests/fixtures/verification_consumer_9185/slice_index_in_bounds_range_inclusive_sat.smt2"
        ),
    ),
];

#[test]
fn theory_program_checks_every_original_wp_reducer_assertion() {
    let mut refused = Vec::new();
    for (label, input) in FIXTURES {
        let mut exec = loaded(input);
        let original_term_count = exec.ctx.terms.len();
        if certify(&mut exec).is_none() {
            // Diagnostic only, after the refused attempt and outside its
            // original grant. Never render a whole DAG in the producer path.
            let diagnostic = (original_term_count..exec.ctx.terms.len())
                .filter_map(|index| u32::try_from(index).ok().map(TermId::new))
                .filter_map(|term| match exec.ctx.terms.get(term) {
                    TermData::App(Symbol::Named(name), arguments) if name == "and" => {
                        Some((arguments.len(), term))
                    }
                    _ => None,
                })
                .max_by_key(|(arity, _)| *arity);
            if let Some((_, term)) = diagnostic {
                eprintln!(
                    "WP refused complete obligation {label}: {}",
                    ay_proof::render_term_canonical(&exec.ctx.terms, term)
                );
                eprintln!(
                    "WP independent complete recognition {label}: {}",
                    ay_proof::recognize_seq_ground_eval(&exec.ctx.terms, &[term])
                );
                if let TermData::App(_, conjuncts) = exec.ctx.terms.get(term) {
                    for &conjunct in conjuncts {
                        if !ay_proof::recognize_seq_ground_eval(&exec.ctx.terms, &[conjunct]) {
                            eprintln!(
                                "WP unrecognized conjunct {label}: {}",
                                ay_proof::render_term_canonical(&exec.ctx.terms, conjunct)
                            );
                        }
                    }
                }
                for name in [
                    "seq.empty",
                    "seq.unit",
                    "seq.++",
                    "seq.len",
                    "seq.contains",
                    "=",
                    "and",
                    "or",
                    "+",
                    "<",
                    "<=",
                ] {
                    eprintln!(
                        "WP native owner {label} {name}: declared={} unambiguous={} kind={:?}",
                        exec.ctx.terms.is_declared_function(name),
                        exec.ctx.canonical_operator_binding_is_unambiguous(name),
                        exec.ctx
                            .symbol_info_by_identity(name)
                            .map(|info| info.declaration_kind())
                    );
                }
            }
            refused.push(label);
        }
    }
    assert!(
        refused.is_empty(),
        "no strict checked whole-source interpretation: {refused:?}"
    );
}

#[test]
fn theory_program_refuses_an_unsatisfiable_wp_neighbor_and_late_ground_conjunct() {
    for (label, input) in FIXTURES {
        let mut exec = loaded(input);
        exec.execute_all(&ay_frontend::parse("(assert false)").unwrap())
            .unwrap();
        assert!(
            certify(&mut exec).is_none(),
            "{label}: no conjunct may be omitted"
        );
    }
}

#[test]
fn theory_program_refuses_a_universal_its_candidate_does_not_satisfy() {
    let mut exec = loaded(
        "(set-logic ALL)
        (declare-fun member ((Seq Int) Int) Bool)
        (assert (forall ((a (Seq Int)) (x Int)) (not (member a x))))",
    );
    let roots = exec.ctx.assertions.clone();
    let deadline = ay_core::time::Instant::now()
        + std::time::Duration::from_millis(CONST_INTERP_CERT_BUDGET_MS);
    assert!(
        exec.theory_program_interp_certificate(
            &roots,
            LogicCategory::Auflia,
            ConstInterpCertMode::On,
            deadline,
            &mut HashMap::default()
        )
        .is_none(),
        "the native membership guess is not authority for a different satisfying interpretation"
    );
    assert!(exec.const_interp_cert_witness_state.is_none());
}

#[test]
fn theory_program_cannot_enter_after_the_original_absolute_deadline() {
    let mut exec = loaded(FIXTURES[0].1);
    let roots = exec.ctx.assertions.clone();
    let before = exec.ctx.terms.len();
    let expired = ay_core::time::Instant::now() - std::time::Duration::from_secs(1);
    exec.set_solve_controls(None, Some(expired));
    let local = ay_core::time::Instant::now()
        + std::time::Duration::from_millis(CONST_INTERP_CERT_BUDGET_MS);
    assert!(exec
        .theory_program_interp_certificate(
            &roots,
            LogicCategory::Auflia,
            ConstInterpCertMode::On,
            local,
            &mut HashMap::default()
        )
        .is_none());
    assert_eq!(
        exec.ctx.terms.len(),
        before,
        "the local slice must not renew the expired original grant"
    );
    assert!(exec.const_interp_cert_witness_state.is_none());
}
