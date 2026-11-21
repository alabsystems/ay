// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_frontend::command::Term as Parsed;

#[path = "numeric_table_tests.rs"]
mod numeric_tables;

#[path = "integer_euf_tests.rs"]
mod integer_euf;

#[path = "projection_tests.rs"]
mod projection;

#[path = "conjunct_tests.rs"]
mod conjuncts;

#[path = "boolean_conjunct_tests.rs"]
mod boolean_conjuncts;

#[path = "subset_tests.rs"]
mod subsets;

fn diagnostic_flags() -> ay_core::misc_test_override::Guard {
    ay_core::misc_test_override::set(ay_core::debug_channel::misc_cli_flags_with(|flags| {
        flags.trace_cegqi_attr = true;
        flags.probe_cert_reject = true;
    }))
}

fn marker() -> Parsed {
    Parsed::Symbol(crate::executor::NATIVE_API_ASSERTION_PLACEHOLDER.to_owned())
}

struct Fixture {
    exec: Executor,
    source: TermId,
    targets: [TermId; 3],
    pin: TermId,
}

/// Exact shapes 220 and 245/246/247 from the captured QMC counterexample
/// query. The quotient table is the constant zero and the Mapping table is
/// `ite(c=map && z=0,1,0)`. All variables retain their original typed roles.
fn fixture() -> Fixture {
    let mut exec = Executor::new();
    exec.set_produce_proofs(true);
    let t = &mut exec.ctx.terms;
    let mapping = Sort::Uninterpreted("Mapping".to_owned());
    let c = t.mk_var("c", mapping.clone());
    let map = t.mk_var("map", mapping);
    let z = t.mk_var("z", Sort::Int);
    let zero = t.mk_int(0.into());
    let one = t.mk_int(1.into());
    let minus_two = t.mk_int((-2).into());
    let product = t.mk_app(Symbol::named("*"), [zero, minus_two], Sort::Int);
    let sum = t.mk_app(Symbol::named("+"), [z, product], Sort::Int);
    let pin = t.mk_app(Symbol::named("="), [c, map], Sort::Bool);
    let a = t.mk_app(Symbol::named("="), [zero, sum], Sort::Bool);
    let b = t.mk_app(Symbol::named("="), [zero, z], Sort::Bool);
    assert_ne!(
        a, b,
        "the captured unsimplified arithmetic guard must survive"
    );
    let guard = t.mk_app(Symbol::named("and"), [pin, b], Sort::Bool);
    let table = t.mk_ite_raw(guard, one, zero);
    let eq_one = t.mk_app(Symbol::named("="), [one, table], Sort::Bool);
    let eq_zero = t.mk_app(Symbol::named("="), [zero, table], Sort::Bool);
    let not_one = t.mk_not_raw(eq_one);
    let not_zero = t.mk_not_raw(eq_zero);
    let source = t.mk_ite_raw(a, not_one, not_zero);
    let not_pin = t.mk_not_raw(pin);
    let not_a = t.mk_not_raw(a);
    let not_b = t.mk_not_raw(b);
    let prefix = t.mk_app(Symbol::named("or"), [not_pin, not_b], Sort::Bool);
    let first = t.mk_app(Symbol::named("or"), [prefix, not_a], Sort::Bool);
    let second = t.mk_app(Symbol::named("or"), [a, guard], Sort::Bool);
    let third = t.mk_app(Symbol::named("or"), [not_pin, guard, not_b], Sort::Bool);
    assert_eq!(
        collect_ite_sites(t, source).unwrap().len(),
        1,
        "retain the actual captured Int ITE"
    );
    Fixture {
        exec,
        source,
        targets: [first, second, third],
        pin,
    }
}

pub(super) fn begin(exec: &mut Executor, roots: &[TermId], native: bool) {
    for &root in roots {
        if native {
            exec.ctx.add_native_assertion_with_parsed(root, marker());
        } else {
            exec.ctx.add_assertion_with_parsed(root, marker());
        }
    }
    exec.begin_public_solve(false);
    exec.bind_unsat_query_assumptions(&[]);
}

fn closed_trust(exec: &mut Executor, target: TermId) -> (Proof, TermId) {
    let negated = exec.ctx.terms.mk_not_raw(target);
    let mut proof = Proof::new();
    let trusted = proof.add_rule_step(AletheRule::Trust, vec![target], Vec::new(), Vec::new());
    let assumption = proof.add_assume(negated, None);
    proof.add_resolution(Vec::new(), target, trusted, assumption);
    (proof, negated)
}

#[test]
fn native_ite_clausification_derives_all_three_captured_consequences() {
    let _diagnostics = diagnostic_flags();
    for position in 0..3 {
        let mut f = fixture();
        let (mut proof, negated) = closed_trust(&mut f.exec, f.targets[position]);
        let mut roots = vec![f.source, negated];
        if position == 0 {
            roots.push(f.source);
        }
        begin(&mut f.exec, &roots, true);
        assert!(
            f.exec.try_rebuild_native_ite_clausification(&mut proof),
            "target {position}: {proof:?}"
        );
        assert!(f
            .exec
            .check_proof_strict_with_datatypes(&proof)
            .is_ok_and(|q| q.is_complete()));
        assert!(ay_proof::validate_reachable_assumes_in_problem_scope(&proof, &roots).is_ok());
        assert!(proof.steps.iter().all(|step| !matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::Trust | AletheRule::Hole,
                ..
            }
        )));
        assert!(proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::IteIntro,
                ..
            }
        )));
    }
}

#[test]
fn native_ite_clausification_admits_supported_sources_with_irrelevant_universals_and_duplicates() {
    let mut f = fixture();
    let (mut proof, negated) = closed_trust(&mut f.exec, f.targets[0]);
    let t = &mut f.exec.ctx.terms;
    let bound = t.mk_var("irrelevant_bound", Sort::Int);
    let reflexive = t.mk_app(Symbol::named("="), [bound, bound], Sort::Bool);
    let universal = t.mk_forall(vec![("irrelevant_bound".to_owned(), Sort::Int)], reflexive);
    let mut roots = vec![universal, negated];
    roots.extend(std::iter::repeat(f.source).take(MAX_NATIVE_ATTEMPTS + 1));
    begin(&mut f.exec, &roots, true);
    assert_eq!(
        select_ite_sources(&f.exec, &roots, &RepairBudget::new(&f.exec))
            .unwrap()
            .iter()
            .map(|source| source.plan.source)
            .collect::<Vec<_>>(),
        vec![f.source]
    );
    assert!(f.exec.try_rebuild_native_ite_clausification(&mut proof));
    assert_eq!(f.exec.proof_original_problem_assertions_slice(), roots);
    assert!(f
        .exec
        .ctx
        .native_authored_originals_match_bounded(&roots, MAX_NATIVE_ROOTS));
    assert!(ay_proof::validate_reachable_assumes_in_problem_scope(&proof, &roots).is_ok());
    assert!(f
        .exec
        .check_proof_strict_with_datatypes(&proof)
        .is_ok_and(|quality| quality.is_complete()));
}

#[test]
fn native_ite_clausification_source_subset_cannot_authorize_foreign_assumptions() {
    for include_foreign in [true, false] {
        let mut f = fixture();
        let (mut proof, negated) = closed_trust(&mut f.exec, f.targets[0]);
        let empty = ay_core::ProofId(u32::try_from(proof.steps.len() - 1).unwrap());
        let foreign = f.exec.ctx.terms.mk_var("foreign", Sort::Bool);
        let not_foreign = f.exec.ctx.terms.mk_not_raw(foreign);
        let weakened = proof.add_rule_step(
            AletheRule::Weakening,
            vec![not_foreign],
            vec![empty],
            Vec::new(),
        );
        let assumption = proof.add_assume(foreign, None);
        proof.add_resolution(Vec::new(), foreign, assumption, weakened);
        let mut roots = vec![f.source, negated, f.source];
        if include_foreign {
            roots.push(foreign);
        }
        begin(&mut f.exec, &roots, true);
        let original = proof.clone();
        assert_eq!(
            f.exec.try_rebuild_native_ite_clausification(&mut proof),
            include_foreign,
            "foreign assumption admitted={include_foreign}"
        );
        if include_foreign {
            assert!(ay_proof::validate_reachable_assumes_in_problem_scope(&proof, &roots).is_ok());
        } else {
            assert_eq!(proof, original);
        }
    }
}

#[test]
fn native_ite_clausification_source_scans_share_the_original_occurrence_limit() {
    let mut f = fixture();
    let t = &mut f.exec.ctx.terms;
    let first = t.mk_var("first", Sort::Bool);
    let second = t.mk_var("second", Sort::Bool);
    let mut roots = Vec::new();
    for width in 1..=63 {
        let mut args = vec![first; 64];
        args[width] = second;
        roots.push(t.mk_app(Symbol::named("and"), args, Sort::Bool));
    }
    roots.push(f.source);
    assert_eq!(roots.len(), MAX_NATIVE_ROOTS);
    assert!(select_ite_sources(&f.exec, &roots, &RepairBudget::new(&f.exec)).is_none());
    assert_eq!(
        select_ite_sources(&f.exec, &[f.source; 64], &RepairBudget::new(&f.exec))
            .unwrap()
            .iter()
            .map(|source| source.plan.source)
            .collect::<Vec<_>>(),
        vec![f.source]
    );
}

#[test]
fn native_ite_clausification_refuses_forged_source_polarity_and_branch() {
    for mutation in 0..3 {
        let mut f = fixture();
        let target = f.targets[0];
        let (mut proof, negated) = closed_trust(&mut f.exec, target);
        let original = proof.clone();
        let source = match mutation {
            0 => f.pin,
            1 => f.exec.ctx.terms.mk_not_raw(f.source),
            _ => {
                let TermData::Ite(cond, left, right) = *f.exec.ctx.terms.get(f.source) else {
                    unreachable!()
                };
                f.exec.ctx.terms.mk_ite_raw(cond, right, left)
            }
        };
        begin(&mut f.exec, &[source, negated], true);
        assert!(
            !f.exec.try_rebuild_native_ite_clausification(&mut proof),
            "mutation {mutation}"
        );
        assert_eq!(proof, original);
    }
}

#[test]
fn native_ite_clausification_text_placeholder_is_not_native_authority() {
    let mut f = fixture();
    let (mut proof, negated) = closed_trust(&mut f.exec, f.targets[0]);
    let original = proof.clone();
    begin(&mut f.exec, &[f.source, negated], false);
    assert!(f
        .exec
        .ctx
        .native_authored_assertion_terms_aligned_bounded(64)
        .is_none());
    assert!(!f.exec.try_rebuild_native_ite_clausification(&mut proof));
    assert_eq!(proof, original);
}

#[test]
fn native_ite_clausification_installer_preserves_occurrences_and_epoch() {
    let mut f = fixture();
    let ordered = [f.source, f.pin, f.source];
    let ctx = f.exec.isolated_probe_context(&ordered).unwrap();
    assert_eq!(
        ctx.native_authored_assertion_terms_aligned_bounded(3)
            .unwrap(),
        ordered
    );
    for mutation in 0..3 {
        let mut f = fixture();
        let (mut proof, negated) = closed_trust(&mut f.exec, f.targets[0]);
        begin(&mut f.exec, &[f.source, negated], true);
        match mutation {
            0 => f
                .exec
                .proof_problem_assertion_provenance
                .as_mut()
                .unwrap()
                .original_problem_assertions
                .swap(0, 1),
            1 => f
                .exec
                .ctx
                .add_native_assertion_with_parsed(f.source, marker()),
            _ => {
                f.exec
                    .execute_all(&ay_frontend::parse("(push 1)(pop 1)").unwrap())
                    .unwrap();
            }
        }
        let original = proof.clone();
        assert!(!f.exec.try_rebuild_native_ite_clausification(&mut proof));
        assert_eq!(proof, original);
    }
}

#[test]
fn native_ite_clausification_uses_frozen_original_after_working_rewrite() {
    let mut f = fixture();
    let (mut proof, negated) = closed_trust(&mut f.exec, f.targets[0]);
    let roots = [f.source, negated, f.source];
    begin(&mut f.exec, &roots, true);
    f.exec.ctx.assertions.clear();
    f.exec.ctx.assertions.push(f.exec.ctx.terms.true_term());
    assert!(f
        .exec
        .ctx
        .native_authored_assertion_terms_aligned_bounded(64)
        .is_none());
    assert!(f.exec.try_rebuild_native_ite_clausification(&mut proof));
    assert!(ay_proof::validate_reachable_assumes_in_problem_scope(&proof, &roots).is_ok());
    assert!(f
        .exec
        .check_proof_strict_with_datatypes(&proof)
        .is_ok_and(|quality| quality.is_complete()));
}

#[test]
fn native_ite_clausification_raw_dag_and_payload_controls() {
    let mut f = fixture();
    let missing = TermId(u32::MAX);
    assert!(admit_terms(&f.exec, &[missing]).is_none());
    let huge = f.exec.ctx.terms.mk_var(&"x".repeat(257), Sort::Int);
    assert!(admit_terms(&f.exec, &[huge]).is_none());
    let boolean = f.exec.ctx.terms.true_term();
    let malformed = f
        .exec
        .ctx
        .terms
        .mk_app(Symbol::named("+"), [boolean], Sort::Int);
    assert!(admit_terms(&f.exec, &[malformed]).is_none());
    let mut deep = f.pin;
    for _ in 0..70 {
        deep = f.exec.ctx.terms.mk_not_raw(deep);
    }
    assert!(admit_terms(&f.exec, &[deep]).is_none());
    let mut wide = f.pin;
    for _ in 0..13 {
        wide = f
            .exec
            .ctx
            .terms
            .mk_app(Symbol::named("and"), [wide, wide], Sort::Bool);
    }
    assert!(admit_terms(&f.exec, &[wide]).is_none());
    let future = TermId(u32::try_from(f.exec.ctx.terms.len()).unwrap());
    let cyclic = f
        .exec
        .ctx
        .terms
        .mk_app(Symbol::named("+"), [future], Sort::Int);
    assert_eq!(cyclic, future);
    assert!(admit_terms(&f.exec, &[cyclic]).is_none());
    let future = TermId(u32::try_from(f.exec.ctx.terms.len() + 1).unwrap());
    let forward = f
        .exec
        .ctx
        .terms
        .mk_app(Symbol::named("+"), [future], Sort::Int);
    let later = f.exec.ctx.terms.mk_var("later", Sort::Int);
    assert_eq!(later, future);
    assert!(
        admit_terms(&f.exec, &[forward]).is_none(),
        "a resolved forward reference is still not an admitted source DAG"
    );

    let mut proof = Proof::new();
    proof.add_rule_step(
        AletheRule::Custom("x".repeat(MAX_NATIVE_PAYLOAD + 1)),
        vec![f.pin],
        Vec::new(),
        Vec::new(),
    );
    assert!(admit_proof_copy(&proof).is_none());
    let mut proof = Proof::new();
    proof.add_theory_lemma_with_farkas_and_kind(
        "lra",
        vec![f.pin],
        FarkasAnnotation::from_ints(&[i64::MAX]),
        TheoryLemmaKind::LraFarkas,
    );
    assert!(
        admit_proof_copy(&proof).is_some(),
        "Rational64 magnitude is inline, not an owned BigInt"
    );
    proof.add_theory_lemma_with_farkas_and_kind(
        "lra",
        vec![f.pin],
        FarkasAnnotation::from_ints(&vec![1; MAX_NATIVE_PAYLOAD + 1]),
        TheoryLemmaKind::LraFarkas,
    );
    assert!(
        admit_proof_copy(&proof).is_none(),
        "even an unused hint vector is charged"
    );
    let sort = Sort::Uninterpreted("S".repeat(257));
    let opaque = f.exec.ctx.terms.mk_var("opaque", sort);
    let outer = f
        .exec
        .ctx
        .terms
        .mk_app(Symbol::named("unregistered"), [opaque], Sort::Int);
    assert!(
        admit_terms(&f.exec, &[outer]).is_none(),
        "raw argument sort refuses before signature cloning"
    );
}

#[test]
fn native_ite_clausification_cancelled_query_does_not_mutate_proof() {
    let mut f = fixture();
    let (mut proof, negated) = closed_trust(&mut f.exec, f.targets[0]);
    begin(&mut f.exec, &[f.source, negated], true);
    f.exec
        .set_interrupt(std::sync::Arc::new(std::sync::atomic::AtomicBool::new(
            true,
        )));
    let original = proof.clone();
    assert!(!f.exec.try_rebuild_native_ite_clausification(&mut proof));
    assert_eq!(proof, original);
}

#[test]
fn native_ite_clausification_honors_smaller_caller_proof_budget() {
    for budget in [0, 1] {
        let mut f = fixture();
        let (mut proof, negated) = closed_trust(&mut f.exec, f.targets[0]);
        begin(&mut f.exec, &[f.source, negated], true);
        f.exec.proof_reconstruction_step_budget = Some(budget);
        let original = proof.clone();
        assert!(!f.exec.try_rebuild_native_ite_clausification(&mut proof));
        assert_eq!(proof, original);
    }
}

pub(super) fn external_check(tag: &str, problem: &str, proof: &str) -> String {
    ay_core::pinned_carcara::pinned_carcara_can_judge(problem, proof)
        .expect("the external checker can judge this exact document");
    let base = std::env::temp_dir().join(format!("ay-native-ite-{}-{tag}", std::process::id()));
    let smt = base.with_extension("smt2");
    let alethe = base.with_extension("alethe");
    std::fs::write(&smt, problem).unwrap();
    std::fs::write(&alethe, proof).unwrap();
    let result = std::process::Command::new("carcara")
        .arg("check")
        .arg(&alethe)
        .arg(&smt)
        .output()
        .expect("Carcara is required for this integration control");
    let output = String::from_utf8_lossy(&result.stdout).trim().to_owned();
    if !result.status.success() {
        // Carcara writes `invalid` to stdout and the actual rule/premise
        // mismatch to stderr. Preserve both so a source-forgery regression
        // cannot pass merely because an unrelated command failed.
        return format!(
            "{output}\n{}\nexternal-check-exit={}",
            String::from_utf8_lossy(&result.stderr),
            result.status
        );
    }
    if output.lines().last() == Some("valid") && !tag.starts_with("forged") {
        let _ = std::fs::remove_file(&smt);
        let _ = std::fs::remove_file(&alethe);
    }
    output
}

#[test]
fn native_ite_clausification_whole_carcara_and_forged_source() {
    for position in 0..3 {
        let mut f = fixture();
        let (mut proof, negated) = closed_trust(&mut f.exec, f.targets[position]);
        let roots = [f.source, negated];
        begin(&mut f.exec, &roots, true);
        assert!(f.exec.try_rebuild_native_ite_clausification(&mut proof));
        let document = ay_proof::try_export_alethe_with_problem_scope_and_overrides(
            &proof,
            &f.exec.ctx.terms,
            &roots,
            None,
        )
        .expect("strict native derivation exports");
        let source = ay_proof::format_term_alethe(&f.exec.ctx.terms, f.source);
        let other = ay_proof::format_term_alethe(&f.exec.ctx.terms, negated);
        let prefix = "(set-logic QF_UFLIA)\n(declare-sort Mapping 0)\n(declare-const c Mapping)\n(declare-const map Mapping)\n(declare-const z Int)\n";
        let problem = format!("{prefix}(assert {source})\n(assert {other})\n(check-sat)\n");
        assert_eq!(
            external_check(&format!("shipped-{position}"), &problem, &document)
                .lines()
                .last(),
            Some("valid")
        );
        if position == 0 {
            let forged =
                format!("{prefix}(assert (not {source}))\n(assert {other})\n(check-sat)\n");
            assert_ne!(
                external_check("forged-source", &forged, &document)
                    .lines()
                    .last(),
                Some("valid")
            );
        }
    }
}

#[test]
fn native_ite_clausification_captured_outer_sat_inputs_never_gain_unsat_authority() {
    for text in [
        include_str!("adds-two-original31.native.json"),
        include_str!("adds-two-forall-five.native.json"),
    ] {
        let artifact = crate::api::NativeReplayArtifact::from_json_str(text).unwrap();
        assert_eq!(artifact.timeout_ms, Some(5624));
        let (details, proof) =
            crate::api::Solver::replay_native_replay_artifact_with_checked_proof(
                &artifact,
                std::time::Duration::from_millis(5624),
            )
            .unwrap();
        assert!(
            !details.result.is_unsat(),
            "independently SAT original input cannot acquire UNSAT authority: {details:?}"
        );
        assert!(proof.is_none());
    }
}

#[test]
fn native_ite_clausification_actual_isolated_counterexample_probe_and_sat_twins() {
    let _diagnostics = diagnostic_flags();
    use crate::executor::quantifier_loop::result_mapping::CheckedGroundDecision;
    use crate::executor::unsat_cert::ProbeUnsatAuthority;
    for cores in [false, true] {
        for variant in 0..3 {
            let mut f = fixture();
            if cores {
                f.exec
                    .execute_all(
                        &ay_frontend::parse("(set-option :produce-unsat-cores true)").unwrap(),
                    )
                    .unwrap();
            }
            let TermData::App(_, args) = f.exec.ctx.terms.get(f.pin) else {
                unreachable!()
            };
            let c = args[0];
            let after = f
                .exec
                .ctx
                .terms
                .mk_var("after", Sort::Uninterpreted("Mapping".to_owned()));
            let after_pin = f.exec.ctx.terms.mk_eq(c, after);
            let roots = match variant {
                0 => vec![f.pin, after_pin, f.source],
                1 => vec![f.exec.ctx.terms.mk_not_raw(f.pin), after_pin, f.source],
                _ => vec![f.pin, after_pin, f.exec.ctx.terms.mk_not_raw(f.source)],
            };
            // This is the actual QMC producer, not a manually repaired test proof.
            // A 200ms diagnostic allowance is below the ordinary QMC sub-solve
            // ceiling (2s); it makes no claim about the old trace's remaining time.
            let (decision, authority) = f
                .exec
                .checked_model_check_solve_classified(roots.clone(), 200)
                .expect("the exact ground QMC probe must have a checked decision");
            assert_eq!(authority, ProbeUnsatAuthority::Checked);
            match decision {
                CheckedGroundDecision::Unsat(checked) => {
                    assert_eq!(variant, 0, "SAT twin cannot acquire UNSAT authority");
                    assert!(checked.consume(&mut f.exec, &roots));
                }
                CheckedGroundDecision::Sat(checked) => {
                    assert_ne!(variant, 0);
                    assert!(checked.consume(&mut f.exec, &roots));
                }
            }
        }
    }
}
