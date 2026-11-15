// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Guard-removal and mutation tests for the lifted-assertion promoter
//! (#probe-ite-lift-promoter).
//!
//! The fixture is the measured AUFDTLIRA `P630-039` ground-core leaf with
//! its uninterpreted bounds kept uninterpreted (`(f b)`, `(g b)` stand for
//! `(integerqtint (first b!rt))` and `(integerqtint (last b!rt))`), so the
//! closer's LRA oracle can see none of the atoms and every arithmetic fact
//! has to come from the seeded, checker-verified leaves.

use super::*;
use num_bigint::BigInt;

/// `(or (not (<= -2147483648 x)) (not (<= x 2147483647)))` with
/// `x = (ite (<= (f b) (g b)) (+ (g b) (- (f b)) 1) 0)`, plus the raw
/// negation of its lift, as a two-assertion probe.
struct RangeCheckFixture {
    exec: Executor,
    source: TermId,
    lifted: TermId,
    not_lifted: TermId,
}

fn range_check_fixture() -> RangeCheckFixture {
    let mut exec = Executor::new();
    let terms = &mut exec.ctx.terms;
    let b = terms.mk_var("b", Sort::Int);
    let first = terms.mk_app(Symbol::named("f"), [b], Sort::Int);
    let last = terms.mk_app(Symbol::named("g"), [b], Sort::Int);
    let cond = terms.mk_le(first, last);
    let one = terms.mk_int(BigInt::from(1));
    let zero = terms.mk_int(BigInt::from(0));
    let neg_first = terms.mk_neg(first);
    let length = terms.mk_add(vec![last, neg_first, one]);
    let ite = terms.mk_ite(cond, length, zero);
    assert!(
        matches!(terms.get(ite), TermData::Ite(..)),
        "the fixture needs a live term-level ite"
    );
    let low = terms.mk_int(BigInt::from(-2_147_483_648_i64));
    let high = terms.mk_int(BigInt::from(2_147_483_647_i64));
    let lower_bound = terms.mk_le(low, ite);
    let upper_bound = terms.mk_le(ite, high);
    let not_lower = terms.mk_not(lower_bound);
    let not_upper = terms.mk_not(upper_bound);
    let source = terms.mk_or(vec![not_lower, not_upper]);
    let lifted = terms.lift_arithmetic_ite(source);
    assert_ne!(lifted, source, "the lift must rewrite the assertion");
    assert!(
        !contains_non_bool_ite(terms, lifted),
        "the lift must eliminate the term-level ite"
    );
    let not_lifted = terms.mk_not_raw(lifted);
    // The probe's exact assertion vector: the strict checker authorizes an
    // `assume` only against it.
    exec.ctx.assertions.push(source);
    exec.ctx.assertions.push(not_lifted);
    RangeCheckFixture {
        exec,
        source,
        lifted,
        not_lifted,
    }
}

/// The probe proof the tracker leaves behind: the lifted assertion as a
/// premiseless trust unit, resolved against the assumed negation.
fn trust_closed_proof(fixture: &RangeCheckFixture) -> Proof {
    let mut proof = Proof::new();
    let trust = proof.add_rule_step(
        AletheRule::Trust,
        vec![fixture.lifted],
        Vec::new(),
        Vec::new(),
    );
    let negated = proof.add_assume(fixture.not_lifted, None);
    proof.add_resolution(Vec::new(), fixture.lifted, trust, negated);
    proof
}

fn count_rule(proof: &Proof, predicate: impl Fn(&AletheRule) -> bool) -> usize {
    proof
        .steps
        .iter()
        .filter(|step| matches!(step, ProofStep::Step { rule, .. } if predicate(rule)))
        .count()
}

fn has_trust(proof: &Proof) -> bool {
    proof.steps.iter().any(|step| {
        matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::Trust,
                ..
            }
        ) || matches!(step, ProofStep::TheoryLemma { kind, .. } if kind.is_trust())
    })
}

#[test]
fn the_lifted_range_check_leaf_is_derived_and_strict_checked() {
    let mut fixture = range_check_fixture();
    let assertions = [fixture.source, fixture.not_lifted];
    let mut proof = trust_closed_proof(&fixture);

    fixture
        .exec
        .promote_consequence_probe_ite_lift_trust_leaves(&mut proof, &assertions);

    assert!(
        !has_trust(&proof),
        "the lifted leaf must be derived, not trusted: {proof:?}"
    );
    assert!(
        count_rule(&proof, |rule| matches!(rule, AletheRule::IteIntro)) >= 1,
        "the branch equalities come from ite_intro"
    );
    assert!(
        count_rule(&proof, |rule| matches!(rule, AletheRule::EqCongruentPred)) >= 1,
        "the atoms transfer across the branch equality by predicate congruence"
    );
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::LraFarkas | TheoryLemmaKind::LiaGeneric,
                farkas: Some(_),
                clause,
                ..
            } if clause.len() == 1
        )),
        "the folded-away else-branch bound must be re-established by a verified unit"
    );
    assert!(matches!(
        proof.steps.last(),
        Some(ProofStep::Resolution { clause, .. }) if clause.is_empty()
    ));
    let strict = fixture.exec.check_proof_strict_with_datatypes(&proof);
    assert!(
        strict.as_ref().is_ok_and(|quality| quality.is_complete()),
        "the rebuilt probe proof must be strict-complete: {strict:?}"
    );
    assert!(
        ay_proof::validate_reachable_assumes_in_problem_scope(&proof, &assertions).is_ok(),
        "the rebuilt proof may assume only the exact probe assertions"
    );
}

/// GUARD-REMOVAL PROOF for the kill switch: with
/// `--no-probe-ite-lift-promoter` the probe proof is byte-identical.
#[test]
fn the_kill_switch_leaves_the_probe_proof_byte_identical() {
    let off = ay_core::MiscCliFlags {
        no_probe_ite_lift_promoter: true,
        ..Default::default()
    };
    let _guard = ay_core::misc_test_override::set(off);
    let mut fixture = range_check_fixture();
    let assertions = [fixture.source, fixture.not_lifted];
    let mut proof = trust_closed_proof(&fixture);
    let before = format!("{proof:?}");
    fixture
        .exec
        .promote_consequence_probe_ite_lift_trust_leaves(&mut proof, &assertions);
    assert_eq!(format!("{proof:?}"), before);
    assert!(has_trust(&proof));
}

/// GUARD-REMOVAL PROOF for the parent switch: `--no-consequence-replay`
/// disables this pass too.
#[test]
fn the_parent_consequence_replay_switch_also_disables_the_promoter() {
    let off = ay_core::MiscCliFlags {
        no_consequence_replay: true,
        ..Default::default()
    };
    let _guard = ay_core::misc_test_override::set(off);
    let mut fixture = range_check_fixture();
    let assertions = [fixture.source, fixture.not_lifted];
    let mut proof = trust_closed_proof(&fixture);
    let before = format!("{proof:?}");
    fixture
        .exec
        .promote_consequence_probe_ite_lift_trust_leaves(&mut proof, &assertions);
    assert_eq!(format!("{proof:?}"), before);
}

/// A trust term that is NOT the lift of any probe assertion is left alone:
/// recognition is the lifter, not a shape match.
#[test]
fn a_trust_term_that_is_not_the_lift_of_an_assertion_stays_trusted() {
    let mut fixture = range_check_fixture();
    // Forge: the lift of a DIFFERENT assertion (upper bound 2147483646).
    let terms = &mut fixture.exec.ctx.terms;
    let TermData::App(_, disjuncts) = terms.get(fixture.source).clone() else {
        panic!("the source is a disjunction");
    };
    let not_upper = disjuncts[1];
    let TermData::Not(upper_bound) = terms.get(not_upper).clone() else {
        panic!("the second disjunct is a negated bound");
    };
    let TermData::App(_, bound_args) = terms.get(upper_bound).clone() else {
        panic!("the bound is a comparison");
    };
    let ite = bound_args[0];
    let forged_high = terms.mk_int(BigInt::from(2_147_483_646_i64));
    let forged_upper = terms.mk_le(ite, forged_high);
    let forged_not_upper = terms.mk_not(forged_upper);
    let forged_source = terms.mk_or(vec![disjuncts[0], forged_not_upper]);
    let forged_lift = terms.lift_arithmetic_ite(forged_source);
    assert_ne!(forged_lift, fixture.lifted);
    let forged_not_lift = terms.mk_not_raw(forged_lift);
    fixture.exec.ctx.assertions.push(forged_not_lift);

    let assertions = [fixture.source, forged_not_lift];
    let mut proof = Proof::new();
    let trust = proof.add_rule_step(AletheRule::Trust, vec![forged_lift], Vec::new(), Vec::new());
    let negated = proof.add_assume(forged_not_lift, None);
    proof.add_resolution(Vec::new(), forged_lift, trust, negated);
    let before = format!("{proof:?}");

    fixture
        .exec
        .promote_consequence_probe_ite_lift_trust_leaves(&mut proof, &assertions);

    assert_eq!(
        format!("{proof:?}"),
        before,
        "a forged lift must not be derived from an assertion it is not the lift of"
    );
}

/// MUTATION DIFFERENTIAL on the checker: forging any seeded leaf of the
/// derivation makes the strict check refuse the proof. Two leaves are
/// forged: the Farkas-verified evaluation unit is flipped to its negation,
/// and one EUF transfer lemma loses its branch-equality hypothesis.
#[test]
fn the_checker_refuses_a_forged_seeded_leaf() {
    let mut fixture = range_check_fixture();
    let assertions = [fixture.source, fixture.not_lifted];
    let mut proof = trust_closed_proof(&fixture);
    fixture
        .exec
        .promote_consequence_probe_ite_lift_trust_leaves(&mut proof, &assertions);
    assert!(!has_trust(&proof));
    assert!(fixture
        .exec
        .check_proof_strict_with_datatypes(&proof)
        .is_ok_and(|quality| quality.is_complete()));

    // (a) Flip the evaluation unit `(cl (<= -2147483648 0))` to its negation.
    let unit_index = proof
        .steps
        .iter()
        .position(|step| {
            matches!(
                step,
                ProofStep::TheoryLemma {
                    farkas: Some(_),
                    clause,
                    ..
                } if clause.len() == 1
            )
        })
        .expect("the derivation seeds a verified evaluation unit");
    let mut forged = proof.clone();
    if let ProofStep::TheoryLemma { clause, .. } = &mut forged.steps[unit_index] {
        let literal = clause[0];
        clause[0] = fixture.exec.ctx.terms.mk_not_raw(literal);
    }
    let strict = fixture.exec.check_proof_strict_with_datatypes(&forged);
    assert!(
        !strict.is_ok_and(|quality| quality.is_complete()),
        "a flipped evaluation unit must be refused"
    );

    // (b) Drop the branch-equality hypothesis from an EUF transfer lemma.
    let transfer_index = proof
        .steps
        .iter()
        .position(|step| {
            matches!(
                step,
                ProofStep::Step {
                    rule: AletheRule::EqCongruentPred,
                    ..
                }
            )
        })
        .expect("the derivation seeds a predicate-congruence transfer");
    let mut forged = proof.clone();
    if let ProofStep::Step { clause, .. } = &mut forged.steps[transfer_index] {
        let hypothesis = clause
            .iter()
            .position(|&literal| {
                matches!(
                    fixture.exec.ctx.terms.get(literal),
                    TermData::Not(inner)
                        if matches!(
                            fixture.exec.ctx.terms.get(*inner),
                            TermData::App(Symbol::Named(name), _) if name == "="
                        )
                )
            })
            .expect("the transfer carries a negated equality hypothesis");
        let _ = clause.remove(hypothesis);
    }
    let strict = fixture.exec.check_proof_strict_with_datatypes(&forged);
    assert!(
        !strict.is_ok_and(|quality| quality.is_complete()),
        "a transfer without its hypothesis must be refused"
    );
}

/// END-TO-END external validation: the rebuilt probe proof, printed over
/// the exact probe assertions, is accepted by the pinned external checker.
/// Skipped (never silently green) when carcara is not installed.
#[test]
fn carcara_accepts_the_promoted_derivation() {
    let Some(carcara) = find_carcara() else {
        assert!(
            std::env::var_os("CI").is_none(),
            "carcara is mandatory in CI for the lifted-assertion external test"
        );
        eprintln!("carcara not found; skipping lifted-assertion external test");
        return;
    };
    let mut fixture = range_check_fixture();
    let assertions = [fixture.source, fixture.not_lifted];
    let mut proof = trust_closed_proof(&fixture);
    fixture
        .exec
        .promote_consequence_probe_ite_lift_trust_leaves(&mut proof, &assertions);
    assert!(!has_trust(&proof));

    let terms = &fixture.exec.ctx.terms;
    let rendered = ay_proof::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        terms,
        &assertions,
        None,
    )
    .expect("the promoted proof exports fallibly");
    assert!(!rendered.contains(":rule trust"), "{rendered}");
    assert!(!rendered.contains(":rule hole"), "{rendered}");
    let problem = format!(
        "(set-logic QF_UFLIA)\n(declare-fun b () Int)\n(declare-fun f (Int) Int)\n\
         (declare-fun g (Int) Int)\n(assert {})\n(assert {})\n(check-sat)\n",
        ay_proof::format_term_alethe(terms, fixture.source),
        ay_proof::format_term_alethe(terms, fixture.not_lifted),
    );

    let verdict = carcara_verdict(&carcara, "shipped", &problem, &rendered);
    assert_eq!(
        verdict.0, "valid",
        "carcara rejected the promoted derivation: {}",
        verdict.1
    );

    // MUTATION DIFFERENTIAL on the printed text: the external accept is
    // evidence only if the seeded leaves are load-bearing there too.
    // (a) The evaluation unit `(cl (<= (- 2147483648) 0))` becomes a false
    //     statement of the same shape.
    let evaluation_line = rendered
        .lines()
        .find(|line| {
            line.contains(":rule la_generic") && line.contains("(cl (<= (- 2147483648) 0))")
        })
        .expect("the document carries the folded else-branch bound as an la_generic unit");
    let forged_evaluation = rendered.replace(
        evaluation_line,
        &evaluation_line.replace("(cl (<= (- 2147483648) 0))", "(cl (<= 0 (- 2147483648)))"),
    );
    assert_ne!(forged_evaluation, rendered);
    let verdict = carcara_verdict(&carcara, "forged_evaluation", &problem, &forged_evaluation);
    assert_ne!(
        verdict.0, "valid",
        "carcara must refuse a flipped evaluation unit: {}",
        verdict.1
    );
    // (b) The `ite_intro` step is deleted: every branch equality then rests
    //     on an undefined premise.
    let intro_line = rendered
        .lines()
        .find(|line| line.contains(":rule ite_intro"))
        .expect("the document carries the ite_intro step");
    let forged_intro = rendered.replace(intro_line, "");
    let verdict = carcara_verdict(&carcara, "forged_intro", &problem, &forged_intro);
    assert_ne!(
        verdict.0, "valid",
        "carcara must refuse a derivation without its ite_intro: {}",
        verdict.1
    );
}

/// `(first stdout line, diagnostics)`; artifacts are kept only on an
/// unexpected outcome (a rejected shipped document, or an accepted mutant).
fn carcara_verdict(
    carcara: &std::path::Path,
    tag: &str,
    problem: &str,
    proof: &str,
) -> (String, String) {
    if let Err(misjudged) = ay_core::pinned_carcara::pinned_carcara_can_judge(problem, proof) {
        panic!("lifted assertion ({tag}): {misjudged}\n{proof}");
    }
    let stem = format!("ay_probe_ite_lift_{}_{tag}", std::process::id());
    let problem_path = std::env::temp_dir().join(format!("{stem}.smt2"));
    let proof_path = std::env::temp_dir().join(format!("{stem}.alethe"));
    std::fs::write(&problem_path, problem).expect("write problem");
    std::fs::write(&proof_path, proof).expect("write proof");
    let output = std::process::Command::new(carcara)
        .arg("check")
        .arg("--allow-int-real-subtyping")
        .arg("--")
        .arg(&proof_path)
        .arg(&problem_path)
        .output()
        .expect("run carcara");
    let stdout = String::from_utf8_lossy(&output.stdout).trim().to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).trim().to_string();
    let first = stdout.lines().last().unwrap_or("").to_string();
    let expected_valid = tag == "shipped";
    if (first == "valid") == expected_valid {
        let _ = std::fs::remove_file(&problem_path);
        let _ = std::fs::remove_file(&proof_path);
    } else {
        eprintln!(
            "Preserving lifted-assertion artifacts ({tag}): smt2={} alethe={}",
            problem_path.display(),
            proof_path.display()
        );
    }
    (
        first,
        format!(
            "status={:?} stdout={stdout} stderr={stderr}",
            output.status.code()
        ),
    )
}

/// NEGATIVE CONTROL: the runner refuses, before the checker runs, a proof
/// resting on an `evaluate` step pinned carcara misjudges
/// (`ay_core::pinned_carcara::FALSE_VALID_CONTROL_PROOF`, which it prints
/// `valid` for against its own problem), so no assertion can pass on it.
#[test]
#[should_panic(expected = "is not evidence")]
fn the_lifted_assertion_runner_refuses_a_document_pinned_carcara_misjudges() {
    carcara_verdict(
        std::path::Path::new("carcara"),
        "false_valid_control",
        ay_core::pinned_carcara::FALSE_VALID_CONTROL_PROBLEM,
        ay_core::pinned_carcara::FALSE_VALID_CONTROL_PROOF,
    );
}

fn find_carcara() -> Option<std::path::PathBuf> {
    if let Ok(path) = std::env::var("CARCARA_PATH") {
        let path = std::path::PathBuf::from(path);
        if path.is_file() {
            return Some(path);
        }
    }
    if let Some(home) = std::env::var_os("HOME") {
        let candidate = std::path::PathBuf::from(home).join(".cargo/bin/carcara");
        if candidate.is_file() {
            return Some(candidate);
        }
    }
    let path = std::env::var_os("PATH")?;
    std::env::split_paths(&path)
        .map(|directory| directory.join("carcara"))
        .find(|candidate| candidate.is_file())
}
