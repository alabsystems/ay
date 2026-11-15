// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the negated-existential ground-instantiation artifact-firewall
//! translation.
//!
//! Split from the producer so the producer stays inside the repository's
//! unwaived 500-line file ratchet. Every test here is a GUARD-REMOVAL proof
//! for one fail-closed leg of that lane.

use super::*;

fn executor_with_assertions(script: &str) -> Executor {
    let commands = ay_frontend::parse(script).expect("negated-exists fixture parses");
    let mut exec = Executor::new();
    assert!(
        exec.execute_all(&commands)
            .expect("negated-exists fixture loads")
            .is_empty(),
        "fixture must contain declarations and assertions only"
    );
    exec
}

/// The Inc FPArith shape, in the cheapest theory that reproduces it: a
/// ground fact plus a negated existential whose body is true at a ground
/// term occurring only INSIDE that body.
const REFUTABLE: &str = r#"
    (set-logic UFLIA)
    (declare-const y Int)
    (assert (= y 0))
    (assert (not (exists ((d Int)) (and (>= d 0) (<= d 16) (= (- 0 d) y)))))
"#;

#[test]
fn translates_the_negated_exists_ground_instance_to_a_strict_proof() {
    let mut exec = executor_with_assertions(REFUTABLE);
    exec.begin_public_solve(false);
    exec.bind_unsat_query_assumptions(&[]);
    assert!(
        exec.try_translate_negated_exists_ground_instantiation_unsat(),
        "d := 0 refutes the negated existential against (= y 0)"
    );
    let proof = exec
        .last_proof
        .clone()
        .expect("translation installs last_proof");
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::QntNegExists,
                ..
            }
        )),
        "the certificate derives the dual universal via qnt_neg_exists"
    );
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::ForallInst,
                ..
            }
        )),
        "the certificate instantiates that universal via forall_inst"
    );
    assert!(exec
        .check_proof_strict_with_datatypes(&proof)
        .is_ok_and(|quality| quality.is_complete()));
    let authored = exec.exact_concrete_authored_scope();
    assert!(
        ay_proof::validate_reachable_assumes_in_problem_scope(&proof, &authored).is_ok(),
        "every reachable assume must be an exact authored root"
    );

    // The certificate must also have a PROBLEM-SCOPED Alethe surface: an
    // external checker reads the original problem file, so a document that
    // needs a declaration of its own is not a certificate of that problem.
    let document = ay_proof::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &exec.ctx.terms,
        &authored,
        None,
    )
    .expect("the certificate is resolvable from the problem scope");
    // Captured unless the run asks for `--nocapture`; this is how the
    // artifact is lifted out for an external carcara replay.
    println!("{document}");
    assert!(document.contains(":rule forall_inst"));
    assert!(
        !document.contains("(declare-"),
        "a certificate may never declare a symbol the problem does not have"
    );
    assert!(
        !document.contains(":rule trust"),
        "a trust step is not a proof; the honest escape hatch is `hole`"
    );
}

#[test]
fn satisfiable_query_cannot_mint_a_certificate() {
    // GUARD-REMOVAL PROOF: the same shape whose existential is genuinely
    // unwitnessed. No instance set refutes it, so the probe declines and
    // nothing installs.
    let mut exec = executor_with_assertions(
        r#"
            (set-logic UFLIA)
            (declare-const y Int)
            (assert (= y 5))
            (assert (not (exists ((d Int)) (and (>= d 0) (<= d 3) (= d y)))))
        "#,
    );
    exec.begin_public_solve(false);
    exec.bind_unsat_query_assumptions(&[]);
    assert!(
        !exec.try_translate_negated_exists_ground_instantiation_unsat(),
        "a satisfiable query must never mint a refutation"
    );
    assert!(exec.last_proof.is_none());
}

#[test]
fn a_positive_exists_root_is_not_a_source() {
    // GUARD-REMOVAL PROOF: only a NEGATED existential entails the dual
    // universal. A positive one must be refused outright.
    let mut exec = executor_with_assertions(
        r#"
            (set-logic UFLIA)
            (declare-const y Int)
            (assert (= y 0))
            (assert (exists ((d Int)) (and (>= d 0) (= d y))))
        "#,
    );
    exec.begin_public_solve(false);
    exec.bind_unsat_query_assumptions(&[]);
    assert!(!exec.try_translate_negated_exists_ground_instantiation_unsat());
    assert!(exec.last_proof.is_none());
}

#[test]
fn lane_attempt_budget_is_enforced() {
    // GUARD-REMOVAL PROOF (attempt budget): the identical executor
    // translates with a fresh budget (sibling test above); an exhausted
    // budget must decline without touching proof state.
    let mut exec = executor_with_assertions(REFUTABLE);
    exec.begin_public_solve(false);
    exec.bind_unsat_query_assumptions(&[]);
    exec.negated_exists_ground_inst_attempts
        .set(MAX_LANE_ATTEMPTS);
    assert!(!exec.try_translate_negated_exists_ground_instantiation_unsat());
    assert!(exec.last_proof.is_none());
}

#[test]
fn witnesses_mentioning_a_bound_name_are_not_proposed() {
    // NOT A GUARD-REMOVAL PROOF, and it was labelled as one. Review measured
    // that the assertion below is a TAUTOLOGY: `ground_witnesses_for_sort`
    // already filters by `term_avoids_names`, so re-asserting it cannot fail
    // for any implementation — and this test passed unchanged with the whole
    // translation stubbed to `return false`.
    //
    // It is kept as a CONTRACT test (the scan yields ground Int terms and none
    // mention a binder), not as evidence that the filter is load-bearing. The
    // filter in fact cannot fire at all: `ground_instantiation_candidates` has
    // no `Forall`/`Exists` arm, so it never descends under a binder and never
    // produces a term containing a `Var`. The premise stated here — "the raw
    // candidate scan descends into the existential body" — is false.
    //
    // The lane's real barrier is
    // `translates_the_negated_exists_ground_instance_to_a_strict_proof`, which
    // FAILS when the translation is stubbed.
    let exec = executor_with_assertions(REFUTABLE);
    let authored = exec.ctx.assertions.clone();
    let bound = exec.authored_binder_names(&authored);
    // The elaborator may alpha-rename, so read the binder off the root
    // rather than assuming the source spelling survived.
    let roots = exec.exact_authored_negated_exists_roots(&authored);
    let (_, _, bindings, _) = roots
        .first()
        .expect("the fixture asserts (not (exists ...))");
    assert!(
        bindings.iter().all(|(name, _)| bound.contains(name)),
        "every binder of the authored existential must be collected"
    );
    let witnesses = exec.ground_witnesses_for_sort(&authored, &Sort::Int, &bound);
    assert!(!witnesses.is_empty(), "the fixture has ground Int terms");
    for &witness in &witnesses {
        assert!(
            exec.term_avoids_names(witness, &bound),
            "no proposed witness may mention a bound name"
        );
    }
}

#[test]
fn bounded_tuples_respects_its_limit_and_leads_with_the_diagonal() {
    let a = TermId(1);
    let b = TermId(2);
    let columns = vec![vec![a, b], vec![a, b]];
    let tuples = bounded_tuples(&columns, 3);
    assert_eq!(tuples.len(), 3);
    assert_eq!(tuples[0], vec![a, a]);
    assert_eq!(tuples[1], vec![b, b]);
    assert!(bounded_tuples(&columns, 0).is_empty());
}

// ---------------------------------------------------------------------------
// Witness sources beyond the authored ground scan
// (#negated-exists-cegqi-witness-hints, `authored_negated_exists_witness_hints`).
// ---------------------------------------------------------------------------

/// The deductive-checks `C_quantifiers` obligation: every `Int` term of the problem
/// lives INSIDE the existential body, so the authored ground scan has no
/// witness to propose and only the CEGQI value (`301`) refutes it.
const BODY_ONLY_WITNESS: &str = r#"
    (set-logic ALL)
    (declare-const ground (_ BitVec 32))
    (assert (= ground #x0000012c))
    (assert (not (exists ((i Int)) (and (<= 0 i) (< i 4294967296) (< 300 i)))))
"#;

/// The deductive-checks `C_seqs` obligation shape: `seq_contains` asserted and
/// denied. Only the Skolem constant of the positive existential refutes it.
const SEQ_CONTAINS_BOTH_SIDES: &str = r#"
    (set-logic ALL)
    (declare-const n Int)
    (assert (exists ((i Int)) (and (<= 0 i) (< i n))))
    (assert (not (exists ((j Int)) (and (<= 0 j) (< j n)))))
    (check-sat)
"#;

fn int_hint(exec: &mut Executor, value: i64) -> TermId {
    exec.ctx.terms.mk_int(num_bigint::BigInt::from(value))
}

fn has_rule(proof: &Proof, wanted: &AletheRule) -> bool {
    proof
        .steps
        .iter()
        .any(|step| matches!(step, ProofStep::Step { rule, .. } if rule == wanted))
}

fn assert_strict_authored_certificate(exec: &mut Executor, proof: &Proof) {
    assert!(has_rule(proof, &AletheRule::QntNegExists));
    assert!(has_rule(proof, &AletheRule::ForallInst));
    assert!(exec
        .check_proof_strict_with_datatypes(proof)
        .is_ok_and(|quality| quality.is_complete()));
    let authored = exec.exact_concrete_authored_scope();
    assert!(ay_proof::validate_reachable_assumes_in_problem_scope(proof, &authored).is_ok());
    let document = ay_proof::try_export_alethe_with_problem_scope_and_overrides(
        proof,
        &exec.ctx.terms,
        &authored,
        None,
    )
    .expect("the certificate is resolvable from the problem scope");
    assert!(!document.contains("(declare-"));
    assert!(!document.contains(":rule trust"));
}

#[test]
fn a_cegqi_witness_hint_closes_the_body_only_shape() {
    let mut exec = executor_with_assertions(BODY_ONLY_WITNESS);
    exec.begin_public_solve(false);
    exec.bind_unsat_query_assumptions(&[]);
    // GUARD-REMOVAL PROOF for the hint source: with no hint the lane has no
    // `Int` witness at all and declines without touching proof state.
    assert!(!exec.try_translate_negated_exists_ground_instantiation_unsat());
    assert!(exec.last_proof.is_none());

    exec.negated_exists_ground_inst_attempts.set(0);
    let witness = int_hint(&mut exec, 301);
    exec.cegqi_witness_hints.push((Sort::Int, witness));
    assert!(
        exec.try_translate_negated_exists_ground_instantiation_unsat(),
        "i := 301 refutes the negated existential"
    );
    let proof = exec
        .last_proof
        .clone()
        .expect("translation installs last_proof");
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step { rule: AletheRule::ForallInst, args, .. } if args == &[witness]
        )),
        "the certificate instantiates the dual at the hinted value"
    );
    assert_strict_authored_certificate(&mut exec, &proof);
}

#[test]
fn a_wrong_hint_only_costs_a_declined_candidate() {
    // A value that does NOT refute the body: the probe stays satisfiable and
    // nothing installs.
    let mut exec = executor_with_assertions(BODY_ONLY_WITNESS);
    exec.begin_public_solve(false);
    exec.bind_unsat_query_assumptions(&[]);
    let wrong = int_hint(&mut exec, 5);
    exec.cegqi_witness_hints.push((Sort::Int, wrong));
    assert!(!exec.try_translate_negated_exists_ground_instantiation_unsat());
    assert!(exec.last_proof.is_none());

    // The same wrong value ahead of the right one costs exactly one declined
    // candidate: the refuting instance is still proposed and certified.
    let mut exec = executor_with_assertions(BODY_ONLY_WITNESS);
    exec.begin_public_solve(false);
    exec.bind_unsat_query_assumptions(&[]);
    let wrong = int_hint(&mut exec, 5);
    let right = int_hint(&mut exec, 301);
    exec.cegqi_witness_hints.push((Sort::Int, wrong));
    exec.cegqi_witness_hints.push((Sort::Int, right));
    assert!(exec.try_translate_negated_exists_ground_instantiation_unsat());
    let proof = exec
        .last_proof
        .clone()
        .expect("translation installs last_proof");
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::Step { rule: AletheRule::ForallInst, args, .. } if args == &[right]
    )));
    assert_strict_authored_certificate(&mut exec, &proof);
}

#[test]
fn hints_naming_a_foreign_symbol_are_not_proposed() {
    // A CEGQI counterexample constant is closed but not problem-closed: it
    // must never reach a certificate. A literal is proposed; hints come
    // BEFORE the authored scan.
    let mut exec = executor_with_assertions(BODY_ONLY_WITNESS);
    exec.begin_public_solve(false);
    let foreign = exec.ctx.terms.mk_var("__ay_ce_i!7", Sort::Int);
    let literal = int_hint(&mut exec, 301);
    exec.cegqi_witness_hints.push((Sort::Int, foreign));
    exec.cegqi_witness_hints.push((Sort::Int, literal));
    let authored = exec.exact_concrete_authored_scope();
    let bound = exec.authored_binder_names(&authored);
    let candidates = exec.negated_exists_witness_candidates(
        &authored,
        &Sort::Int,
        &bound,
        &[],
        MAX_WITNESSES_PER_SORT,
    );
    assert_eq!(candidates, vec![literal]);
    // A stale id past the arena is never dereferenced.
    let past_the_arena = TermId(u32::MAX);
    exec.cegqi_witness_hints.push((Sort::Int, past_the_arena));
    let candidates = exec.negated_exists_witness_candidates(
        &authored,
        &Sort::Int,
        &bound,
        &[],
        MAX_WITNESSES_PER_SORT,
    );
    assert_eq!(candidates, vec![literal]);
}

#[test]
fn the_hint_ledger_lives_exactly_one_public_decision() {
    let mut exec = executor_with_assertions(BODY_ONLY_WITNESS);
    exec.begin_public_solve(false);
    let witness = int_hint(&mut exec, 301);
    exec.cegqi_witness_hints.push((Sort::Int, witness));
    // A CEGAR iteration re-prepares the executor: the ledger must survive,
    // because the firewall reads it in a later iteration than the round
    // that filled it.
    exec.clear_preprocessing_proof_records();
    assert_eq!(exec.cegqi_witness_hints.len(), 1);
    // A nested same-executor scope starts empty and hands the ledger back.
    let saved = exec.take_consequence_replay_state();
    assert!(exec.cegqi_witness_hints.is_empty());
    exec.restore_consequence_replay_state(saved);
    assert_eq!(exec.cegqi_witness_hints.len(), 1);
    // A new public decision starts over.
    exec.begin_public_solve(false);
    assert!(exec.cegqi_witness_hints.is_empty());
}

fn solved_executor(script: &str) -> (Executor, Vec<String>) {
    let commands = ay_frontend::parse(script).expect("fixture parses");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("fixture executes");
    (exec, outputs)
}

/// Alpha-quantifier sharing (`elaborate/term.rs`) elaborates the positive
/// existential and its negated twin to ONE term, and that complementary root
/// pair is then refuted by a single resolution before any quantifier lane
/// runs (`authored_complementary_roots`). The Skolem-witness mechanism under
/// test here is the one that serves every shape sharing does NOT collapse, so
/// these two end-to-end controls pin sharing OFF for the exact original
/// route; the sibling below pins the sharing-on outcome.
fn alpha_sharing_off() -> ay_core::misc_test_override::Guard {
    ay_core::misc_test_override::set(ay_core::MiscCliFlags {
        no_alpha_quantifier_sharing: true,
        ..ay_core::MiscCliFlags::default()
    })
}

#[test]
fn a_registry_skolem_witness_closes_the_seq_contains_shape() {
    let _sharing_off = alpha_sharing_off();
    let (mut exec, outputs) = solved_executor(SEQ_CONTAINS_BOTH_SIDES);
    assert_eq!(outputs, vec!["unsat".to_string()]);
    let proof = exec
        .last_proof
        .clone()
        .expect("the published unsat retains its certificate");
    assert!(
        has_rule(&proof, &AletheRule::Skolem),
        "`B[sk]` is derived from the authored positive existential via sko_ex"
    );
    assert_strict_authored_certificate(&mut exec, &proof);
}

/// The `_variable` sibling of the seq_contains shape: the needle is a
/// declared constant, so the probe's preprocessing would substitute
/// `needle := (select s sk)` and record it as a trust step unless the probe
/// keeps its assume leaves aligned (`proof_probe_skips_varsubst`).
#[test]
fn a_symbolic_needle_certifies_through_the_substitution_free_probe() {
    let _sharing_off = alpha_sharing_off();
    let (mut exec, outputs) = solved_executor(
        r#"
            (set-logic ALL)
            (declare-const needle (_ BitVec 32))
            (declare-const n Int)
            (declare-const s (Array (_ BitVec 32) (_ BitVec 32)))
            (assert (exists ((i Int)) (and (<= 0 i) (< i n) (= needle (select s ((_ int2bv 32) i))))))
            (assert (not (exists ((j Int)) (and (<= 0 j) (< j n) (= needle (select s ((_ int2bv 32) j)))))))
            (check-sat)
        "#,
    );
    assert_eq!(outputs, vec!["unsat".to_string()]);
    let proof = exec
        .last_proof
        .clone()
        .expect("the published unsat retains its certificate");
    assert!(has_rule(&proof, &AletheRule::Skolem));
    assert_strict_authored_certificate(&mut exec, &proof);
}

/// With sharing ON (the default) the same shape is `t` beside `(not t)`: the
/// pre-quantifier BV/LIA bridge refutes it with no clause trace, and the
/// strict certificate is the exact two-assume resolution of the authored
/// pair — no Skolem step, no witness lane, same verdict, same rigor.
#[test]
fn with_alpha_sharing_on_the_seq_contains_pair_certifies_by_one_resolution() {
    let (mut exec, outputs) = solved_executor(SEQ_CONTAINS_BOTH_SIDES);
    assert_eq!(outputs, vec!["unsat".to_string()]);
    let proof = exec
        .last_proof
        .clone()
        .expect("the published unsat retains its certificate");
    assert!(
        !has_rule(&proof, &AletheRule::Skolem),
        "the shared pair never reaches the witness lane"
    );
    let assumes = proof
        .steps
        .iter()
        .filter(|step| matches!(step, ProofStep::Assume(_)))
        .count();
    let resolutions = proof
        .steps
        .iter()
        .filter(|step| matches!(step, ProofStep::Resolution { .. }))
        .count();
    assert_eq!((assumes, resolutions), (2, 1), "{proof:?}");
    // The same strict, in-scope, renderable bar the lane's certificates meet,
    // minus the lane-specific rules (`qnt_neg_exists`, `forall_inst`) that a
    // two-assume resolution has no reason to carry.
    assert!(exec
        .check_proof_strict_with_datatypes(&proof)
        .is_ok_and(|quality| quality.is_complete()));
    let authored = exec.exact_concrete_authored_scope();
    assert!(ay_proof::validate_reachable_assumes_in_problem_scope(&proof, &authored).is_ok());
    let document = ay_proof::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &exec.ctx.terms,
        &authored,
        None,
    )
    .expect("the certificate is resolvable from the problem scope");
    assert!(!document.contains("(declare-"));
    assert!(!document.contains(":rule trust"));
}

#[test]
fn registry_records_are_rebuilt_after_the_per_solve_records_are_cleared() {
    // The s_pure failure mode: the Skolemization record is per internal
    // solve and the firewall runs in a later CEGAR iteration. The persistent
    // choice registry rebuilds it for the exact authored root only.
    let (mut exec, _) = solved_executor(SEQ_CONTAINS_BOTH_SIDES);
    exec.clear_preprocessing_proof_records();
    assert!(exec.skolem_instance_records.is_empty());
    let authored = exec.exact_concrete_authored_scope();
    let records = exec.authored_positive_exists_skolem_records(&authored);
    assert_eq!(
        records.len(),
        1,
        "exactly the positive root has a registered choice"
    );
    let record = &records[0];
    assert!(record.positive);
    assert!(authored.contains(&record.source));
    let TermData::Var(name, _) = exec.ctx.terms.get(record.witness).clone() else {
        panic!("the witness is a Skolem constant");
    };
    assert!(exec.ctx.terms.is_skolem_symbol(&name));
    let choice = exec
        .ctx
        .terms
        .skolem_choice(record.witness)
        .expect("registered")
        .clone();
    let TermData::Exists(bindings, body, _) = exec.ctx.terms.get(record.source).clone() else {
        panic!("the source is the authored exists");
    };
    assert_eq!(choice.body, body);
    assert_eq!(choice.binder, bindings[0].0);
}

#[test]
fn a_skolem_step_with_a_mismatched_choice_body_is_refused() {
    // Two positive existentials with DIFFERENT bodies: borrowing one root's
    // registered witness for the other root's `sko_ex` step must be refused
    // by the strict checker, so a forged registry record can never install.
    let (mut exec, _) = solved_executor(
        r#"
            (set-logic ALL)
            (declare-const n Int)
            (assert (exists ((i Int)) (and (<= 0 i) (< i n))))
            (assert (exists ((k Int)) (and (<= 5 k) (< k n))))
            (assert (not (exists ((j Int)) (and (<= 0 j) (< j n)))))
            (check-sat)
        "#,
    );
    // The live per-solve records still hold both witnesses here; the
    // registry rebuild deduplicates against them, so clear them first.
    exec.clear_preprocessing_proof_records();
    let authored = exec.exact_concrete_authored_scope();
    let records = exec.authored_positive_exists_skolem_records(&authored);
    assert_eq!(records.len(), 2);
    let (first, second) = (&records[0], &records[1]);
    assert_ne!(first.witness, second.witness);
    // Forge: the first root with the second root's witness.
    let TermData::Exists(bindings, body, _) = exec.ctx.terms.get(first.source).clone() else {
        panic!("authored exists");
    };
    let forged_instance = Executor::substitute_single_binder_structurally(
        &mut exec.ctx.terms,
        body,
        &bindings[0].0,
        second.witness,
    )
    .expect("structural substitution");
    let equality = exec.ctx.terms.mk_app(
        Symbol::named("="),
        [first.source, forged_instance],
        Sort::Bool,
    );
    let mut forged = Proof::new();
    forged.add_assume(first.source, None);
    forged.add_rule_step(
        AletheRule::Skolem,
        vec![equality],
        Vec::new(),
        vec![second.witness],
    );
    let refusal = format!(
        "{:?}",
        exec.check_proof_strict_with_datatypes(&forged)
            .err()
            .expect("a witness registered for a different body is not this root's choice")
    );
    assert!(
        refusal.contains("registered choice does not match the existential source"),
        "the Skolem step itself must be the refused step: {refusal}"
    );
    // The genuine pairing is accepted.
    let genuine_instance = Executor::substitute_single_binder_structurally(
        &mut exec.ctx.terms,
        body,
        &bindings[0].0,
        first.witness,
    )
    .expect("structural substitution");
    let equality = exec.ctx.terms.mk_app(
        Symbol::named("="),
        [first.source, genuine_instance],
        Sort::Bool,
    );
    let mut genuine = Proof::new();
    genuine.add_assume(first.source, None);
    genuine.add_rule_step(
        AletheRule::Skolem,
        vec![equality],
        Vec::new(),
        vec![first.witness],
    );
    // The genuine pairing passes the Skolem step: the two-step fragment is
    // then refused only for not deriving the empty clause.
    let verdict = format!(
        "{:?}",
        exec.check_proof_strict_with_datatypes(&genuine).map(|_| ())
    );
    assert!(
        verdict.contains("FinalClauseNotEmpty"),
        "the registered pairing must validate as sko_ex: {verdict}"
    );
}

// ---------------------------------------------------------------------------
// ψ-conjunct roots: `(not (and E ψ))` with ground ψ, read clausally as
// `{¬E, ¬ψ}` (#primes-negated-and-exists). Census shape
// `LIA/UltimateAutomizer/Primes_true-unreach-call.c_1657`.
// ---------------------------------------------------------------------------

/// The X5 minimizer: a ground positive copy at `a`, and the denial carries
/// the ground conjunct `n <= 2` beside the existential.
const PSI_CONJUNCT_MINIMIZER: &str = r#"
    (set-logic LIA)
    (declare-fun n () Int)
    (declare-fun ret () Int)
    (declare-fun a () Int)
    (assert (and (<= n a) (<= a ret) (<= n 2)))
    (assert (not (and (exists ((x Int)) (and (<= n x) (<= x ret) (<= n 2))) (<= n 2))))
"#;

/// The census Primes shape: a 3-binder positive existential, denied under
/// `(not (and E (<= nc 2)))` with `nc <= 2` already a body conjunct.
const PRIMES_SHAPE: &str = r#"
    (set-logic LIA)
    (declare-fun ret () Int)
    (declare-fun nc () Int)
    (declare-fun f1c () Int)
    (assert (exists ((v94 Int) (v95 Int) (v96 Int)) (and (<= (+ f1c (* 2 v94) (* 2 v95) (* 2 v96) 1) ret) (<= f1c v94) (<= v96 v95) (<= v94 v96) (<= nc 2))))
    (assert (not (and (exists ((v94 Int) (v95 Int) (v96 Int)) (and (<= (+ f1c (* 2 v94) (* 2 v95) (* 2 v96) 1) ret) (<= f1c v94) (<= v96 v95) (<= v94 v96) (<= nc 2))) (<= nc 2))))
    (check-sat)
"#;

#[test]
fn psi_conjunct_root_translates_to_a_strict_proof() {
    let mut exec = executor_with_assertions(PSI_CONJUNCT_MINIMIZER);
    exec.begin_public_solve(false);
    exec.bind_unsat_query_assumptions(&[]);
    assert!(
        exec.try_translate_negated_exists_ground_instantiation_unsat(),
        "x := a refutes (not (and Eψ)) against the ground positive copy"
    );
    let proof = exec
        .last_proof
        .clone()
        .expect("translation installs last_proof");
    assert!(has_rule(&proof, &AletheRule::QntNegExists));
    assert_strict_authored_certificate(&mut exec, &proof);
}

#[test]
fn psi_conjunct_minimizer_publishes_unsat_end_to_end() {
    let script = format!("{PSI_CONJUNCT_MINIMIZER}    (check-sat)\n");
    let (mut exec, outputs) = solved_executor(&script);
    assert_eq!(outputs, vec!["unsat".to_string()]);
    let proof = exec
        .last_proof
        .clone()
        .expect("the published unsat retains its certificate");
    assert!(exec
        .check_proof_strict_with_datatypes(&proof)
        .is_ok_and(|quality| quality.is_complete()));
}

#[test]
fn primes_three_binder_psi_conjunct_publishes_unsat_end_to_end() {
    let (mut exec, outputs) = solved_executor(PRIMES_SHAPE);
    assert_eq!(outputs, vec!["unsat".to_string()]);
    let proof = exec
        .last_proof
        .clone()
        .expect("the published unsat retains its certificate");
    assert!(exec
        .check_proof_strict_with_datatypes(&proof)
        .is_ok_and(|quality| quality.is_complete()));
}

#[test]
fn psi_conjunct_root_with_false_psi_cannot_mint_a_certificate() {
    // GUARD-REMOVAL PROOF: same minimizer but ψ (`n <= 2`) is FALSE, so
    // `(not (and E ψ))` holds regardless of E and the query is satisfiable.
    // A derivation that dropped the ψ premise would mint here.
    let mut exec = executor_with_assertions(
        r#"
            (set-logic LIA)
            (declare-fun n () Int)
            (declare-fun ret () Int)
            (declare-fun a () Int)
            (assert (and (<= n a) (<= a ret) (<= 3 n)))
            (assert (not (and (exists ((x Int)) (and (<= n x) (<= x ret) (<= n 2))) (<= n 2))))
        "#,
    );
    exec.begin_public_solve(false);
    exec.bind_unsat_query_assumptions(&[]);
    assert!(
        !exec.try_translate_negated_exists_ground_instantiation_unsat(),
        "a satisfiable ψ-conjunct query must never mint a refutation"
    );
    assert!(exec.last_proof.is_none());
}
