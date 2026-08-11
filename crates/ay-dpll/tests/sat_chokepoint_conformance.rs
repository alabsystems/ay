// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
//! Conformance pin for the single SAT-emission chokepoint (#sat-chokepoint).
//!
//! `crates/ay-dpll/src/executor/model/sat_emit.rs::emit_sat_verdict` is the ONLY
//! place a proposed `Sat` becomes an emitted `Sat`, and every public verdict
//! path (plain check-sat, check-sat-assuming, optimize) must route through it so
//! the strict, quantified-certificate, independent, and
//! authoritative-failclosed gates ALL run, followed by the release-mode
//! validation-evidence postcondition. This test pins that
//! structure: if a verdict path stops funnelling through `emit_sat_verdict`, or
//! the funnel drops a gate, the build fails.

use std::path::PathBuf;

fn read(rel: &str) -> String {
    let p = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(rel);
    std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("cannot read {}: {e}", p.display()))
}

/// (a) The funnel runs the exact strict -> quantified -> independent -> authoritative ->
/// formula-neutral output completion -> validation-postcondition sequence and
/// only then mints the witness token.
#[test]
fn emit_sat_verdict_has_strict_independent_authoritative_postcondition_sequence() {
    let src = read("src/executor/model/sat_emit.rs");
    let funnel_start = src
        .find("pub(in crate::executor) fn emit_sat_verdict(")
        .expect("sat_emit.rs must define the single funnel `emit_sat_verdict`");
    let funnel_end = src[funnel_start..]
        .find("fn apply_sat_validation_postcondition(")
        .map(|offset| funnel_start + offset)
        .expect("sat_emit.rs must define the release-mode SAT postcondition");
    let funnel = &src[funnel_start..funnel_end];

    // The STRICT gate (full validation when unvalidated, else the strict gate).
    let strict = funnel
        .find("finalize_sat_model_validation()")
        .expect("emit_sat_verdict must run the strict gate (finalize_sat_model_validation)");
    let strict_alt = funnel
        .find("apply_strict_model_gate(")
        .expect("emit_sat_verdict must run apply_strict_model_gate for already-validated models");
    let quantified = funnel
        .find("apply_quantified_model_failclosed_gate(")
        .expect("emit_sat_verdict must run the quantified-model certificate gate");
    let independent = funnel
        .find("apply_independent_model_gate(")
        .expect("emit_sat_verdict must run the INDEPENDENT model-check gate");
    let authoritative = funnel
        .find("apply_authoritative_failclosed_gate(")
        .expect("emit_sat_verdict must run the AUTHORITATIVE-failclosed gate");
    let output_completion = funnel
        .rfind("complete_unconstrained_functions_for_output(")
        .expect("emit_sat_verdict must finalize formula-neutral function output");
    let postcondition = funnel
        .find("apply_sat_validation_postcondition(")
        .expect("emit_sat_verdict must enforce the SAT validation-evidence postcondition");
    let nontrivial_mint = funnel
        .rfind("SatCertificate(())")
        .expect("emit_sat_verdict must mint the non-trivial witness token");

    // Ordering: strict (both forms) precede the quantified certificate, which
    // precedes the compositional independent evaluator and its defenses.
    assert!(
        strict < quantified && strict_alt < quantified,
        "the strict gate must run BEFORE the quantified certificate in emit_sat_verdict"
    );
    assert!(
        quantified < independent,
        "the quantified certificate must run BEFORE the independent evaluator so only certified quantified leaves can be composed out"
    );
    assert!(
        independent < authoritative,
        "the independent gate must run BEFORE the authoritative-failclosed gate in \
         emit_sat_verdict (the latter is retained as defense in depth)"
    );
    assert!(
        authoritative < output_completion && output_completion < postcondition,
        "formula-neutral output completion must run after every model gate and before the postcondition"
    );
    assert!(
        postcondition < nontrivial_mint,
        "a non-trivial SatCertificate must be minted only after the validation postcondition"
    );

    // The unforgeable witness token is minted only here.
    assert!(
        funnel.contains("SatCertificate(())"),
        "emit_sat_verdict must mint the SatCertificate witness token"
    );
}

/// (a2) Empty-formula SAT carries explicit vacuous evidence only after its
/// final output-visible unconstrained model has been constructed and completed.
#[test]
fn empty_sat_completes_final_model_before_vacuous_evidence_and_mint() {
    let src = read("src/executor/model/sat_emit.rs");
    let start = src
        .find("if self.ctx.assertions.is_empty() && roots.is_empty()")
        .expect("SAT funnel must define its vacuous empty-formula branch");
    let tail = &src[start..];
    let create = tail
        .find("self.last_model = Some(super::Model::empty());")
        .expect("empty SAT must construct a model before consumer publication");
    let constants = tail
        .find("self.complete_unconstrained_constants_for_output(roots);")
        .expect("empty SAT must complete unconstrained constants");
    let functions = tail
        .find("self.complete_unconstrained_functions_for_output(roots);")
        .expect("empty SAT must complete unconstrained functions");
    let evidence = tail
        .find("self.last_model_validated = true;")
        .expect("empty SAT must record explicit vacuous evidence");
    let mint = tail
        .find("self.last_sat_certificate = Some(SatCertificate(()));")
        .expect("empty SAT must mint its private capability");
    assert!(
        create < constants && constants < functions && functions < evidence && evidence < mint,
        "empty SAT order must be create -> complete constants/functions -> vacuous evidence -> mint"
    );
}

/// (b) Assumptions are installed as real assertions for the entire model-
/// mutation/validation/mint scope, and the persistent assertion stack is
/// restored only after that scope returns. No assumption validator or output
/// completion may mutate the model after emission.
#[test]
fn assumptions_share_one_restored_pre_mint_validation_scope() {
    let sat_emit = read("src/executor/model/sat_emit.rs");
    let funnel_start = sat_emit
        .find("pub(in crate::executor) fn emit_sat_verdict(")
        .expect("sat_emit must define emit_sat_verdict");
    let funnel_end = sat_emit[funnel_start..]
        .find("fn apply_sat_validation_postcondition(")
        .map(|offset| funnel_start + offset)
        .expect("sat_emit must define its validation postcondition");
    let funnel = &sat_emit[funnel_start..funnel_end];

    let combine = funnel
        .find("combined.extend_from_slice(roots);")
        .expect("assumption roots must be installed as validation assertions");
    let completion = funnel
        .find("complete_unconstrained_constants_for_output(roots)")
        .expect("combined-scope output completion must run");
    let strict = funnel
        .find("finalize_sat_model_validation()")
        .expect("combined-scope canonical validation must run when evidence is stale");
    let mint = funnel
        .rfind("SatCertificate(())")
        .expect("combined scope must mint its certificate");
    let restore = funnel
        .rfind("self.ctx.assertions = assertions;")
        .expect("combined validation scope must restore the persistent assertion stack");
    assert!(
        combine < completion && completion < strict && strict < mint && mint < restore,
        "assertions + assumptions must remain active through completion, validation, and mint, then restore"
    );

    let assuming = read("src/executor/check_sat_assuming.rs");
    assert!(
        !assuming.contains("let validated = self.emit_sat_verdict"),
        "check-sat-assuming must not run a model-mutating validator after a provisional certificate"
    );
    assert!(
        !assuming.contains("complete_unconstrained_functions_for_output("),
        "check-sat-assuming must not mutate output models after certificate minting"
    );
    let plain = read("src/executor/check_sat.rs");
    assert!(
        !plain.contains("complete_unconstrained_functions_for_output("),
        "plain check-sat must not mutate output models after certificate minting"
    );
}

/// (c) A control flag that merely suppresses model evaluation is not validation
/// evidence. In particular, the public BV+LIA fallback routes may leave this
/// flag set after a failed model-validation attempt; the final funnel must
/// still fail closed in release builds.
#[test]
fn sat_postcondition_does_not_accept_skip_model_eval_as_evidence() {
    let src = read("src/executor/model/sat_emit.rs");
    let postcondition_start = src
        .find("fn apply_sat_validation_postcondition(")
        .expect("sat_emit.rs must define the release-mode SAT postcondition");
    let tests_start = src[postcondition_start..]
        .find("#[cfg(test)]")
        .map(|offset| postcondition_start + offset)
        .unwrap_or(src.len());
    let postcondition = &src[postcondition_start..tests_start];

    assert!(
        !postcondition.contains("|| self.skip_model_eval"),
        "skip_model_eval suppresses work but is not validation evidence; accepting it can make
         public BV+LIA model-validation failures escape as Sat"
    );
}

/// (d) A strict repair of an already-validated array model invalidates the old
/// evidence. A silent re-verdict must flow into full validation; a rejecting
/// re-verdict must replace the stale original violation.
#[test]
fn post_validation_array_retry_propagates_both_outcomes_and_revalidates() {
    let pipeline = read("src/executor/model/validation/pipeline.rs");
    let repair_start = pipeline
        .find("fn repair_asserted_array_read_pins(&mut self)")
        .expect("pipeline must define the shared array-repair primitive");
    let repair_end = pipeline[repair_start..]
        .find("fn unit_clause_contradiction(")
        .map(|offset| repair_start + offset)
        .expect("array repair must precede the unit-clause helper");
    let repair = &pipeline[repair_start..repair_end];
    let evidence_invalidation = repair
        .find("self.last_model_validated = false;")
        .expect("every actual array repair must invalidate prior validation evidence");
    let first_mutation = repair
        .find("self.last_model.as_mut()")
        .expect("array repair must mutate the selected model");
    assert!(
        evidence_invalidation < first_mutation,
        "the shared repair primitive must invalidate evidence BEFORE its first model mutation"
    );

    let completion = read("src/executor/model/completion.rs");
    let validation_completion_start = completion
        .find("fn complete_model_for_validation(")
        .expect("completion must define complete_model_for_validation");
    let validation_completion_end = completion[validation_completion_start..]
        .find("fn complete_uninterpreted_sort_model(")
        .map(|offset| validation_completion_start + offset)
        .expect("model completion must precede uninterpreted-sort completion");
    let validation_completion = &completion[validation_completion_start..validation_completion_end];
    let invalidate = validation_completion
        .find("self.last_model_validated = false;")
        .expect("general model completion must invalidate prior evidence");
    let take = validation_completion
        .find("self.last_model.take()")
        .expect("general model completion must take the selected model");
    assert!(
        invalidate < take,
        "general completion must invalidate evidence before taking or mutating the model"
    );

    let strict_start = pipeline
        .find("pub(in crate::executor) fn apply_strict_model_gate(")
        .expect("pipeline must define apply_strict_model_gate");
    let strict_end = pipeline[strict_start..]
        .find("fn find_unwitnessed_array_disequality(")
        .map(|offset| strict_start + offset)
        .expect("strict gate must precede the array-disequality helper");
    let strict_gate = &pipeline[strict_start..strict_end];

    assert!(
        strict_gate.contains("self.last_model_validated = false;")
            && strict_gate.contains("strict = self.verify_model_strict();"),
        "post-validation array repair must invalidate old evidence and retain the CURRENT retry verdict"
    );
    assert!(
        strict_gate.contains("if strict.is_none()")
            && strict_gate.contains("if let Some((idx, oracle, assertion)) = strict"),
        "a silent retry must continue, while a changed rejecting retry must report the new verdict"
    );
    assert!(
        !strict_gate.contains("return SolveResult::Sat;"),
        "a silent strict retry must not escape before the final validation pipeline"
    );

    let sat_emit = read("src/executor/model/sat_emit.rs");
    let funnel_start = sat_emit
        .find("pub(in crate::executor) fn emit_sat_verdict(")
        .expect("sat_emit must define emit_sat_verdict");
    let funnel_end = sat_emit[funnel_start..]
        .find("fn apply_sat_validation_postcondition(")
        .map(|offset| funnel_start + offset)
        .expect("sat_emit must define its validation postcondition");
    let funnel = &sat_emit[funnel_start..funnel_end];
    let strict_call = funnel
        .find("let strict = self.apply_strict_model_gate(SolveResult::Sat);")
        .expect("already-validated witnesses must still run the strict gate");
    let post_repair = &funnel[strict_call..];
    assert!(
        post_repair.contains("strict == SolveResult::Sat && !self.last_model_validated")
            && post_repair.contains("self.finalize_sat_model_validation()?"),
        "a successful repair must rerun full validation before SAT certification"
    );
}

/// (e) The two historically-ungated verdict paths emit `Sat` ONLY via
/// `emit_sat_verdict` — no bare `Ok(SolveResult::Sat)` escape remains.
#[test]
fn assuming_and_optimize_emit_sat_only_through_the_funnel() {
    for rel in [
        "src/executor/check_sat_assuming.rs",
        "src/executor/optimization.rs",
    ] {
        let src = read(rel);
        assert!(
            src.contains("emit_sat_verdict("),
            "{rel} must emit its SAT verdict via emit_sat_verdict"
        );
        // No bare `Ok(SolveResult::Sat)` verdict ESCAPE. A match arm
        // (`Ok(SolveResult::Sat) =>`) that CONSUMES an inner result is fine — it
        // is inspecting a verdict, not minting one. A comment mentioning the
        // pattern is fine too. Only a CONSTRUCTED `Ok(SolveResult::Sat)`
        // return/tail would bypass the funnel.
        for (lineno, line) in src.lines().enumerate() {
            if !line.contains("Ok(SolveResult::Sat)") {
                continue;
            }
            let trimmed = line.trim_start();
            let is_match_arm = line.contains("=>");
            let is_comment = trimmed.starts_with("//") || trimmed.starts_with('*');
            assert!(
                is_match_arm || is_comment,
                "{rel}:{} emits a bare `Ok(SolveResult::Sat)` — route every SAT verdict \
                 through emit_sat_verdict so the independent + authoritative gates run:\n  {line}",
                lineno + 1,
            );
        }
    }

    let optimization = read("src/executor/optimization.rs");
    let finalizer_start = optimization
        .find("fn finalize_optimization(")
        .expect("optimization must define its public SAT finalizer");
    let finalizer = &optimization[finalizer_start..];
    let evidence_invalidation = finalizer
        .find("self.last_model_validated = false;")
        .expect("optimization must invalidate probe evidence for its selected witness");
    let emit = finalizer
        .find("self.emit_sat_verdict(SolveResult::Sat, &value_roots)")
        .expect("optimization must use the SAT emission funnel with objective-value roots");
    let reaccount = finalizer
        .find("self.optimization_final_values_match(finite_values)")
        .expect("optimization must re-account finite values against the final model");
    let publish = finalizer
        .find("self.finite_objective_values\n            .extend(finite_values.iter().cloned());")
        .expect("optimization must publish indexed finite values only after admission");
    assert!(
        evidence_invalidation < emit,
        "optimization must invalidate probe evidence before validating and certifying its selected witness"
    );
    assert!(
        emit < reaccount && reaccount < publish,
        "optimization order must be exact-root emission -> final re-accounting -> indexed publication"
    );
    assert!(
        optimization.contains(
            "self.last_model_validated = false;\n        self.last_model = captured_model;"
        ),
        "MaxSMT must invalidate evidence before replacing the most recent probe model"
    );
}

/// (f) MaxSMT may capture an optimum from an earlier temporary probe. Replacing
/// the probe model invalidates its evidence, and the captured witness must pass
/// through the restored hard scope plus its exact soft-classification roots,
/// then be re-accounted from the final model before any cost is published.
#[test]
fn maxsmt_revalidates_captured_witness_before_publishing_optimum() {
    let optimization = read("src/executor/optimization.rs");
    let maxsmt_start = optimization
        .find("pub(in crate::executor) fn maxsmt_check_sat(")
        .expect("optimization must define maxsmt_check_sat");
    let maxsmt_end = optimization[maxsmt_start..]
        .find("fn maxsmt_assert(&mut self")
        .map(|offset| maxsmt_start + offset)
        .expect("maxsmt_check_sat must precede its assertion helper");
    let maxsmt = &optimization[maxsmt_start..maxsmt_end];

    let invalidate = maxsmt
        .find("self.last_model_validated = false;")
        .expect("MaxSMT must invalidate the last probe's validation evidence");
    let reinstall = maxsmt
        .find("self.last_model = captured_model;")
        .expect("MaxSMT must install its captured optimal witness");
    let classify = maxsmt
        .find("self.maxsmt_classification_roots(&softs, &captured_violations)")
        .expect("MaxSMT must turn its captured soft partition into validation roots");
    let emit = maxsmt
        .find("self.emit_sat_verdict(captured_result, &classification_roots)")
        .expect("MaxSMT must certify the captured witness against hard + classification roots");
    let reaccount = maxsmt
        .find("self.maxsmt_final_witness_accounting(&softs)")
        .expect("MaxSMT must recompute cost and partition from the final public model");
    let publish_cost = maxsmt
        .find("self.last_soft_cost = Some(captured_cost);")
        .expect("MaxSMT must publish cost only after witness admission");
    assert!(
        invalidate < reinstall
            && reinstall < classify
            && classify < emit
            && emit < reaccount
            && reaccount < publish_cost,
        "MaxSMT order must be invalidate -> replace witness -> bind partition -> validate/mint -> final re-account -> publish optimum"
    );
    assert!(
        maxsmt.contains("self.last_sat_certificate = None;")
            && maxsmt.contains("self.last_model = None;")
            && maxsmt.contains("self.last_soft_cost = None;")
            && maxsmt.contains("self.objective_certificates.clear();")
            && maxsmt.contains("Err(error) =>"),
        "a MaxSMT validation downgrade or error must clear witness, certificate, and optimum artefacts"
    );
}

/// (f2) Optimization transactions must restore the user assertion stack and
/// revoke probe artefacts on every non-admission path.
#[test]
fn optimization_transactions_restore_scope_and_fail_closed_on_errors() {
    let optimization = read("src/executor/optimization.rs");

    let lex_start = optimization
        .find("fn optimize_lex(&mut self")
        .expect("optimization must define optimize_lex");
    let lex_end = optimization[lex_start..]
        .find("fn optimize_box(&mut self")
        .map(|offset| lex_start + offset)
        .expect("optimize_lex must precede optimize_box");
    let lex = &optimization[lex_start..lex_end];
    let snapshot = lex
        .find("let assertion_snapshot = self.ctx.assertions.len();")
        .expect("lex must snapshot the user assertion stack");
    let commit = lex
        .find("self.optimization_assert(commit);")
        .expect("lex commits must keep parsed/elaborated assertion stacks aligned");
    let restore = lex
        .find("self.ctx.truncate_assertions(assertion_snapshot);")
        .expect("lex must restore transient commits on every closure exit");
    let finalize = lex
        .find("self.finalize_optimization(&finite_values, true)")
        .expect("lex must certify its selected optimum after restoration");
    assert!(
        snapshot < commit && commit < restore && restore < finalize,
        "lex order must be snapshot -> transient commit -> restore -> public certification"
    );
    assert!(
        lex.contains("Err(error) => {")
            && lex.contains("self.invalidate_last_check_result();")
            && lex.contains("Ok(false) => Ok(self.optimization_inconclusive())"),
        "lex errors and inconclusive probes must revoke partial admission state"
    );

    assert!(
        !optimization.contains("self.ctx.assertions.push(commit);")
            && !optimization.contains("self.ctx.assertions.push(b);")
            && optimization.contains("self.optimization_assert(b);"),
        "all transient lex/Pareto assertions must use the aligned assertion helper"
    );

    let inconclusive_start = optimization
        .find("fn optimization_inconclusive(&mut self)")
        .expect("optimization must define its inconclusive cleanup");
    let inconclusive_end = optimization[inconclusive_start..]
        .find("fn finalize_optimization(")
        .map(|offset| inconclusive_start + offset)
        .expect("inconclusive cleanup must precede finalization");
    let inconclusive = &optimization[inconclusive_start..inconclusive_end];
    for required in [
        "self.last_sat_certificate = None;",
        "self.last_model_validated = false;",
        "self.last_model = None;",
        "self.unbounded_objectives.clear();",
        "self.unavailable_objectives.clear();",
        "self.finite_objective_values.clear();",
        "self.objective_certificates.clear();",
        "self.pareto_state = None;",
        "self.last_result = Some(SolveResult::Unknown);",
    ] {
        assert!(
            inconclusive.contains(required),
            "inconclusive optimization must revoke `{required}`"
        );
    }
}

/// (f3) MaxSMT must not use `?` to escape from an engine outcome after an
/// internal relaxed-scope probe, and every later fallible exit must clean first.
#[test]
fn maxsmt_cleans_every_fallible_pre_admission_exit() {
    let optimization = read("src/executor/optimization.rs");
    let maxsmt_start = optimization
        .find("pub(in crate::executor) fn maxsmt_check_sat(")
        .expect("optimization must define maxsmt_check_sat");
    let maxsmt_end = optimization[maxsmt_start..]
        .find("fn maxsmt_assert(&mut self")
        .map(|offset| maxsmt_start + offset)
        .expect("maxsmt_check_sat must precede its assertion helper");
    let maxsmt = &optimization[maxsmt_start..maxsmt_end];

    assert!(
        !maxsmt.contains("= outcome?;"),
        "MaxSMT engine errors may follow successful probes and must not bypass cleanup via `?`"
    );
    let outcome_match = maxsmt
        .find("match outcome {")
        .expect("MaxSMT must explicitly classify its engine outcome");
    let outcome_error = maxsmt[outcome_match..]
        .find("Err(error) => {")
        .map(|offset| outcome_match + offset)
        .expect("MaxSMT must handle engine errors explicitly");
    let outcome_cleanup = maxsmt[outcome_error..]
        .find("self.invalidate_last_check_result();")
        .map(|offset| outcome_error + offset)
        .expect("MaxSMT engine errors must revoke probe artefacts");
    let outcome_return = maxsmt[outcome_error..]
        .find("return Err(error);")
        .map(|offset| outcome_error + offset)
        .expect("MaxSMT engine error must propagate");
    assert!(outcome_cleanup < outcome_return);

    assert!(
        maxsmt.contains("if hard_result.is_err() {")
            && maxsmt.contains("self.invalidate_last_check_result();"),
        "hard-only proof rerun errors must also revoke partial MaxSMT state"
    );

    let optimize_wrapper_start = optimization
        .find("pub(in crate::executor) fn optimize_check_sat(")
        .expect("optimization must define its fallible public wrapper");
    let optimize_wrapper = &optimization[optimize_wrapper_start..];
    assert!(
        optimize_wrapper.contains("if result.is_err() {")
            && optimize_wrapper.contains("self.invalidate_last_check_result();"),
        "every objective-engine error must revoke internal probe artefacts"
    );
}

/// (f4) The native MaxSMT API must reuse the executor transaction, restore the
/// parsed soft owner before handling the command result, and fail closed unless
/// the executor supplies independently checked exact accounting.
#[test]
fn native_maxsmt_is_transactional_exact_and_has_no_duplicate_solver() {
    let api = read("src/api/solving/maxsmt.rs");
    assert!(
        !api.contains("try_push(")
            && !api.contains("assert_at_most_k")
            && !api.contains("find_violated_softs"),
        "native MaxSMT must not reintroduce a duplicate relaxation/cardinality solver"
    );

    let query_start = api
        .find("pub fn check_sat_max(&mut self)")
        .expect("native API must define check_sat_max");
    let query = &api[query_start..];
    let retire = query
        .find("self.clear_last_solve_state(true, false);")
        .expect("native MaxSMT must retire the preceding query at entry");
    let reject = query
        .find("self.reject_composite_bv_cnf_export(\"check_sat_max\")?")
        .expect("native MaxSMT must reject unsupported artifact export");
    assert!(
        retire < reject,
        "retirement must precede fallible preflight"
    );

    let install = query
        .find(".replace_soft_constraints(native_softs)")
        .expect("native MaxSMT must transactionally install API softs");
    let execute = query
        .find("self.executor.execute(&Command::CheckSat)")
        .expect("native MaxSMT must reuse executor CheckSat dispatch");
    let restore = query
        .find(".replace_soft_constraints(parsed_softs)")
        .expect("native MaxSMT must restore the parsed soft set");
    let propagate_error = query
        .find("if let Err(error) = execution")
        .expect("native MaxSMT must handle executor errors after restoration");
    assert!(
        install < execute && execute < restore && restore < propagate_error,
        "native soft ownership order must be install -> execute -> restore -> classify"
    );

    assert!(
        query.contains("MAXSMT_EXACT_MAX_TOTAL_WEIGHT")
            && query.contains("soft.group.is_some()")
            && query.contains("if !optimal")
            && query.contains("self.executor.last_maxsmt_outcome()")
            && query.contains("recomputed_violated_weight != Some(violated_weight)")
            && query.contains("installed_native_softs != expected_native_softs"),
        "native MaxSMT must reject grouped/large/approximate/accounting- or transaction-inconsistent outcomes"
    );

    let result_type = read("src/api/types/maxsmt.rs");
    assert!(
        result_type.contains("pub violated_weight: u64")
            && result_type.contains("pub fn violated_weight(&self) -> u64")
            && result_type.contains("self.violated_weight"),
        "MaxSmtResult must store and return real violated-weight accounting"
    );

    let executor = read("src/executor/optimization.rs");
    assert!(
        executor.contains("self.last_soft_violations = Some(captured_violations);")
            && executor.contains("self.last_soft_violations = None;"),
        "executor must publish violated indices only with an admitted MaxSMT witness"
    );
}

/// (f5) Objective declarations, not term DAG nodes, own public outcomes. This
/// prevents duplicate same-term max/min objectives from overwriting finite box
/// values, infinities, or independently verified certificates.
#[test]
fn objective_outcomes_are_keyed_by_declaration_identity() {
    let executor = read("src/executor.rs");
    assert!(
        executor.contains("unbounded_objectives: HashMap<usize,")
            && executor.contains("objective_certificates: HashMap<usize,")
            && executor.contains("finite_objective_values: HashMap<usize,"),
        "all per-objective public artefacts must be keyed by declaration index"
    );

    let optimization = read("src/executor/optimization.rs");
    assert!(
        optimization.contains("fn objective_optimum(&self, objective_index: usize)")
            && optimization.contains(".extend(finite_values.iter().cloned())")
            && optimization.contains(".insert(objective_index, cert)")
            && optimization.contains(".insert(objective_index, ObjectiveDirection::Maximize)")
            && optimization.contains(".insert(objective_index, ObjectiveDirection::Minimize)"),
        "optimizer writes must preserve objective declaration identity"
    );

    let output = read("src/executor/model/output.rs");
    let api = read("src/api/solving/optimize.rs");
    assert!(
        output.contains("for (objective_index, obj) in self.ctx.objectives().iter().enumerate()")
            && output.contains("self.finite_objective_values.get(&objective_index)")
            && output.contains("self.objective_certificates.get(&objective_index)")
            && api.contains("self.executor.objective_optimum(idx)"),
        "SMT-LIB and native reads must use the same declaration index"
    );
}

/// (f6) A lexicographic suffix after an unbounded objective has no scalar exact
/// outcome. AY must stop, mark the suffix unavailable, and clear that marker on
/// every lifecycle/inconclusive path rather than independently optimizing it.
#[test]
fn unbounded_lex_prefix_never_fabricates_suffix_optima() {
    let optimization = read("src/executor/optimization.rs");
    let lex_start = optimization
        .find("fn optimize_lex(&mut self")
        .expect("optimization must define optimize_lex");
    let lex_end = optimization[lex_start..]
        .find("fn optimize_box(&mut self")
        .map(|offset| lex_start + offset)
        .expect("optimize_lex must precede optimize_box");
    let lex = &optimization[lex_start..lex_end];
    assert!(
        lex.contains("self.unbounded_objectives.contains_key(&objective_index)")
            && lex.contains(".extend((objective_index + 1)..objectives.len())")
            && lex.contains("return Ok(true);"),
        "lex must terminate and mark every suffix objective after an unbounded prefix"
    );

    let output = read("src/executor/model/output.rs");
    assert!(
        optimization.contains("self.unavailable_objectives.contains(&objective_index)")
            && output.contains("self.unavailable_objectives.contains(&objective_index)"),
        "native and SMT-LIB objective readers must reject unavailable suffix values"
    );

    let lifecycle = read("src/executor/lifecycle.rs");
    assert!(
        lifecycle
            .matches("self.unavailable_objectives.clear();")
            .count()
            >= 2
            && lifecycle.contains("unavailable_objectives: HashSet::default()"),
        "unavailable suffix state must be initialized and cleared with query artefacts"
    );
}

/// (f6b) An UNATTAINED (infinitesimal, #opt-epsilon) optimum is published only
/// behind BOTH full-solver twins, and it flows through the same
/// no-fabrication discipline as an unbounded one: the lex suffix is marked
/// unavailable (never independently optimized), every reader resolves the
/// epsilon record BEFORE the finite map, the native API maps it to
/// "no scalar" rather than a fabricated number, and the state clears with
/// every query artefact.
#[test]
fn epsilon_outcome_requires_twin_proofs_and_never_fabricates_scalars() {
    let optimization = read("src/executor/optimization.rs");

    // Each publication site (maximize + minimize) inserts into
    // `infinitesimal_objectives` only AFTER two full-solver probes inside the
    // OptimalInf arm: the refutation twin (finite part unattainable, UNSAT)
    // and the δ-closeness twin (near-sup point exists, SAT).
    for (fn_start, fn_end) in [
        ("fn maximize_real_objective(", "fn minimize_real_objective("),
        ("fn minimize_real_objective(", "fn mk_real_gt("),
    ] {
        let start = optimization.find(fn_start).expect("objective fn present");
        let end = optimization[start..]
            .find(fn_end)
            .map(|offset| start + offset)
            .expect("objective fn delimited");
        let body = &optimization[start..end];
        let arm_start = body
            .find("SimplexOpt::OptimalInf")
            .expect("OptimalInf arm present");
        let insert_at = body[arm_start..]
            .find("self.infinitesimal_objectives")
            .map(|offset| arm_start + offset)
            .expect("OptimalInf arm publishes the epsilon record");
        let arm_before_insert = &body[arm_start..insert_at];
        assert!(
            arm_before_insert
                .matches("self.check_sat_assuming(&[")
                .count()
                >= 2
                && arm_before_insert.contains("SolveResult::Unsat(_)")
                && arm_before_insert.contains("SolveResult::Sat"),
            "the epsilon record must be published only after the refutation \
             AND the δ-closeness full-solver twins: {fn_start}"
        );
    }

    // The audit-free Optimal(k=0) lane newly sees strict-bound problems: with
    // no verified certificate it must demand the full-solver maximality twin.
    assert!(
        optimization.contains("lra.has_strict_var_bound() && certificate.is_none()")
            && optimization.matches("needs_maximality_twin").count() >= 4,
        "strict-bound Optimal outcomes must carry the maximality-twin obligation"
    );

    // Lex: an infinitesimal prefix terminates the search and marks the whole
    // suffix unavailable, exactly like the unbounded case (f6).
    let lex_start = optimization
        .find("fn optimize_lex(&mut self")
        .expect("optimize_lex present");
    let lex_end = optimization[lex_start..]
        .find("fn optimize_box(&mut self")
        .map(|offset| lex_start + offset)
        .expect("optimize_lex delimited");
    let lex = &optimization[lex_start..lex_end];
    assert!(
        lex.contains("self.infinitesimal_objectives.contains_key(&objective_index)"),
        "lex must stop at an unattained prefix instead of committing its sup"
    );

    // Readers resolve the epsilon record BEFORE the finite map, in both the
    // SMT-LIB renderer and the structured native reader.
    let output = read("src/executor/model/output.rs");
    for (name, source) in [("output.rs", &output), ("optimization.rs", &optimization)] {
        let eps = source
            .find("infinitesimal_objectives.get(&objective_index)")
            .unwrap_or_else(|| panic!("{name} must read the epsilon record"));
        let finite = source
            .find("finite_objective_values.get(&objective_index)")
            .unwrap_or_else(|| panic!("{name} must read the finite map"));
        assert!(
            eps < finite,
            "{name}: epsilon outcomes must resolve before finite ones"
        );
    }

    // The native/FFI surface never fabricates a scalar for an epsilon outcome.
    let api = read("src/api/solving/optimize.rs");
    assert!(
        api.contains("ObjectiveOutcome::Epsilon { .. } => None"),
        "the native API must report no scalar for an unattained optimum"
    );

    // State lifecycle: initialized and cleared with every query artefact.
    let lifecycle = read("src/executor/lifecycle.rs");
    assert!(
        lifecycle
            .matches("self.infinitesimal_objectives.clear();")
            .count()
            >= 2
            && lifecycle.contains("infinitesimal_objectives: HashMap::default()"),
        "epsilon state must be initialized and cleared with query artefacts"
    );
    assert!(
        optimization
            .matches("self.infinitesimal_objectives.clear();")
            .count()
            >= 3,
        "epsilon state must clear on fresh-optimization, inconclusive, and \
         maxsmt-downgrade paths"
    );
}

/// (f7) The Z3 compatibility layer must capture the exact consumer-admissible
/// optimized witness. Re-solving selected softs after certification would sever
/// the exposed model from the MaxSMT accounting.
#[test]
fn ffi_optimize_captures_admitted_witness_without_reconstruction() {
    let ffi = read("../ay-ffi/src/z3_compat/optimize.rs");
    assert!(
        !ffi.contains("reconstruct_optimal_model")
            && ffi.matches("ctx.solver.model_for_consumer()").count() >= 2,
        "FFI arithmetic and MaxSMT lanes must capture the admitted model directly"
    );
    assert!(
        ffi.contains("has_objectives && (has_parsed_softs || has_api_softs)")
            && ffi.contains(
                "joint arithmetic-objective + soft-constraint optimization is not implemented"
            ),
        "unsupported mixed optimization must fail closed instead of ignoring one class"
    );
}

/// (g) A certificate is a one-query capability: lifecycle invalidation, public
/// solve entry, and funnel entry all revoke the old token before any fallible
/// work can run.
#[test]
fn prior_sat_certificate_is_revoked_before_new_fallible_work() {
    let lifecycle = read("src/executor/lifecycle.rs");
    let invalidation_start = lifecycle
        .find("pub(super) fn invalidate_last_check_result(&mut self)")
        .expect("lifecycle must define result invalidation");
    let public_solve_start = lifecycle[invalidation_start..]
        .find("pub(crate) fn begin_public_solve(")
        .map(|offset| invalidation_start + offset)
        .expect("lifecycle must define public-solve invalidation");
    let invalidation = &lifecycle[invalidation_start..public_solve_start];
    assert!(
        invalidation.contains("self.last_sat_certificate = None;"),
        "assertion/objective mutations must revoke the preceding SAT certificate"
    );

    let sat_emit = read("src/executor/model/sat_emit.rs");
    let funnel_start = sat_emit
        .find("pub(in crate::executor) fn emit_sat_verdict(")
        .expect("sat_emit must define the funnel");
    let funnel_end = sat_emit[funnel_start..]
        .find("fn apply_sat_validation_postcondition(")
        .map(|offset| funnel_start + offset)
        .expect("sat_emit must define its postcondition");
    let funnel = &sat_emit[funnel_start..funnel_end];
    let revoke = funnel
        .find("self.last_sat_certificate = None;")
        .expect("funnel entry must revoke the preceding certificate");
    let fallible_validation = funnel
        .find("self.finalize_sat_model_validation()?")
        .expect("funnel must contain fallible validation");
    let mint = funnel
        .rfind("self.last_sat_certificate = Some(SatCertificate(()));")
        .expect("funnel must mint only after admission");
    assert!(
        revoke < fallible_validation && fallible_validation < mint,
        "the funnel must revoke before fallible validation and mint only afterward"
    );

    let executor = read("src/executor.rs");
    assert!(
        executor.contains("if matches!(cmd, Command::CheckSat | Command::CheckSatAssuming(_)) {")
            && executor.contains("self.begin_public_solve(true);"),
        "SMT-LIB decision commands must retire stale artefacts before elaboration"
    );
}

/// (g2) The public result wrapper must not expose a caller-chosen validation
/// bit. Tests may fabricate rejection cases only inside ay-dpll, while ay-ffi
/// injects an already-rejected outcome through a cfg(test)-only local helper.
#[test]
fn verified_result_exposes_no_public_sat_fabrication_capability() {
    let results = read("src/api/types/results.rs");
    assert!(
        !results.contains("pub fn for_testing("),
        "VerifiedSolveResult must not ship a public caller-chosen validation constructor"
    );
    assert!(
        results.contains("#[cfg(test)]\n    pub(crate) fn for_testing("),
        "the fabrication helper must be both cfg(test) and crate-private"
    );
    assert!(
        results.contains("pub(crate) fn certified_sat(_certificate: SatCertificate)")
            && results.contains("pub(crate) fn certified_unsat(")
            && results.contains("pub(crate) fn unknown()")
            && !results.contains("pub(crate) fn from_validated("),
        "definite construction must stay crate-private and require an exact capability"
    );
    assert!(
        !results.contains(
            "result: SolveResult,\n        model_validated: bool,\n        sat_certificate: Option<SatCertificate>"
        ) && results.contains("model_validated: true"),
        "SAT validation provenance must be derived from the consumed certificate, not a caller-supplied bool"
    );
    assert!(
        results.contains("```compile_fail")
            && results.contains("VerifiedSolveResult::for_testing(SolveResult::Sat, true)"),
        "the public API must carry a negative compile test for SAT fabrication"
    );

    let ffi_solver = read("../ay-ffi/src/z3_compat/solver.rs");
    assert!(
        ffi_solver.contains(
            "#[cfg(test)]\npub(super) fn solve_lbool_from_consumer_rejection_for_testing("
        ),
        "ay-ffi may inject a rejection only through a non-shipping local helper"
    );
    let ffi_tests = read("../ay-ffi/src/z3_compat/tests.rs");
    assert!(
        !ffi_tests.contains("VerifiedSolveResult::for_testing"),
        "cross-crate tests must not require a production SAT-fabrication capability"
    );

    let sat_emit = read("src/executor/model/sat_emit.rs");
    assert!(
        sat_emit.contains("#[derive(Debug)]\npub(crate) struct SatCertificate(());")
            && !sat_emit.contains("#[derive(Debug, Clone)]\npub(crate) struct SatCertificate"),
        "the one-shot SAT capability must not be clonable"
    );
}

/// (g3) A tactic wrapper performs fallible transformation work before the
/// ordinary Solver entrypoint. It must therefore retire the preceding query at
/// wrapper entry and again after any partially-solving composite tactic fails.
#[test]
fn tactic_query_failures_cannot_reuse_preceding_solve_artefacts() {
    let tactics = read("src/api/solving/tactics.rs");
    let wrapper_start = tactics
        .find("impl TacticSolver {")
        .expect("tactics must define TacticSolver");
    let apply_start = tactics[wrapper_start..]
        .find("impl Solver {")
        .map(|offset| wrapper_start + offset)
        .expect("TacticSolver methods must precede Solver tactic helpers");
    let wrappers = &tactics[wrapper_start..apply_start];

    for (entry, clear) in [
        (
            "pub fn check_sat(&mut self)",
            "clear_last_solve_state(true, false)",
        ),
        (
            "pub fn check_sat_assuming(&mut self, assumptions: &[Term])",
            "clear_last_solve_state(false, false)",
        ),
    ] {
        let start = wrappers
            .find(entry)
            .unwrap_or_else(|| panic!("TacticSolver must define {entry}"));
        let body = &wrappers[start..];
        let retire = body
            .find(clear)
            .unwrap_or_else(|| panic!("{entry} must retire the preceding public result"));
        let transform = body
            .find("apply_tactic(&self.tactic)")
            .unwrap_or_else(|| panic!("{entry} must apply its tactic"));
        assert!(
            retire < transform,
            "{entry} must revoke stale artefacts before fallible tactic work"
        );
    }

    let error_helper = tactics
        .find("pub(crate) fn set_internal_error_unknown(&mut self, detail: &str)")
        .expect("tactic errors must use a shared fail-closed helper");
    let error_tail = &tactics[error_helper..];
    let revoke = error_tail
        .find("self.executor.begin_public_solve(false);")
        .expect("a failed composite tactic must revoke partial internal solves");
    let diagnose = error_tail
        .find("self.last_unknown_reason = Some(crate::UnknownReason::InternalError);")
        .expect("failed tactics must publish an InternalError reason");
    assert!(
        revoke < diagnose,
        "partial tactic solve artefacts must be revoked before Unknown is diagnosed"
    );
}

/// (h) Trivial string fast paths install their final witness before marking it
/// validated.  Validation evidence must never be allowed to describe the model
/// that happened to precede the current public solve.
#[test]
fn trivial_string_fast_paths_validate_the_model_they_publish() {
    for rel in [
        "src/executor/theories/strings.rs",
        "src/executor/theories/strings_lia.rs",
    ] {
        let src = read(rel);
        let install = src
            .find("self.last_model = Some(super::super::model::Model {")
            .unwrap_or_else(|| panic!("{rel} must install its trivial-SAT model"));
        let validate = src
            .find("self.last_model_validated = true;")
            .unwrap_or_else(|| panic!("{rel} must record trivial-SAT validation evidence"));
        let return_sat = src[validate..]
            .find("return Ok(SolveResult::Sat);")
            .map(|offset| validate + offset)
            .unwrap_or_else(|| panic!("{rel} must return its trivial SAT verdict"));

        assert!(
            install < validate && validate < return_sat,
            "{rel} must install the final witness before attaching validation evidence"
        );
    }
}

/// (i) The funnel's authoritative gate is reachable from the independent gate's
/// module and routes its downgrade through the proven `gate_keeps_sat` core.
#[test]
fn authoritative_gate_routes_through_the_proven_core() {
    let gate = read("src/executor/model/independent_gate.rs");
    assert!(
        gate.contains("fn apply_authoritative_failclosed_gate(")
            && gate.contains("fn assertion_is_authoritatively_ground("),
        "independent_gate.rs must define the authoritative-failclosed gate and its \
         authoritative-ground predicate"
    );
    assert!(
        gate.contains("gate_keeps_sat(true, /* confirmed = */ false, ENFORCE_ON_REFUTATION)"),
        "the authoritative gate must route its keep/downgrade decision through the proven \
         `gate_keeps_sat` core with unconditional enforcement"
    );
}
