// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::transform::{BackTranslator, ClauseInliner, Transformer};
use crate::CancellationToken;

fn original_problem() -> ChcProblem {
    ChcParser::parse(
        r#"
        (set-logic HORN)
        (declare-rel P ((_ BitVec 2) Bool))
        (declare-rel Q ((_ BitVec 2) Bool))
        (declare-var x (_ BitVec 2))
        (declare-var b Bool)
        (rule (=> (and (= x #b00) b) (P x b)))
        (rule (=> (and (= x #b01) b) (P x b)))
        (rule (=> (P x b) (Q x b)))
        (rule (=> (and (Q x b) (not b)) false))
        (check-sat)
    "#,
    )
    .unwrap()
}

fn inlined_summary(original: &ChcProblem) -> PreprocessSummary {
    let transformed =
        Box::new(ClauseInliner::new().preserve_query_body_predicates()).transform(original.clone());
    assert_eq!(transformed.problem.predicates().len(), 1);
    assert_eq!(transformed.problem.predicates()[0].name, "Q");
    let transform_memory = transformed.transform_memory();
    assert!(!transform_memory.is_equisat_grade());
    PreprocessSummary {
        original_problem: original.clone(),
        transformed_problem: transformed.problem,
        back_translator: transformed.back_translator,
        bv_abstracted: false,
        transform_memory,
    }
}

#[test]
#[timeout(60000)]
fn empty_acyclic_survivor_reconstructs_compacted_original_model() {
    let original = original_problem();
    let summary = inlined_summary(&original);
    assert!(summary
        .back_translator
        .translate_validity(InvariantModel::default())
        .get(&original.lookup_predicate("Q").unwrap())
        .is_none());
    let adaptive = AdaptivePortfolio::new(
        original.clone(),
        AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(20)),
    );
    let deadline = Instant::now() + Duration::from_secs(15);
    let result = adaptive.run_preprocessed_acyclic_bmc_probe_until(
        summary,
        &adaptive.features(),
        deadline,
        "test-survivor",
        true,
        &adaptive.cancellation_token,
    );
    let Some((PortfolioResult::Safe(model), evidence)) = result else {
        panic!("complete original model required, got {result:?}");
    };
    assert_eq!(evidence, ValidationEvidence::FullVerification);
    assert_eq!(model.len(), original.predicates().len());
    assert!(adaptive.validate_preprocessed_safe_model(
        &model,
        "test-survivor-recheck",
        deadline,
        &adaptive.cancellation_token
    ));
}

#[test]
#[timeout(60000)]
fn fabricated_safe_survivor_cannot_hide_unsafe_original_definition() {
    let safe_original = original_problem();
    let mut original = safe_original.clone();
    let clause = &mut original.clauses_mut()[1];
    let ClauseHead::Predicate(_, args) = &clause.head else {
        panic!("fact");
    };
    clause.body.constraint = Some(ChcExpr::and(
        ChcExpr::eq(args[0].clone(), ChcExpr::BitVec(1, 2)),
        ChcExpr::not(args[1].clone()),
    ));
    let mut fabricated = inlined_summary(&safe_original);
    fabricated.original_problem = original.clone();
    let adaptive = AdaptivePortfolio::new(
        original,
        AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(20)),
    );
    assert!(
        adaptive
            .run_preprocessed_acyclic_bmc_probe_until(
                fabricated,
                &adaptive.features(),
                Instant::now() + Duration::from_secs(15),
                "test-fabricated-survivor",
                true,
                &adaptive.cancellation_token,
            )
            .is_none(),
        "candidate must pass every ORIGINAL defining clause"
    );
}

struct CancelAfterTranslation {
    inner: Box<dyn BackTranslator>,
    cancellation: CancellationToken,
    called: std::sync::Arc<std::sync::atomic::AtomicBool>,
}

impl BackTranslator for CancelAfterTranslation {
    fn translate_validity(&self, witness: InvariantModel) -> InvariantModel {
        assert!(
            !witness.is_empty(),
            "must reach candidate, not an empty proof fallback"
        );
        let translated = self.inner.translate_validity(witness);
        self.called
            .store(true, std::sync::atomic::Ordering::Relaxed);
        self.cancellation.cancel();
        translated
    }

    fn translate_invalidity(&self, witness: Counterexample) -> Counterexample {
        self.inner.translate_invalidity(witness)
    }
}

#[test]
#[timeout(60000)]
fn cancellation_after_survivor_projection_cannot_fall_back_to_empty_safe() {
    let original = original_problem();
    let mut summary = inlined_summary(&original);
    let caller = CancellationToken::new();
    let called = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
    summary.back_translator = Box::new(CancelAfterTranslation {
        inner: summary.back_translator,
        cancellation: caller.clone(),
        called: called.clone(),
    });
    let adaptive = AdaptivePortfolio::new(
        original,
        AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(20)),
    );
    assert!(adaptive
        .run_preprocessed_acyclic_bmc_probe_until(
            summary,
            &adaptive.features(),
            Instant::now() + Duration::from_secs(15),
            "test-cancel-survivor",
            true,
            &caller,
        )
        .is_none());
    assert!(called.load(std::sync::atomic::Ordering::Relaxed));
    caller.reset();
    assert!(
        !adaptive.cancellation_token.is_cancelled(),
        "no upward cancellation writes"
    );
}

struct DiscardCandidate;

impl BackTranslator for DiscardCandidate {
    fn translate_validity(&self, witness: InvariantModel) -> InvariantModel {
        assert!(!witness.is_empty());
        InvariantModel::default()
    }

    fn translate_invalidity(&self, witness: Counterexample) -> Counterexample {
        witness
    }
}

#[test]
#[timeout(60000)]
fn invalid_candidate_retains_only_the_existing_equisat_empty_fallback() {
    let original = original_problem();
    let summary = inlined_summary(&original);
    let transformed = summary.transformed_problem;
    let adaptive = AdaptivePortfolio::new(
        transformed.clone(),
        AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(20)),
    );
    let summary = PreprocessSummary {
        original_problem: transformed.clone(),
        transformed_problem: transformed,
        back_translator: Box::new(DiscardCandidate),
        bv_abstracted: false,
        // The PROBLEM is unchanged here; only candidate construction fails.
        transform_memory: crate::transform::TransformMemoryReport::identity(),
    };
    let result = adaptive.run_preprocessed_acyclic_bmc_probe_until(
        summary,
        &adaptive.features(),
        Instant::now() + Duration::from_secs(15),
        "test-survivor-existing-fallback",
        true,
        &adaptive.cancellation_token,
    );
    let Some((PortfolioResult::Safe(model), evidence)) = result else {
        panic!("existing equisat exhaustion must remain available: {result:?}");
    };
    assert!(model.is_empty(), "do not return the failed candidate");
    assert!(matches!(
        evidence,
        ValidationEvidence::ScalarAcyclicBmcExhaustive { .. }
    ));
}
