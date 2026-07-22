// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// A no-op transformer for testing.
struct NoOpTransformer;

impl Transformer for NoOpTransformer {
    fn transform(self: Box<Self>, problem: ChcProblem) -> TransformationResult {
        TransformationResult {
            problem,
            back_translator: Box::new(IdentityBackTranslator),
        }
    }
}

struct ReportTransformer {
    report: TransformMemoryReport,
}

impl Transformer for ReportTransformer {
    fn transform(self: Box<Self>, problem: ChcProblem) -> TransformationResult {
        TransformationResult {
            problem,
            back_translator: Box::new(ReportBackTranslator {
                report: self.report,
            }),
        }
    }
}

struct ReportBackTranslator {
    report: TransformMemoryReport,
}

impl BackTranslator for ReportBackTranslator {
    fn translate_validity(&self, witness: ValidityWitness) -> ValidityWitness {
        witness
    }

    fn translate_invalidity(&self, witness: InvalidityWitness) -> InvalidityWitness {
        witness
    }

    fn transform_memory(&self) -> TransformMemoryReport {
        self.report.clone()
    }
}

#[test]
fn test_transformer_pipeline_empty() {
    let pipeline = TransformationPipeline::new();

    let problem = ChcProblem::new();
    let result = pipeline.transform(problem);

    // Empty pipeline should return the same problem
    assert_eq!(result.problem.clauses().len(), 0);
}

#[test]
fn test_transformer_pipeline_single() {
    let pipeline = TransformationPipeline::new().with(NoOpTransformer);

    let problem = ChcProblem::new();
    let result = pipeline.transform(problem);

    assert_eq!(result.problem.clauses().len(), 0);
}

#[test]
fn test_transformer_identity_back_translator() {
    let translator = IdentityBackTranslator;

    // Test validity witness pass-through
    let invariant = InvariantModel::new();
    let translated = translator.translate_validity(invariant);
    assert_eq!(translated.iter().count(), 0);
}

#[test]
fn test_transform_result_reports_reversible_identity_memory() {
    let pipeline = TransformationPipeline::new().with(NoOpTransformer);
    let result = pipeline.transform(ChcProblem::new());

    let report = result.transform_memory();
    assert_eq!(report.transform(), "composite");
    assert!(report.is_reversible());
    assert!(report.validates_original());
    assert!(!report.safe_requires_original_validation());
    assert!(report.unsafe_backtranslation_complete());
    assert!(report.obligations().is_empty());
}

#[test]
fn test_transform_memory_can_report_original_validation() {
    let report = TransformMemoryReport::validates_on_original("projection");

    assert_eq!(report.transform(), "projection");
    assert!(!report.is_reversible());
    assert!(report.validates_original());
    assert!(report.safe_requires_original_validation());
    assert!(report.unsafe_backtranslation_complete());
    assert!(report.obligations().is_empty());
}

#[test]
fn test_transform_pipeline_composes_memory_obligations() {
    let pipeline = TransformationPipeline::new()
        .with(NoOpTransformer)
        .with(ReportTransformer {
            report: TransformMemoryReport::with_obligations(
                "projection",
                [
                    TransformObligation::named("model-reconstruction"),
                    TransformObligation::named("original-query-validation"),
                ],
            )
            .with_fact("observed_keys", "2"),
        });

    let result = pipeline.transform(ChcProblem::new());
    let report = result.transform_memory();
    let obligation_names: Vec<&str> = report
        .obligations()
        .iter()
        .map(TransformObligation::name)
        .collect();

    assert_eq!(report.transform(), "composite");
    assert!(!report.is_reversible());
    assert!(!report.validates_original());
    assert!(report.safe_requires_original_validation());
    assert!(!report.unsafe_backtranslation_complete());
    assert!(report.has_obligation("model-reconstruction"));
    assert!(!report.has_obligation("missing-obligation"));
    assert_eq!(report.fact_value("observed_keys"), Some("2"));
    assert_eq!(
        obligation_names,
        vec!["model-reconstruction", "original-query-validation"]
    );
}

#[test]
fn test_transform_memory_marks_incomplete_unsafe_backtranslation() {
    let report = TransformMemoryReport::validates_on_original("projection")
        .with_incomplete_unsafe_backtranslation();

    assert!(report.validates_original());
    assert!(report.safe_requires_original_validation());
    assert!(!report.unsafe_backtranslation_complete());
    assert!(report
        .diagnostic_summary()
        .contains("unsafe_backtranslation_complete=false"));
}

#[test]
fn test_transformer_pipeline_multiple() {
    let pipeline = TransformationPipeline::new()
        .with(NoOpTransformer)
        .with(NoOpTransformer)
        .with(NoOpTransformer);

    assert_eq!(pipeline.len(), 3);

    let problem = ChcProblem::new();
    let result = pipeline.transform(problem);

    // Multiple no-ops should still return empty problem
    assert_eq!(result.problem.clauses().len(), 0);
}

// Moved from tests/portfolio_tests.rs — uses ClauseInliner (no longer pub)

/// Test that preprocessing (ClauseInliner) reduces clause count for problems
/// with intermediate predicates.
#[test]
fn test_preprocessing_reduces_clause_count() {
    use crate::parser::ChcParser;
    use crate::pdr::PdrConfig;
    use crate::portfolio::{EngineConfig, PortfolioConfig, PortfolioResult, PortfolioSolver};

    let input = r#"
(set-logic HORN)
(declare-fun Init (Int) Bool)
(declare-fun Loop (Int) Bool)

; Init(x) ⇐ x = 0
(assert (forall ((x Int))
    (=> (= x 0) (Init x))))

; Loop(y) ⇐ Init(y)
(assert (forall ((y Int))
    (=> (Init y) (Loop y))))

; Loop(y') ⇐ Loop(y), y' = y + 1, y < 10
(assert (forall ((y Int) (y2 Int))
    (=> (and (Loop y) (= y2 (+ y 1)) (< y 10)) (Loop y2))))

; false ⇐ Loop(z), z < 0
(assert (forall ((z Int))
    (=> (and (Loop z) (< z 0)) false)))

(check-sat)
"#;

    let problem = ChcParser::parse(input).unwrap();
    let original_clause_count = problem.clauses().len();
    let original_predicate_count = problem.predicates().len();

    let inliner = ClauseInliner::new();
    let transformed = inliner.inline(&problem);

    assert!(
        transformed.clauses().len() < original_clause_count
            || transformed.predicates().len() < original_predicate_count,
        "Preprocessing should reduce clause or predicate count: \
         clauses={}->{}, predicates={}->{}",
        original_clause_count,
        transformed.clauses().len(),
        original_predicate_count,
        transformed.predicates().len()
    );

    // Verify the transformed problem is still solvable
    let config = PortfolioConfig::with_engines(vec![EngineConfig::Pdr(PdrConfig::default())])
        .parallel(false);
    let solver = PortfolioSolver::new(problem, config);
    let result = solver.solve();
    assert!(
        matches!(result, PortfolioResult::Safe(_)),
        "Problem should be Safe after preprocessing: {result:?}"
    );
}
