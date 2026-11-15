// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The cata route's PDR counterexamples name the abstraction's clauses.

use super::*;

/// The cata route's element level {Size, RootDisc, Min, Sorted} abstracts
/// `all_lists_unsafe_problem` to three clauses whose transition carries two
/// `ite`s (the `Min` and `Sorted` updates). The route's nested portfolio races
/// PDR, TPA and TRL on it. PDR case-splits those `ite`s before searching, and
/// its counterexample used to name the SPLIT problem's clauses (`query_clause`
/// 4 of the 3-clause abstraction): whenever PDR won the race, the portfolio's
/// Unsafe validation tripped the clause-index precondition in
/// `pdr/verification/cex.rs` (about 1 run in 8). Each PDR variant of that
/// portfolio (`simple_loop_portfolio_config`), run alone, has no race to lose.
#[test]
fn pdr_unsafe_on_the_cata_element_abstraction_names_its_clauses() {
    use crate::transform::cata_abstract::{CataAbstraction, CataKind};
    use crate::{CexVerificationResult, PdrConfig, PdrResult, PdrSolver};
    let _guard = lock_env();
    let kinds = [
        CataKind::Size,
        CataKind::RootDisc,
        CataKind::Min,
        CataKind::Sorted,
    ];
    let abstraction =
        CataAbstraction::build(&all_lists_unsafe_problem(), &kinds).expect("abstraction applies");
    let problem = abstraction.abstract_problem.clone();
    let clauses = problem.clauses();
    assert_eq!(clauses.len(), 3);
    let variants = [
        PdrConfig {
            use_lemma_hints: true,
            ..PdrConfig::default()
        },
        PdrConfig {
            use_lemma_hints: true,
            ..PdrConfig::portfolio_spacer_variant()
        },
    ];
    for (variant, config) in variants.into_iter().enumerate() {
        let PdrResult::Unsafe(cex) = PdrSolver::new(problem.clone(), config).solve() else {
            panic!("variant {variant}: PDR refutes the abstraction");
        };
        let witness = cex.witness.as_ref().expect("PDR's witness is kept");
        for entry in &witness.entries {
            if let Some(index) = entry.incoming_clause {
                assert!(index < clauses.len(), "variant {variant}: clause {index}");
                assert!(matches!(
                    &clauses[index].head,
                    crate::ClauseHead::Predicate(head, _) if *head == entry.predicate
                ));
            }
        }
        let query = witness.query_clause.expect("the witness names its query");
        assert!(query < clauses.len(), "variant {variant}: query {query}");
        assert!(clauses[query].is_query());
        let validation = PdrConfig {
            preserve_original_clauses: true,
            ..PdrConfig::default()
        };
        assert_eq!(
            PdrSolver::new(problem.clone(), validation).verify_counterexample(&cex),
            CexVerificationResult::Valid,
            "variant {variant}"
        );
    }
}
