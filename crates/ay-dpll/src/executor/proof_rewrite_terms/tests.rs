// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::{NraSosCertificate, NraSosOrigin, NraSosRational, NraSosTerm, ProofId, Sort};
use ay_frontend::command::Term as FrontendTerm;
use num_bigint::BigInt;
use num_rational::BigRational;

fn rational(value: i64) -> NraSosRational {
    NraSosRational {
        numerator: BigInt::from(value),
        denominator: BigInt::from(1u8),
    }
}

struct Fixture {
    lemma: ProofStep,
    x: TermId,
    lower: TermId,
    not_upper: TermId,
}

fn fixture(terms: &mut TermStore) -> Fixture {
    let x = terms.mk_var("rewrite_sos_x", Sort::Real);
    let zero = terms.mk_rational(BigRational::from_integer(BigInt::from(0u8)));
    let one = terms.mk_rational(BigRational::from_integer(BigInt::from(1u8)));
    let lower = terms.mk_ge(x, one);
    let upper = terms.mk_le(x, zero);
    let not_lower = terms.mk_not_raw(lower);
    let not_upper = terms.mk_not_raw(upper);
    Fixture {
        lemma: ProofStep::NraSos {
            clause: vec![not_lower, not_upper],
            certificate: NraSosCertificate {
                basis: vec![vec![], vec![x]],
                gram: vec![vec![rational(0); 2]; 2],
                terms: (0..2)
                    .map(|position| NraSosTerm {
                        origin: NraSosOrigin::ClauseLiteral { position },
                        multiplier: rational(1),
                    })
                    .collect(),
                rhs: rational(-1),
            },
        },
        x,
        lower,
        not_upper,
    }
}

#[test]
fn source_bound_sos_refuses_the_whole_rewrite_atomically() {
    for position in 0..=2 {
        for rewrite_x in [false, true] {
            let mut terms = TermStore::new();
            let fixture = fixture(&mut terms);
            let y = terms.mk_var("rewrite_sos_y", Sort::Real);
            let mut proof = Proof::new();
            // Rewriting this prefix would both change the proof and intern
            // new comparison terms before reaching a later SOS step.
            proof.add_assume(fixture.lower, Some("ordinary_prefix".to_string()));
            proof.add_rule_step(
                AletheRule::ThResolution,
                vec![fixture.lower, fixture.lower],
                vec![],
                vec![fixture.x],
            );
            proof.steps.insert(position, fixture.lemma);
            let mut rewrites = HashMap::default();
            if rewrite_x {
                rewrites.insert(fixture.x, y);
            }
            let original_proof = proof.clone();
            let original_entries = terms.entries_snapshot();
            let stamp = terms.snapshot_stamp();
            let metadata = terms.checker_visible_metadata_generation();
            let variables = terms.var_counter();

            assert_eq!(
                Executor::rewrite_proof_terms(&mut terms, &mut proof, &rewrites),
                Err(ProofTermRewriteError::SourceBoundSos { step: position })
            );
            assert_eq!(proof, original_proof);
            assert_eq!(terms.entries_snapshot(), original_entries);
            assert_eq!(terms.snapshot_stamp(), stamp);
            assert_eq!(terms.checker_visible_metadata_generation(), metadata);
            assert_eq!(terms.var_counter(), variables);
        }
    }
}

#[test]
fn direct_resolution_fixup_uses_the_actual_sos_clause() {
    for rule in [AletheRule::Resolution, AletheRule::ThResolution] {
        let mut terms = TermStore::new();
        let fixture = fixture(&mut terms);
        let original_lemma = fixture.lemma.clone();
        let mut proof = Proof::new();
        let lemma = proof.add_step(fixture.lemma);
        let assumption = proof.add_assume(fixture.lower, None);
        let conclusion = proof.add_rule_step(rule, vec![], vec![lemma, assumption], vec![]);
        let stamp = terms.snapshot_stamp();

        Executor::fixup_resolution_conclusions(&terms, &mut proof);

        assert_eq!(proof.steps[lemma.0 as usize], original_lemma);
        assert!(matches!(
            &proof.steps[conclusion.0 as usize],
            ProofStep::Step { clause, .. } if clause == &[fixture.not_upper]
        ));
        assert_eq!(terms.snapshot_stamp(), stamp);
    }
}

#[test]
fn production_surface_rewrite_poisons_sos_before_all_source_passes() {
    // Exercise no assertions, retained source syntax, and retention-off. The
    // refusal must precede every early return as well as the mutable passes.
    for source_case in 0..3 {
        let mut executor = Executor::new();
        let fixture = fixture(&mut executor.ctx.terms);
        if source_case != 0 {
            let source = executor.ctx.terms.mk_var("surface_input", Sort::Bool);
            if source_case == 2 {
                executor.ctx.set_retain_parsed_assertions(false);
            }
            executor.ctx.add_assertion_with_parsed(
                source,
                FrontendTerm::Symbol("surface_input".to_string()),
            );
        }
        let mut proof = Proof::from_steps(vec![fixture.lemma]);
        ay_proof::authenticate_premise_clauses_strict_with_context(
            &proof,
            &executor.ctx.terms,
            None,
            None,
            &[],
        )
        .expect("the original source-bound SOS theorem checks independently");
        let mut overrides = HashMap::default();
        overrides.insert(fixture.lower, "false".to_string());
        executor.last_proof_term_overrides = Some(overrides);
        let original_entries = executor.ctx.terms.entries_snapshot();
        let stamp = executor.ctx.terms.snapshot_stamp();
        let metadata = executor.ctx.terms.checker_visible_metadata_generation();

        executor.apply_input_syntax_rewrites_to_proof(&mut proof);

        assert!(executor.last_proof_term_overrides.is_none());
        assert_eq!(executor.ctx.terms.entries_snapshot(), original_entries);
        assert_eq!(executor.ctx.terms.snapshot_stamp(), stamp);
        assert_eq!(
            executor.ctx.terms.checker_visible_metadata_generation(),
            metadata
        );
        assert!(ay_proof::terminal_trust_report(&proof).has_terminal_trust());
        assert_eq!(
            ay_proof::check_proof_strict(&proof, &executor.ctx.terms),
            Err(ay_proof::ProofCheckError::TrustStep { step: ProofId(0) })
        );
    }
}
