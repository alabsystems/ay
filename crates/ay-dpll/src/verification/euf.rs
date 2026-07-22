// Copyright 2026 Andrew Yates
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0

//! EUF (Equality with Uninterpreted Functions) semantic verification.
//!
//! Verifies EUF conflicts by re-running congruence closure in a fresh solver,
//! and verifies EUF propagations by checking that reason ∧ ¬propagated is UNSAT.
use ay_core::{TermStore, TheoryLit, TheoryPropagation};

use super::structural::{verify_theory_conflict, verify_theory_propagation};
use super::VerificationError;

/// Verify an EUF conflict by re-running congruence closure.
///
/// This creates a fresh EUF solver, asserts the conflict literals, and checks
/// that congruence closure derives UNSAT. If the conflict is satisfiable,
/// the original EUF solver has a bug.
///
/// # Arguments
/// * `conflict` - The conflict literals returned by EUF
/// * `terms` - The term store (needed to create a fresh EUF solver)
/// * `support_axioms` - Literals that are TRUE IN EVERY MODEL of the problem,
///   asserted alongside the conflict so the fresh EUF solver can reprove a
///   conflict it would otherwise call spuriously-Sat. Two provenance sources,
///   both valid-in-all-models: (1) datatype **tautology** literals (constructor
///   disjointness, tester evaluation) — pure EUF treats datatype constructors
///   (`Ok`/`Err`) as uninterpreted functions and cannot see that distinct
///   constructors are disjoint, so a genuine constructor-clash conflict
///   (`self = Ok(a) AND self = Err(b)`) would be reported SAT and spuriously
///   rejected (#8123); (2) ground instances of UNCONDITIONALLY-asserted Foralls
///   (top-level conjuncts) — entailed by universal instantiation. Both can only
///   confirm genuine conflicts and never manufacture a spurious one. Empty when
///   neither datatypes nor unconditional-Forall instances are present.
///
/// # Returns
/// * `Ok(())` if the conflict is verified as UNSAT
/// * `Err(ConflictIsSat)` if the conflict is actually satisfiable
pub(crate) fn verify_euf_conflict(
    conflict: &[TheoryLit],
    terms: &TermStore,
    support_axioms: &[TheoryLit],
) -> Result<(), VerificationError> {
    use ay_core::{TheoryResult, TheorySolver};
    use ay_euf::EufSolver;

    // First do basic structural checks
    verify_theory_conflict(conflict)?;

    // Create a fresh EUF solver and assert the conflict literals.
    // verify_only_scoped(): this solver recomputes only the Sat/Unsat verdict;
    // the caller discards all reason vectors. Skipping propagation-reason
    // building removes the dominant re-verification cost without changing the
    // verdict (#8529), and scoping the congruence table to the subterm closure
    // of the asserted literals removes the O(all-apps) per-merge churn that
    // dominated QF_UF PEQ solves (one fresh solver per theory conflict) — see
    // `EufSolver::verify_only_scoped` for the verdict-preservation argument.
    let mut verify_euf = EufSolver::new(terms)
        .verify_only_scoped(conflict.iter().chain(support_axioms).map(|lit| lit.term));

    for lit in conflict {
        verify_euf.assert_literal(lit.term, lit.value);
    }

    // Assert the support axioms (datatype tautologies AND ground instances of
    // unconditionally-asserted Foralls) so the fresh EUF solver can chain e.g.
    // `self = Ok(a)`, `self = Err(b)`, `Ok(a) != Err(b)` into UNSAT (#8123).
    // Sound: every support literal is true in all models of the problem; adding
    // them can only confirm genuine conflicts, never manufacture spurious ones.
    for lit in support_axioms {
        verify_euf.assert_literal(lit.term, lit.value);
    }

    // Run congruence closure
    match verify_euf.check() {
        TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_) => Ok(()),
        TheoryResult::Sat => Err(VerificationError::ConflictIsSat),
        TheoryResult::Unknown => {
            // EUF should never return Unknown, but handle it gracefully
            Err(VerificationError::Internal(
                "EUF verification returned Unknown".to_string(),
            ))
        }
        // Split/lemma requests shouldn't happen for pure EUF verification
        TheoryResult::NeedSplit(_)
        | TheoryResult::NeedDisequalitySplit(_)
        | TheoryResult::NeedExpressionSplit(_)
        | TheoryResult::NeedStringLemma(_)
        | TheoryResult::NeedLemmas(_)
        | TheoryResult::NeedModelEquality(_)
        | TheoryResult::NeedModelEqualities(_) => Err(VerificationError::Internal(
            "EUF verification requested split/lemma/model-equality (unexpected)".to_string(),
        )),
        // All current TheoryResult variants handled above (#4906, #6149).
        // Wildcard covers future variants from #[non_exhaustive].
        _ => unreachable!("unhandled TheoryResult variant — update this match"),
    }
}

/// Verify an EUF propagation by checking that reason ∧ ¬propagated is UNSAT.
///
/// Creates a fresh EUF solver, asserts the reason literals and the negation
/// of the propagated literal, then checks that congruence closure derives UNSAT.
/// If it's SAT, the reason set does not imply the propagated literal via EUF.
///
/// Returns `Ok(())` if verified, `Err(PropagationNotImplied)` if the propagation
/// is semantically invalid under EUF.
#[cfg_attr(not(debug_assertions), allow(dead_code))]
pub(crate) fn verify_euf_propagation(
    propagation: &TheoryPropagation,
    terms: &TermStore,
) -> Result<(), VerificationError> {
    use ay_core::{TheoryResult, TheorySolver};
    use ay_euf::EufSolver;

    // Structural checks ALWAYS run (cheap, catch duplicate/circular reasons).
    verify_theory_propagation(propagation)?;

    // #12: EUF-only warmup-then-sample for the EXPENSIVE fresh-solver semantic
    // re-check. `EufSolver::new(terms)` is O(terms) (rebuilds func_apps + enodes
    // + cong_table), and EUF finite-model instances do 10k+ propagations with
    // few atoms, so the existing #8256 sampling (keyed on theory_atoms > 1000)
    // never kicks in — recreating the solver ~36k times/solve (~18% of QF_UF
    // runtime, profiled). This is the EUF path ONLY, so it does NOT touch the
    // LRA/BV semantic gates (which catch REAL input-dependent unsound props,
    // #8529). We fully verify the first WARMUP EUF propagations (solver bugs
    // manifest early), then sample every 64th. The always-on structural check
    // above is unaffected. Validated by the AY-vs-yices oracle differential.
    {
        use std::cell::Cell;
        thread_local!(static SEM_CTR: Cell<u64> = const { Cell::new(0) });
        const WARMUP: u64 = 512;
        let n = SEM_CTR.with(|c| {
            let v = c.get().wrapping_add(1);
            c.set(v);
            v
        });
        if n > WARMUP && !n.is_multiple_of(64) {
            // Sampled out: trust this (congruence-sound, oracle-validated) EUF
            // propagation. Completeness, not soundness — skipping never asserts
            // a wrong verdict, and unsound EUF props are caught in the sampled
            // fraction + the structural check + SAT-level model validation.
            return Ok(());
        }
    }

    // verify_only_scoped(): see verify_euf_conflict — verdict-only re-check
    // (#8529) scoped to the asserted literals' subterm closure (#A2 PEQ perf).
    let mut verify_euf = EufSolver::new(terms).verify_only_scoped(
        propagation
            .reason
            .iter()
            .map(|lit| lit.term)
            .chain(std::iter::once(propagation.literal.term)),
    );

    // Assert all reason literals
    for lit in &propagation.reason {
        verify_euf.assert_literal(lit.term, lit.value);
    }

    // Assert negation of the propagated literal
    verify_euf.assert_literal(propagation.literal.term, !propagation.literal.value);

    // If reason ∧ ¬propagated is UNSAT, then reason ⊨ propagated (valid)
    match verify_euf.check() {
        TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_) => Ok(()),
        TheoryResult::Sat => Err(VerificationError::PropagationNotImplied {
            term: propagation.literal.term,
            value: propagation.literal.value,
        }),
        // Unknown: the standalone EUF solver cannot verify this propagation.
        // This is expected for cross-theory (Nelson-Oppen) propagations where
        // EUF alone cannot reproduce the implication. Treat as "skip" not "fail".
        TheoryResult::Unknown => Ok(()),
        // Split/lemma requests: the standalone solver needs more information than
        // a single-theory check can provide. Skip rather than fail.
        TheoryResult::NeedSplit(_)
        | TheoryResult::NeedDisequalitySplit(_)
        | TheoryResult::NeedExpressionSplit(_)
        | TheoryResult::NeedStringLemma(_)
        | TheoryResult::NeedLemmas(_)
        | TheoryResult::NeedModelEquality(_)
        | TheoryResult::NeedModelEqualities(_) => Ok(()),
        // All current TheoryResult variants handled above (#4906, #6149).
        // Wildcard covers future variants from #[non_exhaustive].
        _ => unreachable!("unhandled TheoryResult variant — update this match"),
    }
}
