// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Control-flow shim for adding one incremental conflict clause.

/// Thin control-flow shim over [`crate::pipeline_fns::add_incremental_conflict_clause`].
///
/// The clause-building / level-0-minimization / verdict logic lives in the
/// function; this macro only translates its `Break` verdict into the caller's
/// loop and captures the executor's private result fields.
macro_rules! pipeline_add_incremental_conflict_clause {
    (
        $self:ident,
        state: $state:ident,
        solver: $solver:ident,
        term_to_var: $term_to_var:ident,
        conflict_terms: $conflict_terms:expr,
        tag: $tag:expr,
        set_unknown_on_error: $set_unknown:expr,
        unmapped_message: $unmapped_message:literal,
        proof_enabled: $proof_enabled:expr,
        theory_proof: $theory_proof:expr
    ) => {{
        match $crate::pipeline_fns::add_incremental_conflict_clause(
            &mut $self.last_result,
            &mut $self.last_unknown_reason,
            $solver,
            &$term_to_var,
            &$conflict_terms,
            $tag,
            $set_unknown,
            $unmapped_message,
            $proof_enabled,
        ) {
            $crate::pipeline_fns::AddConflictClauseOutcome::Added { original_id } => {
                let __acc_theory_proof = $theory_proof;
                if let (Some(__acc_id), Some(__acc_proof)) = (original_id, __acc_theory_proof) {
                    if !matches!(__acc_proof.kind, ay_core::TheoryLemmaKind::Generic) {
                        $crate::pipeline_fns::place_original_clause_authority_at_id(
                            &$solver,
                            __acc_id,
                            None,
                            Some(__acc_proof),
                            &mut $state.clausification_proofs,
                            &mut $state.original_clause_theory_proofs,
                        );
                    }
                }
                if $proof_enabled {
                    $crate::pipeline_fns::align_original_clause_authority_ledgers(
                        &$solver,
                        &mut $state.clausification_proofs,
                        &mut $state.original_clause_theory_proofs,
                    );
                }
            }
            $crate::pipeline_fns::AddConflictClauseOutcome::Break(__acc_result) => {
                break Ok(__acc_result)
            }
        }
    }};
}
