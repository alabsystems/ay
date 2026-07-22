//! Surface a resolution/LRAT refutation of a production bit-blasted BV CNF.
//!
//! Piece 2/3 of giving a BV UNSAT verdict a zero-trust, independently-checkable
//! certificate (the verified-firewall shape). The production BV solver
//! (`ay-bv::BvSolver`) bit-blasts to a CNF of [`ay_core::CnfClause`] and, on UNSAT,
//! accepts the verdict as "bare-trust": no per-step refutation is surfaced, so it
//! cannot be rendered as a kernel-checkable proof.
//!
//! This closes that by driving a fresh SAT solver over the emitted clauses with an
//! in-memory LRAT writer ([`ay_sat::prove_unsat_resolution_dag`]) and returning the
//! resolution DAG (original clauses with LRAT ids `1..=n` in emission order, plus
//! the RUP-derived steps ending in the empty clause).
//!
//! It lives in `ay-proof` rather than `ay-bv` on purpose: the BV theory library is
//! deliberately decoupled from the SAT engine (`ay-sat` is only a dev-dependency
//! there), and proof surfacing is squarely this crate's responsibility — the same
//! `prove_unsat_resolution_dag` channel that [`crate::bv_blast_solver`] already
//! uses for the slice fragment. Composed with the BV solver's gate provenance
//! (`and_children` / `xor_children` / `mux_children`) and bit↔variable map, this is
//! the refutation a full `BvBlastProof`-style export (piece 3, the Lean renderer)
//! consumes.
//!
//! Fail-closed: a SAT formula yields [`ResolutionDagError::Satisfiable`] (no bogus
//! refutation is fabricated), and a non-pure-RUP CDCL proof yields
//! [`ResolutionDagError::RatStepUnsupported`] rather than an unsound lift.

use ay_core::CnfClause;
use ay_sat::{prove_unsat_resolution_dag, Literal, ResolutionDag, ResolutionDagError};

/// Surface a resolution refutation of the bit-blasted BV CNF `clauses` over
/// `num_vars` Boolean variables.
///
/// `clauses` are the production BV solver's emitted CNF (DIMACS-style `CnfLit`s,
/// 1-indexed signed); `num_vars` is the variable count (`BvSolver::next_var - 1`).
/// The returned [`ResolutionDag`]'s `original_clauses` carry LRAT ids `1..=n`
/// matching `clauses[i]` ↔ id `i+1`.
///
/// This re-runs SAT, so it is a proof-export entry point, **not** part of the hot
/// solve path — call it only when a certificate is wanted.
///
/// # Errors
/// - [`ResolutionDagError::Satisfiable`] if the CNF is SAT (no bogus refutation).
/// - [`ResolutionDagError::Unknown`] on resource limit / interruption.
/// - [`ResolutionDagError::RatStepUnsupported`] if the CDCL proof is not pure RUP
///   (fail-closed; the unsound RAT lift is intentionally not performed).
/// - other variants if the LRAT could not be recovered/parsed.
pub fn surface_bv_cnf_refutation(
    clauses: &[CnfClause],
    num_vars: usize,
) -> Result<ResolutionDag, ResolutionDagError> {
    let sat_clauses: Vec<Vec<Literal>> = clauses
        .iter()
        .map(|c| {
            c.literals()
                .iter()
                .map(|&l| Literal::from_dimacs(l))
                .collect()
        })
        .collect();
    prove_unsat_resolution_dag(num_vars, &sat_clauses)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unsat_cnf_surfaces_empty_clause() {
        // x ∧ ¬x is UNSAT — a real resolution refutation ending in ⊥, replacing
        // bare-trust acceptance of a bit-blasted BV UNSAT.
        let clauses = vec![CnfClause::unit(1), CnfClause::unit(-1)];
        let dag = surface_bv_cnf_refutation(&clauses, 1).expect("UNSAT surfaces a refutation");
        assert_eq!(dag.num_vars, 1);
        assert_eq!(dag.original_clauses.len(), 2);
        let last = dag.derived.last().expect("refutation has derived steps");
        assert!(
            last.clause.is_empty(),
            "the final derived clause must be the empty clause"
        );
        assert_eq!(last.id, dag.empty_clause_id);
    }

    #[test]
    fn unsat_three_var_chain_surfaces_refutation() {
        // (x) ∧ (¬x ∨ y) ∧ (¬y ∨ z) ∧ (¬z) — a propagation chain to ⊥.
        let clauses = vec![
            CnfClause::unit(1),
            CnfClause::binary(-1, 2),
            CnfClause::binary(-2, 3),
            CnfClause::unit(-3),
        ];
        let dag = surface_bv_cnf_refutation(&clauses, 3).expect("UNSAT surfaces a refutation");
        assert!(dag.derived.last().is_some_and(|s| s.clause.is_empty()));
    }

    #[test]
    fn sat_cnf_is_fail_closed() {
        // Just `x` is SAT — no bogus refutation is fabricated.
        let clauses = vec![CnfClause::unit(1)];
        assert_eq!(
            surface_bv_cnf_refutation(&clauses, 1).unwrap_err(),
            ResolutionDagError::Satisfiable
        );
    }
}
