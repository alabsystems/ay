// Copyright 2026 Andrew Yates
// Native PR/SR (propagation-/substitution-redundancy) proof checker.
//
// Ported from the redundancy-check loop of the reference checker `dsr-trim`
// (Codel / Avigad / Heule, https://github.com/ccodel/dsr-trim), specifically:
//   * `global_data.c::assume_subst`            -> `Subst::from_witness`
//   * `global_data.c::map_lit_under_subst`     -> `Subst::map_lit`
//   * `global_data.c::reduce_clause_under_subst` -> `reduce_clause_under_subst`
//   * `global_data.c::assume_negated_clause_under_subst`
//     and `dsr-trim.c::check_reduced_clause`   -> `check_reduced_clause`
//   * `dsr-trim.c::check_dsr_line`             -> `sr_redundant_step` (the kernel)
//
// The first three, the substitution itself, are in `sr_subst.rs`; the kernel
// and the per-step driver are here.
//
// It reuses the watched-literal BCP engine of `DratChecker` (assign / propagate
// / backtrack / value / clause DB), exactly as the backward checker does. The
// only new state is the substitution map `Subst`.
//
// THE TRUSTED KERNEL is the single function `DratChecker::sr_redundant_step`:
// it decides redundancy of ONE clause addition under ONE witness via reverse
// unit propagation. It is small and self-contained on purpose -- a later Trust
// task will verify IT. Everything else (parsing, the per-step driver) is
// untrusted glue: if the glue is wrong the kernel still fails closed, because
// the kernel re-derives every refutation by propagation and never trusts the
// witness blindly.
//
// Literal encoding note: `ay_proof_common::Literal` uses pos=2v, neg=2v+1,
// `negated()`=^1, `variable()`=>>1 -- byte-identical to dsr-trim's
// `FROM_DIMACS_LIT`/`NEGATE_LIT`/`VAR_FROM_LIT`, so witness codes map 1:1.

use super::DratChecker;
use crate::error::DratCheckError;
use crate::literal::Literal;

#[path = "sr_subst.rs"]
mod subst;
use subst::{reduce_clause_under_subst, LitImage, Reduce, Subst};

impl DratChecker {
    /// THE TRUSTED KERNEL.
    ///
    /// Decide whether adding `clause` with substitution witness `subst` is
    /// redundant with respect to the current formula `F` held by the engine.
    /// Returns `Ok(())` iff the clause is redundant. Does **not** mutate the
    /// clause DB; on every exit the trail is restored to `saved`.
    ///
    /// Decision procedure (Heule-Kiesl-Biere PR / Codel-Avigad-Heule SR):
    ///
    /// Let `alpha = !clause` (the assignment falsifying `clause`).
    ///   1. If `F /\ alpha |-1 false` then `clause` is RUP -- redundant, done.
    ///   2. Otherwise the witness must touch `clause` (`reduce(clause) !=
    ///      NOT_REDUCED`, and not all-false): if sigma neither satisfies nor
    ///      reduces `clause`, redundancy is unproven -> reject.
    ///   3. With `alpha` and its unit-propagation closure fixed as the base,
    ///      for every clause `D` in `F` that sigma reduces (`REDUCED`), check
    ///      `F /\ alpha /\ !(D|sigma) |-1 false`. Satisfied/untouched `D` are
    ///      skipped; an all-false `D|sigma` (`CONTRADICTION`) is a reject.
    ///   4. Finally subject `clause` itself to the same reduced-clause check
    ///      (a no-op when sigma satisfies `clause`, the usual AY case; required
    ///      for the general witnesses dsr-trim also accepts).
    ///
    /// Soundness does not depend on the witness being well-formed: every step
    /// re-derives its refutation by propagation, so a corrupt witness can only
    /// make a check FAIL, never spuriously succeed.
    fn sr_redundant_step(
        &mut self,
        clause: &[Literal],
        subst: &Subst,
    ) -> Result<(), DratCheckError> {
        self.stats.checks = self.stats.checks.saturating_add(1);
        let saved = self.trail.len();

        // (1) RUP shortcut: assume !clause and propagate.
        for &lit in clause {
            match self.value(lit) {
                Some(true) => {
                    // `clause` is already satisfied by the (global) trail, so it
                    // is implied. Restore and accept.
                    self.backtrack(saved);
                    return Ok(());
                }
                Some(false) => {} // !lit already on the trail
                None => self.assign(lit.negated()),
            }
        }
        let rup_conflict = !self.propagate();
        if rup_conflict {
            self.backtrack(saved);
            return Ok(());
        }

        // (2) The witness must touch `clause`; a clause that needs no witness
        // would have been RUP above (dsr-trim.c:3544).
        let Some(candidate_reduct) = reduce_clause_under_subst(subst, clause) else {
            self.backtrack(saved);
            return Err(self.sr_fail(
                clause,
                "reduct tally of a clause under the witness is unrepresentable",
            ));
        };
        match candidate_reduct {
            Reduce::NotReduced => {
                self.backtrack(saved);
                return Err(self.sr_fail(clause, "candidate clause not reduced by the witness"));
            }
            Reduce::Contradiction => {
                self.backtrack(saved);
                return Err(self.sr_fail(clause, "witness falsifies the entire candidate clause"));
            }
            _ => {}
        }

        // Base assignment = !clause + its UP closure, shared by every D-check.
        let base = self.trail.len();

        // (3) Every clause D in F reduced by sigma must satisfy
        //     F /\ alpha /\ !(D|sigma) |-1 false.
        let num_clauses = self.clauses.len();
        for cidx in 0..num_clauses {
            let reduce = match &self.clauses[cidx] {
                Some(d) => reduce_clause_under_subst(subst, d),
                None => continue, // deleted
            };
            let Some(reduce) = reduce else {
                self.backtrack(saved);
                return Err(self.sr_fail(
                    clause,
                    "reduct tally of a clause under the witness is unrepresentable",
                ));
            };
            match reduce {
                Reduce::Satisfied | Reduce::NotReduced => continue,
                Reduce::Contradiction => {
                    self.backtrack(saved);
                    return Err(self.sr_fail(clause, "a formula clause maps to the empty clause"));
                }
                Reduce::Reduced => {
                    // Clone only the clauses we actually have to refute.
                    let d = match &self.clauses[cidx] {
                        Some(d) => d.clone(),
                        None => continue,
                    };
                    if !self.check_reduced_clause(&d, subst, base) {
                        self.backtrack(saved);
                        return Err(self.sr_fail(clause, "reduced formula clause is not implied"));
                    }
                }
            }
        }

        // (4) The candidate clause itself (general-witness case). When sigma
        // satisfies `clause` this is `Satisfied` and trivially passes.
        // `candidate_reduct` is this same pure reduction, computed in (2).
        if candidate_reduct == Reduce::Reduced && !self.check_reduced_clause(clause, subst, base) {
            self.backtrack(saved);
            return Err(self.sr_fail(clause, "reduced candidate clause is not implied"));
        }

        self.backtrack(saved);
        Ok(())
    }

    /// Check one reduced clause `D`: assume `!(D|sigma)` on top of `base` and
    /// propagate; success iff a conflict is derived. Restores the trail to
    /// `base` before returning.
    ///
    /// Mirrors `assume_negated_clause_under_subst` + the `perform_up` in
    /// `check_reduced_clause`: literals whose image is false under alpha are
    /// already-true negations (skip); an image true under alpha means `D|sigma`
    /// is already satisfied by alpha (trivial conflict, accept); otherwise
    /// assume the negated image.
    fn check_reduced_clause(&mut self, d: &[Literal], subst: &Subst, base: usize) -> bool {
        let mut trivial = false;
        for &lit in d {
            match subst.map_lit(lit) {
                LitImage::False => {} // not present in D|sigma
                LitImage::True => {
                    // D|sigma is satisfied by sigma -- should be unreachable for
                    // a REDUCED clause, but accept defensively.
                    trivial = true;
                    break;
                }
                LitImage::Lit(m) => match self.value(m) {
                    Some(true) => {
                        // m already true under alpha: alpha |= D|sigma.
                        trivial = true;
                        break;
                    }
                    Some(false) => {} // !m already on the trail
                    None => self.assign(m.negated()),
                },
            }
        }
        let ok = trivial || !self.propagate();
        self.backtrack(base);
        ok
    }

    fn sr_fail(&mut self, clause: &[Literal], why: &str) -> DratCheckError {
        self.stats.failures = self.stats.failures.saturating_add(1);
        let lits: Vec<_> = clause.iter().map(ToString::to_string).collect();
        DratCheckError::NotImplied {
            clause: format!("{lits:?} ({why})"),
            step: self.stats.additions,
            kind: "PR/SR ",
        }
    }
}

/// Native PR/SR proof checker built on the `DratChecker` BCP engine.
///
/// Handles the four proof-step kinds AY emits:
///   * `Add`    -> RUP/RAT (delegated to the DRAT engine)
///   * `Delete` -> clause deletion
///   * `AddPr`  -> PR (partial-assignment witness) **or** SR (substitution
///     witness) -- both decided by `DratChecker::sr_redundant_step`.
///
/// PR is the special case of SR whose witness maps only to true/false, so the
/// single kernel covers DPR/LPR (the `j=0` symmetry binaries) and full DSR.
pub struct SrChecker {
    inner: DratChecker,
}

impl SrChecker {
    /// Create a checker. `check_rat` lets plain `Add` steps fall back to RAT
    /// (full DRAT) as well as RUP.
    pub fn new(num_vars: usize, check_rat: bool) -> Self {
        Self {
            inner: DratChecker::new(num_vars, check_rat),
        }
    }

    pub fn stats(&self) -> &super::Stats {
        self.inner.stats()
    }

    /// Add one PR/SR step and, on success, commit the clause to the DB.
    fn add_sr(&mut self, clause: &[Literal], witness: &[Literal]) -> Result<(), DratCheckError> {
        self.inner.stats.additions = self.inner.stats.additions.saturating_add(1);

        // If the formula is already inconsistent, any non-empty clause is
        // vacuously redundant (matches `DratChecker::add_derived`).
        if self.inner.inconsistent && !clause.is_empty() {
            return Ok(());
        }

        for &lit in clause.iter().chain(witness.iter()) {
            let variable = lit.variable().index();
            if let Err(refusal) = self.inner.ensure_capacity(variable) {
                self.inner.stats.failures = self.inner.stats.failures.saturating_add(1);
                return Err(refusal.step_error(variable, self.inner.stats.additions));
            }
        }

        // A tautological clause is trivially redundant; the DB insert skips it.
        if self.inner.is_tautology(clause) {
            return Ok(());
        }

        let subst = Subst::from_witness(witness, self.inner.num_vars())?;
        debug_assert_eq!(Some(&subst.pivot), witness.first());
        self.inner.sr_redundant_step(clause, &subst)?;

        // Redundant: commit it so later steps see it (also sets `inconsistent`
        // if it reduced to the empty clause).
        self.inner.add_clause_internal(clause);
        Ok(())
    }

    /// Verify a complete PR/SR (or mixed DRAT) proof on a fresh checker.
    ///
    /// This bulk API is one-shot. A repeated call fails with
    /// [`DratCheckError::CheckerNotFresh`] rather than reusing proof state from
    /// an earlier formula.
    pub fn verify(
        &mut self,
        clauses: &[Vec<Literal>],
        steps: &[crate::drat_parser::ProofStep],
    ) -> Result<(), DratCheckError> {
        use crate::drat_parser::ProofStep;

        self.inner.begin_bulk_verify()?;
        for clause in clauses {
            self.inner.add_original(clause);
        }
        if self.inner.inconsistent {
            return match self.inner.conclude_unsat() {
                super::ConcludeResult::Verified => Ok(()),
                super::ConcludeResult::Failed(reason) => Err(DratCheckError::from(reason)),
            };
        }

        for (i, step) in steps.iter().enumerate() {
            let res = match step {
                ProofStep::Add(lits) => self.inner.add_derived(lits),
                ProofStep::Delete(lits) => {
                    self.inner.delete_clause(lits);
                    Ok(())
                }
                ProofStep::AddPr { clause, witness } => self.add_sr(clause, witness),
            };
            res.map_err(|e| DratCheckError::StepFailed {
                step: i.saturating_add(1),
                source: Box::new(e),
            })?;
        }

        match self.inner.conclude_unsat() {
            super::ConcludeResult::Verified => Ok(()),
            super::ConcludeResult::Failed(reason) => Err(DratCheckError::from(reason)),
        }
    }
}

impl DratChecker {
    /// Expose the (possibly grown) variable count for sizing the subst map.
    #[inline]
    pub(super) fn num_vars(&self) -> usize {
        self.num_vars
    }
}

#[cfg(test)]
#[path = "sr_tests.rs"]
mod sr_tests;
