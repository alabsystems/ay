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

use super::sr_reduct_core::classify_reduct;
use super::DratChecker;
use crate::error::DratCheckError;
use crate::literal::Literal;

/// The image of a *variable's positive literal* under the substitution sigma.
///
/// dsr-trim stores `subst_mappings[var] = mapping ^ IS_NEG(lit)`, i.e. the
/// image of the positive literal; the sign is re-applied on lookup. We mirror
/// that: `True`/`False` are the boolean constants `SUBST_TT`/`SUBST_FF`, and
/// `Lit(m)` is a literal image.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum SubImage {
    True,
    False,
    Lit(Literal),
}

impl SubImage {
    /// Negate an image (applying the sign of a negative literal on lookup).
    #[inline]
    fn negate(self) -> Self {
        match self {
            SubImage::True => SubImage::False,
            SubImage::False => SubImage::True,
            SubImage::Lit(m) => SubImage::Lit(m.negated()),
        }
    }
}

/// Result of evaluating one literal under sigma. (`map_lit_under_subst`.)
enum LitImage {
    True,
    False,
    Lit(Literal),
}

/// Outcome of reducing a clause under sigma. Mirrors dsr-trim's return codes
/// `SATISFIED_OR_MUL` / `NOT_REDUCED` / `REDUCED` / `CONTRADICTION`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Reduce {
    /// Some literal maps to true: the reduced clause is satisfied -> skip.
    Satisfied,
    /// sigma does not touch the clause (every literal maps to itself).
    NotReduced,
    /// sigma touches the clause and it is neither satisfied nor empty.
    Reduced,
    /// Every literal maps to false: the reduced clause is empty.
    Contradiction,
}

/// The substitution sigma, indexed by variable.
///
/// `map[var] == None` means sigma is the identity on `var`.
struct Subst {
    map: Vec<Option<SubImage>>,
    /// The clause pivot (= `witness[0]`), retained for diagnostics.
    pivot: Literal,
}

impl Subst {
    /// Build sigma from an `AddPr`/`AddSr` witness token stream.
    ///
    /// Layout (see `dsr-trim::parse_sr_clause_and_witness` and AY's
    /// `DratWriter::add_sr`): `pivot [pr-atoms...] [pivot(sep) (l m)...]`.
    /// `witness[0]` is the pivot, which maps to true. Atoms before the second
    /// pivot occurrence each map to true (PR / DPR part). After the separating
    /// second pivot, tokens are read in (l, m) pairs giving `sigma(l) = m`
    /// (the substitution part that makes this SR rather than PR).
    ///
    /// Faithful to `assume_subst`: the pivot variable may be re-set in the
    /// substitution part, but no *other* variable may be assigned twice; a
    /// duplicate (or a malformed dangling pair) makes the witness invalid and
    /// the step is rejected (fail closed).
    fn from_witness(witness: &[Literal], num_vars: usize) -> Result<Self, DratCheckError> {
        let pivot = *witness
            .first()
            .ok_or_else(|| DratCheckError::UnsupportedPr {
                clause: "empty SR/PR witness".to_string(),
            })?;
        let pivot_var = pivot.variable().index();
        let mut map: Vec<Option<SubImage>> = vec![None; num_vars];

        // pivot |-> true.
        Self::set(&mut map, pivot, SubImage::True);

        let mut seen_divider = false;
        let mut i = 1;
        while i < witness.len() {
            let lit = witness[i];
            let var = lit.variable().index();
            if !seen_divider {
                if lit == pivot {
                    // The second occurrence of the pivot is the separator.
                    seen_divider = true;
                    i += 1;
                    continue;
                }
                if map[var].is_some() && var != pivot_var {
                    return Err(Self::invalid("witness assigns a variable twice"));
                }
                Self::set(&mut map, lit, SubImage::True);
                i += 1;
            } else {
                // Substitution part: (l, m) pairs.
                let mapped = *witness.get(i + 1).ok_or_else(|| {
                    Self::invalid("witness has a dangling substitution half-pair")
                })?;
                if map[var].is_some() && var != pivot_var {
                    return Err(Self::invalid("witness assigns a variable twice"));
                }
                Self::set(&mut map, lit, SubImage::Lit(mapped));
                i += 2;
            }
        }

        Ok(Subst { map, pivot })
    }

    fn invalid(detail: &str) -> DratCheckError {
        DratCheckError::UnsupportedPr {
            clause: format!("invalid SR/PR witness: {detail}"),
        }
    }

    /// Store `sigma(lit) = image`, normalising to the positive-literal image
    /// (dsr-trim's `set_mapping_for_subst`).
    #[inline]
    fn set(map: &mut [Option<SubImage>], lit: Literal, image: SubImage) {
        let stored = if lit.is_positive() {
            image
        } else {
            image.negate()
        };
        map[lit.variable().index()] = Some(stored);
    }

    /// Compute `sigma(lit)` (dsr-trim's `map_lit_under_subst`).
    #[inline]
    fn map_lit(&self, lit: Literal) -> LitImage {
        match self.map.get(lit.variable().index()).copied().flatten() {
            None => LitImage::Lit(lit), // identity
            Some(image) => {
                let img = if lit.is_positive() {
                    image
                } else {
                    image.negate()
                };
                match img {
                    SubImage::True => LitImage::True,
                    SubImage::False => LitImage::False,
                    SubImage::Lit(m) => LitImage::Lit(m),
                }
            }
        }
    }
}

/// Reduce `clause` under sigma (dsr-trim's `reduce_clause_under_subst`).
///
/// Pure function of the clause and the substitution -- no engine state -- so it
/// can be called while a clause is borrowed from the DB.
fn reduce_clause_under_subst(subst: &Subst, clause: &[Literal]) -> Reduce {
    let mut falsified = 0usize;
    let mut identity = 0usize;
    let mut any_true = false;
    for &lit in clause {
        match subst.map_lit(lit) {
            LitImage::True => any_true = true,
            LitImage::False => falsified += 1,
            LitImage::Lit(m) => {
                if m == lit {
                    identity += 1;
                }
            }
        }
    }
    // The soundness-critical skip/reject decision is the SHARED, Trust-verified
    // `classify_reduct` (proofs/sr_reduct_soundness_proof.rs makes it
    // load-bearing). 0=Satisfied, 1=NotReduced, 2=Reduced, 3=Contradiction.
    // (Counting all literals before classifying — rather than short-circuiting on
    // the first True — yields the identical class but routes the WHOLE decision
    // through the verified core.)
    match classify_reduct(any_true, falsified, identity, clause.len()) {
        0 => Reduce::Satisfied,
        1 => Reduce::NotReduced,
        3 => Reduce::Contradiction,
        _ => Reduce::Reduced,
    }
}

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
        self.stats.checks += 1;
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
        match reduce_clause_under_subst(subst, clause) {
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
        if reduce_clause_under_subst(subst, clause) == Reduce::Reduced
            && !self.check_reduced_clause(clause, subst, base)
        {
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
        self.stats.failures += 1;
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
        self.inner.stats.additions += 1;

        // If the formula is already inconsistent, any non-empty clause is
        // vacuously redundant (matches `DratChecker::add_derived`).
        if self.inner.inconsistent && !clause.is_empty() {
            return Ok(());
        }

        for &lit in clause.iter().chain(witness.iter()) {
            self.inner.ensure_capacity(lit.variable().index());
        }

        // A tautological clause is trivially redundant; the DB insert skips it.
        if self.inner.is_tautology(clause) {
            return Ok(());
        }

        let subst = Subst::from_witness(witness, self.inner.num_vars())?;
        debug_assert_eq!(subst.pivot, witness[0]);
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
                step: i + 1,
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
