// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The one explanation for an UNSAT the NIA cannot narrow: the asserted set
//! PLUS every cross-theory fact the inner LIA holds (#nonlinear-shared-reasons).
//!
//! The inner LIA's state is the atoms this solver asserted into it, the EUF
//! shared equalities and disequalities the combiner forwarded
//! (`assert_shared_equality` / `assert_shared_disequality`, held as tableau
//! rows and disequality constraints), definitional axioms, and this solver's
//! own lemmas — whose premises are asserted atoms or bounds with their own
//! reasons — and tentative guesses, which cannot support a refutation
//! (`ay-lia/src/justified_bounds.rs`). A procedure that refutes that state
//! AS A WHOLE (the check loop's exact-lemma refutation, the tangent recheck,
//! the factor splits' branches, the bounded enumeration's box, …) has used
//! whatever it held, so the only explanation it can give without tracking
//! is all of it. The asserted atoms alone are NOT a theorem when a shared
//! equality carried the refutation: QF_UFNIA `euf_div_010` (x*y = 28,
//! x = f(a), w = f(b), w >= 29, `a = b` in force) got the 17 asserted atoms
//! back as the conflict — a set z3 satisfies — the learned clause was empty
//! and the problem was answered `unsat`.
//!
//! Every full-set site in this crate goes through [`NiaSolver::full_conflict_lits`];
//! none maps `self.asserted` to a conflict by hand. The one other use of the
//! asserted literals as an explanation, [`NiaSolver::asserted_lits_at`], names
//! the asserted literals a derivation that reads the asserted atoms and
//! nothing else was derived from (the factor split's branch provenance).

use super::*;

impl NiaSolver<'_> {
    /// The asserted literals, in assertion order, followed by the reason
    /// literals of every cross-theory fact the inner LIA holds that are not
    /// already among them. With no cross-theory facts this is exactly the
    /// asserted set, so pure QF_NIA conflicts are unchanged.
    pub(crate) fn full_conflict_lits(&self) -> Vec<TheoryLit> {
        let mut conflict = self.asserted_atom_lits();
        let shared = self.lia.shared_constraint_reasons();
        if !shared.is_empty() {
            let mut seen: HashSet<TheoryLit> = conflict.iter().copied().collect();
            conflict.extend(shared.into_iter().filter(|lit| seen.insert(*lit)));
        }
        conflict
    }

    /// The asserted literals alone, in assertion order.
    fn asserted_atom_lits(&self) -> Vec<TheoryLit> {
        self.asserted
            .iter()
            .map(|&(term, value)| TheoryLit::new(term, value))
            .collect()
    }

    /// The asserted literals at `positions` (indices into `self.asserted`):
    /// the premises of a derivation that reads the ASSERTED ATOMS and nothing
    /// the inner LIA holds — the factor split's linearized-atom contraction
    /// (`derive_branch_facts` substitutes branch pins into the asserted
    /// atoms' skeletons) and the cuts built from what it derives, each named
    /// by the atoms it came from (#nia-factor-split-provenance). Never the
    /// explanation of a refutation of the inner solver's state; that is
    /// [`Self::full_conflict_lits`]. `None` (fail closed: the caller has no
    /// explanation and falls back to the full set) if a position is not an
    /// asserted literal — dropping it would make the explanation weaker than
    /// the derivation.
    pub(crate) fn asserted_lits_at(&self, positions: &[usize]) -> Option<Vec<TheoryLit>> {
        positions
            .iter()
            .map(|&i| {
                let &(term, value) = self.asserted.get(i)?;
                Some(TheoryLit::new(term, value))
            })
            .collect()
    }

    /// Is `lit` a premise this solver may name in a conflict: an asserted
    /// literal, or the reason of a cross-theory fact the inner LIA holds
    /// (an EUF shared equality or disequality — the LRA installs those as
    /// bounds carrying exactly these reasons, so an LRA conflict that used
    /// the fact cites them).
    pub(crate) fn is_live_premise(&self, lit: &TheoryLit, shared: &HashSet<TheoryLit>) -> bool {
        self.asserted.contains(&(lit.term, lit.value)) || shared.contains(lit)
    }
}
