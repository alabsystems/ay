// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BitVec values on the routes that decide BitVec terms as uninterpreted
//! (#uninterpreted-bitvec-class-values).
//!
//! The AUFLIA, Array+EUF and EUF lanes carry no BV model: a BitVec term is an
//! uninterpreted constant to them, and EUF decides the equalities between such
//! terms. Their witnesses therefore valued no BitVec variable, and phase 1
//! gave every one the canonical default 0, even a variable the SAT model had
//! put apart from `#x0` by a committed disequality:
//!
//! ```text
//! (and (= l 1) (not (= b #x0000000000000000)))
//! ```
//!
//! The lane's own validation then refused the witness (`b = 0` falsifies the
//! disequality) and the lane answered `unknown`. In the `_BV_LIA_INDEP`
//! category that `unknown` is the AUFLIA cross-check's, and the agreement step
//! (`theories/combined/bv_lia_indep_agreement.rs`) then has no AUFLIA witness
//! to merge: the shape of the TPA reachability checks on model-checker-consumer's per-row
//! CHC route over `const_pointer_read_type_dual.rs` that stayed `unknown` at
//! 29a0f2cab (the development design notes, 2026-10-13), and of a store-chain read at a
//! BitVec variable index (`executor_tests::smt::bv_lia_indep_final_assignment`).
//!
//! EUF's model already names one value per equality class of BitVec terms:
//! a class holding a literal takes that literal, every other class a value no
//! literal and no other class of its width uses, chosen apart from every
//! committed-disequal class (`ay_euf` `model_extraction.rs`). This phase
//! offers each BitVec variable that value. EUF modelled no BitVec semantics
//! beyond equality, though: a `bvult` atom was an uninterpreted predicate to
//! it and `bvadd` an uninterpreted function, so a class value can contradict
//! an atom the solve committed to (the 2026-09-17 revert of
//! #bv-euf-class-literal-read measured exactly that, when the class spelling
//! was read for every evaluation). So the offer is VERIFIED where it is
//! taken, per variable: every atom of the roots that mentions an offered
//! variable must evaluate, under the completed model, to the truth value the
//! solve committed to it (the SAT model's, or the polarity a top-level
//! conjunction forces), with every other variable it mentions already valued
//! for good. An atom that disagrees, that cannot be decided, or that still
//! reads an unvalued variable (one a later phase decides: an equality over it
//! can evaluate through the EUF classes meanwhile) withdraws the offer for
//! every variable in it, to a fixpoint; the withdrawn variables reach phase 1
//! and its default exactly as before. Last, the independent gate's evaluator
//! reads the roots with the surviving offers in place (it evaluates a UF
//! application through its function table, at the argument values the
//! offers set): if it falsifies one, every offer is withdrawn.
//!
//! SOUNDNESS. Fill-only, like every completion phase: a variable that already
//! evaluates is never touched, a substitution key is left to the substitution
//! fixpoint, and the values are candidates only. The full model validation
//! and the independent gate re-check every assertion afterwards, so an offer
//! that slipped past the atom check degrades `sat` to `unknown` as the default
//! 0 did, never to a wrong `sat`. A route with a BV model is untouched: its
//! bits are the BitVec semantics, and the EUF spelling means nothing there.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{Sort, TermId};

use super::{EvalValue, Model};
use crate::executor::Executor;
use crate::executor_types::UnknownOrigin;

mod control;
mod index;
pub(in crate::executor) use control::CandidateOwner;

#[cfg(test)]
mod tests;

/// The theory atoms of a root window, indexed both ways against the BitVec
/// variables they mention.
#[derive(Default)]
struct BitVecAtomIndex {
    /// Each BitVec variable to the atoms that mention it.
    atoms_of: HashMap<TermId, Vec<TermId>>,
    /// Each atom to the BitVec variables it mentions.
    vars_of: HashMap<TermId, Vec<TermId>>,
    /// Each atom to every variable it mentions of a sort model completion
    /// values (Bool, Int, Real, BitVec).
    leaves_of: HashMap<TermId, Vec<TermId>>,
    /// BitVec variables met where no atom check covers them (a quantifier or
    /// `let` body): never offered.
    unverifiable: HashSet<TermId>,
    /// The truth value a top-level conjunction forces on an atom.
    forced: HashMap<TermId, bool>,
}

impl Executor {
    /// Phase 0.5 of model completion: offer each unvalued BitVec variable of
    /// a BV-model-free witness its EUF class value, keeping only the offers
    /// every atom that mentions them confirms (see module docs). Returns the
    /// number of variables valued.
    pub(super) fn complete_uninterpreted_bitvec_values(
        &self,
        model: &mut Model,
        extra_roots: &[TermId],
        substituted: &HashSet<TermId>,
    ) -> Result<usize, UnknownOrigin> {
        let mut owner = CandidateOwner::capture(self)?;
        let _nested_owner = owner.enter_nested();
        if model.bv_model.is_some() || !self.euf_spells_a_bitvec_variable(model, &mut owner)? {
            return Ok(0);
        }
        owner.entries(self.ctx.assertions.len())?;
        owner.entries(extra_roots.len())?;
        let mut roots = self.ctx.assertions.clone();
        roots.extend_from_slice(extra_roots);
        let index = self.bitvec_atom_index(&roots, &mut owner)?;
        let offers = self.euf_class_bitvec_offers(model, &index, substituted, &mut owner)?;
        if offers.is_empty() {
            owner.finish(self.ctx.terms.true_memory_bytes())?;
            return Ok(0);
        }
        let mut offered: HashSet<TermId> = HashSet::default();
        let outcome = (|| {
            for (var, value) in &offers {
                owner.entries(2)?;
                if Self::insert_completed_value(&self.ctx.terms, model, *var, value) {
                    offered.insert(*var);
                }
            }
            loop {
                let withdrawn = self.offers_an_atom_refuses(model, &index, &offered, &mut owner)?;
                if withdrawn.is_empty() {
                    break;
                }
                owner.pay(withdrawn.len(), 0)?;
                Self::withdraw_offers(model, &mut offered, withdrawn);
            }
            // Executor atom evaluation and independent UF-table evaluation
            // differ. The independent evaluator must retain the last word.
            if !offered.is_empty() {
                owner.poll()?;
                let refuted = self.independent_evaluator_refutes(model, &roots)?;
                super::super::eval_memo_clear();
                owner.poll()?;
                if refuted {
                    Self::withdraw_all_offers(model, &mut offered);
                }
            }
            owner.finish(self.ctx.terms.true_memory_bytes())?;
            Ok(offered.len())
        })();
        if outcome.is_err() {
            // Cleanup is mandatory even after refusal and allocates nothing.
            // No partially admitted candidate may leak into later defaulting.
            Self::withdraw_all_offers(model, &mut offered);
        }
        outcome
    }

    fn withdraw_all_offers(model: &mut Model, offered: &mut HashSet<TermId>) {
        for var in offered.drain() {
            model.completed_values.remove(&var);
        }
        model.revoke_all_quantified_model_seals();
        super::super::eval_memo_clear();
    }

    /// Remove `withdrawn` from the offers and their values from `model`.
    fn withdraw_offers(model: &mut Model, offered: &mut HashSet<TermId>, withdrawn: Vec<TermId>) {
        for var in withdrawn {
            offered.remove(&var);
            model.completed_values.remove(&var);
        }
        model.revoke_all_quantified_model_seals();
        super::super::eval_memo_clear();
    }

    /// Whether `model`'s EUF names a class value for some BitVec variable:
    /// the cheap test that spares every other witness the atom walk.
    fn euf_spells_a_bitvec_variable(
        &self,
        model: &Model,
        owner: &mut CandidateOwner,
    ) -> Result<bool, UnknownOrigin> {
        if let Some(euf) = model.euf_model.as_ref() {
            for &term in euf.term_values.keys() {
                owner.pay(1, 0)?;
                if matches!(self.ctx.terms.get(term), TermData::Var(..))
                    && matches!(self.ctx.terms.sort(term), Sort::BitVec(_))
                {
                    return Ok(true);
                }
            }
        }
        Ok(false)
    }

    /// The EUF class value of every BitVec variable of `index` that is
    /// unvalued, offerable and spelled as a literal of its width, in
    /// deterministic order.
    fn euf_class_bitvec_offers(
        &self,
        model: &Model,
        index: &BitVecAtomIndex,
        substituted: &HashSet<TermId>,
        owner: &mut CandidateOwner,
    ) -> Result<Vec<(TermId, EvalValue)>, UnknownOrigin> {
        let Some(euf) = model.euf_model.as_ref() else {
            return Ok(Vec::new());
        };
        owner.entries(index.atoms_of.len())?;
        let mut vars: Vec<TermId> = index.atoms_of.keys().copied().collect();
        owner.sort(vars.len())?;
        vars.sort_by_key(|var| var.index());
        let mut offers = Vec::new();
        for var in vars {
            owner.pay(1, 0)?;
            if substituted.contains(&var) || index.unverifiable.contains(&var) {
                continue;
            }
            let Sort::BitVec(bv) = self.ctx.terms.sort(var) else {
                continue;
            };
            let width = bv.width;
            let Some(spelled) = euf.term_values.get(&var) else {
                continue;
            };
            if !matches!(self.evaluate_term(model, var), EvalValue::Unknown) {
                continue;
            }
            // Decimal BigInt parsing can be quadratic; precharge its input
            // bound, and bit storage, before the existing opaque parser.
            let work = spelled
                .len()
                .checked_mul(spelled.len())
                .ok_or_else(|| owner.refuse(UnknownOrigin::DeterministicResourceBudget))?;
            let bytes = spelled
                .len()
                .checked_add(width as usize / 8 + 1)
                .and_then(|n| n.checked_mul(4))
                .ok_or_else(|| owner.refuse(UnknownOrigin::MemoryBudget))?;
            owner.pay(work, bytes)?;
            let value = Self::parse_bitvec_string(spelled, width);
            owner.poll()?;
            if matches!(value, EvalValue::BitVec { .. }) {
                owner.entries(1)?;
                offers.push((var, value));
            }
        }
        Ok(offers)
    }

    /// The offered variables of every atom that mentions one and does not
    /// evaluate to its committed truth value under `model`.
    fn offers_an_atom_refuses(
        &self,
        model: &Model,
        index: &BitVecAtomIndex,
        offered: &HashSet<TermId>,
        owner: &mut CandidateOwner,
    ) -> Result<Vec<TermId>, UnknownOrigin> {
        let mut atoms = Vec::new();
        for var in offered {
            owner.pay(1, 0)?;
            if let Some(mentions) = index.atoms_of.get(var) {
                owner.entries(mentions.len())?;
                atoms.extend_from_slice(mentions);
            }
        }
        owner.sort(atoms.len())?;
        atoms.sort_by_key(|atom| atom.index());
        atoms.dedup();
        let mut withdrawn: HashSet<TermId> = HashSet::default();
        for atom in atoms {
            owner.pay(1, 0)?;
            let committed = self
                .term_value(&model.sat_model, &model.term_to_var, atom)
                .or_else(|| index.forced.get(&atom).copied());
            // Every other variable of the atom must already carry the value it
            // will keep: one still unvalued is decided by a later phase (a
            // default, a substitution), and an equality over it can evaluate
            // through the EUF classes meanwhile, which says nothing about that
            // later value. (An array variable is left to the array machinery;
            // no completion phase defaults one.)
            let mut closed = true;
            for leaf in index.leaves_of.get(&atom).into_iter().flatten() {
                owner.pay(1, 0)?;
                if !offered.contains(leaf)
                    && matches!(self.evaluate_term(model, *leaf), EvalValue::Unknown)
                {
                    closed = false;
                    break;
                }
            }
            let confirmed = closed
                && committed
                    .is_some_and(|value| self.evaluate_term(model, atom) == EvalValue::Bool(value));
            owner.poll()?;
            if confirmed {
                continue;
            }
            for var in index.vars_of.get(&atom).into_iter().flatten() {
                owner.entries(1)?;
                if offered.contains(var) {
                    withdrawn.insert(*var);
                }
            }
        }
        owner.entries(withdrawn.len())?;
        let mut withdrawn: Vec<TermId> = withdrawn.into_iter().collect();
        owner.sort(withdrawn.len())?;
        withdrawn.sort_by_key(|var| var.index());
        Ok(withdrawn)
    }
}
