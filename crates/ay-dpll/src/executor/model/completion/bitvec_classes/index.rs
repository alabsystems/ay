// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{
    BitVecAtomIndex, CandidateOwner, Executor, HashMap, HashSet, Sort, TermData, TermId,
    UnknownOrigin,
};

impl Executor {
    /// Index the theory atoms of `roots` (every Bool-sorted term that is not
    /// a Boolean connective) against the BitVec variables they mention, and
    /// record the polarity each top-level conjunction forces on its atoms.
    pub(super) fn bitvec_atom_index(
        &self,
        roots: &[TermId],
        owner: &mut CandidateOwner,
    ) -> Result<BitVecAtomIndex, UnknownOrigin> {
        let mut index = BitVecAtomIndex {
            forced: self.forced_atom_polarities(roots, owner)?,
            ..BitVecAtomIndex::default()
        };
        let mut seen: HashSet<TermId> = HashSet::default();
        owner.entries(roots.len())?;
        let mut stack: Vec<TermId> = roots.to_vec();
        while let Some(term) = stack.pop() {
            owner.entries(1)?;
            if !seen.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::Forall(..) | TermData::Exists(..) | TermData::Let(..) => {
                    self.mark_unverifiable_bitvec_vars(term, &mut index.unverifiable, owner)?;
                }
                _ if self.is_boolean_connective(term) => {
                    stack.extend(owner.children(&self.ctx.terms, term)?);
                }
                _ => self.index_atom(term, &mut index, owner)?,
            }
        }
        Ok(index)
    }

    /// The truth value the top-level conjunctions of `roots` force on each
    /// atom they reach through `and`, `not` and a false `or`.
    fn forced_atom_polarities(
        &self,
        roots: &[TermId],
        owner: &mut CandidateOwner,
    ) -> Result<HashMap<TermId, bool>, UnknownOrigin> {
        let mut forced: HashMap<TermId, bool> = HashMap::default();
        let mut seen: HashSet<(TermId, bool)> = HashSet::default();
        owner.entries(roots.len())?;
        let mut stack: Vec<(TermId, bool)> = roots.iter().map(|&root| (root, true)).collect();
        while let Some((term, polarity)) = stack.pop() {
            owner.entries(2)?;
            if !seen.insert((term, polarity)) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::Not(inner) => {
                    owner.entries(1)?;
                    stack.push((*inner, !polarity));
                }
                TermData::App(symbol, args)
                    if (symbol.name() == "and" && polarity)
                        || (symbol.name() == "or" && !polarity) =>
                {
                    owner.entries(args.len())?;
                    stack.extend(args.iter().map(|&arg| (arg, polarity)));
                }
                _ if self.is_boolean_connective(term) => {}
                _ => {
                    forced.entry(term).or_insert(polarity);
                }
            }
        }
        Ok(forced)
    }

    /// Whether `term` is a Boolean connective of the skeleton: `not`, `and`,
    /// `or`, `=>`, `xor`, a Bool `ite`, or an `=`/`distinct` over Bool
    /// operands.
    fn is_boolean_connective(&self, term: TermId) -> bool {
        if !matches!(self.ctx.terms.sort(term), Sort::Bool) {
            return false;
        }
        match self.ctx.terms.get(term) {
            TermData::Not(_) | TermData::Ite(..) => true,
            TermData::App(symbol, args) => match symbol.name() {
                "and" | "or" | "=>" | "xor" => true,
                "=" | "distinct" => args
                    .first()
                    .is_some_and(|&first| matches!(self.ctx.terms.sort(first), Sort::Bool)),
                _ => false,
            },
            _ => false,
        }
    }

    /// Record the Bool, Int, Real and BitVec variables `atom` mentions,
    /// outside any binder; a BitVec variable under a binder is unverifiable.
    fn index_atom(
        &self,
        atom: TermId,
        index: &mut BitVecAtomIndex,
        owner: &mut CandidateOwner,
    ) -> Result<(), UnknownOrigin> {
        if index.vars_of.contains_key(&atom) {
            return Ok(());
        }
        let mut leaves: Vec<TermId> = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::default();
        owner.entries(1)?;
        let mut stack = vec![atom];
        while let Some(term) = stack.pop() {
            owner.entries(2)?;
            if !seen.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::Var(..) => {
                    if matches!(
                        self.ctx.terms.sort(term),
                        Sort::Bool | Sort::Int | Sort::Real | Sort::BitVec(_)
                    ) {
                        leaves.push(term);
                    }
                }
                TermData::Forall(..) | TermData::Exists(..) | TermData::Let(..) => {
                    self.mark_unverifiable_bitvec_vars(term, &mut index.unverifiable, owner)?;
                }
                _ => stack.extend(owner.children(&self.ctx.terms, term)?),
            }
        }
        owner.sort(leaves.len())?;
        leaves.sort_by_key(|leaf| leaf.index());
        owner.entries(leaves.len())?;
        let vars: Vec<TermId> = leaves
            .iter()
            .copied()
            .filter(|&leaf| matches!(self.ctx.terms.sort(leaf), Sort::BitVec(_)))
            .collect();
        for &var in &vars {
            owner.entries(2)?;
            index.atoms_of.entry(var).or_default().push(atom);
        }
        owner.entries(2)?;
        index.vars_of.insert(atom, vars);
        index.leaves_of.insert(atom, leaves);
        Ok(())
    }

    /// Every BitVec variable occurring anywhere under `term`.
    fn mark_unverifiable_bitvec_vars(
        &self,
        term: TermId,
        unverifiable: &mut HashSet<TermId>,
        owner: &mut CandidateOwner,
    ) -> Result<(), UnknownOrigin> {
        let mut seen: HashSet<TermId> = HashSet::default();
        owner.entries(1)?;
        let mut stack = vec![term];
        while let Some(term) = stack.pop() {
            owner.entries(2)?;
            if !seen.insert(term) {
                continue;
            }
            if matches!(self.ctx.terms.get(term), TermData::Var(..))
                && matches!(self.ctx.terms.sort(term), Sort::BitVec(_))
            {
                unverifiable.insert(term);
            }
            stack.extend(owner.children(&self.ctx.terms, term)?);
        }
        Ok(())
    }
}
