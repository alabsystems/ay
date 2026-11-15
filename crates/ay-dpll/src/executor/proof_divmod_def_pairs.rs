// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Recovering the div/mod purification PAIRS a proof's demoted atoms mention,
//! and the FRESH / INDEPENDENT admission over them. Split out of
//! `proof_divmod_def` so each file stays inside the 500-line ceiling; the lane,
//! its ordering and its soundness argument live there.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{DivModPurification, Symbol, TermData};
use ay_core::{Proof, ProofStep, Sort, TermId};

use super::{demoted_unit_atom, Pair, MAX_DIVMOD_PAIRS};
use crate::executor::Executor;

impl Executor {
    /// Every purification pair whose quotient or remainder a demoted unit
    /// `trust` atom mentions, as `mod_div_elim` recorded it at the mint site
    /// (`TermStore::divmod_purification`), in proof order.
    ///
    /// The pair is found from EITHER symbol, whichever atoms the refutation
    /// used: `(assert (< 2 (mod x (- 3))))` is refuted through the bound
    /// `(< r 3)` and the rewritten leaf `(< 2 r)` alone, which mention neither
    /// the quotient nor the equation `x = -3*q + r`.
    pub(super) fn recover_divmod_pairs(&self, proof: &Proof) -> Vec<DivModPurification> {
        let terms = &self.ctx.terms;
        let mut recovered: Vec<DivModPurification> = Vec::new();
        if !terms.has_divmod_purifications() {
            return recovered;
        }
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut visited: HashSet<TermId> = HashSet::default();
        for step in &proof.steps {
            let Some(atom) = demoted_unit_atom(step) else {
                continue;
            };
            let mut stack = vec![atom];
            while let Some(term) = stack.pop() {
                if !visited.insert(term) {
                    continue;
                }
                if let Some(pair) = terms.divmod_purification(term) {
                    if recovered.len() < MAX_DIVMOD_PAIRS && seen.insert(pair.quotient) {
                        recovered.push(pair);
                    }
                }
                stack.extend(terms.children(term));
            }
        }
        recovered
    }

    /// The `(D, M)` a pair is defined by: `(div x k)` and `(mod x k)` over the
    /// dividend and literal divisor the mint site recorded.
    ///
    /// They are the RAW applications (`mk_app`, never folded): one pair of
    /// opaque atoms the checker reads through the SMT-LIB definition, whatever
    /// the dividend. A literal dividend therefore keeps the `(div 0 2)`
    /// spelling a quantifier instance carries, which the `fresh_def_eq`
    /// bridges align against, and the quotient and remainder are never split
    /// between a folded literal and an atom.
    fn divmod_definientia(&mut self, pair: &DivModPurification) -> (TermId, TermId) {
        let operands = [pair.dividend, pair.divisor];
        let terms = &mut self.ctx.terms;
        let quotient = terms.mk_app(Symbol::named("div"), operands, Sort::Int);
        let remainder = terms.mk_app(Symbol::named("mod"), operands, Sort::Int);
        (quotient, remainder)
    }

    /// Stage A (FRESH) and stage B (INDEPENDENT), mirroring `FreshDefRegistry`.
    pub(super) fn eligible_divmod_pairs(
        &mut self,
        proof: &Proof,
        problem_assertions: &[TermId],
        recovered: Vec<DivModPurification>,
    ) -> Vec<Pair> {
        let mut constrained: HashSet<String> = HashSet::default();
        let mut visited: HashSet<TermId> = HashSet::default();
        for &assertion in problem_assertions {
            self.collect_proof_symbol_names(assertion, &mut constrained, &mut visited);
        }
        for step in &proof.steps {
            if let ProofStep::Assume(term) = step {
                self.collect_proof_symbol_names(*term, &mut constrained, &mut visited);
            }
        }
        let mut candidates = Vec::new();
        for pair in recovered {
            let fresh = [pair.quotient, pair.remainder].iter().all(|&symbol| {
                matches!(self.ctx.terms.get(symbol), TermData::Var(name, _) if !constrained.contains(name))
            });
            if !fresh {
                continue;
            }
            let (quotient_definiens, remainder_definiens) = self.divmod_definientia(&pair);
            candidates.push(Pair {
                quotient: pair.quotient,
                quotient_definiens,
                remainder: pair.remainder,
                remainder_definiens,
            });
        }
        let mut definiens_names: HashSet<String> = HashSet::default();
        let mut definiens_visited: HashSet<TermId> = HashSet::default();
        for pair in &candidates {
            for definiens in [pair.quotient_definiens, pair.remainder_definiens] {
                self.collect_proof_symbol_names(
                    definiens,
                    &mut definiens_names,
                    &mut definiens_visited,
                );
            }
        }
        candidates.retain(|pair| {
            [pair.quotient, pair.remainder].iter().all(|&symbol| {
                matches!(self.ctx.terms.get(symbol), TermData::Var(name, _) if !definiens_names.contains(name))
            })
        });
        candidates
    }

    /// The pair whose quotient or remainder `atom` mentions, when exactly one
    /// pair's symbols occur in it.
    pub(super) fn divmod_pair_of(
        &self,
        atom: TermId,
        owner: &HashMap<TermId, usize>,
    ) -> Option<usize> {
        let mut found: Option<usize> = None;
        let mut stack = vec![atom];
        let mut visited: HashSet<TermId> = HashSet::default();
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            if let Some(&index) = owner.get(&term) {
                if found.is_some_and(|prior| prior != index) {
                    return None;
                }
                found = Some(index);
            }
            if let TermData::App(_, args) = self.ctx.terms.get(term) {
                stack.extend(args.iter().copied());
            }
        }
        found
    }
}
