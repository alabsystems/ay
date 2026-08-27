// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Assembling the CONJUNCT-BY-CONJUNCT decomposition fragment.
//!
//! Split out of `conjunct_decomposition_leaf.rs` so each file stays inside the
//! repository's 500-line ceiling. That file owns the lane, the alignment and
//! the module-level soundness argument; this one turns one
//! `(leaf, root, minted)` triple into steps.

use ay_core::kani_compat::DetHashMap;
use ay_core::{AletheRule, ProofId, ProofStep, TermData, TermId};

use super::super::Executor;
use super::congruence_explanation::offset_premises;
use super::minted_definition_leaf::{syntactic_complement, MintContext, Minted};
use super::rewritten_assertion_bridge::{is_binary_equality, ConjunctDescent, HypothesisLeaf};

impl Executor {
    /// Build the whole replacement fragment for one leaf, or `None`.
    ///
    /// `conjuncts` are the LEAF's, `root_conjuncts` the ROOT's, index for
    /// index; the caller has already established that they have the same
    /// length and that at least one position differs.
    pub(super) fn assemble_decomposition(
        &mut self,
        atom: TermId,
        root: TermId,
        conjuncts: &[TermId],
        root_conjuncts: &[TermId],
        minted: &[Minted],
        context: &MintContext<'_>,
    ) -> Option<Vec<ProofStep>> {
        let (pool, leaf_of) = self.decomposition_pool(minted, context)?;
        let mut fragment: Vec<ProofStep> = Vec::new();
        let mut root_assumes: DetHashMap<TermId, usize> = DetHashMap::default();
        let mut units: Vec<usize> = Vec::with_capacity(conjuncts.len());
        for (position, (&goal_conjunct, &root_conjunct)) in
            conjuncts.iter().zip(root_conjuncts.iter()).enumerate()
        {
            let position = u32::try_from(position).ok()?;
            let source = self.push_root_conjunct(
                &mut fragment,
                &mut root_assumes,
                root,
                position,
                root_conjunct,
            )?;
            let unit = if goal_conjunct == root_conjunct {
                source
            } else {
                self.push_rewritten_conjunct(
                    &mut fragment,
                    source,
                    root_conjunct,
                    goal_conjunct,
                    &pool,
                    &leaf_of,
                )?
            };
            units.push(unit);
        }
        self.close_with_and_neg(&mut fragment, atom, conjuncts, &units)?;
        // Guard 8: the fragment ends on exactly the leaf's clause.
        match fragment.last() {
            Some(ProofStep::Step { clause, .. }) if clause.as_slice() == [atom] => {}
            _ => return None,
        }
        // Guard 5, re-asked at EMISSION time: every `fresh_def_eq` step the
        // fragment carries must be one the CHECKER's own recognizer admits for
        // exactly that `(clause, premises, args)` triple.
        fragment
            .iter()
            .all(|step| match step {
                ProofStep::Step {
                    rule: AletheRule::FreshDefEq,
                    clause,
                    premises,
                    args,
                } => {
                    premises.is_empty()
                        && ay_core::proof_validation::recognize_fresh_def_eq(
                            &self.ctx.terms,
                            clause,
                            0,
                            args,
                        )
                        .is_ok()
                }
                _ => true,
            })
            .then_some(fragment)
    }

    /// The hypothesis pool for the per-conjunct congruences: the sibling
    /// lanes' base pool plus this leaf's minted definitions.
    fn decomposition_pool(
        &self,
        minted: &[Minted],
        context: &MintContext<'_>,
    ) -> Option<(Vec<TermId>, DetHashMap<TermId, HypothesisLeaf>)> {
        let mut pool = context.base_pool.to_vec();
        let mut leaf_of = context.base_leaf_of.clone();
        for entry in minted {
            if leaf_of
                .insert(
                    entry.definition,
                    HypothesisLeaf::Definition {
                        rule: AletheRule::FreshDefEq,
                        args: vec![entry.definiendum],
                    },
                )
                .is_none()
            {
                pool.push(entry.definition);
            }
        }
        (pool.len() <= ay_proof::MAX_BRIDGE_CANDIDATES).then_some((pool, leaf_of))
    }

    /// Derive `(cl root_conjunct)` from an `assume` of `root` by one `and_pos`
    /// at `position`, and return the index of that unit step.
    ///
    /// The emitter is the rewritten-assertion bridge's own `Conjunct` arm,
    /// reused verbatim — including its sharing of one `assume` per root.
    fn push_root_conjunct(
        &mut self,
        fragment: &mut Vec<ProofStep>,
        root_assumes: &mut DetHashMap<TermId, usize>,
        root: TermId,
        position: u32,
        root_conjunct: TermId,
    ) -> Option<usize> {
        let not_root = self.ctx.terms.mk_not_raw(root);
        let leaf = HypothesisLeaf::Conjunct {
            root,
            descents: vec![ConjunctDescent {
                position,
                parent: root,
                not_parent: not_root,
                child: root_conjunct,
            }],
        };
        self.push_hypothesis_leaf(fragment, root_assumes, &leaf, root_conjunct)
    }

    /// Turn a derived `(cl root_conjunct)` into `(cl goal_conjunct)` through
    /// the congruence between them, and return the index of that unit step.
    ///
    /// This is the non-equality bridge's propositional tail with ONE
    /// difference: its source is a DERIVED step inside this fragment rather
    /// than an `assume`, because a conjunct is not an authored assertion and
    /// `validate_reachable_assumes_in_problem_scope` admits only EXACT
    /// membership.
    fn push_rewritten_conjunct(
        &mut self,
        fragment: &mut Vec<ProofStep>,
        source: usize,
        root_conjunct: TermId,
        goal_conjunct: TermId,
        pool: &[TermId],
        leaf_of: &DetHashMap<TermId, HypothesisLeaf>,
    ) -> Option<usize> {
        if self.ctx.terms.sort(root_conjunct) != self.ctx.terms.sort(goal_conjunct) {
            return None;
        }
        // `mk_eq` folds a Boolean equality in six different ways — and the
        // LIFTING `(= (not x) (not y)) -> (= x y)` is exactly what lets this
        // lane past the `not` the whole-term congruence cannot descend. The
        // built term is decoded back and anything that is not a binary `=`
        // application is declined.
        let goal = self.ctx.terms.mk_eq(root_conjunct, goal_conjunct);
        if !is_binary_equality(&self.ctx.terms, goal) {
            return None;
        }
        let equality = self.push_conjunct_equality(fragment, goal, pool, leaf_of)?;
        let complement = syntactic_complement(&mut self.ctx.terms, root_conjunct);
        let not_goal = self.ctx.terms.mk_not(goal);
        // The gate literal must be a plain `Not` wrapper: `mk_not` normalises
        // De Morgan, and a literal that is not the wrapper is not what the
        // validator reads as `(not (= ..))`.
        if !matches!(self.ctx.terms.get(not_goal), TermData::Not(inner) if *inner == goal) {
            return None;
        }
        let clause = vec![not_goal, complement, goal_conjunct];
        // Guard 6, second half: the propositional rule is CHOSEN by the
        // checker, not by re-deriving its operand-order convention here.
        let rule = self.equiv_rule_accepted_for(&clause)?;
        fragment.push(ProofStep::Step {
            rule,
            clause: clause.clone(),
            premises: Vec::new(),
            args: Vec::new(),
        });
        let tautology = fragment.len() - 1;
        fragment.push(ProofStep::Step {
            rule: AletheRule::ThResolution,
            clause: vec![complement, goal_conjunct],
            premises: vec![
                ProofId(u32::try_from(tautology).ok()?),
                ProofId(u32::try_from(equality).ok()?),
            ],
            args: Vec::new(),
        });
        let resolved = fragment.len() - 1;
        fragment.push(ProofStep::Step {
            rule: AletheRule::ThResolution,
            clause: vec![goal_conjunct],
            premises: vec![
                ProofId(u32::try_from(resolved).ok()?),
                ProofId(u32::try_from(source).ok()?),
            ],
            args: Vec::new(),
        });
        Some(fragment.len() - 1)
    }

    /// Emit the steps that derive `(cl goal)`, and return the index of the
    /// step whose clause that is.
    ///
    /// TWO routes, and the first is not an optimisation — it is the case this
    /// lane's own population needs. When the leaf's conjunct IS the fresh
    /// symbol and the root's conjunct is its definiens, the equality the
    /// conjunct needs is VERBATIM the minted definition, and
    /// `ay_proof::plan_definitional_bridge` declines a goal that is its own
    /// hypothesis — it plans a CONGRUENCE, and there is nothing here to
    /// congruence over. Measured on `clearsy_0001_00310_falsesat44`: 26 of 26
    /// planning attempts declined at conjunct 9,
    /// `(= (= g_s148_149 g_s636_732) boolarg_848)`, which is itself a pool
    /// entry. Citing the hypothesis directly is no new authority: it is exactly
    /// the leaf the sibling bridge lanes already emit for a cited hypothesis,
    /// under the same pool rule.
    fn push_conjunct_equality(
        &mut self,
        fragment: &mut Vec<ProofStep>,
        goal: TermId,
        pool: &[TermId],
        leaf_of: &DetHashMap<TermId, HypothesisLeaf>,
    ) -> Option<usize> {
        if let Some(leaf) = leaf_of.get(&goal) {
            let mut root_assumes: DetHashMap<TermId, usize> = DetHashMap::default();
            let mut sub: Vec<ProofStep> = Vec::new();
            let last = self.push_hypothesis_leaf(&mut sub, &mut root_assumes, leaf, goal)?;
            // The cited leaf's LAST step must be the one carrying `(cl goal)`.
            if last + 1 != sub.len() {
                return None;
            }
            let base = fragment.len();
            for step in sub {
                fragment.push(offset_premises(step, base));
            }
            return fragment.len().checked_sub(1);
        }
        let bridge = ay_proof::plan_definitional_bridge(&mut self.ctx.terms, goal, pool)?;
        // Guard 6: the untouched strict checker replays the congruence half,
        // closed, before any step of it may enter the proof.
        let closed = ay_proof::close_congruence_derivation(&mut self.ctx.terms, &bridge.derivation);
        if ay_proof::check_proof_strict(&closed, &self.ctx.terms).is_err() {
            return None;
        }
        let sub = self.assemble_bridge_fragment(&bridge, leaf_of, goal)?;
        let base = fragment.len();
        for step in sub {
            fragment.push(offset_premises(step, base));
        }
        fragment.len().checked_sub(1)
    }

    /// Which `equiv_pos` rule states `clause` — decided by CLOSING the
    /// one-step fragment and asking the untouched strict checker.
    fn equiv_rule_accepted_for(&mut self, clause: &[TermId]) -> Option<AletheRule> {
        [AletheRule::EquivPos1, AletheRule::EquivPos2]
            .into_iter()
            .find(|rule| {
                let derivation = ay_proof::CongruenceDerivation {
                    steps: vec![ProofStep::Step {
                        rule: rule.clone(),
                        clause: clause.to_vec(),
                        premises: Vec::new(),
                        args: Vec::new(),
                    }],
                    clause: clause.to_vec(),
                };
                let closed =
                    ay_proof::close_congruence_derivation(&mut self.ctx.terms, &derivation);
                ay_proof::check_proof_strict(&closed, &self.ctx.terms).is_ok()
            })
    }

    /// Reassemble the conjunction from the `n` derived unit clauses: one
    /// `and_neg` tautology and one chain `th_resolution`.
    fn close_with_and_neg(
        &mut self,
        fragment: &mut Vec<ProofStep>,
        atom: TermId,
        conjuncts: &[TermId],
        units: &[usize],
    ) -> Option<()> {
        if units.len() != conjuncts.len() {
            return None;
        }
        let mut clause = Vec::with_capacity(conjuncts.len() + 1);
        clause.push(atom);
        for &conjunct in conjuncts {
            clause.push(syntactic_complement(&mut self.ctx.terms, conjunct));
        }
        // Guard 7: `validate_and_neg` — not this lane — decides that the
        // complement literals bijectively cover the conjuncts. The step is
        // CLOSED into a self-contained refutation and replayed by the
        // UNTOUCHED strict checker before it may enter the fragment.
        let step = ProofStep::Step {
            rule: AletheRule::AndNeg,
            clause: clause.clone(),
            premises: Vec::new(),
            args: vec![atom],
        };
        let derivation = ay_proof::CongruenceDerivation {
            steps: vec![step.clone()],
            clause: clause.clone(),
        };
        let closed = ay_proof::close_congruence_derivation(&mut self.ctx.terms, &derivation);
        if ay_proof::check_proof_strict(&closed, &self.ctx.terms).is_err() {
            return None;
        }
        fragment.push(step);
        let and_neg = fragment.len() - 1;
        let mut premises = Vec::with_capacity(units.len() + 1);
        premises.push(ProofId(u32::try_from(and_neg).ok()?));
        for &unit in units {
            premises.push(ProofId(u32::try_from(unit).ok()?));
        }
        fragment.push(ProofStep::Step {
            rule: AletheRule::ThResolution,
            clause: vec![atom],
            premises,
            args: Vec::new(),
        });
        Some(())
    }
}
