// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! UNSAT publication of the QSAT route.
//!
//! The ∃ player's lemmas at level 1 carry the ∀ player's moves as TERMS
//! (substitution-based projection), and the conjunction of the matrix
//! instantiated at every move is unsatisfiable: the final level-0 check
//! refuted `φ ∧ ⋀¬Pᵢ` for all values of the universals, and `φ[tᵢ] ⇒ ¬Pᵢ`.
//! Those instances go to the authored consequence replay as records of the
//! authored conjuncts they instantiate: `forall` units, `(not (exists …))`
//! units through their dual, clause-shaped conjuncts (`(or …)`,
//! `(not (and …))`) literal by literal, and single-binder `exists`
//! conjuncts through registered Skolem witnesses. Deeper games go through
//! the expansion chain (`expansion.rs`); what neither can carry goes to the
//! artifact firewall's own producers. Only a strictly checked proof
//! publishes.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Symbol, TermData};
use ay_core::{Sort, TermId};

use super::super::proof::{
    ClausalInstanceRecord, ClausalLiteral, ExpansionStep, NegatedExistsDual,
};
use super::super::{Executor, SkolemInstanceRecord};
pub(super) use super::closed_terms::{and_closure, clause_literals, default_term, fold_closed};
use super::evidence::ProofStateSnapshot;
use crate::cegqi::lra_nested;
use crate::ematching::{contains_quantifier, ForallInstantiationProvenance};
use crate::executor_types::{Result, SolveResult, UnknownReason};
use crate::qsat::{self, Game, Run};

/// A published verdict and whether a proof was installed (the pass's terms
/// must then be kept).
pub(super) type Published = (Option<Result<SolveResult>>, bool);

/// Every record kind the depth-1 publication hands to the replay.
#[derive(Default)]
pub(super) struct Records {
    forall: Vec<ForallInstantiationProvenance>,
    duals: Vec<NegatedExistsDual>,
    skolem: Vec<SkolemInstanceRecord>,
    clausal: Vec<ClausalInstanceRecord>,
    /// Multi-binder `exists` conjuncts, Skolemized one binder at a time
    /// (`skolem::skolemize_binders`): `qnt_join` splits and `sko` steps.
    pub(super) chain: Vec<ExpansionStep>,
}

/// One universal literal of an authored conjunct.
#[derive(Clone)]
struct Universal {
    /// Index of its game occurrence.
    occurrence: usize,
    binders: Vec<(String, Sort)>,
    /// The body instances are taken from (the dual's body for `¬∃`).
    body: TermId,
    /// `(exists, dual forall)` for a negated existential.
    dual: Option<(TermId, TermId)>,
    /// The universal that is instantiated.
    quantifier: TermId,
}

enum Node {
    Unit(Universal, TermId),
    Clause(TermId, Vec<Option<Universal>>),
}

impl Executor {
    /// UNSAT publication (see the module docs): a published `unsat` also
    /// passes the evidence gate (`evidence.rs`).
    pub(super) fn qsat_publish_unsat(
        &mut self,
        roots: &[TermId],
        game: &Game,
        run: &Run,
    ) -> Published {
        let snapshot = ProofStateSnapshot::take(self);
        let (published, route) = self.qsat_publish_unsat_unchecked(roots, game, run);
        self.qsat_unsat_evidence_gate(published, route, snapshot)
    }

    /// The publication attempt and the label of the route that made it.
    fn qsat_publish_unsat_unchecked(
        &mut self,
        roots: &[TermId],
        game: &Game,
        run: &Run,
    ) -> (Published, &'static str) {
        // A multi-binder Skolemization (`qnt_join` + per-binder `sko`) is a
        // capability the route did not have: when its replay refuses, the
        // route goes on exactly as it did when that shape declined (the
        // expansion chain, then the firewall), so the new attempt can only
        // add a publication, never remove one.
        let depth1 = match self.qsat_unsat_records(roots, game, run) {
            Ok(mut records) => {
                let chain = std::mem::take(&mut records.chain);
                let multi_binder = !chain.is_empty();
                let published = self.qsat_replay_authored(roots, &records, &chain);
                if published.0.is_some() || !multi_binder {
                    let label = if published.0.is_some() {
                        "unsat-replayed"
                    } else {
                        "unsat-refused"
                    };
                    self.qsat_note("qsat.publish", label);
                    return (published, label);
                }
                self.qsat_note("qsat.publish_multi_binder", "unsat-refused");
                "unsat-multi-binder-exists"
            }
            Err(depth1) => depth1,
        };
        match self.qsat_expansion_chain(roots, game, run) {
            Ok(chain) => {
                let multi_binder = chain
                    .iter()
                    .any(|step| matches!(step, ExpansionStep::Join(_)));
                let published = self.qsat_replay_authored(roots, &Records::default(), &chain);
                if published.0.is_some() || !multi_binder {
                    let label = if published.0.is_some() {
                        "unsat-expansion"
                    } else {
                        "unsat-expansion-refused"
                    };
                    self.qsat_note("qsat.publish", label);
                    return (published, label);
                }
                self.qsat_note(
                    "qsat.publish_expansion",
                    "unsat-expansion-multi-binder-refused",
                );
                (
                    self.qsat_publish_unsat_firewall(roots, depth1),
                    "unsat-firewall",
                )
            }
            Err(reason) => {
                self.qsat_note("qsat.publish_expansion", reason);
                (
                    self.qsat_publish_unsat_firewall(roots, depth1),
                    "unsat-firewall",
                )
            }
        }
    }

    /// Last resort for a QSAT `unsat` no instance record can carry: the
    /// quantified-UNSAT artifact firewall's own producers (checked sidecar,
    /// authored ground core, ground instantiation, Boolean-skeleton
    /// refutation), exactly as the legacy path reaches them with a semantic
    /// `unsat`. Only a built strict artifact publishes.
    fn qsat_publish_unsat_firewall(&mut self, roots: &[TermId], reason: &'static str) -> Published {
        let window = std::mem::replace(&mut self.ctx.assertions, roots.to_vec());
        let saved_reason = self.last_unknown_reason;
        let result = self.quantified_semantic_unsat_or_unknown(UnknownReason::QuantifierUnhandled);
        self.ctx.assertions = window;
        match result {
            Ok(SolveResult::Unsat(proof)) => {
                self.qsat_note("qsat.publish", "unsat-firewall");
                self.last_unknown_reason = None;
                (Some(Ok(SolveResult::Unsat(proof))), true)
            }
            _ => {
                self.last_unknown_reason = saved_reason;
                self.qsat_note("qsat.publish", reason);
                (None, false)
            }
        }
    }

    /// The strict obligation is read from the live assertion window, which
    /// quantifier preprocessing may have rewritten (a folded linear equality
    /// inside a binder): the proof is over the AUTHORED roots, so present
    /// exactly those while the replay runs.
    ///
    /// The installed proof replaces `last_proof` outside the ordinary
    /// assembly, so it owes that assembly's final presentation pass: every
    /// reachable `assume` (and every `forall_inst` under an authored root)
    /// gets the problem file's own spelling, not AY's normalized rendering.
    ///
    /// A refused replay leaves every byte of proof state (the attempt ledger
    /// included) as it found it; the published one still owes the evidence
    /// gate (`evidence.rs`, applied by [`Self::qsat_publish_unsat`]).
    fn qsat_replay_authored(
        &mut self,
        roots: &[TermId],
        records: &Records,
        chain: &[ExpansionStep],
    ) -> Published {
        let saved = ProofStateSnapshot::take(self);
        let window = std::mem::replace(&mut self.ctx.assertions, roots.to_vec());
        let published = self.qsat_replay(records, chain);
        self.ctx.assertions = window;
        if published.0.is_none() {
            saved.restore(self);
            return published;
        }
        if let Some(proof) = self.last_proof.clone() {
            self.restore_reachable_authored_assume_surface_overrides(&proof);
            self.qsat_spell_replay_proof(&proof);
        }
        published
    }

    /// Hand the records to the consequence replay (probe without SOM) and publish
    /// an installed strict proof; the caller restores the ledger on a decline.
    fn qsat_replay(&mut self, records: &Records, chain: &[ExpansionStep]) -> Published {
        let installed = self.qsat_without_som(|this| {
            this.try_translate_authored_consequence_replay_unsat_with_clauses(
                &records.forall,
                &records.duals,
                &records.skolem,
                &records.clausal,
                chain,
            )
        });
        let publishable = installed
            && !self.should_abort_theory_loop()
            && self.authored_scope_strict_proof_installed();
        if !publishable {
            return (None, installed);
        }
        self.last_unknown_reason = None;
        (Some(Ok(SolveResult::unsat())), true)
    }

    /// A universal literal at level 1 (a depth-1 game node): a positive
    /// `forall` or a `(not (exists …))`, with a quantifier-free body.
    fn qsat_universal_literal(&mut self, game: &Game, literal: TermId) -> Option<Universal> {
        let find = |q: TermId, positive: bool| {
            game.occurrences.iter().position(|o| {
                o.quantifier == q
                    && o.positive == positive
                    && o.universal
                    && o.level == 1
                    && o.parent.is_none()
            })
        };
        match self.ctx.terms.get(literal).clone() {
            TermData::Forall(binders, body, _) => {
                let occurrence = find(literal, true)?;
                (!contains_quantifier(&self.ctx.terms, body)).then_some(Universal {
                    occurrence,
                    binders,
                    body,
                    dual: None,
                    quantifier: literal,
                })
            }
            TermData::Not(inner) => {
                let TermData::Exists(binders, body, _) = self.ctx.terms.get(inner).clone() else {
                    return None;
                };
                let occurrence = find(inner, false)?;
                if contains_quantifier(&self.ctx.terms, body) {
                    return None;
                }
                let negated = self.ctx.terms.mk_not_raw(body);
                let dual = self.ctx.terms.mk_forall(binders.clone(), negated);
                Some(Universal {
                    occurrence,
                    binders,
                    body: negated,
                    dual: Some((inner, dual)),
                    quantifier: dual,
                })
            }
            _ => None,
        }
    }

    /// Classify the quantified authored conjuncts.
    fn qsat_classify(
        &mut self,
        roots: &[TermId],
        game: &Game,
        records: &mut Records,
        map: &mut Vec<(TermId, TermId)>,
    ) -> std::result::Result<Vec<Node>, &'static str> {
        let mut nodes = Vec::new();
        for conjunct in and_closure(self, roots) {
            if !contains_quantifier(&self.ctx.terms, conjunct) {
                continue;
            }
            if let Some(u) = self.qsat_universal_literal(game, conjunct) {
                nodes.push(Node::Unit(u, conjunct));
            } else if matches!(self.ctx.terms.get(conjunct), TermData::Exists(binders, ..) if binders.len() > 1)
            {
                self.qsat_skolem_conjunct_binders(game, conjunct, map, records)?;
            } else if matches!(self.ctx.terms.get(conjunct), TermData::Exists(..)) {
                let record = self.qsat_skolem_conjunct(game, conjunct, map)?;
                records.skolem.push(record);
            } else {
                let literals = clause_literals(self, conjunct).ok_or("unsat-shape")?;
                let mut kinds = Vec::with_capacity(literals.len());
                for literal in literals {
                    kinds.push(if contains_quantifier(&self.ctx.terms, literal) {
                        Some(
                            self.qsat_universal_literal(game, literal)
                                .ok_or("unsat-clause-literal")?,
                        )
                    } else {
                        None
                    });
                }
                nodes.push(Node::Clause(conjunct, kinds));
            }
        }
        Ok(nodes)
    }

    /// The instance tuple of `u` at the ∀ move `mv`.
    fn qsat_tuple(
        &mut self,
        game: &Game,
        u: &Universal,
        mv: &HashMap<TermId, TermId>,
        map: &[(TermId, TermId)],
    ) -> std::result::Result<Vec<TermId>, &'static str> {
        let occ = game
            .occurrences
            .get(u.occurrence)
            .ok_or("unsat-occurrence")?;
        let mut tuple = Vec::with_capacity(occ.vars.len());
        for (&v, (_, sort)) in occ.vars.iter().zip(&u.binders) {
            tuple.push(match mv.get(&v) {
                Some(&t) => {
                    let t = qsat::mbp::substitute(&mut self.ctx.terms, t, map);
                    fold_closed(&mut self.ctx.terms, t)
                }
                None => default_term(self, sort),
            });
        }
        Ok(tuple)
    }

    fn qsat_instance(
        &mut self,
        u: &Universal,
        tuple: &[TermId],
    ) -> std::result::Result<TermId, &'static str> {
        lra_nested::tree::instantiate(&mut self.ctx.terms, u.body, &u.binders, tuple)
            .ok_or("unsat-substitution")
    }

    /// Records for one node at one ∀ move.
    fn qsat_node_records(
        &mut self,
        game: &Game,
        node: &Node,
        mv: &HashMap<TermId, TermId>,
        map: &[(TermId, TermId)],
        records: &mut Records,
        seen: &mut HashSet<TermId>,
    ) -> std::result::Result<(), &'static str> {
        match node {
            Node::Unit(u, source) => {
                let tuple = self.qsat_tuple(game, u, mv, map)?;
                let instance = self.qsat_instance(u, &tuple)?;
                if !seen.insert(instance) {
                    return Ok(());
                }
                if let Some((exists, forall)) = u.dual {
                    if !records.duals.iter().any(|d| d.forall == forall) {
                        records.duals.push(NegatedExistsDual {
                            not_exists_root: *source,
                            exists,
                            forall,
                            co_units: Vec::new(),
                        });
                    }
                }
                records.forall.push(ForallInstantiationProvenance {
                    quantifier: u.quantifier,
                    binding: tuple,
                    instance,
                });
            }
            Node::Clause(source, kinds) => {
                let literal_terms = clause_literals(self, *source).ok_or("unsat-shape")?;
                let mut literals = Vec::with_capacity(kinds.len());
                let mut rewritten = Vec::with_capacity(kinds.len());
                for (kind, &literal) in kinds.iter().zip(&literal_terms) {
                    let Some(u) = kind else {
                        literals.push(ClausalLiteral::Keep);
                        rewritten.push(literal);
                        continue;
                    };
                    let tuple = self.qsat_tuple(game, u, mv, map)?;
                    rewritten.push(self.qsat_instance(u, &tuple)?);
                    literals.push(match u.dual {
                        None => ClausalLiteral::Forall { binding: tuple },
                        Some((_, forall)) => ClausalLiteral::NegatedExists {
                            forall,
                            binding: tuple,
                        },
                    });
                }
                let consequence = self
                    .ctx
                    .terms
                    .mk_app(Symbol::named("or"), rewritten, Sort::Bool);
                if seen.insert(consequence) {
                    records.clausal.push(ClausalInstanceRecord {
                        source: *source,
                        literals,
                        consequence,
                    });
                }
            }
        }
        Ok(())
    }

    /// Records of a depth-1 refutation, or why the shape is out of reach.
    fn qsat_unsat_records(
        &mut self,
        roots: &[TermId],
        game: &Game,
        run: &Run,
    ) -> std::result::Result<Records, &'static str> {
        let mut records = Records::default();
        // Engine level-0 variables -> publication terms.
        let mut map: Vec<(TermId, TermId)> = Vec::new();
        let nodes = self.qsat_classify(roots, game, &mut records, &mut map)?;
        for p in &game.purified {
            if p.level == 0 {
                let def = qsat::mbp::substitute(&mut self.ctx.terms, p.def, &map);
                map.push((p.var, def));
            }
        }
        // The ∀ player's moves: one substitution per ∃ lemma at level 1, or
        // a default move when the matrix was refuted outright.
        let mut moves: Vec<HashMap<TermId, TermId>> = run
            .lemmas
            .iter()
            .filter(|l| !l.forall_owned && l.level == 1)
            .map(|l| l.subst.iter().copied().collect())
            .collect();
        if moves.is_empty() {
            moves.push(HashMap::default());
        }
        let mut seen = HashSet::default();
        for mv in &moves {
            for node in &nodes {
                self.qsat_node_records(game, node, mv, &map, &mut records, &mut seen)?;
            }
        }
        let total = records.forall.len()
            + records.clausal.len()
            + records.skolem.len()
            + records.chain.len();
        if total > lra_nested::caps::M1_PUBLISHABLE_INSTANCES {
            return Err("unsat-too-many-instances");
        }
        Ok(records)
    }
}
