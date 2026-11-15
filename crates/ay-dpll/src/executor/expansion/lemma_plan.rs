// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The lemma plan of the UNSAT expansion certificate (plan §4.1).
//!
//! Every authored root is walked in NNF polarity over the nested search's
//! node tree and instance log Γ. Each quantifier occurrence contributes
//! lemma clauses of four kinds, EVERY ONE VALID AT ANY POLARITY:
//!
//! | kind | occurrence | lemma term | derivation |
//! |---|---|---|---|
//! | L1 | effective ∀, authored `forall` Q | `(or (not Q) Q_body[v⃗])` | `forall_inst` |
//! | L2 | effective ∀, authored `exists` E | `(or E F)` + L1 on `F` | `qnt_neg_exists` (+ `or_neg`/`contraction`) |
//! | L3 | effective ∃, authored `exists` E | `(= E E_body[w])` | `sko` (registered choice) |
//! | L4 | effective ∃, authored `forall` Q | `(= Q Q_body[w])` | `sko` (registered Skolem symbol) |
//!
//! `F` is the universal dual `∀x⃗. ¬E_body` of `E`. A lemma is never a
//! free-standing instance: `#quant-alternation` stays intact because only the
//! authored roots are ever assumed, and a lemma holds in every model of the
//! quantifiers it mentions.
//!
//! Effective-∀ occurrences contribute every logged tuple of their node,
//! transported onto the surface (enclosing instance values and witnesses);
//! effective-∃ occurrences contribute one registered witness per enclosing
//! instance path. Merged same-kind blocks are expanded one AUTHORED
//! quantifier at a time (chained `forall_inst` / `sko`), so nested singleton
//! binders need no multi-binder `sko`; a multi-binder effective-∃ level
//! declines ([`PlanDecline::MultiBinderSkolem`]; the M0 scan found none in
//! the recognized population).
//!
//! The plan is a set of CANDIDATE lemmas: the certificate proves each one
//! with its strict derivation and a ground probe decides whether they refute
//! the roots. Nothing here grants anything.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Symbol, TermData};
use ay_core::{SkolemChoice, Sort, TermId, TermStore};

use super::align::{self, Sigma};
use super::lemma::MAX_EXPANSION_LEMMAS;
pub(in crate::executor) use super::lemma::{Lemma, LemmaKind, LemmaPlan, PlanDecline};
use crate::cegqi::lra_nested::approx::NInstance;
use crate::cegqi::lra_nested::ntree::{arg_pols, Kind, NestedTree, Pol};
use crate::ematching::subst_vars_exact_qf;

struct Planner<'a> {
    terms: &'a mut TermStore,
    tree: &'a NestedTree,
    gamma: &'a [Vec<NInstance>],
    /// The search's own constants: counterexample and Skolem constants.
    pattern: HashSet<TermId>,
    plan: LemmaPlan,
    visited: HashSet<(TermId, TermId, bool, bool, bool)>,
    quantified: HashMap<TermId, bool>,
    /// Surface quantifier → its Skolem instance `Q_body[w]`.
    skolemized: HashMap<TermId, TermId>,
    /// Surface existential → its universal dual.
    duals: HashMap<TermId, TermId>,
}

/// Build the lemma plan of `authored` (the exact roots the search's
/// `tree.roots` were rewritten from, in the same order) from the search's
/// final instance log `gamma`. Mints and registers Skolem witnesses.
pub(in crate::executor) fn build_lemma_plan(
    terms: &mut TermStore,
    tree: &NestedTree,
    gamma: &[Vec<NInstance>],
    authored: &[TermId],
) -> Result<LemmaPlan, PlanDecline> {
    if authored.len() != tree.roots.len() || gamma.len() != tree.nodes.len() {
        return Err(PlanDecline::Alignment);
    }
    let mut pattern: HashSet<TermId> = tree.skolems.iter().copied().collect();
    for node in &tree.nodes {
        pattern.extend(node.ce_vars.iter().copied());
    }
    let mut planner = Planner {
        terms,
        tree,
        gamma,
        pattern,
        plan: LemmaPlan::default(),
        visited: HashSet::default(),
        quantified: HashMap::default(),
        skolemized: HashMap::default(),
        duals: HashMap::default(),
    };
    for (&root, &search) in authored.iter().zip(&tree.roots) {
        planner.walk(root, search, Pol::POS, true)?;
    }
    let lemma_terms: Vec<TermId> = planner.plan.lemmas.iter().map(|l| l.term).collect();
    if align::mentions_any(planner.terms, &planner.pattern, &lemma_terms) {
        return Err(PlanDecline::SearchConstantLeak);
    }
    Ok(planner.plan)
}

fn or2(terms: &mut TermStore, a: TermId, b: TermId) -> TermId {
    terms.mk_app(Symbol::named("or"), vec![a, b], Sort::Bool)
}

impl Planner<'_> {
    fn has_quantifier(&mut self, term: TermId) -> bool {
        if let Some(&known) = self.quantified.get(&term) {
            return known;
        }
        let known = match self.terms.get(term).clone() {
            TermData::Forall(..) | TermData::Exists(..) | TermData::Let(..) => true,
            TermData::App(_, args) => args.iter().any(|&a| self.has_quantifier(a)),
            TermData::Not(inner) => self.has_quantifier(inner),
            TermData::Ite(c, a, b) => {
                self.has_quantifier(c) || self.has_quantifier(a) || self.has_quantifier(b)
            }
            _ => false,
        };
        self.quantified.insert(term, known);
        known
    }

    fn push(&mut self, term: TermId, kind: LemmaKind) -> Result<(), PlanDecline> {
        if self.plan.by_term.contains_key(&term) {
            return Ok(());
        }
        if self.plan.lemmas.len() >= MAX_EXPANSION_LEMMAS {
            return Err(PlanDecline::Cap);
        }
        self.plan.by_term.insert(term, self.plan.lemmas.len());
        self.plan.lemmas.push(Lemma { term, kind });
        Ok(())
    }

    /// Walk the surface term `surface` in lockstep with its search
    /// counterpart `search`, at polarity `pol`. `top`: no enclosing
    /// quantifier occurrence, where the tree builder Skolemized every
    /// single-polarity effective existential in place.
    fn walk(
        &mut self,
        surface: TermId,
        search: TermId,
        pol: Pol,
        top: bool,
    ) -> Result<(), PlanDecline> {
        if !self.has_quantifier(surface) {
            return Ok(());
        }
        if !self
            .visited
            .insert((surface, search, pol.pos, pol.neg, top))
        {
            return Ok(());
        }
        stacker::maybe_grow(64 * 1024, 2 * 1024 * 1024, || {
            self.walk_inner(surface, search, pol, top)
        })
    }

    fn walk_inner(
        &mut self,
        surface: TermId,
        search: TermId,
        pol: Pol,
        top: bool,
    ) -> Result<(), PlanDecline> {
        match self.terms.get(surface).clone() {
            TermData::Not(inner) => {
                let TermData::Not(s) = self.terms.get(search).clone() else {
                    return Err(PlanDecline::Alignment);
                };
                self.walk(inner, s, pol.flip(), top)
            }
            TermData::Ite(c, a, b) => {
                let TermData::Ite(sc, sa, sb) = self.terms.get(search).clone() else {
                    return Err(PlanDecline::Alignment);
                };
                self.walk(c, sc, Pol::BOTH, top)?;
                self.walk(a, sa, pol, top)?;
                self.walk(b, sb, pol, top)
            }
            TermData::App(symbol, args) => {
                let TermData::App(s_symbol, s_args) = self.terms.get(search).clone() else {
                    return Err(PlanDecline::Alignment);
                };
                if s_symbol != symbol || s_args.len() != args.len() {
                    return Err(PlanDecline::Alignment);
                }
                let pols = arg_pols(self.terms, symbol.name(), &args, pol)
                    .ok_or(PlanDecline::Connective)?;
                for ((&arg, &s_arg), arg_pol) in args.iter().zip(&s_args).zip(pols) {
                    self.walk(arg, s_arg, arg_pol, top)?;
                }
                Ok(())
            }
            TermData::Forall(..) | TermData::Exists(..) => {
                // Mirror of the tree builder's `skolemize`: at top level a
                // single-polarity effective existential was replaced by its
                // body over fresh Skolem constants; every other quantifier
                // occurrence is a node.
                let exists = matches!(self.terms.get(surface), TermData::Exists(..));
                if top && !pol.both() && exists == pol.pos {
                    return self.top_skolem(surface, search, pol);
                }
                match self.tree.node_of.get(&search) {
                    Some(&node) => self.node_occurrence(node, surface, search, pol),
                    None => Err(PlanDecline::Alignment),
                }
            }
            _ => Err(PlanDecline::Connective),
        }
    }

    /// A quantifier the search Skolemized in place (top level, single
    /// polarity, effectively existential): one `sko` level, then continue
    /// against the search's rewritten body.
    fn top_skolem(&mut self, surface: TermId, search: TermId, pol: Pol) -> Result<(), PlanDecline> {
        let instance = self.skolem(surface)?;
        self.walk(instance, search, pol, true)
    }

    /// `(= Q Q_body[w])` for a single-binder quantifier `Q`, minting and
    /// registering `w` once per surface term. Returns `Q_body[w]`.
    fn skolem(&mut self, quantified: TermId) -> Result<TermId, PlanDecline> {
        if let Some(&done) = self.skolemized.get(&quantified) {
            return Ok(done);
        }
        let (bindings, body, exists) = match self.terms.get(quantified).clone() {
            TermData::Exists(b, body, _) => (b, body, true),
            TermData::Forall(b, body, _) => (b, body, false),
            _ => return Err(PlanDecline::Alignment),
        };
        let [(binder, sort)] = bindings.as_slice() else {
            return Err(PlanDecline::MultiBinderSkolem);
        };
        let witness = self
            .terms
            .mk_fresh_var(&format!("sk!{binder}"), sort.clone());
        if let TermData::Var(name, _) = self.terms.get(witness).clone() {
            self.terms.mark_skolem_symbol(name);
        }
        // The same registration `skolemize.rs` makes: the choice body of a
        // `forall` source is the negated body (`¬∀x.B ≡ ∃x.¬B`).
        let choice_body = if exists {
            body
        } else {
            self.terms.mk_not(body)
        };
        self.terms.register_skolem_choice(
            witness,
            SkolemChoice {
                binder: binder.clone(),
                sort: sort.clone(),
                body: choice_body,
            },
        );
        let map: HashMap<String, TermId> = [(binder.clone(), witness)].into_iter().collect();
        let instance =
            subst_vars_exact_qf(self.terms, body, &map).ok_or(PlanDecline::Substitution)?;
        let equality =
            self.terms
                .mk_app(Symbol::named("="), vec![quantified, instance], Sort::Bool);
        self.push(
            equality,
            LemmaKind::Skolem {
                quantified,
                witness,
            },
        )?;
        self.skolemized.insert(quantified, instance);
        Ok(instance)
    }

    /// `(or E F)` for the universal dual `F` of `E`. Returns `F`.
    fn dual(&mut self, exists: TermId) -> Result<TermId, PlanDecline> {
        if let Some(&done) = self.duals.get(&exists) {
            return Ok(done);
        }
        let TermData::Exists(bindings, body, triggers) = self.terms.get(exists).clone() else {
            return Err(PlanDecline::Alignment);
        };
        let negated = self.terms.mk_not_raw(body);
        let dual = self
            .terms
            .mk_forall_with_triggers(bindings, negated, triggers);
        let term = or2(self.terms, exists, dual);
        self.push(term, LemmaKind::NegatedExists { exists, dual })?;
        self.duals.insert(exists, dual);
        Ok(dual)
    }

    /// The authored binder levels of the merged node read off its surface
    /// term, which must carry exactly the node's binders in order.
    fn levels(
        &self,
        surface: TermId,
        node: usize,
    ) -> Result<Vec<Vec<(String, Sort)>>, PlanDecline> {
        let expected = &self.tree.nodes[node].binders;
        let exists = self.tree.nodes[node].kind == Kind::Exists;
        let mut levels = Vec::new();
        let mut seen = 0;
        let mut current = surface;
        while seen < expected.len() {
            let (bindings, body) = match (exists, self.terms.get(current)) {
                (false, TermData::Forall(b, body, _)) | (true, TermData::Exists(b, body, _)) => {
                    (b.clone(), *body)
                }
                _ => return Err(PlanDecline::Alignment),
            };
            if expected.get(seen..seen + bindings.len()) != Some(bindings.as_slice()) {
                return Err(PlanDecline::Alignment);
            }
            seen += bindings.len();
            levels.push(bindings);
            current = body;
        }
        Ok(levels)
    }

    fn node_occurrence(
        &mut self,
        node: usize,
        surface: TermId,
        search: TermId,
        pol: Pol,
    ) -> Result<(), PlanDecline> {
        let sigma = align::bind(self.terms, &self.pattern, search, surface)?;
        let levels = self.levels(surface, node)?;
        let forall = self.tree.nodes[node].kind == Kind::Forall;
        // Effective ∀ side: the logged instances. Effective ∃ side: Skolem.
        if pol.pos {
            if forall {
                self.instances(node, surface, &levels, &sigma, Pol::POS)?;
            } else {
                self.skolem_chain(node, surface, &levels, pol)?;
            }
        }
        if pol.neg {
            if forall {
                self.skolem_chain(node, surface, &levels, pol)?;
            } else {
                self.instances(node, surface, &levels, &sigma, Pol::NEG)?;
            }
        }
        Ok(())
    }

    /// L1 (authored `forall`, `side` positive) or L2 (authored `exists`,
    /// `side` negative) for every logged tuple of `node`, then the instance
    /// bodies, which carry the occurrence's own polarity `side`.
    fn instances(
        &mut self,
        node: usize,
        surface: TermId,
        levels: &[Vec<(String, Sort)>],
        sigma: &Sigma,
        side: Pol,
    ) -> Result<(), PlanDecline> {
        let forall = self.tree.nodes[node].kind == Kind::Forall;
        let ce_body = self.tree.nodes[node].ce_body;
        let mut memo = HashMap::default();
        for index in 0..self.gamma[node].len() {
            let tuple = self.gamma[node][index].tuple.clone();
            let mut values = Vec::with_capacity(tuple.len());
            for &t in &tuple {
                values.push(align::apply(
                    self.terms,
                    &self.pattern,
                    sigma,
                    t,
                    &mut memo,
                )?);
            }
            let mut current = surface;
            let mut offset = 0;
            for bindings in levels {
                let slice = values
                    .get(offset..offset + bindings.len())
                    .ok_or(PlanDecline::Alignment)?
                    .to_vec();
                offset += bindings.len();
                let source = if forall { current } else { self.dual(current)? };
                let TermData::Forall(_, body, _) = self.terms.get(source).clone() else {
                    return Err(PlanDecline::Alignment);
                };
                let map: HashMap<String, TermId> = bindings
                    .iter()
                    .map(|(name, _)| name.clone())
                    .zip(slice.iter().copied())
                    .collect();
                let instance =
                    subst_vars_exact_qf(self.terms, body, &map).ok_or(PlanDecline::Substitution)?;
                let not_source = self.terms.mk_not_raw(source);
                let term = or2(self.terms, not_source, instance);
                self.push(
                    term,
                    LemmaKind::ForallInst {
                        quantifier: source,
                        values: slice,
                    },
                )?;
                current = if forall {
                    instance
                } else {
                    // The dual's instance is `(not E_body[v⃗])`.
                    match self.terms.get(instance) {
                        TermData::Not(inner) => *inner,
                        _ => return Err(PlanDecline::Alignment),
                    }
                };
            }
            if offset != values.len() {
                return Err(PlanDecline::Alignment);
            }
            self.walk(current, ce_body, side, false)?;
        }
        Ok(())
    }

    /// L3/L4 one authored level at a time, then the witnessed body at the
    /// occurrence's full polarity (an iff occurrence keeps both).
    fn skolem_chain(
        &mut self,
        node: usize,
        surface: TermId,
        levels: &[Vec<(String, Sort)>],
        pol: Pol,
    ) -> Result<(), PlanDecline> {
        let mut current = surface;
        for bindings in levels {
            if bindings.len() != 1 {
                return Err(PlanDecline::MultiBinderSkolem);
            }
            current = self.skolem(current)?;
        }
        self.walk(current, self.tree.nodes[node].ce_body, pol, false)
    }
}
