// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Confining a CERTIFIED `let` assume spelling to its own `assume`, before any
//! step is printed.
//!
//! # The leak this closes
//!
//! The root surface override of an assertion authored with `let` IS the
//! authored `(let ...)` text: carcara matches every `assume` against the
//! problem file through, never into, `Term::Let`, so the leaf must reproduce
//! it. [`AlethePrinter::format_let_assume_bridge`] keeps that leaf exact under
//! `tK.a` and derives the eliminated term at `tK`; it installed the eliminated
//! rendering in `let_bridge_renderings` only when the `assume` itself was
//! printed, and never touched the wire view (`wire_term_overrides`). So the
//! `(let ...)` text stayed DOCUMENT-WIDE in three places:
//!
//! * every step printed BEFORE the `assume` spelled the root (and every term
//!   above it) through the producer's table, and the memo kept those
//!   renderings for steps printed after it;
//! * every wire judgement — the printer's own and the producer's
//!   (`effective_wire_term_overrides_for_authored_proof`) — read the `let`
//!   text, which no theory lowering can decompose;
//! * every producer that predicts a step FRAGMENT's text with the bare step
//!   formatter read the raw table
//!   ([`crate::term_overrides_outside_confined_let_assumes`] is the table the
//!   export actually prints).
//!
//! MEASURED on `benchmarks/smt/QF_AUFLIA/storeinv_nf_size2.smt2`, whose
//! assumed array equality is authored as `(let ((?v_0 ..) (?v_1 ..)) (= (store
//! ?v_1 ..) (store ?v_0 ..)))`: the `ArrayRowChain` lemma at `t5` precedes the
//! `assume` at `t6`, `format_array_row_chain` refused the `let`-abbreviated
//! equality (by design) and printed `hole`, the `EufCongruenceExplanation` at
//! `t16` printed `hole` too, and the printed-text `or_pos` judge refused
//! `t18`, so the whole export was refused. The let-free spelling of the same
//! problem publishes `unsat` with no hole, carcara `valid`; with this channel
//! and the fragment table, so does the `let` spelling (canonical invocation).
//!
//! # The repair
//!
//! Exactly the folded-conjunction channel's (`folded_assume.rs`): decide
//! before emission. Every assumed term whose authored spelling is a `let` that
//! the bridge eliminates on its CERTIFIED arm (the textual substitution IS the
//! document's rendering, so the equivalence is a genuine `refl`/`let`
//! derivation) gets its eliminated rendering in `let_bridge_renderings` and
//! leaves the wire view now. The `assume` still re-reads the authored text
//! (`format_step_text` already does, for a term the bridge channel shadows)
//! and prints the same bridge it printed before. That bridge is valid in
//! pinned Carcara's canonical plain invocation only, which the certificate
//! discloses as `carcara_surface=without-let-expansion`.
//!
//! A `let` the bridge can eliminate only through its `hole` arm is left
//! exactly as it was; so is a term another channel already owns, and so is
//! every root of a nested group (one root's certified text spells another
//! root's authored `let`), whose certification depends on that spelling.

use super::{AlethePrintError, AlethePrinter, HashMap};
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::{AletheRule, Proof, ProofStep, TermId};

/// Cap the planning scan. Override tables are already bounded by the collector
/// (`surface_override_map_is_bounded`); this is the printer's own belt.
const MAX_CONFINED_LET_ASSUMES: usize = 8_192;

/// Cap the nesting walk over the planned roots' shared DAG; past it nothing is
/// confined, which is the pre-confinement document.
const MAX_NESTING_WALK_TERMS: usize = 1 << 20;

impl AlethePrinter<'_> {
    /// Confine every certified `let` assume spelling of `proof` to its
    /// `assume`; see the module docs. Runs after every other channel that can
    /// re-spell a descendant has been planned, so the eliminated rendering is
    /// the one the `assume`'s own bridge recomputes.
    pub(super) fn confine_certified_let_assumes(&self, proof: &Proof) {
        let planned = self.plan_certified_let_assumes(proof);
        if planned.is_empty() {
            return;
        }
        let mut renderings = self.let_bridge_renderings.borrow_mut();
        let mut wire = self.wire_term_overrides.borrow_mut();
        for (term, eliminated) in planned {
            renderings.insert(term, eliminated);
            // The eliminated rendering is what every step prints, so the wire
            // rules judge that text too.
            if let Some(wire) = wire.as_mut() {
                wire.remove(&term);
            }
        }
        drop((renderings, wire));
        // A rendering cached while planning read the authored spelling.
        self.format_cache.borrow_mut().clear();
    }

    /// The producer's table as every step OTHER than a confined `let` assume
    /// prints it, planned as the exporter plans; see
    /// [`crate::term_overrides_outside_confined_let_assumes`].
    pub(crate) fn overrides_outside_confined_let_assumes(
        self,
        proof: &Proof,
    ) -> Result<Option<HashMap<TermId, String>>, AlethePrintError> {
        let Some(overrides) = self.term_overrides else {
            return Ok(None);
        };
        self.plan_equivalent_authored_assumes(proof)?;
        self.plan_folded_and_assumes(proof);
        let confined: HashSet<TermId> = self
            .plan_certified_let_assumes(proof)
            .into_iter()
            .map(|(term, _)| term)
            .collect();
        Ok(Some(
            overrides
                .iter()
                .filter(|(term, _)| !confined.contains(*term))
                .map(|(term, surface)| (*term, surface.clone()))
                .collect(),
        ))
    }

    /// Every assumed term whose authored spelling is a `let` the bridge
    /// eliminates on its certified arm, with its eliminated rendering. Reads
    /// the channels, writes nothing: the rendering must be computed against
    /// the untouched state.
    fn plan_certified_let_assumes(&self, proof: &Proof) -> Vec<(TermId, String)> {
        let Some(overrides) = self.term_overrides else {
            return Vec::new();
        };
        if overrides.is_empty() {
            return Vec::new();
        }
        // An instance a `forall_inst` concludes must print as the quantifier
        // body substituted, `let` and all: that channel is
        // `confined_forall_instance.rs`'s, never this one's.
        let instances: HashSet<TermId> = proof
            .steps
            .iter()
            .filter_map(|step| match step {
                ProofStep::Step {
                    rule: AletheRule::ForallInst,
                    clause,
                    ..
                } => Some(clause.iter().copied()),
                _ => None,
            })
            .flatten()
            .collect();
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut planned: Vec<(TermId, String)> = Vec::new();
        for step in &proof.steps {
            let ProofStep::Assume(term) = step else {
                continue;
            };
            if planned.len() >= MAX_CONFINED_LET_ASSUMES {
                break;
            }
            if !seen.insert(*term) || instances.contains(term) {
                continue;
            }
            let Some(surface) = overrides.get(term) else {
                continue;
            };
            if !surface.starts_with("(let") || self.spelling_has_another_channel(*term) {
                continue;
            }
            let Some(plan) = self.plan_let_assume_bridge(*term, surface) else {
                continue;
            };
            if plan.is_certified() {
                planned.push((*term, plan.eliminated));
            }
        }
        // A term with another planned term strictly below it rendered that one
        // through its AUTHORED text just now, which stops printing once it is
        // confined. So the outer term's certification depends on the inner
        // term keeping its authored text, and so does every producer screen
        // that recomputes it from the wire view (`proof_has_known_wire_gap`):
        // the WHOLE nested group keeps its old, document-wide reading.
        if planned.len() > 1 {
            let roots: HashSet<TermId> = planned.iter().map(|(term, _)| *term).collect();
            let Some(nested) = self.nested_let_roots(&roots) else {
                return Vec::new();
            };
            planned.retain(|(term, _)| !nested.contains(term));
        }
        planned
    }

    /// Every root of `roots` with another root strictly below it, and every
    /// root strictly below one: the nested groups. `None` past the walk bound,
    /// which keeps the caller conservative.
    ///
    /// Linear in the roots' shared DAG: one memoized walk decides, for every
    /// term below a root, whether a root occurs at or below it; a second walk
    /// collects the inner roots, descending only where the first found one.
    fn nested_let_roots(&self, roots: &HashSet<TermId>) -> Option<HashSet<TermId>> {
        let mut reaches: HashMap<TermId, bool> = HashMap::default();
        let mut walked = 0usize;
        let mut outers: Vec<TermId> = Vec::new();
        for &root in roots {
            let mut nests = false;
            for child in self.terms.children(root) {
                nests |= self.reaches_a_root(child, roots, &mut reaches, &mut walked)?;
            }
            if nests {
                outers.push(root);
            }
        }
        let mut nested: HashSet<TermId> = outers.iter().copied().collect();
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = Vec::new();
        for outer in outers {
            stack.extend(self.terms.children(outer));
        }
        while let Some(term) = stack.pop() {
            if !reaches.get(&term).copied().unwrap_or(true) || !seen.insert(term) {
                continue;
            }
            if roots.contains(&term) {
                nested.insert(term);
            }
            stack.extend(self.terms.children(term));
        }
        Some(nested)
    }

    /// Whether a term of `roots` occurs at or below `start`, memoized in
    /// `reaches`; `None` once `walked` passes the caller's bound.
    fn reaches_a_root(
        &self,
        start: TermId,
        roots: &HashSet<TermId>,
        reaches: &mut HashMap<TermId, bool>,
        walked: &mut usize,
    ) -> Option<bool> {
        let mut stack = vec![(start, false)];
        while let Some((term, expanded)) = stack.pop() {
            if reaches.contains_key(&term) {
                continue;
            }
            let children = self.terms.children(term);
            if expanded {
                let hit = roots.contains(&term)
                    || children
                        .iter()
                        .any(|child| reaches.get(child) == Some(&true));
                reaches.insert(term, hit);
                continue;
            }
            *walked += 1;
            if *walked > MAX_NESTING_WALK_TERMS {
                return None;
            }
            stack.push((term, true));
            stack.extend(
                children
                    .into_iter()
                    .filter(|child| !reaches.contains_key(child))
                    .map(|child| (child, false)),
            );
        }
        reaches.get(&start).copied()
    }

    /// Whether a channel other than the producer's table already decides how
    /// `term` prints.
    fn spelling_has_another_channel(&self, term: TermId) -> bool {
        self.let_bridge_renderings.borrow().contains_key(&term)
            || self.skolem_overrides.borrow().contains_key(&term)
            || self.assume_only_override_terms.borrow().contains(&term)
            || self.authored_assume_surfaces.borrow().contains_key(&term)
            || self.folded_assume_surfaces.borrow().contains_key(&term)
    }
}

#[cfg(test)]
#[path = "let_assume_confinement_tests.rs"]
mod tests;
