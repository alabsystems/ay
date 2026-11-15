// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Confine an authored `forall_inst` instance spelling to its own step.
//!
//! `forall_inst` is syntactic: pinned carcara substitutes the printed `:args`
//! into the printed body of the AUTHORED quantifier and compares the result
//! with the printed instance. So the producer spells the instance TermId with
//! the substituted authored body (`(=> (bvult k (len v)) (= (select (data v)
//! k) (f true x)))`), while AY's internal instance is the elaborated
//! `(or (= (f true x) (select (data v) k)) (not (bvult k (len v))))`. That
//! override is document-wide, so every LATER step that consumes the instance
//! (`cong`, `and_pos`, `or`, resolution against a canonical clause) prints the
//! authored text against canonical operands, and the printer refuses the
//! whole export: `surface rewriting gives the two congruence applications
//! different operators ('=>' and 'or')`, or `and_pos indexed conjunct is absent
//! from its effective source`.
//!
//! This pass keeps the authored instance ONLY inside the `forall_inst`
//! command and derives the canonical instance right there:
//!
//! ```text
//! (step tK.fi (cl (or (not Q) S)) :rule forall_inst :args (..))
//! ... tK.n  (cl (= S C))                       ; surface_equivalence
//! (step tK.c (cl (= (or (not Q) S) (or (not Q) C))) :rule cong :premises (tK.n))
//! (step tK.e (cl (not (= ..)) (not (or (not Q) S)) (or (not Q) C)) :rule equiv_pos2)
//! (step tK (cl (or (not Q) C)) :rule resolution :premises (tK.e tK.c tK.fi))
//! ```
//!
//! Every later step then prints the canonical instance `C`, which is what its
//! own internal clause says. An instance is confined only when EVERY
//! `forall_inst` producing it has a checked bridge and the authored literal
//! passes the printed `forall_inst` judgement; otherwise nothing changes.
//!
//! The plan is made LAST in `prepare_proof`, once every Skolem witness has its
//! final `choice` spelling. An instance at a witness (`forall_inst :args
//! (sk!j)`) has a producer spelling that names the witness's internal symbol,
//! which `respell_renderings_naming_witnesses` copies into the printer's own
//! table in `choice` form. At c57bd8481 (and until this change) the plan ran
//! before Skolem preparation: it planned texts naming the raw symbol, the drift check at the
//! step declined them, and the copied authored equality stayed the instance's
//! text document-wide. The `u64`-guarded frame fixture
//! (`carcara_external_check/frame_ite_lift.rs`) then holed both `ite`
//! projections of its witness instance, because their premise printed as that
//! equality rather than the `ite` they were verified over. Such a copied entry
//! is now the authored surface the plan confines, and a successful plan drops
//! it, so the canonical rendering reaches every later step.
//!
//! For a proof with no certified Skolem step and no array-extensionality
//! witness, Skolem preparation installs nothing, so the plan reads exactly the
//! channels it read in its earlier position. Every other plan now reads the
//! spellings the document actually prints; a plan whose text a later channel
//! still contradicts is declined by the drift check below, and every command
//! it ships is judged over its bytes, so the move can cost a hole, never
//! validity.

use super::quantifier_surface::printed_forall_inst_holds;
use super::*;

/// The planned rendering of one `forall_inst` step whose instance is confined.
pub(super) struct ConfinedForallInstance {
    authored_literal: String,
    canonical_literal: String,
    args: Vec<String>,
    /// Steps concluding `(= S C)` under `tK.n`.
    equivalence: Vec<String>,
}

struct InstanceSite {
    id: ProofId,
    literal: TermId,
    negated_quantifier: TermId,
    args: Vec<TermId>,
}

impl AlethePrinter<'_> {
    /// Plan every confinable instance before any step is emitted. Runs after
    /// the authored-assume planner, whose channels take precedence, and after
    /// Skolem preparation; `respelled` is the set of producer entries
    /// `respell_renderings_naming_witnesses` copied into `skolem_overrides`.
    pub(super) fn plan_confined_forall_instances(
        &self,
        proof: &Proof,
        respelled: &HashSet<TermId>,
    ) {
        let Some(overrides) = self.term_overrides else {
            return;
        };
        if overrides.is_empty() {
            return;
        }
        let assumed: HashSet<TermId> = proof
            .steps
            .iter()
            .filter_map(|step| match step {
                ProofStep::Assume(term) => Some(*term),
                _ => None,
            })
            .collect();
        let mut sites: HashMap<TermId, Vec<InstanceSite>> = HashMap::default();
        for (index, step) in proof.steps.iter().enumerate() {
            let ProofStep::Step {
                rule: ay_core::AletheRule::ForallInst,
                clause,
                args,
                ..
            } = step
            else {
                continue;
            };
            let [literal] = clause.as_slice() else {
                continue;
            };
            let TermData::App(Symbol::Named(head), parts) = self.terms.get(*literal) else {
                continue;
            };
            let [negated_quantifier, instance] = parts.as_slice() else {
                continue;
            };
            // The step's own literal is the one parent this pass re-spells;
            // any OTHER overridden ancestor would keep the authored text.
            if head != "or" || !overrides.contains_key(instance) || overrides.contains_key(literal)
            {
                continue;
            }
            sites.entry(*instance).or_default().push(InstanceSite {
                id: ProofId(index as u32),
                literal: *literal,
                negated_quantifier: *negated_quantifier,
                args: args.clone(),
            });
        }
        if sites.is_empty() {
            return;
        }
        let Some(override_descendants) = self.strict_descendants_of_overridden_terms() else {
            return;
        };
        let mut planned: Vec<(TermId, String, Vec<(ProofId, ConfinedForallInstance)>)> = Vec::new();
        for (instance, sites) in sites {
            if let Some((canonical, plans)) = self.plan_confined_instance(
                instance,
                &sites,
                overrides,
                &assumed,
                &override_descendants,
                respelled.contains(&instance),
            ) {
                planned.push((instance, canonical, plans));
            }
        }
        if planned.is_empty() {
            return;
        }
        for (instance, canonical, plans) in planned {
            if respelled.contains(&instance) {
                self.skolem_overrides.borrow_mut().remove(&instance);
            }
            self.let_bridge_renderings
                .borrow_mut()
                .insert(instance, canonical);
            if let Some(wire) = self.wire_term_overrides.borrow_mut().as_mut() {
                wire.remove(&instance);
            }
            self.confined_forall_instances.borrow_mut().extend(plans);
        }
        // A cached rendering of a term ABOVE a confined instance still spells
        // the authored text; drop the memo so every later rendering reads the
        // confined channel.
        self.format_cache.borrow_mut().clear();
    }

    fn plan_confined_instance(
        &self,
        instance: TermId,
        sites: &[InstanceSite],
        overrides: &HashMap<TermId, String>,
        assumed: &HashSet<TermId>,
        override_descendants: &HashSet<TermId>,
        respelled: bool,
    ) -> Option<(String, Vec<(ProofId, ConfinedForallInstance)>)> {
        // An assumed instance, or one another channel already re-spells,
        // keeps that channel. A respelled entry IS the producer's spelling.
        if assumed.contains(&instance)
            || override_descendants.contains(&instance)
            || self.let_bridge_renderings.borrow().contains_key(&instance)
            || (!respelled && self.skolem_overrides.borrow().contains_key(&instance))
            || self.assume_only_override_terms.borrow().contains(&instance)
            || self
                .authored_assume_surfaces
                .borrow()
                .contains_key(&instance)
            || self.folded_assume_surfaces.borrow().contains_key(&instance)
        {
            return None;
        }
        let (surface, canonical) = if respelled {
            let surface = self.skolem_overrides.borrow().get(&instance)?.clone();
            (surface, self.format_term_structurally(instance))
        } else {
            let surface = overrides.get(&instance)?.clone();
            (surface, self.format_term_without_own_override(instance)?)
        };
        if canonical == surface {
            return None;
        }
        let surface = &surface;
        let mut plans = Vec::with_capacity(sites.len());
        for site in sites {
            if overrides.contains_key(&site.literal)
                || self.skolem_overrides.borrow().contains_key(&site.literal)
            {
                return None;
            }
            let quantifier = self.format_term(site.negated_quantifier);
            let authored_literal = format!("(or {quantifier} {surface})");
            let canonical_literal = format!("(or {quantifier} {canonical})");
            let args: Vec<String> = site.args.iter().map(|&arg| self.format_term(arg)).collect();
            let borrowed: Vec<&str> = args.iter().map(String::as_str).collect();
            if !printed_forall_inst_holds(&authored_literal, &borrowed) {
                return None;
            }
            let (equivalence, _) = self.printed_surface_equivalence_steps(
                &format!("{}.n", site.id),
                surface,
                instance,
                &canonical,
            )?;
            plans.push((
                site.id,
                ConfinedForallInstance {
                    authored_literal,
                    canonical_literal,
                    args,
                    equivalence,
                },
            ));
        }
        Some((canonical, plans))
    }

    /// The confined rendering of `id`, or `None` for an unplanned step.
    ///
    /// Re-checks that the document now prints the step's own literal as the
    /// planned canonical text; a drift declines to the ordinary path, whose
    /// printed `forall_inst` judgement then holes the step.
    pub(super) fn format_confined_forall_inst(
        &self,
        id: ProofId,
        clause: &[TermId],
    ) -> Option<String> {
        let plans = self.confined_forall_instances.borrow();
        let plan = plans.get(&id)?;
        let [literal] = clause else {
            return None;
        };
        if self.format_term(*literal) != plan.canonical_literal {
            return None;
        }
        let ConfinedForallInstance {
            authored_literal,
            canonical_literal,
            args,
            equivalence,
        } = plan;
        let equality = format!("(= {authored_literal} {canonical_literal})");
        let mut output = format!(
            "(step {id}.fi (cl {authored_literal}) :rule forall_inst :args ({}))\n",
            args.join(" ")
        );
        for step in equivalence {
            output.push_str(step);
            output.push('\n');
        }
        output.push_str(&format!(
            "(step {id}.c (cl {equality}) :rule cong :premises ({id}.n))\n\
             (step {id}.e (cl (not {equality}) (not {authored_literal}) {canonical_literal}) :rule equiv_pos2)\n\
             (step {id} (cl {canonical_literal}) :rule resolution :premises ({id}.e {id}.c {id}.fi))"
        ));
        self.charge(output.len() as u64);
        Some(output)
    }
}

#[cfg(test)]
mod tests;
