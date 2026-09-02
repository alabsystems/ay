// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checked use-site bridges for exact authored assumption spellings.
//!
//! A source assertion can elaborate to an equivalent canonical term whose
//! Alethe text differs (`(>= t 0)` becomes `(<= 0 t)`, or `(* 4 a)` is stored
//! as `(* a 4)`). Carcara matches `assume` against the problem syntactically,
//! while later resolution must consume the canonical clause. A document-wide
//! override satisfies only one side of that boundary. This module confines the
//! exact source text to `tK.a`, proves source=canonical with checked stock
//! rules, and restores the original proof id `tK` as the canonical unit.

use super::{split_application, AlethePrintError, AlethePrinter};
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{Proof, ProofId, ProofStep, Sort, TermData, TermId};

mod bounds;
mod equivalence;

use bounds::{
    account_authored_assume_emission, account_authored_assume_planning_input,
    canonical_term_is_bounded_for_authored_assume, invalid_authored_assume_plan,
    CanonicalRenderBound,
};

pub(super) const MAX_AUTHORED_ASSUME_BRIDGES: usize = 8_192;
const MAX_EQUIVALENCE_DEPTH: usize = 64;
const MAX_EQUIVALENCE_NODES: usize = 256;
pub(super) const MAX_EQUIVALENCE_BYTES: usize = 64 * 1024;
pub(super) const MAX_EQUIVALENCE_TOTAL_INPUT_BYTES: usize = 8 * 1024 * 1024;
const MAX_EQUIVALENCE_TOTAL_NODES: usize = 64 * 1024;
const MAX_EQUIVALENCE_TOTAL_OUTPUT_BYTES: usize = 32 * 1024 * 1024;
const MAX_CANONICAL_RENDER_NODES: usize = 8 * 1024;
const MAX_AUTHORED_ASSUME_PLANNER_STEPS: usize = 1_000_000;

#[derive(Clone, Copy)]
enum EquivalenceLeafSchema {
    AuthoredAssume,
    MultiplicationOnly,
}

#[derive(Clone, Copy)]
pub(super) enum EquivalenceDirection {
    SurfaceToCanonical,
    CanonicalToSurface,
}

fn oriented_equivalence(surface: &str, canonical: &str, direction: EquivalenceDirection) -> String {
    match direction {
        EquivalenceDirection::SurfaceToCanonical => format!("(= {surface} {canonical})"),
        EquivalenceDirection::CanonicalToSurface => format!("(= {canonical} {surface})"),
    }
}

struct AuthoredAssumePlan {
    surface: String,
    canonical: String,
    input_bytes: usize,
    bridge: AuthoredAssumeBridge,
}

#[derive(Clone, Copy)]
enum AuthoredAssumeBridge {
    Equivalence,
    LinearArithmeticImplication,
}

#[derive(Default)]
struct AuthoredAssumeAccounting {
    bridge_count: usize,
    total_input_bytes: usize,
    total_nodes: usize,
    total_output_bytes: usize,
}

#[derive(Default)]
struct AuthoredAssumePlanner {
    planned: HashMap<TermId, AuthoredAssumePlan>,
    unsupported: HashSet<TermId>,
    bridged_ids: HashSet<ProofId>,
    /// Terms with override-bearing `Assume` rows but no consumed row. This is
    /// term-keyed only after the duplicate census has excluded every term for
    /// which even one sibling `Assume` id is consumed.
    assume_only_terms: HashSet<TermId>,
    inspected_terms: usize,
    accounting: AuthoredAssumeAccounting,
}

/// Borrowed admission and exact work charge for cloning the override ledger.
///
/// These are the authored-assume channel's existing published entry, token and
/// aggregate-input limits. Reusing them here keeps the copy envelope identical
/// to the planner that consumes the map. Work charges one unit for each entry
/// in the borrowed scan, one for each entry copied into the owned map, and one
/// per owned rendering byte copied. The caller spends and checks this charge
/// before allocating that map.
pub(super) fn wire_term_override_clone_work_from_lengths(
    entry_count: usize,
    rendering_lengths: impl IntoIterator<Item = usize>,
) -> Result<u64, AlethePrintError> {
    if entry_count > MAX_AUTHORED_ASSUME_BRIDGES {
        return Err(invalid_authored_assume_plan(
            ProofId(0),
            "surface override entry count exceeds the authored assume bound",
        ));
    }
    let mut total_bytes = 0usize;
    let mut observed_entries = 0usize;
    for length in rendering_lengths {
        observed_entries = observed_entries.checked_add(1).ok_or_else(|| {
            invalid_authored_assume_plan(ProofId(0), "surface override entry count overflowed")
        })?;
        if observed_entries > entry_count {
            return Err(invalid_authored_assume_plan(
                ProofId(0),
                "surface override ledger changed during borrowed preflight",
            ));
        }
        if length > MAX_EQUIVALENCE_BYTES {
            return Err(invalid_authored_assume_plan(
                ProofId(0),
                "one surface override exceeds the authored assume input-size bound",
            ));
        }
        total_bytes = total_bytes.checked_add(length).ok_or_else(|| {
            invalid_authored_assume_plan(
                ProofId(0),
                "surface override aggregate input size overflowed",
            )
        })?;
        if total_bytes > MAX_EQUIVALENCE_TOTAL_INPUT_BYTES {
            return Err(invalid_authored_assume_plan(
                ProofId(0),
                "surface overrides exceed the authored assume aggregate input-size bound",
            ));
        }
    }
    if observed_entries != entry_count {
        return Err(invalid_authored_assume_plan(
            ProofId(0),
            "surface override ledger changed during borrowed preflight",
        ));
    }
    let work = entry_count
        .checked_mul(2)
        .and_then(|entries| entries.checked_add(total_bytes))
        .and_then(|work| u64::try_from(work).ok())
        .ok_or_else(|| {
            invalid_authored_assume_plan(ProofId(0), "surface override clone work overflowed")
        })?;
    Ok(work)
}

fn wire_term_override_clone_work(
    overrides: Option<&HashMap<TermId, String>>,
) -> Result<u64, AlethePrintError> {
    let Some(overrides) = overrides else {
        return Ok(0);
    };
    wire_term_override_clone_work_from_lengths(overrides.len(), overrides.values().map(String::len))
}

fn consumed_authored_assume_ids(proof: &Proof) -> Result<Vec<bool>, AlethePrintError> {
    if proof.steps.len() > MAX_AUTHORED_ASSUME_PLANNER_STEPS {
        return Err(invalid_authored_assume_plan(
            ProofId(0),
            "proof step count exceeds the authored assume planner bound",
        ));
    }
    let mut consumed = vec![false; proof.steps.len()];
    for (index, step) in proof.steps.iter().enumerate() {
        let mut mark = |premise: ProofId| -> Result<(), AlethePrintError> {
            let Some(slot) = consumed.get_mut(premise.0 as usize) else {
                return Err(invalid_authored_assume_plan(
                    ProofId(index as u32),
                    "proof step references an out-of-range premise in authored assume planner",
                ));
            };
            *slot = true;
            Ok(())
        };
        match step {
            ProofStep::Step { premises, .. } => {
                for &premise in premises {
                    mark(premise)?;
                }
            }
            ProofStep::Resolution {
                clause1, clause2, ..
            } => {
                mark(*clause1)?;
                mark(*clause2)?;
            }
            ProofStep::Anchor { end_step, .. } => mark(*end_step)?,
            ProofStep::Assume(_) | ProofStep::TheoryLemma { .. } => {}
            _ => {
                return Err(invalid_authored_assume_plan(
                    ProofId(index as u32),
                    "unrecognized proof-step dependency shape in authored assume planner",
                ));
            }
        }
    }
    Ok(consumed)
}

impl AlethePrinter<'_> {
    /// Initialize the downstream wire-rule view only after its complete source
    /// map is admitted and its scan/copy work fits the caller's emission budget.
    /// No owned override string is duplicated on a declining path.
    pub(super) fn initialize_wire_term_overrides(&self) -> Result<(), AlethePrintError> {
        if self.wire_term_overrides_initialized.get() {
            return Ok(());
        }
        let clone_work = wire_term_override_clone_work(self.term_overrides)?;
        self.charge(clone_work);
        if self.work_budget_exhausted() {
            return Err(self.work_budget_error(0));
        }
        // Do not use `HashMap::clone`: hashbrown preserves the source table's
        // bucket count, so a tiny but heavily over-reserved caller map could
        // duplicate an allocation far beyond the admitted entry/byte bounds.
        // Entry-wise collection sizes the owned table from the admitted len.
        let cloned = self.term_overrides.map(|overrides| {
            overrides
                .iter()
                .map(|(term, rendering)| (*term, rendering.clone()))
                .collect()
        });
        *self.wire_term_overrides.borrow_mut() = cloned;
        self.wire_term_overrides_initialized.set(true);
        Ok(())
    }

    /// Materialize exactly the bridge `format_step` would emit for one proof
    /// id. The planner uses the returned byte length and node count, so id
    /// length, premise lists, and duplicate rows are accounted byte-for-byte
    /// rather than through a shared per-term estimate.
    fn render_authored_assume_bridge(
        &self,
        id: ProofId,
        term: TermId,
        surface: &str,
        canonical: &str,
        bridge: AuthoredAssumeBridge,
    ) -> (Option<String>, usize) {
        if matches!(bridge, AuthoredAssumeBridge::LinearArithmeticImplication) {
            if !crate::printed_la_generic_unit_implication_is_supported(surface, canonical) {
                return (None, 1);
            }
            let output = format!(
                "(assume {id}.a {surface})\n\
                 (step {id}.n (cl (not {surface}) {canonical}) :rule la_generic :args (1 1))\n\
                 (step {id} (cl {canonical}) :rule resolution :premises ({id}.n {id}.a))"
            );
            return (Some(output), 1);
        }
        let mut equality_steps = Vec::new();
        let mut nodes = 0;
        let equality_id = format!("{id}.n");
        if !self.build_authored_surface_equivalence(
            &equality_id,
            surface,
            term,
            EquivalenceLeafSchema::AuthoredAssume,
            EquivalenceDirection::SurfaceToCanonical,
            0,
            &mut nodes,
            &mut equality_steps,
        ) {
            return (None, nodes);
        }
        let equality = format!("(= {surface} {canonical})");
        let mut output = format!("(assume {id}.a {surface})\n");
        output.push_str(&equality_steps.join("\n"));
        output.push('\n');
        output.push_str(&format!(
            "(step {id}.e (cl (not {equality}) (not {surface}) {canonical}) :rule equiv_pos2)\n\
             (step {id} (cl {canonical}) :rule resolution :premises ({id}.e {equality_id} {id}.a))"
        ));
        (Some(output), nodes)
    }

    /// Charge the planner's exact dry run and the later emitted bridge for one
    /// consumed assume id. Returns `false` only for a source/canonical pair
    /// outside the supported checked equivalence schemas.
    fn plan_authored_assume_use(
        &self,
        id: ProofId,
        term: TermId,
        plan: &AuthoredAssumePlan,
        accounting: &mut AuthoredAssumeAccounting,
    ) -> Result<bool, AlethePrintError> {
        account_authored_assume_planning_input(id, plan.input_bytes, accounting)?;

        let (rendered, nodes) = self.render_authored_assume_bridge(
            id,
            term,
            &plan.surface,
            &plan.canonical,
            plan.bridge,
        );
        let Some(planning_nodes) = accounting.total_nodes.checked_add(nodes) else {
            return Err(invalid_authored_assume_plan(
                id,
                "authored assume bridge node accounting overflowed",
            ));
        };
        if planning_nodes > MAX_EQUIVALENCE_TOTAL_NODES {
            return Err(invalid_authored_assume_plan(
                id,
                "authored assume bridges exceed the aggregate node bound",
            ));
        }
        accounting.total_nodes = planning_nodes;
        let Some(rendered) = rendered else {
            return Ok(false);
        };
        let output_bytes = rendered.len();
        let Some(planning_output_bytes) = accounting.total_output_bytes.checked_add(output_bytes)
        else {
            return Err(invalid_authored_assume_plan(
                id,
                "authored assume bridge aggregate output size overflowed",
            ));
        };
        if planning_output_bytes > MAX_EQUIVALENCE_TOTAL_OUTPUT_BYTES {
            return Err(invalid_authored_assume_plan(
                id,
                "authored assume bridges exceed the aggregate output-size bound",
            ));
        }
        accounting.total_output_bytes = planning_output_bytes;
        account_authored_assume_emission(id, plan, nodes, output_bytes, accounting)?;
        Ok(true)
    }

    fn plan_new_authored_assume_term(
        &self,
        id: ProofId,
        term: TermId,
        surface: &str,
        planner: &mut AuthoredAssumePlanner,
    ) -> Result<Option<AuthoredAssumePlan>, AlethePrintError> {
        let Some(next_inspected) = planner.inspected_terms.checked_add(1) else {
            return Err(invalid_authored_assume_plan(
                id,
                "authored assume inspected-term count overflowed",
            ));
        };
        if next_inspected > MAX_AUTHORED_ASSUME_BRIDGES {
            return Err(invalid_authored_assume_plan(
                id,
                "authored assume inspected-term count exceeds the planner bound",
            ));
        }
        planner.inspected_terms = next_inspected;
        if !matches!(self.terms.sort(term), Sort::Bool) {
            return Err(invalid_authored_assume_plan(
                id,
                "an authored assume bridge root is not Boolean",
            ));
        }
        match canonical_term_is_bounded_for_authored_assume(self.terms, term) {
            CanonicalRenderBound::Bounded => {}
            // A binder, a `let` or an internal constant array is a schema this
            // lane never renders. Decline the bridge exactly the way every
            // other unsupported schema does (`plan_authored_assume_use` ->
            // `Ok(false)` -> `planner.unsupported`): the assume keeps printing
            // through the ordinary override channel and stays subject to the
            // fail-closed surface validators. Escalating it killed the whole
            // document over one quantified assertion.
            CanonicalRenderBound::UnsupportedShape => return Ok(None),
            CanonicalRenderBound::ExceedsBound => {
                return Err(invalid_authored_assume_plan(
                    id,
                    "authored assume canonical term exceeds the structural rendering bound",
                ))
            }
        }
        let canonical = crate::render_term_canonical(self.terms, term);
        let Some(input_bytes) = surface.len().checked_add(canonical.len()) else {
            return Err(invalid_authored_assume_plan(
                id,
                "authored assume bridge input size overflowed",
            ));
        };
        if input_bytes > MAX_EQUIVALENCE_BYTES {
            return Err(invalid_authored_assume_plan(
                id,
                "one authored assume bridge exceeds the input-size bound",
            ));
        }
        if surface == canonical {
            account_authored_assume_planning_input(id, input_bytes, &mut planner.accounting)?;
            return Ok(None);
        }
        let mut probe_steps = Vec::new();
        let mut probe_nodes = 0;
        let bridge = if self.build_authored_surface_equivalence(
            "probe",
            surface,
            term,
            EquivalenceLeafSchema::AuthoredAssume,
            EquivalenceDirection::SurfaceToCanonical,
            0,
            &mut probe_nodes,
            &mut probe_steps,
        ) {
            AuthoredAssumeBridge::Equivalence
        } else if crate::printed_la_generic_unit_implication_is_supported(surface, &canonical) {
            AuthoredAssumeBridge::LinearArithmeticImplication
        } else {
            account_authored_assume_planning_input(id, input_bytes, &mut planner.accounting)?;
            return Ok(None);
        };
        let plan = AuthoredAssumePlan {
            surface: surface.to_string(),
            canonical,
            input_bytes,
            bridge,
        };
        if !self.plan_authored_assume_use(id, term, &plan, &mut planner.accounting)? {
            return Ok(None);
        }
        Ok(Some(plan))
    }

    fn plan_one_authored_assume_id(
        &self,
        id: ProofId,
        term: TermId,
        surface: &str,
        planner: &mut AuthoredAssumePlanner,
    ) -> Result<(), AlethePrintError> {
        if planner.accounting.bridge_count >= MAX_AUTHORED_ASSUME_BRIDGES {
            return Err(invalid_authored_assume_plan(
                id,
                "authored assume bridge count exceeds the planner bound",
            ));
        }
        if let Some(plan) = planner.planned.get(&term) {
            if !self.plan_authored_assume_use(id, term, plan, &mut planner.accounting)? {
                return Err(invalid_authored_assume_plan(
                    id,
                    "planned authored assume equivalence lost its checked derivation",
                ));
            }
            planner.bridged_ids.insert(id);
            return Ok(());
        }
        if planner.unsupported.contains(&term) {
            return Ok(());
        }
        let Some(plan) = self.plan_new_authored_assume_term(id, term, surface, planner)? else {
            planner.unsupported.insert(term);
            return Ok(());
        };
        planner.bridged_ids.insert(id);
        planner.planned.insert(term, plan);
        Ok(())
    }

    fn commit_authored_assume_plan(
        &self,
        proof_step_count: usize,
        planner: AuthoredAssumePlanner,
    ) -> Result<(), AlethePrintError> {
        let accounting = &planner.accounting;
        let Some(total_charge) = proof_step_count
            .checked_mul(2)
            .and_then(|work| work.checked_add(accounting.total_input_bytes))
            .and_then(|work| {
                accounting
                    .total_nodes
                    .checked_mul(32)
                    .and_then(|node_work| work.checked_add(node_work))
            })
            .and_then(|work| work.checked_add(accounting.total_output_bytes))
            .and_then(|work| u64::try_from(work).ok())
        else {
            return Err(invalid_authored_assume_plan(
                ProofId(0),
                "authored assume planner work accounting overflowed",
            ));
        };
        self.charge(total_charge);
        if self.work_budget_exhausted() {
            return Err(self.work_budget_error(0));
        }

        let mut canonical_renderings = self.let_bridge_renderings.borrow_mut();
        let mut surfaces = self.authored_assume_surfaces.borrow_mut();
        let mut bridged = self.authored_assume_bridged.borrow_mut();
        let mut assume_only = self.assume_only_override_terms.borrow_mut();
        let mut linear_arithmetic_bridges = self.linear_arithmetic_assume_bridges.borrow_mut();
        if planner.planned.keys().any(|term| {
            canonical_renderings.contains_key(term)
                || surfaces.contains_key(term)
                || self.folded_assume_surfaces.borrow().contains_key(term)
        }) || planner.assume_only_terms.iter().any(|term| {
            planner.planned.contains_key(term)
                || canonical_renderings.contains_key(term)
                || surfaces.contains_key(term)
                || self.folded_assume_surfaces.borrow().contains_key(term)
        }) || !bridged.is_empty()
            || !assume_only.is_empty()
        {
            return Err(invalid_authored_assume_plan(
                ProofId(0),
                "authored assume bridge conflicts with another assume rendering channel",
            ));
        }
        for (term, plan) in planner.planned {
            if let Some(overrides) = self.wire_term_overrides.borrow_mut().as_mut() {
                overrides.remove(&term);
            }
            if matches!(
                plan.bridge,
                AuthoredAssumeBridge::LinearArithmeticImplication
            ) {
                linear_arithmetic_bridges.insert(term);
            }
            canonical_renderings.insert(term, plan.canonical);
            surfaces.insert(term, plan.surface);
        }
        if let Some(overrides) = self.wire_term_overrides.borrow_mut().as_mut() {
            for term in &planner.assume_only_terms {
                overrides.remove(term);
            }
        }
        *assume_only = planner.assume_only_terms;
        *bridged = planner.bridged_ids;
        Ok(())
    }

    /// Atomically confine source spellings to the assumptions that need them.
    ///
    /// Every admitted source-to-canonical step is independently expressible
    /// through `comp_simplify`, binary numeric-multiplication `aci_simp`, and
    /// `cong`, or through the exact two-row arithmetic implication checked by
    /// [`crate::printed_la_generic_unit_implication_is_supported`]. Anything
    /// else is left to the existing fail-closed surface validators when a
    /// consumed assumption makes a bridge necessary. If every override-bearing
    /// `Assume` id for a term is unused, no bridge is owed: the source spelling
    /// is emitted only at those leaves and the canonical term is rendered at
    /// every downstream occurrence. A single consumed duplicate keeps the
    /// whole term out of this bridge-free channel.
    pub(super) fn plan_equivalent_authored_assumes(
        &self,
        proof: &Proof,
    ) -> Result<(), AlethePrintError> {
        self.initialize_wire_term_overrides()?;
        let Some(overrides) = self.term_overrides else {
            return Ok(());
        };
        if overrides.is_empty() {
            return Ok(());
        }
        let consumed = consumed_authored_assume_ids(proof)?;
        let mut planner = AuthoredAssumePlanner::default();
        let mut consumed_override_terms = HashSet::default();
        for (index, step) in proof.steps.iter().enumerate() {
            let ProofStep::Assume(term) = step else {
                continue;
            };
            let Some(surface) = overrides.get(term) else {
                continue;
            };
            if consumed[index] {
                consumed_override_terms.insert(*term);
                self.plan_one_authored_assume_id(
                    ProofId(index as u32),
                    *term,
                    surface,
                    &mut planner,
                )?;
            } else {
                planner.assume_only_terms.insert(*term);
            }
        }
        planner
            .assume_only_terms
            .retain(|term| !consumed_override_terms.contains(term));
        self.commit_authored_assume_plan(proof.steps.len(), planner)
    }

    pub(super) fn format_equivalent_authored_assume_bridge(
        &self,
        id: ProofId,
        term: TermId,
    ) -> Result<Option<String>, AlethePrintError> {
        if self.assume_only_override_terms.borrow().contains(&term) {
            let Some(surface) = self
                .term_overrides
                .and_then(|overrides| overrides.get(&term))
            else {
                return Err(AlethePrintError::InvalidSurfaceStep {
                    id,
                    reason: "assume-only override lost its authored rendering".to_string(),
                });
            };
            return Ok(Some(format!("(assume {id} {surface})")));
        }
        let Some(surface) = self.authored_assume_surfaces.borrow().get(&term).cloned() else {
            return Ok(None);
        };
        if !self.authored_assume_bridged.borrow().contains(&id) {
            return Ok(Some(format!("(assume {id} {surface})")));
        }
        let Some(canonical) = self.let_bridge_renderings.borrow().get(&term).cloned() else {
            return Err(AlethePrintError::InvalidSurfaceStep {
                id,
                reason: "authored assume bridge lost its canonical rendering".to_string(),
            });
        };
        let bridge = if self
            .linear_arithmetic_assume_bridges
            .borrow()
            .contains(&term)
        {
            AuthoredAssumeBridge::LinearArithmeticImplication
        } else {
            AuthoredAssumeBridge::Equivalence
        };
        let (output, _) =
            self.render_authored_assume_bridge(id, term, &surface, &canonical, bridge);
        let Some(output) = output else {
            return Err(AlethePrintError::InvalidSurfaceStep {
                id,
                reason: "planned authored assume equivalence no longer has a checked derivation"
                    .to_string(),
            });
        };
        Ok(Some(output))
    }
}
