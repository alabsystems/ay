// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Whole-authored fallback for native clauses containing private EqDiffVars.
//!
//! An EqDiffVar may occur in the native packed clause without any checkable
//! Alethe declaration.  Such a symbol must not be weakened into an exported
//! proof.  Instead, this module retains only structurally mapped source
//! literals, discharges every unused source equality exactly, and closes the
//! remaining arithmetic literals from a bounded subset of authenticated raw
//! authored problem facts.

use ay_core::kani_compat::DetHashMap;
use ay_core::{
    AletheRule, FarkasAnnotation, Proof, ProofId, ProofStep, Sort, Symbol, TermData, TermId,
    TheoryLemmaKind,
};

use super::eq_plan::{
    collect_definitions, emit_eq_plan, plan_numeric_equality, Definition, EqBudget, EqPlan,
};
use super::{emit_literal_bridge, BridgeAuthority, Executor, SourcePlan};

pub(super) const MAX_DIRECT_FACTS: usize = 16;
const MAX_DIRECT_AUTHORITY_TERMS: usize = 128;
const MAX_DIRECT_COMBINED_SCOPE: usize = 288;
const MAX_LINEAR_SUPPORT: usize = 2;
const MAX_LINEAR_ATTEMPTS: u16 = 256;
const MAX_DIRECT_STEPS: usize = 4_096;
const MAX_DIRECT_EQUALITY_EMITTED_STEPS: usize = 128;
const MAX_POSITIVE_UNIT_EMITTED_STEPS: usize = MAX_DIRECT_EQUALITY_EMITTED_STEPS;
const MAX_DIRECT_OVERRIDE_ENTRIES: usize = 8_192;
const MAX_DIRECT_OVERRIDE_TOKEN_BYTES: usize = 64 * 1024;
const MAX_DIRECT_OVERRIDE_BYTES: usize = 1024 * 1024;
const MAX_DIRECT_RENDER_WORK: u64 = 4 * 1024 * 1024;

struct LinearUnitPlan {
    facts: Vec<TermId>,
    clause: Vec<TermId>,
    authority: LinearAuthority,
}

enum LinearAuthority {
    Farkas(FarkasAnnotation),
    IntBounds,
}

impl Executor {
    pub(super) fn plan_direct_negated_conjunct_refutation(
        &mut self,
        plan: SourcePlan,
    ) -> Option<Proof> {
        let (authenticated_facts, authority_scope) = self.bounded_direct_refutation_scopes()?;
        // Refuse before `proof_export_term_overrides` clones the source map.
        // A node-bounded arithmetic DAG can still carry arbitrarily large
        // source renderings, so bytes and entry count need their own envelope.
        if !direct_overrides_admitted(self.last_proof_term_overrides.as_ref()) {
            return None;
        }
        let overrides = self.proof_export_term_overrides();
        if !direct_overrides_admitted(overrides.as_ref()) {
            return None;
        }
        // Build the candidate over the authenticated identity terms checked by
        // the internal proof checker. The raw source map can still contain
        // authored spellings used only by an `assume`; applying those
        // spellings to a newly derived Farkas step before candidate-specific
        // authored-assume confinement can falsely make the checked row appear
        // divergent. The mandatory wire screen and exact exporter below both
        // derive the effective map for this candidate and still fail closed on
        // any override that reaches a downstream rule.
        let candidate = emit_direct_refutation(self, plan, &authenticated_facts, None)?;
        let scope =
            ay_proof::validate_reachable_assumes_in_problem_scope(&candidate, &authority_scope);
        let empty = Self::proof_derives_empty_clause(&candidate);
        let strict = self.check_proof_strict_with_datatypes(&candidate);
        let wire = self.proof_has_known_wire_gap(&candidate);
        if scope.is_err() || !empty || !strict.is_ok_and(|quality| quality.is_complete()) || wire {
            return None;
        }
        let rendered = ay_proof::try_export_alethe_with_problem_scope_overrides_and_budget(
            &candidate,
            &self.ctx.terms,
            &authority_scope,
            overrides.as_ref(),
            Some(MAX_DIRECT_RENDER_WORK),
        )
        .ok()?;
        if rendered.contains(":rule hole") || rendered.contains(":rule trust") {
            return None;
        }
        Some(candidate)
    }

    /// Admit the fallback before either broad scope helper allocates.  This
    /// lane is intentionally unavailable without a frozen query provenance:
    /// the fallback must know both the exact authored facts and the exact
    /// external authority scope, and a missing snapshot cannot provide either
    /// inside this fixed resource envelope.
    fn direct_refutation_scope_admitted(&self) -> bool {
        let Some(provenance) = &self.proof_problem_assertion_provenance else {
            return false;
        };
        let assumption_count = self.last_assumptions.as_ref().map_or(0, Vec::len);
        let canonical_fact_count_admitted = provenance
            .original_problem_assertions
            .len()
            .checked_add(assumption_count)
            .is_some_and(|count| count <= MAX_DIRECT_FACTS);
        let raw_fact_count_admitted = self
            .last_proof_raw_original_assertions
            .len()
            .checked_add(assumption_count)
            .is_some_and(|count| count <= MAX_DIRECT_FACTS);
        canonical_fact_count_admitted
            && raw_fact_count_admitted
            && provenance.problem_assertions.len() <= MAX_DIRECT_AUTHORITY_TERMS
            && self.last_proof_rebuild_originals.len() <= MAX_DIRECT_AUTHORITY_TERMS
            && self.last_proof_raw_original_assertions.len() <= MAX_DIRECT_AUTHORITY_TERMS
            && self
                .last_proof_raw_original_assertions
                .iter()
                .all(|root| self.last_proof_rebuild_originals.contains(root))
    }

    /// Clone the two exact authority scopes only after the borrowed ledger
    /// admission above proves their source vectors fit this lane's envelope.
    pub(super) fn bounded_direct_refutation_scopes(&self) -> Option<(Vec<TermId>, Vec<TermId>)> {
        if !self.direct_refutation_scope_admitted() {
            return None;
        }
        // Farkas certificates are orientation-sensitive.  The canonical
        // provenance snapshot may reverse an authored equality while its
        // exporter override restores the source spelling; certifying the
        // former and printing the latter produces a different linear row.
        // Use only the recursively raw, provenance-authenticated source roots
        // (plus exact check-sat-assuming inputs) as numeric authority, so the
        // term checked internally is the term exposed on the wire.
        let mut facts = Vec::with_capacity(MAX_DIRECT_FACTS);
        for &fact in &self.last_proof_raw_original_assertions {
            if !facts.contains(&fact) {
                facts.push(fact);
            }
        }
        if let Some(assumptions) = &self.last_assumptions {
            for &fact in assumptions {
                if !facts.contains(&fact) {
                    facts.push(fact);
                }
            }
        }
        let authority = self.proof_export_scope_assertions();
        if facts.len() > MAX_DIRECT_FACTS
            || authority.len() > MAX_DIRECT_COMBINED_SCOPE
            || !facts.iter().all(|fact| authority.contains(fact))
        {
            return None;
        }
        Some((facts, authority))
    }
}

fn direct_overrides_admitted(overrides: Option<&DetHashMap<TermId, String>>) -> bool {
    let Some(overrides) = overrides else {
        return true;
    };
    if overrides.len() > MAX_DIRECT_OVERRIDE_ENTRIES {
        return false;
    }
    let mut bytes = 0usize;
    for rendering in overrides.values() {
        if rendering.len() > MAX_DIRECT_OVERRIDE_TOKEN_BYTES {
            return false;
        }
        let Some(next) = bytes.checked_add(rendering.len()) else {
            return false;
        };
        if next > MAX_DIRECT_OVERRIDE_BYTES {
            return false;
        }
        bytes = next;
    }
    true
}

pub(super) fn emit_direct_refutation(
    executor: &mut Executor,
    plan: SourcePlan,
    authenticated_facts: &[TermId],
    term_overrides: Option<&DetHashMap<TermId, String>>,
) -> Option<Proof> {
    // The ordinary fragment can be unrenderable even when every goal mapped:
    // a surface override may expose a private preprocessor spelling in one of
    // its intermediate clauses.  `weakened_goals` therefore need not be
    // non-empty.  This whole-authored lane independently closes every mapped
    // goal below and is published only after the strict, provenance, empty-
    // clause, wire-gap, and rendered-hole gates in the caller all pass.
    if authenticated_facts.len() > MAX_DIRECT_FACTS {
        return None;
    }
    let direct_step_upper_bound = plan.common_prefix_step_upper_bound()?.checked_add(
        plan.bridges
            .len()
            .checked_mul(MAX_POSITIVE_UNIT_EMITTED_STEPS.checked_add(1)?)?,
    );
    if !super::emitted_steps_admitted(direct_step_upper_bound, MAX_DIRECT_STEPS) {
        return None;
    }
    let numeric_facts: Vec<TermId> = authenticated_facts
        .iter()
        .copied()
        .filter(|&term| super::decode_relation(&executor.ctx.terms, term).is_some())
        .collect();
    if numeric_facts.is_empty() || numeric_facts.len() > MAX_DIRECT_FACTS {
        return None;
    }
    let mut arithmetic_surfaces = numeric_facts.clone();
    for bridge in &plan.bridges {
        let TermData::Not(atom) = executor.ctx.terms.get(bridge.goal) else {
            return None;
        };
        arithmetic_surfaces.push(*atom);
    }
    if !super::surface_budget::surfaces_admitted(&executor.ctx.terms, &arithmetic_surfaces) {
        return None;
    }

    let mut proof = Proof::new();
    let root = proof.add_assume(plan.root, None);
    let mut assumptions = DetHashMap::default();
    assumptions.insert(plan.root, root);
    let mut running = plan.source_negatives.clone();
    let mut current =
        proof.add_rule_step(AletheRule::NotAnd, running.clone(), vec![root], Vec::new());

    for bridge in &plan.bridges {
        if matches!(&bridge.authority, BridgeAuthority::Direct) {
            continue;
        }
        let bridge_unit = emit_literal_bridge(&mut proof, bridge, &mut assumptions)?;
        let position = running
            .iter()
            .position(|&literal| literal == bridge.source_negative)?;
        let _ = running.remove(position);
        if !running.contains(&bridge.goal) {
            running.push(bridge.goal);
        }
        current = proof.add_resolution(running.clone(), bridge.source_atom, current, bridge_unit);
    }
    for (discharged_index, discharged_equality) in &plan.discharged {
        let discharged = emit_eq_plan(&mut proof, discharged_equality, &mut assumptions)?;
        let atom = discharged_equality.equality();
        let position = running
            .iter()
            .position(|&literal| literal == plan.source_negatives[*discharged_index])?;
        let _ = running.remove(position);
        current = proof.add_resolution(running.clone(), atom, current, discharged);
    }

    let mapped_goals: Vec<TermId> = plan.bridges.iter().map(|bridge| bridge.goal).collect();
    if !super::same_unique_set(&running, &mapped_goals) {
        return None;
    }
    let mut linear_attempts = MAX_LINEAR_ATTEMPTS;
    let definitions = collect_definitions(&executor.ctx.terms, &numeric_facts);
    let mut equality_budget = EqBudget::new(super::EQ_WORK);
    for negative in running.clone() {
        let TermData::Not(atom) = executor.ctx.terms.get(negative) else {
            return None;
        };
        let atom = *atom;
        let positive = if numeric_facts.contains(&atom) {
            Some(assume_once(&mut proof, &mut assumptions, atom))
        } else if arithmetic_equality_operands(executor, atom).is_some() {
            let source_bridge = plan.bridges.iter().find(|bridge| bridge.goal == negative);
            if let Some(unit) = source_bridge.and_then(|bridge| {
                plan_direct_source_equality_unit(
                    executor,
                    bridge,
                    &definitions,
                    &mut equality_budget,
                )
                .and_then(|source_plan| {
                    emit_reverse_equality_bridge_unit(
                        executor,
                        &mut proof,
                        &mut assumptions,
                        bridge,
                        source_plan,
                        atom,
                    )
                })
            }) {
                Some(unit)
            } else if let Some(plan) =
                plan_direct_numeric_equality(executor, &definitions, atom, &mut equality_budget)
            {
                emit_eq_plan(&mut proof, &plan, &mut assumptions)
            } else {
                emit_positive_equality_unit(
                    executor,
                    &mut proof,
                    &mut assumptions,
                    &numeric_facts,
                    atom,
                    &mut linear_attempts,
                    term_overrides,
                )
            }
        } else {
            let plan = plan_positive_unit(executor, &numeric_facts, atom, &mut linear_attempts);
            plan.and_then(|plan| {
                emit_linear_unit_plan(
                    executor,
                    &mut proof,
                    &mut assumptions,
                    plan,
                    atom,
                    term_overrides,
                )
            })
        };
        let positive = positive?;
        let position = running.iter().position(|&literal| literal == negative)?;
        let _ = running.remove(position);
        current = proof.add_resolution(running.clone(), atom, current, positive);
    }
    if !running.is_empty() || proof.steps.len() > MAX_DIRECT_STEPS {
        return None;
    }
    let closes = matches!(
        proof.steps.get(current.0 as usize),
        Some(ProofStep::Resolution { clause, .. })
            | Some(ProofStep::Step { clause, .. }) if clause.is_empty()
    );
    if !closes {
        return None;
    }
    hoist_direct_assumes(proof)
}

pub(super) fn plan_direct_source_equality_unit(
    executor: &mut Executor,
    bridge: &super::LiteralBridge,
    definitions: &[Definition],
    budget: &mut EqBudget,
) -> Option<EqPlan> {
    let (left, right) = arithmetic_equality_operands(executor, bridge.source_atom)?;
    plan_numeric_equality(&mut executor.ctx.terms, left, right, definitions, budget)
}

fn emit_reverse_equality_bridge_unit(
    executor: &mut Executor,
    proof: &mut Proof,
    assumptions: &mut DetHashMap<TermId, ProofId>,
    bridge: &super::LiteralBridge,
    source_plan: EqPlan,
    target_atom: TermId,
) -> Option<ProofId> {
    if bridge.source_atom == target_atom {
        return emit_eq_plan(proof, &source_plan, assumptions);
    }
    let mut clause: Vec<TermId> = bridge
        .equalities
        .iter()
        .map(EqPlan::negated_equality)
        .collect();
    clause.push(bridge.source_negative);
    clause.push(target_atom);
    if !matches!(&bridge.authority, BridgeAuthority::Euf { .. })
        || !ay_proof::recognize_euf_congruent_pred(&executor.ctx.terms, &clause)
    {
        return None;
    }
    let bridge_steps = bridge.equalities.iter().try_fold(2usize, |total, plan| {
        total
            .checked_add(plan.emitted_step_upper_bound()?)?
            .checked_add(1)
    })?;
    let upper_bound = source_plan
        .emitted_step_upper_bound()?
        .checked_add(bridge_steps)?;
    if upper_bound > MAX_DIRECT_EQUALITY_EMITTED_STEPS {
        return None;
    }

    let source_unit = emit_eq_plan(proof, &source_plan, assumptions)?;
    let mut residual = clause.clone();
    let mut current = proof.add_step(ProofStep::TheoryLemma {
        theory: "EUF".to_string(),
        clause,
        farkas: None,
        kind: TheoryLemmaKind::EufCongruentPred,
        lia: None,
    });
    for equality in &bridge.equalities {
        let unit = emit_eq_plan(proof, equality, assumptions)?;
        let negative = equality.negated_equality();
        let position = residual.iter().position(|literal| *literal == negative)?;
        let _ = residual.remove(position);
        current = proof.add_resolution(residual.clone(), equality.equality(), current, unit);
    }
    if residual.as_slice() != [bridge.source_negative, target_atom] {
        return None;
    }
    Some(proof.add_resolution(vec![target_atom], bridge.source_atom, current, source_unit))
}

fn plan_direct_numeric_equality(
    executor: &mut Executor,
    definitions: &[Definition],
    equality: TermId,
    budget: &mut EqBudget,
) -> Option<EqPlan> {
    let (left, right) = arithmetic_equality_operands(executor, equality)?;
    let plan = plan_numeric_equality(&mut executor.ctx.terms, left, right, definitions, budget)?;
    if plan.emitted_step_upper_bound()? > MAX_DIRECT_EQUALITY_EMITTED_STEPS {
        return None;
    }
    Some(plan)
}

/// Put every top-level input premise before the first inference.
///
/// The direct lane discovers authenticated facts on demand, but Alethe's
/// document convention requires top-level `assume` commands to form a
/// prologue.  This stable partition preserves the relative order of both
/// groups and remaps every premise and named assumption exactly.  Direct
/// proofs contain no anchors, so encountering one (or a future proof-step
/// variant) declines instead of risking moving a subproof-local hypothesis.
fn hoist_direct_assumes(mut proof: Proof) -> Option<Proof> {
    if proof.steps.len() > MAX_DIRECT_STEPS {
        return None;
    }
    let was_assume: Vec<bool> = proof
        .steps
        .iter()
        .map(|step| matches!(step, ProofStep::Assume(_)))
        .collect();
    let mut order = Vec::with_capacity(proof.steps.len());
    order.extend(
        proof
            .steps
            .iter()
            .enumerate()
            .filter_map(|(index, step)| matches!(step, ProofStep::Assume(_)).then_some(index)),
    );
    order.extend(
        proof
            .steps
            .iter()
            .enumerate()
            .filter_map(|(index, step)| (!matches!(step, ProofStep::Assume(_))).then_some(index)),
    );

    let mut remap = vec![ProofId(u32::MAX); proof.steps.len()];
    for (new_index, &old_index) in order.iter().enumerate() {
        remap[old_index] = ProofId(u32::try_from(new_index).ok()?);
    }
    if remap.iter().any(|id| id.0 == u32::MAX) {
        return None;
    }

    let old_steps = std::mem::take(&mut proof.steps);
    let mut slots: Vec<Option<ProofStep>> = old_steps.into_iter().map(Some).collect();
    let mut steps = Vec::with_capacity(slots.len());
    for old_index in order {
        let step = slots.get_mut(old_index)?.take()?;
        let new_index = steps.len();
        steps.push(remap_direct_step(step, &remap, new_index)?);
    }

    let mut named_steps = std::mem::take(&mut proof.named_steps);
    for id in named_steps.values_mut() {
        let old_index = usize::try_from(id.0).ok()?;
        if !was_assume.get(old_index).copied().unwrap_or(false) {
            return None;
        }
        *id = *remap.get(old_index)?;
    }
    proof.steps = steps;
    proof.named_steps = named_steps;
    Some(proof)
}

fn remap_direct_step(step: ProofStep, remap: &[ProofId], new_index: usize) -> Option<ProofStep> {
    let mapped = |id: ProofId| -> Option<ProofId> {
        let id = *remap.get(usize::try_from(id.0).ok()?)?;
        (usize::try_from(id.0).ok()? < new_index).then_some(id)
    };
    match step {
        ProofStep::Assume(term) => Some(ProofStep::Assume(term)),
        ProofStep::Resolution {
            clause,
            pivot,
            clause1,
            clause2,
        } => Some(ProofStep::Resolution {
            clause,
            pivot,
            clause1: mapped(clause1)?,
            clause2: mapped(clause2)?,
        }),
        ProofStep::TheoryLemma {
            theory,
            clause,
            farkas,
            kind,
            lia,
        } => Some(ProofStep::TheoryLemma {
            theory,
            clause,
            farkas,
            kind,
            lia,
        }),
        ProofStep::Step {
            rule,
            clause,
            premises,
            args,
        } => Some(ProofStep::Step {
            rule,
            clause,
            premises: premises
                .into_iter()
                .map(mapped)
                .collect::<Option<Vec<_>>>()?,
            args,
        }),
        ProofStep::Anchor { .. } => None,
        _ => None,
    }
}

#[cfg(test)]
fn emit_positive_unit(
    executor: &mut Executor,
    proof: &mut Proof,
    assumptions: &mut DetHashMap<TermId, ProofId>,
    facts: &[TermId],
    atom: TermId,
    attempts: &mut u16,
    term_overrides: Option<&DetHashMap<TermId, String>>,
) -> Option<ProofId> {
    if facts.contains(&atom) {
        return Some(assume_once(proof, assumptions, atom));
    }
    if arithmetic_equality_operands(executor, atom).is_some() {
        return emit_positive_equality_unit(
            executor,
            proof,
            assumptions,
            facts,
            atom,
            attempts,
            term_overrides,
        );
    }
    let plan = plan_positive_unit(executor, facts, atom, attempts)?;
    emit_linear_unit_plan(executor, proof, assumptions, plan, atom, term_overrides)
}

fn emit_linear_unit_plan(
    executor: &mut Executor,
    proof: &mut Proof,
    assumptions: &mut DetHashMap<TermId, ProofId>,
    plan: LinearUnitPlan,
    atom: TermId,
    term_overrides: Option<&DetHashMap<TermId, String>>,
) -> Option<ProofId> {
    let mut residual = plan.clause.clone();
    let mut current = match plan.authority {
        LinearAuthority::Farkas(farkas) => {
            if !ay_proof::la_generic_farkas_lowering_supported(
                &executor.ctx.terms,
                &residual,
                &farkas,
                term_overrides,
            ) {
                return None;
            }
            proof.add_step(ProofStep::TheoryLemma {
                theory: "LRA".to_string(),
                clause: residual.clone(),
                farkas: Some(farkas),
                kind: TheoryLemmaKind::LraFarkas,
                lia: None,
            })
        }
        LinearAuthority::IntBounds => proof.add_step(ProofStep::TheoryLemma {
            theory: "LIA".to_string(),
            clause: residual.clone(),
            farkas: None,
            kind: TheoryLemmaKind::IntBoundsTautology,
            lia: None,
        }),
    };
    for fact in plan.facts {
        let blocker = executor.ctx.terms.mk_not_raw(fact);
        let position = residual.iter().position(|&literal| literal == blocker)?;
        let _ = residual.remove(position);
        let unit = assume_once(proof, assumptions, fact);
        current = proof.add_resolution(residual.clone(), fact, current, unit);
    }
    (residual.as_slice() == [atom]).then_some(current)
}

/// Lower a Farkas-implied equality through two independently certified bounds
/// and Alethe's checked arithmetic antisymmetry triangle.
///
/// Carcara's `la_generic` accepts a negated equality as an equality row, but a
/// positive equality is not a disequality operation and cannot conclude that
/// rule.  This is the same established lowering used by the EqDiffVar bridge:
/// derive both `<=` directions with the ordinary bounded Farkas path, then use
/// `ArithEqTriangle`, whose printer expands to checked `la_disequality`, `or`,
/// and `reordering` steps.  Both direction certificates debit `attempts`, so
/// this adapter cannot exceed the direct lane's existing global reconstruction
/// cap.
fn emit_positive_equality_unit(
    executor: &mut Executor,
    proof: &mut Proof,
    assumptions: &mut DetHashMap<TermId, ProofId>,
    facts: &[TermId],
    equality: TermId,
    attempts: &mut u16,
    term_overrides: Option<&DetHashMap<TermId, String>>,
) -> Option<ProofId> {
    let (left, right) = arithmetic_equality_operands(executor, equality)?;
    let forward = raw_le(executor, left, right)?;
    let reverse = raw_le(executor, right, left)?;
    let (forward_plan, reverse_plan) = plan_positive_equality_bounds(
        executor,
        facts,
        equality,
        forward,
        reverse,
        attempts,
        term_overrides,
    )?;
    let forward_unit = emit_linear_unit_plan(
        executor,
        proof,
        assumptions,
        forward_plan,
        forward,
        term_overrides,
    )?;
    let reverse_unit = emit_linear_unit_plan(
        executor,
        proof,
        assumptions,
        reverse_plan,
        reverse,
        term_overrides,
    )?;
    let not_forward = executor.ctx.terms.mk_not_raw(forward);
    let not_reverse = executor.ctx.terms.mk_not_raw(reverse);
    let triangle = vec![not_forward, not_reverse, equality];
    if !ay_proof::recognize_arith_eq_triangle(&executor.ctx.terms, &triangle) {
        return None;
    }
    let triangle_id = proof.add_step(ProofStep::TheoryLemma {
        theory: "LIA".to_string(),
        clause: triangle,
        farkas: None,
        kind: TheoryLemmaKind::ArithEqTriangle,
        lia: None,
    });
    let after_forward = proof.add_resolution(
        vec![not_reverse, equality],
        forward,
        triangle_id,
        forward_unit,
    );
    Some(proof.add_resolution(vec![equality], reverse, after_forward, reverse_unit))
}

/// Build the exact raw binary application that the triangle recognizer and
/// `la_disequality` wire rule inspect positionally.  Re-read the node so a
/// future folding/canonicalization change declines instead of changing an
/// operand behind the certificate.
fn raw_le(executor: &mut Executor, left: TermId, right: TermId) -> Option<TermId> {
    let atom = executor
        .ctx
        .terms
        .mk_app(Symbol::named("<="), [left, right], Sort::Bool);
    matches!(
        executor.ctx.terms.get(atom),
        TermData::App(symbol, arguments)
            if symbol.name() == "<=" && arguments.as_slice() == [left, right]
    )
    .then_some(atom)
}

fn arithmetic_equality_operands(executor: &Executor, equality: TermId) -> Option<(TermId, TermId)> {
    let TermData::App(symbol, arguments) = executor.ctx.terms.get(equality) else {
        return None;
    };
    if symbol.name() != "=" || arguments.len() != 2 {
        return None;
    }
    let (left, right) = (arguments[0], arguments[1]);
    let sort = executor.ctx.terms.sort(left);
    (sort == executor.ctx.terms.sort(right) && matches!(sort, Sort::Int | Sort::Real))
        .then_some((left, right))
}

fn plan_positive_unit(
    executor: &mut Executor,
    facts: &[TermId],
    atom: TermId,
    attempts: &mut u16,
) -> Option<LinearUnitPlan> {
    let limit = 1_u32.checked_shl(u32::try_from(facts.len()).ok()?)?;
    for support in 1..=MAX_LINEAR_SUPPORT.min(facts.len()) {
        for mask in 1..limit {
            if mask.count_ones() as usize != support {
                continue;
            }
            let selected: Vec<TermId> = facts
                .iter()
                .enumerate()
                .filter_map(|(index, &fact)| ((mask & (1_u32 << index)) != 0).then_some(fact))
                .collect();
            spend_linear_attempt(attempts)?;
            if let Some(plan) = plan_selected_positive_unit(executor, &selected, atom) {
                return Some(plan);
            }
        }
    }
    None
}

/// Discover a bounded support with the existing equality planner, then
/// independently certify both directions against that exact selected support.
/// The support walk and both direction reconstructions consume units from the
/// same global attempt ledger.
fn plan_positive_equality_bounds(
    executor: &mut Executor,
    facts: &[TermId],
    equality: TermId,
    forward: TermId,
    reverse: TermId,
    attempts: &mut u16,
    term_overrides: Option<&DetHashMap<TermId, String>>,
) -> Option<(LinearUnitPlan, LinearUnitPlan)> {
    let limit = 1_u32.checked_shl(u32::try_from(facts.len()).ok()?)?;
    for support in 1..=MAX_LINEAR_SUPPORT.min(facts.len()) {
        for mask in 1..limit {
            if mask.count_ones() as usize != support {
                continue;
            }
            let selected: Vec<TermId> = facts
                .iter()
                .enumerate()
                .filter_map(|(index, &fact)| ((mask & (1_u32 << index)) != 0).then_some(fact))
                .collect();
            spend_linear_attempt(attempts)?;
            if plan_selected_positive_unit(executor, &selected, equality).is_none() {
                continue;
            }
            spend_linear_attempt(attempts)?;
            let Some(forward_plan) = plan_selected_positive_unit(executor, &selected, forward)
            else {
                continue;
            };
            if !linear_unit_plan_lowering_supported(executor, &forward_plan, term_overrides) {
                continue;
            }
            spend_linear_attempt(attempts)?;
            let Some(reverse_plan) = plan_selected_positive_unit(executor, &selected, reverse)
            else {
                continue;
            };
            if !linear_unit_plan_lowering_supported(executor, &reverse_plan, term_overrides) {
                continue;
            }
            return Some((forward_plan, reverse_plan));
        }
    }
    None
}

fn linear_unit_plan_lowering_supported(
    executor: &Executor,
    plan: &LinearUnitPlan,
    term_overrides: Option<&DetHashMap<TermId, String>>,
) -> bool {
    match &plan.authority {
        LinearAuthority::Farkas(farkas) => ay_proof::la_generic_farkas_lowering_supported(
            &executor.ctx.terms,
            &plan.clause,
            farkas,
            term_overrides,
        ),
        LinearAuthority::IntBounds => true,
    }
}

fn spend_linear_attempt(attempts: &mut u16) -> Option<()> {
    *attempts = attempts.checked_sub(1)?;
    Some(())
}

fn plan_selected_positive_unit(
    executor: &mut Executor,
    selected: &[TermId],
    atom: TermId,
) -> Option<LinearUnitPlan> {
    let mut clause: Vec<TermId> = selected
        .iter()
        .map(|&fact| executor.ctx.terms.mk_not_raw(fact))
        .collect();
    clause.push(atom);
    let mut farkas = None;
    let mut kind = TheoryLemmaKind::Generic;
    let reconstructed = super::super::super::proof_farkas::try_lra_farkas_reconstruction(
        &executor.ctx.terms,
        &clause,
        &mut farkas,
        &mut kind,
    );
    let direct = FarkasAnnotation::new(vec![num_rational::Rational64::from(1); clause.len()]);
    let authority = if reconstructed {
        farkas.map(LinearAuthority::Farkas)
    } else if super::super::super::proof_farkas_validation::certificate_valid_for_blocking_clause(
        &executor.ctx.terms,
        &clause,
        &direct,
    ) {
        Some(LinearAuthority::Farkas(direct))
    } else if ay_core::proof_validation::recognize_int_bounds_tautology(
        &executor.ctx.terms,
        &clause,
    ) {
        Some(LinearAuthority::IntBounds)
    } else {
        None
    }?;
    Some(LinearUnitPlan {
        facts: selected.to_vec(),
        clause,
        authority,
    })
}

fn assume_once(
    proof: &mut Proof,
    assumptions: &mut DetHashMap<TermId, ProofId>,
    term: TermId,
) -> ProofId {
    if let Some(&id) = assumptions.get(&term) {
        return id;
    }
    let id = proof.add_assume(term, None);
    assumptions.insert(term, id);
    id
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn linear_reconstruction_attempt_cap_fails_closed() {
        let mut executor = Executor::new();
        let x = executor.ctx.terms.mk_var("linear_cap_x", Sort::Int);
        let zero = executor.ctx.terms.mk_int(0.into());
        let one = executor.ctx.terms.mk_int(1.into());
        let fact = executor
            .ctx
            .terms
            .mk_app(Symbol::named("<="), [zero, x], Sort::Bool);
        let x_plus_one = executor
            .ctx
            .terms
            .mk_app(Symbol::named("+"), [x, one], Sort::Int);
        let atom = executor
            .ctx
            .terms
            .mk_app(Symbol::named("<="), [zero, x_plus_one], Sort::Bool);
        let mut attempts = 0;
        assert!(plan_positive_unit(&mut executor, &[fact], atom, &mut attempts).is_none());
    }

    #[test]
    fn shared_linear_attempt_boundary_is_exact_and_fails_closed() {
        let mut attempts = MAX_LINEAR_ATTEMPTS;
        for _ in 0..MAX_LINEAR_ATTEMPTS {
            assert!(spend_linear_attempt(&mut attempts).is_some());
        }
        assert_eq!(attempts, 0);
        assert!(spend_linear_attempt(&mut attempts).is_none());
        assert_eq!(attempts, 0);
    }

    #[test]
    fn direct_override_byte_boundaries_are_exact() {
        let mut at_token_cap = DetHashMap::default();
        at_token_cap.insert(TermId(0), "x".repeat(MAX_DIRECT_OVERRIDE_TOKEN_BYTES));
        assert!(direct_overrides_admitted(Some(&at_token_cap)));
        at_token_cap.insert(TermId(0), "x".repeat(MAX_DIRECT_OVERRIDE_TOKEN_BYTES + 1));
        assert!(!direct_overrides_admitted(Some(&at_token_cap)));

        let exact_entries = MAX_DIRECT_OVERRIDE_BYTES / MAX_DIRECT_OVERRIDE_TOKEN_BYTES;
        assert_eq!(
            exact_entries * MAX_DIRECT_OVERRIDE_TOKEN_BYTES,
            MAX_DIRECT_OVERRIDE_BYTES
        );
        let build = |entries: usize| {
            (0..entries)
                .map(|index| {
                    (
                        TermId(u32::try_from(index).expect("small test index")),
                        "x".repeat(MAX_DIRECT_OVERRIDE_TOKEN_BYTES),
                    )
                })
                .collect::<DetHashMap<_, _>>()
        };
        assert!(direct_overrides_admitted(Some(&build(exact_entries))));
        assert!(!direct_overrides_admitted(Some(&build(exact_entries + 1))));

        let build_empty = |entries: usize| {
            (0..entries)
                .map(|index| {
                    (
                        TermId(u32::try_from(index).expect("small test index")),
                        String::new(),
                    )
                })
                .collect::<DetHashMap<_, _>>()
        };
        assert!(direct_overrides_admitted(Some(&build_empty(
            MAX_DIRECT_OVERRIDE_ENTRIES
        ))));
        assert!(!direct_overrides_admitted(Some(&build_empty(
            MAX_DIRECT_OVERRIDE_ENTRIES + 1
        ))));
    }

    #[test]
    fn implied_equality_uses_two_bounds_and_the_checked_triangle() {
        let mut executor = Executor::new();
        let x = executor.ctx.terms.mk_var("triangle_x", Sort::Int);
        let y = executor.ctx.terms.mk_var("triangle_y", Sort::Int);
        let z = executor.ctx.terms.mk_var("triangle_z", Sort::Int);
        let eq = |executor: &mut Executor, left, right| {
            executor
                .ctx
                .terms
                .mk_app(Symbol::named("="), [left, right], Sort::Bool)
        };
        let x_eq_y = eq(&mut executor, x, y);
        let y_eq_z = eq(&mut executor, y, z);
        let x_eq_z = eq(&mut executor, x, z);
        let mut proof = Proof::new();
        let mut assumptions = DetHashMap::default();
        let mut attempts = MAX_LINEAR_ATTEMPTS;
        let unit = emit_positive_unit(
            &mut executor,
            &mut proof,
            &mut assumptions,
            &[x_eq_y, y_eq_z],
            x_eq_z,
            &mut attempts,
            None,
        )
        .expect("two equality facts must derive their transitive equality");

        assert!(matches!(
            proof.steps.get(unit.0 as usize),
            Some(ProofStep::Resolution { clause, .. }) if clause.as_slice() == [x_eq_z]
        ));
        assert_eq!(
            proof
                .steps
                .iter()
                .filter(|step| matches!(
                    step,
                    ProofStep::TheoryLemma {
                        kind: TheoryLemmaKind::LraFarkas,
                        ..
                    }
                ))
                .count(),
            2,
            "each <= direction needs one independently checked Farkas lemma"
        );
        assert_eq!(
            proof
                .steps
                .iter()
                .filter(|step| matches!(
                    step,
                    ProofStep::TheoryLemma {
                        kind: TheoryLemmaKind::ArithEqTriangle,
                        ..
                    }
                ))
                .count(),
            1
        );
        for step in &proof.steps {
            let ProofStep::TheoryLemma {
                clause,
                kind: TheoryLemmaKind::LraFarkas,
                ..
            } = step
            else {
                continue;
            };
            assert!(clause.iter().all(|literal| {
                let (inner, negated) = match executor.ctx.terms.get(*literal) {
                    TermData::Not(inner) => (*inner, true),
                    _ => (*literal, false),
                };
                negated
                    || !matches!(
                        executor.ctx.terms.get(inner),
                        TermData::App(symbol, _) if symbol.name() == "="
                    )
            }));
        }
        assert!(attempts < MAX_LINEAR_ATTEMPTS);
        assert!(
            ay_proof::authenticate_premise_clauses_strict_with_context(
                &proof,
                &executor.ctx.terms,
                None,
                None,
                &[x_eq_y, y_eq_z],
            )
            .is_ok(),
            "the open unit fragment must pass the strict step/premise checker"
        );
    }

    #[test]
    fn direct_farkas_accepts_exact_equality_symmetry_but_declines_divergent_surface() {
        let mut executor = Executor::new();
        let x = executor.ctx.terms.mk_var("direct_surface_x", Sort::Int);
        let y = executor.ctx.terms.mk_var("direct_surface_y", Sort::Int);
        let equality = executor
            .ctx
            .terms
            .mk_app(Symbol::named("="), [x, y], Sort::Bool);
        let bound = executor
            .ctx
            .terms
            .mk_app(Symbol::named("<="), [x, y], Sort::Bool);
        let mut symmetric = DetHashMap::default();
        symmetric.insert(
            equality,
            "(= direct_surface_y direct_surface_x)".to_string(),
        );
        let symmetric_plan = plan_selected_positive_unit(&mut executor, &[equality], bound)
            .expect("an equality must imply its forward bound");
        assert!(matches!(
            &symmetric_plan.authority,
            LinearAuthority::Farkas(_)
        ));
        assert!(
            emit_linear_unit_plan(
                &mut executor,
                &mut Proof::new(),
                &mut DetHashMap::default(),
                symmetric_plan,
                bound,
                Some(&symmetric),
            )
            .is_some(),
            "exact equality symmetry is the same atom and its printed coefficient signs are replayed"
        );

        let mut divergent = DetHashMap::default();
        divergent.insert(
            equality,
            "(= direct_surface_y (+ direct_surface_x 0))".to_string(),
        );
        let divergent_plan = plan_selected_positive_unit(&mut executor, &[equality], bound)
            .expect("an equality must imply its forward bound");
        assert!(
            emit_linear_unit_plan(
                &mut executor,
                &mut Proof::new(),
                &mut DetHashMap::default(),
                divergent_plan,
                bound,
                Some(&divergent),
            )
            .is_none(),
            "an algebraically similar but non-symmetric operand rewrite remains divergent"
        );
    }
}
