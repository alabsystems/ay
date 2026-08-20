// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Surface-override roles for emitted EUF derivations.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{AletheRule, Proof, ProofStep, Symbol};

use super::super::proof_trust_surgery_provenance::ProvenanceSurfaceAudit;
use super::super::proof_trust_surgery_surface_audit::live_proof_rendering_is_static;
use super::{EufConcl, EufDeriv, EufJust, EufLemmaPlan, EufTarget};
use crate::executor::Executor;

fn protect_congruence_equality(
    audit: &mut ProvenanceSurfaceAudit,
    terms: &mut ay_core::TermStore,
    equality: ay_core::TermId,
) {
    let sides = match terms.get(equality).clone() {
        TermData::App(Symbol::Named(op), sides) if op == "=" && sides.len() == 2 => Some(sides),
        _ => None,
    };
    audit.protect_rigid_operand(terms, equality);
    if let Some(sides) = sides {
        // `eq_congruent` is positional and requires the two printed sides to
        // retain their canonical application heads. Equivalent implication,
        // reordered arithmetic, or let spellings are not interchangeable in
        // this rigid rule role.
        for side in sides {
            audit.protect_rigid_operand(terms, side);
        }
    }
}

fn protect_justification(
    audit: &mut ProvenanceSurfaceAudit,
    terms: &mut ay_core::TermStore,
    justification: &EufJust,
) {
    match justification {
        EufJust::Refl(side) => {
            let equality = terms.mk_eq(*side, *side);
            audit.protect_rigid_operand(terms, equality);
        }
        EufJust::Hyp(literal) => audit.protect_operand(terms, *literal),
        EufJust::Derived(_) => {}
    }
}

impl EufLemmaPlan {
    pub(in crate::executor) fn protect_surface_operands(
        &self,
        audit: &mut ProvenanceSurfaceAudit,
        terms: &mut ay_core::TermStore,
    ) {
        for deriv in &self.derivs {
            match deriv {
                EufDeriv::Cong { eq_term, prems } => {
                    protect_congruence_equality(audit, terms, *eq_term);
                    for premise in prems {
                        protect_justification(audit, terms, premise);
                    }
                }
                EufDeriv::Chain { eq_term, edges } => {
                    audit.protect_rigid_operand(terms, *eq_term);
                    for edge in edges {
                        protect_justification(audit, terms, edge);
                    }
                }
            }
        }
        match &self.concl {
            EufConcl::Eq { .. } => {}
            EufConcl::EqRefl { eq_term } => audit.protect_rigid_operand(terms, *eq_term),
            EufConcl::Pred {
                neg_lit,
                pos_lit,
                prems,
            } => {
                audit.protect_rigid_operand(terms, *neg_lit);
                audit.protect_rigid_operand(terms, *pos_lit);
                for premise in prems {
                    protect_justification(audit, terms, premise);
                }
            }
            EufConcl::ConstClash { unit_lit, .. } => {
                audit.protect_rigid_operand(terms, *unit_lit);
            }
        }
        match &self.target {
            EufTarget::Bare { extras } => {
                for &extra in extras {
                    audit.protect_operand(terms, extra);
                }
            }
            EufTarget::OrUnit { term } => audit.protect_rigid_operand(terms, *term),
        }
    }
}

/// Positional-role scan bounds for the promotion-local surface screen,
/// matching the shared audit's alias-scan envelope.
const MAX_PROMOTION_SURFACE_SCAN: usize = 100_000;
const MAX_PROMOTION_SURFACE_DEPTH: usize = 256;

/// Collect the full term DAG reachable from every certified `Skolem` step's
/// clause and arguments (the sko equality: source quantifier, its body, the
/// substituted instance, and the witness). Bounded; `None` on overflow.
fn skolem_managed_cone(
    terms: &ay_core::TermStore,
    proof: &Proof,
) -> Option<HashSet<ay_core::TermId>> {
    let mut cone: HashSet<ay_core::TermId> = HashSet::default();
    let mut pending: Vec<(ay_core::TermId, usize)> = Vec::new();
    for step in &proof.steps {
        let ProofStep::Step {
            rule: AletheRule::Skolem,
            clause,
            args,
            ..
        } = step
        else {
            continue;
        };
        pending.extend(clause.iter().map(|&term| (term, 0usize)));
        pending.extend(args.iter().map(|&term| (term, 0usize)));
    }
    let mut work = 0usize;
    while let Some((term, depth)) = pending.pop() {
        work = work.checked_add(1)?;
        if work > MAX_PROMOTION_SURFACE_SCAN || depth > MAX_PROMOTION_SURFACE_DEPTH {
            return None;
        }
        if !cone.insert(term) {
            continue;
        }
        for child in terms.children(term) {
            pending.push((child, depth + 1));
        }
    }
    Some(cone)
}

/// Whether any retained-override key occurs in the DAG of `roots`. Bounded;
/// overflow counts as an intersection (fail closed).
fn cone_mentions_key(
    terms: &ay_core::TermStore,
    roots: impl IntoIterator<Item = ay_core::TermId>,
    keys: &HashMap<ay_core::TermId, String>,
    work: &mut usize,
) -> bool {
    let mut pending: Vec<(ay_core::TermId, usize)> =
        roots.into_iter().map(|term| (term, 0usize)).collect();
    let mut seen: HashSet<ay_core::TermId> = HashSet::default();
    while let Some((term, depth)) = pending.pop() {
        *work = work.saturating_add(1);
        if *work > MAX_PROMOTION_SURFACE_SCAN || depth > MAX_PROMOTION_SURFACE_DEPTH {
            return true;
        }
        if keys.contains_key(&term) {
            return true;
        }
        if !seen.insert(term) {
            continue;
        }
        for child in terms.children(term) {
            pending.push((child, depth + 1));
        }
    }
    false
}

impl Executor {
    /// Validate every rule role introduced by standalone generic-EUF
    /// promotion against the already-active surface map. Unlike trust
    /// surgery, this pass has no authored-source authority with which to add
    /// or change an override, so any active spelling that reaches a promoted
    /// operand must already be compatible with its exact Alethe role.
    ///
    /// The screen audits the DELTA this pass creates plus every copied
    /// positional role, with two principled carve-outs that the original
    /// blanket version (c25240fc9c) lacked — without them the pass was
    /// unreachable for exactly the certified single-binder Skolem refutations
    /// (#forall-goal-boundary) it was landed for, because such proofs always
    /// carry both a `Skolem` step and authored-source overrides:
    ///
    /// 1. INERT IDENTITY OVERRIDES are pruned first (same rule as trust
    ///    surgery's `retained_surface_overrides_...`): an override that spells
    ///    its term exactly as the canonical renderer cannot change one printed
    ///    byte, so key-presence scans must not read it as a hazard.
    /// 2. The SKOLEM-MANAGED CONE — every term reachable from a certified
    ///    `Skolem` step's sko equality (source quantifier, body, substituted
    ///    instance, witness) — is rendered under the printer's own dynamic
    ///    substitution machinery (`prepare_skolem_choice_definitions`), which
    ///    independently re-validates each Skolem step, installs the
    ///    substituted spellings itself, and HARD-ERRORS the whole export on
    ///    any incompatible rendering. A static pre-veto on those keys can
    ///    only decline the promotion; it cannot make that printer validation
    ///    stricter. Keys inside the cone are therefore excluded from the
    ///    static scans, and `Skolem` steps themselves are exempt from the
    ///    static-rendering veto.
    ///
    /// Every key that survives both carve-outs must then be compatible with
    /// the roles this pass emits and copies:
    /// - a key in a RIGID emitted role tree (congruence equality and its
    ///   sides, predicate-transfer literals, the or-unit term) rejects;
    /// - an equality key must be exactly the orientation swap of its
    ///   canonical rendering (`eq_transitive`/`eq_congruent` premises accept
    ///   either orientation; identity was already pruned);
    /// - a negation key must keep the `(not ...)` shell so printed complement
    ///   matching in resolutions still holds;
    /// - any other key (an opaque literal spelling such as an authored
    ///   `(>= len 0)` for the canonical `(<= 0 len)`) renders consistently at
    ///   every occurrence and participates only in literal-identity roles;
    /// - a key reaching the operand cone of ANY copied positional step
    ///   (everything except pure resolution/contraction/weakening literal
    ///   plumbing, `Assume` leaves, replaced leaves, and printer-validated
    ///   `Skolem` steps) rejects — strictly broader than the shared
    ///   `copied_structural_roles_are_static` whitelist, deliberately, since
    ///   this pass performs none of the compensating role-composition
    ///   validation trust surgery does.
    pub(in crate::executor) fn generic_euf_promotion_surface_is_safe(
        &mut self,
        proof: &Proof,
        plans: &[Option<EufLemmaPlan>],
    ) -> bool {
        let Some(effective) = self.last_proof_term_overrides.as_ref() else {
            return true;
        };
        if effective.is_empty() {
            return true;
        }
        if plans.len() != proof.steps.len() {
            return false;
        }

        let mut audit = ProvenanceSurfaceAudit::default();
        let mut replaced = HashSet::default();
        for (index, plan) in plans.iter().enumerate() {
            let Some(plan) = plan else {
                continue;
            };
            replaced.insert(index);
            plan.protect_surface_operands(&mut audit, &mut self.ctx.terms);
        }
        if !audit.active_map_is_bounded(effective) || audit.is_overflowed() {
            return false;
        }

        // Carve-out 1: prune inert identity overrides (byte-for-byte the
        // canonical rendering; observationally free either way).
        let mut audited: HashMap<ay_core::TermId, String> = effective.clone();
        audited.retain(|&term, spelling| {
            *spelling != ay_proof::format_term_alethe(&self.ctx.terms, term)
        });
        if audited.is_empty() {
            return true;
        }

        // Carve-out 2: keys whose rendering the printer's checked Skolem
        // substitution machinery owns and re-validates fail-closed at export.
        let Some(cone) = skolem_managed_cone(&self.ctx.terms, proof) else {
            return false;
        };
        audited.retain(|term, _| !cone.contains(term));
        if audited.is_empty() {
            return true;
        }

        // Static-rendering veto for the remaining keys, with `Skolem` steps
        // exempt (printer-validated; see carve-out 2). All other arms — the
        // let-assume bridge, argument-bearing resolutions, and
        // array-extensionality lemmas — keep their veto.
        let live: Vec<bool> = proof
            .steps
            .iter()
            .map(|step| {
                !matches!(
                    step,
                    ProofStep::Step {
                        rule: AletheRule::Skolem,
                        ..
                    }
                )
            })
            .collect();
        if !live_proof_rendering_is_static(proof, &live, &self.ctx.terms, &audited) {
            return false;
        }

        // Copied positional roles: no surviving key may reach the operand
        // cone of any step whose printed shape is load-bearing.
        let mut work = 0usize;
        for (index, step) in proof.steps.iter().enumerate() {
            if !live[index] || replaced.contains(&index) {
                continue;
            }
            let (clause, args) = match step {
                ProofStep::Assume(_) | ProofStep::Anchor { .. } => continue,
                // Pure literal plumbing: printed per-term-consistent literal
                // identity (plus the negation-shell rule below) suffices.
                ProofStep::Resolution { .. } => continue,
                ProofStep::Step {
                    rule: AletheRule::Contraction | AletheRule::Weakening,
                    ..
                } => continue,
                ProofStep::Step { clause, args, .. } => (clause.as_slice(), args.as_slice()),
                ProofStep::TheoryLemma { clause, .. } => (clause.as_slice(), &[] as &[_]),
                _ => return false,
            };
            if cone_mentions_key(
                &self.ctx.terms,
                clause.iter().chain(args).copied(),
                &audited,
                &mut work,
            ) {
                return false;
            }
        }

        // Emitted-role compatibility for every surviving key.
        for (&key, spelling) in &audited {
            if audit.is_rigid(key) {
                return false;
            }
            match self.ctx.terms.get(key) {
                TermData::App(Symbol::Named(op), sides) if op == "=" && sides.len() == 2 => {
                    let swapped = format!(
                        "(= {} {})",
                        ay_proof::format_term_alethe(&self.ctx.terms, sides[1]),
                        ay_proof::format_term_alethe(&self.ctx.terms, sides[0]),
                    );
                    if *spelling != swapped {
                        return false;
                    }
                }
                TermData::Not(_) => {
                    if !spelling.starts_with("(not ") {
                        return false;
                    }
                }
                _ => {}
            }
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use ay_core::kani_compat::DetHashMap as HashMap;
    use ay_core::Sort;

    use super::ProvenanceSurfaceAudit;
    use crate::executor::Executor;

    #[test]
    fn standalone_euf_plan_audits_boolean_equality_surface() {
        let mut executor = Executor::new();
        let a = executor.ctx.terms.mk_var("late_euf_a", Sort::Int);
        let b = executor.ctx.terms.mk_var("late_euf_b", Sort::Int);
        let c = executor.ctx.terms.mk_var("late_euf_c", Sort::Int);
        let ab = executor.ctx.terms.mk_eq(a, b);
        let bc = executor.ctx.terms.mk_eq(b, c);
        let ac = executor.ctx.terms.mk_eq(a, c);
        let not_ab = executor.ctx.terms.mk_not_raw(ab);
        let not_bc = executor.ctx.terms.mk_not_raw(bc);
        let plan = executor
            .plan_euf_lemma(&[ac, not_ab, not_bc])
            .expect("transitivity fixture must plan");
        let mut audit = ProvenanceSurfaceAudit::default();
        plan.protect_surface_operands(&mut audit, &mut executor.ctx.terms);
        let mut active = HashMap::default();
        active.insert(not_ab, "(= (= late_euf_a late_euf_b) false)".to_string());
        assert!(!audit.validate_effective(&executor.ctx.terms, &active));
    }
}
