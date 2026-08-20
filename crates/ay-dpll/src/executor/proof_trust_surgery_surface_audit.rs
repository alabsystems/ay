// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Final rendered-surface audit for trust-surgery proof operands.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{FarkasAnnotation, Proof, ProofStep, Sort, Symbol, TermId};
use ay_frontend::command::Term as FrontendTerm;

use super::proof_trust_surgery_provenance::{collect_surface_arithmetic_literals, complement_of};

#[cfg(test)]
#[path = "proof_trust_surgery_surface_alias_tests.rs"]
mod alias_tests;
#[path = "proof_trust_surgery_surface_connective.rs"]
mod connective;
#[path = "proof_trust_surgery_surface_copied.rs"]
mod copied;
#[path = "proof_trust_surgery_surface_limits.rs"]
mod limits;
#[path = "proof_trust_surgery_source_work.rs"]
mod source_work;
#[path = "proof_trust_surgery_surface_sources.rs"]
mod sources;
#[cfg(test)]
#[path = "proof_trust_surgery_surface_audit_tests.rs"]
mod tests;
#[path = "proof_trust_surgery_surface_validate.rs"]
mod validate;
pub(in crate::executor) use copied::copied_structural_roles_are_static;
pub(in crate::executor) use limits::render_roots_have_bounded_payload;
#[cfg(test)]
pub(in crate::executor) use limits::surface_pass_work;
pub(in crate::executor) use limits::{
    live_proof_rendering_is_static, surface_source_is_bounded, surface_source_work,
    surface_sources_have_bounded_work, term_child_count, ProofSourcePass, ProofSourceWorkEnvelope,
};
use limits::{render_roots_have_bounded_depth, MAX_REQUIREMENT_BYTES, MAX_SURFACE_DEPTH};

const MAX_AUDITED_POLARITY_PAIRS: usize = 4_096;
const MAX_AUDITED_FARKAS_LEMMAS: usize = 512;
const MAX_AUDITED_FARKAS_ROWS: usize = 8_192;
const MAX_AUDITED_FARKAS_SIGN_CHECKS: usize = 16_384;
const MAX_AUDITED_TERMS: usize = 16_384;
const MAX_AUDITED_REQUIREMENTS: usize = 8_192;
const MAX_AUDITED_RENDER_WORK: u64 = 8 * 1024 * 1024;
const MAX_ALIAS_SCAN_TERMS: usize = 100_000;

/// Retained surface syntax cannot coexist with an unaudited deferred leaf or
/// with quantifier repair's separately prepared rendering map. Standalone
/// quantifier repair remains supported.
pub(in crate::executor) fn retained_surface_plan_mix_is_safe(
    keeps_surface_overrides: bool,
    has_deferred_leaves: bool,
    has_quant_plans: bool,
) -> bool {
    !(keeps_surface_overrides && (has_deferred_leaves || has_quant_plans)
        || has_quant_plans && has_deferred_leaves)
}

#[derive(Default)]
pub(in crate::executor) struct ProvenanceSurfaceAudit {
    requirements: HashMap<TermId, String>,
    compatibility_requirements: HashSet<TermId>,
    protected: HashSet<TermId>,
    rigid: HashSet<TermId>,
    recursive_rigid_identity: HashSet<TermId>,
    farkas: HashSet<TermId>,
    arithmetic_requirements: HashSet<TermId>,
    polarity_pairs: HashSet<(TermId, TermId)>,
    render_equalities: HashSet<(TermId, TermId)>,
    ite_intro_roles: HashSet<(TermId, TermId, TermId)>,
    or_decomposition_roles: HashSet<(TermId, Vec<TermId>)>,
    and_projection_roles: HashSet<(TermId, u32, TermId)>,
    and_introduction_roles: HashSet<(TermId, Vec<TermId>)>,
    copied_and_projection_roles: HashSet<(TermId, u32, TermId)>,
    generated_connective_render_uses: HashMap<TermId, usize>,
    generated_and_projection_uses: usize,
    aliases: HashSet<TermId>,
    promoted_requirements: HashSet<TermId>,
    suppressed_overrides: HashSet<TermId>,
    farkas_lemmas: Vec<(Vec<TermId>, FarkasAnnotation)>,
    source_registrations: HashSet<(TermId, TermId, bool, bool)>,
    source_indices: HashMap<TermId, Option<usize>>,
    source_identity: Option<(usize, usize)>,
    farkas_rows: usize,
    requirement_bytes: usize,
    source_work_used: usize,
    canonical_source_work_used: usize,
    overflowed: bool,
}

impl ProvenanceSurfaceAudit {
    /// Whether any bounded collection overflowed; an overflowed audit must
    /// fail closed in every consumer.
    pub(in crate::executor) fn is_overflowed(&self) -> bool {
        self.overflowed
    }

    /// Whether `term` participates in a RIGID printed role (registered via
    /// [`Self::protect_rigid_operand`]/[`Self::protect_rigid_root`]): its
    /// exact canonical rendering is load-bearing for a positional Alethe rule,
    /// so no retained spelling may reach it.
    pub(in crate::executor) fn is_rigid(&self, term: TermId) -> bool {
        self.rigid.contains(&term)
    }

    pub(in crate::executor) fn active_map_is_bounded(
        &self,
        active: &HashMap<TermId, String>,
    ) -> bool {
        active.len() <= MAX_AUDITED_REQUIREMENTS
            && active
                .values()
                .try_fold(0usize, |bytes, spelling| bytes.checked_add(spelling.len()))
                .is_some_and(|bytes| bytes <= MAX_REQUIREMENT_BYTES)
    }

    fn validate_farkas_lemmas_with_budget(
        &self,
        terms: &ay_core::TermStore,
        rendered: &HashMap<TermId, String>,
        remaining_checks: &mut usize,
        remaining_parse_bytes: &mut usize,
    ) -> bool {
        self.farkas_lemmas.iter().all(|(clause, farkas)| {
            ay_proof::printed_la_generic_certificate_is_valid_bounded(
                terms,
                clause,
                farkas,
                rendered,
                remaining_checks,
                remaining_parse_bytes,
            )
        })
    }

    fn register_polarity_pair(&mut self, terms: &mut ay_core::TermStore, term: TermId) {
        if *terms.sort(term) != Sort::Bool {
            return;
        }
        let complement = complement_of(terms, term);
        let pair = if term.0 <= complement.0 {
            (term, complement)
        } else {
            (complement, term)
        };
        if !self.polarity_pairs.contains(&pair) {
            if self.polarity_pairs.len() >= MAX_AUDITED_POLARITY_PAIRS {
                self.overflowed = true;
                return;
            }
            self.polarity_pairs.insert(pair);
        }
    }

    fn protect_tree(&mut self, terms: &ay_core::TermStore, root: TermId) {
        let mut pending = vec![(root, 0usize)];
        while let Some((term, depth)) = pending.pop() {
            if depth > MAX_SURFACE_DEPTH {
                self.overflowed = true;
                return;
            }
            if !self.protected.contains(&term) {
                if self.protected.len() >= MAX_AUDITED_TERMS {
                    self.overflowed = true;
                    return;
                }
                self.protected.insert(term);
                let Some(child_count) = term_child_count(terms, term) else {
                    self.overflowed = true;
                    return;
                };
                if pending
                    .len()
                    .saturating_add(self.protected.len())
                    .saturating_add(child_count)
                    > MAX_AUDITED_TERMS
                {
                    self.overflowed = true;
                    return;
                }
                for child in terms.children(term) {
                    pending.push((child, depth + 1));
                }
            }
        }
    }

    fn protect_rigid_tree(&mut self, terms: &ay_core::TermStore, root: TermId) {
        let mut pending = vec![(root, 0usize)];
        while let Some((term, depth)) = pending.pop() {
            if depth > MAX_SURFACE_DEPTH {
                self.overflowed = true;
                return;
            }
            if !self.protected.contains(&term) {
                if self.protected.len() >= MAX_AUDITED_TERMS {
                    self.overflowed = true;
                    return;
                }
                self.protected.insert(term);
            }
            if !self.rigid.contains(&term) {
                if self.rigid.len() >= MAX_AUDITED_TERMS {
                    self.overflowed = true;
                    return;
                }
                self.rigid.insert(term);
            }
            if !self.recursive_rigid_identity.contains(&term) {
                if self.recursive_rigid_identity.len() >= MAX_AUDITED_TERMS {
                    self.overflowed = true;
                    return;
                }
                self.recursive_rigid_identity.insert(term);
                let Some(child_count) = term_child_count(terms, term) else {
                    self.overflowed = true;
                    return;
                };
                if pending
                    .len()
                    .saturating_add(self.recursive_rigid_identity.len())
                    .saturating_add(child_count)
                    > MAX_AUDITED_TERMS
                {
                    self.overflowed = true;
                    return;
                }
                for child in terms.children(term) {
                    pending.push((child, depth + 1));
                }
            }
        }
    }

    pub(in crate::executor) fn protect_operand(
        &mut self,
        terms: &mut ay_core::TermStore,
        term: TermId,
    ) {
        self.protect_tree(terms, term);
        self.register_polarity_pair(terms, term);
        if *terms.sort(term) == Sort::Bool {
            let complement = complement_of(terms, term);
            self.protect_tree(terms, complement);
        }
    }

    pub(in crate::executor) fn protect_rigid_operand(
        &mut self,
        terms: &mut ay_core::TermStore,
        term: TermId,
    ) {
        self.protect_operand(terms, term);
        self.protect_rigid_tree(terms, term);
        if *terms.sort(term) == Sort::Bool {
            let complement = complement_of(terms, term);
            self.protect_rigid_tree(terms, complement);
        }
    }

    pub(in crate::executor) fn protect_rigid_root(
        &mut self,
        terms: &mut ay_core::TermStore,
        term: TermId,
    ) {
        self.protect_operand(terms, term);
        if !self.rigid.contains(&term) {
            if self.rigid.len() >= MAX_AUDITED_TERMS {
                self.overflowed = true;
                return;
            }
            self.rigid.insert(term);
        }
    }

    /// Register the exact positional terms consumed by `ite_intro`.
    ///
    /// Authenticated spellings may remain on the condition and branches, but
    /// the rendered ITE and both defining equalities must compose from those
    /// same spellings in the rule's required operand order.
    pub(in crate::executor) fn protect_ite_intro_role(
        &mut self,
        terms: &mut ay_core::TermStore,
        ite_term: TermId,
        eq_then: TermId,
        eq_else: TermId,
    ) {
        let TermData::Ite(_, then_term, else_term) = *terms.get(ite_term) else {
            self.overflowed = true;
            return;
        };
        let eq_has_shape = |term: TermId, branch: TermId| {
            matches!(
                terms.get(term),
                TermData::App(Symbol::Named(op), args)
                    if op == "=" && args.as_slice() == [ite_term, branch]
            )
        };
        if !eq_has_shape(eq_then, then_term) || !eq_has_shape(eq_else, else_term) {
            self.overflowed = true;
            return;
        }
        let role = (ite_term, eq_then, eq_else);
        if self.ite_intro_roles.contains(&role) {
            return;
        }
        if self.ite_intro_roles.len() >= MAX_AUDITED_FARKAS_LEMMAS {
            self.overflowed = true;
            return;
        }
        for operand in [ite_term, eq_then, eq_else] {
            self.protect_operand(terms, operand);
        }
        self.ite_intro_roles.insert(role);
    }

    /// Demand that an already-authenticated authored spelling be INSTALLED in
    /// the effective rendering map, not merely tolerated there.
    ///
    /// `collect_deep_arith_surface_overrides` registers the authored spelling
    /// of every arithmetic subterm of a retained assertion as a COMPATIBILITY
    /// requirement: `merge_into` checks such an entry when the active map
    /// already carries it and otherwise SKIPS it, because a subterm that is
    /// only ever printed inside its parent inherits the parent's authored
    /// spelling and needs no entry of its own.
    ///
    /// An `ite_intro` role breaks that assumption. The lift retains the
    /// authored whole-assertion spelling on the re-added assume — which
    /// embeds the authored spelling of the term-level ite — while `ite1` and
    /// `ite2` print that same ite, its condition and its branches as
    /// independent operands of the generated defining equalities. Where the
    /// authored spelling differs from the canonical rendering (an authored
    /// `(= 0 r)` against the canonicalized `(= r 0)`) the two printings
    /// disagree, the exported `la_generic` transfer row can no longer cancel
    /// its opaque atoms, and the whole repair is discarded.
    ///
    /// Only a spelling already registered by `require_original*` is eligible:
    /// those are obtained by re-elaborating the authored source subtree to
    /// this exact hash-consed `TermId`, so nothing new is asserted here. A
    /// term with no registered requirement renders canonically wherever it
    /// stands alone and needs no install; should its parent's override
    /// nevertheless spell it differently, the printed-certificate re-check in
    /// `validate_effective` still rejects the mismatch, so this is a
    /// completeness repair and never a trusted shortcut.
    pub(in crate::executor) fn require_installed_surface(
        &mut self,
        terms: &mut ay_core::TermStore,
        term: TermId,
    ) {
        if !self.requirements.contains_key(&term) {
            return;
        }
        if !self.promote_registered_requirement(term) {
            self.overflowed = true;
            return;
        }
        self.protect_operand(terms, term);
    }

    pub(in crate::executor) fn require_same_rendering(
        &mut self,
        terms: &mut ay_core::TermStore,
        left: TermId,
        right: TermId,
    ) {
        self.protect_operand(terms, left);
        self.protect_operand(terms, right);
        let pair = if left.0 <= right.0 {
            (left, right)
        } else {
            (right, left)
        };
        if !self.render_equalities.contains(&pair) {
            if self.render_equalities.len() >= MAX_AUDITED_POLARITY_PAIRS {
                self.overflowed = true;
                return;
            }
            self.render_equalities.insert(pair);
        }
    }

    pub(in crate::executor) fn protect_farkas_operand(
        &mut self,
        terms: &mut ay_core::TermStore,
        term: TermId,
    ) {
        if self.overflowed {
            return;
        }
        self.register_polarity_pair(terms, term);
        let complement = complement_of(terms, term);
        for mut current in [term, complement] {
            let mut depth = 0usize;
            loop {
                if depth > MAX_SURFACE_DEPTH {
                    self.overflowed = true;
                    return;
                }
                self.protect_tree(terms, current);
                if self.overflowed || self.farkas.len() >= MAX_AUDITED_TERMS {
                    self.overflowed = true;
                    return;
                }
                self.farkas.insert(current);
                let TermData::Not(inner) = terms.get(current) else {
                    break;
                };
                current = *inner;
                depth += 1;
            }
        }
    }

    pub(in crate::executor) fn protect_farkas_lemma(
        &mut self,
        terms: &mut ay_core::TermStore,
        clause: &[TermId],
        farkas: &FarkasAnnotation,
    ) {
        let Some(rows) = self.farkas_rows.checked_add(clause.len()) else {
            self.overflowed = true;
            return;
        };
        if self.farkas_lemmas.len() >= MAX_AUDITED_FARKAS_LEMMAS || rows > MAX_AUDITED_FARKAS_ROWS {
            self.overflowed = true;
            return;
        }
        self.farkas_rows = rows;
        for &literal in clause {
            self.protect_farkas_operand(terms, literal);
        }
        self.farkas_lemmas.push((clause.to_vec(), farkas.clone()));
    }

    pub(in crate::executor) fn aliases_are_fresh_in(
        &self,
        proof: &Proof,
        terms: &ay_core::TermStore,
    ) -> bool {
        if self.aliases.is_empty() && self.suppressed_overrides.is_empty() {
            return true;
        }
        let mut work = 0usize;
        for step in &proof.steps {
            let mut roots = Vec::new();
            match step {
                ProofStep::Assume(term) => roots.push(*term),
                ProofStep::Resolution { clause, pivot, .. } => {
                    if clause.len().saturating_add(1) > MAX_ALIAS_SCAN_TERMS.saturating_sub(work) {
                        return false;
                    }
                    roots.extend(clause.iter().copied());
                    roots.push(*pivot);
                }
                ProofStep::TheoryLemma { clause, .. } => {
                    if clause.len() > MAX_ALIAS_SCAN_TERMS.saturating_sub(work) {
                        return false;
                    }
                    roots.extend(clause.iter().copied());
                }
                ProofStep::Step { clause, args, .. } => {
                    if clause.len().saturating_add(args.len())
                        > MAX_ALIAS_SCAN_TERMS.saturating_sub(work)
                    {
                        return false;
                    }
                    roots.extend(clause.iter().copied());
                    roots.extend(args.iter().copied());
                }
                ProofStep::Anchor { .. } => {}
                _ => return false,
            }
            let mut pending: Vec<(TermId, usize)> =
                roots.into_iter().map(|term| (term, 0usize)).collect();
            let mut seen = HashSet::default();
            while let Some((term, depth)) = pending.pop() {
                work += 1;
                if work > MAX_ALIAS_SCAN_TERMS
                    || depth > MAX_SURFACE_DEPTH
                    || self.aliases.contains(&term)
                    || self.suppressed_overrides.contains(&term)
                {
                    return false;
                }
                if seen.insert(term) {
                    let Some(child_count) = term_child_count(terms, term) else {
                        return false;
                    };
                    if pending
                        .len()
                        .saturating_add(work)
                        .saturating_add(child_count)
                        > MAX_ALIAS_SCAN_TERMS
                    {
                        return false;
                    }
                    for child in terms.children(term) {
                        pending.push((child, depth + 1));
                    }
                }
            }
        }
        true
    }
}
