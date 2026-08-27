// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact authored-source registration for retained-surface proof operands.

use super::*;

pub(super) const MAX_RETAINED_ORIGINALS: usize = 8_192;
const MAX_RETAINED_SOURCE_WORK: usize = 32 * 1024 * 1024;

#[derive(Clone, Copy, PartialEq, Eq)]
enum RequirementAuthority {
    Mandatory,
    CompatibilityOnly,
}

fn raw_arithmetic_equality_alias_matches(
    ctx: &mut ay_frontend::Context,
    parsed: &FrontendTerm,
    alias: TermId,
    installed: &str,
) -> bool {
    if !super::super::proof_surface_syntax::parsed_term_is_binder_free(parsed)
        || !ay_proof::printed_linear_arithmetic_literal_is_supported(installed)
    {
        return false;
    }
    let FrontendTerm::App(op, surface_operands) =
        super::super::proof_surface_syntax::strip_frontend_annotations(parsed)
    else {
        return false;
    };
    if op != "=" || surface_operands.len() != 2 || *ctx.terms.sort(alias) != Sort::Bool {
        return false;
    }
    let Some(operands) = surface_operands
        .iter()
        .map(|operand| ctx.elaborate_surface_subterm(operand))
        .collect::<Option<Vec<_>>>()
    else {
        return false;
    };
    if !operands
        .iter()
        .all(|&operand| matches!(ctx.terms.sort(operand), Sort::Int | Sort::Real))
    {
        return false;
    }
    matches!(
        ctx.terms.get(alias),
        TermData::App(Symbol::Named(alias_op), alias_operands)
            if alias_op == "=" && alias_operands.as_slice() == operands.as_slice()
    )
}

impl ProvenanceSurfaceAudit {
    fn merge_requirements_with_authority(
        &mut self,
        terms: &mut ay_core::TermStore,
        additions: HashMap<TermId, String>,
        authority: RequirementAuthority,
    ) -> bool {
        for (term, spelling) in additions {
            if let Some(existing) = self.requirements.get(&term) {
                if existing != &spelling {
                    return false;
                }
                if authority == RequirementAuthority::Mandatory {
                    self.compatibility_requirements.remove(&term);
                }
            } else {
                if self.requirements.len() >= MAX_AUDITED_REQUIREMENTS {
                    self.overflowed = true;
                    return false;
                }
                let Some(bytes) = self.requirement_bytes.checked_add(spelling.len()) else {
                    self.overflowed = true;
                    return false;
                };
                if bytes > MAX_REQUIREMENT_BYTES {
                    self.overflowed = true;
                    return false;
                }
                self.requirement_bytes = bytes;
                self.requirements.insert(term, spelling);
                if authority == RequirementAuthority::CompatibilityOnly {
                    self.compatibility_requirements.insert(term);
                }
            }
            self.register_polarity_pair(terms, term);
        }
        true
    }

    fn merge_requirements(
        &mut self,
        terms: &mut ay_core::TermStore,
        additions: HashMap<TermId, String>,
    ) -> bool {
        self.merge_requirements_with_authority(terms, additions, RequirementAuthority::Mandatory)
    }

    fn merge_compatibility_requirements(
        &mut self,
        terms: &mut ay_core::TermStore,
        additions: HashMap<TermId, String>,
    ) -> bool {
        self.merge_requirements_with_authority(
            terms,
            additions,
            RequirementAuthority::CompatibilityOnly,
        )
    }

    #[cfg(test)]
    pub(in crate::executor) fn require_spelling(
        &mut self,
        terms: &mut ay_core::TermStore,
        term: TermId,
        spelling: &str,
    ) -> bool {
        let mut requirement = HashMap::default();
        requirement.insert(term, spelling.to_string());
        self.merge_requirements(terms, requirement)
    }

    #[cfg(test)]
    pub(in crate::executor) fn require_compatibility_spelling(
        &mut self,
        terms: &mut ay_core::TermStore,
        term: TermId,
        spelling: &str,
    ) -> bool {
        let mut requirement = HashMap::default();
        requirement.insert(term, spelling.to_string());
        self.merge_compatibility_requirements(terms, requirement)
    }

    fn ensure_original_index(&mut self, originals: &[(TermId, FrontendTerm)]) -> bool {
        let identity = (originals.as_ptr() as usize, originals.len());
        if let Some(existing) = self.source_identity {
            return existing == identity;
        }
        if originals.len() > MAX_RETAINED_ORIGINALS {
            self.overflowed = true;
            return false;
        }
        for (index, (canonical, _)) in originals.iter().enumerate() {
            if self
                .source_indices
                .insert(*canonical, Some(index))
                .is_some()
            {
                self.source_indices.insert(*canonical, None);
            }
        }
        self.source_identity = Some(identity);
        true
    }

    pub(in crate::executor) fn require_original(
        &mut self,
        ctx: &mut ay_frontend::Context,
        originals: &[(TermId, FrontendTerm)],
        canonical: TermId,
    ) -> bool {
        self.require_original_as(ctx, originals, canonical, canonical)
    }

    /// Require one spelling that an exact source registration already
    /// authenticated. Deep arithmetic spellings are compatibility-only by
    /// default because most certified rules must stay canonical. An ITE-lift
    /// plan promotes its guard and any authenticated term-ITE spellings that
    /// generated ITE rules print independently, so the authored premise and
    /// those rules use one opaque-atom spelling. Final copied-step, rule-role,
    /// and printed-certificate replay still decide whether a promotion is safe.
    pub(in crate::executor) fn promote_registered_requirement(&mut self, term: TermId) -> bool {
        if !self.requirements.contains_key(&term) {
            return false;
        }
        if !self.promoted_requirements.contains(&term)
            && self.promoted_requirements.len() >= MAX_AUDITED_TERMS
        {
            self.overflowed = true;
            return false;
        }
        self.compatibility_requirements.remove(&term);
        self.promoted_requirements.insert(term);
        true
    }

    pub(in crate::executor) fn require_original_as(
        &mut self,
        ctx: &mut ay_frontend::Context,
        originals: &[(TermId, FrontendTerm)],
        canonical: TermId,
        alias: TermId,
    ) -> bool {
        self.require_original_as_inner(ctx, originals, canonical, alias, true, true)
    }

    /// Authenticate a fresh raw alias without retaining the canonical root's
    /// whole authored spelling. This is used when preprocessing elaborated an
    /// authored defining equality into a formula ITE: only the raw equality
    /// is an Assume, while the canonical ITE is a derived rigid rule operand.
    pub(in crate::executor) fn require_original_alias_only(
        &mut self,
        ctx: &mut ay_frontend::Context,
        originals: &[(TermId, FrontendTerm)],
        canonical: TermId,
        alias: TermId,
    ) -> bool {
        if canonical == alias
            || !self.require_original_as_inner(ctx, originals, canonical, alias, true, false)
            || (!self.suppressed_overrides.contains(&canonical)
                && self.suppressed_overrides.len() >= MAX_AUDITED_TERMS)
        {
            return false;
        }
        self.suppressed_overrides.insert(canonical);
        true
    }

    /// Upgrade one fresh raw defining-equality alias for use as an exact
    /// printed `la_generic` row. The authored whole can canonicalize to a
    /// formula ITE, so validate the raw alias against the two surface operands
    /// directly instead of granting arithmetic authority to the canonical
    /// source root.
    pub(in crate::executor) fn require_original_arithmetic_alias_only(
        &mut self,
        ctx: &mut ay_frontend::Context,
        originals: &[(TermId, FrontendTerm)],
        canonical: TermId,
        alias: TermId,
    ) -> bool {
        if !self.require_original_alias_only(ctx, originals, canonical, alias) {
            return false;
        }
        let Some(index) = self.source_indices.get(&canonical).copied().flatten() else {
            return false;
        };
        let Some((source, parsed)) = originals.get(index) else {
            return false;
        };
        let Some(installed) = self.requirements.get(&alias) else {
            return false;
        };
        if *source != canonical
            || !self.aliases.contains(&alias)
            || !raw_arithmetic_equality_alias_matches(ctx, parsed, alias, installed)
        {
            return false;
        }
        if !self.arithmetic_requirements.contains(&alias)
            && self.arithmetic_requirements.len() >= MAX_AUDITED_TERMS
        {
            self.overflowed = true;
            return false;
        }
        self.arithmetic_requirements.insert(alias);
        true
    }

    fn require_original_as_inner(
        &mut self,
        ctx: &mut ay_frontend::Context,
        originals: &[(TermId, FrontendTerm)],
        canonical: TermId,
        alias: TermId,
        alias_must_be_fresh: bool,
        include_canonical_root: bool,
    ) -> bool {
        if !self.ensure_original_index(originals) {
            return false;
        }
        let Some(index) = self.source_indices.get(&canonical).copied().flatten() else {
            return false;
        };
        let Some((source, parsed)) = originals.get(index) else {
            return false;
        };
        if *source != canonical {
            return false;
        }
        self.require_parsed_original_as_inner(
            ctx,
            parsed,
            canonical,
            alias,
            alias_must_be_fresh,
            include_canonical_root,
        )
    }

    /// Register one source whose exact, unique `(canonical, parsed)` authority
    /// has already been established by a bounded caller-owned index.
    pub(in crate::executor) fn require_parsed_original_as(
        &mut self,
        ctx: &mut ay_frontend::Context,
        parsed: &FrontendTerm,
        canonical: TermId,
        alias: TermId,
        alias_must_be_fresh: bool,
    ) -> bool {
        self.require_parsed_original_as_inner(
            ctx,
            parsed,
            canonical,
            alias,
            alias_must_be_fresh,
            true,
        )
    }

    fn require_parsed_original_as_inner(
        &mut self,
        ctx: &mut ay_frontend::Context,
        parsed: &FrontendTerm,
        canonical: TermId,
        alias: TermId,
        alias_must_be_fresh: bool,
        include_canonical_root: bool,
    ) -> bool {
        let registration = (
            canonical,
            alias,
            alias_must_be_fresh,
            include_canonical_root,
        );
        if self.source_registrations.contains(&registration) {
            return true;
        }
        // Native-API root (`api/solving/assertions.rs` sentinel): the
        // assertion has NO parsed surface, so the canonical rendering IS the
        // printed spelling and no override may be registered — registering
        // one would print the sentinel string. Same doctrine as
        // `proof_original_rebuild::is_api_placeholder`. Alias flows derive an
        // alias spelling FROM the parsed surface, which does not exist here;
        // they stay fail-closed.
        if alias == canonical && crate::executor::proof_original_rebuild::is_api_placeholder(parsed)
        {
            if !self.native_sources.contains(&canonical)
                && self.native_sources.len() >= MAX_AUDITED_TERMS
            {
                self.overflowed = true;
                return false;
            }
            self.native_sources.insert(canonical);
            self.source_registrations.insert(registration);
            return true;
        }
        let Some(canonical_work) =
            crate::executor::proof_surface_syntax::surface_override_collection_work(
                &ctx.terms, canonical,
            )
        else {
            return false;
        };
        let Some(canonical_source_work_used) =
            self.canonical_source_work_used.checked_add(canonical_work)
        else {
            self.overflowed = true;
            return false;
        };
        if canonical_source_work_used > MAX_RETAINED_SOURCE_WORK {
            self.overflowed = true;
            return false;
        }
        self.canonical_source_work_used = canonical_source_work_used;
        let Some(work) = surface_source_work(parsed) else {
            return false;
        };
        let Some(source_work_used) = self.source_work_used.checked_add(work.max(1)) else {
            self.overflowed = true;
            return false;
        };
        if source_work_used > MAX_RETAINED_SOURCE_WORK {
            self.overflowed = true;
            return false;
        }
        self.source_work_used = source_work_used;
        let mut arithmetic = HashSet::default();
        collect_surface_arithmetic_literals(ctx, parsed, &mut arithmetic);
        if arithmetic.contains(&canonical) {
            arithmetic.insert(alias);
        }
        let mut surface = HashMap::default();
        if !super::super::proof_surface_syntax::collect_surface_term_overrides(
            ctx,
            canonical,
            parsed,
            &mut surface,
        ) {
            return false;
        }
        let Some(whole) = surface.get(&canonical).cloned() else {
            return false;
        };
        if !include_canonical_root {
            surface.remove(&canonical);
            arithmetic.remove(&canonical);
        }
        surface.insert(alias, whole);
        if !self.merge_requirements(&mut ctx.terms, surface) {
            return false;
        }
        let mut deep = HashMap::default();
        super::super::proof_surface_syntax::collect_deep_arith_surface_overrides(
            ctx, parsed, &mut deep,
        );
        if !include_canonical_root {
            deep.remove(&canonical);
        }
        if !self.merge_compatibility_requirements(&mut ctx.terms, deep) {
            return false;
        }
        if alias != canonical && alias_must_be_fresh {
            if !self.aliases.contains(&alias) && self.aliases.len() >= MAX_AUDITED_TERMS {
                self.overflowed = true;
                return false;
            }
            self.aliases.insert(alias);
        }
        for term in arithmetic {
            if !self.arithmetic_requirements.contains(&term)
                && self.arithmetic_requirements.len() >= MAX_AUDITED_TERMS
            {
                self.overflowed = true;
                return false;
            }
            self.arithmetic_requirements.insert(term);
        }
        self.source_registrations.insert(registration);
        true
    }

    #[cfg(test)]
    pub(super) fn retained_source_work_used(&self) -> usize {
        self.source_work_used
    }

    pub(in crate::executor) fn merge_into(&self, active: &mut HashMap<TermId, String>) -> bool {
        for term in &self.suppressed_overrides {
            if self.requirements.contains_key(term)
                && !self.compatibility_requirements.contains(term)
            {
                return false;
            }
            active.remove(term);
        }
        self.requirements.iter().all(|(&term, expected)| {
            if !self.protected.contains(&term) {
                return true;
            }
            if let Some(actual) = active.get(&term) {
                actual == expected
            } else if self.compatibility_requirements.contains(&term) {
                true
            } else if self.aliases.contains(&term) || self.promoted_requirements.contains(&term) {
                active.insert(term, expected.clone());
                true
            } else {
                false
            }
        })
    }
}
