// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Reachable-assumption detection and source-faithful classification.

use super::*;

/// Whether faithful source-spelling overrides remain available to an assume.
pub(super) enum SurfaceOverridePolicy {
    /// Existing authenticated overrides may preserve an otherwise unsupported
    /// source spelling without rebuilding it.
    Retained,
    /// Overrides will be discarded, so classification must plan every repair
    /// needed by the surviving proof.
    Rebuilt,
}

impl Executor {
    /// Whether any assume REACHABLE from an empty-clause step is an original
    /// assertion whose exported (canonical) form would not print like the
    /// problem file — i.e. it classifies into one of the repairable assume
    /// bridge plans (expanded n-ary `distinct`, arithmetic-normalized `and`).
    /// Such proofs are checker-invalid even with ZERO trust steps: the
    /// caller uses this as a rebuild trigger alongside the trust report.
    pub(in crate::executor) fn reachable_normalized_assume(
        &mut self,
        proof: &Proof,
        originals: &[(TermId, FrontendTerm)],
    ) -> bool {
        let source_index = OriginalSourceIndex::new(originals);
        if !source_index.is_valid() {
            return true;
        }
        let Some(live) = taut_surface::live_steps(proof) else {
            return true;
        };
        for (idx, step) in proof.steps.iter().enumerate() {
            if !live[idx] {
                continue;
            }
            let ProofStep::Assume(term) = step else {
                continue;
            };
            let Some((_, parsed)) = source_index.get(originals, *term) else {
                if source_index.is_ambiguous(*term) {
                    return true;
                }
                continue; // non-original assumes are the sibling trigger's job
            };
            // A whole-term override can make the Assume itself match while
            // leaving its downstream canonical `and_pos`/distinct steps
            // inconsistent with that printed spelling (notably a
            // deduplicated conjunction). Classification, not the presence of
            // an override, decides whether a bridge is required.
            if matches!(
                self.classify_assume(*term, parsed, SurfaceOverridePolicy::Retained),
                Ok(Some(_))
            ) {
                return true;
            }
        }
        false
    }

    /// Classify a (verified-original) assume for repair. `Ok(None)` = keep
    /// as-is; `Err(())` = a repair is needed but cannot be built
    /// (fail-closed: abort the whole surgery).
    pub(super) fn classify_assume(
        &mut self,
        term: TermId,
        parsed: &FrontendTerm,
        override_policy: SurfaceOverridePolicy,
    ) -> Result<Option<AssumePlan>, ()> {
        if !surface_source_is_bounded(parsed) {
            return Err(());
        }
        // A `let`-wrapped surface (common in SMT-COMP inputs) hides the
        // repairable shape: expand the bindings first (pure substitution;
        // fail-closed on any capture risk). External checkers compare
        // against the same expansion (carcara: `--expand-let-bindings`).
        let expanded;
        let parsed = if matches!(strip_frontend_annotations(parsed), FrontendTerm::Let(..)) {
            match expand_surface_lets(
                strip_frontend_annotations(parsed),
                &std::collections::HashMap::new(),
            ) {
                Some(e) => {
                    expanded = e;
                    &expanded
                }
                None => return Ok(None),
            }
        } else {
            parsed
        };
        let stripped = strip_frontend_annotations(parsed);
        let FrontendTerm::App(head, operands) = stripped else {
            return Ok(None);
        };
        match head.as_str() {
            "distinct" if operands.len() >= 3 => {
                let pair_count = operands
                    .len()
                    .checked_mul(operands.len() - 1)
                    .map(|count| count / 2)
                    .ok_or(())?;
                if pair_count > taut_surface::MAX_EMITTED_CLAUSE_WIDTH {
                    return Err(());
                }
                let mut xs = Vec::with_capacity(operands.len());
                for op in operands {
                    xs.push(self.ctx.elaborate_surface_subterm(op).ok_or(())?);
                }
                let raw_xs = operands
                    .iter()
                    .map(|op| self.raw_intern_surface(op))
                    .collect::<Option<Vec<TermId>>>()
                    .ok_or(())?;
                if raw_xs != xs {
                    // The bridge below proves only the `distinct_elim` of
                    // these exact operands. A nested source rewrite needs its
                    // own derivation; never authorize the canonicalized
                    // shallow surrogate as an authored premise.
                    return Err(());
                }
                // The exported assume must be the pairwise `i < j` expansion
                // (exactly the `distinct_elim` conjunct order).
                let TermData::App(Symbol::Named(name), conjs) = self.ctx.terms.get(term) else {
                    return Err(());
                };
                if name != "and" {
                    return Err(());
                }
                if conjs.len() != pair_count {
                    return Err(());
                }
                let conjs = conjs.clone();
                let mut k = 0;
                for i in 0..xs.len() {
                    for j in (i + 1)..xs.len() {
                        let TermData::Not(inner) = self.ctx.terms.get(conjs[k]) else {
                            return Err(());
                        };
                        let TermData::App(Symbol::Named(op), args) = self.ctx.terms.get(*inner)
                        else {
                            return Err(());
                        };
                        if op != "=" || args.len() != 2 || args[0] != xs[i] || args[1] != xs[j] {
                            return Err(());
                        }
                        k += 1;
                    }
                }
                let raw = self
                    .ctx
                    .terms
                    .mk_app(Symbol::named("distinct"), raw_xs, Sort::Bool);
                if !matches!(
                    self.ctx.terms.get(raw),
                    TermData::App(Symbol::Named(op), args) if op == "distinct" && args.len() == xs.len()
                ) {
                    return Err(());
                }
                Ok(Some(AssumePlan::Distinct {
                    raw,
                    and_term: term,
                    conjs,
                }))
            }
            "and" => {
                if operands.len() > taut_surface::MAX_EMITTED_CLAUSE_WIDTH {
                    return Err(());
                }
                let TermData::App(Symbol::Named(name), conjs) = self.ctx.terms.get(term) else {
                    return Err(());
                };
                if name != "and" || conjs.len() > taut_surface::MAX_EMITTED_CLAUSE_WIDTH {
                    return Err(());
                }
                let conjs = conjs.clone();
                // A `distinct`-sugar operand (exported canonically as
                // `(not (= s t))` / its pairwise expansion, whose print no
                // longer matches the file) switches the scan into the
                // full-alignment `AndDistinct` mode. Without distinct sugar
                // the historical bounds-only behavior below is preserved
                // byte-for-byte.
                if operands.iter().any(|surf| {
                    matches!(strip_frontend_annotations(surf),
                        FrontendTerm::App(h, args) if h == "distinct" && args.len() >= 2)
                }) {
                    return self.classify_and_distinct(term, &conjs, operands);
                }
                if conjs.len() != operands.len() {
                    // Canonicalization FOLDED or DEDUPLICATED whole conjuncts
                    // away (e.g. a duplicated linear atom kept once): the
                    // positional bounds pairing below is impossible, but the
                    // alignment-capable `AndDistinct` classifier handles the
                    // skew (fail-open to keeping the assume as-is).
                    return self.classify_and_distinct(term, &conjs, operands);
                }
                let mut raws: Vec<(TermId, Option<TermId>)> = Vec::with_capacity(conjs.len());
                let mut any_bridge = false;
                let mut any_unshaped = false;
                for (surf, &conj) in operands.iter().zip(conjs.iter()) {
                    let Some((raw, bridge)) = self.surface_bound_or_linear_raw_term(surf, conj)
                    else {
                        // Not a bound-literal conjunct (e.g. an `or`-term in
                        // a CNF-shaped conjunction). Whether this vetoes the
                        // surgery is decided after the scan: a conjunction
                        // with NO orientation-bridged conjunct at all is not
                        // the arithmetic-normalized-bounds class and is kept
                        // as-is; a MIX of bridged and unshaped conjuncts is
                        // unrepairable (fail-closed, as before).
                        any_unshaped = true;
                        continue;
                    };
                    // Verify the orientation bridge certificate up front
                    // (fail-closed before any emission).
                    if bridge.is_some() {
                        let raw_complement = complement_of(&mut self.ctx.terms, raw);
                        if !self.pair_lemma_valid(conj, raw_complement) {
                            return Err(());
                        }
                        any_bridge = true;
                    } else if raw != conj {
                        return Err(());
                    }
                    raws.push((raw, bridge));
                }
                if any_unshaped {
                    if any_bridge {
                        return Err(());
                    }
                    // No conjunct needs repair: the assume prints as it
                    // always did — keep it rather than vetoing the whole
                    // surgery (other defect classes in the same proof may
                    // still be repairable).
                    return Ok(None);
                }
                if !any_bridge {
                    // Every conjunct already IS its canonical form: the
                    // exported assume prints like the file. Keep it.
                    return Ok(None);
                }
                let raw_and = self.ctx.terms.mk_app(
                    Symbol::named("and"),
                    raws.iter().map(|&(r, _)| r).collect::<Vec<_>>(),
                    Sort::Bool,
                );
                if !matches!(
                    self.ctx.terms.get(raw_and),
                    TermData::App(Symbol::Named(op), args) if op == "and" && args.len() == raws.len()
                ) {
                    return Err(());
                }
                Ok(Some(AssumePlan::AndBounds {
                    raw_and,
                    raws,
                    conjs,
                }))
            }
            "<" | "<=" | ">" | ">=" | "not" => {
                // A plain bound literal whose canonical orientation differs
                // from the surface spelling (e.g. `(> a 5)` vs `(< 5 a)`).
                // When surface overrides survive the surgery (ite-lift
                // class), an override-covered literal already prints
                // correctly and must not be planned (a plan would trip the
                // ite-lift exclusivity abort and leave the WHOLE proof
                // unrepaired). When overrides are purged, the same literal
                // MUST be bridged: its canonical print no longer matches.
                // No bridge needed when the raw term IS the canonical one;
                // unsupported shapes are kept as-is (they printed without
                // the surgery's help before, and the surgery fails closed on
                // its trust-free check if that ever stops holding).
                if matches!(override_policy, SurfaceOverridePolicy::Retained)
                    && self
                        .last_proof_term_overrides
                        .as_ref()
                        .is_some_and(|m| m.contains_key(&term))
                {
                    return Ok(None);
                }
                match self.surface_bound_or_linear_raw_term(parsed, term) {
                    Some((raw, Some(atom))) => {
                        let raw_complement = complement_of(&mut self.ctx.terms, raw);
                        if !self.pair_lemma_valid(term, raw_complement) {
                            return Err(());
                        }
                        Ok(Some(AssumePlan::Literal {
                            raw,
                            atom,
                            canonical: term,
                        }))
                    }
                    Some((_, None)) | None => Ok(None),
                }
            }
            _ => Ok(None),
        }
    }
}
