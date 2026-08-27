// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Authenticated surface-head and distinct-conjunction classification.

use super::*;

impl Executor {
    /// Authenticate the declaration identity selected while elaborating one
    /// surface application.
    ///
    /// `Ok(Some(symbol))` means elaboration retained the exact identity of one
    /// live declaration with this surface name. `Ok(None)` means no live
    /// declaration has the spelling, so rebuilding a builtin-shaped raw head
    /// is safe. A live declaration whose identity is absent or ambiguous is an
    /// authority mismatch and returns `Err(())`.
    pub(super) fn authenticated_surface_application_symbol(
        &self,
        surface_head: &str,
        elaborated: TermId,
    ) -> Result<Option<Symbol>, ()> {
        let elaborated_symbol = match self.ctx.terms.get(elaborated) {
            TermData::App(symbol @ Symbol::Named(_), _) => Some(symbol.clone()),
            _ => None,
        };
        let elaborated_identity = match elaborated_symbol.as_ref() {
            Some(Symbol::Named(identity)) => Some(identity.as_str()),
            _ => None,
        };

        let mut has_surface_declaration = false;
        let mut exact_matches = 0_usize;
        for (surface, info) in self.ctx.symbol_iter() {
            if surface.as_str() != surface_head {
                continue;
            }
            has_surface_declaration = true;
            if elaborated_identity
                .is_some_and(|identity| self.ctx.symbol_identity_name(surface, info) == identity)
            {
                exact_matches += 1;
            }
        }

        match (has_surface_declaration, exact_matches) {
            (false, 0) => Ok(None),
            (true, 1) => elaborated_symbol.map(Some).ok_or(()),
            // A declaration is live but elaboration either folded/expanded it
            // away or did not select one unique identity. Reconstructing the
            // source spelling as a canonical builtin would grant the wrong
            // premise semantics, so proof repair must fail closed.
            _ => Err(()),
        }
    }

    /// Classify a surface conjunction containing `distinct` sugar against
    /// its canonical export (see [`AssumePlan::AndDistinct`]). The canonical
    /// conjunction may have FOLDED trivial operands away (`(= c c)` ->
    /// `true`), DEDUPLICATED repeated conjuncts, and EXPANDED n-ary
    /// `distinct` operands into pairwise blocks — the scan aligns the
    /// surface operands with the canonical conjuncts in order, fail-open to
    /// `Ok(None)` (keep the assume as-is; the surgery's trust-free check
    /// still decides overall success) on anything unalignable.
    pub(super) fn classify_and_distinct(
        &mut self,
        term: TermId,
        conjs: &[TermId],
        operands: &[FrontendTerm],
    ) -> Result<Option<AssumePlan>, ()> {
        if conjs.len() > taut_surface::MAX_EMITTED_CLAUSE_WIDTH
            || operands.len() > taut_surface::MAX_EMITTED_CLAUSE_WIDTH
        {
            return Err(());
        }
        let mut units: Vec<AndDistinctUnit> = Vec::new();
        let mut raws: Vec<TermId> = Vec::with_capacity(operands.len());
        let mut k = 0usize;
        for (pos, surf) in operands.iter().enumerate() {
            #[allow(clippy::cast_possible_truncation)]
            let pos = pos as u32;
            let stripped = strip_frontend_annotations(surf);
            if let FrontendTerm::App(head, ops) = stripped {
                if head == "distinct" && ops.len() >= 2 {
                    let m = ops
                        .len()
                        .checked_mul(ops.len() - 1)
                        .map(|count| count / 2)
                        .ok_or(())?;
                    if m > taut_surface::MAX_EMITTED_CLAUSE_WIDTH
                        || k.checked_add(m).is_none_or(|end| end > conjs.len())
                    {
                        return Err(());
                    }
                    let Some(xs) = ops
                        .iter()
                        .map(|op| self.ctx.elaborate_surface_subterm(op))
                        .collect::<Option<Vec<TermId>>>()
                    else {
                        return Ok(None);
                    };
                    let Some(raw_xs) = ops
                        .iter()
                        .map(|op| self.raw_intern_surface(op))
                        .collect::<Option<Vec<TermId>>>()
                    else {
                        return Ok(None);
                    };
                    // `distinct_elim` below bridges the raw `distinct` only
                    // when its operands are the exact canonical operands used
                    // by the expansion. If a nested source operand itself
                    // folds/reorders, admitting the canonicalized term as an
                    // authored premise would be a provenance violation; such
                    // a case needs an additional explicit rewrite proof.
                    if raw_xs != xs {
                        return Err(());
                    }
                    let raw = self
                        .ctx
                        .terms
                        .mk_app(Symbol::named("distinct"), raw_xs, Sort::Bool);
                    if !matches!(
                        self.ctx.terms.get(raw),
                        TermData::App(Symbol::Named(op), args)
                            if op == "distinct" && args.len() == xs.len()
                    ) {
                        return Ok(None);
                    }
                    // The canonical export is the pairwise `i < j` block.
                    let mut kk = k;
                    for i in 0..xs.len() {
                        for j in (i + 1)..xs.len() {
                            let TermData::Not(inner) = self.ctx.terms.get(conjs[kk]) else {
                                return Ok(None);
                            };
                            let TermData::App(Symbol::Named(op), args) = self.ctx.terms.get(*inner)
                            else {
                                return Ok(None);
                            };
                            if op != "=" || args.len() != 2 || args[0] != xs[i] || args[1] != xs[j]
                            {
                                return Ok(None);
                            }
                            kk += 1;
                        }
                    }
                    let kind = if xs.len() == 2 {
                        AndDistinctKind::DistinctBinary
                    } else {
                        // The expansion conjunction itself (for the
                        // `distinct_elim` equivalence + `and_pos` splits).
                        let Some(block) = self.ctx.elaborate_surface_subterm(surf) else {
                            return Ok(None);
                        };
                        let TermData::App(Symbol::Named(op), args) = self.ctx.terms.get(block)
                        else {
                            return Ok(None);
                        };
                        if op != "and" || args.as_slice() != &conjs[k..k + m] {
                            return Ok(None);
                        }
                        #[allow(clippy::cast_possible_truncation)]
                        AndDistinctKind::DistinctNary {
                            and_term: block,
                            count: m as u32,
                        }
                    };
                    units.push(AndDistinctUnit { pos, raw, kind });
                    raws.push(raw);
                    k += m;
                    continue;
                }
            }
            let Some(elab) = self.ctx.elaborate_surface_subterm(surf) else {
                return Ok(None);
            };
            if self.ctx.terms.is_true(elab) || conjs[..k].contains(&elab) {
                // Folded-away (`(= c c)`) or deduplicated conjunct: present
                // in the raw print only, supplies no unit.
                let Some(raw) = self.raw_intern_surface(surf) else {
                    return Ok(None);
                };
                raws.push(raw);
                continue;
            }
            if k < conjs.len() && elab == conjs[k] {
                let conj = conjs[k];
                if let Some((raw, bridge)) = self.surface_bound_or_linear_raw_term(surf, conj) {
                    let kind = match bridge {
                        Some(atom) => {
                            let raw_complement = complement_of(&mut self.ctx.terms, raw);
                            if !self.pair_lemma_valid(conj, raw_complement) {
                                return Ok(None);
                            }
                            AndDistinctKind::Arith { atom }
                        }
                        None => {
                            if raw != conj {
                                return Ok(None);
                            }
                            AndDistinctKind::Plain
                        }
                    };
                    units.push(AndDistinctUnit { pos, raw, kind });
                    raws.push(raw);
                } else {
                    // A plain conjunct: keep the CANONICAL term as the raw
                    // conjunct (the strict checker then sees a fully
                    // id-consistent proof), accepted only when its print
                    // differs from the file by AT MOST binary-equality
                    // orientation — the one difference carcara's default
                    // mode tolerates everywhere. Anything else (`distinct`
                    // sugar, canonicalization that reordered an `or`, ...)
                    // would print unlike the file: keep the assume as-is.
                    let Some(raw) = self.raw_intern_surface(surf) else {
                        return Ok(None);
                    };
                    if !eq_flip_equivalent(&self.ctx.terms, raw, conj) {
                        // Last chance (#C2b): an `or`-conjunct whose
                        // canonical export reordered the disjuncts and/or
                        // flipped binary-equality orientations. The RAW
                        // disjunction (file order + orientations) is kept
                        // for the assume and bridged per-literal.
                        let Some(lits) = taut_surface::or_perm_lits(&self.ctx.terms, raw, conj)
                        else {
                            return Ok(None);
                        };
                        units.push(AndDistinctUnit {
                            pos,
                            raw,
                            kind: AndDistinctKind::OrPerm { lits },
                        });
                        raws.push(raw);
                        k += 1;
                        continue;
                    }
                    units.push(AndDistinctUnit {
                        pos,
                        raw: conj,
                        kind: AndDistinctKind::Plain,
                    });
                    raws.push(conj);
                }
                k += 1;
                continue;
            }
            return Ok(None);
        }
        if k != conjs.len() {
            return Ok(None);
        }
        if units
            .iter()
            .all(|u| matches!(u.kind, AndDistinctKind::Plain))
            && raws.len() == conjs.len()
        {
            // Nothing to repair: the canonical print already matches.
            return Ok(None);
        }
        let raw_and = self
            .ctx
            .terms
            .mk_app(Symbol::named("and"), raws.clone(), Sort::Bool);
        if !matches!(
            self.ctx.terms.get(raw_and),
            TermData::App(Symbol::Named(op), args) if op == "and" && args.len() == raws.len()
        ) {
            return Ok(None);
        }
        Ok(Some(AssumePlan::AndDistinct {
            raw_and,
            and_term: term,
            units,
            conjs: conjs.to_vec(),
        }))
    }
}
