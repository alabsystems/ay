// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Bounded planning for authenticated proof surface rewrites.

impl Executor {
    fn poison_input_syntax_rewrite(proof: &mut Proof) {
        let mut poisoned = Proof::new();
        poisoned.add_rule_step(AletheRule::Trust, Vec::new(), Vec::new(), Vec::new());
        *proof = poisoned;
    }

    fn provenance_pair_specs(
        &self,
        problem_assertions: &[TermId],
        original_problem_assertions: &[TermId],
        source_scan_work: &mut usize,
        override_plan_valid: &mut bool,
    ) -> Vec<(TermId, usize)> {
        let Some(provenance) = &self.proof_problem_assertion_provenance else {
            return Vec::new();
        };
        let parsed_by_original: HashMap<TermId, usize> = original_problem_assertions
            .iter()
            .copied()
            .enumerate()
            .map(|(index, term)| (term, index))
            .collect();
        let mut pairs = Vec::new();
        let mut seen = HashSet::default();
        'problem_sources: for &canonical in problem_assertions {
            let Some(source_sets) = provenance.assertion_sources.get(&canonical) else {
                continue;
            };
            let Some(next_work) = source_scan_work.checked_add(source_sets.len()) else {
                *override_plan_valid = false;
                break;
            };
            if next_work > MAX_OVERRIDE_SOURCE_SCAN {
                *override_plan_valid = false;
                break;
            }
            *source_scan_work = next_work;
            for source_set in source_sets {
                if let [source] = source_set.as_slice() {
                    if let Some(&parsed_index) = parsed_by_original.get(source) {
                        if seen.insert((canonical, parsed_index)) {
                            if pairs.len() >= MAX_OVERRIDE_PAIRS {
                                *override_plan_valid = false;
                                break 'problem_sources;
                            }
                            pairs.push((canonical, parsed_index));
                        }
                    }
                }
            }
        }

        // Original assertions that appear in MULTI-source provenance sets
        // (e.g. a propagated theory atom sourced from a Boolean definition
        // `(= c atom)` plus the defining literal `c`) are problem premises in
        // their own right: the derivation pass can re-introduce them as
        // `assume` steps. Pair each with its own parsed form so those assumes —
        // and their surface subterms — print with the problem file's syntax and
        // an external checker can match them to the original premises.
        let mut paired: ay_core::kani_compat::DetHashSet<TermId> =
            pairs.iter().map(|(canonical, _)| *canonical).collect();
        'all_sources: for source_sets in provenance.assertion_sources.values() {
            let Some(next_work) = source_scan_work.checked_add(source_sets.len()) else {
                *override_plan_valid = false;
                break;
            };
            if next_work > MAX_OVERRIDE_SOURCE_SCAN {
                *override_plan_valid = false;
                break;
            }
            *source_scan_work = next_work;
            for source_set in source_sets {
                if source_set.len() < 2 {
                    continue;
                }
                let Some(next_work) = source_scan_work.checked_add(source_set.len()) else {
                    *override_plan_valid = false;
                    break 'all_sources;
                };
                if next_work > MAX_OVERRIDE_SOURCE_SCAN {
                    *override_plan_valid = false;
                    break 'all_sources;
                }
                *source_scan_work = next_work;
                for &source in source_set {
                    if paired.insert(source) {
                        if let Some(&parsed_index) = parsed_by_original.get(&source) {
                            if seen.insert((source, parsed_index)) {
                                if pairs.len() >= MAX_OVERRIDE_PAIRS {
                                    *override_plan_valid = false;
                                    break 'all_sources;
                                }
                                pairs.push((source, parsed_index));
                            }
                        }
                    }
                }
            }
        }
        pairs
    }

    fn prepare_surface_overrides(
        &mut self,
    ) -> Option<(
        Vec<(TermId, ay_frontend::command::Term)>,
        HashMap<TermId, String>,
    )> {
        let problem_assertions = self.proof_problem_assertions();
        let original_problem_assertions = self.proof_original_problem_assertions();
        let parsed_assertions: &[ay_frontend::command::Term] = self.ctx.assertions_parsed();
        let mut override_plan_valid = problem_assertions.len() <= MAX_OVERRIDE_SOURCE_SCAN
            && original_problem_assertions.len() <= MAX_OVERRIDE_SOURCE_SCAN;
        let mut source_scan_work = problem_assertions.len();
        let mut pair_specs = if !override_plan_valid {
            Vec::new()
        } else if self.proof_problem_assertion_provenance.is_some() {
            self.provenance_pair_specs(
                &problem_assertions,
                &original_problem_assertions,
                &mut source_scan_work,
                &mut override_plan_valid,
            )
        } else if problem_assertions.len() <= MAX_OVERRIDE_PAIRS {
            problem_assertions
                .iter()
                .enumerate()
                .map(|(index, &canonical)| (canonical, index))
                .collect()
        } else {
            override_plan_valid = false;
            Vec::new()
        };
        surface_pairs::retain_available_surface_pairs(&mut pair_specs, parsed_assertions.len());
        let canonical_plan_is_bounded =
            super::proof_surface_syntax::surface_override_roots_have_bounded_work(
                &self.ctx.terms,
                pair_specs.iter().map(|(canonical, _)| *canonical),
            );
        if !override_plan_valid
            || pair_specs.len() > MAX_OVERRIDE_PAIRS
            || !canonical_plan_is_bounded
            || !self.proof_source_work.spend(
                super::proof_trust_surgery_surface_audit::ProofSourcePass::InputSyntaxOverridePairs,
                pair_specs
                    .iter()
                    .filter_map(|(_, index)| parsed_assertions.get(*index)),
            )
        {
            return None;
        }

        let override_pairs: Vec<(TermId, ay_frontend::command::Term)> = pair_specs
            .drain(..)
            .filter_map(|(canonical, index)| {
                let parsed = parsed_assertions.get(index)?;
                // The native API marker aligns counts; it is not surface text.
                (!matches!(
                    strip_frontend_annotations(parsed),
                    ay_frontend::command::Term::Symbol(name)
                        if name == super::NATIVE_API_ASSERTION_PLACEHOLDER
                ))
                .then(|| (canonical, parsed.clone()))
            })
            .collect();
        let mut term_overrides = HashMap::default();
        for (canonical, parsed) in &override_pairs {
            if !collect_surface_term_overrides(
                &mut self.ctx,
                *canonical,
                parsed,
                &mut term_overrides,
            ) || !surface_override_map_is_bounded(&term_overrides)
            {
                return None;
            }
        }
        Some((override_pairs, term_overrides))
    }

    /// Add exact source spellings for ground instances of authored quantifiers.
    ///
    /// Canonical term rewriting alone is insufficient: `(forall ((x Int)) (> x
    /// 0))` is stored as `< 0 x`, and its exact ground instance is a different
    /// [`TermId`] that the ordinary source walk never visits. A conflicting
    /// rendering for one shared term cannot be represented by the global
    /// printer table, so conflict suppresses external export rather than
    /// emitting a certificate an external checker would reject. The internal
    /// strict-verdict certificate is unaffected.
    fn add_forall_instance_surface_overrides(
        &mut self,
        proof: &Proof,
        override_pairs: &[(TermId, ay_frontend::command::Term)],
        term_overrides: &mut HashMap<TermId, String>,
    ) {
        let parsed_foralls: HashMap<TermId, ay_frontend::command::Term> = override_pairs
            .iter()
            .filter(|(_, parsed)| {
                matches!(
                    strip_frontend_annotations(parsed),
                    ay_frontend::command::Term::Forall(..)
                )
            })
            .cloned()
            .collect();
        let mut failed = false;
        for step in &proof.steps {
            let ProofStep::Step {
                rule: AletheRule::ForallInst,
                clause,
                args,
                ..
            } = step
            else {
                continue;
            };
            let [implication] = clause.as_slice() else {
                continue;
            };
            let TermData::App(Symbol::Named(name), disjuncts) = self.ctx.terms.get(*implication)
            else {
                continue;
            };
            if name != "or" || disjuncts.len() != 2 {
                continue;
            }
            let TermData::Not(quantifier) = self.ctx.terms.get(disjuncts[0]) else {
                continue;
            };
            let Some(parsed) = parsed_foralls.get(quantifier) else {
                continue;
            };
            let instance = disjuncts[1];
            let Some(surface) =
                format_forall_instance_surface(&self.ctx.terms, parsed, args, term_overrides)
            else {
                failed = true;
                break;
            };
            if term_overrides
                .get(&instance)
                .is_some_and(|existing| existing != &surface)
            {
                failed = true;
                break;
            }
            term_overrides.insert(instance, surface);
        }
        if failed {
            self.suppress_unsat_proof_reconstruction();
        }
    }

    /// Drop cosmetic division rewrites that would de-authorize an assume.
    ///
    /// Auxiliary quotient/remainder recognition is name-based: it recognizes
    /// `_mod_q`, `_div_q`, `_divmod_q`, and their `_r` twins. AY's own div/mod
    /// elimination never mints those names; `ay-chc` declares them to the
    /// executor as ordinary client constants. A match can therefore belong to
    /// the authored problem, and its inferred side condition can be derived
    /// rather than authored. Merely asking whether that side condition is an
    /// assertion does not protect the authority boundary.
    ///
    /// What is decisive is the effect: if rewriting changes an `Assume` leaf
    /// into a term absent from the frozen problem obligation, discard the whole
    /// cosmetic rewrite. A correct verdict must never be sacrificed for print
    /// fidelity.
    fn drop_rewrites_that_break_assumption_authority(
        &mut self,
        proof: &Proof,
        rewrites: &mut HashMap<TermId, TermId>,
    ) {
        if rewrites.is_empty() {
            return;
        }
        let obligation = self.problem_assertions_for_strict_proof();
        let mut cache: HashMap<TermId, TermId> = HashMap::default();
        let breaks_authorization = proof.steps.iter().any(|step| {
            let ProofStep::Assume(term) = step else {
                return false;
            };
            let rewritten = Self::rewrite_term(&mut self.ctx.terms, *term, rewrites, &mut cache);
            rewritten != *term && !obligation.contains(&rewritten)
        });
        if breaks_authorization {
            rewrites.clear();
        }
    }
}
