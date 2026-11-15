// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Bounded planning for authenticated proof surface rewrites.

/// Why the override plan declined, as far as the derivation behind it is
/// concerned (#certify-before-presentation).
pub(in crate::executor) struct OverridePlanDecline {
    /// Every canonical root the plan refused was refused for its binder
    /// SHAPE alone (no size, visit or symbol refusal, no ceiling), and the
    /// largest of them expands to at most [`SHAPE_ONLY_MAX_EXPANDED_NODES`]
    /// nodes. The bound then says nothing about the size of the terms a
    /// derivation over these roots carries, so the derivation is kept for
    /// certification and only the document is withheld. Any other exit is a
    /// SIZE statement — measured on QF_UFLRA cpachecker `minepump_spec4_
    /// product58` (a root expanding to 674,862,507 nodes), strict-checking the
    /// kept derivation ran the process out of memory, `unsat` 7.2 s ->
    /// `memout` — and keeps the one-line poison.
    pub(in crate::executor) shape_only: bool,
}

/// The per-root expansion a shape-only decline admits: the visit bound the
/// canonical work probe itself prices a root against
/// (`canonical_term_work_probe`). Measured on the D7 list: every binder-veto
/// decline is at most 20,201 expanded nodes, every size decline at least
/// 209,605.
const SHAPE_ONLY_MAX_EXPANDED_NODES: u64 = 100_000;

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

    /// Record one override-plan exit and decline.
    ///
    /// #unbounded-population. The census stays write-only: nothing
    /// downstream reads `last_unbounded_census` to decide anything. The
    /// plan's own [`OverridePlanDecline`] verdict is computed here, from the
    /// counts this exit took.
    fn decline_override_plan<T>(
        &mut self,
        mut census: crate::executor::OverridePlanCensus,
        exit: crate::executor::OverridePlanExit,
    ) -> Result<T, OverridePlanDecline> {
        census.exit = Some(exit);
        let shape_only = exit == crate::executor::OverridePlanExit::CanonicalRootsUnbounded
            && census.canonical_roots_refused_shape > 0
            && census.canonical_roots_refused_size == 0
            && census.canonical_roots_refused_symbol == 0
            && census.largest_canonical.expanded_nodes <= SHAPE_ONLY_MAX_EXPANDED_NODES;
        self.last_unbounded_census = Some(crate::executor::UnboundedCensus::OverridePlan(census));
        Err(OverridePlanDecline { shape_only })
    }

    pub(in crate::executor) fn prepare_surface_overrides(
        &mut self,
    ) -> Result<
        (
            Vec<(TermId, ay_frontend::command::Term)>,
            HashMap<TermId, String>,
        ),
        OverridePlanDecline,
    > {
        // #unbounded-population. Six exits below decline under ONE tag, and
        // the census could not say which. Record what each one saw. Write-only:
        // every decision below is taken exactly as it was, and a `None` exit is
        // still a `None` exit.
        let mut census = crate::executor::OverridePlanCensus {
            has_provenance: self.proof_problem_assertion_provenance.is_some(),
            ..Default::default()
        };
        let mut pair_specs = self.surface_override_pair_specs(&mut census)?;
        let parsed_assertions: &[ay_frontend::command::Term] = self.ctx.assertions_parsed();
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
        self.collect_surface_override_spellings(override_pairs, census)
    }

    /// The pair specs the override plan will render, or `None` at one of the
    /// four exits that decline before any spelling is collected.
    fn surface_override_pair_specs(
        &mut self,
        census: &mut crate::executor::OverridePlanCensus,
    ) -> Result<Vec<(TermId, usize)>, OverridePlanDecline> {
        let problem_assertions = self.proof_problem_assertions();
        let original_problem_assertions = self.proof_original_problem_assertions();
        let parsed_assertions: &[ay_frontend::command::Term] = self.ctx.assertions_parsed();
        census.problem_assertions = u32::try_from(problem_assertions.len()).unwrap_or(u32::MAX);
        census.original_problem_assertions =
            u32::try_from(original_problem_assertions.len()).unwrap_or(u32::MAX);
        census.parsed_assertions = u32::try_from(parsed_assertions.len()).unwrap_or(u32::MAX);
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
        let parsed_len = self.ctx.assertions_parsed().len();
        surface_pairs::retain_available_surface_pairs(&mut pair_specs, parsed_len);
        census.source_scan_work = source_scan_work as u64;
        census.pair_specs = u32::try_from(pair_specs.len()).unwrap_or(u32::MAX);
        let canonical_plan_is_bounded =
            super::proof_surface_syntax::surface_override_roots_have_bounded_work(
                &self.ctx.terms,
                pair_specs.iter().map(|(canonical, _)| *canonical),
            );
        if !override_plan_valid {
            return self
                .decline_override_plan(*census, crate::executor::OverridePlanExit::ScanCeiling);
        }
        if pair_specs.len() > MAX_OVERRIDE_PAIRS {
            return self
                .decline_override_plan(*census, crate::executor::OverridePlanExit::PairCeiling);
        }
        if !canonical_plan_is_bounded {
            crate::executor::proof::census_canonical_roots(
                &self.ctx.terms,
                census,
                pair_specs.iter().map(|(canonical, _)| *canonical),
            );
            return self.decline_override_plan(
                *census,
                crate::executor::OverridePlanExit::CanonicalRootsUnbounded,
            );
        }
        census.envelope_remaining = self.proof_source_work.remaining() as u64;
        let parsed_assertions: &[ay_frontend::command::Term] = self.ctx.assertions_parsed();
        if self.proof_source_work.spend(
            super::proof_trust_surgery_surface_audit::ProofSourcePass::InputSyntaxOverridePairs,
            pair_specs
                .iter()
                .filter_map(|(_, index)| parsed_assertions.get(*index)),
        ) {
            return Ok(pair_specs);
        }
        census.envelope_charge = super::proof_trust_surgery_surface_audit::surface_pass_work(
            pair_specs
                .iter()
                .filter_map(|(_, index)| parsed_assertions.get(*index)),
        )
        .map(|work| work as u64);
        self.decline_override_plan(*census, crate::executor::OverridePlanExit::EnvelopeRefused)
    }

    /// Collect the exact source spelling of every pair, or decline at one of
    /// the two exits the collector owns.
    fn collect_surface_override_spellings(
        &mut self,
        override_pairs: Vec<(TermId, ay_frontend::command::Term)>,
        mut census: crate::executor::OverridePlanCensus,
    ) -> Result<
        (
            Vec<(TermId, ay_frontend::command::Term)>,
            HashMap<TermId, String>,
        ),
        OverridePlanDecline,
    > {
        let mut term_overrides = HashMap::default();
        for (pair_index, (canonical, parsed)) in override_pairs.iter().enumerate() {
            let collected = collect_surface_term_overrides(
                &mut self.ctx,
                *canonical,
                parsed,
                &mut term_overrides,
            );
            if !collected || !surface_override_map_is_bounded(&term_overrides) {
                let exit = if collected {
                    crate::executor::OverridePlanExit::OverrideMapUnbounded
                } else {
                    crate::executor::OverridePlanExit::CollectorRefused
                };
                census.collector_refused_pair = Some(u32::try_from(pair_index).unwrap_or(u32::MAX));
                census.overrides = u32::try_from(term_overrides.len()).unwrap_or(u32::MAX);
                census.override_bytes = term_overrides.values().fold(0u64, |bytes, spelling| {
                    bytes.saturating_add(spelling.len() as u64)
                });
                crate::executor::proof::census_canonical_roots(
                    &self.ctx.terms,
                    &mut census,
                    std::iter::once(*canonical),
                );
                return self.decline_override_plan(census, exit);
            }
        }
        Ok((override_pairs, term_overrides))
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
        let debug = ay_core::misc_cli_flags().debug_cert;
        for (index, step) in proof.steps.iter().enumerate() {
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
                // A census line, not a decision: which `forall_inst` steps
                // this pass cannot re-spell, and why. The sko_ex sibling of
                // the eighth false green shipped a canonical instance under an
                // authored quantifier because the step's quantifier was not
                // an authored root here.
                if debug {
                    ay_core::safe_eprintln!(
                        "c !! forall-inst surface at t{index}: quantifier is not an authored root, no instance spelling"
                    );
                }
                continue;
            };
            let instance = disjuncts[1];
            let Some(surface) =
                format_forall_instance_surface(&self.ctx.terms, parsed, args, term_overrides)
            else {
                if debug {
                    ay_core::safe_eprintln!(
                        "c !! forall-inst surface at t{index}: authored body does not render under the substitution"
                    );
                }
                failed = true;
                break;
            };
            if term_overrides
                .get(&instance)
                .is_some_and(|existing| existing != &surface)
            {
                if debug {
                    ay_core::safe_eprintln!(
                        "c !! forall-inst surface at t{index}: instance already spelled another way"
                    );
                }
                failed = true;
                break;
            }
            if debug {
                ay_core::safe_eprintln!("c !! forall-inst surface at t{index}: {surface}");
            }
            term_overrides.insert(instance, surface);
        }
        if failed {
            self.suppress_unsat_proof_reconstruction();
            // #evidence-stage-3, second pass.
            self.record_proof_decline(
                crate::executor::ProofDeclineMechanism::ForallInstanceSurfaceConflict,
            );
        }
    }

    /// Drop cosmetic division rewrites that would de-authorize an assume.
    ///
    /// Auxiliary quotient/remainder recognition is name-based: it recognizes
    /// `_mod_q`, `_div_q`, `_divmod_q`, and their `_r` twins. AY's own div/mod
    /// elimination mints `_divmod_q`/`_divmod_r` (its purification is derived
    /// by `proof_divmod_def`, from the mint-site record, not here), and
    /// `ay-chc` declares such names to the executor as ordinary client
    /// constants. A match can therefore belong to the authored problem, and
    /// its inferred side condition can be derived rather than authored.
    /// Merely asking whether that side condition is an assertion does not
    /// protect the authority boundary.
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
