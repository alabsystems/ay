// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The MANDATORY incremental-matching differential canary (feature
//! `ematching-differential`). It recomputes the firewall-critical
//! `instantiated_quantifiers` set with a FULL per-round re-match (every
//! candidate, no new-candidate skip, no epoch replay) over the SAME quantifiers
//! and working eqclasses, and asserts it equals the incrementally computed set.
//! A divergence would mean the new-candidate skip dropped a match the full path
//! finds (the only way incremental matching could change a result), so this
//! MUST hold. It is feature-gated so production builds keep the perf win; the
//! verification suite enables it.
//!
//! It runs only on a round that completed normally: the instantiation budget
//! limits (`max_total`/`max_per_quantifier`) and the deadline/`should_stop`
//! break out of the loop early and skip the marking for later quantifiers,
//! which the unlimited full recomputation would still mark — a benign, expected
//! difference under truncation, not a matching divergence.

use super::*;

/// The canary's failure message.
pub(super) const DIVERGENCE: &str = "incremental matching diverged from full re-match: \
     instantiated_quantifiers differs (new-candidate skip / epoch replay dropped or added a match)";

/// Differential-canary helper: recompute the `instantiated_quantifiers` set the
/// way the HEAD full-rematch path would — matching EVERY candidate for every
/// quantifier (no new-candidate skip, no epoch replay), marking a quantifier
/// instantiated for any binding whose cost is `<= lazy_threshold`, and applying
/// the same primary/fallback phase rule. Used only under the
/// `ematching-differential` feature to assert the incremental path is identical.
///
/// It applies the incremental loop's eligibility too, which is soundness policy
/// rather than matching: an existential is never instantiated, and a forall
/// the assertions do not entail is refused or only guarded, so neither is ever
/// marked. Without it the canary reported every such quantifier as a dropped
/// match.
pub(super) fn compute_full_instantiated_quantifiers(
    terms: &TermStore,
    quantifiers: &[TermId],
    entailed_foralls: &HashSet<TermId>,
    tracker: &GenerationTracker,
    config: &EMatchingConfig,
    eqclasses_opt: Option<&EqualityClasses>,
    index: &TermIndex,
) -> HashSet<TermId> {
    let mut instantiated: HashSet<TermId> = HashSet::default();
    for &quant in quantifiers {
        let quantifier_weight = effective_quantifier_weight(terms, quant, config);
        let trigger_groups = extract_patterns_with_fallback(terms, quant);
        let var_sorts: Vec<Sort> = match terms.get(quant) {
            TermData::Forall(v, _, _) if entailed_foralls.contains(&quant) => {
                v.iter().map(|(_, sort)| sort.clone()).collect()
            }
            _ => continue,
        };
        let mut quantifier_instantiated_this_round = false;
        for (phase_idx, groups) in [&trigger_groups.primary, &trigger_groups.fallback]
            .iter()
            .enumerate()
        {
            if phase_idx == 1 && quantifier_instantiated_this_round {
                break;
            }
            for trigger_group in *groups {
                let bindings: Vec<Vec<TermId>> = if trigger_group.patterns.len() == 1 {
                    let pattern = &trigger_group.patterns[0];
                    index
                        .get_by_symbol(pattern.symbol.name())
                        .iter()
                        .filter_map(|&gt| {
                            match_pattern(terms, pattern, gt, &var_sorts, eqclasses_opt)
                        })
                        .collect()
                } else {
                    match_multi_trigger(
                        terms,
                        &trigger_group.patterns,
                        index,
                        &var_sorts,
                        eqclasses_opt,
                    )
                };
                for binding in bindings {
                    let cost = tracker.instantiation_cost(&binding, quantifier_weight);
                    if cost > config.lazy_threshold {
                        continue;
                    }
                    instantiated.insert(quant);
                    quantifier_instantiated_this_round = true;
                }
            }
        }
    }
    instantiated
}
