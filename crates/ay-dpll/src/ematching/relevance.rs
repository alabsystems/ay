// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Relevance ranking for E-matching instances (the "middle gear").
//!
//! # The problem this solves
//!
//! A raw E-matching call emits at most `EMatchingConfig::max_total` (10 000)
//! fresh instances. A ranked admission batch can be larger after it merges
//! carried work; measured SQ Equality batches contain 7 500-16 300 candidates.
//! Admitting the whole batch before the next ground solve spends the budget
//! inside the EUF core (`incremental_propagate` / `CongruenceTable`) rather than
//! in the quantifier engine. The engine had no middle gear: it either matched
//! nothing, or matched everything and drowned.
//!
//! # What this module does
//!
//! It ranks the instances a round produced and lets the caller admit a bounded
//! top-K, CARRYING the remainder forward (see `QuantifierManager::carry_*`)
//! instead of discarding them. The carry queue counts as deferred work, so
//! completeness degrades gracefully and visibly rather than silently.
//!
//! Ranking is deliberately bypassed while the executor's mandatory proof
//! tracker is recording. A carried entry does not yet retain the authenticated
//! quantifier and binding needed to replay a strict `forall_inst`; filtering in
//! that posture could therefore leave an untranslatable UNSAT certificate.
//! Certified public solves admit the whole batch even when the CLI switch is
//! set. On the public path, ranking can currently engage only under
//! competition proof shedding, where the internal tracker is disabled.
//!
//! # Soundness
//!
//! Withholding an instance only ever REMOVES a conjunct from the ground
//! problem, so it can never manufacture a refutation: a wrong `unsat` is
//! structurally impossible here. The risk is the other direction — a `sat`
//! read off a problem that is missing constraints. That is blocked because a
//! non-empty carry queue makes [`crate::quantifier_manager::QuantifierManager::has_deferred`]
//! true (the same gate the cost-deferred queue and the demand lane use), and
//! `classify_quantifier_result` maps `Sat && has_deferred` to
//! `Unknown(QuantifierDeferred)`. The interleaved seam additionally reports
//! `reached_limit` for the round in which it withheld.
//!
//! # Scoring
//!
//! Structural signals cost one bounded DAG walk per instance. The optional
//! model signal additionally evaluates the term against the caller's existing
//! model; it does not launch another solve.
//!
//! - `reuse`: fraction of the instance's subterms that already existed before
//!   this round (`TermId < watermark`). An instance built entirely out of
//!   terms the ground solver already reasons about can close a conflict; one
//!   built out of freshly minted terms mostly grows the E-graph.
//! - `fresh`: how many NEW ground terms the instance introduces (penalty) —
//!   these are exactly the terms that feed the next round's flood.
//! - `depth`/`size`: term-depth and node count (penalty).
//! - `generation`: instantiation-chain depth from `GenerationTracker`
//!   (penalty) — a generation-4 instance is 4 instantiations away from the
//!   input problem.
//! - `model`: when the caller has a model, whether the instance is FALSIFIED
//!   by it. A falsified instance is likely to change the ground solver's state
//!   (this is the same signal `promote_deferred_conflicts` uses to promote a
//!   deferred instance), so it receives a strong bonus; an instance the current
//!   model already satisfies receives a strong penalty.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::TermData;
use ay_core::{TermId, TermStore};

/// How the caller's current model evaluates an instance.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ModelStanding {
    /// The current model falsifies the instance: asserting it forces a change.
    Violated,
    /// The current model already satisfies the instance.
    Satisfied,
    /// No model, or the model does not determine the instance.
    Unknown,
}

/// Tunables for relevance-ranked admission.
#[derive(Clone, Copy, Debug)]
pub(crate) struct RelevanceConfig {
    /// Requested switch, DEFAULT OFF — see the measurement note on
    /// [`relevance_config`]. When `false`, ranking and filtering are bypassed
    /// and the caller preserves the pre-existing admitted terms and their
    /// order, although the admission wrapper and bookkeeping still run. Proof
    /// authority may also force unfiltered admission when this is `true`.
    pub(crate) enabled: bool,
    /// Maximum instances admitted into `ctx.assertions` per round.
    pub(crate) admit_per_round: usize,
    /// Rounds producing at most this many novel instances are admitted whole,
    /// with no scoring pass at all. This is the blast-radius seam: a problem
    /// that never floods preserves the pre-existing admission semantics.
    pub(crate) flood_threshold: usize,
    /// Node budget for the per-instance feature walk.
    pub(crate) max_walk: usize,
    /// Use the model signal when a model is available.
    pub(crate) use_model_signal: bool,
    /// Score bonus added per round an instance has waited in the carry queue.
    /// This monotonically raises its priority and reduces starvation within the
    /// bounded round/deadline budget; it cannot guarantee eventual admission.
    pub(crate) age_bonus: f64,
    /// Per-round admission trace on stderr (`--quant-relevance-debug=1`).
    pub(crate) debug: bool,
}

impl Default for RelevanceConfig {
    fn default() -> Self {
        Self {
            enabled: false,
            admit_per_round: 512,
            flood_threshold: 512,
            max_walk: 256,
            use_model_signal: true,
            age_bonus: 0.5,
            debug: false,
        }
    }
}

/// Process-wide relevance configuration, read once from CLI-carried flags.
///
/// `--quant-relevance true` requests the layer; `--quant-relevance-k` /
/// `--quant-relevance-min` / `--quant-relevance-model` tune it (B79). Mandatory
/// proof recording still forces unfiltered admission; see the module policy.
///
/// # Why the default is OFF (measured 2026-08-19)
///
/// These measurements predate the proof-authority bypass and justify the
/// default-OFF policy itself. Reproducing ranked admission in the current
/// implementation requires a proof-shedding posture.
///
/// The layer does what it claims — over 32 stratified SQ Equality /
/// Equality_LinearArith instances at 60s it cut the interleaved ground-resolve
/// time from 211s to 75s, and the flood is real (20/32 files ranked, up to
/// 195 656 cumulative withholding events on one). It did not convert: solved
/// was 10/32 both ways, with no verdict changes. Pushing harder did not help —
/// K ∈ {16, 64, 512, 4096} all solved 0/22 on the flooded subset, and at
/// K=16 (16-256 instances admitted instead of 8 000-28 000) the same files
/// still fail to close, three of them now on the deterministic budget.
///
/// So the ground solves on this population are NOT instance-count-bound:
/// shrinking the pile a thousandfold does not make them decide. The cost is
/// real and this removes most of it, but the budget it frees does not buy a
/// verdict here, and on a tight deadline the extra rounds cost one solve
/// (`dl_traverse_postcondition_of_dl_traverse_24_1` at 12s, 11.7s -> 13.8s).
/// Default OFF until a population is found where the freed budget converts.
pub(crate) fn relevance_config() -> &'static RelevanceConfig {
    static CONFIG: std::sync::OnceLock<RelevanceConfig> = std::sync::OnceLock::new();
    CONFIG.get_or_init(|| {
        let d = RelevanceConfig::default();
        // B79: CLI-carried (--quant-relevance*, MiscCliFlags); env retired.
        let f = ay_core::misc_cli_flags();
        let enabled = f.quant_relevance.unwrap_or(d.enabled);
        let admit_per_round = f.quant_relevance_k.unwrap_or(d.admit_per_round).max(1);
        let flood_threshold = f.quant_relevance_min.unwrap_or(d.flood_threshold);
        let use_model_signal = f.quant_relevance_model.unwrap_or(d.use_model_signal);
        RelevanceConfig {
            enabled,
            admit_per_round,
            // An admission budget below the flood threshold would filter rounds
            // it then admits whole; keep the two consistent.
            flood_threshold: flood_threshold.max(admit_per_round),
            use_model_signal,
            debug: f.quant_relevance_debug,
            ..d
        }
    })
}

/// Structural features of one instance, from a single bounded DAG walk.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct InstanceFeatures {
    /// Distinct subterms visited (capped at `max_walk`).
    pub(crate) size: u32,
    /// Distinct subterms minted at or after the round watermark.
    pub(crate) fresh: u32,
    /// Maximum nesting depth reached.
    pub(crate) depth: u32,
}

impl InstanceFeatures {
    /// Fraction of the instance built from terms that predate this round.
    fn reuse(self) -> f64 {
        if self.size == 0 {
            return 0.0;
        }
        f64::from(self.size - self.fresh) / f64::from(self.size)
    }
}

/// Walk `inst` and collect its structural features.
///
/// `watermark` is `TermStore::len()` captured BEFORE the round that produced
/// `inst`: every subterm with a smaller id predates the round. The walk is
/// iterative (instances can be deep) and node-capped, so this is O(min(size,
/// max_walk)) per instance using a visited set and an explicit work stack.
pub(crate) fn instance_features(
    terms: &TermStore,
    inst: TermId,
    watermark: u32,
    max_walk: usize,
) -> InstanceFeatures {
    let mut visited: HashSet<TermId> = HashSet::default();
    let mut stack: Vec<(TermId, u32)> = vec![(inst, 0)];
    let mut f = InstanceFeatures::default();
    while let Some((t, d)) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        f.size += 1;
        if t.0 >= watermark {
            f.fresh += 1;
        }
        f.depth = f.depth.max(d);
        if visited.len() >= max_walk {
            break;
        }
        match terms.get(t) {
            TermData::App(_, args) => {
                for &a in args {
                    stack.push((a, d + 1));
                }
            }
            TermData::Not(a) => stack.push((*a, d + 1)),
            TermData::Ite(c, t1, e) => {
                stack.push((*c, d + 1));
                stack.push((*t1, d + 1));
                stack.push((*e, d + 1));
            }
            TermData::Let(bindings, body) => {
                for (_, v) in bindings {
                    stack.push((*v, d + 1));
                }
                stack.push((*body, d + 1));
            }
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                stack.push((*body, d + 1));
            }
            TermData::Const(_) | TermData::Var(_, _) => {}
            _ => {}
        }
    }
    f
}

/// Relevance score; higher is admitted first.
///
/// Deterministic pure function of its inputs — no clock, no allocation, no
/// global state — so a re-run of the same solve ranks identically.
pub(crate) fn score_instance(f: InstanceFeatures, generation: u32, standing: ModelStanding) -> f64 {
    let model_term = match standing {
        // Strongly prefer an instance that can move the ground solver off its
        // current model. Structural and generation penalties still participate.
        ModelStanding::Violated => 4.0,
        ModelStanding::Unknown => 0.0,
        // Already satisfied — asserting it changes nothing in the current
        // model. Penalized, not dropped: the model can change across rounds.
        ModelStanding::Satisfied => -4.0,
    };
    model_term + 2.0 * f.reuse()
        - 0.25 * f64::from(f.fresh + 1).ln()
        - 0.10 * f64::from(f.depth)
        - 0.50 * f64::from(generation)
        - 0.10 * f64::from(f.size + 1).ln()
}

/// One instance with its score, as ranked and carried.
#[derive(Clone, Copy, Debug)]
pub(crate) struct ScoredInstance {
    pub(crate) inst: TermId,
    pub(crate) score: f64,
    /// The instance is a ground instance of an UNCONDITIONALLY-asserted
    /// `forall`, i.e. it belongs in `active_support_axioms` once (and only
    /// once) it is actually asserted. Carried alongside the instance so a
    /// later flush can register it with the same provenance the producing
    /// round would have.
    pub(crate) support_root: bool,
    /// Rounds this instance has spent in the carry queue.
    pub(crate) age: u32,
}

/// Rank `candidates` and split them into (admitted, carried).
///
/// Ordering is by score descending, ties broken by ascending `TermId`, so the
/// split is a deterministic function of the candidate set.
pub(crate) fn split_top_k(
    mut candidates: Vec<ScoredInstance>,
    k: usize,
) -> (Vec<ScoredInstance>, Vec<ScoredInstance>) {
    candidates.sort_by(|a, b| {
        b.score
            .total_cmp(&a.score)
            .then_with(|| a.inst.0.cmp(&b.inst.0))
    });
    if candidates.len() <= k {
        return (candidates, Vec::new());
    }
    let carried = candidates.split_off(k);
    (candidates, carried)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::term::Symbol;
    use ay_core::Sort;

    #[test]
    fn the_layer_ships_default_off() {
        // Pins the 2026-08-19 measurement decision: the ranker cuts ground-solve
        // time but converts no solves on SQ Equality / Equality_LinearArith, and
        // costs one solve at a 12s deadline. It stays opt-in
        // (`--quant-relevance=1`) until a population is found where the freed
        // budget buys a verdict. Flipping this default is a measurement claim.
        assert!(!RelevanceConfig::default().enabled);
    }

    #[test]
    fn features_count_fresh_terms_against_the_watermark() {
        let mut terms = TermStore::new();
        let a = terms.mk_app(Symbol::named("a"), Vec::<TermId>::new(), Sort::Int);
        let watermark = u32::try_from(terms.len()).expect("small store");
        let fa = terms.mk_app(Symbol::named("f"), vec![a], Sort::Int);
        let ffa = terms.mk_app(Symbol::named("f"), vec![fa], Sort::Int);
        let f = instance_features(&terms, ffa, watermark, 256);
        // a predates the round; f(a) and f(f(a)) are fresh.
        assert_eq!(f.size, 3);
        assert_eq!(f.fresh, 2);
        assert_eq!(f.depth, 2);
    }

    #[test]
    fn reuse_beats_freshness_at_equal_generation() {
        let reusing = InstanceFeatures {
            size: 6,
            fresh: 0,
            depth: 2,
        };
        let minting = InstanceFeatures {
            size: 6,
            fresh: 5,
            depth: 2,
        };
        assert!(
            score_instance(reusing, 1, ModelStanding::Unknown)
                > score_instance(minting, 1, ModelStanding::Unknown)
        );
    }

    #[test]
    fn a_violated_instance_outranks_a_satisfied_one() {
        let f = InstanceFeatures {
            size: 40,
            fresh: 30,
            depth: 9,
        };
        let g = InstanceFeatures {
            size: 3,
            fresh: 0,
            depth: 1,
        };
        // Even a big, deep, mostly-fresh instance that the model FALSIFIES
        // outranks a small tidy one the model already satisfies: only the
        // former can change the ground solver's state.
        assert!(
            score_instance(f, 2, ModelStanding::Violated)
                > score_instance(g, 0, ModelStanding::Satisfied)
        );
    }

    #[test]
    fn lower_generation_ranks_first() {
        let f = InstanceFeatures {
            size: 5,
            fresh: 2,
            depth: 2,
        };
        assert!(
            score_instance(f, 1, ModelStanding::Unknown)
                > score_instance(f, 4, ModelStanding::Unknown)
        );
    }

    #[test]
    fn split_is_deterministic_and_carries_the_remainder() {
        let mk = |id: u32, score: f64| ScoredInstance {
            inst: TermId::new(id),
            score,
            support_root: false,
            age: 0,
        };
        let cands = vec![mk(3, 1.0), mk(1, 5.0), mk(2, 5.0), mk(4, -1.0)];
        let (admitted, carried) = split_top_k(cands.clone(), 2);
        assert_eq!(
            admitted.iter().map(|s| s.inst.0).collect::<Vec<_>>(),
            vec![1, 2],
            "ties break on ascending TermId"
        );
        assert_eq!(
            carried.iter().map(|s| s.inst.0).collect::<Vec<_>>(),
            vec![3, 4],
            "nothing is discarded — the remainder is carried in rank order"
        );
        // Same input, same split.
        let (admitted2, carried2) = split_top_k(cands, 2);
        assert_eq!(
            admitted.iter().map(|s| s.inst.0).collect::<Vec<_>>(),
            admitted2.iter().map(|s| s.inst.0).collect::<Vec<_>>()
        );
        assert_eq!(carried.len(), carried2.len());
    }

    #[test]
    fn k_at_or_above_candidate_count_admits_everything() {
        let mk = |id: u32| ScoredInstance {
            inst: TermId::new(id),
            score: f64::from(id),
            support_root: false,
            age: 0,
        };
        let (admitted, carried) = split_top_k(vec![mk(1), mk(2)], 8);
        assert_eq!(admitted.len(), 2);
        assert!(carried.is_empty());
    }
}
