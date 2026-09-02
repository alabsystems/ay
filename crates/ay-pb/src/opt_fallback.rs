// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! THE certified-optimization portfolio fallback — one definition, both frontends.
//!
//! # Why this module exists
//!
//! `try_opt_lin_cert_fallback` was written twice: once in `crates/ay/src/cmd_pb.rs`
//! (the `ay` CLI) and once in `crates/ay-pb/src/bin/ay.rs` (the competition
//! `ay-pb` binary). The two copies carried the SAME prose, the same candidate
//! widening, the same certificate chain — and drifted anyway, in the only way
//! that matters: the SEARCH each one runs.
//!
//! That drift has now cost this project a headline TWICE. The first time, the
//! CLI's copy of the certificate ladder still named two rungs while the
//! competition binary's had grown to eight, so six shipped emitters were dead on
//! one of the two frontends. The fix then was the fix now: ONE library
//! definition (`ay_pb::proof::certify_opt_lin_any_interruptible`) called from
//! every production site, with no second copy left to drift. The second time,
//! a patch taught the CLI's copy to route eligible instances to the parallel
//! primal and left the `ay-pb` copy calling the sequential portfolio
//! unconditionally — so a route-gap fix measured as "10 of 12 pairs" was really
//! 5 of 12: 5/6 on `ay pb solve` and 0/6 on `ay-pb`.
//!
//! So the policy does not live in either binary any more. Everything that
//! decides WHAT IS SEARCHED, WHICH CANDIDATE IS ADMITTED and WHICH CERTIFICATE
//! IS BUILT is here, once. The binaries keep only their own I/O: writing the
//! proof to their own temp path, committing it with their own atomic-commit
//! helper, caching the incumbent in their own `Mutex`, and converting the
//! outcome into their own result type. There is nothing left in either caller
//! that a future change could teach one frontend and not the other.
//!
//! # Where the drift actually was
//!
//! Beyond the search route, the two copies disagreed on their STOP PREDICATE:
//! `ay-pb` also stopped on `ay_sys::process_memory_exceeded()`, the CLI did
//! not. This module unifies on the `ay-pb` spelling, which is the fail-closed
//! one — under memory pressure the alternative to declining is being SIGKILLed
//! with the optimum already in hand (exit 137, no `s` line at all), which is
//! precisely the failure the governor bucket of the residual census is made of.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use ay_pb_core::{PbExactSolution, PbInstance, PbObjective, PbSolution, PbStatus};

use crate::portfolio::{self, PbPortfolioPhaseTimings};
use crate::proof::{certify_opt_lin_any_interruptible, certify_reserve, OptLinCertRoute};

/// What [`run_opt_lin_cert_fallback`] concluded.
///
/// `Declined` carries the phase timings when there were any to carry, so a
/// caller can still report the portfolio's phase breakdown for a run that
/// produced no certificate.
pub enum OptLinCertFallback {
    /// No certificate. Either the objective is not linear (this fallback does
    /// not apply), no candidate optimum survived the checked upgrade gate, or
    /// every rung of the certificate chain declined.
    Declined {
        timings: Option<PbPortfolioPhaseTimings>,
    },
    /// A VeriPB proof was built. The caller writes and commits it.
    Certified {
        /// The proof text, ready to write.
        pbp: String,
        /// Which rung produced it (diagnostics only).
        route: OptLinCertRoute,
        /// `OptimumFound` with the certified objective and its incumbent.
        solution: PbSolution,
        timings: Option<PbPortfolioPhaseTimings>,
    },
}

/// Whether the certified-optimization fallback's PRIMAL phase may use the
/// PARALLEL portfolio.
///
/// # This is a determinism decision, not a performance one
///
/// It is `false`, and the reason is a guarantee this repository has already
/// shipped and published: **the emitted certificate bytes do not depend on
/// machine load**. That guarantee is not incidental. It is why every floor rung
/// is capped by a deterministic WORK COUNT rather than a clock —
/// `lp_dual_floor::MAX_DUAL_SOLVE_POLLS` says it in as many words ("a
/// clock-based cap would make the emitted bytes depend on machine load"), and
/// `odd_cycle_cover::packing::Limits` says it again. The plain optimization
/// path's own comment records the same invariant from the other side: "Proof
/// mode never reaches here."
///
/// The parallel coordinator is built on FIRST-PROVEN-WINS. It returns the first
/// worker to reach a definitive verdict and stops the rest, so WHICH optimal
/// model comes back is decided by a race. Two workers can both be right and
/// hand back different models of the same optimum; the certificate embeds the
/// model, so the bytes move. There is no cheap repair: canonicalising the model
/// after the fact (greedy descent to a lexicographic fixpoint) is deterministic
/// only GIVEN a starting model, and different starting models reach different
/// fixpoints, so it is not canonical at all. A genuinely canonical model costs
/// a fresh complete search per variable.
///
/// # What is given up, measured, and why it was not worth it
///
/// The win this forgoes is real and was measured, on
/// `normalized-hw32-vm85p-opt.opb.negationfix.opb`, one 60 s budget each:
/// the sequential primal ends at `o 30 / s SATISFIABLE`, the parallel one
/// reaches `o 27 / s OPTIMUM FOUND` and the shipped `lp_dual_floor` emitter
/// then certifies `BOUNDS 27 <= obj <= 27`. Six instances of the residual
/// census's route-gap bucket are of that shape.
///
/// It is still not worth it, because the win is not one strategy that could be
/// lifted onto the deterministic path — it is the concurrency itself. Measured
/// on the same instance and binary, sweeping the worker budget: 1, 2, 3, 4, 5
/// and 6 workers all end `s SATISFIABLE` at the budget; 8 workers reach
/// `s OPTIMUM FOUND` in 5.0 s; 12 reach it in 0.20 s. A result that needs
/// SEVEN cooperating workers, and whose time falls 25-fold between eight and
/// twelve, is a result that depends on how much of the machine is free — which
/// is the definition of the thing the guarantee forbids.
///
/// So the certified path takes the smaller, honest win. Re-enabling this is a
/// one-line change plus a corpus determinism sweep that stays green; it is
/// deliberately left as a decision with a name rather than a condition buried
/// in a call site, so the next person to want it has to answer this comment.
#[must_use]
pub fn proof_path_uses_parallel_primal(_instance: &PbInstance) -> bool {
    false
}

/// Run the portfolio, pick a certifiable optimum candidate, and build its
/// VeriPB proof. Returns the proof for the caller to commit; writes nothing.
///
/// `on_improve` is the CALLER'S streaming-improvement callback, not a stub.
/// Passing `|_, _| {}` here is how the CLI once dropped every feasible
/// incumbent this phase found and reported `s UNKNOWN` for instances it had a
/// verified model for (measured on a 74-instance sample: 0 `s SATISFIABLE` and
/// 71 `s UNKNOWN` in proof mode, against 37 / 25 for the competition binary).
/// The callback re-verifies each model and only advances the bar on a VERIFIED
/// construction, so it can only publish answers AY already has.
pub fn run_opt_lin_cert_fallback(
    instance: &Arc<PbInstance>,
    objective: &PbObjective,
    timeout_dur: Option<Duration>,
    start: Instant,
    term_flag: &AtomicBool,
    best_solution: &Mutex<Option<PbExactSolution>>,
    on_improve: &mut dyn FnMut(i128, &[bool]),
) -> OptLinCertFallback {
    let instance_ref: &PbInstance = instance;

    // The OPT-LIN-CERT helpers only handle single-literal (linear) objective
    // terms.
    if objective.terms.iter().any(|term| term.lits.len() != 1) {
        return OptLinCertFallback::Declined { timings: None };
    }

    // Stop the portfolio SHORT of the caller's deadline: the certification
    // stage behind it needs a slice, and it used to be handed the deadline the
    // portfolio had already run to. `should_stop` below still runs to the FULL
    // timeout (absolute deadlines), so time the portfolio does not use rolls
    // into certification rather than being lost.
    let portfolio_timeout = timeout_dur.map(|timeout| {
        let remaining = timeout.saturating_sub(start.elapsed());
        timeout.saturating_sub(certify_reserve(remaining))
    });

    // Phase timings are a SEQUENTIAL-only artefact (the parallel coordinator
    // reports none), so the reported field goes `None` on the parallel route
    // exactly as the plain optimization path already does — never a zeroed
    // struct, which would read as "measured, all phases free".
    let (portfolio_solution, timings) = if proof_path_uses_parallel_primal(instance_ref) {
        let solution = portfolio::solve_optimization_portfolio_parallel(
            instance,
            objective,
            portfolio_timeout,
            start,
            term_flag,
            on_improve,
        );
        (solution, None)
    } else {
        let result = portfolio::solve_optimization_portfolio_with_timings(
            instance_ref,
            objective,
            portfolio_timeout,
            start,
            term_flag,
            on_improve,
        );
        (result.solution, Some(result.timings))
    };

    // Unified stop predicate: deadline, outer termination, AND memory pressure.
    // See the module header for why the memory arm is in the shared spelling.
    let should_stop = || {
        term_flag.load(Ordering::SeqCst)
            || timeout_dur.is_some_and(|d| start.elapsed() >= d)
            || ay_sys::process_memory_exceeded()
    };

    // Only a proven optimum is certifiable (BOUNDS V V). CANDIDATE WIDENING:
    // take the portfolio's own `OptimumFound` when it has one, otherwise ask
    // the checked optimum-upgrade gate whether a merely-feasible result is in
    // fact optimal. Either way this is only a CANDIDATE — every certificate
    // route below re-derives both bounds itself and declines rather than trust
    // it — so widening cannot weaken anything.
    //
    // THE CACHE IS READ, NOT JUST WRITTEN: the native CDCL phase's best
    // incumbent is in `best_solution`, and on the odd-cycle family it MEETS the
    // structural floor while the portfolio's certification-reserve slice does
    // not rediscover it (`dim_054` at 5 s: `o 1512 s UNKNOWN` with `--proof`
    // against `s OPTIMUM FOUND` without). The widening helper re-verifies both
    // arms from raw bits and only ever CHOOSES a candidate; the verdict still
    // has to clear `finalize_optimum_verdict`'s certified-floor gate and the
    // certificate chain below.
    let candidate = if portfolio_solution.status == PbStatus::OptimumFound {
        portfolio_solution
    } else {
        let cached = best_solution
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .clone();
        let widened = portfolio::widen_optimum_candidate_with_cached_incumbent(
            portfolio_solution,
            cached,
            instance_ref,
            objective,
        );
        let upgraded =
            portfolio::finalize_optimum_verdict(widened, instance_ref, objective, &should_stop);
        if upgraded.status != PbStatus::OptimumFound {
            return OptLinCertFallback::Declined { timings };
        }
        upgraded
    };

    let Some(optimum) = candidate.objective else {
        return OptLinCertFallback::Declined { timings };
    };
    let incumbent = candidate.assignment;
    if incumbent.len() != instance_ref.num_vars as usize {
        return OptLinCertFallback::Declined { timings };
    }

    // THE WHOLE CHAIN, cheapest-first — the single library definition
    // (`ay_pb::proof::certify_opt_lin_any_interruptible`). Every rung
    // re-verifies the incumbent itself and returns `None` rather than a
    // doubtful proof; VeriPB re-checks whatever comes back.
    let Some((pbp, route)) = certify_opt_lin_any_interruptible(
        instance_ref,
        &incumbent,
        optimum,
        timeout_dur.map(|timeout| start + timeout),
        &should_stop,
    ) else {
        return OptLinCertFallback::Declined { timings };
    };

    OptLinCertFallback::Certified {
        pbp,
        route,
        solution: PbSolution {
            status: PbStatus::OptimumFound,
            assignment: incumbent,
            objective: Some(optimum),
        },
        timings,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_pb_core::parse_opb;

    /// The certified path does not use the racing coordinator, for ANY
    /// instance shape.
    ///
    /// This test exists to be in the way. The determinism guarantee it defends
    /// ("byte-identical certs under load") is not visible from the call site —
    /// flipping `proof_path_uses_parallel_primal` to `true` compiles, passes
    /// every functional test, converts six more instances of the residual
    /// census, and silently breaks a shipped promise that only a multi-repeat
    /// corpus sweep can detect. So the flip has to come here and delete a test
    /// whose name says what is being given up.
    #[test]
    fn certified_path_never_uses_the_racing_coordinator() {
        // A linear instance the parallel gate would otherwise accept.
        let opb = "* #variable= 4 #constraint= 2\n\
                   min: 1 x1 1 x2 1 x3 1 x4 ;\n\
                   1 x1 1 x2 >= 1 ;\n\
                   1 x3 1 x4 >= 1 ;\n";
        let instance = parse_opb(opb).expect("fixture parses");
        assert!(
            !proof_path_uses_parallel_primal(&instance),
            "the certified fallback must not route to the first-proven-wins \
             coordinator: which optimal model comes back is decided by a race, \
             and the certificate embeds the model"
        );
    }
}
