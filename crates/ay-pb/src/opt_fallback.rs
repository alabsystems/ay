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

use std::path::Path;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use ay_pb_core::{PbExactSolution, PbInstance, PbObjective, PbSolution, PbStatus};

use crate::portfolio::{self, PbPortfolioPhaseTimings};
use crate::proof::{
    cert_debug_line, certify_opt_infeasible_pb_interruptible, certify_opt_lin_any_interruptible,
    certify_reserve, OptLinCertRoute,
};

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
    /// The instance has no feasible solution, and a VeriPB proof concluding
    /// `BOUNDS INF INF` was built (`certify_opt_infeasible_pb_interruptible`).
    /// The caller writes and commits it and answers `s UNSATISFIABLE`.
    CertifiedInfeasible {
        /// The proof text, ready to write.
        pbp: String,
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
    // PHASE ACCOUNTING for the certified fallback, `--cert-debug` only.
    //
    // The chain's per-rung trace starts when the chain starts, so everything
    // BEFORE it — how much of the declared budget the fallback portfolio was
    // handed, how much it used, and therefore how much is left for the rungs —
    // was invisible. A miss whose rungs each report `slice=3333ms` says nothing
    // about WHY the slice is 3.3 s; this line does.
    if ay_core::misc_cli_flags().cert_debug {
        cert_debug_line(format_args!(
            "c [cert/phase] portfolio grant={} elapsed={}ms status={:?} obj={:?}; \
             declared={} left-for-chain={}ms",
            portfolio_timeout.map_or_else(
                || "unbounded".to_string(),
                |t| format!("{}ms", t.as_millis())
            ),
            start.elapsed().as_millis(),
            portfolio_solution.status,
            portfolio_solution.objective,
            timeout_dur.map_or_else(
                || "unbounded".to_string(),
                |t| format!("{}ms", t.as_millis())
            ),
            timeout_dur.map_or(0, |t| t.saturating_sub(start.elapsed()).as_millis()),
        ));
    }

    // Unified stop predicate: deadline, outer termination, AND memory pressure.
    // See the module header for why the memory arm is in the shared spelling.
    let should_stop = || {
        term_flag.load(Ordering::SeqCst)
            || timeout_dur.is_some_and(|d| start.elapsed() >= d)
            || ay_sys::process_memory_exceeded()
    };

    // AY-SAT-7: the portfolio says the constraints have no solution. The
    // optimization proof solver logs through the legacy writer, which cannot
    // refute some such instances in any budget (factor-size=9-P=379-Q=521:
    // none in 58 s); the decision proof tap refutes them at once
    // (`certify_opt_infeasible_pb_interruptible`). Tried only when no
    // incumbent was ever verified (one would contradict the portfolio, and
    // then nothing is tried). The checker re-validates every step.
    if portfolio_solution.status == PbStatus::Unsatisfiable
        && best_solution.lock().is_ok_and(|cached| cached.is_none())
    {
        if let Some(pbp) = certify_opt_infeasible_pb_interruptible(instance_ref, &should_stop) {
            cert_debug_line(format_args!(
                "c opt-lin-cert route: infeasible (decision proof tap)"
            ));
            return OptLinCertFallback::CertifiedInfeasible { pbp, timings };
        }
    }

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
    // has to clear the certificate chain below.
    //
    // THE UPGRADE GATE NO LONGER DECIDES WHETHER THE CHAIN RUNS, and that is
    // this block's whole point. `finalize_optimum_verdict` proves optimality
    // from exactly TWO routes (`recovered_structural_search_floor` and
    // `certified_objective_floor_interruptible`). The chain behind it has
    // THIRTEEN. Returning `Declined` on the gate's verdict therefore skipped
    // eleven routes because two of them failed — and it did so AFTER
    // `certify_reserve` had already been taken out of the search, so the
    // reserve was subtracted and then destroyed.
    //
    // MEASURED, delivery bucket, `ay pb solve --timeout 60000 --cert-debug`,
    // one solve at a time, 18 instances: on 7 of them the chain emitted NOT ONE
    // `c [cert/floor]` line — it was never entered — each with
    // `left-for-chain` ~= 10,000 ms of the declared 60,000 ms unspent. Three of
    // those 7 were holding an incumbent EQUAL to the instance's known optimum
    // (`50-750-...-2000opt` -70, `comppebphp_...06` 28, `rande89f80` 2979398).
    //
    // WHY LETTING A MERELY-FEASIBLE CANDIDATE THROUGH IS SOUND. It is a
    // CANDIDATE, exactly as the widening above is. Every rung independently
    // re-verifies that the incumbent is complete and feasible and that it
    // evaluates to the claimed value, and then DERIVES the matching lower bound
    // itself — `lp_dual_floor` from an exact rational dual, `certified_bb` by
    // closing a tree, the three `bounds_*` rungs by refuting
    // {instance AND obj <= v-1}. A non-optimal `v` makes that augmented
    // instance SATISFIABLE and every rung returns `None`. So no rung can emit
    // `BOUNDS v <= obj <= v` for a `v` that is not the optimum, the status is
    // upgraded only on the strength of a proof, and the pinned external checker
    // re-checks that proof before any CERTIFIED claim is made. This is the same
    // "certificate-backed SATISFIABLE becomes OPTIMUM, sound by construction"
    // rule `finalize_optimum_verdict` already documents, applied to the whole
    // route inventory instead of two of it.
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
        // A feasible candidate is still a candidate. Only a result with no
        // incumbent at all has nothing for the chain to work from; the
        // `objective`/width guards immediately below reject that case.
        if !matches!(
            upgraded.status,
            PbStatus::OptimumFound | PbStatus::Satisfiable
        ) {
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

/// NATIVE-PHASE ACCOUNTING, `--cert-debug` only: the `c [cert/phase]
/// native-cdcl` line both frontends print after their proof-logging CDCL phase.
///
/// That phase is the one that writes to the proof file DIRECTLY, and unless it
/// closes the optimality bound every one of those bytes is thrown away: the
/// fallback above and the known-optimum commit both overwrite the temp path
/// wholesale. How much wall and how many bytes that costs was unmeasurable from
/// outside; this reports both. The frontends keep their own native phase (only
/// the fallback is shared), so this line used to be spelled twice; it is
/// spelled here once and both call it.
///
/// Diagnostics only: the proof file is measured only when the line is written.
pub fn trace_native_cdcl_phase(
    start: Instant,
    solution: &PbSolution,
    temp_proof_path: &Path,
    deferred_lb: bool,
) {
    if !ay_core::misc_cli_flags().cert_debug {
        return;
    }
    let discarded = std::fs::metadata(temp_proof_path).map_or(0, |m| m.len());
    cert_debug_line(format_args!(
        "c [cert/phase] native-cdcl elapsed={}ms status={:?} obj={:?} \
         proof-bytes-so-far={} deferred-lb={}",
        start.elapsed().as_millis(),
        solution.status,
        solution.objective,
        discarded,
        deferred_lb,
    ));
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

    /// THE PROPERTY THAT LICENSES ADMITTING A MERELY-FEASIBLE CANDIDATE.
    ///
    /// The fallback used to return `Declined` whenever
    /// `finalize_optimum_verdict` could not prove optimality from its two
    /// routes, which skipped the eleven other rungs and destroyed the
    /// `certify_reserve` it had already taken out of the search. It now hands
    /// the chain a candidate the gate could not upgrade.
    ///
    /// That is only safe because NO RUNG WILL CERTIFY A VALUE THAT IS NOT THE
    /// OPTIMUM. This test states that directly, on the smallest instance where
    /// a feasible point is not optimal: `min: x1 + x2` subject to
    /// `x1 + x2 >= 1` has optimum 1, and `x1 = x2 = true` is feasible at 2. If
    /// this ever starts returning a proof, the widened admission above is
    /// unsound and must be reverted with it — a `BOUNDS 2 <= obj <= 2` here
    /// would be a wrong answer carrying a certificate.
    #[test]
    fn no_rung_certifies_a_feasible_incumbent_that_is_not_optimal() {
        let opb = "* #variable= 2 #constraint= 1\n\
                   min: 1 x1 1 x2 ;\n\
                   1 x1 1 x2 >= 1 ;\n";
        let instance = parse_opb(opb).expect("fixture parses");
        let feasible_but_not_optimal = vec![true, true];
        let got = certify_opt_lin_any_interruptible(
            &instance,
            &feasible_but_not_optimal,
            2,
            None,
            &|| false,
        );
        assert!(
            got.is_none(),
            "a rung certified BOUNDS 2 <= obj <= 2 for an instance whose optimum \
             is 1 (route {:?}); the whole chain must be fail-closed against a \
             non-optimal claimed value, because that is what makes it safe to \
             run it on a candidate the upgrade gate could not prove optimal",
            got.map(|(_, route)| route.as_str())
        );
    }
}
