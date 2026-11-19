// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `main`: the claim that keeps a proof with its verdict.

/// Which outcome owns the end of this run, settled once by compare-and-swap
/// (2026-09-13). A DIMACS publication path claims its decisive verdict before
/// printing it; an exit that ends the run without an answer (the timeout,
/// memory and termination watchdogs, or a main-thread timeout, unknown or
/// failure exit) claims the run as unanswered before it discards proofs and
/// prints `s UNKNOWN`. Exactly one wins, which keeps a proof with its verdict:
///
///  * an unanswered exit that wins discards every proof generation, and a
///    publication path that finds the claim taken never prints
///    `s UNSATISFIABLE` behind a discarded proof: it yields to the exiting
///    thread;
///  * a decisive verdict that wins keeps its proof, and a watchdog that fires
///    afterwards leaves with that verdict's exit code, never the timeout's, so
///    the SAT-COMP runner's `rc != 20` cleanup cannot delete a certified proof.
///
/// Measured on 166e1e5a: the solve answered UNSAT at 248.2 s and its 2.73 GB
/// proof was published at 248.3 s, but `s UNSATISFIABLE` came only at
/// 295.3 s, after the publication checks. A budget that ended in between made
/// the watchdog print `s UNKNOWN` and exit, leaving the whole proof behind.
///
/// Holds [`RUN_OUTCOME_OPEN`], [`RUN_OUTCOME_UNANSWERED`], or the exit code of
/// the claimed decisive verdict, which is never negative.
static RUN_OUTCOME: std::sync::atomic::AtomicI32 =
    std::sync::atomic::AtomicI32::new(RUN_OUTCOME_OPEN);
const RUN_OUTCOME_OPEN: i32 = -1;
const RUN_OUTCOME_UNANSWERED: i32 = -2;
/// How long a hard exit that finds the run already claimed lets the claiming
/// thread finish ending it: that thread only prints and exits, or discards
/// and exits.
const OTHER_EXIT_GRACE: Duration = Duration::from_secs(10);

/// The outcome of claiming a run as unanswered; see [`RUN_OUTCOME`].
pub(crate) enum UnansweredClaim {
    /// This exit owns the run: it discards the proofs and answers unknown.
    Won,
    /// Another unanswered exit already owns the run.
    AlreadyUnanswered,
    /// A decisive verdict with this exit code already owns the run.
    Decisive(i32),
}

/// Claim the run for an exit that ends it without an answer.
pub(crate) fn claim_unanswered_outcome() -> UnansweredClaim {
    claim_unanswered_in(&RUN_OUTCOME)
}

/// What an unanswered exit on a solving thread (a DIMACS timeout, unknown or
/// failure exit, `settle_unanswered_dimacs_exit`) does once it has tried to
/// claim the run.
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum SolvingThreadExit {
    /// This exit owns the run: it discards the proofs and answers unknown.
    Discard,
    /// Another unanswered exit owns the run and is ending it.
    YieldToUnansweredExit,
    /// The other member of the parallel DIMACS race holds a decisive verdict
    /// with this exit code and is publishing it. This exit prints nothing and
    /// never leaves with its own code: it gives that member the time to
    /// finish, then leaves with the verdict's code
    /// ([`leave_with_claimed_verdict`]), as the hard exits do.
    YieldToVerdict(i32),
    /// This thread claimed the decisive verdict itself and is publishing it;
    /// the exit leaves the verdict's proof alone. Outside a race every
    /// decisive claim a solving thread meets is its own (2026-09-13).
    OwnVerdict,
}

/// Claim the run for an unanswered exit on a solving thread; see
/// [`SolvingThreadExit`].
pub(crate) fn claim_unanswered_solving_exit() -> SolvingThreadExit {
    let race_owner = verdict_race_active().then_some(&VERDICT_RACE_OWNER);
    solving_thread_exit_in(&RUN_OUTCOME, race_owner, std::thread::current().id())
}

/// Inside the race every decisive claim is made by the race's owner
/// ([`claim_decisive_verdict_or_yield`] claims the race first), so a decisive
/// claim meets an exit on another thread exactly when the race is owned by a
/// thread other than `caller`. The two threads' claims are ordered by
/// [`RUN_OUTCOME`] alone, so the decision does not depend on whether the
/// owner has marked its verdict printed yet: an exit that finds the verdict
/// claimed never answers unknown, and a verdict that finds the run claimed
/// unanswered never prints.
fn solving_thread_exit_in(
    outcome: &std::sync::atomic::AtomicI32,
    race_owner: Option<&std::sync::Mutex<Option<std::thread::ThreadId>>>,
    caller: std::thread::ThreadId,
) -> SolvingThreadExit {
    match claim_unanswered_in(outcome) {
        UnansweredClaim::Won => SolvingThreadExit::Discard,
        UnansweredClaim::AlreadyUnanswered => SolvingThreadExit::YieldToUnansweredExit,
        UnansweredClaim::Decisive(exit_code) => {
            let held_by_other_member = race_owner.is_some_and(|owner| {
                owner
                    .lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner)
                    .is_some_and(|owner| owner != caller)
            });
            if held_by_other_member {
                SolvingThreadExit::YieldToVerdict(exit_code)
            } else {
                SolvingThreadExit::OwnVerdict
            }
        }
    }
}

/// End an unanswered exit that found a decisive verdict owning the run: the
/// verdict's thread prints it and exits with its own code. Give it
/// [`OTHER_EXIT_GRACE`] to, then leave with that code, never the exit's own.
pub(crate) fn leave_with_claimed_verdict(exit_code: i32) -> ! {
    std::thread::sleep(OTHER_EXIT_GRACE);
    std::process::exit(exit_code);
}

/// Claim the run for the decisive verdict about to be printed, which exits
/// with `exit_code`, and record that verdict. Returns only when the claim
/// holds: a run an unanswered exit already owns has discarded its proofs, so
/// this thread never prints the verdict and yields to the exiting thread.
pub(crate) fn claim_decisive_verdict_or_yield(exit_code: i32) {
    // Backstop for the parallel DIMACS race: whichever publication path gets
    // here, only the member that owns the race may print a decisive verdict.
    claim_verdict_race_or_yield();
    if !claim_decisive_in(&RUN_OUTCOME, exit_code) {
        yield_to_exiting_thread();
    }
    mark_verdict_printed();
    mark_decisive_verdict_printed();
}

/// The parallel DIMACS race (`ay solve <cnf> --parallel N` without a proof):
/// the sequential default route runs as one member beside the portfolio, each
/// on its own thread, and each publishes through its own, unchanged path. Two
/// members can reach a decisive answer at almost the same moment, and
/// [`RUN_OUTCOME`] does not referee two decisive claims, so the race does:
/// the first member thread to claim owns the verdict, and the other parks
/// until the owner's `process::exit` takes the process down. Nothing is
/// recorded while no race is running, so every other route is untouched.
static VERDICT_RACE_ACTIVE: AtomicBool = AtomicBool::new(false);
static VERDICT_RACE_OWNER: std::sync::Mutex<Option<std::thread::ThreadId>> =
    std::sync::Mutex::new(None);

/// Start the parallel DIMACS race. Called once, before either member runs.
pub(crate) fn begin_verdict_race() {
    VERDICT_RACE_ACTIVE.store(true, Ordering::SeqCst);
}

/// Whether the parallel DIMACS race is running in this process.
pub(crate) fn verdict_race_active() -> bool {
    VERDICT_RACE_ACTIVE.load(Ordering::SeqCst)
}

/// Claim the race's verdict for the calling member thread. Returns only when
/// this thread owns it (claiming again is a no-op); a thread that finds the
/// verdict owned by the other member never returns. Outside a race it returns
/// at once.
pub(crate) fn claim_verdict_race_or_yield() {
    if !verdict_race_active() {
        return;
    }
    if !claim_verdict_race_in(&VERDICT_RACE_OWNER, std::thread::current().id()) {
        yield_to_exiting_thread();
    }
}

/// True when `claimant` owns the race after this call.
fn claim_verdict_race_in(
    owner: &std::sync::Mutex<Option<std::thread::ThreadId>>,
    claimant: std::thread::ThreadId,
) -> bool {
    let mut owner = owner
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    match *owner {
        None => {
            *owner = Some(claimant);
            true
        }
        Some(current) => current == claimant,
    }
}

fn claim_unanswered_in(outcome: &std::sync::atomic::AtomicI32) -> UnansweredClaim {
    match outcome.compare_exchange(
        RUN_OUTCOME_OPEN,
        RUN_OUTCOME_UNANSWERED,
        Ordering::SeqCst,
        Ordering::SeqCst,
    ) {
        Ok(_) => UnansweredClaim::Won,
        Err(RUN_OUTCOME_UNANSWERED) => UnansweredClaim::AlreadyUnanswered,
        Err(exit_code) => UnansweredClaim::Decisive(exit_code),
    }
}

/// False only when an unanswered exit owns the run. A second decisive claim
/// is not this protocol's to referee.
fn claim_decisive_in(outcome: &std::sync::atomic::AtomicI32, exit_code: i32) -> bool {
    debug_assert!(exit_code >= 0, "decisive exit codes are never negative");
    outcome
        .compare_exchange(
            RUN_OUTCOME_OPEN,
            exit_code,
            Ordering::SeqCst,
            Ordering::SeqCst,
        )
        .err()
        != Some(RUN_OUTCOME_UNANSWERED)
}

/// Park the calling thread for good: another thread owns the end of the run
/// and is taking the process down.
pub(crate) fn yield_to_exiting_thread() -> ! {
    loop {
        std::thread::park();
    }
}

/// Whether an unanswered exit owns the run. A proof generation created after
/// that claim is abandoned at birth, since the exit's discard may not see it.
pub(crate) fn run_claimed_unanswered() -> bool {
    RUN_OUTCOME.load(Ordering::SeqCst) == RUN_OUTCOME_UNANSWERED
}

/// Settle the run's proofs before a hard exit that does not answer. The exit
/// claims the run, then discards every proof generation it holds, before any
/// output that could block on a pipe. If another thread claimed the run
/// first, that thread is ending it: a decisive verdict's thread prints the
/// verdict and exits with its own code, an unanswered exit's thread discards
/// and exits. Give it the time to, so neither exit cuts the other short, and
/// only then leave: with the verdict's code, or after a discard of its own.
fn settle_proofs_before_unanswered_exit() {
    match claim_unanswered_outcome() {
        UnansweredClaim::Decisive(exit_code) => leave_with_claimed_verdict(exit_code),
        UnansweredClaim::AlreadyUnanswered => {
            std::thread::sleep(OTHER_EXIT_GRACE);
            dimacs::discard_unanswered_dimacs_proofs();
        }
        UnansweredClaim::Won => dimacs::discard_unanswered_dimacs_proofs(),
    }
}

/// Settle the run when the allocator's hard memory ceiling ends it
/// (2026-09-13), like every other exit that does not answer: claim the run,
/// then discard every proof generation it holds
/// ([`dimacs::discard_dimacs_proofs_at_memory_ceiling`]). If a decisive
/// verdict owns the run, give its thread the grace to end it and leave with
/// its code, writing nothing. If another unanswered exit owns it, give that
/// exit the grace, then discard as well. Registered with
/// `ay_sys::set_hard_memory_ceiling_settlement`, it runs inside the global
/// allocator on the breaching thread, which may allocate past the ceiling: it
/// takes no lock and writes only through `ay_sys::write_stderr_unlocked`. The
/// allocator then writes the armed verdict, unless one was printed already,
/// and leaves through `_exit`.
///
/// Before this, the breach left through `_exit` with no discard: at a 76 MB
/// ceiling on 12cd0c31 the run printed `s UNKNOWN` and left a 3,145,681-byte
/// partial VeriPB proof in its output directory under the private staging
/// name, which the SAT-COMP runner does not remove.
fn settle_run_at_memory_ceiling(armed_exit_code: i32) -> ay_sys::CeilingSettlement {
    settle_memory_ceiling_in(
        &RUN_OUTCOME,
        claim_owed_unknown_response,
        &DECISIVE_VERDICT_PRINTED,
        OTHER_EXIT_GRACE,
        armed_exit_code,
        dimacs::discard_dimacs_proofs_at_memory_ceiling,
    )
}

/// `claim_owed` claims the CURRENT query's response
/// ([`owe_response_for_new_query`]); `decisive_printed` says an earlier
/// query's `sat`/`unsat` is on stdout. A breach during a later query of an
/// incremental script answers that query `unknown` with the memout reason
/// and statistics, and leaves 0 if a decisive verdict stands (it left 124
/// with nothing written, which read as "no verdict" with a `sat` on stdout).
fn settle_memory_ceiling_in(
    outcome: &std::sync::atomic::AtomicI32,
    claim_owed: impl FnOnce() -> bool,
    decisive_printed: &AtomicBool,
    grace: Duration,
    armed_exit_code: i32,
    discard: impl FnOnce() -> (usize, u64),
) -> ay_sys::CeilingSettlement {
    match claim_unanswered_in(outcome) {
        UnansweredClaim::Decisive(exit_code) => {
            std::thread::sleep(grace);
            return ay_sys::CeilingSettlement::Silent(exit_code);
        }
        UnansweredClaim::AlreadyUnanswered => std::thread::sleep(grace),
        UnansweredClaim::Won => {}
    }
    let (discarded, bytes) = discard();
    if discarded > 0 {
        ay_sys::write_stderr_unlocked(
            format!(
                "c memout: the allocator's memory ceiling ended the run; discarded {discarded} proof generation(s) holding {bytes} bytes\n"
            )
            .as_bytes(),
        );
    }
    let decisive = decisive_printed.load(Ordering::SeqCst);
    match (claim_owed(), decisive) {
        (true, false) => ay_sys::CeilingSettlement::ArmedVerdict,
        (true, true) => ay_sys::CeilingSettlement::ArmedVerdictWithStatus(0),
        (false, true) => {
            write_verdict_stands_note(ay_sys::write_stderr_unlocked);
            ay_sys::CeilingSettlement::Silent(0)
        }
        (false, false) => ay_sys::CeilingSettlement::Silent(armed_exit_code),
    }
}

/// The `unsat_admission=… evidence=… corroboration=… disabled=…` fields of the
/// last decisive verdict when it was `unsat`; empty after a `sat`.
///
/// Evidence policy P4 (2026-10-02): every published `unsat` says what backs
/// it. Those fields ride on the certificate line, which is printed after the
/// verdict, once the proof is rendered; a memory ceiling reached in between
/// ends the run with only the "verdict stands" note. Measured on the D7 list
/// (`-memory:4096`): QF_UFIDL uclid 22s and q2.12 published `unsat` with no
/// evidence label at all. The note now carries the fields recorded here.
static PUBLISHED_UNSAT_EVIDENCE: std::sync::Mutex<String> = std::sync::Mutex::new(String::new());

/// Record the evidence of the decisive verdict just printed: `Some(fields)`
/// for an `unsat`, `None` for a `sat` (an earlier `unsat`'s fields no longer
/// describe the verdict that stands).
pub(crate) fn record_decisive_verdict_evidence(unsat_fields: Option<String>) {
    if let Ok(mut slot) = PUBLISHED_UNSAT_EVIDENCE.lock() {
        *slot = unsat_fields.unwrap_or_default();
    }
}

/// Write the memout note for a run whose decisive verdict is already on
/// stdout, naming what admitted it when it was `unsat`. Never blocks: the
/// fields are read with `try_lock`, and a writer that cannot take the lock
/// writes the bare note.
fn write_verdict_stands_note(write: impl FnMut(&[u8])) {
    match PUBLISHED_UNSAT_EVIDENCE.try_lock() {
        Ok(fields) => verdict_stands_note(&fields, write),
        Err(_) => verdict_stands_note("", write),
    }
}

/// The "verdict stands" note, with the `unsat`'s evidence fields when there
/// are any. Writes in pieces, so it allocates nothing.
fn verdict_stands_note(unsat_fields: &str, mut write: impl FnMut(&[u8])) {
    write(b"c memout after the verdict was published; verdict stands");
    if !unsat_fields.is_empty() {
        write(b" (the unsat was admitted by ");
        write(unsat_fields.as_bytes());
        write(b")");
    }
    write(b"\n");
}

/// The arbitration between a verdict and an unanswered exit (2026-09-13), on a
/// cell of its own: the process-wide claim is one-shot.
#[cfg(test)]
mod run_outcome_tests {
    use super::*;
    use std::sync::atomic::AtomicI32;

    /// The parallel race's referee: the first member thread owns the verdict,
    /// claiming again is a no-op for it, and the other member never owns it.
    #[test]
    fn the_verdict_race_has_one_owner() {
        let owner = std::sync::Mutex::new(None);
        let first = std::thread::current().id();
        let second = std::thread::spawn(|| std::thread::current().id())
            .join()
            .expect("thread id");
        assert!(claim_verdict_race_in(&owner, first));
        assert!(claim_verdict_race_in(&owner, first));
        assert!(!claim_verdict_race_in(&owner, second));
        assert!(claim_verdict_race_in(&owner, first));
    }

    /// The id of a thread other than the calling one.
    fn other_thread_id() -> std::thread::ThreadId {
        std::thread::spawn(|| std::thread::current().id())
            .join()
            .expect("thread id")
    }

    /// The race's deadline defect (review of 2026-11-13): the sequential
    /// member claimed the race and the run's outcome (SAT, exit 10) and is
    /// printing its model when the portfolio thread's timeout exit runs. That
    /// exit must yield to the verdict and leave with 10, not discard, print
    /// `s UNKNOWN` or leave 124. The member's claim was made on another
    /// thread, exactly as in the race; whether it has marked its verdict
    /// printed yet does not enter the decision.
    #[test]
    fn an_unanswered_exit_yields_to_a_verdict_the_other_race_member_holds() {
        let outcome = Arc::new(AtomicI32::new(RUN_OUTCOME_OPEN));
        let owner = Arc::new(std::sync::Mutex::new(None));
        let member = {
            let (outcome, owner) = (Arc::clone(&outcome), Arc::clone(&owner));
            std::thread::spawn(move || {
                assert!(claim_verdict_race_in(&owner, std::thread::current().id()));
                assert!(claim_decisive_in(&outcome, 10));
            })
        };
        member.join().expect("member");
        assert_eq!(
            solving_thread_exit_in(&outcome, Some(&owner), std::thread::current().id()),
            SolvingThreadExit::YieldToVerdict(10)
        );
        assert_eq!(
            outcome.load(Ordering::SeqCst),
            10,
            "the verdict still owns the run"
        );
    }

    /// The owner's own exit after its decisive claim leaves its proof alone
    /// and keeps its path, inside the race and out of it.
    #[test]
    fn an_exit_on_the_verdicts_own_thread_keeps_its_path() {
        let me = std::thread::current().id();
        let outcome = AtomicI32::new(RUN_OUTCOME_OPEN);
        let owner = std::sync::Mutex::new(Some(me));
        assert!(claim_decisive_in(&outcome, 20));
        assert_eq!(
            solving_thread_exit_in(&outcome, Some(&owner), me),
            SolvingThreadExit::OwnVerdict
        );
    }

    /// Outside the race the decision is what it was before the race existed:
    /// a decisive claim is the exiting thread's own, so nothing changes for
    /// sequential ay.
    #[test]
    fn outside_the_race_a_decisive_claim_keeps_the_old_path() {
        let outcome = AtomicI32::new(RUN_OUTCOME_OPEN);
        assert!(claim_decisive_in(&outcome, 10));
        assert_eq!(
            solving_thread_exit_in(&outcome, None, other_thread_id()),
            SolvingThreadExit::OwnVerdict
        );
    }

    /// An exit that claims an open run first owns it, and the other member's
    /// later verdict never prints (it yields before writing anything); an
    /// exit that finds another unanswered exit owning the run yields to it.
    #[test]
    fn an_unanswered_exit_that_claims_first_keeps_the_race_unanswered() {
        let outcome = AtomicI32::new(RUN_OUTCOME_OPEN);
        let owner = std::sync::Mutex::new(Some(other_thread_id()));
        let me = std::thread::current().id();
        assert_eq!(
            solving_thread_exit_in(&outcome, Some(&owner), me),
            SolvingThreadExit::Discard
        );
        assert!(
            !claim_decisive_in(&outcome, 10),
            "the verdict must not print"
        );
        assert_eq!(
            solving_thread_exit_in(&outcome, Some(&owner), me),
            SolvingThreadExit::YieldToUnansweredExit
        );
    }

    /// [`settle_memory_ceiling_in`] on test-local cells, armed exit code 0.
    fn settle(
        outcome: &AtomicI32,
        printed: &AtomicBool,
        decisive: bool,
        discard: impl FnOnce() -> (usize, u64),
    ) -> ay_sys::CeilingSettlement {
        let decisive = AtomicBool::new(decisive);
        settle_memory_ceiling_in(
            outcome,
            || !printed.swap(true, Ordering::SeqCst),
            &decisive,
            Duration::ZERO,
            0,
            discard,
        )
    }

    /// A breach during a later query of an incremental script answers THAT
    /// query: the armed `unknown`, reason and statistics are written even
    /// though an earlier query's `sat` is on stdout, and the run leaves 0
    /// because that decisive verdict stands. It left 124 with nothing written.
    #[test]
    fn the_memory_ceiling_answers_the_query_in_flight_after_an_earlier_verdict() {
        let outcome = AtomicI32::new(RUN_OUTCOME_OPEN);
        let printed = AtomicBool::new(false);
        let settlement = settle(&outcome, &printed, true, || (0, 0));
        assert_eq!(
            settlement,
            ay_sys::CeilingSettlement::ArmedVerdictWithStatus(0)
        );
        assert!(printed.load(Ordering::SeqCst));

        // No query in flight and a decisive verdict on stdout: nothing owed,
        // and the verdict's run is not reported as failed.
        let outcome = AtomicI32::new(RUN_OUTCOME_OPEN);
        let printed = AtomicBool::new(true);
        let settlement = settle(&outcome, &printed, true, || (0, 0));
        assert_eq!(settlement, ay_sys::CeilingSettlement::Silent(0));
    }

    /// The allocator's memory ceiling settles an open run like every other
    /// unanswered exit (2026-09-13): it claims the run and discards its proofs
    /// before the allocator writes the armed verdict, and no decisive verdict
    /// can print behind that discard.
    #[test]
    fn the_memory_ceiling_claims_an_open_run_and_discards_its_proofs_first() {
        let outcome = AtomicI32::new(RUN_OUTCOME_OPEN);
        let printed = AtomicBool::new(false);
        let mut discards = 0;
        let settlement = settle(&outcome, &printed, false, || {
            discards += 1;
            (0, 0)
        });
        assert_eq!(settlement, ay_sys::CeilingSettlement::ArmedVerdict);
        assert_eq!(discards, 1);
        assert_eq!(outcome.load(Ordering::SeqCst), RUN_OUTCOME_UNANSWERED);
        assert!(
            printed.load(Ordering::SeqCst),
            "the armed verdict is the run's one verdict"
        );
        assert!(
            !claim_decisive_in(&outcome, 20),
            "no verdict prints behind the discard"
        );
    }

    /// A decisive verdict that owns the run keeps its proof: the ceiling
    /// discards nothing, writes nothing, and leaves with the verdict's code.
    #[test]
    fn the_memory_ceiling_never_discards_a_decisive_verdicts_proof() {
        let outcome = AtomicI32::new(RUN_OUTCOME_OPEN);
        assert!(claim_decisive_in(&outcome, 20));
        let printed = AtomicBool::new(true);
        let settlement = settle(&outcome, &printed, false, || -> (usize, u64) {
            panic!("a decisive verdict's proof must not be discarded")
        });
        assert_eq!(settlement, ay_sys::CeilingSettlement::Silent(20));
    }

    /// Another unanswered exit owns the run: the ceiling discards as well,
    /// which is idempotent, and does not write a second verdict.
    #[test]
    fn the_memory_ceiling_after_another_unanswered_exit_discards_without_a_second_verdict() {
        let outcome = AtomicI32::new(RUN_OUTCOME_UNANSWERED);
        let printed = AtomicBool::new(true);
        let mut discards = 0;
        let settlement = settle(&outcome, &printed, false, || {
            discards += 1;
            (0, 0)
        });
        assert_eq!(settlement, ay_sys::CeilingSettlement::Silent(0));
        assert_eq!(discards, 1);
    }

    #[test]
    fn a_verdict_claimed_first_keeps_the_run_and_its_exit_code() {
        let outcome = AtomicI32::new(RUN_OUTCOME_OPEN);
        assert!(claim_decisive_in(&outcome, 20));
        assert!(matches!(
            claim_unanswered_in(&outcome),
            UnansweredClaim::Decisive(20)
        ));
    }

    #[test]
    fn an_unanswered_exit_claimed_first_keeps_the_verdict_from_printing() {
        let outcome = AtomicI32::new(RUN_OUTCOME_OPEN);
        assert!(matches!(
            claim_unanswered_in(&outcome),
            UnansweredClaim::Won
        ));
        assert!(
            !claim_decisive_in(&outcome, 20),
            "the verdict must not print"
        );
        assert!(matches!(
            claim_unanswered_in(&outcome),
            UnansweredClaim::AlreadyUnanswered
        ));
    }

    /// Verdicts and unanswered exits racing on one cell: exactly one side
    /// wins, and every loser sees that side.
    #[test]
    fn exactly_one_side_wins_a_race() {
        for _ in 0..200 {
            let outcome = Arc::new(AtomicI32::new(RUN_OUTCOME_OPEN));
            let barrier = Arc::new(std::sync::Barrier::new(4));
            let racers: Vec<_> = (0..4)
                .map(|racer| {
                    let (outcome, barrier) = (Arc::clone(&outcome), Arc::clone(&barrier));
                    std::thread::spawn(move || {
                        barrier.wait();
                        if racer % 2 == 0 {
                            (true, claim_decisive_in(&outcome, 20))
                        } else {
                            (
                                false,
                                matches!(claim_unanswered_in(&outcome), UnansweredClaim::Won),
                            )
                        }
                    })
                })
                .collect();
            let results: Vec<(bool, bool)> = racers
                .into_iter()
                .map(|racer| racer.join().expect("racer"))
                .collect();
            let decisive_won = outcome.load(Ordering::SeqCst) == 20;
            for (decisive, claimed) in results {
                if decisive {
                    assert_eq!(
                        claimed, decisive_won,
                        "a verdict prints only if verdicts won"
                    );
                } else if decisive_won {
                    assert!(!claimed, "no exit discards a claimed verdict's proof");
                }
            }
        }
    }

    /// P4: a memout after a published `unsat` still names what admitted it;
    /// after a `sat` the note is bare.
    #[test]
    fn the_verdict_stands_note_names_an_unsat_admission() {
        let note = |fields: &str| {
            let mut out = Vec::new();
            verdict_stands_note(fields, |bytes| out.extend_from_slice(bytes));
            String::from_utf8(out).expect("ascii")
        };
        assert_eq!(
            note(""),
            "c memout after the verdict was published; verdict stands\n"
        );
        assert_eq!(
            note(
                "unsat_admission=discharged-trust evidence=E1 corroboration=resolve disabled=none"
            ),
            "c memout after the verdict was published; verdict stands (the unsat was admitted by \
             unsat_admission=discharged-trust evidence=E1 corroboration=resolve disabled=none)\n"
        );
    }
}
