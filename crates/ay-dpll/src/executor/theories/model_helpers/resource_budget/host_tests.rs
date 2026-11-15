// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! P4a: a bit-blast solve under `:rlimit` is decided by counts, never by the
//! host's speed.
//!
//! The slow host is [`slow_host`]: a sleep inside every stop poll of the SAT
//! search (a count: every 100 conflicts and every 1,000 decisions), which
//! every clock the solve reads sees and no count it keeps does. It reaches
//! the fresh BV chain, the assumption arm, the array-FC re-solves, the
//! persistent incremental BV solver and every FP lane's search
//! (`solve_sat_under_query_stop`). The split-loop seam
//! (`ay_core::resource::test_seams::delay_each_round_trip`) cannot reach this
//! path: an eager bit-blast solve runs no DPLL(T) round trip.
//!
//! A sleep in the search's polls moves every clock the solve reads, but a
//! wall budget measured inside one pass (an inprocessing round) only as far
//! as the pass polls. The bounded solves therefore also run ay-sat's counted
//! schedules (`SatSolver::set_deterministic_inproc`), which the tests below
//! check directly, beside the idle-versus-slowed comparisons.

use std::time::{Duration, Instant};

use ay_frontend::parse;

use super::*;
use crate::executor::theories::sat_stop;
use crate::executor_types::UnknownReason;

/// Factor a 32-bit semiprime into two 16-bit primes (44549 * 55717) by
/// bit-blasting: about 13k conflicts and 16k decisions, through the delayed
/// multiplier's re-solve chain.
const FACTOR16: &str = r#"
    (set-logic QF_BV)
    (set-option :rlimit RLIMIT)
    (declare-fun x () (_ BitVec 16))
    (declare-fun y () (_ BitVec 16))
    (assert (= (bvmul ((_ zero_extend 16) x) ((_ zero_extend 16) y))
               #b10010011111100100110011000111001))
    (assert (bvult #b0000000000000001 x))
    (assert (bvult #b0000000000000001 y))
    (assert (bvule x y))
    (check-sat)
"#;

/// What a bit-blast check-sat decided, as the executor reports it.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Decided {
    output: Vec<String>,
    unknown_reason: Option<UnknownReason>,
    conflicts: u64,
    decisions: u64,
}

struct Run {
    decided: Decided,
    polls: u64,
    elapsed: Duration,
}

/// Run `script` with a far backstop (or `backstop`), a slow host of `delay`
/// per SAT stop poll and, if given, an explicit decision limit.
fn run(script: &str, backstop: Duration, delay: Duration, decision_limit: Option<u64>) -> Run {
    let commands = parse(script).expect("fixture parses");
    let mut exec = Executor::new();
    exec.set_timeout(Some(backstop));
    exec.set_decision_limit(decision_limit);
    slow_host::delay_each_poll(delay);
    let started = Instant::now();
    let output = exec.execute_all(&commands).expect("fixture runs");
    let elapsed = started.elapsed();
    let polls = slow_host::polls();
    slow_host::delay_each_poll(Duration::ZERO);
    let statistics = exec.statistics();
    Run {
        decided: Decided {
            output,
            unknown_reason: exec.unknown_reason(),
            conflicts: statistics.conflicts,
            decisions: statistics.decisions,
        },
        polls,
        elapsed,
    }
}

/// Far enough that no run below meets it, idle or slowed.
const BACKSTOP: Duration = Duration::from_secs(600);
/// The slow host's stop poll costs about this many idle polls' worth more...
const SLOWDOWN: u32 = 20;
/// ...unless that would add more than this to one run (the slowdown is then
/// smaller, still several times).
const SLOW_RUN_ALLOWANCE: Duration = Duration::from_secs(5);

/// A backstop near enough that the time left before it is a few slowed runs:
/// ay-sat's wall schedules size the independent-support probe's head start
/// at a tenth of the time left (4 s here), which a slowed run (the whole
/// [`SLOW_RUN_ALLOWANCE`] of sleeps plus its work) outlasts, far inside the
/// backstop itself.
const NEAR_BACKSTOP: Duration = Duration::from_secs(40);

/// Run `script` idle and on the slow host; everything the counts decide must
/// agree. Returns the idle decision and the slowed run.
fn idle_and_slow(script: &str, decision_limit: Option<u64>) -> (Decided, Run, Duration) {
    idle_and_slow_at(script, decision_limit, BACKSTOP)
}

/// [`idle_and_slow`], with the slowed run under `slow_backstop` while the idle
/// run keeps the far one: the counts must decide both alike whatever time is
/// left before the backstop. A slowed run that the backstop itself ends is a
/// stop (`timeout`), never another count or verdict.
fn idle_and_slow_at(
    script: &str,
    decision_limit: Option<u64>,
    slow_backstop: Duration,
) -> (Decided, Run, Duration) {
    let idle = run(script, BACKSTOP, Duration::ZERO, decision_limit);
    // The slowed run polls exactly as often as the idle one: the polls are
    // counted (every 100 conflicts, every 1,000 decisions, between passes).
    let polls = u32::try_from(idle.polls.max(1)).unwrap_or(u32::MAX);
    let delay = if slow_backstop == BACKSTOP {
        (idle.elapsed / polls * SLOWDOWN).min(SLOW_RUN_ALLOWANCE / polls)
    } else {
        // Under a near backstop, the whole allowance: the slowed run outlasts
        // a tenth of the backstop and stays well inside it.
        SLOW_RUN_ALLOWANCE / polls
    }
    .max(Duration::from_micros(200));
    let slow = run(script, slow_backstop, delay, decision_limit);
    let backstop_fired = slow_backstop != BACKSTOP
        && slow.elapsed >= slow_backstop
        && matches!(slow.decided.unknown_reason, Some(UnknownReason::Timeout));
    if backstop_fired {
        eprintln!(
            "the {slow_backstop:?} backstop ended the slowed run ({:?}): a stop, \
             compared with nothing",
            slow.elapsed
        );
    } else {
        assert_eq!(
            idle.decided, slow.decided,
            "the bit-blast solve decided differently on a slower host \
             (idle {:?}, slow {:?} under a {slow_backstop:?} backstop, {delay:?} per poll)",
            idle.elapsed, slow.elapsed
        );
    }
    // Non-vacuity: the seam reached this solve, and every poll slept.
    let slowed = u32::try_from(slow.polls).unwrap_or(u32::MAX);
    assert!(
        slowed > 0 && slow.elapsed >= delay * slowed,
        "the seam slowed the solve ({:?} for {slowed} polls at {delay:?})",
        slow.elapsed
    );
    eprintln!(
        "{:?}: idle {:?}, slow {:?} ({slowed} polls, {delay:?} each)",
        idle.decided, idle.elapsed, slow.elapsed
    );
    (idle.decided, slow, delay)
}

#[test]
fn a_decided_bitblast_solve_is_the_same_on_a_slower_host() {
    let (decided, _, _) = idle_and_slow(&FACTOR16.replace("RLIMIT", "400000"), None);
    assert_eq!(decided.output, vec!["sat"]);
    assert!(
        decided.conflicts > 1_000 && decided.decisions > 1_000,
        "the fixture searches: {decided:?}"
    );
}

#[test]
fn an_rlimit_stop_is_the_same_count_on_a_slower_host_and_a_backstop_is_a_stop() {
    let script = FACTOR16.replace("RLIMIT", "2000");
    let (decided, slow, delay) = idle_and_slow(&script, None);
    assert_eq!(decided.output, vec!["unknown"]);
    assert_eq!(decided.unknown_reason, Some(UnknownReason::ResourceLimit));
    assert!(
        decided.conflicts <= 2_000,
        "the solve chain ends at its :rlimit: {decided:?}"
    );
    // Negative control: a backstop that lands inside the slowed run ends it
    // as the stop it is, never as a count or an incomplete answer.
    let mut stopped = 0;
    for eighths in [1u32, 3, 5] {
        let cut = run(&script, slow.elapsed * eighths / 8, delay, None);
        match cut.decided.unknown_reason {
            None => assert_eq!(cut.decided, decided, "no stop: the counts decide"),
            Some(UnknownReason::ResourceLimit) => {
                assert_eq!(cut.decided, decided, "the count came first")
            }
            Some(UnknownReason::Timeout | UnknownReason::Interrupted) => stopped += 1,
            other => panic!(
                "a backstop at {eighths}/8 read as {other:?}: {:?}",
                cut.decided
            ),
        }
    }
    assert!(stopped > 0, "a backstop inside the slowed run stops it");
}

/// The factoring search beside 300 free bytes: lucky probes cannot satisfy
/// the multiplier, so CDCL runs, and every descent re-decides free bits that
/// no conflict involves.
fn decision_heavy_script(rlimit: &str) -> String {
    let mut script = FACTOR16
        .replace("RLIMIT", rlimit)
        .replace("(check-sat)", "");
    for i in 0..300 {
        script.push_str(&format!("(declare-fun v{i} () (_ BitVec 8))\n"));
    }
    for i in 0..299 {
        let j = i + 1;
        script.push_str(&format!("(assert (bvule (bvand v{i} v{j}) #xf0))\n"));
    }
    script.push_str("(check-sat)\n");
    script
}

#[test]
fn a_decision_heavy_bitblast_query_under_rlimit_ends_resourceout_not_timeout() {
    // The conflicts can never end this search: only the decision count can,
    // or the clock. The decision count does, at the same point on a slow
    // host. Without a decision budget the bit-blast arm ignored the limit.
    let script = decision_heavy_script("1000000");
    let (decided, _, _) = idle_and_slow(&script, Some(1_000));
    assert_eq!(decided.output, vec!["unknown"]);
    assert_eq!(decided.unknown_reason, Some(UnknownReason::ResourceLimit));
    assert!(
        decided.conflicts < 1_000,
        "the decision count ended the search, far below the :rlimit: {decided:?}"
    );
    // Sanity: the query is satisfiable and needs far more search, so nothing
    // but the decision count stopped it. (The reported decisions include the
    // lucky probes' assignments, which the search budget does not count.)
    let unbounded = run(&script, BACKSTOP, Duration::ZERO, None);
    assert_eq!(unbounded.decided.output, vec!["sat"]);
    assert!(
        unbounded.decided.decisions > decided.decisions
            && unbounded.decided.conflicts > decided.conflicts,
        "{:?}",
        unbounded.decided
    );
}

#[test]
fn a_bounded_bitblast_solve_ignores_the_time_left_before_its_backstop() {
    // FACTOR16 at :rlimit 2000 ends on its count under the far backstop.
    // The former 10000 budget now admits a deterministic SAT answer at
    // 8713 conflicts on both hosts. Use the resource-limited fixture already
    // checked above, so this control still exercises a count stop while the
    // slowed run outlasts the near backstop's former wall head start.
    // Under a near one, ay-sat's wall schedule gave its independent-support
    // probe a head start of a tenth of the time left, and a run that outlasted
    // it answered `sat` instead: on the release binary before the counted
    // schedules, `-t 1000` answered sat at 9,586 conflicts where `-t 600000`
    // ended resourceout at 10,000, and 16 of 36 parallel copies at `-t 3000`
    // answered sat.
    let script = FACTOR16.replace("RLIMIT", "2000");
    let (decided, slow, _) = idle_and_slow_at(&script, None, NEAR_BACKSTOP);
    assert_eq!(decided.output, vec!["unknown"]);
    assert_eq!(decided.unknown_reason, Some(UnknownReason::ResourceLimit));
    assert_eq!(decided.conflicts, 2_000, "{decided:?}");
    assert!(
        slow.elapsed > NEAR_BACKSTOP / 10,
        "the slowed run outlasts the wall head start it would have had: {:?}",
        slow.elapsed
    );
}

/// Float16 multiplication: `x * y = 7` with both factors above 1 while
/// `7 / x` is not `y`, satisfiable through rounding. About 2,700 conflicts
/// and 43,000 decisions, under the pre- and inprocessing the FP lanes keep.
const FP_MUL16: &str = r#"
    (set-logic QF_FP)
    RLIMIT_OPTION
    (declare-fun x () (_ FloatingPoint 5 11))
    (declare-fun y () (_ FloatingPoint 5 11))
    (assert (fp.isNormal x))
    (assert (fp.isNormal y))
    (assert (fp.lt ((_ to_fp 5 11) RNE 1.0) x))
    (assert (fp.lt ((_ to_fp 5 11) RNE 1.0) y))
    (assert (fp.eq (fp.mul RNE x y) ((_ to_fp 5 11) RNE 7.0)))
    (assert (not (fp.eq (fp.div RNE ((_ to_fp 5 11) RNE 7.0) x) y)))
    (check-sat)
"#;

fn fp_mul16(rlimit: Option<u64>) -> String {
    let option = rlimit.map_or(String::new(), |n| format!("(set-option :rlimit {n})"));
    FP_MUL16.replace("RLIMIT_OPTION", &option)
}

#[test]
fn every_fp_search_under_rlimit_runs_on_counts_and_none_without() {
    sat_stop::searches::take();
    let bounded = run(&fp_mul16(Some(100_000)), BACKSTOP, Duration::ZERO, None);
    assert_eq!(bounded.decided.output, vec!["sat"]);
    let searches = sat_stop::searches::take();
    assert!(!searches.is_empty(), "the FP lane searched");
    for search in &searches {
        assert!(
            search.conflict_budget.is_some_and(|n| n <= 100_000)
                && search.decision_budget.is_some()
                && search.counted,
            "every FP search under :rlimit carries both counts and counted \
             schedules: {:?} / {:?} / {}",
            search.conflict_budget,
            search.decision_budget,
            search.counted
        );
    }

    let unbounded = run(&fp_mul16(None), BACKSTOP, Duration::ZERO, None);
    assert_eq!(unbounded.decided.output, vec!["sat"]);
    for search in &sat_stop::searches::take() {
        assert_eq!(search.conflict_budget, None);
        assert_eq!(search.decision_budget, None);
        assert_eq!(search.counted, ay_sat::deterministic_inproc_enabled());
    }
}

#[test]
fn an_fp_solve_under_rlimit_is_the_same_on_a_slower_host() {
    let (decided, _, _) = idle_and_slow_at(&fp_mul16(Some(100_000)), None, NEAR_BACKSTOP);
    assert_eq!(decided.output, vec!["sat"]);
    assert!(
        decided.conflicts > 1 && decided.decisions > 0,
        "the fixture must perform an actual counted search: {decided:?}"
    );
    // Literal/circuit simplification can legitimately lower the SAT cost.
    // Exercise a count stop below this healthy run's actual search instead
    // of freezing the former 1,000-conflict UNKNOWN result.
    let stopping_budget = decided.conflicts / 2;
    let (decided, _, _) = idle_and_slow_at(&fp_mul16(Some(stopping_budget)), None, NEAR_BACKSTOP);
    assert_eq!(decided.output, vec!["unknown"]);
    assert_eq!(decided.unknown_reason, Some(UnknownReason::ResourceLimit));
}

/// Run `script`'s commands, then `check-sat` `extra` more times; returns the
/// outputs and the conflicts each check-sat spent.
fn repeated_check_sats(exec: &mut Executor, script: &str, extra: usize) -> Vec<(String, u64)> {
    let mut spent = Vec::new();
    let mut before = exec.statistics().conflicts;
    let mut record = |exec: &Executor, output: Vec<String>| {
        let after = exec.statistics().conflicts;
        spent.push((output.concat(), after.saturating_sub(before)));
        before = after;
    };
    let output = exec
        .execute_all(&parse(script).expect("fixture parses"))
        .expect("fixture runs");
    record(exec, output);
    for _ in 0..extra {
        let output = exec
            .execute_all(&parse("(check-sat)").expect("parses"))
            .expect("runs");
        record(exec, output);
    }
    spent
}

#[test]
fn an_incremental_bv_session_grants_each_check_sat_its_rlimit_and_clears_it() {
    // The persistent solver once ran each check-sat under its previous
    // solve's count plus the :rlimit: 2,000, then 4,000, then 6,000 conflicts
    // under :rlimit 2000, until one answered sat on the extra allowance.
    let script = FACTOR16
        .replace("RLIMIT", "2000")
        .replace("(assert (= (bvmul", "(push 1)\n(assert (= (bvmul");
    let mut exec = Executor::new();
    exec.set_timeout(Some(BACKSTOP));
    let spent = repeated_check_sats(&mut exec, &script, 5);
    for (check, (output, conflicts)) in spent.iter().enumerate() {
        assert!(
            *conflicts <= 2_000,
            "check-sat {check} spent {conflicts} conflicts under :rlimit 2000: {spent:?}"
        );
        if output == "unknown" {
            assert_eq!(*conflicts, 2_000, "check-sat {check} ended on its count");
        }
    }
    assert_eq!(spent[0].0, "unknown", "{spent:?}");
    let solver = exec
        .incremental_bv_state()
        .and_then(|state| state.persistent_sat.as_ref())
        .expect("the session keeps its persistent solver");
    assert!(solver.deterministic_inproc());

    // Lifting the :rlimit clears the persistent solver's budgets and its
    // counted schedules; the search then runs to its answer.
    exec.set_resource_limit(None);
    let output = exec
        .execute_all(&parse("(check-sat)").expect("parses"))
        .expect("runs");
    assert_eq!(output, vec!["sat"]);
    let solver = exec
        .incremental_bv_state()
        .and_then(|state| state.persistent_sat.as_ref())
        .expect("the session keeps its persistent solver");
    assert_eq!(solver.conflict_budget(), None);
    assert_eq!(solver.decision_budget(), None);
    assert_eq!(
        solver.deterministic_inproc(),
        ay_sat::deterministic_inproc_enabled()
    );
}

#[test]
fn an_incremental_fp_session_arms_each_check_sat_with_its_rlimit() {
    let script = fp_mul16(Some(300)).replace(
        "(assert (fp.isNormal x))",
        "(push 1)\n(assert (fp.isNormal x))",
    );
    let mut exec = Executor::new();
    exec.set_timeout(Some(BACKSTOP));
    sat_stop::searches::take();
    let spent = repeated_check_sats(&mut exec, &script, 3);
    let searches = sat_stop::searches::take();
    assert!(!searches.is_empty(), "the FP lanes searched");
    for search in &searches {
        assert!(
            search.conflict_budget.is_some_and(|n| n <= 300) && search.counted,
            "each FP search is armed with what is left of :rlimit 300, never a \
             previous solve's count on top: {:?}",
            search.conflict_budget
        );
    }
    for (check, (_, conflicts)) in spent.iter().enumerate() {
        assert!(
            *conflicts <= 300 * searches.len() as u64,
            "check-sat {check} spent {conflicts}: {spent:?}"
        );
    }
}
