// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::unwrap_used)]

use std::cell::{Cell, RefCell};
use std::collections::VecDeque;

use super::super::policy::{
    explore, INITIAL_SLICE, MAX_DISCOVERY_MICROSTEPS, MICROSTEPS_PER_CANDIDATE,
};
use super::super::*;
use super::{CpuSource, WorkClock};
use crate::quantified::counterexample::tests::SEARCH_WINDOW;

/// Per-derivation-depth solver work of the filled-Vec source
/// (`deep::filled_vec_iterator_reaches_position_nine...`), from native probe
/// traces at load 40. Depth 11 is the one SAT derivation; every other depth is
/// UNSAT. Ties with the doubling slices are nudged apart by 5 ms so that no
/// outcome hinges on `after >= child` equality.
const WORK_MS: [(usize, u64); 21] = [
    (2, 20),
    (3, 20),
    (4, 22),
    (5, 35),
    (6, 40),
    (7, 45),
    (8, 60),
    (9, 80),
    (10, 140),
    (11, 900),
    (12, 80),
    (13, 85),
    (14, 105),
    (15, 110),
    (16, 130),
    (17, 120),
    (18, 210),
    (19, 220),
    (20, 240),
    (21, 260),
    (22, 280),
];
const LEADER: usize = 11;
/// Candidates the generator yields in each discovery stage of the same trace;
/// the rest of every stage is `Pending` generator transitions, and the
/// generator never exhausts (the source loops).
const STAGES: [&[usize]; 9] = [
    &[2],
    &[3, 4],
    &[5, 6, 7],
    &[8, 9, 10, 11],
    &[12, 13, 14],
    &[15, 16, 17],
    &[18, 19],
    &[20, 21],
    &[22],
];
const DISCOVERY_STEP: Duration = Duration::from_micros(200);
const ENVELOPE: Duration = Duration::from_secs(15);
/// CPU the same filled-Vec probe takes on each core of the development host,
/// in percent of an X925 core: 1.51-1.71x (median 1.63x) on an A725, measured
/// per decided probe (depths 3-17) on pinned cores.
const X925: u32 = 100;
const A725: u32 = 163;

fn work(depth: usize) -> Duration {
    let (_, ms) = WORK_MS.iter().find(|(d, _)| *d == depth).unwrap();
    Duration::from_millis(*ms)
}

/// Every depth starts at the initial slice; depth 11 needs more than five
/// doublings of it, so the scenario exercises the retry schedule.
fn discovery_script() -> VecDeque<Option<usize>> {
    assert!(INITIAL_SLICE * 32 < work(LEADER));
    let mut script = VecDeque::new();
    let mut quota = 1usize;
    for stage in STAGES {
        script.extend(stage.iter().copied().map(Some));
        let microsteps = (quota * MICROSTEPS_PER_CANDIDATE).min(MAX_DISCOVERY_MICROSTEPS);
        if stage.len() < quota {
            script.extend(std::iter::repeat_n(None, microsteps - stage.len()));
        }
        quota *= 2;
    }
    script
}

/// A single-threaded searcher sharing its core: every unit of its CPU work
/// costs `slowdown` units of wall time. The same solver work costs `core`
/// percent of the X925's CPU, and the search fails closed after `envelope`.
struct Machine {
    origin: Instant,
    cpu: Cell<Duration>,
    wall: Cell<Instant>,
    slowdown: u32,
    core: u32,
    envelope: Duration,
}

impl Machine {
    fn new(slowdown: u32, core: u32, envelope: Duration) -> Self {
        let origin = Instant::now();
        Self {
            origin,
            cpu: Cell::new(Duration::ZERO),
            wall: Cell::new(origin),
            slowdown,
            core,
            envelope,
        }
    }

    /// The CPU this machine's core spends on `work` measured on an X925.
    fn cost(&self, work: Duration) -> Duration {
        work * self.core / X925
    }

    fn run(&self, work: Duration) {
        self.cpu.set(self.cpu.get() + work);
        self.wall.set(self.wall.get() + work * self.slowdown);
    }

    fn backstop(&self) -> Instant {
        self.origin + self.envelope
    }
}

struct Cpu<'a>(&'a Cell<Duration>);

impl CpuSource for Cpu<'_> {
    fn cpu(&self) -> Option<Duration> {
        Some(self.0.get())
    }
}

struct Outcome {
    found: Option<usize>,
    /// Every probe with the CPU its slice actually bought.
    slices: Vec<(usize, Duration)>,
    wall: Duration,
}

/// The production policy on a simulated machine. `metered` schedules on the
/// work clock (this module's fix); otherwise on the wall (the old clock).
fn dovetail(slowdown: u32, metered: bool) -> Outcome {
    dovetail_on(Machine::new(slowdown, X925, ENVELOPE), metered)
}

fn dovetail_on(machine: Machine, metered: bool) -> Outcome {
    let slowdown = machine.slowdown;
    let clock = WorkClock::with_source(machine.origin, Cpu(&machine.cpu)).unwrap();
    let token = CancellationToken::new();
    let control = SourceControl::new(machine.origin + Duration::from_secs(600), &token);
    let script = RefCell::new(discovery_script());
    let slices = RefCell::new(Vec::new());
    let now = || {
        if metered {
            clock.now()
        } else {
            machine.wall.get()
        }
    };
    let found = explore(
        machine.backstop(),
        &control,
        now,
        || {
            // The real search's control polls the same wall deadline.
            if machine.wall.get() >= machine.backstop() {
                return None;
            }
            machine.run(machine.cost(DISCOVERY_STEP));
            Some(match script.borrow_mut().pop_front().flatten() {
                Some(depth) => Discovery::Candidate(depth),
                None => Discovery::Pending,
            })
        },
        |depth: &usize, child| {
            if machine.wall.get() >= machine.backstop() {
                return Probe::Terminal;
            }
            let bought = if metered {
                clock
                    .work_until(child)
                    .unwrap()
                    .saturating_sub(machine.cpu.get())
            } else {
                child.saturating_duration_since(machine.wall.get()) / slowdown
            };
            slices.borrow_mut().push((*depth, bought));
            let needed = machine.cost(work(*depth));
            let verdict = if needed <= bought {
                machine.run(needed);
                if *depth == LEADER {
                    Probe::Sat
                } else {
                    Probe::Unsat
                }
            } else {
                machine.run(bought);
                Probe::Inconclusive
            };
            if machine.wall.get() >= machine.backstop() {
                // The solver's wall backstop stopped this probe.
                machine.wall.set(machine.backstop());
                return Probe::Terminal;
            }
            verdict
        },
    );
    Outcome {
        found,
        slices: slices.into_inner(),
        wall: machine.wall.get() - machine.origin,
    }
}

#[test]
fn work_clock_follows_cpu_and_ignores_descheduled_wall() {
    let origin = Instant::now();
    let cpu = Cell::new(Duration::from_millis(700));
    let clock = WorkClock::with_source(origin, Cpu(&cpu)).unwrap();
    assert_eq!(clock.now(), origin);
    cpu.set(Duration::from_millis(950));
    assert_eq!(clock.now(), origin + Duration::from_millis(250));
    // A slice ending 400 ms of scheduling time after the origin is spent when
    // the thread's CPU clock reads 700 + 400 ms, however long the wall takes.
    let child = origin + Duration::from_millis(400);
    assert_eq!(clock.work_until(child), Some(Duration::from_millis(1_100)));
    assert_eq!(clock.work_until(origin), Some(Duration::from_millis(700)));
}

/// The regression: the same source, the same envelope, a machine twice as
/// contended. On the wall clock the depth-11 counterexample is lost; on the
/// work clock every slice, retirement and discovery decision is identical to
/// the idle run and the counterexample is found, only later in wall time.
#[test]
fn contention_stretches_the_dovetail_without_reshaping_it() {
    let idle = dovetail(1, true);
    let contended = dovetail(2, true);
    assert_eq!(idle.found, Some(LEADER));
    assert_eq!(contended.found, Some(LEADER));
    assert_eq!(
        idle.slices, contended.slices,
        "contention must stretch the schedule, never reshape it"
    );
    assert!(contended.wall < ENVELOPE, "{:?}", contended.wall);
    assert!(contended.wall >= idle.wall * 2);

    // The old wall clock: identical when idle, but under the same 2x
    // contention its slices buy half the work, the fair shares shrink as the
    // deadline nears, and the counterexample is never probed long enough.
    let wall_idle = dovetail(1, false);
    let wall_contended = dovetail(2, false);
    assert_eq!(wall_idle.slices, idle.slices);
    assert_eq!(wall_idle.found, Some(LEADER));
    assert_eq!(wall_contended.found, None, "the load-dependent verdict");
    assert!(wall_contended.slices.len() > idle.slices.len());
    assert!(wall_contended
        .slices
        .iter()
        .filter(|(depth, _)| *depth == LEADER)
        .all(|(_, bought)| *bought < work(LEADER)));

    // The caller's envelope stays the bound: past it the search fails closed.
    let overloaded = dovetail(3, true);
    assert_eq!(overloaded.found, None);
    assert!(overloaded.wall >= ENVELOPE);
}

/// A slower core is not contention. Contention only delays the searching
/// thread, which the work clock stretches away (above); a core that needs
/// more CPU for the same probe buys less work with every CPU slice. So even an
/// idle A725 reshapes the schedule as the wall clock did under contention: the
/// leader earns its 1.6 s allowance, but the shrinking fair share of the 15 s
/// envelope caps every retry below what its probe needs and the counterexample
/// is lost (on the engine: capped at 742, 621, 629, 479, 355 and 204 ms against
/// a 0.91 s probe). No clock absorbs a slower core; an envelope sized for the
/// work does, even when contended, which is why `tests::deep` hands the search
/// its own `SEARCH_WINDOW` instead of the quarter of a 60 s solve.
#[test]
fn a_slower_core_is_absorbed_only_by_an_envelope_sized_for_the_work() {
    let reference = dovetail(1, true);
    let slower = dovetail_on(Machine::new(1, A725, ENVELOPE), true);
    assert_eq!(reference.found, Some(LEADER));
    assert_eq!(slower.found, None, "the core-dependent verdict");
    assert!(slower.wall >= ENVELOPE, "{:?}", slower.wall);
    let need = work(LEADER) * A725 / X925;
    let leader: Vec<_> = slower
        .slices
        .iter()
        .filter(|(depth, _)| *depth == LEADER)
        .map(|(_, bought)| *bought)
        .collect();
    assert!(leader.iter().all(|bought| *bought < need), "{leader:?}");
    assert!(leader.contains(&(INITIAL_SLICE * 32)), "{leader:?}");

    let sized = dovetail_on(Machine::new(1, A725, SEARCH_WINDOW), true);
    let overloaded = dovetail_on(Machine::new(5, A725, SEARCH_WINDOW), true);
    assert_eq!(sized.found, Some(LEADER));
    assert_eq!(overloaded.found, Some(LEADER));
    assert_eq!(sized.slices, overloaded.slices);
    assert!(overloaded.wall < SEARCH_WINDOW, "{:?}", overloaded.wall);
}
