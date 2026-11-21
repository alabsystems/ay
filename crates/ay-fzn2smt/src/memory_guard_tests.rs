// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

const MIB: usize = 1024 * 1024;
const GIB: usize = 1024 * MIB;

#[test]
fn the_harness_limit_is_read_in_mib() {
    assert_eq!(env_ceiling_bytes(None), None);
    assert_eq!(env_ceiling_bytes(Some("16384")), Some(16 * GIB));
    assert_eq!(env_ceiling_bytes(Some(" 512\n")), Some(512 * MIB));
    assert_eq!(env_ceiling_bytes(Some("0")), None);
    assert_eq!(env_ceiling_bytes(Some("-1")), None);
    assert_eq!(env_ceiling_bytes(Some("16G")), None);
    assert_eq!(env_ceiling_bytes(Some(&usize::MAX.to_string())), None);
}

/// Nothing bounds the run: nothing is supervised. Otherwise ay keeps 10%
/// below the tightest of the harness limit and the kernel bounds.
#[test]
fn the_limit_is_ninety_percent_of_the_tightest_bound() {
    assert_eq!(plan_limit(None, KernelMemoryBounds::default(), 1), None);

    let harness = plan_limit(Some(16 * GIB), KernelMemoryBounds::default(), 1)
        .expect("a harness limit bounds the run");
    assert_eq!(harness.limit_bytes, 16 * GIB / 100 * 90);

    let cgroup_only = KernelMemoryBounds {
        cgroup: Some(8 * GIB),
        ..KernelMemoryBounds::default()
    };
    let tighter_cgroup = plan_limit(Some(16 * GIB), cgroup_only, 1).expect("bounded");
    assert_eq!(tighter_cgroup.limit_bytes, 8 * GIB / 100 * 90);
    let cgroup = plan_limit(None, cgroup_only, 1).expect("a cgroup limit bounds the run");
    assert_eq!(cgroup.limit_bytes, 8 * GIB / 100 * 90);
}

/// The memory kills of run ay-minizinc-fix-20261118: the job's cgroup held
/// MiniZinc (2.2 GB on warehouse/wlp22) beside ay, so ay's own memory alone
/// can look safe while the job is about to be killed at 16 GiB.
#[test]
fn the_job_cgroup_stops_the_run_when_the_process_alone_looks_safe() {
    let limit = 16 * GIB / 100 * 90;
    assert_eq!(memory_state(6 * GIB, limit, &[]), MemoryState::Within);
    assert_eq!(
        memory_state(limit / 100 * 96, limit, &[]),
        MemoryState::Stop
    );
    assert_eq!(memory_state(limit, limit, &[]), MemoryState::Critical);

    let job = |used| CgroupUsage {
        limit: 16 * GIB,
        used,
    };
    // ay at 12 GiB (81% of its own limit) with MiniZinc at 2.2 GiB.
    let own = 12 * GIB;
    assert_eq!(
        memory_state(own, limit, &[job(own + 2 * GIB)]),
        MemoryState::Stop
    );
    assert_eq!(
        memory_state(own, limit, &[job(own + 2 * GIB + 300 * MIB)]),
        MemoryState::Critical
    );
    assert_eq!(
        memory_state(own, limit, &[job(own + 100 * MIB)]),
        MemoryState::Within
    );
    // An unlimited ancestor (no level) or a zero budget never trips.
    assert_eq!(memory_state(own, 0, &[]), MemoryState::Within);
}

#[test]
fn cgroup_usage_excludes_page_cache_and_needs_a_limit() {
    assert_eq!(cgroup_level_usage(Some("max\n"), Some("100"), None), None);
    assert_eq!(cgroup_level_usage(Some("1000\n"), None, None), None);
    assert_eq!(
        cgroup_level_usage(
            Some("1000\n"),
            Some("900\n"),
            Some("anon 500\nfile 300\nkernel 100\n")
        ),
        Some(CgroupUsage {
            limit: 1000,
            used: 600
        })
    );
    assert_eq!(
        cgroup_level_usage(Some("1000"), Some("900"), Some("anon 900\n")),
        Some(CgroupUsage {
            limit: 1000,
            used: 900
        })
    );
}

/// A memory stop prints UNKNOWN only while nothing is on the solution stream:
/// once a solution has been written it stays the answer, with no status line
/// after it.
#[test]
fn a_stop_after_a_solution_keeps_the_solution() {
    assert_eq!(settle_at_hard_ceiling(0), CeilingSettlement::ArmedVerdict);
    let mut out = GuardedOutput::new(Vec::new());
    out.write_all(b"").expect("write");
    assert_eq!(settle_at_hard_ceiling(0), CeilingSettlement::ArmedVerdict);
    out.write_all(b"x = 3;\n----------\n").expect("write");
    out.flush().expect("flush");
    assert_eq!(settle_at_hard_ceiling(0), CeilingSettlement::Silent(0));
    assert_eq!(out.inner, b"x = 3;\n----------\n");
    assert_eq!(HARD_CEILING_ACTION.stdout_line, b"=====UNKNOWN=====\n");
    assert_eq!(HARD_CEILING_ACTION.exit_code, 0);
}

/// The deadline watchdog asks the run to stop the grace before the
/// deadline and ends it at the deadline, never before.
#[test]
fn deadline_watchdog_stops_before_the_deadline_and_finishes_at_it() {
    let deadline = Instant::now() + Duration::from_millis(80);
    let grace = Duration::from_millis(30);
    let stopped = std::cell::Cell::new(None);
    let finished = std::cell::Cell::new(None);
    deadline_watchdog(
        deadline,
        grace,
        || stopped.set(Some(Instant::now())),
        || finished.set(Some(Instant::now())),
    );
    let stopped = stopped.get().expect("stop was asked");
    let finished = finished.get().expect("the run was ended");
    assert!(
        stopped >= deadline - grace,
        "asked to stop before the grace"
    );
    assert!(finished >= deadline, "ended before the deadline");
    assert!(finished >= stopped);
}

/// A deadline already past: both actions at once, in order.
#[test]
fn deadline_watchdog_with_a_past_deadline_acts_at_once() {
    let order = std::cell::RefCell::new(Vec::new());
    deadline_watchdog(
        Instant::now(),
        Duration::ZERO,
        || order.borrow_mut().push("stop"),
        || order.borrow_mut().push("finish"),
    );
    assert_eq!(*order.borrow(), ["stop", "finish"]);
}
