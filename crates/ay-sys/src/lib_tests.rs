// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_current_rss_nonzero() {
    let rss = current_rss_bytes();
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    assert!(rss > 1024 * 1024, "RSS should be at least 1MB, got {rss}");
}

#[test]
fn test_physical_memory_nonzero() {
    let phys = physical_memory_bytes();
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    assert!(
        phys > 1024 * 1024 * 1024,
        "Physical memory should be at least 1GB, got {phys}"
    );
}

#[test]
fn test_default_memory_limit_reasonable() {
    let limit = default_memory_limit();
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    {
        assert!(limit >= 2 * 1024 * 1024 * 1024, "Limit should be >= 2GB");
        assert!(limit <= 64 * 1024 * 1024 * 1024, "Limit should be <= 64GB");
    }
}

#[test]
fn test_process_memory_limit_default_disabled() {
    // Default limit is 0 (disabled)
    assert!(!process_memory_exceeded());
}

#[test]
fn test_process_memory_limit_tiny() {
    // Save and restore
    let old = get_process_memory_limit();
    set_process_memory_limit(1024); // 1 KB - any running process exceeds this
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    assert!(process_memory_exceeded());
    set_process_memory_limit(old);
}

#[test]
fn test_process_memory_limit_huge() {
    let old = get_process_memory_limit();
    set_process_memory_limit(1024 * 1024 * 1024 * 1024); // 1 TB
    assert!(!process_memory_exceeded());
    set_process_memory_limit(old);
}

#[test]
fn test_system_available_bytes_within_physical() {
    let avail = system_available_bytes();
    let phys = physical_memory_bytes();
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    {
        assert!(avail > 0, "system_available_bytes should be non-zero");
        // Available can be slightly higher than "free" but never larger than
        // physical memory. Allow a tiny slack for kernel accounting race.
        if phys > 0 {
            assert!(
                avail <= phys.saturating_add(phys / 10),
                "available {avail} exceeds physical {phys} + 10% slack",
            );
        }
    }
    #[cfg(not(any(target_os = "macos", target_os = "linux")))]
    {
        // Fallback path returns physical (or 0 if that also fails).
        let _ = (avail, phys);
    }
}

#[test]
fn test_effective_available_bytes_no_rlimit() {
    // Deterministic: with no rlimit, effective = 0.75 * system_available. Use a
    // fixed `avail` rather than reading the live (volatile) system figure twice,
    // which made this assertion flaky under memory pressure.
    let avail = 8 * 1024 * 1024 * 1024; // 8 GB
    assert_eq!(
        effective_available_bytes_from(avail, 0),
        avail.saturating_mul(3) / 4
    );
}

#[test]
fn test_effective_available_bytes_rlimit_tightens() {
    let avail = 8 * 1024 * 1024 * 1024; // 8 GB => headroom 6 GB
                                        // A small rlimit below the headroom wins.
    let small = 100 * 1024 * 1024; // 100 MB
    assert_eq!(effective_available_bytes_from(avail, small), small);
    // A large rlimit above the headroom does not raise the effective figure.
    let large = 1024 * 1024 * 1024 * 1024; // 1 TB
    assert_eq!(
        effective_available_bytes_from(avail, large),
        avail.saturating_mul(3) / 4
    );
}

// ---------------------------------------------------------------------------
// cgroup memory-limit detection (pure cores; run on every platform)
// ---------------------------------------------------------------------------

#[test]
fn test_parse_cgroup_memory_limit_numeric() {
    // A real ceiling (v2 numeric value or v1 limit_in_bytes), trailing newline
    // as read from the cgroupfs file.
    assert_eq!(
        parse_cgroup_memory_limit("4294967296\n"),
        Some(4 * 1024 * 1024 * 1024)
    );
    assert_eq!(parse_cgroup_memory_limit("  134217728  "), Some(134217728));
}

#[test]
fn test_parse_cgroup_memory_limit_v2_max_is_unlimited() {
    assert_eq!(parse_cgroup_memory_limit("max\n"), None);
}

#[test]
fn test_parse_cgroup_memory_limit_v1_sentinel_is_unlimited() {
    // The kernel's v1 "no limit": PAGE_COUNTER_MAX * PAGE_SIZE, i.e. i64::MAX
    // rounded down to a page multiple.
    assert_eq!(parse_cgroup_memory_limit("9223372036854771712\n"), None);
    // Threshold boundary: anything >= i64::MAX / 2 is a sentinel.
    let floor = u64::try_from(i64::MAX).unwrap() / 2;
    assert_eq!(parse_cgroup_memory_limit(&floor.to_string()), None);
    #[cfg(target_pointer_width = "64")]
    assert_eq!(
        parse_cgroup_memory_limit(&(floor - 1).to_string()),
        Some(usize::try_from(floor - 1).unwrap())
    );
}

#[test]
fn test_parse_cgroup_memory_limit_no_information_yields_none() {
    // Garbage / empty / zero carry no usable ceiling: `None` here means the
    // caller falls back to host RAM. Returning Some(0) instead would read as
    // "detection failed" downstream and DISABLE the limit (fail-open).
    assert_eq!(parse_cgroup_memory_limit(""), None);
    assert_eq!(parse_cgroup_memory_limit("not-a-number\n"), None);
    assert_eq!(parse_cgroup_memory_limit("-1\n"), None);
    assert_eq!(parse_cgroup_memory_limit("0\n"), None);
}

#[test]
fn test_effective_physical_memory_takes_minimum() {
    let host = 512 * 1024 * 1024 * 1024; // 512 GB host
    let cgroup = 4 * 1024 * 1024 * 1024; // 4 GB container ceiling
                                         // Missing cgroup files → host fallback.
    assert_eq!(effective_physical_memory_from(host, None), host);
    // The tighter bound wins in both directions.
    assert_eq!(effective_physical_memory_from(host, Some(cgroup)), cgroup);
    assert_eq!(effective_physical_memory_from(cgroup, Some(host)), cgroup);
    // Host detection failed but a cgroup ceiling is known → use it
    // (fail-closed: a real bound beats "unknown").
    assert_eq!(effective_physical_memory_from(0, Some(cgroup)), cgroup);
    assert_eq!(effective_physical_memory_from(0, None), 0);
}

#[cfg(not(target_arch = "wasm32"))]
#[test]
fn test_default_limit_floors_never_exceed_detected_ceiling() {
    let gb = 1024 * 1024 * 1024;
    // 1 GB container: the old flat 2 GB floor exceeded the ceiling the kernel
    // enforces — OOM-kill before any watermark could trip.
    assert_eq!(default_memory_limit_from(gb), gb);
    assert_eq!(default_standalone_memory_limit_from(gb), gb);
    assert_eq!(default_embedded_memory_limit_from(gb), gb);
    // Ceiling above the floor: the 2 GB floor still applies as before.
    assert_eq!(default_memory_limit_from(3 * gb), 2 * gb);
    // Large-host behavior unchanged: phys/2 in [2,64] GB, 85%, phys/8 in
    // [2,16] GB respectively.
    assert_eq!(default_memory_limit_from(16 * gb), 8 * gb);
    assert_eq!(default_standalone_memory_limit_from(20 * gb), 17 * gb);
    assert_eq!(default_embedded_memory_limit_from(64 * gb), 8 * gb);
    // Detection failure still disables the limit.
    assert_eq!(default_memory_limit_from(0), 0);
    assert_eq!(default_standalone_memory_limit_from(0), 0);
    assert_eq!(default_embedded_memory_limit_from(0), 0);
}

/// The real Linux read path (cgroupfs + sysconf) must never panic, whatever
/// environment the test runs in (bare host, v1 or v2 cgroup, container), and
/// any detected figure must be a usable ceiling.
#[cfg(target_os = "linux")]
#[test]
fn test_linux_cgroup_and_physical_memory_paths_no_panic() {
    if let Some(limit) = cgroup_memory_limit_bytes() {
        assert!(limit > 0, "detected cgroup limit must be a real ceiling");
        assert!(
            physical_memory_bytes() <= limit,
            "physical_memory_bytes must honor the cgroup ceiling"
        );
    }
    // Covered by test_physical_memory_nonzero too, but assert the clamped
    // figure stays sane here as well.
    assert!(physical_memory_bytes() > 0);
}

// ---------------------------------------------------------------------------
// Live-bytes counter + CountingAllocator (L2 OOM guard)
// ---------------------------------------------------------------------------
//
// NOTE: `LIVE_BYTES` is process-global. The test binary does *not* install
// `CountingAllocator` as its `#[global_allocator]`, so the counter is only ever
// moved by these tests' explicit `add_live_bytes`/`sub_live_bytes` calls. Each
// test saves and restores the counter to stay robust if that ever changes, and
// they avoid asserting an exact absolute value mid-flight to avoid coupling to
// any background allocator activity.

#[test]
fn test_live_bytes_add_then_sub_round_trips() {
    let base = current_live_bytes();
    add_live_bytes(4096);
    assert_eq!(current_live_bytes(), base + 4096);
    sub_live_bytes(4096);
    assert_eq!(current_live_bytes(), base);
}

#[test]
fn test_sub_live_bytes_saturates_at_zero() {
    // Underflow must clamp at 0, never wrap to a huge value that would
    // spuriously trip `process_memory_exceeded`.
    let base = current_live_bytes();
    // Drain whatever is there, then over-subtract.
    sub_live_bytes(base);
    assert_eq!(current_live_bytes(), 0);
    sub_live_bytes(1_000_000);
    assert_eq!(current_live_bytes(), 0, "underflow must clamp to zero");
    // Restore the prior baseline for any concurrently-running tests.
    add_live_bytes(base);
}

#[test]
fn test_process_memory_exceeded_trips_on_live_bytes() {
    // Live-bytes alone (no RSS growth) must be able to trip the ceiling: this is
    // the burst-detection property that peak-RSS-via-getrusage misses.
    let old_limit = get_process_memory_limit();
    let base = current_live_bytes();

    // 1 GB ceiling; push live bytes to 1.5 GB (well above the 95% threshold).
    let limit = 1024 * 1024 * 1024;
    set_process_memory_limit(limit);
    add_live_bytes(limit + limit / 2);
    assert!(
        process_memory_exceeded(),
        "live bytes above ceiling must trip process_memory_exceeded"
    );

    // Drop back below the threshold; with a real-but-modest RSS the check should
    // clear (assuming the test process is not itself over a 1 GB limit, which is
    // true for a unit-test binary).
    sub_live_bytes(limit + limit / 2);
    // Restore state before the RSS-dependent assertion to avoid leaking the
    // limit into other tests on failure.
    set_process_memory_limit(old_limit);
    add_live_bytes(base.saturating_sub(current_live_bytes()));
}

#[test]
fn test_process_memory_exceeded_at_percent_predictive_threshold() {
    // The lower (predictive) thresholds must trip on a smaller fraction of the
    // limit than the 95% hard guard. This is the pre-clone backpressure property:
    // at ~53% usage the imminent (≈1.8x) clone would breach, so the 53% probe
    // fires while the 95% guard is still clear.
    let old_limit = get_process_memory_limit();
    let base = current_live_bytes();

    // 1 GB ceiling; push live to 600 MB (60% of limit).
    let limit = 1024 * 1024 * 1024;
    set_process_memory_limit(limit);
    let used = limit * 60 / 100;
    add_live_bytes(used);

    // 53% probe trips (60% > 53%); 95% hard guard does not (60% < 95%).
    assert!(
        process_memory_exceeded_at_percent(53),
        "60% usage must trip the 53% predictive probe"
    );
    assert!(
        !process_memory_exceeded_at_percent(95),
        "60% usage must NOT trip the 95% hard guard"
    );
    // The public alias is the 95% guard, so it must agree.
    assert!(
        !process_memory_exceeded(),
        "process_memory_exceeded() is the 95% guard and must stay clear at 60%"
    );

    // No limit set => strict no-op for every percentage.
    set_process_memory_limit(0);
    assert!(!process_memory_exceeded_at_percent(1));
    assert!(!process_memory_exceeded_at_percent(53));

    // Restore.
    sub_live_bytes(used);
    set_process_memory_limit(old_limit);
    add_live_bytes(base.saturating_sub(current_live_bytes()));
}

#[test]
fn test_counting_allocator_tracks_live_bytes() {
    use std::alloc::{GlobalAlloc, Layout, System};

    let base = current_live_bytes();
    let alloc = CountingAllocator::new(System);
    let layout = Layout::from_size_align(8192, 8).unwrap();

    // SAFETY: `layout` is non-zero-sized and well-formed; the pointer returned
    // is freed exactly once below with the same layout.
    let ptr = unsafe { alloc.alloc(layout) };
    assert!(!ptr.is_null());
    assert_eq!(
        current_live_bytes(),
        base + 8192,
        "alloc must add layout.size() live bytes"
    );

    // SAFETY: `ptr` came from `alloc.alloc(layout)` just above with this layout.
    unsafe { alloc.dealloc(ptr, layout) };
    assert_eq!(
        current_live_bytes(),
        base,
        "dealloc must subtract layout.size() live bytes"
    );
}

#[test]
fn test_counting_allocator_realloc_grow_and_shrink() {
    use std::alloc::{GlobalAlloc, Layout, System};

    let base = current_live_bytes();
    let alloc = CountingAllocator::new(System);
    let layout = Layout::from_size_align(1024, 8).unwrap();

    // SAFETY: well-formed non-zero layout; freed once below.
    let ptr = unsafe { alloc.alloc(layout) };
    assert!(!ptr.is_null());
    assert_eq!(current_live_bytes(), base + 1024);

    // Grow 1024 -> 4096: +3072.
    // SAFETY: `ptr`/`layout` are the live block; `new_size` is non-zero.
    let ptr = unsafe { alloc.realloc(ptr, layout, 4096) };
    assert!(!ptr.is_null());
    assert_eq!(current_live_bytes(), base + 4096, "grow must add the delta");

    // Shrink 4096 -> 512: -3584. The block's current layout size is 4096.
    let grown = Layout::from_size_align(4096, 8).unwrap();
    // SAFETY: `ptr` is the live block whose current size is 4096.
    let ptr = unsafe { alloc.realloc(ptr, grown, 512) };
    assert!(!ptr.is_null());
    assert_eq!(
        current_live_bytes(),
        base + 512,
        "shrink must subtract the delta"
    );

    let shrunk = Layout::from_size_align(512, 8).unwrap();
    // SAFETY: frees the live block with its current (512-byte) layout.
    unsafe { alloc.dealloc(ptr, shrunk) };
    assert_eq!(current_live_bytes(), base);
}
