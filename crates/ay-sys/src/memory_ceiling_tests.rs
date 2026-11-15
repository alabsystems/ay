// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The memory ceiling is never looser than a bound the kernel shows, and ay
//! keeps 10% headroom below the tightest one.

use super::*;
use std::path::PathBuf;

/// The SAT-COMP 2026 limit read conservatively: 32 GB decimal.
const OFFICIAL: usize = 32_000_000_000;
const GIB: usize = 1024 * 1024 * 1024;

fn ninety_percent(bytes: usize) -> usize {
    bytes / 100 * 90
}

fn cgroup_only(limit: Option<usize>) -> KernelMemoryBounds {
    KernelMemoryBounds {
        cgroup: limit,
        ..KernelMemoryBounds::default()
    }
}

/// A fake cgroup root on disk, removed on drop.
struct FakeCgroupRoot(PathBuf);

impl FakeCgroupRoot {
    fn new(tag: &str) -> Self {
        let dir = std::env::temp_dir().join(format!(
            "ay-sys-memory-ceiling-{tag}-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("create fake cgroup root");
        Self(dir)
    }

    fn limit(&self, cgroup: &str, file: &str, contents: &str) -> &Self {
        let dir = self.0.join(cgroup.trim_start_matches('/'));
        std::fs::create_dir_all(&dir).expect("create fake cgroup");
        std::fs::write(dir.join(file), contents).expect("write fake limit");
        self
    }

    fn v2_limit(&self, proc_self_cgroup: &str) -> Option<usize> {
        cgroup_memory_limit_in(&self.0, &self.0.join("no-v1"), proc_self_cgroup)
    }
}

impl Drop for FakeCgroupRoot {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

#[test]
fn a_cgroup_below_the_ceiling_binds() {
    let root = FakeCgroupRoot::new("below");
    root.limit("/job", "memory.max", "max\n").limit(
        "/job/step",
        "memory.max",
        &format!("{}\n", 8 * GIB),
    );
    let cgroup = root.v2_limit("0::/job/step\n");
    assert_eq!(cgroup, Some(8 * GIB));
    let resolved = limit_under_ceiling_from(OFFICIAL, cgroup_only(cgroup), 1);
    assert_eq!(resolved.binding, BindingBound::Cgroup);
    assert_eq!(resolved.bound_bytes, 8 * GIB);
    assert_eq!(resolved.limit_bytes, ninety_percent(8 * GIB));
}

#[test]
fn a_cgroup_above_the_ceiling_leaves_the_ceiling_binding() {
    let root = FakeCgroupRoot::new("above");
    root.limit("/job", "memory.max", &format!("{}\n", 64 * GIB));
    let cgroup = root.v2_limit("0::/job\n");
    assert_eq!(cgroup, Some(64 * GIB));
    let resolved = limit_under_ceiling_from(OFFICIAL, cgroup_only(cgroup), 1);
    assert_eq!(resolved.binding, BindingBound::Ceiling);
    assert_eq!(resolved.bound_bytes, OFFICIAL);
    assert_eq!(resolved.limit_bytes, ninety_percent(OFFICIAL));
}

#[test]
fn an_absent_cgroup_leaves_the_ceiling_binding() {
    let root = FakeCgroupRoot::new("absent");
    root.limit("/job", "memory.max", "max\n");
    assert_eq!(root.v2_limit("0::/job\n"), None);
    assert_eq!(root.v2_limit(""), None, "no /proc/self/cgroup at all");
    let resolved = limit_under_ceiling_from(OFFICIAL, cgroup_only(None), 1);
    assert_eq!(resolved.binding, BindingBound::Ceiling);
    assert_eq!(resolved.limit_bytes, ninety_percent(OFFICIAL));
    // A zero bound is ignored, never read as "no limit" (fail-open trap).
    assert_eq!(
        limit_under_ceiling_from(OFFICIAL, cgroup_only(Some(0)), 1),
        resolved.clone_with_bounds(cgroup_only(Some(0)))
    );
}

#[test]
fn an_ancestor_tighter_than_the_leaf_binds() {
    let root = FakeCgroupRoot::new("ancestor");
    root.limit("/", "memory.max", "max\n")
        .limit("/user.slice", "memory.max", &format!("{}\n", 4 * GIB))
        .limit("/user.slice/job", "memory.max", &format!("{}\n", 16 * GIB));
    assert_eq!(root.v2_limit("0::/user.slice/job\n"), Some(4 * GIB));
}

#[test]
fn the_walk_stops_at_a_parent_component_and_skips_missing_levels() {
    let root = FakeCgroupRoot::new("walk");
    root.limit("/a/b", "memory.max", &format!("{}\n", 2 * GIB));
    // `/a` has no memory.max: skipped, not unlimited; `/a/b` still counts.
    assert_eq!(root.v2_limit("0::/a/b\n"), Some(2 * GIB));
    // A cgroup outside this namespace's view: only the root is visible.
    assert_eq!(root.v2_limit("0::/../host/job\n"), None);
}

#[test]
fn v1_reads_the_memory_hierarchy_and_both_hierarchies_take_the_minimum() {
    let v1 = FakeCgroupRoot::new("v1");
    v1.limit(
        "/docker/x",
        "memory.limit_in_bytes",
        &format!("{}\n", 6 * GIB),
    );
    let own = "1:name=systemd:/other\n5:cpu,memory:/docker/x\n";
    assert_eq!(
        cgroup_memory_limit_in(&v1.0.join("no-v2"), &v1.0, own),
        Some(6 * GIB)
    );
    let v2 = FakeCgroupRoot::new("v2-and-v1");
    v2.limit("/job", "memory.max", &format!("{}\n", 3 * GIB));
    let both = format!("0::/job\n{own}");
    assert_eq!(cgroup_memory_limit_in(&v2.0, &v1.0, &both), Some(3 * GIB));
}

#[test]
fn each_rlimit_and_the_govern_budget_bind_when_tightest() {
    for (bounds, binding) in [
        (
            KernelMemoryBounds {
                rlimit_as: Some(20 * GIB),
                ..KernelMemoryBounds::default()
            },
            BindingBound::RlimitAs,
        ),
        (
            KernelMemoryBounds {
                rlimit_data: Some(20 * GIB),
                ..KernelMemoryBounds::default()
            },
            BindingBound::RlimitData,
        ),
        (
            KernelMemoryBounds {
                govern_budget: Some(20 * GIB),
                ..KernelMemoryBounds::default()
            },
            BindingBound::GovernBudget,
        ),
    ] {
        let resolved = limit_under_ceiling_from(OFFICIAL, bounds, 1);
        assert_eq!(resolved.binding, binding);
        assert_eq!(resolved.limit_bytes, ninety_percent(20 * GIB));
    }
    let several = KernelMemoryBounds {
        cgroup: Some(24 * GIB),
        rlimit_as: Some(10 * GIB),
        rlimit_data: Some(12 * GIB),
        govern_budget: Some(40 * GIB),
    };
    let resolved = limit_under_ceiling_from(OFFICIAL, several, 1);
    assert_eq!(resolved.binding, BindingBound::RlimitAs);
    assert!(resolved.limit_bytes < resolved.bound_bytes);
}

#[test]
fn peers_split_the_shared_bounds_but_not_the_per_process_ones() {
    let bounds = KernelMemoryBounds {
        cgroup: Some(20 * GIB),
        rlimit_as: Some(9 * GIB),
        ..KernelMemoryBounds::default()
    };
    // Two peers: ceiling share 16e9, cgroup share 10 GiB, RLIMIT_AS 9 GiB.
    let resolved = limit_under_ceiling_from(OFFICIAL, bounds, 2);
    assert_eq!(resolved.binding, BindingBound::RlimitAs);
    let resolved = limit_under_ceiling_from(OFFICIAL, cgroup_only(Some(20 * GIB)), 2);
    assert_eq!(resolved.binding, BindingBound::Cgroup);
    assert_eq!(resolved.bound_bytes, 10 * GIB);
    let resolved = limit_under_ceiling_from(OFFICIAL, cgroup_only(None), 2);
    assert_eq!(resolved.bound_bytes, OFFICIAL / 2);
}

#[test]
fn rlimit_sentinels_mean_no_bound() {
    assert_eq!(soft_rlimit_bound(u64::MAX, u64::MAX), None);
    assert_eq!(
        soft_rlimit_bound(0x7fff_ffff_ffff_ffff, 0x7fff_ffff_ffff_ffff),
        None
    );
    assert_eq!(soft_rlimit_bound(0, u64::MAX), None);
    assert_eq!(soft_rlimit_bound(1 << 30, u64::MAX), Some(1 << 30));
}

#[test]
fn live_detection_is_sane() {
    let bounds = KernelMemoryBounds::detect();
    for bound in [
        bounds.cgroup,
        bounds.rlimit_as,
        bounds.rlimit_data,
        bounds.govern_budget,
    ] {
        assert_ne!(bound, Some(0));
    }
    let resolved = limit_under_ceiling(1 << 40);
    assert!(resolved.limit_bytes > 0 && resolved.limit_bytes <= ninety_percent(1 << 40));
    let origin = resolved.origin();
    assert!(!origin.contains('\n'), "the origin is one line: {origin}");
    assert!(
        origin.starts_with("90% of the tightest memory bound"),
        "{origin}"
    );
}

impl MemoryCeiling {
    fn clone_with_bounds(mut self, bounds: KernelMemoryBounds) -> Self {
        self.bounds = bounds;
        self
    }
}
