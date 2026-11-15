// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A hard memory ceiling for one run, such as a competition's limit, that can
//! never be looser than a limit the kernel already shows.
//!
//! `ay solve --memory-ceiling-bytes N` does not make N the budget. ay's own
//! memory limit becomes 90% ([`crate::KERNEL_BUDGET_HEADROOM_PERCENT`]) of the
//! SMALLEST of: N; the cgroup memory limit the process runs under, read from
//! its own cgroup and each ancestor visible in its cgroup namespace (v2
//! `memory.max`, v1 `memory.limit_in_bytes`); its `RLIMIT_AS` and
//! `RLIMIT_DATA` soft limits; and the macOS govern kernel budget when one is
//! armed. The bounds a job shares (N and the cgroup) are split across detected
//! peer ay processes (`AY_CONCURRENCY`, or the CPU count under a test harness,
//! as for the default limit). Owner decision, 2026-09-12: the SAT-COMP
//! constant is a ceiling, not an override.
//!
//! The 10% headroom gives ay's graceful stop at 95% of its own limit room to
//! run before a cgroup or govern kill. An rlimit fails an allocation (ENOMEM)
//! instead of killing, and it counts address space or the data segment, which
//! ay's heap accounting tracks only approximately, so there the headroom is a
//! margin, not a guarantee. Physical RAM and swap are not bounds here.

#[cfg(any(target_os = "linux", test))]
use std::path::Path;

/// The memory bounds the kernel shows this process, in bytes; `None` means
/// no bound of that kind.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct KernelMemoryBounds {
    /// The cgroup memory limit, tightest over the process's cgroup and its
    /// ancestors.
    pub cgroup: Option<usize>,
    /// The `RLIMIT_AS` soft limit (address space).
    pub rlimit_as: Option<usize>,
    /// The `RLIMIT_DATA` soft limit.
    pub rlimit_data: Option<usize>,
    /// The macOS govern kernel budget, when armed.
    pub govern_budget: Option<usize>,
}

impl KernelMemoryBounds {
    /// Read the bounds in force for this process now.
    #[must_use]
    pub fn detect() -> Self {
        Self {
            cgroup: live_cgroup_limit(),
            rlimit_as: soft_rlimit_bytes(Rlimit::AddressSpace),
            rlimit_data: soft_rlimit_bytes(Rlimit::Data),
            govern_budget: crate::govern::active_budget_bytes(),
        }
    }
}

/// Which bound decided the limit.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BindingBound {
    /// The caller's ceiling (`--memory-ceiling-bytes`).
    Ceiling,
    /// The cgroup memory limit.
    Cgroup,
    /// The `RLIMIT_AS` soft limit.
    RlimitAs,
    /// The `RLIMIT_DATA` soft limit.
    RlimitData,
    /// The macOS govern kernel budget.
    GovernBudget,
}

impl BindingBound {
    fn label(self) -> &'static str {
        match self {
            Self::Ceiling => "the ceiling",
            Self::Cgroup => "the cgroup limit",
            Self::RlimitAs => "RLIMIT_AS",
            Self::RlimitData => "RLIMIT_DATA",
            Self::GovernBudget => "the govern kernel budget",
        }
    }
}

/// The limit ay takes under a ceiling, with how it was decided.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MemoryCeiling {
    /// The caller's ceiling in bytes.
    pub ceiling_bytes: usize,
    /// Detected peer ay processes the shared bounds were split across.
    pub peers: usize,
    /// The kernel bounds that were considered.
    pub bounds: KernelMemoryBounds,
    /// Which bound decided the limit.
    pub binding: BindingBound,
    /// The binding bound in bytes, after the peer split for shared bounds.
    pub bound_bytes: usize,
    /// ay's own memory limit: 90% of `bound_bytes`.
    pub limit_bytes: usize,
}

impl MemoryCeiling {
    /// One line naming the limit's origin, for the memout note and the log.
    #[must_use]
    pub fn origin(&self) -> String {
        const MIB: usize = 1024 * 1024;
        let mib = |bound: Option<usize>| {
            bound.map_or_else(
                || "none".to_string(),
                |bytes| format!("{} MiB", bytes / MIB),
            )
        };
        let peers = if self.peers > 1 {
            format!(", shared bounds split across {} peers", self.peers)
        } else {
            String::new()
        };
        format!(
            "{}% of the tightest memory bound, {} at {} MiB (ceiling {} bytes{peers}; cgroup {}; RLIMIT_AS {}; RLIMIT_DATA {}; govern budget {})",
            crate::KERNEL_BUDGET_HEADROOM_PERCENT,
            self.binding.label(),
            self.bound_bytes / MIB,
            self.ceiling_bytes,
            mib(self.bounds.cgroup),
            mib(self.bounds.rlimit_as),
            mib(self.bounds.rlimit_data),
            mib(self.bounds.govern_budget),
        )
    }
}

/// ay's own memory limit under `ceiling_bytes`, against the bounds in force
/// now; see the module docs.
#[must_use]
pub fn limit_under_ceiling(ceiling_bytes: usize) -> MemoryCeiling {
    limit_under_ceiling_from(
        ceiling_bytes,
        KernelMemoryBounds::detect(),
        crate::detected_concurrency(),
    )
}

/// Pure core of [`limit_under_ceiling`]: the tightest of the ceiling and
/// every present bound (a zero bound is ignored, never read as "no limit"),
/// with the shared ones split across `peers`, then 90% of it. A tie credits
/// the ceiling.
#[must_use]
pub fn limit_under_ceiling_from(
    ceiling_bytes: usize,
    bounds: KernelMemoryBounds,
    peers: usize,
) -> MemoryCeiling {
    let peers = peers.max(1);
    let share = |bytes: usize| bytes / peers;
    let mut binding = BindingBound::Ceiling;
    let mut bound_bytes = share(ceiling_bytes).max(1);
    for (source, bound) in [
        (BindingBound::Cgroup, bounds.cgroup.map(share)),
        (BindingBound::RlimitAs, bounds.rlimit_as),
        (BindingBound::RlimitData, bounds.rlimit_data),
        (BindingBound::GovernBudget, bounds.govern_budget),
    ] {
        if let Some(bytes) = bound.filter(|&bytes| bytes > 0 && bytes < bound_bytes) {
            bound_bytes = bytes;
            binding = source;
        }
    }
    MemoryCeiling {
        ceiling_bytes,
        peers,
        bounds,
        binding,
        bound_bytes,
        limit_bytes: crate::standalone_limit_under_kernel_bound(bound_bytes).max(1),
    }
}

/// A soft rlimit as a bound: the platform's `RLIM_INFINITY` and 0 mean none.
#[cfg(any(unix, test))]
pub(crate) fn soft_rlimit_bound(current: u64, infinity: u64) -> Option<usize> {
    if current == infinity || current == 0 {
        None
    } else {
        usize::try_from(current).ok()
    }
}

#[derive(Clone, Copy)]
enum Rlimit {
    AddressSpace,
    Data,
}

#[cfg(unix)]
fn soft_rlimit_bytes(which: Rlimit) -> Option<usize> {
    let resource = match which {
        Rlimit::AddressSpace => libc::RLIMIT_AS,
        Rlimit::Data => libc::RLIMIT_DATA,
    };
    let mut limit = libc::rlimit {
        rlim_cur: 0,
        rlim_max: 0,
    };
    // SAFETY: getrlimit(2) writes one fully initialized `rlimit` into `limit`,
    // an owned local borrowed exclusively for this call; `resource` is a valid
    // platform constant; a failure is reported through the return value and
    // leaves `limit` unread.
    if unsafe { libc::getrlimit(resource, &raw mut limit) } != 0 {
        return None;
    }
    soft_rlimit_bound(u64::from(limit.rlim_cur), u64::from(libc::RLIM_INFINITY))
}

#[cfg(not(unix))]
fn soft_rlimit_bytes(_which: Rlimit) -> Option<usize> {
    None
}

#[cfg(target_os = "linux")]
fn live_cgroup_limit() -> Option<usize> {
    let own = std::fs::read_to_string("/proc/self/cgroup").unwrap_or_default();
    cgroup_memory_limit_in(
        Path::new("/sys/fs/cgroup"),
        Path::new("/sys/fs/cgroup/memory"),
        &own,
    )
}

#[cfg(not(target_os = "linux"))]
fn live_cgroup_limit() -> Option<usize> {
    None
}

/// The tightest cgroup memory limit over the process's own cgroup and every
/// ancestor, for both hierarchies, given their mount roots and the contents of
/// `/proc/self/cgroup`. `None` when no level states a limit.
#[cfg(any(target_os = "linux", test))]
pub(crate) fn cgroup_memory_limit_in(
    v2_root: &Path,
    v1_root: &Path,
    proc_self_cgroup: &str,
) -> Option<usize> {
    tighter(
        nested_cgroup_limit(v2_root, cgroup_v2_path(proc_self_cgroup), "memory.max"),
        nested_cgroup_limit(
            v1_root,
            cgroup_v1_memory_path(proc_self_cgroup),
            "memory.limit_in_bytes",
        ),
    )
}

/// The v2 path from `/proc/self/cgroup` (the `0::<path>` line), else the root.
#[cfg(any(target_os = "linux", test))]
fn cgroup_v2_path(proc_self_cgroup: &str) -> &str {
    proc_self_cgroup
        .lines()
        .find_map(|line| line.strip_prefix("0::"))
        .unwrap_or("/")
}

/// The v1 path of the hierarchy holding the `memory` controller, else the root.
#[cfg(any(target_os = "linux", test))]
fn cgroup_v1_memory_path(proc_self_cgroup: &str) -> &str {
    proc_self_cgroup
        .lines()
        .find_map(|line| {
            let mut fields = line.splitn(3, ':');
            let _hierarchy = fields.next()?;
            let controllers = fields.next()?;
            let path = fields.next()?;
            controllers
                .split(',')
                .any(|controller| controller == "memory")
                .then_some(path)
        })
        .unwrap_or("/")
}

/// The tightest `file` limit over `root` and each directory along
/// `cgroup_path` beneath it. Only plain path components are followed: a `..`
/// (a cgroup outside this namespace's view) stops the walk, and a level whose
/// file is missing or unreadable is skipped, never read as unlimited.
#[cfg(any(target_os = "linux", test))]
fn nested_cgroup_limit(root: &Path, cgroup_path: &str, file: &str) -> Option<usize> {
    use std::path::Component;
    let read = |dir: &Path| {
        std::fs::read_to_string(dir.join(file))
            .ok()
            .and_then(|contents| crate::parse_cgroup_memory_limit(&contents))
    };
    let mut tightest = read(root);
    let mut dir = root.to_path_buf();
    for component in Path::new(cgroup_path).components() {
        match component {
            Component::Normal(name) => {
                dir.push(name);
                tightest = tighter(tightest, read(&dir));
            }
            Component::RootDir | Component::CurDir => {}
            Component::ParentDir | Component::Prefix(_) => break,
        }
    }
    tightest
}

#[cfg(any(target_os = "linux", test))]
fn tighter(a: Option<usize>, b: Option<usize>) -> Option<usize> {
    match (a, b) {
        (Some(a), Some(b)) => Some(a.min(b)),
        (a, b) => a.or(b),
    }
}

#[cfg(test)]
#[path = "memory_ceiling_tests.rs"]
mod tests;
