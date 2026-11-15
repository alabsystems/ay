// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Native measurements restrict the existing campaign lease; they never grant
//! shared-machine capacity. Linux hierarchy mapping follows proc(5) mountinfo
//! and the kernel cgroup-v1/memory and cgroup-v2 controller interfaces.

use super::{BenchError, ResourcePlan, Result, CHILD_FLOOR_MIB, MIB};
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Component, Path, PathBuf};
use std::time::{Duration, Instant};

#[derive(Default, Debug)]
pub(super) struct Restrictions {
    ceiling_mib: Option<usize>,
    remaining_mib: Option<usize>,
    remaining_controller_ceiling_mib: Option<usize>,
    cores: Option<usize>,
}

pub(super) fn plan(requested: usize, enforcement: &Path) -> Result<ResourcePlan> {
    if requested == 0 {
        return Err(BenchError::msg("requested benchmark jobs must be positive"));
    }
    let end = Instant::now()
        .checked_add(Duration::from_secs(30))
        .ok_or_else(|| BenchError::msg("native measurement deadline overflow"))?;
    #[cfg(not(test))]
    refuse_concurrent_build(end)?;
    let cores = physical_cores(end)?.min(std::thread::available_parallelism()?.get());
    #[cfg(target_os = "linux")]
    let restrictions = linux_restrictions()?;
    #[cfg(not(target_os = "linux"))]
    let restrictions = Restrictions::default();
    let physical = ay_sys::observed_host_memory_bytes()
        .ok_or_else(|| BenchError::msg("host physical memory observation unavailable"))?
        / MIB;
    let available = ay_sys::observed_available_memory_bytes()
        .ok_or_else(|| BenchError::msg("available memory observation unavailable"))?
        / MIB;
    check_deadline(end)?;
    let mut result = measured_plan(requested, physical, available, cores, &restrictions)?;
    result.planner = format!(
        "ay-native-measured-v1;enforcement={}",
        enforcement.display()
    );
    Ok(result)
}

pub(super) fn measured_plan(
    requested: usize,
    physical: usize,
    available: usize,
    cores: usize,
    restrictions: &Restrictions,
) -> Result<ResourcePlan> {
    if requested == 0 || physical == 0 || cores == 0 {
        return Err(BenchError::msg(
            "invalid native resource observation or job request",
        ));
    }
    // Preserve the old tightest-remaining controller's coupled limit/current
    // headroom policy. Separately enforce ALL nominal ceilings below: the
    // tightest nominal controller need not have the tightest remaining space.
    let container = restrictions
        .remaining_controller_ceiling_mib
        .is_some_and(|limit| limit <= physical);
    let physical = restrictions
        .remaining_controller_ceiling_mib
        .map_or(physical, |limit| physical.min(limit));
    let headroom = if container {
        CHILD_FLOOR_MIB.max(physical / 10)
    } else {
        16_000usize.max(physical / 3)
    }
    .min(physical.saturating_sub(CHILD_FLOOR_MIB));
    let mut budget = physical
        .saturating_sub(headroom)
        .min(available.saturating_sub(CHILD_FLOOR_MIB));
    if let Some(ceiling) = restrictions.ceiling_mib {
        budget = budget.min(ceiling.saturating_sub(headroom));
    }
    if let Some(remaining) = restrictions.remaining_mib {
        budget = budget.min(remaining.saturating_sub(headroom));
    }
    if budget < CHILD_FLOOR_MIB {
        return Err(BenchError::msg(
            "insufficient observed memory for one bounded child",
        ));
    }
    // Preserve requested IO/concurrency semantics even on one core. NBCORE,
    // not an invented serial cap, restricts each admitted child's CPU request.
    let jobs = requested.min(budget / CHILD_FLOOR_MIB);
    let cores = restrictions.cores.map_or(cores, |limit| cores.min(limit));
    if cores == 0 {
        return Err(BenchError::msg("zero observed CPU capacity"));
    }
    Ok(ResourcePlan {
        requested_jobs: requested,
        jobs,
        memlimit_mb_per_child: budget / jobs,
        nbcore_per_child: (cores / jobs).max(1),
        headroom_mb: headroom,
        planner: "ay-native-measured-v1".into(),
    })
}

fn check_deadline(end: Instant) -> Result<()> {
    if Instant::now() >= end {
        Err(BenchError::msg(
            "native resource measurement deadline expired",
        ))
    } else {
        Ok(())
    }
}

fn metadata(mut command: std::process::Command, end: Instant, label: &str) -> Result<String> {
    check_deadline(end)?;
    command.stdin(std::process::Stdio::null());
    let output = ay_sys::metadata_capture::capture(
        command,
        ay_sys::metadata_capture::CaptureLimits {
            timeout: end.saturating_duration_since(Instant::now()),
            output_bytes: super::super::MAX_METADATA_BYTES as usize,
            resident_bytes: Some(super::super::MAX_METADATA_BYTES),
        },
        label,
    )?;
    check_deadline(end)?;
    if !output.status.success() {
        return Err(BenchError::msg(format!(
            "{label} failed: {}",
            output.status
        )));
    }
    String::from_utf8(output.stdout)
        .map_err(|_| BenchError::msg(format!("{label} emitted invalid UTF-8")))
}

#[cfg(target_os = "macos")]
fn physical_cores(end: Instant) -> Result<usize> {
    let mut command = std::process::Command::new("/usr/sbin/sysctl");
    command.args(["-n", "hw.physicalcpu"]);
    let value = metadata(command, end, "physical core observation")?;
    let count = integer(value.trim())?;
    usize::try_from(count)
        .ok()
        .filter(|value| *value > 0)
        .ok_or_else(|| BenchError::msg("invalid physical core observation"))
}

#[cfg(not(target_os = "macos"))]
fn physical_cores(end: Instant) -> Result<usize> {
    check_deadline(end)?;
    #[cfg(target_os = "linux")]
    {
        let text = read_required(Path::new("/proc/cpuinfo"))?;
        let mut pairs = BTreeSet::new();
        let mut package = None;
        for line in text.lines() {
            if line.is_empty() {
                package = None;
            }
            if let Some((key, value)) = line.split_once(':') {
                match key.trim() {
                    "physical id" => package = Some(integer(value.trim())?),
                    "core id" => {
                        pairs.insert((package, integer(value.trim())?));
                    }
                    _ => {}
                }
            }
        }
        if !pairs.is_empty() {
            return Ok(pairs.len());
        }
    }
    // Some ARM kernels expose no physical/core IDs. This is the existing
    // planner's native OS CPU observation fallback, not a guessed one-core grant.
    Ok(std::thread::available_parallelism()?.get())
}

fn integer(text: &str) -> Result<u64> {
    if text.is_empty() || !text.bytes().all(|byte| byte.is_ascii_digit()) {
        return Err(BenchError::msg("invalid numeric kernel observation"));
    }
    text.parse()
        .map_err(|_| BenchError::msg("kernel observation integer overflow"))
}

fn read_required(path: &Path) -> Result<String> {
    super::super::read_bounded_text(
        path,
        super::super::MAX_METADATA_BYTES,
        "native kernel observation",
    )
}

fn read_optional(path: &Path) -> Result<Option<String>> {
    match std::fs::symlink_metadata(path) {
        Ok(metadata) if metadata.is_file() => read_required(path).map(Some),
        Ok(_) => Err(BenchError::msg(
            "kernel controller observation is not a regular file",
        )),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(None),
        Err(error) => Err(error.into()),
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Hierarchy {
    Unified,
    Legacy,
}

#[derive(Debug)]
struct ControllerPath {
    path: PathBuf,
    hierarchy: Hierarchy,
    memory: bool,
    cpu: bool,
    cpuset: bool,
}

#[derive(Clone, Copy)]
enum PathEncoding {
    MountInfo,
    Literal,
}

fn decode_path(text: &str, encoding: PathEncoding) -> Result<PathBuf> {
    let mut bytes = Vec::with_capacity(text.len());
    let mut input = text.as_bytes().iter().copied();
    while let Some(byte) = input.next() {
        if byte != b'\\' || matches!(encoding, PathEncoding::Literal) {
            bytes.push(byte);
            continue;
        }
        let digits = [input.next(), input.next(), input.next()];
        let mut value = 0u16;
        for digit in digits {
            let digit = digit
                .filter(|digit| (b'0'..=b'7').contains(digit))
                .ok_or_else(|| BenchError::msg("invalid mountinfo path escape"))?;
            value = value * 8 + u16::from(digit - b'0');
        }
        bytes.push(u8::try_from(value).map_err(|_| BenchError::msg("mountinfo escape overflow"))?);
    }
    use std::os::unix::ffi::OsStringExt as _;
    let path = PathBuf::from(std::ffi::OsString::from_vec(bytes));
    if !path.is_absolute()
        || path
            .components()
            .any(|part| matches!(part, Component::ParentDir))
    {
        return Err(BenchError::msg("invalid cgroup absolute path"));
    }
    Ok(path)
}

fn controller_paths(membership: &str, mounts: &str) -> Result<Vec<ControllerPath>> {
    if membership.trim().is_empty() || mounts.trim().is_empty() {
        return Err(BenchError::msg("cgroup hierarchy observation unavailable"));
    }
    let mut members = BTreeMap::new();
    for line in membership.lines().filter(|line| !line.is_empty()) {
        let mut fields = line.splitn(3, ':');
        integer(
            fields
                .next()
                .ok_or_else(|| BenchError::msg("missing cgroup hierarchy"))?,
        )?;
        let controllers = fields
            .next()
            .ok_or_else(|| BenchError::msg("missing cgroup controllers"))?;
        let path = decode_path(
            fields
                .next()
                .ok_or_else(|| BenchError::msg("missing cgroup membership"))?,
            PathEncoding::Literal,
        )?;
        for controller in if controllers.is_empty() {
            vec![""]
        } else {
            controllers.split(',').collect()
        } {
            if members.insert(controller, path.clone()).is_some() {
                return Err(BenchError::msg("duplicate cgroup controller membership"));
            }
        }
    }
    let mut result = Vec::new();
    let mut seen = BTreeSet::new();
    let mut resolved = BTreeSet::new();
    for line in mounts.lines().filter(|line| !line.is_empty()) {
        let (before, after) = line
            .split_once(" - ")
            .ok_or_else(|| BenchError::msg("invalid mountinfo record"))?;
        let left = before.split_whitespace().collect::<Vec<_>>();
        let right = after.split_whitespace().collect::<Vec<_>>();
        if left.len() < 6 || right.len() < 3 {
            return Err(BenchError::msg("incomplete mountinfo record"));
        }
        let hierarchy = match right[0] {
            "cgroup2" => Hierarchy::Unified,
            "cgroup" => Hierarchy::Legacy,
            _ => continue,
        };
        let root = decode_path(left[3], PathEncoding::MountInfo)?;
        let mount = decode_path(left[4], PathEncoding::MountInfo)?;
        for controller in ["memory", "cpu", "cpuset"] {
            if hierarchy == Hierarchy::Legacy
                && !right[2].split(',').any(|value| value == controller)
            {
                continue;
            }
            let Some(member) = members.get(if hierarchy == Hierarchy::Unified {
                ""
            } else {
                controller
            }) else {
                continue;
            };
            resolved.insert(if hierarchy == Hierarchy::Unified {
                ""
            } else {
                controller
            });
            let relative = member.strip_prefix(&root).unwrap_or(member.as_path());
            let relative = relative.strip_prefix("/").unwrap_or(relative);
            let mut current = mount.join(relative);
            loop {
                if !current.starts_with(&mount) {
                    return Err(BenchError::msg("cgroup path escaped mount"));
                }
                if seen.insert((current.clone(), hierarchy, controller)) {
                    result.push(ControllerPath {
                        path: current.clone(),
                        hierarchy,
                        memory: controller == "memory",
                        cpu: controller == "cpu",
                        cpuset: controller == "cpuset",
                    });
                }
                if current == mount {
                    break;
                }
                if !current.pop() {
                    return Err(BenchError::msg("cgroup ancestor path unavailable"));
                }
            }
        }
    }
    // A relevant membership without a visible mount cannot be treated as an
    // unrestricted host. Root cgroups with disabled controllers have a mount
    // but legitimately omit the optional controller files below.
    if members
        .keys()
        .any(|key| ["", "memory", "cpu", "cpuset"].contains(key) && !resolved.contains(key))
    {
        return Err(BenchError::msg(
            "cgroup membership has no visible controller mount",
        ));
    }
    Ok(result)
}

fn min_assign(slot: &mut Option<usize>, value: usize) {
    *slot = Some(slot.map_or(value, |old| old.min(value)));
}

fn restrictions_from(paths: &[ControllerPath]) -> Result<Restrictions> {
    let mut result = Restrictions::default();
    for controller in paths {
        if !std::fs::symlink_metadata(&controller.path)?.is_dir() {
            return Err(BenchError::msg("visible cgroup directory unavailable"));
        }
        let unified = controller.hierarchy == Hierarchy::Unified;
        if controller.memory {
            let limit_file = controller.path.join(if unified {
                "memory.max"
            } else {
                "memory.limit_in_bytes"
            });
            if let Some(text) = read_optional(&limit_file)? {
                let text = text.trim();
                if unified && text == "max" {
                    continue;
                }
                let limit = integer(text)?;
                if !unified && limit >= 1u64 << 60 {
                    continue;
                }
                let current = read_required(&controller.path.join(if unified {
                    "memory.current"
                } else {
                    "memory.usage_in_bytes"
                }))?;
                let used = integer(current.trim())?;
                let ceiling = usize::try_from(limit / MIB as u64)
                    .map_err(|_| BenchError::msg("cgroup memory overflow"))?;
                let remaining = usize::try_from(limit.saturating_sub(used) / MIB as u64)
                    .map_err(|_| BenchError::msg("cgroup remaining memory overflow"))?;
                min_assign(&mut result.ceiling_mib, ceiling);
                if result.remaining_mib.is_none_or(|old| {
                    remaining < old
                        || (remaining == old
                            && result
                                .remaining_controller_ceiling_mib
                                .is_none_or(|old_limit| ceiling < old_limit))
                }) {
                    result.remaining_mib = Some(remaining);
                    result.remaining_controller_ceiling_mib = Some(ceiling);
                }
            }
        }
        if controller.cpu {
            if let Some(text) = read_optional(&controller.path.join(if unified {
                "cpu.max"
            } else {
                "cpu.cfs_quota_us"
            }))? {
                let quota = if unified {
                    let fields = text.split_whitespace().collect::<Vec<_>>();
                    if fields.len() != 2 {
                        return Err(BenchError::msg("invalid unified CPU quota"));
                    }
                    let period = integer(fields[1])?;
                    if period == 0 {
                        return Err(BenchError::msg("zero CPU quota period"));
                    }
                    if fields[0] == "max" {
                        None
                    } else {
                        Some((integer(fields[0])?, period))
                    }
                } else if text.trim() == "-1" {
                    None
                } else {
                    let period = read_required(&controller.path.join("cpu.cfs_period_us"))?;
                    Some((integer(text.trim())?, integer(period.trim())?))
                };
                if let Some((quota, period)) = quota {
                    if quota == 0 || period == 0 {
                        return Err(BenchError::msg("invalid CPU quota"));
                    }
                    min_assign(
                        &mut result.cores,
                        usize::try_from((quota / period).max(1))
                            .map_err(|_| BenchError::msg("CPU quota overflow"))?,
                    );
                }
            }
        }
        if controller.cpuset {
            for name in if unified {
                ["cpuset.cpus.effective", "cpuset.cpus"]
            } else {
                ["cpuset.cpus", "cpuset.effective_cpus"]
            } {
                if let Some(text) = read_optional(&controller.path.join(name))? {
                    if !text.trim().is_empty() {
                        min_assign(&mut result.cores, cpuset_count(text.trim())?);
                    }
                }
            }
        }
    }
    Ok(result)
}

fn cpuset_count(text: &str) -> Result<usize> {
    let mut ranges = Vec::new();
    for entry in text.split(',') {
        let (start, end) = entry.split_once('-').unwrap_or((entry, entry));
        let start = integer(start)?;
        let end = integer(end)?;
        if end < start {
            return Err(BenchError::msg("reversed CPU range"));
        }
        ranges.push((start, end));
    }
    ranges.sort_unstable();
    let mut total = 0u64;
    let mut previous = None;
    for (start, end) in ranges {
        if previous.is_some_and(|last| end <= last) {
            continue;
        }
        let start = previous.map_or(start, |last: u64| start.max(last + 1));
        if start <= end {
            total = total
                .checked_add(end - start)
                .and_then(|value| value.checked_add(1))
                .ok_or_else(|| BenchError::msg("CPU set count overflow"))?;
        }
        previous = Some(previous.map_or(end, |last| last.max(end)));
    }
    usize::try_from(total)
        .ok()
        .filter(|value| *value > 0)
        .ok_or_else(|| BenchError::msg("empty CPU set"))
}

#[cfg(target_os = "linux")]
fn linux_restrictions() -> Result<Restrictions> {
    let membership = read_required(Path::new("/proc/self/cgroup"))?;
    let mounts = read_required(Path::new("/proc/self/mountinfo"))?;
    let result = restrictions_from(&controller_paths(&membership, &mounts)?)?;
    if read_required(Path::new("/proc/self/cgroup"))? != membership
        || read_required(Path::new("/proc/self/mountinfo"))? != mounts
    {
        return Err(BenchError::msg("cgroup source changed during observation"));
    }
    Ok(result)
}

#[cfg(not(test))]
fn refuse_concurrent_build(end: Instant) -> Result<()> {
    let activity =
        ay_sys::build_observation::active_builds(end, super::super::MAX_METADATA_BYTES as usize)?;
    if activity.count() > 0 {
        return Err(BenchError::msg(format!(
            "concurrent Rust compiler/build driver active; benchmark planning refused: {activity}"
        )));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mounted(root: &Path, hierarchy_root: &str, kind: &str, options: &str) -> String {
        let escaped = root
            .to_str()
            .unwrap()
            .replace('\\', "\\134")
            .replace(' ', "\\040");
        format!("1 0 0:1 {hierarchy_root} {escaped} rw - {kind} cgroup {options}\n")
    }

    fn write_memory(path: &Path, limit: u64, used: u64) {
        std::fs::create_dir_all(path).unwrap();
        std::fs::write(path.join("memory.max"), (limit * MIB as u64).to_string()).unwrap();
        std::fs::write(path.join("memory.current"), (used * MIB as u64).to_string()).unwrap();
    }

    #[test]
    fn nested_parent_usage_restricts_the_whole_aggregate_before_job_split() {
        let temp = tempfile::tempdir().unwrap();
        write_memory(temp.path(), 10 * 1024, 6 * 1024);
        write_memory(&temp.path().join("leaf"), 8 * 1024, 1024);
        let paths =
            controller_paths("0::/leaf\n", &mounted(temp.path(), "/", "cgroup2", "rw")).unwrap();
        let restrictions = restrictions_from(&paths).unwrap();
        assert_eq!(restrictions.ceiling_mib, Some(8 * 1024));
        assert_eq!(restrictions.remaining_mib, Some(4 * 1024));
        let plan = measured_plan(10, 64 * 1024, 60 * 1024, 16, &restrictions).unwrap();
        assert_eq!(plan.jobs, 3);
        assert_eq!(plan.headroom_mb, 1024);
        assert_eq!(plan.jobs * plan.memlimit_mb_per_child, 3 * 1024);
        write_memory(temp.path(), 10 * 1024, 11 * 1024);
        assert!(measured_plan(
            10,
            64 * 1024,
            60 * 1024,
            16,
            &restrictions_from(&paths).unwrap()
        )
        .is_err());
    }

    #[test]
    fn finite_controller_usage_must_be_observed_and_malformed_limits_refuse() {
        let temp = tempfile::tempdir().unwrap();
        let paths =
            controller_paths("0::/\n", &mounted(temp.path(), "/", "cgroup2", "rw")).unwrap();
        std::fs::write(temp.path().join("memory.max"), "4096").unwrap();
        assert!(restrictions_from(&paths).is_err());
        std::fs::write(temp.path().join("memory.current"), "-1").unwrap();
        assert!(restrictions_from(&paths).is_err());
        std::fs::write(temp.path().join("memory.max"), "garbage").unwrap();
        assert!(restrictions_from(&paths).is_err());
        std::fs::write(temp.path().join("memory.max"), "max").unwrap();
        assert_eq!(restrictions_from(&paths).unwrap().ceiling_mib, None);
        std::fs::write(temp.path().join("memory.max"), "0").unwrap();
        std::fs::write(temp.path().join("memory.current"), "0").unwrap();
        assert!(measured_plan(1, 64000, 60000, 8, &restrictions_from(&paths).unwrap()).is_err());
    }

    #[test]
    fn mount_roots_namespace_relative_membership_and_escaped_paths_preserve_ancestors() {
        let temp = tempfile::tempdir().unwrap();
        let mount = temp.path().join("mount space");
        write_memory(&mount, 8192, 2048);
        write_memory(&mount.join("leaf"), 4096, 1024);
        let mounts = mounted(&mount, "/host/slice", "cgroup2", "rw");
        let absolute =
            restrictions_from(&controller_paths("0::/host/slice/leaf\n", &mounts).unwrap())
                .unwrap();
        let relative =
            restrictions_from(&controller_paths("0::/leaf\n", &mounts).unwrap()).unwrap();
        assert_eq!(absolute.remaining_mib, Some(3072));
        assert_eq!(absolute.remaining_mib, relative.remaining_mib);
        assert!(controller_paths("0::/../escape\n", &mounts).is_err());
        assert!(controller_paths(
            "1:memory:/\n2:cpu:/\n",
            &mounted(&mount, "/", "cgroup", "rw,cpu")
        )
        .is_err());
    }

    #[test]
    fn hybrid_v1_memory_and_cpu_constraints_are_both_applied() {
        let temp = tempfile::tempdir().unwrap();
        let memory = temp.path().join("memory");
        let cpu = temp.path().join("cpu");
        std::fs::create_dir_all(&memory).unwrap();
        std::fs::create_dir_all(&cpu).unwrap();
        std::fs::write(
            memory.join("memory.limit_in_bytes"),
            (8192u64 * MIB as u64).to_string(),
        )
        .unwrap();
        std::fs::write(
            memory.join("memory.usage_in_bytes"),
            (2048u64 * MIB as u64).to_string(),
        )
        .unwrap();
        std::fs::write(cpu.join("cpu.cfs_quota_us"), "250000").unwrap();
        std::fs::write(cpu.join("cpu.cfs_period_us"), "100000").unwrap();
        std::fs::write(cpu.join("cpuset.cpus"), "0-7").unwrap();
        let mounts = mounted(&memory, "/", "cgroup", "rw,memory")
            + &mounted(&cpu, "/", "cgroup", "rw,cpu,cpuset");
        let paths = controller_paths("1:memory:/\n2:cpu,cpuset:/\n", &mounts).unwrap();
        let restrictions = restrictions_from(&paths).unwrap();
        let plan = measured_plan(1, 64000, 60000, 16, &restrictions).unwrap();
        assert_eq!(plan.nbcore_per_child, 2);
        assert_eq!(plan.memlimit_mb_per_child, 5120);
        std::fs::write(memory.join("memory.limit_in_bytes"), "9223372036854771712").unwrap();
        std::fs::remove_file(memory.join("memory.usage_in_bytes")).unwrap();
        assert_eq!(restrictions_from(&paths).unwrap().ceiling_mib, None);
    }

    #[test]
    fn cpusets_are_counted_as_intervals_without_expanding_declared_ranges() {
        assert_eq!(cpuset_count("0-2,1-4,4").unwrap(), 5);
        assert_eq!(
            cpuset_count("18446744073709551615,18446744073709551615").unwrap(),
            1
        );
        assert!(cpuset_count("0-18446744073709551615").is_err());
        assert!(cpuset_count("4-1").is_err());
        assert!(cpuset_count("1,").is_err());
    }

    #[test]
    fn original_margin_and_requested_parallelism_survive_native_planning() {
        let plan = measured_plan(8, 65536, 4096, 2, &Restrictions::default()).unwrap();
        assert_eq!(plan.jobs, 3);
        assert_eq!(plan.nbcore_per_child, 1);
        assert_eq!(plan.jobs * plan.memlimit_mb_per_child + 1024, 4096);
        assert!(measured_plan(8, 65536, 0, 2, &Restrictions::default()).is_err());
        assert!(measured_plan(8, 65536, 1024, 2, &Restrictions::default()).is_err());
    }

    #[test]
    fn headroom_keeps_the_tightest_remaining_controllers_coupled_limit() {
        let restrictions = Restrictions {
            ceiling_mib: Some(80 * 1024),
            remaining_mib: Some(12 * 1024),
            remaining_controller_ceiling_mib: Some(100 * 1024),
            cores: None,
        };
        let plan = measured_plan(8, 128 * 1024, 120 * 1024, 16, &restrictions).unwrap();
        assert_eq!(plan.headroom_mb, 10 * 1024);
        assert_eq!(plan.jobs * plan.memlimit_mb_per_child, 2 * 1024);
        let restrictions = Restrictions {
            ceiling_mib: Some(1024 * 1024),
            remaining_mib: Some(1024 * 1024),
            remaining_controller_ceiling_mib: Some(1024 * 1024),
            cores: None,
        };
        let plan = measured_plan(1, 64 * 1024, 60 * 1024, 16, &restrictions).unwrap();
        assert_eq!(plan.headroom_mb, 64 * 1024 / 3);
    }

    #[test]
    fn actual_native_measurement_keeps_enforcement_separate_and_uses_no_python_plan() {
        let enforcement = crate::runner::repo_root_public().join("scripts/_oom_guard.py");
        let plan = plan(1, &enforcement).unwrap();
        assert_eq!(plan.requested_jobs, 1);
        assert_eq!(plan.jobs, 1);
        assert!(plan.memlimit_mb_per_child >= CHILD_FLOOR_MIB);
        assert!(plan.nbcore_per_child > 0);
        let end = Instant::now() + Duration::from_secs(30);
        ay_sys::build_observation::active_builds(
            end,
            super::super::super::MAX_METADATA_BYTES as usize,
        )
        .unwrap();
    }
}
