// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Birth-identified process-group observation for owned child supervision.

use std::io;
#[cfg(target_os = "macos")]
use std::mem::{size_of, size_of_val};

const MAX_GROUP_MEMBERS: usize = 16_384;

#[derive(Debug)]
struct CensusMemberDisappeared;

impl std::fmt::Display for CensusMemberDisappeared {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("group member disappeared during census")
    }
}
impl std::error::Error for CensusMemberDisappeared {}

pub(crate) fn census_member_disappeared() -> io::Error {
    io::Error::other(CensusMemberDisappeared)
}

/// An incomplete observation, never an empty-group or zero-RSS witness.
pub(crate) fn is_census_member_disappearance(error: &io::Error) -> bool {
    error
        .get_ref()
        .is_some_and(|cause| cause.is::<CensusMemberDisappeared>())
}

fn unchanged_census_identity(
    before: ProcessIdentity,
    after: Option<ProcessIdentity>,
) -> io::Result<()> {
    match after {
        None => Err(census_member_disappeared()),
        Some(after) if after == before => Ok(()),
        Some(_) => Err(io::Error::other("group member changed birth during census")),
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProcessIdentity {
    pub pid: u32,
    pub parent: u32,
    pub group: u32,
    pub birth: u128,
}

#[derive(Debug)]
pub struct ProcessGroupSample {
    pub resident_bytes: u64,
    pub members: Vec<ProcessIdentity>,
    pub live_members: Vec<ProcessIdentity>,
}

#[cfg(target_os = "macos")]
fn mac_process(pid: u32) -> io::Result<Option<(ProcessIdentity, bool)>> {
    let pid = i32::try_from(pid).map_err(|_| io::Error::other("PID exceeds pid_t"))?;
    // SAFETY: proc_bsdinfo is POD; the matching read-only flavor initializes
    // this owned output buffer. A short read is never accepted as identity.
    let mut info: libc::proc_bsdinfo = unsafe { std::mem::zeroed() };
    let size = size_of_val(&info);
    // SAFETY: the pointer spans exactly the requested initialized buffer.
    let count = unsafe {
        libc::proc_pidinfo(
            pid,
            libc::PROC_PIDTBSDINFO,
            0,
            (&raw mut info).cast(),
            size as i32,
        )
    };
    if count == 0 {
        let error = io::Error::last_os_error();
        return if matches!(error.raw_os_error(), Some(libc::ESRCH | libc::ENOENT)) {
            Ok(None)
        } else {
            Err(error)
        };
    }
    if count != size as i32 || info.pbi_pid != pid as u32 {
        return Err(io::Error::other("incomplete process birth observation"));
    }
    Ok(Some((
        ProcessIdentity {
            pid: info.pbi_pid,
            parent: info.pbi_ppid,
            group: info.pbi_pgid,
            birth: u128::from(info.pbi_start_tvsec) * 1_000_000 + u128::from(info.pbi_start_tvusec),
        },
        info.pbi_status == 5,
    )))
}

#[cfg(target_os = "macos")]
pub fn process_identity(pid: u32) -> io::Result<Option<ProcessIdentity>> {
    Ok(mac_process(pid)?.map(|(identity, _)| identity))
}

#[cfg(target_os = "macos")]
pub fn process_group_sample(group: u32) -> io::Result<ProcessGroupSample> {
    // Darwin libproc.h's PROC_PGRP_ONLY selects the kernel's exact group, not
    // a capped top-process list or a guessed descendant relationship.
    const PROC_PGRP_ONLY: u32 = 2;
    let mut pids = vec![0_i32; MAX_GROUP_MEMBERS];
    let capacity = pids.len() * size_of::<i32>();
    // SAFETY: pids owns the entire writable capacity supplied to libproc.
    let count = unsafe {
        libc::proc_listpids(
            PROC_PGRP_ONLY,
            group,
            pids.as_mut_ptr().cast(),
            capacity as i32,
        )
    };
    if count < 0 {
        return Err(io::Error::last_os_error());
    }
    if count as usize >= capacity || !(count as usize).is_multiple_of(size_of::<i32>()) {
        return Err(io::Error::other(
            "process group membership exceeds observation bound",
        ));
    }
    let mut sample = ProcessGroupSample {
        resident_bytes: 0,
        members: Vec::new(),
        live_members: Vec::new(),
    };
    for pid in pids
        .into_iter()
        .take(count as usize / size_of::<i32>())
        .filter(|p| *p > 0)
    {
        let Some((before, zombie)) = mac_process(pid as u32)? else {
            // Darwin's group listing retains an unreaped zombie leader even
            // when PIDTBSDINFO no longer exposes it. The caller retains its
            // original Child and observes exit without reaping before using
            // this sample for quiescence; that capability supplies the anchor
            // identity. Never apply this exception to another member.
            if pid as u32 == group {
                continue;
            }
            return Err(census_member_disappeared());
        };
        if before.group != group {
            return Err(io::Error::other("group member changed group during census"));
        }
        if zombie {
            sample.members.push(before);
            continue;
        }
        // SAFETY: the exact proc_taskinfo output type and size match this
        // read-only flavor; the initialized buffer is exclusively borrowed.
        let mut task: libc::proc_taskinfo = unsafe { std::mem::zeroed() };
        let size = size_of_val(&task);
        // SAFETY: task is a valid owned output buffer of the supplied size.
        let read = unsafe {
            libc::proc_pidinfo(
                pid,
                libc::PROC_PIDTASKINFO,
                0,
                (&raw mut task).cast(),
                size as i32,
            )
        };
        let after = process_identity(pid as u32)?;
        unchanged_census_identity(before, after)?;
        if read != size as i32 {
            // Zombie leaders keep their PID/group reservation but no RSS.
            // A live unreadable member must never count as zero memory.
            return Err(io::Error::other("group member RSS is unavailable"));
        }
        sample.resident_bytes = sample
            .resident_bytes
            .checked_add(task.pti_resident_size)
            .ok_or_else(|| io::Error::other("process group RSS overflow"))?;
        sample.members.push(before);
        sample.live_members.push(before);
    }
    Ok(sample)
}

#[cfg(target_os = "linux")]
fn linux_process(pid: u32) -> io::Result<Option<(ProcessIdentity, u64, bool)>> {
    use std::io::Read;
    let mut text = String::new();
    let file = match std::fs::File::open(format!("/proc/{pid}/stat")) {
        Ok(file) => file,
        Err(error)
            if error.kind() == io::ErrorKind::NotFound
                || matches!(error.raw_os_error(), Some(libc::ESRCH)) =>
        {
            return Ok(None)
        }
        Err(error) => return Err(error),
    };
    if let Err(error) = file.take(65_537).read_to_string(&mut text) {
        if matches!(error.raw_os_error(), Some(libc::ESRCH | libc::ENOENT)) {
            return Ok(None);
        }
        return Err(error);
    }
    if text.len() > 65_536 {
        return Err(io::Error::other("oversized process stat"));
    }
    let fields = text
        .rsplit_once(')')
        .ok_or_else(|| io::Error::other("invalid process stat"))?
        .1
        .split_whitespace()
        .collect::<Vec<_>>();
    let number = |index: usize| -> io::Result<u64> {
        fields
            .get(index)
            .and_then(|v| v.parse().ok())
            .ok_or_else(|| io::Error::other("invalid process stat field"))
    };
    // Fields after comm: state(0), ppid(1), pgrp(2), starttime(19), rss(21).
    let parent = u32::try_from(number(1)?).map_err(io::Error::other)?;
    let group = u32::try_from(number(2)?).map_err(io::Error::other)?;
    let birth = u128::from(number(19)?);
    let pages = number(21)?;
    // SAFETY: sysconf's named page-size query takes no pointer arguments.
    let page = unsafe { libc::sysconf(libc::_SC_PAGESIZE) };
    let page = u64::try_from(page).map_err(io::Error::other)?;
    let rss = pages
        .checked_mul(page)
        .ok_or_else(|| io::Error::other("RSS overflow"))?;
    Ok(Some((
        ProcessIdentity {
            pid,
            parent,
            group,
            birth,
        },
        rss,
        fields.first().is_some_and(|state| *state == "Z"),
    )))
}

#[cfg(target_os = "linux")]
pub fn process_identity(pid: u32) -> io::Result<Option<ProcessIdentity>> {
    Ok(linux_process(pid)?.map(|(identity, _, _)| identity))
}

#[cfg(target_os = "linux")]
pub fn process_group_sample(group: u32) -> io::Result<ProcessGroupSample> {
    process_groups_sample(&[group])?
        .remove(&group)
        .ok_or_else(|| io::Error::other("missing requested group sample"))
}

/// One bounded Linux census serves every active group, avoiding one /proc
/// traversal per child per watchdog tick.
#[cfg(target_os = "linux")]
pub fn process_groups_sample(
    groups: &[u32],
) -> io::Result<std::collections::BTreeMap<u32, ProcessGroupSample>> {
    if groups.is_empty() {
        return Ok(std::collections::BTreeMap::new());
    }
    let mut samples = groups
        .iter()
        .map(|group| {
            (
                *group,
                ProcessGroupSample {
                    resident_bytes: 0,
                    members: Vec::new(),
                    live_members: Vec::new(),
                },
            )
        })
        .collect::<std::collections::BTreeMap<_, _>>();
    for (index, entry) in std::fs::read_dir("/proc")?.enumerate() {
        if index >= 1_000_000 {
            return Err(io::Error::other("process census bound exceeded"));
        }
        let entry = entry?;
        let Some(pid) = entry
            .file_name()
            .to_str()
            .and_then(|s| s.parse::<u32>().ok())
        else {
            continue;
        };
        let Some((identity, rss, zombie)) = linux_process(pid)? else {
            continue;
        };
        let Some(sample) = samples.get_mut(&identity.group) else {
            continue;
        };
        if sample.members.len() >= MAX_GROUP_MEMBERS {
            return Err(io::Error::other("group membership bound exceeded"));
        }
        sample.resident_bytes = sample
            .resident_bytes
            .checked_add(rss)
            .ok_or_else(|| io::Error::other("group RSS overflow"))?;
        sample.members.push(identity);
        if !zombie {
            sample.live_members.push(identity);
        }
    }
    Ok(samples)
}

#[cfg(not(target_os = "linux"))]
pub fn process_groups_sample(
    groups: &[u32],
) -> io::Result<std::collections::BTreeMap<u32, ProcessGroupSample>> {
    groups
        .iter()
        .map(|group| Ok((*group, process_group_sample(*group)?)))
        .collect()
}

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
pub fn process_identity(_pid: u32) -> io::Result<Option<ProcessIdentity>> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "native process identity unavailable",
    ))
}

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
pub fn process_group_sample(_group: u32) -> io::Result<ProcessGroupSample> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "native group RSS unavailable",
    ))
}

#[cfg(test)]
#[test]
fn census_disappearance_is_distinct_from_a_changed_original_identity() {
    let original = ProcessIdentity {
        pid: 31,
        parent: 7,
        group: 31,
        birth: 99,
    };
    assert!(unchanged_census_identity(original, Some(original)).is_ok());
    let missing = unchanged_census_identity(original, None).unwrap_err();
    assert!(is_census_member_disappearance(&missing));
    for changed in [
        ProcessIdentity {
            birth: 100,
            ..original
        },
        ProcessIdentity {
            group: 32,
            ..original
        },
        ProcessIdentity {
            parent: 8,
            ..original
        },
    ] {
        let error = unchanged_census_identity(original, Some(changed)).unwrap_err();
        assert!(!is_census_member_disappearance(&error));
    }
}
