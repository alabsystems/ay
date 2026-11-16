// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Read-only build activity, not machine admission. Unknown reads refuse.
//! Darwin ABI/PROCARGS2 and single-flight reads follow the maintained
//! aterm-sysprobe kproc/procargs implementation (Apache-2.0).

use crate::supervisor::process_group::ProcessIdentity;
use std::collections::{BTreeMap, BTreeSet};
use std::io;
use std::sync::{Condvar, Mutex};
use std::time::Instant;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum State {
    Active,
    Stopped,
    Exited,
}

#[derive(Clone, Debug)]
struct Record {
    identity: ProcessIdentity,
    name: Vec<u8>,
    state: State,
}

/// One bounded catalog observation, never process custody or admission.
/// The first matching identity is retained only to explain a refusal; it must
/// never be used to signal, adopt or authorize work in that process.
#[derive(Debug)]
pub struct BuildActivity {
    count: usize,
    first: Option<(ProcessIdentity, &'static str)>,
}

impl BuildActivity {
    /// Number of active compiler/build-driver observations in this catalog.
    pub fn count(&self) -> usize {
        self.count
    }
}

impl std::fmt::Display for BuildActivity {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "{} active compiler/build driver(s)", self.count)?;
        if let Some((identity, program)) = &self.first {
            write!(formatter, "; first={program} {identity:?}")?;
        }
        Ok(())
    }
}

struct Reader {
    busy: Mutex<bool>,
    finished: Condvar,
}
static READER: Reader = Reader {
    busy: Mutex::new(false),
    finished: Condvar::new(),
};

struct Finished;
impl Drop for Finished {
    fn drop(&mut self) {
        if let Ok(mut busy) = READER.busy.lock() {
            *busy = false;
        }
        READER.finished.notify_all();
    }
}

fn current(end: Instant) -> io::Result<()> {
    if Instant::now() >= end {
        Err(io::Error::new(
            io::ErrorKind::TimedOut,
            "original build-observation deadline expired",
        ))
    } else {
        Ok(())
    }
}

/// Observe live compilers and non-ancestor build-driving Targo/Cargo processes.
/// The supplied original deadline and byte bound only restrict this DATA read.
/// One kernel read may remain blocked after a timeout; while it does, further
/// requests wait/refuse, never launch more readers or reuse its stale result.
pub fn active_builds(end: Instant, maximum_bytes: usize) -> io::Result<BuildActivity> {
    current(end)?;
    if maximum_bytes == 0 || maximum_bytes > isize::MAX as usize {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "invalid metadata byte bound",
        ));
    }
    let mut busy = READER
        .busy
        .lock()
        .map_err(|_| io::Error::other("build reader poisoned"))?;
    while *busy {
        current(end)?;
        busy = READER
            .finished
            .wait_timeout(busy, end.saturating_duration_since(Instant::now()))
            .map_err(|_| io::Error::other("build reader poisoned"))?
            .0;
    }
    current(end)?;
    *busy = true;
    drop(busy);
    let (sender, receiver) = std::sync::mpsc::sync_channel(1);
    let spawned = std::thread::Builder::new()
        .name("ay-build-observation".into())
        .spawn(move || {
            let result = {
                let _finished = Finished;
                observe(end, maximum_bytes)
            };
            let _ = sender.send(result);
        });
    if let Err(error) = spawned {
        drop(Finished);
        return Err(error);
    }
    let result = receiver
        .recv_timeout(end.saturating_duration_since(Instant::now()))
        .map_err(|error| {
            io::Error::new(
                match error {
                    std::sync::mpsc::RecvTimeoutError::Timeout => io::ErrorKind::TimedOut,
                    std::sync::mpsc::RecvTimeoutError::Disconnected => io::ErrorKind::BrokenPipe,
                },
                format!("build observation unavailable: {error}"),
            )
        })?;
    if result.is_ok() {
        current(end)?;
    }
    result
}

fn classify(
    records: &[Record],
    mut arguments: impl FnMut(&Record) -> io::Result<Option<Vec<Vec<u8>>>>,
) -> io::Result<BuildActivity> {
    let mut by_pid = BTreeMap::new();
    for record in records {
        if by_pid.insert(record.identity.pid, record).is_some() {
            return Err(io::Error::other("duplicate process record"));
        }
    }
    let mut ancestors = BTreeSet::new();
    let mut pid = std::process::id();
    if !by_pid.contains_key(&pid) {
        return Err(io::Error::other("current process missing from catalog"));
    }
    while pid > 0 && ancestors.insert(pid) {
        if pid == 1 {
            break;
        }
        pid = by_pid
            .get(&pid)
            .ok_or_else(|| io::Error::other("incomplete process ancestry"))?
            .identity
            .parent;
    }
    let mut count = 0usize;
    let mut first = None;
    for record in records {
        if record.state != State::Active {
            continue;
        }
        if record.name.is_empty() {
            return Err(io::Error::other("live process name unavailable"));
        }
        let compiler = matches!(record.name.as_slice(), b"rustc" | b"compiler_consumer");
        let driver = matches!(record.name.as_slice(), b"cargo" | b"targo")
            && !ancestors.contains(&record.identity.pid);
        let building = if compiler {
            true
        } else if driver {
            let Some(words) = arguments(record)? else {
                continue;
            };
            // A malformed/ambiguous argv0 is UNKNOWN, never a metadata-only
            // driver. In particular an empty argv0 must not hide argv1=build.
            let first = words
                .first()
                .ok_or_else(|| io::Error::other("build argv unavailable"))?;
            let first = first.rsplit(|byte| *byte == b'/').next().unwrap_or(&[]);
            if !matches!(first, b"cargo" | b"targo") {
                return Err(io::Error::other("build argv identity is ambiguous"));
            }
            words.iter().skip(1).any(|word| {
                matches!(
                    word.as_slice(),
                    b"build"
                        | b"check"
                        | b"test"
                        | b"run"
                        | b"clippy"
                        | b"tippy"
                        | b"rustc"
                        | b"doc"
                        | b"bench"
                        | b"install"
                        | b"fix"
                )
            })
        } else {
            false
        };
        if building {
            count = count
                .checked_add(1)
                .ok_or_else(|| io::Error::other("build count overflow"))?;
            first.get_or_insert((
                record.identity,
                if compiler {
                    if record.name == b"rustc" {
                        "rustc"
                    } else {
                        "compiler_consumer"
                    }
                } else if record.name == b"cargo" {
                    "cargo"
                } else {
                    "targo"
                },
            ));
        }
    }
    Ok(BuildActivity { count, first })
}

#[cfg(target_os = "macos")]
fn observe(end: Instant, maximum: usize) -> io::Result<BuildActivity> {
    darwin::observe(end, maximum)
}

#[cfg(target_os = "linux")]
fn observe(end: Instant, maximum: usize) -> io::Result<BuildActivity> {
    linux::observe(end, maximum)
}

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
fn observe(_end: Instant, _maximum: usize) -> io::Result<BuildActivity> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "native build catalog unsupported",
    ))
}

#[cfg(any(target_os = "macos", test))]
mod darwin {
    use super::*;
    // 64-bit Darwin SDK struct kinfo_proc; same audited offsets as
    // aterm-sysprobe::jobs::darwin. No struct transmute or pointer aliasing.
    const SIZE: usize = 648;

    fn number<const N: usize>(bytes: &[u8], at: usize) -> io::Result<[u8; N]> {
        bytes
            .get(at..at + N)
            .and_then(|value| value.try_into().ok())
            .ok_or_else(|| io::Error::other("short Darwin process record"))
    }

    fn record(bytes: &[u8]) -> io::Result<Record> {
        if bytes.len() != SIZE {
            return Err(io::Error::other("Darwin process ABI size mismatch"));
        }
        let sec = i64::from_ne_bytes(number(bytes, 0)?);
        let usec = i32::from_ne_bytes(number(bytes, 8)?);
        if sec < 0 || !(0..1_000_000).contains(&usec) {
            return Err(io::Error::other("invalid process birth"));
        }
        let state = match bytes[36] {
            1..=3 => State::Active,
            4 => State::Stopped,
            5 => State::Exited,
            _ => return Err(io::Error::other("unknown Darwin process state")),
        };
        let name = &bytes[243..260];
        let nul = name
            .iter()
            .position(|byte| *byte == 0)
            .ok_or_else(|| io::Error::other("unterminated process name"))?;
        Ok(Record {
            identity: ProcessIdentity {
                pid: u32::from_ne_bytes(number(bytes, 40)?),
                parent: u32::from_ne_bytes(number(bytes, 560)?),
                group: u32::from_ne_bytes(number(bytes, 564)?),
                birth: sec as u128 * 1_000_000 + usec as u128,
            },
            name: name[..nul].to_vec(),
            state,
        })
    }

    fn argv(bytes: &[u8]) -> io::Result<Vec<Vec<u8>>> {
        let argc = i32::from_ne_bytes(number(bytes, 0)?);
        let argc = usize::try_from(argc).map_err(io::Error::other)?;
        if argc == 0 || argc > bytes.len() {
            return Err(io::Error::other("invalid process argc"));
        }
        let rest = &bytes[4..];
        let path_end = rest
            .iter()
            .position(|byte| *byte == 0)
            .ok_or_else(|| io::Error::other("missing exec path terminator"))?;
        let mut rest = &rest[path_end..];
        let first = rest
            .iter()
            .position(|byte| *byte != 0)
            .ok_or_else(|| io::Error::other("missing process arguments"))?;
        rest = &rest[first..];
        let mut words = Vec::new();
        for _ in 0..argc {
            let end = rest
                .iter()
                .position(|byte| *byte == 0)
                .ok_or_else(|| io::Error::other("truncated process arguments"))?;
            words.push(rest[..end].to_vec());
            rest = &rest[end + 1..];
        }
        Ok(words)
    }

    #[cfg(target_os = "macos")]
    fn read(mib: &mut [i32], buffer: &mut [u8]) -> io::Result<usize> {
        let mut len = buffer.len();
        // SAFETY: mib owns exactly the supplied integer key; buffer is writable
        // for len bytes, len is an exclusive local; no kernel writes requested.
        let rc = unsafe {
            libc::sysctl(
                mib.as_mut_ptr(),
                mib.len() as u32,
                buffer.as_mut_ptr().cast(),
                &raw mut len,
                std::ptr::null_mut(),
                0,
            )
        };
        if rc != 0 {
            return Err(io::Error::last_os_error());
        }
        if len > buffer.len() {
            return Err(io::Error::other("oversized kernel reply"));
        }
        Ok(len)
    }

    #[cfg(target_os = "macos")]
    fn sized(mib: &mut [i32]) -> io::Result<usize> {
        let mut len = 0usize;
        // SAFETY: a null output asks only for size; len and mib are live
        // exclusively borrowed locals; no kernel value is changed.
        let rc = unsafe {
            libc::sysctl(
                mib.as_mut_ptr(),
                mib.len() as u32,
                std::ptr::null_mut(),
                &raw mut len,
                std::ptr::null_mut(),
                0,
            )
        };
        if rc != 0 {
            Err(io::Error::last_os_error())
        } else {
            Ok(len)
        }
    }

    #[cfg(target_os = "macos")]
    pub(super) fn observe(end: Instant, maximum: usize) -> io::Result<BuildActivity> {
        if !cfg!(any(target_arch = "aarch64", target_arch = "x86_64")) {
            return Err(io::Error::new(
                io::ErrorKind::Unsupported,
                "Darwin process ABI unsupported",
            ));
        }
        let original = crate::supervisor::process_group::process_identity(std::process::id())?
            .ok_or_else(|| io::Error::other("original catalog caller unavailable"))?;
        let mut key = [libc::CTL_KERN, 14, 0]; // KERN_PROC / KERN_PROC_ALL
        let table = loop {
            current(end)?;
            let requested = sized(&mut key)?;
            let room = requested
                .checked_add(requested / 8)
                .and_then(|value| value.checked_add(SIZE * 16))
                .ok_or_else(|| io::Error::other("process table size overflow"))?
                .min(maximum);
            if requested > room {
                return Err(io::Error::other(
                    "process table exceeds original metadata bound",
                ));
            }
            let mut buffer = Vec::new();
            buffer.try_reserve_exact(room).map_err(io::Error::other)?;
            buffer.resize(room, 0);
            match read(&mut key, &mut buffer) {
                Ok(len) => {
                    buffer.truncate(len);
                    break buffer;
                }
                Err(error) if error.raw_os_error() == Some(libc::ENOMEM) => continue,
                Err(error) => return Err(error),
            }
        };
        if table.len() % SIZE != 0 {
            return Err(io::Error::other("partial Darwin process table"));
        }
        let mut records = Vec::new();
        for bytes in table.as_chunks::<SIZE>().0 {
            current(end)?;
            // PID0 is the kernel scheduler, never a userspace build driver.
            if u32::from_ne_bytes(number(bytes, 40)?) == 0 {
                continue;
            }
            records.push(record(bytes)?);
        }
        if !records.iter().any(|record| record.identity == original)
            || crate::supervisor::process_group::process_identity(original.pid)? != Some(original)
        {
            return Err(io::Error::other(
                "Darwin process catalog ABI/source mismatch",
            ));
        }
        let mut used = table.len();
        let mut buffer = Vec::new();
        classify(&records, |original| {
            current(end)?;
            let mut identity_key = [
                libc::CTL_KERN,
                14,
                1,
                i32::try_from(original.identity.pid).map_err(io::Error::other)?,
            ];
            let mut identity_bytes = [0u8; SIZE];
            let before = match read(&mut identity_key, &mut identity_bytes) {
                Ok(size) => size,
                Err(error) if error.raw_os_error() == Some(libc::ESRCH) => return Ok(None),
                Err(error) => return Err(error),
            };
            if before == 0 {
                return Ok(None);
            }
            if before != SIZE || record(&identity_bytes)?.identity != original.identity {
                return Err(io::Error::other("build process changed identity"));
            }
            if buffer.is_empty() {
                let mut argmax_key = [libc::CTL_KERN, 8]; // KERN_ARGMAX
                let mut word = [0u8; 4];
                if read(&mut argmax_key, &mut word)? != 4 {
                    return Err(io::Error::other("invalid kernel argv bound"));
                }
                let cap = usize::try_from(i32::from_ne_bytes(word))
                    .map_err(io::Error::other)?
                    .checked_add(4)
                    .ok_or_else(|| io::Error::other("argv bound overflow"))?;
                if cap <= 4 || cap > maximum {
                    return Err(io::Error::other("argv exceeds original metadata bound"));
                }
                buffer.try_reserve_exact(cap).map_err(io::Error::other)?;
                buffer.resize(cap, 0);
            }
            let mut arg_key = [libc::CTL_KERN, 49, identity_key[3]]; // KERN_PROCARGS2
            let len = match read(&mut arg_key, &mut buffer) {
                Ok(size) => size,
                Err(error) if error.raw_os_error() == Some(libc::ESRCH) => return Ok(None),
                Err(error) => return Err(error),
            };
            if len == buffer.len() {
                return Err(io::Error::other("potentially truncated kernel argv"));
            }
            used = used
                .checked_add(len)
                .filter(|value| *value <= maximum)
                .ok_or_else(|| io::Error::other("original metadata byte bound exhausted"))?;
            let words = argv(&buffer[..len])?;
            let after = match read(&mut identity_key, &mut identity_bytes) {
                Ok(size) => size,
                Err(error) if error.raw_os_error() == Some(libc::ESRCH) => return Ok(None),
                Err(error) => return Err(error),
            };
            if after == 0 {
                return Ok(None);
            }
            if after != SIZE || record(&identity_bytes)?.identity != original.identity {
                return Err(io::Error::other("build argv source changed"));
            }
            current(end)?;
            Ok(Some(words))
        })
    }

    #[cfg(test)]
    pub(super) fn check_decoders() {
        let mut bytes = [0u8; SIZE];
        bytes[36] = 2;
        bytes[40..44].copy_from_slice(&123u32.to_ne_bytes());
        bytes[243..248].copy_from_slice(b"targo");
        assert_eq!(record(&bytes).unwrap().name, b"targo");
        bytes[8..12].copy_from_slice(&1_000_000i32.to_ne_bytes());
        assert!(record(&bytes).is_err());
        assert!(record(&bytes[..SIZE - 1]).is_err());
        let mut args = 3i32.to_ne_bytes().to_vec();
        args.extend_from_slice(
            b"/a/targo\0\0/a/targo\0--unverified\0build\0SECRET=not-an-argument\0",
        );
        let parsed = argv(&args).unwrap();
        assert_eq!(
            parsed,
            [
                b"/a/targo".to_vec(),
                b"--unverified".to_vec(),
                b"build".to_vec()
            ]
        );
        args.truncate(8);
        assert!(argv(&args).is_err());
    }
}

#[cfg(any(target_os = "linux", test))]
mod linux {
    use super::*;
    #[cfg(test)]
    pub(super) fn check_record() {
        let mut fields = vec!["0"; 22];
        fields[0] = "R";
        fields[1] = "1";
        fields[2] = "123";
        fields[19] = "99";
        let mut bytes = b"123 (opaque\xffname) ".to_vec();
        bytes.extend_from_slice(fields.join(" ").as_bytes());
        let parsed = record(123, &bytes).unwrap();
        assert_eq!(parsed.name, b"opaque\xffname");
        assert_eq!(parsed.identity.birth, 99);
        assert!(record(124, &bytes).is_err());
        assert!(record(123, b"123 (short) R 1").is_err());
    }
    #[cfg(target_os = "linux")]
    fn read(path: &std::path::Path, maximum: usize) -> io::Result<Option<Vec<u8>>> {
        use std::io::Read as _;
        use std::os::unix::fs::OpenOptionsExt as _;
        let file = match std::fs::OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK)
            .open(path)
        {
            Ok(file) => file,
            Err(error)
                if error.kind() == io::ErrorKind::NotFound
                    || error.raw_os_error() == Some(libc::ESRCH) =>
            {
                return Ok(None)
            }
            Err(error) => return Err(error),
        };
        if !file.metadata()?.is_file() {
            return Err(io::Error::other("process source is not regular"));
        }
        let mut bytes = Vec::new();
        file.take(maximum as u64 + 1).read_to_end(&mut bytes)?;
        if bytes.len() > maximum {
            return Err(io::Error::other("process data exceeds original bound"));
        }
        Ok(Some(bytes))
    }
    fn record(pid: u32, bytes: &[u8]) -> io::Result<Record> {
        let close = bytes
            .iter()
            .rposition(|byte| *byte == b')')
            .ok_or_else(|| io::Error::other("invalid process stat"))?;
        let open = bytes[..close]
            .iter()
            .position(|byte| *byte == b'(')
            .ok_or_else(|| io::Error::other("missing process name"))?;
        let printed_pid = std::str::from_utf8(&bytes[..open]).map_err(io::Error::other)?;
        let fields = std::str::from_utf8(&bytes[close + 1..]).map_err(io::Error::other)?;
        if printed_pid
            .trim()
            .parse::<u32>()
            .map_err(io::Error::other)?
            != pid
        {
            return Err(io::Error::other("process PID changed"));
        }
        let fields = fields.split_whitespace().collect::<Vec<_>>();
        let field = |at: usize| {
            fields
                .get(at)
                .ok_or_else(|| io::Error::other("short process stat"))
        };
        let state = match *field(0)? {
            "T" | "t" => State::Stopped,
            "Z" | "X" | "x" => State::Exited,
            "R" | "S" | "D" | "I" | "W" | "P" | "K" => State::Active,
            _ => return Err(io::Error::other("unknown process state")),
        };
        Ok(Record {
            identity: ProcessIdentity {
                pid,
                parent: field(1)?.parse().map_err(io::Error::other)?,
                group: field(2)?.parse().map_err(io::Error::other)?,
                birth: u128::from(field(19)?.parse::<u64>().map_err(io::Error::other)?),
            },
            name: bytes[open + 1..close].to_vec(),
            state,
        })
    }
    #[cfg(target_os = "linux")]
    pub(super) fn observe(end: Instant, maximum: usize) -> io::Result<BuildActivity> {
        let mut records = Vec::new();
        let mut remaining = maximum;
        for entry in std::fs::read_dir("/proc")? {
            current(end)?;
            let entry = entry?;
            let Some(pid) = entry
                .file_name()
                .to_str()
                .and_then(|value| value.parse::<u32>().ok())
            else {
                continue;
            };
            if let Some(bytes) = read(&entry.path().join("stat"), remaining)? {
                remaining = remaining
                    .checked_sub(bytes.len())
                    .ok_or_else(|| io::Error::other("metadata bound exhausted"))?;
                records.push(record(pid, &bytes)?);
            }
        }
        classify(&records, |original| {
            current(end)?;
            let root = std::path::PathBuf::from(format!("/proc/{}", original.identity.pid));
            let Some(before) = read(&root.join("stat"), remaining)? else {
                return Ok(None);
            };
            if record(original.identity.pid, &before)?.identity != original.identity {
                return Err(io::Error::other("build process source changed"));
            }
            let Some(bytes) = read(&root.join("cmdline"), remaining)? else {
                return Ok(None);
            };
            remaining = remaining
                .checked_sub(bytes.len())
                .ok_or_else(|| io::Error::other("metadata bound exhausted"))?;
            if bytes.last() != Some(&0) {
                return Err(io::Error::other("truncated process arguments"));
            }
            let words = bytes[..bytes.len() - 1]
                .split(|byte| *byte == 0)
                .map(<[u8]>::to_vec)
                .collect();
            let Some(after) = read(&root.join("stat"), remaining)? else {
                return Ok(None);
            };
            if record(original.identity.pid, &after)?.identity != original.identity {
                return Err(io::Error::other("build argv source changed"));
            }
            current(end)?;
            Ok(Some(words))
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn row(pid: u32, parent: u32, name: &[u8], state: State) -> Record {
        Record {
            identity: ProcessIdentity {
                pid,
                parent,
                group: pid,
                birth: 1,
            },
            name: name.to_vec(),
            state,
        }
    }
    #[test]
    fn metadata_drivers_and_ancestors_are_not_compilers_but_unreadable_drivers_refuse() {
        let own = std::process::id();
        let parent = own + 1;
        let records = [
            row(own, parent, b"test", State::Active),
            row(parent, 1, b"targo", State::Active),
            row(own + 2, 1, b"compiler_consumer", State::Active),
            row(own + 3, 1, b"compiler_consumer", State::Stopped),
            row(own + 4, 1, b"targo", State::Active),
        ];
        let activity = classify(&records, |record| {
            assert_ne!(record.identity.pid, parent);
            Ok(Some(vec![b"targo".to_vec(), b"--version".to_vec()]))
        })
        .unwrap();
        assert_eq!(activity.count(), 1);
        let (identity, program) = activity.first.unwrap();
        assert_eq!(identity, records[2].identity);
        assert_eq!(program, "compiler_consumer");
        assert_eq!(
            classify(&records, |_| Ok(Some(vec![
                b"targo".to_vec(),
                b"test".to_vec()
            ])))
            .unwrap()
            .count(),
            2
        );
        assert!(classify(&records, |_| Err(io::ErrorKind::PermissionDenied.into())).is_err());
        assert!(classify(&records, |_| Ok(Some(vec![Vec::new(), b"build".to_vec()]))).is_err());
    }
    #[test]
    fn darwin_complete_records_and_arguments_are_checked_without_environment_projection() {
        darwin::check_decoders();
    }
    #[test]
    fn linux_stat_keeps_opaque_names_and_checks_original_pid() {
        linux::check_record();
    }
    #[test]
    fn actual_native_catalog_and_original_expired_deadline() {
        assert!(active_builds(Instant::now(), 64 * 1024 * 1024).is_err());
        active_builds(
            Instant::now() + std::time::Duration::from_secs(30),
            64 * 1024 * 1024,
        )
        .unwrap();
    }
}
