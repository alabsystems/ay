// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Binary SAT decision trace for deterministic replay.
//!
//! The format is append-only and intentionally compact so traces stay small on
//! long runs. A replay session consumes the same event stream and fails at the
//! first divergence.

use std::fs::{File, Metadata, OpenOptions};
use std::io::{self, BufReader, BufWriter, Read, Seek, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Mutex, OnceLock};

const MAGIC: &[u8; 8] = b"AYDTRC1\0";
const VERSION: u8 = 1;

// Replay files are untrusted inputs. These bounds cap both parser work and
// retained memory without adding user-facing configuration knobs.
const MAX_REPLAY_TRACE_BYTES: u64 = 256 * 1024 * 1024;
const MAX_REPLAY_EVENTS: usize = 8_000_000;
const MAX_REDUCE_CLAUSE_IDS: usize = 4_000_000;

const TAG_DECIDE: u8 = 1;
const TAG_PROPAGATE: u8 = 2;
const TAG_CONFLICT: u8 = 3;
const TAG_LEARN: u8 = 4;
const TAG_RESTART: u8 = 5;
const TAG_REDUCE: u8 = 6;
const TAG_INPROCESS: u8 = 7;
const TAG_RESULT: u8 = 8;

const INITIALIZED_TRACE_BYTES: u64 = MAGIC.len() as u64 + 1;

/// How a checked file can be reached for platform identity queries.
///
/// Every call site holds either the retained descriptor or the public pathname.
/// Windows exposes neither the file identity nor the hard-link count through
/// `Metadata` on stable (the accessors sit behind the perpetually unstable
/// `windows_by_handle` feature, rust-lang/rust#63010), so the source is threaded
/// through to `GetFileInformationByHandle` instead of read off the metadata.
#[derive(Clone, Copy)]
#[cfg_attr(not(windows), allow(dead_code))]
enum TraceFileRef<'a> {
    Handle(&'a File),
    Path(&'a Path),
}

#[cfg(windows)]
impl TraceFileRef<'_> {
    fn windows_info(self) -> io::Result<ay_sys::windows_fs::WindowsFileInfo> {
        match self {
            Self::Handle(file) => ay_sys::windows_fs::file_info(file),
            Self::Path(path) => ay_sys::windows_fs::file_info_no_follow(path),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct DecisionTraceFileIdentity {
    #[cfg(unix)]
    device: u64,
    #[cfg(unix)]
    inode: u64,
    #[cfg(windows)]
    volume_serial_number: u32,
    #[cfg(windows)]
    file_index: u64,
    #[cfg(not(any(unix, windows)))]
    created: Option<std::time::SystemTime>,
}

impl DecisionTraceFileIdentity {
    fn resolve(metadata: &Metadata, source: TraceFileRef<'_>) -> io::Result<Self> {
        #[cfg(unix)]
        {
            let _ = source;
            use std::os::unix::fs::MetadataExt as _;
            Ok(Self {
                device: metadata.dev(),
                inode: metadata.ino(),
            })
        }
        #[cfg(windows)]
        {
            let _ = metadata;
            let info = source.windows_info()?;
            Ok(Self {
                volume_serial_number: info.volume_serial_number,
                file_index: info.file_index,
            })
        }
        #[cfg(not(any(unix, windows)))]
        {
            let _ = source;
            Ok(Self {
                created: metadata.created().ok(),
            })
        }
    }
}

struct ReservedDecisionTrace {
    path: PathBuf,
    file: File,
    identity: DecisionTraceFileIdentity,
    claimed_by_solver: bool,
}

/// Exact-inode rollback for a reservation consumed by an invalidation attempt.
///
/// Namespace authentication can fail after the reservation leaves the global
/// registry. Keeping this guard armed ensures that every such return still
/// makes the descriptor-owned same-run trace non-replayable without touching a
/// raced-in pathname replacement.
struct ReservedDecisionTraceInvalidationGuard {
    reserved: ReservedDecisionTrace,
    invalidate_on_drop: bool,
}

impl ReservedDecisionTraceInvalidationGuard {
    fn new(reserved: ReservedDecisionTrace) -> Self {
        Self {
            reserved,
            invalidate_on_drop: true,
        }
    }

    fn invalidate_exact(&mut self) -> io::Result<()> {
        self.reserved.file.set_len(0)?;
        self.reserved.file.sync_all()?;
        self.invalidate_on_drop = false;
        Ok(())
    }
}

impl Drop for ReservedDecisionTraceInvalidationGuard {
    fn drop(&mut self) {
        if self.invalidate_on_drop {
            let _ = self.reserved.file.set_len(0);
            let _ = self.reserved.file.sync_all();
        }
    }
}

/// Authenticated same-run trace retained after terminal-outcome settlement.
///
/// The guard remains armed until [`Self::commit`] is called. Dropping an armed
/// guard makes the exact descriptor-owned inode non-replayable without
/// following or deleting its public pathname, which may have been replaced.
#[must_use = "dropping an uncommitted settled trace invalidates its exact inode"]
pub struct SettledDecisionTrace {
    reserved: ReservedDecisionTrace,
    expected: SolveOutcome,
    invalidate_on_drop: bool,
}

static RESERVED_DECISION_TRACE: OnceLock<Mutex<Option<ReservedDecisionTrace>>> = OnceLock::new();

fn reserved_decision_trace() -> &'static Mutex<Option<ReservedDecisionTrace>> {
    RESERVED_DECISION_TRACE.get_or_init(|| Mutex::new(None))
}

fn decision_trace_registry_error() -> io::Error {
    io::Error::other("decision-trace ownership registry is poisoned")
}

fn ensure_regular_single_link(
    metadata: &Metadata,
    path: &Path,
    source: TraceFileRef<'_>,
) -> io::Result<()> {
    if !metadata.file_type().is_file() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!(
                "decision-trace output '{}' is not a regular file",
                path.display()
            ),
        ));
    }
    #[cfg(unix)]
    {
        let _ = source;
        use std::os::unix::fs::MetadataExt as _;
        if metadata.nlink() != 1 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!(
                    "decision-trace output '{}' has {} hard links; exactly one is required",
                    path.display(),
                    metadata.nlink()
                ),
            ));
        }
    }
    #[cfg(windows)]
    {
        let links = source.windows_info()?.number_of_links;
        if links != 1 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!(
                    "decision-trace output '{}' has {links} hard links; exactly one is required",
                    path.display()
                ),
            ));
        }
    }
    #[cfg(not(any(unix, windows)))]
    {
        let _ = source;
    }
    Ok(())
}

fn open_new_decision_trace(path: &Path) -> io::Result<File> {
    let mut options = OpenOptions::new();
    options.read(true).write(true).create_new(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;
        options
            .mode(0o600)
            .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK);
    }
    let file = options.open(path)?;
    ensure_regular_single_link(&file.metadata()?, path, TraceFileRef::Handle(&file))?;
    Ok(file)
}

fn initialize_decision_trace(file: &mut File) -> io::Result<()> {
    file.write_all(MAGIC)?;
    write_u8(file, VERSION)?;
    file.flush()?;
    Ok(())
}

/// Zero a failed, partially initialized trace through its retained descriptor.
///
/// The pathname is never removed. A raced-in replacement is left untouched;
/// `false` reports that the visible path no longer names the created file.
fn invalidate_failed_decision_trace_creation(path: &Path, file: &File) -> io::Result<bool> {
    file.set_len(0)?;
    file.sync_all()?;
    let path_metadata = match std::fs::symlink_metadata(path) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(false),
        Err(error) => return Err(error),
    };
    let descriptor_metadata = file.metadata()?;
    if DecisionTraceFileIdentity::resolve(&path_metadata, TraceFileRef::Path(path))?
        != DecisionTraceFileIdentity::resolve(&descriptor_metadata, TraceFileRef::Handle(file))?
    {
        return Ok(false);
    }
    ensure_regular_single_link(&path_metadata, path, TraceFileRef::Path(path))?;
    ensure_regular_single_link(&descriptor_metadata, path, TraceFileRef::Handle(file))?;
    if path_metadata.len() != 0 || descriptor_metadata.len() != 0 {
        return Err(io::Error::other(format!(
            "failed decision-trace output '{}' was not fully invalidated",
            path.display()
        )));
    }
    Ok(true)
}

fn create_initialized_decision_trace(path: &Path) -> io::Result<File> {
    let mut file = open_new_decision_trace(path)?;
    if let Err(initialization_error) = initialize_decision_trace(&mut file) {
        return match invalidate_failed_decision_trace_creation(path, &file) {
            Ok(_) => Err(initialization_error),
            Err(cleanup_error) => Err(io::Error::new(
                initialization_error.kind(),
                format!(
                    "{initialization_error}; additionally failed to invalidate partial decision trace '{}': {cleanup_error}",
                    path.display()
                ),
            )),
        };
    }
    Ok(file)
}

fn validate_reserved_path(reserved: &ReservedDecisionTrace) -> io::Result<()> {
    let path_metadata = std::fs::symlink_metadata(&reserved.path)?;
    let descriptor_metadata = reserved.file.metadata()?;
    let path_identity =
        DecisionTraceFileIdentity::resolve(&path_metadata, TraceFileRef::Path(&reserved.path))?;
    let descriptor_identity = DecisionTraceFileIdentity::resolve(
        &descriptor_metadata,
        TraceFileRef::Handle(&reserved.file),
    )?;
    if path_identity != reserved.identity || descriptor_identity != reserved.identity {
        return Err(io::Error::other(format!(
            "decision-trace output '{}' was replaced after this run reserved it",
            reserved.path.display()
        )));
    }
    ensure_regular_single_link(
        &path_metadata,
        &reserved.path,
        TraceFileRef::Path(&reserved.path),
    )?;
    ensure_regular_single_link(
        &descriptor_metadata,
        &reserved.path,
        TraceFileRef::Handle(&reserved.file),
    )?;
    Ok(())
}

/// Reserve and initialize an explicit decision-trace output before solving.
///
/// The destination must not already exist. The retained descriptor and file
/// identity authenticate later SAT-writer attachment and CLI fallback
/// completion as belonging to this exact invocation.
pub fn reserve_decision_trace(path: &str) -> io::Result<()> {
    let path = PathBuf::from(path);
    let mut slot = reserved_decision_trace()
        .lock()
        .map_err(|_| decision_trace_registry_error())?;
    if slot.is_some() {
        return Err(io::Error::new(
            io::ErrorKind::AlreadyExists,
            "a decision-trace output is already reserved by this process",
        ));
    }
    let file = create_initialized_decision_trace(&path)?;
    let metadata = file.metadata()?;
    ensure_regular_single_link(&metadata, &path, TraceFileRef::Handle(&file))?;
    let identity = DecisionTraceFileIdentity::resolve(&metadata, TraceFileRef::Handle(&file))?;
    *slot = Some(ReservedDecisionTrace {
        path,
        file,
        identity,
        claimed_by_solver: false,
    });
    Ok(())
}

fn take_reserved_decision_trace(path: &Path) -> io::Result<Option<ReservedDecisionTrace>> {
    let mut slot = reserved_decision_trace()
        .lock()
        .map_err(|_| decision_trace_registry_error())?;
    let Some(reserved) = slot.take() else {
        return Ok(None);
    };
    if reserved.path != path {
        let reserved_path = reserved.path.clone();
        *slot = Some(reserved);
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!(
                "decision-trace path '{}' differs from reserved path '{}'",
                path.display(),
                reserved_path.display()
            ),
        ));
    }
    Ok(Some(reserved))
}

fn claim_reserved_decision_trace(path: &Path) -> io::Result<Option<File>> {
    let mut slot = reserved_decision_trace()
        .lock()
        .map_err(|_| decision_trace_registry_error())?;
    let Some(reserved) = slot.as_mut() else {
        return Ok(None);
    };
    if reserved.path != path {
        return Ok(None);
    }
    validate_reserved_path(reserved)?;
    if reserved.claimed_by_solver {
        return Err(io::Error::new(
            io::ErrorKind::AlreadyExists,
            format!(
                "decision-trace output '{}' is already claimed by a SAT solver",
                path.display()
            ),
        ));
    }
    if reserved.file.metadata()?.len() != INITIALIZED_TRACE_BYTES {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!(
                "reserved decision-trace output '{}' changed before SAT initialization",
                path.display()
            ),
        ));
    }
    let mut writer = reserved.file.try_clone()?;
    writer.seek(io::SeekFrom::End(0))?;
    reserved.claimed_by_solver = true;
    Ok(Some(writer))
}

/// Final solve outcome recorded in the trace.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SolveOutcome {
    Sat,
    Unsat,
    Unknown,
}

impl SolveOutcome {
    fn to_u8(self) -> u8 {
        match self {
            Self::Sat => 0,
            Self::Unsat => 1,
            Self::Unknown => 2,
        }
    }

    fn from_u8(raw: u8) -> io::Result<Self> {
        match raw {
            0 => Ok(Self::Sat),
            1 => Ok(Self::Unsat),
            2 => Ok(Self::Unknown),
            _ => Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("unknown solve outcome tag: {raw}"),
            )),
        }
    }
}

/// Compact deterministic replay event stream.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum TraceEvent {
    /// Decision literal chosen by the branching heuristic (DIMACS encoding).
    Decide { lit_dimacs: i32 },
    /// Propagated literal with the reason clause ID.
    Propagate { lit_dimacs: i32, clause_id: u64 },
    /// Conflict clause ID produced by propagation.
    Conflict { clause_id: u64 },
    /// Learned clause insertion with assigned clause ID.
    Learn { clause_id: u64 },
    /// Restart transition.
    Restart,
    /// Clause IDs removed by `reduce_db`.
    Reduce { clause_ids: Vec<u64> },
    /// Inprocessing pass marker (stable numeric code).
    Inprocess { pass_code: u8 },
    /// Final solve outcome.
    Result { outcome: SolveOutcome },
}

impl TraceEvent {
    fn write_to<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        match self {
            Self::Decide { lit_dimacs } => {
                write_u8(writer, TAG_DECIDE)?;
                write_i32(writer, *lit_dimacs)
            }
            Self::Propagate {
                lit_dimacs,
                clause_id,
            } => {
                write_u8(writer, TAG_PROPAGATE)?;
                write_i32(writer, *lit_dimacs)?;
                write_u64(writer, *clause_id)
            }
            Self::Conflict { clause_id } => {
                write_u8(writer, TAG_CONFLICT)?;
                write_u64(writer, *clause_id)
            }
            Self::Learn { clause_id } => {
                write_u8(writer, TAG_LEARN)?;
                write_u64(writer, *clause_id)
            }
            Self::Restart => write_u8(writer, TAG_RESTART),
            Self::Reduce { clause_ids } => {
                if clause_ids.len() > MAX_REDUCE_CLAUSE_IDS {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        format!(
                            "decision trace reduction contains {} clause IDs; limit is {}",
                            clause_ids.len(),
                            MAX_REDUCE_CLAUSE_IDS
                        ),
                    ));
                }
                let count = u32::try_from(clause_ids.len()).map_err(|_| {
                    io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "decision trace reduction clause-ID count exceeds u32",
                    )
                })?;
                write_u8(writer, TAG_REDUCE)?;
                write_u32(writer, count)?;
                for &clause_id in clause_ids {
                    write_u64(writer, clause_id)?;
                }
                Ok(())
            }
            Self::Inprocess { pass_code } => {
                write_u8(writer, TAG_INPROCESS)?;
                write_u8(writer, *pass_code)
            }
            Self::Result { outcome } => {
                write_u8(writer, TAG_RESULT)?;
                write_u8(writer, outcome.to_u8())
            }
        }
    }

    fn read_from<R: Read>(
        reader: &mut R,
        max_reduce_clause_ids: usize,
    ) -> io::Result<Option<Self>> {
        let mut tag = [0u8; 1];
        let read = reader.read(&mut tag)?;
        if read == 0 {
            return Ok(None);
        }

        let event = match tag[0] {
            TAG_DECIDE => Self::Decide {
                lit_dimacs: read_i32(reader)?,
            },
            TAG_PROPAGATE => Self::Propagate {
                lit_dimacs: read_i32(reader)?,
                clause_id: read_u64(reader)?,
            },
            TAG_CONFLICT => Self::Conflict {
                clause_id: read_u64(reader)?,
            },
            TAG_LEARN => Self::Learn {
                clause_id: read_u64(reader)?,
            },
            TAG_RESTART => Self::Restart,
            TAG_REDUCE => {
                let count = usize::try_from(read_u32(reader)?).map_err(|_| {
                    io::Error::new(
                        io::ErrorKind::InvalidData,
                        "decision trace reduction clause-ID count does not fit usize",
                    )
                })?;
                if count > max_reduce_clause_ids {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        format!(
                            "decision trace reduction contains {count} clause IDs; limit is \
                             {max_reduce_clause_ids}"
                        ),
                    ));
                }
                let mut clause_ids = Vec::new();
                clause_ids.try_reserve_exact(count).map_err(|error| {
                    io::Error::new(
                        io::ErrorKind::OutOfMemory,
                        format!(
                            "could not allocate decision trace reduction for {count} clause IDs: \
                             {error}"
                        ),
                    )
                })?;
                for _ in 0..count {
                    clause_ids.push(read_u64(reader)?);
                }
                Self::Reduce { clause_ids }
            }
            TAG_INPROCESS => Self::Inprocess {
                pass_code: read_u8(reader)?,
            },
            TAG_RESULT => Self::Result {
                outcome: SolveOutcome::from_u8(read_u8(reader)?)?,
            },
            other => {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!("unknown event tag: {other}"),
                ))
            }
        };

        Ok(Some(event))
    }
}

#[derive(Clone, Copy)]
struct ReplayLimits {
    max_bytes: u64,
    max_events: usize,
    max_reduce_clause_ids: usize,
}

const REPLAY_LIMITS: ReplayLimits = ReplayLimits {
    max_bytes: MAX_REPLAY_TRACE_BYTES,
    max_events: MAX_REPLAY_EVENTS,
    max_reduce_clause_ids: MAX_REDUCE_CLAUSE_IDS,
};

/// Reader that refuses to consume even one byte beyond the replay budget.
///
/// The one-byte probe at the boundary distinguishes an exactly-full trace
/// from a file that grew after its initial metadata check.
struct BoundedReplayReader<R> {
    inner: R,
    remaining: u64,
}

impl<R> BoundedReplayReader<R> {
    fn new(inner: R, max_bytes: u64) -> Self {
        Self {
            inner,
            remaining: max_bytes,
        }
    }
}

impl<R: Read> Read for BoundedReplayReader<R> {
    fn read(&mut self, buffer: &mut [u8]) -> io::Result<usize> {
        if buffer.is_empty() {
            return Ok(0);
        }
        if self.remaining == 0 {
            let mut overflow = [0u8; 1];
            return match self.inner.read(&mut overflow)? {
                0 => Ok(0),
                _ => Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "decision trace exceeds the replay byte limit",
                )),
            };
        }

        let allowed = usize::try_from(self.remaining)
            .unwrap_or(usize::MAX)
            .min(buffer.len());
        let read = self.inner.read(&mut buffer[..allowed])?;
        let read_u64 = u64::try_from(read)
            .map_err(|_| io::Error::other("replay read length does not fit u64"))?;
        self.remaining = self
            .remaining
            .checked_sub(read_u64)
            .ok_or_else(|| io::Error::other("replay byte accounting underflow"))?;
        Ok(read)
    }
}

/// Write-side binary trace sink.
pub(crate) struct DecisionTraceWriter {
    writer: BufWriter<File>,
    event_count: u64,
}

impl DecisionTraceWriter {
    /// Create and initialize a trace file.
    pub(crate) fn new(path: &str) -> io::Result<Self> {
        let path = Path::new(path);
        let file = match claim_reserved_decision_trace(path)? {
            Some(file) => file,
            None => create_initialized_decision_trace(path)?,
        };
        Ok(Self {
            writer: BufWriter::new(file),
            event_count: 0,
        })
    }

    /// Append one event to the trace.
    pub(crate) fn write_event(&mut self, event: &TraceEvent) -> io::Result<()> {
        event.write_to(&mut self.writer)?;
        self.event_count += 1;
        if self.event_count.is_multiple_of(1024) {
            self.writer.flush()?;
        }
        Ok(())
    }

    /// Flush and return the number of events written.
    pub(crate) fn finish(&mut self) -> io::Result<u64> {
        self.writer.flush()?;
        Ok(self.event_count)
    }
}

fn parse_trace<R: Read>(reader: &mut R, limits: ReplayLimits) -> io::Result<Vec<TraceEvent>> {
    let mut magic = [0u8; 8];
    reader.read_exact(&mut magic)?;
    if &magic != MAGIC {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "decision trace magic mismatch",
        ));
    }

    let version = read_u8(reader)?;
    if version != VERSION {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("unsupported decision trace version: {version}"),
        ));
    }

    let mut events = Vec::new();
    loop {
        if events.len() == limits.max_events {
            let mut overflow = [0u8; 1];
            if reader.read(&mut overflow)? != 0 {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!(
                        "decision trace contains more than {} events",
                        limits.max_events
                    ),
                ));
            }
            break;
        }

        let Some(event) = TraceEvent::read_from(reader, limits.max_reduce_clause_ids)? else {
            break;
        };
        events.try_reserve(1).map_err(|error| {
            io::Error::new(
                io::ErrorKind::OutOfMemory,
                format!("could not allocate decision trace event storage: {error}"),
            )
        })?;
        let is_result = matches!(event, TraceEvent::Result { .. });
        events.push(event);
        if is_result {
            let mut trailing = [0u8; 1];
            if reader.read(&mut trailing)? != 0 {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "decision trace contains trailing data after its terminal result",
                ));
            }
            break;
        }
    }
    Ok(events)
}

fn ensure_regular_replay_file(metadata: &Metadata, stage: &str) -> io::Result<()> {
    if metadata.file_type().is_file() {
        Ok(())
    } else {
        Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("decision replay input is not a regular file ({stage})"),
        ))
    }
}

fn ensure_same_replay_file(before: &Metadata, after: &Metadata, stage: &str) -> io::Result<()> {
    let mut unchanged = before.len() == after.len();
    if let (Ok(before_modified), Ok(after_modified)) = (before.modified(), after.modified()) {
        unchanged &= before_modified == after_modified;
    }

    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;

        unchanged &= before.dev() == after.dev()
            && before.ino() == after.ino()
            && before.mtime() == after.mtime()
            && before.mtime_nsec() == after.mtime_nsec();
    }

    if unchanged {
        Ok(())
    } else {
        Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("decision replay input changed {stage}"),
        ))
    }
}

fn open_replay_file(path: &Path, limits: ReplayLimits) -> io::Result<(File, Metadata)> {
    let path_metadata = std::fs::symlink_metadata(path)?;
    ensure_regular_replay_file(&path_metadata, "before open")?;
    if path_metadata.len() > limits.max_bytes {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!(
                "decision trace is {} bytes; replay byte limit is {}",
                path_metadata.len(),
                limits.max_bytes
            ),
        ));
    }

    let mut options = OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;

        // O_NONBLOCK prevents a raced-in FIFO or device from hanging open;
        // O_NOFOLLOW preserves the pre-open symlink rejection across the race.
        options.custom_flags(libc::O_NONBLOCK | libc::O_NOFOLLOW);
    }
    let file = options.open(path)?;
    let opened_metadata = file.metadata()?;
    ensure_regular_replay_file(&opened_metadata, "after open")?;
    ensure_same_replay_file(&path_metadata, &opened_metadata, "while opening")?;
    if opened_metadata.len() > limits.max_bytes {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!(
                "decision trace is {} bytes; replay byte limit is {}",
                opened_metadata.len(),
                limits.max_bytes
            ),
        ));
    }

    Ok((file, opened_metadata))
}

fn read_trace_with_limits(path: &str, limits: ReplayLimits) -> io::Result<Vec<TraceEvent>> {
    let (file, opened_metadata) = open_replay_file(Path::new(path), limits)?;
    let mut bounded = BoundedReplayReader::new(file, limits.max_bytes);
    let parse_result = {
        let mut reader = BufReader::new(&mut bounded);
        parse_trace(&mut reader, limits)
    };

    // Validate the already-open descriptor even when parsing failed. This
    // catches truncation or growth races without reopening the path.
    let final_metadata = bounded.inner.metadata()?;
    ensure_regular_replay_file(&final_metadata, "after read")?;
    ensure_same_replay_file(&opened_metadata, &final_metadata, "while reading")?;
    parse_result
}

/// Read a full binary trace from disk.
pub(crate) fn read_trace(path: &str) -> io::Result<Vec<TraceEvent>> {
    read_trace_with_limits(path, REPLAY_LIMITS)
}

/// Replay mismatch with exact stream position.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ReplayMismatch {
    pub(crate) position: usize,
    pub(crate) expected: Option<TraceEvent>,
    pub(crate) actual: Option<TraceEvent>,
}

impl ReplayMismatch {
    /// Human-readable mismatch summary for panic/error messages.
    pub(crate) fn describe(&self) -> String {
        format!(
            "decision trace divergence at event {}: expected {:?}, actual {:?}",
            self.position, self.expected, self.actual
        )
    }
}

/// Replay state that validates the observed event stream.
pub(crate) struct ReplayTrace {
    events: Vec<TraceEvent>,
    cursor: usize,
}

impl ReplayTrace {
    /// Load replay events from a binary trace file.
    pub(crate) fn from_file(path: &str) -> io::Result<Self> {
        let events = read_trace(path)?;
        if !matches!(events.last(), Some(TraceEvent::Result { .. })) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "decision replay trace is missing its terminal result",
            ));
        }
        Ok(Self { events, cursor: 0 })
    }

    /// Validate the next observed event.
    pub(crate) fn expect(&mut self, event: &TraceEvent) -> Result<(), ReplayMismatch> {
        let expected = self.events.get(self.cursor).cloned();
        match expected {
            Some(exp) if exp == *event => {
                self.cursor += 1;
                Ok(())
            }
            other => Err(ReplayMismatch {
                position: self.cursor,
                expected: other,
                actual: Some(event.clone()),
            }),
        }
    }

    /// Validate that the full replay stream was consumed.
    pub(crate) fn finish(&self) -> Result<(), ReplayMismatch> {
        if self.cursor == self.events.len() {
            Ok(())
        } else {
            Err(ReplayMismatch {
                position: self.cursor,
                expected: self.events.get(self.cursor).cloned(),
                actual: None,
            })
        }
    }
}

/// Resolve recording path from environment.
///
/// Activation:
/// - `AY_DECISION_TRACE_FILE=<path>`
static DECISION_TRACE_SUPPRESSED_AFTER_PUBLIC_MISMATCH: AtomicBool = AtomicBool::new(false);

/// Permanently suppress decision-trace recording for this process after a
/// public result diverges from the solver's raw result.
///
/// Such a trace cannot be replayed honestly: replay observes the raw SAT
/// result, not a CLI post-solve gate or synthesized fail-closed outcome. The
/// configured trace path is process-global, so suppression is process-global
/// as well. Existing writers must be detached before their retained descriptor
/// is used to zero the non-authoritative file.
pub fn suppress_decision_trace_after_public_mismatch() {
    DECISION_TRACE_SUPPRESSED_AFTER_PUBLIC_MISMATCH.store(true, Ordering::Release);
}

/// Whether decision tracing was permanently suppressed after a public/raw
/// verdict mismatch.
pub fn decision_trace_suppressed_after_public_mismatch() -> bool {
    DECISION_TRACE_SUPPRESSED_AFTER_PUBLIC_MISMATCH.load(Ordering::Acquire)
}

pub(crate) fn decision_trace_path_from_env() -> Option<String> {
    if decision_trace_suppressed_after_public_mismatch() {
        return None;
    }
    // Delegates to ay-core's centralized TraceConfig (#8495).
    ay_core::trace_config().decision_trace_path.clone()
}

/// Public outcome enum for minimal-trace emission.
///
/// Mirrors the internal `SolveOutcome` tag but is exposed as a stable API so
/// CLI callers can emit a fallback trace from outside `ay-sat` (see
/// [`write_minimal_trace`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TraceOutcome {
    /// Formula is satisfiable.
    Sat,
    /// Formula is unsatisfiable.
    Unsat,
    /// Solver could not decide (timeout, incomplete theory, etc.).
    Unknown,
}

impl TraceOutcome {
    fn to_internal(self) -> SolveOutcome {
        match self {
            Self::Sat => SolveOutcome::Sat,
            Self::Unsat => SolveOutcome::Unsat,
            Self::Unknown => SolveOutcome::Unknown,
        }
    }
}

/// Write a minimal valid decision trace containing only MAGIC + VERSION + a
/// single `Result` event with the given outcome.
///
/// Used by the CLI to guarantee that `--decision-trace <file>` always produces
/// a non-empty, replay-safe file even when the solver short-circuits on a
/// preprocessing-only UNSAT (or SAT / Unknown) path that never constructs a
/// `DecisionTraceWriter` on the SAT solver itself.
///
/// Refuses an existing path rather than following/truncating a symlink or hard
/// link. Callers that intentionally replace an empty placeholder should write
/// to an exclusively-created sibling via [`write_minimal_trace_to`] and rename
/// it atomically.
///
/// Part of `EXPLAINABILITY_AUDIT.md` Finding B: `--replay` round-trip
/// requires the trace file to end in a `Result` event; an empty or missing
/// file breaks the replay consumer.
pub fn write_minimal_trace(path: &str, outcome: TraceOutcome) -> io::Result<()> {
    let path = Path::new(path);
    let mut file = open_new_decision_trace(path)?;
    if let Err(write_error) = write_minimal_trace_to(&mut file, outcome) {
        return match invalidate_failed_decision_trace_creation(path, &file) {
            Ok(_) => Err(write_error),
            Err(cleanup_error) => Err(io::Error::new(
                write_error.kind(),
                format!(
                    "{write_error}; additionally failed to invalidate partial decision trace '{}': {cleanup_error}",
                    path.display()
                ),
            )),
        };
    }
    Ok(())
}

/// Write a minimal trace to an already-open sink.
///
/// This lets artifact-owning callers reserve a file with exclusive/no-follow
/// semantics and atomically publish it without reopening a pathname.
pub fn write_minimal_trace_to<W: Write>(writer: &mut W, outcome: TraceOutcome) -> io::Result<()> {
    writer.write_all(MAGIC)?;
    write_u8(writer, VERSION)?;
    TraceEvent::Result {
        outcome: outcome.to_internal(),
    }
    .write_to(writer)?;
    writer.flush()
}

fn parse_trace_terminal_outcome<R: Read>(
    reader: &mut R,
    limits: ReplayLimits,
) -> io::Result<Option<SolveOutcome>> {
    let mut magic = [0u8; 8];
    reader.read_exact(&mut magic)?;
    if &magic != MAGIC {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "decision trace magic mismatch",
        ));
    }
    let version = read_u8(reader)?;
    if version != VERSION {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("unsupported decision trace version: {version}"),
        ));
    }

    let mut event_count = 0_usize;
    loop {
        if event_count == limits.max_events {
            let mut overflow = [0_u8; 1];
            if reader.read(&mut overflow)? != 0 {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!(
                        "decision trace contains more than {} events",
                        limits.max_events
                    ),
                ));
            }
            return Ok(None);
        }
        let Some(event) = TraceEvent::read_from(reader, limits.max_reduce_clause_ids)? else {
            return Ok(None);
        };
        event_count += 1;
        if let TraceEvent::Result { outcome } = event {
            let mut trailing = [0_u8; 1];
            if reader.read(&mut trailing)? != 0 {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "decision trace contains trailing data after its terminal result",
                ));
            }
            return Ok(Some(outcome));
        }
    }
}

fn read_reserved_terminal_outcome(
    path: &Path,
    identity: DecisionTraceFileIdentity,
) -> io::Result<Option<SolveOutcome>> {
    let (file, opened_metadata) = open_replay_file(path, REPLAY_LIMITS)?;
    if DecisionTraceFileIdentity::resolve(&opened_metadata, TraceFileRef::Handle(&file))?
        != identity
    {
        return Err(io::Error::other(format!(
            "decision-trace output '{}' no longer names the file reserved by this run",
            path.display()
        )));
    }
    let mut bounded = BoundedReplayReader::new(file, REPLAY_LIMITS.max_bytes);
    let parse_result = {
        let mut reader = BufReader::new(&mut bounded);
        parse_trace_terminal_outcome(&mut reader, REPLAY_LIMITS)
    };
    let final_metadata = bounded.inner.metadata()?;
    ensure_regular_replay_file(&final_metadata, "after reserved-trace read")?;
    ensure_regular_single_link(&final_metadata, path, TraceFileRef::Handle(&bounded.inner))?;
    ensure_same_replay_file(
        &opened_metadata,
        &final_metadata,
        "while reading the reserved trace",
    )?;
    if DecisionTraceFileIdentity::resolve(&final_metadata, TraceFileRef::Handle(&bounded.inner))?
        != identity
    {
        return Err(io::Error::other(format!(
            "decision-trace output '{}' changed identity while it was validated",
            path.display()
        )));
    }
    let visible_metadata = std::fs::symlink_metadata(path)?;
    ensure_regular_single_link(&visible_metadata, path, TraceFileRef::Path(path))?;
    if DecisionTraceFileIdentity::resolve(&visible_metadata, TraceFileRef::Path(path))? != identity
    {
        return Err(io::Error::other(format!(
            "decision-trace output '{}' was replaced while it was validated",
            path.display()
        )));
    }
    parse_result
}

impl SettledDecisionTrace {
    /// Revalidate the exact retained trace and its public namespace binding.
    pub fn validate(&self) -> io::Result<()> {
        self.reserved.file.sync_data()?;
        validate_reserved_path(&self.reserved)?;
        match read_reserved_terminal_outcome(&self.reserved.path, self.reserved.identity)? {
            Some(outcome) if outcome == self.expected => {}
            Some(outcome) => {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!(
                        "decision trace terminal outcome {outcome:?} differs from public outcome {:?}",
                        self.expected
                    ),
                ));
            }
            None => {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "decision trace is missing its terminal result",
                ));
            }
        }
        validate_reserved_path(&self.reserved)
    }

    /// Preserve the settled trace when this guard is dropped.
    ///
    /// Call this only after every result gate and the corresponding public
    /// verdict emission have completed successfully.
    pub fn commit(&mut self) {
        self.invalidate_on_drop = false;
    }

    fn invalidate_exact(&self) -> io::Result<()> {
        self.reserved.file.set_len(0)?;
        self.reserved.file.sync_all()
    }
}

impl Drop for SettledDecisionTrace {
    fn drop(&mut self) {
        if self.invalidate_on_drop {
            let _ = self.invalidate_exact();
        }
    }
}

/// Complete or validate the decision trace reserved by this invocation while
/// retaining exact-inode rollback authority for later result gates.
///
/// If no SAT solver was constructed, this appends the one terminal result to
/// the retained descriptor. If a solver claimed the trace, the exact
/// descriptor-owned file must already contain a matching terminal result.
/// No pathname-only or pre-existing bytes are accepted as a fallback. The
/// returned guard must be committed only after the public verdict is emitted.
pub fn finish_reserved_decision_trace_retained(
    path: &str,
    outcome: TraceOutcome,
) -> io::Result<SettledDecisionTrace> {
    let path = Path::new(path);
    // Taking first makes the reservation single-use. The returned guard keeps
    // the exact descriptor armed across every subsequent publication gate.
    let reserved = take_reserved_decision_trace(path)?.ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::NotFound,
            "no decision-trace output was reserved by this invocation",
        )
    })?;
    let expected = outcome.to_internal();
    let mut settled = SettledDecisionTrace {
        reserved,
        expected,
        invalidate_on_drop: true,
    };
    validate_reserved_path(&settled.reserved)?;
    if !settled.reserved.claimed_by_solver {
        let length = settled.reserved.file.metadata()?.len();
        if length != INITIALIZED_TRACE_BYTES {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "unclaimed decision-trace output '{}' has {length} bytes; expected only the initialized header",
                    path.display()
                ),
            ));
        }
        settled.reserved.file.seek(io::SeekFrom::End(0))?;
        TraceEvent::Result { outcome: expected }.write_to(&mut settled.reserved.file)?;
        settled.reserved.file.flush()?;
        settled.reserved.file.sync_data()?;
    } else {
        // The solver flushes its buffered writer before returning a result.
        // Sync the shared file description before authenticating its bytes.
        settled.reserved.file.sync_data()?;
    }
    settled.validate()?;
    Ok(settled)
}

/// Complete or validate a reserved decision trace and commit it immediately.
///
/// Callers with later result gates should use
/// [`finish_reserved_decision_trace_retained`] instead.
pub fn finish_reserved_decision_trace(path: &str, outcome: TraceOutcome) -> io::Result<()> {
    let mut settled = finish_reserved_decision_trace_retained(path, outcome)?;
    settled.commit();
    Ok(())
}

/// Make a same-run reserved trace permanently non-replayable.
///
/// The reservation is consumed on every path. Its exact retained descriptor is
/// armed for truncation before namespace validation, so even a replaced public
/// path cannot strand the same-run inode. The pathname is never deleted or
/// opened for writing, so a raced-in replacement is preserved.
pub fn invalidate_reserved_decision_trace(path: &str) -> io::Result<()> {
    let path = Path::new(path);
    let Some(reserved) = take_reserved_decision_trace(path)? else {
        return match std::fs::symlink_metadata(path) {
            Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(()),
            Ok(metadata) if metadata.file_type().is_file() && metadata.len() == 0 => Ok(()),
            Ok(_) => Err(io::Error::new(
                io::ErrorKind::NotFound,
                "no same-run decision-trace reservation is available for safe invalidation",
            )),
            Err(error) => Err(error),
        };
    };

    let mut invalidation = ReservedDecisionTraceInvalidationGuard::new(reserved);

    validate_reserved_path(&invalidation.reserved)?;
    invalidation.invalidate_exact()?;
    validate_reserved_path(&invalidation.reserved)?;
    let visible_metadata = std::fs::symlink_metadata(path)?;
    if invalidation.reserved.file.metadata()?.len() != 0 || visible_metadata.len() != 0 {
        return Err(io::Error::other(format!(
            "decision-trace output '{}' was not fully invalidated",
            path.display()
        )));
    }
    Ok(())
}

/// Resolve replay path from environment.
///
/// Activation:
/// - `AY_REPLAY_TRACE_FILE=<path>`
pub(crate) fn replay_trace_path_from_env() -> Option<String> {
    // Delegates to ay-core's centralized TraceConfig (#8495).
    ay_core::trace_config().replay_trace_path.clone()
}

#[inline]
fn write_u8<W: Write>(writer: &mut W, value: u8) -> io::Result<()> {
    writer.write_all(&[value])
}

#[inline]
fn write_u32<W: Write>(writer: &mut W, value: u32) -> io::Result<()> {
    writer.write_all(&value.to_le_bytes())
}

#[inline]
fn write_u64<W: Write>(writer: &mut W, value: u64) -> io::Result<()> {
    writer.write_all(&value.to_le_bytes())
}

#[inline]
fn write_i32<W: Write>(writer: &mut W, value: i32) -> io::Result<()> {
    writer.write_all(&value.to_le_bytes())
}

#[inline]
fn read_u8<R: Read>(reader: &mut R) -> io::Result<u8> {
    let mut bytes = [0u8; 1];
    reader.read_exact(&mut bytes)?;
    Ok(bytes[0])
}

#[inline]
fn read_u32<R: Read>(reader: &mut R) -> io::Result<u32> {
    let mut bytes = [0u8; 4];
    reader.read_exact(&mut bytes)?;
    Ok(u32::from_le_bytes(bytes))
}

#[inline]
fn read_u64<R: Read>(reader: &mut R) -> io::Result<u64> {
    let mut bytes = [0u8; 8];
    reader.read_exact(&mut bytes)?;
    Ok(u64::from_le_bytes(bytes))
}

#[inline]
fn read_i32<R: Read>(reader: &mut R) -> io::Result<i32> {
    let mut bytes = [0u8; 4];
    reader.read_exact(&mut bytes)?;
    Ok(i32::from_le_bytes(bytes))
}

#[cfg(test)]
#[path = "decision_trace_tests.rs"]
mod tests;
