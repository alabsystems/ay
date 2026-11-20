// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A durable, ordered corpus stream. Only one bounded row is serialized or
//! decoded at a time. The final manifest commits to the entire byte stream,
//! including its campaign header, row order, and terminating newlines.

use super::*;
use std::io::{BufRead, BufReader, BufWriter, Read, Seek, SeekFrom, Write};

// A query may retain four 1-MiB capture streams (producer/checker stdout/stderr),
// whose JSON escaping can expand sixfold, plus identities and classifications.
// SAT and UNSAT transcript sets are mutually exclusive. This leaves headroom
// for metadata while bounding parser allocation independently of corpus size.
const MAX_ROW_BYTES: u64 = 32 * 1024 * 1024;
const MAX_CHECKPOINT_ROW_BYTES: u64 = 64 * 1024 * 1024;
const MAX_HEADER_BYTES: u64 = 64 * 1024;
const SCHEMA: &str = "ay-official-corpus-record-stream/v1";
const CHECKPOINT_SCHEMA: &str = "ay-official-corpus-record-stream/v2";

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub(super) struct Header {
    schema: String,
    campaign: String,
    profile: String,
    inventory: String,
    corpus: String,
    selection: String,
    ay: String,
    z3: String,
    envelope: String,
    rows: usize,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    producer: Option<Producer>,
}

impl Header {
    pub(super) fn new(results: &CorpusRunResults, rows: usize) -> Self {
        let producer = results.evaluator_sha256.as_ref().map(|evaluator| Producer {
            evaluator_sha256: evaluator.clone(),
            checker_sha256: results
                .checker
                .as_ref()
                .map(|checker| checker.sha256.clone()),
            artifact_root: results.artifact_root.clone(),
        });
        Self {
            schema: if producer.is_some() {
                CHECKPOINT_SCHEMA
            } else {
                SCHEMA
            }
            .to_string(),
            campaign: results.campaign_id.clone(),
            profile: results.profile_sha256.clone(),
            inventory: results.inventory_sha256.clone(),
            corpus: results.corpus_manifest_sha256.clone(),
            selection: results.corpus_selection_sha256.clone(),
            ay: results.ay_sha256.clone(),
            z3: results.z3_sha256.clone(),
            envelope: results.resource_envelope.clone(),
            rows,
            producer,
        }
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub(super) struct Manifest {
    pub(super) artifact: Artifact,
    pub(super) bytes: u64,
    pub(super) rows: usize,
    pub(super) semantic_sha256: String,
}

pub(super) struct Writer {
    writer: BufWriter<fs::File>,
    relative: String,
    digest: Sha256,
    semantic: Sha256,
    bytes: u64,
    rows: usize,
    expected_rows: usize,
}

fn encoded_line<T: Serialize>(value: &T, limit: u64) -> Result<Vec<u8>, String> {
    // The row's individual capture fields are already bounded. Still enforce a
    // serialization limit during writing, before a malformed row can allocate
    // an arbitrarily large JSON buffer.
    struct Limited {
        bytes: Vec<u8>,
        limit: u64,
    }
    impl Write for Limited {
        fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
            if bytes.len() as u64 > self.limit.saturating_sub(self.bytes.len() as u64) {
                return Err(std::io::Error::other(
                    "corpus record exceeds its byte bound",
                ));
            }
            self.bytes.extend_from_slice(bytes);
            Ok(bytes.len())
        }
        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }
    let mut output = Limited {
        bytes: Vec::new(),
        limit: limit.saturating_sub(1),
    };
    serde_json::to_writer(&mut output, value).map_err(|error| error.to_string())?;
    output.bytes.push(b'\n');
    Ok(output.bytes)
}

impl Writer {
    pub(super) fn create(path: &Path, relative: String, header: &Header) -> Result<Self, String> {
        let parent = path
            .parent()
            .filter(|path| !path.as_os_str().is_empty())
            .unwrap_or_else(|| Path::new("."));
        let encoded = encoded_line(header, MAX_HEADER_BYTES)?;
        let mut temporary = tempfile::NamedTempFile::new_in(parent)
            .map_err(|error| format!("create corpus record header: {error}"))?;
        temporary
            .write_all(&encoded)
            .and_then(|()| temporary.as_file().sync_data())
            .map_err(|error| format!("persist corpus record header: {error}"))?;
        let file = temporary
            .persist_noclobber(path)
            .map_err(|error| format!("publish corpus record stream {}: {error}", path.display()))?;
        fs::File::open(parent)
            .and_then(|directory| directory.sync_all())
            .map_err(|error| format!("persist corpus record directory: {error}"))?;
        let mut digest = Sha256::new();
        digest.update(&encoded);
        Ok(Self {
            writer: BufWriter::new(file),
            relative,
            digest,
            semantic: Sha256::new(),
            bytes: encoded.len() as u64,
            rows: 0,
            expected_rows: header.rows,
        })
    }

    pub(super) fn resume(
        path: &Path,
        relative: String,
        expected: &Header,
        mut validate: impl FnMut(usize, &FileRun) -> Result<(), String>,
        check_custody: impl FnOnce() -> Result<(), String>,
    ) -> Result<Self, String> {
        let mut file = open_checkpoint_mode(path, true)?;
        let initial = file.metadata().map_err(|error| error.to_string())?;
        check_same_checkpoint(path, &initial)?;
        let limit = (expected.rows as u64)
            .checked_mul(MAX_ROW_BYTES)
            .and_then(|bytes| bytes.checked_add(MAX_HEADER_BYTES))
            .ok_or("corpus stream budget overflow")?;
        if initial.len() > limit {
            return Err("corpus checkpoint exceeds its writer byte bound".into());
        }
        let mut reader = BufReader::new((&mut file).take(initial.len()));
        let line = read_line(&mut reader, MAX_HEADER_BYTES)?;
        let actual: Header = serde_json::from_slice(&line).map_err(|error| error.to_string())?;
        actual.bound_producer()?;
        if &actual != expected {
            return Err("corpus checkpoint producer or campaign header mismatch".into());
        }

        let mut digest = Sha256::new();
        digest.update(&line);
        let mut semantic = Sha256::new();
        let mut bytes = line.len() as u64;
        let mut rows = 0;
        loop {
            let line = read_bounded_line(&mut reader, MAX_ROW_BYTES)?;
            if line.is_empty() {
                break;
            }
            if rows >= expected.rows {
                return Err("unexpected extra corpus checkpoint data".into());
            }
            if !line.ends_with(b"\n") {
                break;
            }
            let row: FileRun = serde_json::from_slice(&line)
                .map_err(|error| format!("invalid corpus checkpoint record {rows}: {error}"))?;
            validate_final_row_fields(expected, &row)?;
            validate(rows, &row)?;
            digest.update(&line);
            bytes = bytes
                .checked_add(line.len() as u64)
                .ok_or("checkpoint size overflow")?;
            update_semantic(&mut semantic, &row)?;
            rows += 1;
        }
        drop(reader);

        // No write, including removal of a torn row, precedes prefix
        // authentication and replay. Recheck against the opened inode.
        file.seek(SeekFrom::Start(0))
            .map_err(|error| error.to_string())?;
        let mut rehash = Sha256::new();
        let read = std::io::copy(&mut (&mut file).take(bytes), &mut rehash)
            .map_err(|error| format!("rehash corpus checkpoint prefix: {error}"))?;
        if read != bytes || rehash.finalize() != digest.clone().finalize() {
            return Err("corpus checkpoint prefix changed during replay".into());
        }
        check_custody()?;
        check_same_checkpoint(path, &initial)?;
        if bytes != initial.len() {
            file.set_len(bytes)
                .and_then(|()| file.sync_data())
                .map_err(|error| format!("persist removal of torn corpus record: {error}"))?;
        }
        file.seek(SeekFrom::Start(bytes))
            .map_err(|error| error.to_string())?;
        Ok(Self {
            writer: BufWriter::new(file),
            relative,
            digest,
            semantic,
            bytes,
            rows,
            expected_rows: expected.rows,
        })
    }

    fn append_bytes(&mut self, bytes: &[u8]) -> Result<(), String> {
        self.writer
            .write_all(bytes)
            .and_then(|()| self.writer.flush())
            .and_then(|()| self.writer.get_ref().sync_data())
            .map_err(|error| format!("persist corpus record stream: {error}"))?;
        self.digest.update(bytes);
        self.bytes = self
            .bytes
            .checked_add(bytes.len() as u64)
            .ok_or("corpus record size overflow")?;
        Ok(())
    }

    pub(super) fn append(&mut self, row: &FileRun) -> Result<(), String> {
        if self.rows >= self.expected_rows {
            return Err("unexpected extra corpus record".into());
        }
        let bytes = encoded_line(row, MAX_ROW_BYTES)?;
        self.append_bytes(&bytes)?;
        update_semantic(&mut self.semantic, row)?;
        self.rows += 1;
        Ok(())
    }

    pub(super) fn finish(self) -> Result<Manifest, String> {
        if self.rows != self.expected_rows {
            return Err("corpus record stream is incomplete".into());
        }
        Ok(Manifest {
            artifact: Artifact {
                path: self.relative,
                sha256: format!("{:x}", self.digest.finalize()),
            },
            bytes: self.bytes,
            rows: self.rows,
            semantic_sha256: format!("{:x}", self.semantic.finalize()),
        })
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct Producer {
    evaluator_sha256: String,
    checker_sha256: Option<String>,
    artifact_root: String,
}

fn open_checkpoint(path: &Path) -> Result<fs::File, String> {
    open_checkpoint_mode(path, false)
}

fn open_checkpoint_mode(path: &Path, writable: bool) -> Result<fs::File, String> {
    let mut open = fs::OpenOptions::new();
    open.read(true).write(writable);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        open.custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK);
    }
    #[cfg(not(unix))]
    if !fs::symlink_metadata(path)
        .map_err(|error| error.to_string())?
        .is_file()
    {
        return Err("checkpoint must be a regular non-symlink file".into());
    }
    open.open(path)
        .map_err(|error| format!("open corpus checkpoint {}: {error}", path.display()))
}

fn check_same_checkpoint(path: &Path, initial: &fs::Metadata) -> Result<(), String> {
    let current = fs::symlink_metadata(path).map_err(|error| error.to_string())?;
    if !initial.is_file() || !current.is_file() || current.len() != initial.len() {
        return Err("corpus checkpoint was replaced or resized during replay".into());
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        if initial.nlink() != 1
            || current.nlink() != 1
            || current.ino() != initial.ino()
            || current.dev() != initial.dev()
            || current.ctime() != initial.ctime()
            || current.ctime_nsec() != initial.ctime_nsec()
            || current.mtime() != initial.mtime()
            || current.mtime_nsec() != initial.mtime_nsec()
        {
            return Err("corpus checkpoint was linked, replaced, or changed during replay".into());
        }
    }
    Ok(())
}

fn read_bounded_line(reader: &mut impl BufRead, limit: u64) -> Result<Vec<u8>, String> {
    let mut line = Vec::new();
    reader
        .take(limit + 1)
        .read_until(b'\n', &mut line)
        .map_err(|error| error.to_string())?;
    if line.len() as u64 > limit {
        return Err("corpus record exceeds its byte bound".into());
    }
    Ok(line)
}

fn read_line(reader: &mut impl BufRead, limit: u64) -> Result<Vec<u8>, String> {
    let line = read_bounded_line(reader, limit)?;
    if !line.ends_with(b"\n") {
        return Err("missing or truncated corpus record".into());
    }
    Ok(line)
}

fn checkpoint_size_limit(header: &Header) -> Result<u64, String> {
    (header.rows as u64)
        .checked_mul(MAX_CHECKPOINT_ROW_BYTES)
        .and_then(|n| n.checked_add(MAX_HEADER_BYTES))
        .ok_or_else(|| "corpus stream budget overflow".into())
}

#[derive(Serialize)]
pub(super) struct CheckpointSnapshot {
    rows: usize,
    bytes: u64,
    prefix_sha256: String,
}

impl Header {
    pub(super) fn reference_sha256(&self) -> &str {
        &self.z3
    }

    pub(super) fn has_pinned_checker(&self) -> bool {
        self.producer
            .as_ref()
            .and_then(|producer| producer.checker_sha256.as_deref())
            .is_some_and(|digest| checker_cohort::version_for_sha(digest).is_some())
    }

    pub(super) fn require_checkpoint_population(
        &self,
        manifest: &OfficialCorpusManifest,
        manifest_sha256: &str,
    ) -> Result<(), String> {
        validate_id(&self.campaign, "corpus checkpoint campaign")?;
        let producer = self.bound_producer()?;
        validate_sha256(&self.ay, "checkpoint AY executable")?;
        validate_sha256(&self.inventory, "checkpoint inventory")?;
        validate_sha256(&producer.evaluator_sha256, "checkpoint evaluator")?;
        if let Some(checker) = &producer.checker_sha256 {
            validate_sha256(checker, "checkpoint checker")?;
        }
        validate_relative_path(&producer.artifact_root, "checkpoint artifact root")?;
        parse_resource_envelope_for(&self.envelope, ResourceEnvelopeUse::Observation)?;
        if self.corpus != manifest_sha256
            || self.selection != manifest.selection_sha256
            || self.rows != manifest.files.len()
        {
            return Err("checkpoint does not describe the exact pinned corpus".into());
        }
        self.require_pinned_producer_platform()
    }

    fn bound_producer(&self) -> Result<&Producer, String> {
        if self.schema != CHECKPOINT_SCHEMA {
            return Err("unsupported corpus checkpoint schema".into());
        }
        self.producer
            .as_ref()
            .ok_or_else(|| "corpus checkpoint lacks its producer binding".into())
    }

    fn require_pinned_producer_platform(&self) -> Result<(), String> {
        let producer = self.bound_producer()?;
        for platform in reference_platform::Platform::ALL {
            let release = platform.release()?;
            if self.z3 == release.executable_sha256
                && self.profile == profile_sha256(&canonical_profile_for(release)?)?
            {
                if producer.checker_sha256.as_deref().is_some_and(|digest| {
                    checker_cohort::version_for_platform(platform, digest).is_none()
                }) {
                    return Err("checkpoint checker is outside the producer platform pins".into());
                }
                return Ok(());
            }
        }
        Err("checkpoint profile and reference are outside the compiled pins".into())
    }
}

/// Capture only newline-complete rows present at the first file-size sample.
/// An active writer may append; it keeps authority to validate and publish
/// final results. Rehash the same accepted prefix before exposing the view.
pub(super) fn inspect_checkpoint(
    path: &Path,
    mut inspect_header: impl FnMut(&Header) -> Result<(), String>,
    mut inspect_row: impl FnMut(&Header, usize, &FileRun) -> Result<(), String>,
) -> Result<(Header, CheckpointSnapshot), String> {
    let mut file = open_checkpoint(path)?;
    let initial = file.metadata().map_err(|error| error.to_string())?;
    if !initial.is_file() {
        return Err("corpus checkpoint must be a regular file".into());
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        if initial.nlink() != 1 {
            return Err("checkpoint must have exactly one link".into());
        }
    }
    let mut reader = BufReader::new((&mut file).take(initial.len()));
    let line = read_line(&mut reader, MAX_HEADER_BYTES)?;
    let header: Header = serde_json::from_slice(&line).map_err(|error| error.to_string())?;
    header.bound_producer()?;
    inspect_header(&header)?;
    if initial.len() > checkpoint_size_limit(&header)? {
        return Err("corpus checkpoint exceeds the bounded population size".into());
    }
    let mut digest = Sha256::new();
    digest.update(&line);
    let mut bytes = line.len() as u64;
    let mut rows = 0;
    loop {
        let line = read_bounded_line(&mut reader, MAX_CHECKPOINT_ROW_BYTES)?;
        if line.is_empty() {
            break;
        }
        if rows >= header.rows {
            return Err("unexpected extra corpus checkpoint data".into());
        }
        if !line.ends_with(b"\n") {
            break;
        }
        let row: FileRun = serde_json::from_slice(&line)
            .map_err(|error| format!("invalid corpus checkpoint record {rows}: {error}"))?;
        inspect_row(&header, rows, &row)?;
        digest.update(&line);
        bytes = bytes
            .checked_add(line.len() as u64)
            .ok_or("checkpoint size overflow")?;
        rows += 1;
    }
    drop(reader);
    let hash = digest.finalize();
    let current = open_checkpoint(path)?;
    let current_meta = current.metadata().map_err(|error| error.to_string())?;
    if !current_meta.is_file() || current_meta.len() < bytes {
        return Err("checkpoint prefix was removed while it was inspected".into());
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        if initial.nlink() != 1
            || current_meta.nlink() != 1
            || initial.ino() != current_meta.ino()
            || initial.dev() != current_meta.dev()
        {
            return Err("checkpoint was linked or replaced during inspection".into());
        }
    }
    let mut rehash = Sha256::new();
    let read = std::io::copy(&mut current.take(bytes), &mut rehash)
        .map_err(|error| format!("rehash corpus checkpoint prefix: {error}"))?;
    if read != bytes || rehash.finalize() != hash {
        return Err("checkpoint prefix changed while it was inspected".into());
    }
    Ok((
        header,
        CheckpointSnapshot {
            rows,
            bytes,
            prefix_sha256: format!("{hash:x}"),
        },
    ))
}

pub(super) fn visit(
    manifest: &Manifest,
    base: &Path,
    header: &Header,
    mut consume: impl FnMut(usize, FileRun) -> Result<(), String>,
) -> Result<(), String> {
    validate_sha256(&manifest.artifact.sha256, "corpus record stream")?;
    validate_sha256(&manifest.semantic_sha256, "corpus semantic stream")?;
    if manifest.rows != header.rows {
        return Err("corpus record count differs from population".into());
    }
    let max_bytes = (header.rows as u64)
        .checked_mul(MAX_ROW_BYTES)
        .and_then(|n| n.checked_add(MAX_HEADER_BYTES))
        .ok_or("corpus stream budget overflow")?;
    let path = resolve_relative_evidence_path(base, &manifest.artifact.path)?;
    let metadata = fs::symlink_metadata(&path).map_err(|error| error.to_string())?;
    if !metadata.file_type().is_file()
        || metadata.len() != manifest.bytes
        || metadata.len() > max_bytes
    {
        return Err("corpus record stream type or size mismatch".into());
    }
    let mut reader = BufReader::new(fs::File::open(&path).map_err(|error| error.to_string())?);
    let mut digest = Sha256::new();
    let mut semantic = Sha256::new();
    let line = read_line(&mut reader, MAX_HEADER_BYTES)?;
    let actual: Header = serde_json::from_slice(&line).map_err(|error| error.to_string())?;
    if &actual != header {
        return Err("corpus record campaign header mismatch".into());
    }
    digest.update(&line);
    let mut bytes = line.len() as u64;
    for index in 0..manifest.rows {
        let line = read_line(&mut reader, MAX_ROW_BYTES)?;
        digest.update(&line);
        bytes = bytes
            .checked_add(line.len() as u64)
            .ok_or("corpus stream byte count overflow")?;
        let row: FileRun = serde_json::from_slice(&line)
            .map_err(|error| format!("invalid corpus record {index}: {error}"))?;
        validate_final_row_fields(header, &row)?;
        update_semantic(&mut semantic, &row)?;
        consume(index, row)?;
    }
    if !reader
        .fill_buf()
        .map_err(|error| error.to_string())?
        .is_empty()
    {
        return Err("trailing or extra corpus records".into());
    }
    if bytes != manifest.bytes
        || format!("{:x}", digest.finalize()) != manifest.artifact.sha256
        || format!("{:x}", semantic.finalize()) != manifest.semantic_sha256
    {
        return Err("corpus record stream digest mismatch".into());
    }
    Ok(())
}

fn validate_final_row_fields(header: &Header, row: &FileRun) -> Result<(), String> {
    if header.producer.is_some() {
        if row.input_size.is_none() || row.has_extended_observation_fields() {
            return Err("v2 corpus receipt has invalid final record fields".into());
        }
    } else if row.input_size.is_some() || row.has_extended_observation_fields() {
        return Err("v1 corpus receipt contains v2 checkpoint row fields".into());
    }
    Ok(())
}

fn update_semantic(digest: &mut Sha256, file: &FileRun) -> Result<(), String> {
    let row = (
        file.path.as_str(),
        file.outcome,
        file.queries
            .iter()
            .map(|query| {
                (
                    query.ordinal,
                    query.command.as_str(),
                    query.prefix_sha256.as_str(),
                    query.z3,
                    query.ay,
                    query.evidence.status,
                    query.outcome,
                )
            })
            .collect::<Vec<_>>(),
    );
    digest.update(encoded_line(&row, MAX_ROW_BYTES)?);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn header(rows: usize) -> Header {
        Header {
            schema: SCHEMA.into(),
            campaign: "test-campaign".into(),
            profile: "p".into(),
            inventory: "i".into(),
            corpus: "c".into(),
            selection: "s".into(),
            ay: "a".into(),
            z3: "z".into(),
            envelope: "bounded-test".into(),
            rows,
            producer: None,
        }
    }

    fn file(index: usize) -> CorpusFile {
        let input = b"(check-sat)";
        CorpusFile {
            path: format!("QF_UF/{index}.smt2"),
            size: input.len() as u64,
            sha256: sha256_bytes(input),
            queries: scan_queries(input).unwrap(),
            echoes: None,
        }
    }

    fn failed(index: usize) -> FileRun {
        classify_file(
            &file(index),
            ProcessRun::unavailable("retained AY failure".into()),
            ProcessRun::unavailable("retained oracle failure".into()),
        )
    }

    fn write_rows(base: &Path, rows: &[FileRun]) -> Manifest {
        let path = base.join("records.jsonl");
        let mut writer =
            Writer::create(&path, "records.jsonl".into(), &header(rows.len())).unwrap();
        for row in rows {
            writer.append(row).unwrap();
        }
        writer.finish().unwrap()
    }

    fn check_rows(
        base: &Path,
        manifest: &Manifest,
        count: usize,
    ) -> Result<CorpusRunCounts, String> {
        let mut counts = CorpusRunCounts::default();
        visit(manifest, base, &header(count), |index, row| {
            validate_file_result(&row, &file(index), "/unused", base, "evidence", None)?;
            accumulate_run_counts(&mut counts, &row)
        })?;
        Ok(counts)
    }

    fn checkpoint_header(rows: usize) -> Header {
        Header {
            schema: CHECKPOINT_SCHEMA.into(),
            producer: Some(Producer {
                evaluator_sha256: sha256_bytes(b"test evaluator"),
                checker_sha256: None,
                artifact_root: "evidence".into(),
            }),
            ..header(rows)
        }
    }

    #[test]
    fn checkpoint_binds_reference_profile_and_checker_to_one_producer_platform() {
        use reference_platform::Platform;

        let linux = Platform::LinuxArm64.release().unwrap();
        let mac = Platform::MacosArm64.release().unwrap();
        let mut header = checkpoint_header(1);
        header.z3 = linux.executable_sha256.into();
        header.profile = profile_sha256(&canonical_profile_for(linux).unwrap()).unwrap();
        assert!(header.require_pinned_producer_platform().is_ok());

        header.profile = profile_sha256(&canonical_profile_for(mac).unwrap()).unwrap();
        assert!(header.require_pinned_producer_platform().is_err());

        header.profile = profile_sha256(&canonical_profile_for(linux).unwrap()).unwrap();
        header.producer.as_mut().unwrap().checker_sha256 =
            Some(checker_cohort::PACKAGED_SHA256.into());
        assert!(header.require_pinned_producer_platform().is_err());

        header.z3 = mac.executable_sha256.into();
        header.profile = profile_sha256(&canonical_profile_for(mac).unwrap()).unwrap();
        assert!(header.require_pinned_producer_platform().is_ok());
    }

    fn write_checkpoint(path: &Path, header: &Header, rows: &[FileRun]) -> fs::File {
        let mut writer = fs::OpenOptions::new()
            .create_new(true)
            .append(true)
            .open(path)
            .unwrap();
        writer
            .write_all(&encoded_line(header, MAX_HEADER_BYTES).unwrap())
            .unwrap();
        for row in rows {
            writer
                .write_all(&encoded_line(row, MAX_CHECKPOINT_ROW_BYTES).unwrap())
                .unwrap();
        }
        writer
    }

    fn stored_failure(index: usize) -> FileRun {
        let mut result = failed(index);
        result.input_size = Some(file(index).size);
        result
    }

    #[test]
    fn resume_replays_before_trimming_and_commits_only_the_exact_suffix() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("records.jsonl");
        let header = checkpoint_header(2);
        let mut file = write_checkpoint(&path, &header, &[stored_failure(0)]);
        file.write_all(b"{\"path\":").unwrap();
        drop(file);
        let initial = fs::read(&path).unwrap();

        let denied = Writer::resume(
            &path,
            "records.jsonl".into(),
            &header,
            |_, _| Err("independent replay refused".into()),
            || unreachable!("custody check cannot precede replay"),
        );
        assert!(denied.is_err());
        assert_eq!(fs::read(&path).unwrap(), initial);
        let denied = Writer::resume(
            &path,
            "records.jsonl".into(),
            &header,
            |_, _| Ok(()),
            || Err("producer lease moved".into()),
        );
        assert!(denied.is_err());
        assert_eq!(fs::read(&path).unwrap(), initial);

        let mut observed = Vec::new();
        let mut resumed = Writer::resume(
            &path,
            "records.jsonl".into(),
            &header,
            |index, row| {
                observed.push((index, row.input_sha256.clone()));
                Ok(())
            },
            || Ok(()),
        )
        .unwrap();
        assert_eq!(observed, [(0, stored_failure(0).input_sha256)]);
        assert_eq!(fs::read(&path).unwrap(), initial[..initial.len() - 8]);
        resumed.append(&stored_failure(1)).unwrap();
        let final_manifest = resumed.finish().unwrap();
        visit(&final_manifest, dir.path(), &header, |index, actual| {
            assert_eq!(actual, stored_failure(index));
            Ok(())
        })
        .unwrap();
    }

    #[test]
    fn resume_refuses_legacy_foreign_malformed_or_extra_data_without_writes() {
        let dir = tempfile::tempdir().unwrap();
        let expected = checkpoint_header(2);
        let mut foreign = expected.clone();
        foreign.producer.as_mut().unwrap().evaluator_sha256 = sha256_bytes(b"other evaluator");
        for (name, actual, rows, tail) in [
            ("legacy", header(2), vec![failed(0)], &b"torn"[..]),
            ("foreign", foreign, vec![stored_failure(0)], &b"torn"[..]),
            (
                "malformed",
                expected.clone(),
                vec![stored_failure(0)],
                &b"bad\n"[..],
            ),
            ("missing-size", expected.clone(), vec![failed(0)], &b""[..]),
            (
                "extra",
                expected.clone(),
                vec![stored_failure(0), stored_failure(1)],
                &b"torn"[..],
            ),
        ] {
            let path = dir.path().join(name);
            let mut file = write_checkpoint(&path, &actual, &rows);
            file.write_all(tail).unwrap();
            drop(file);
            let initial = fs::read(&path).unwrap();
            assert!(
                Writer::resume(&path, name.into(), &expected, |_, _| Ok(()), || Ok(()),).is_err(),
                "{name}"
            );
            assert_eq!(fs::read(&path).unwrap(), initial, "{name}");
        }
    }

    #[test]
    fn resume_refuses_same_length_prefix_change_during_replay() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("records.jsonl");
        let header = checkpoint_header(2);
        let mut writer = write_checkpoint(&path, &header, &[stored_failure(0)]);
        writer.write_all(b"torn").unwrap();
        drop(writer);
        let initial = fs::read(&path).unwrap();
        let mut changed = initial.clone();
        changed[0] = b' ';
        let resumed = Writer::resume(
            &path,
            "records.jsonl".into(),
            &header,
            |_, _| {
                fs::write(&path, &changed).unwrap();
                Ok(())
            },
            || Ok(()),
        );
        assert!(resumed.is_err());
        assert_eq!(fs::read(&path).unwrap(), changed);
    }

    #[test]
    fn live_writer_and_final_reader_share_producer_bound_records() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("records.jsonl");
        let header = checkpoint_header(2);
        let mut writer = Writer::create(&path, "records.jsonl".into(), &header).unwrap();
        let row = |index| {
            let mut result = failed(index);
            result.input_size = Some(file(index).size);
            result
        };
        let first = row(0);
        writer.append(&first).unwrap();
        let mut seen = Vec::new();
        let (observed, snapshot) = inspect_checkpoint(
            &path,
            |_| Ok(()),
            |_, index, result| {
                seen.push((index, result.input_sha256.clone(), result.input_size));
                Ok(())
            },
        )
        .unwrap();
        assert_eq!(observed, header);
        assert_eq!(snapshot.rows, 1);
        assert_eq!(seen, [(0, first.input_sha256, first.input_size)]);
        writer.append(&row(1)).unwrap();
        let manifest = writer.finish().unwrap();
        visit(&manifest, dir.path(), &header, |index, result| {
            assert_eq!(result.input_size, Some(file(index).size));
            Ok(())
        })
        .unwrap();
        let mut foreign = header.clone();
        foreign.producer.as_mut().unwrap().evaluator_sha256 = sha256_bytes(b"other evaluator");
        assert!(visit(&manifest, dir.path(), &foreign, |_, _| Ok(())).is_err());

        let missing = dir.path().join("missing-size.jsonl");
        let incomplete_header = checkpoint_header(1);
        let mut incomplete =
            Writer::create(&missing, "missing-size.jsonl".into(), &incomplete_header).unwrap();
        incomplete.append(&failed(0)).unwrap();
        let malformed = incomplete.finish().unwrap();
        assert!(visit(&malformed, dir.path(), &incomplete_header, |_, _| Ok(())).is_err());
    }

    #[test]
    fn checkpoint_inspection_reads_only_the_sampled_complete_rows() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("records.jsonl");
        let header = checkpoint_header(3);
        let mut writer = write_checkpoint(&path, &header, &[failed(0)]);
        let first = fs::read(&path).unwrap();
        let mut seen = Vec::new();
        let (_, snapshot) = inspect_checkpoint(
            &path,
            |actual| {
                assert_eq!(&header, actual);
                writer
                    .write_all(&encoded_line(&failed(1), MAX_CHECKPOINT_ROW_BYTES)?)
                    .map_err(|error| error.to_string())
            },
            |_, index, row| {
                seen.push((index, row.path.clone()));
                Ok(())
            },
        )
        .unwrap();
        assert_eq!(seen, vec![(0, file(0).path)]);
        assert_eq!(snapshot.rows, 1);
        assert_eq!(snapshot.bytes, first.len() as u64);
        assert_eq!(snapshot.prefix_sha256, sha256_bytes(&first));
        drop(writer);

        let complete = fs::read(&path).unwrap();
        fs::OpenOptions::new()
            .append(true)
            .open(&path)
            .unwrap()
            .write_all(b"{\"path\":\"unfinished")
            .unwrap();
        let with_tail = fs::read(&path).unwrap();
        let (_, snapshot) = inspect_checkpoint(&path, |_| Ok(()), |_, _, _| Ok(())).unwrap();
        assert_eq!(snapshot.rows, 2);
        assert_eq!(snapshot.bytes, complete.len() as u64);
        assert_eq!(snapshot.prefix_sha256, sha256_bytes(&complete));
        assert_eq!(fs::read(&path).unwrap(), with_tail);
    }

    #[test]
    fn checkpoint_inspection_refuses_mutation_of_the_sampled_prefix() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("records.jsonl");
        drop(write_checkpoint(&path, &checkpoint_header(1), &[failed(0)]));
        let error = inspect_checkpoint(
            &path,
            |_| Ok(()),
            |_, _, _| {
                fs::OpenOptions::new()
                    .write(true)
                    .open(&path)
                    .unwrap()
                    .write_all(b"[")
                    .unwrap();
                Ok(())
            },
        )
        .err()
        .expect("mutation must prevent publication");
        assert!(error.contains("checkpoint prefix changed"));
    }

    #[test]
    fn native_watchdog_label_is_observational_only() {
        let envelope = "oom-guard-v2:jobs=1;memlimit_mb=4096;nbcore=1;headroom_mb=2048;timeout_ns=30000000000;enforcement=ay-resource-v1:native-rss-watchdog-zero-grace;aggregate=ay-host-exclusive-flock-v1";
        parse_resource_envelope_for(envelope, ResourceEnvelopeUse::Observation).unwrap();
        assert!(parse_resource_envelope(envelope).is_err());

        let foreign = envelope.replace("native-rss-watchdog-zero-grace", "foreign-watchdog");
        assert!(parse_resource_envelope_for(&foreign, ResourceEnvelopeUse::Observation).is_err());
    }

    #[test]
    fn checkpoint_binding_is_required_and_v1_final_reader_stays_closed() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("records.jsonl");
        let mut writer = Writer::create(&path, "records.jsonl".into(), &header(1)).unwrap();
        writer.append(&failed(0)).unwrap();
        let manifest = writer.finish().unwrap();
        let data = fs::read_to_string(&path).unwrap();
        assert!(!data.contains("input_size"));
        assert!(!data.contains("echo_streams"));
        visit(&manifest, dir.path(), &header(1), |_, _| Ok(())).unwrap();
        assert!(inspect_checkpoint(&path, |_| Ok(()), |_, _, _| Ok(())).is_err());

        let forged = dir.path().join("forged.jsonl");
        let mut row = failed(0);
        row.input_size = Some(file(0).size);
        let mut writer = Writer::create(&forged, "forged.jsonl".into(), &header(1)).unwrap();
        writer.append(&row).unwrap();
        let manifest = writer.finish().unwrap();
        let error = visit(&manifest, dir.path(), &header(1), |_, _| Ok(())).unwrap_err();
        assert!(error.contains("v2 checkpoint row fields"));

        let unbound = dir.path().join("unbound.jsonl");
        let mut value = serde_json::to_value(checkpoint_header(1)).unwrap();
        value.as_object_mut().unwrap().remove("producer");
        fs::write(&unbound, encoded_line(&value, MAX_HEADER_BYTES).unwrap()).unwrap();
        assert!(inspect_checkpoint(&unbound, |_| Ok(()), |_, _, _| Ok(())).is_err());
    }

    #[test]
    fn stream_preserves_every_failed_row_and_derives_counts() {
        let dir = tempfile::tempdir().unwrap();
        let manifest = write_rows(dir.path(), &[failed(0), failed(1)]);
        let counts = check_rows(dir.path(), &manifest, 2).unwrap();
        assert_eq!(counts.files_total, 2);
        assert_eq!(counts.files_failed, 2);
        assert_eq!(counts.unavailable, 2);
        assert_eq!(counts.missing, 2);
        assert!(!counts.complete());
        visit(&manifest, dir.path(), &header(2), |_, row| {
            assert_eq!(row.ay.harness_error.as_deref(), Some("retained AY failure"));
            assert_eq!(
                row.z3.harness_error.as_deref(),
                Some("retained oracle failure")
            );
            Ok(())
        })
        .unwrap();
    }

    #[test]
    fn authenticated_duplicate_reordered_and_forged_rows_are_rejected() {
        for rows in [vec![failed(0), failed(0)], vec![failed(1), failed(0)]] {
            let dir = tempfile::tempdir().unwrap();
            let manifest = write_rows(dir.path(), &rows);
            assert!(check_rows(dir.path(), &manifest, 2)
                .unwrap_err()
                .contains("row drift"));
        }
        let dir = tempfile::tempdir().unwrap();
        let mut row = failed(0);
        row.outcome = FileOutcome::Pass;
        let manifest = write_rows(dir.path(), &[row]);
        assert!(check_rows(dir.path(), &manifest, 1)
            .unwrap_err()
            .contains("forged"));
        let dir = tempfile::tempdir().unwrap();
        let mut row = failed(0);
        row.queries[0].prefix_sha256 = "0".repeat(64);
        let manifest = write_rows(dir.path(), &[row]);
        assert!(check_rows(dir.path(), &manifest, 1)
            .unwrap_err()
            .contains("query identity"));
    }

    #[test]
    fn rehashed_missing_and_trailing_rows_still_fail_population_closure() {
        for missing in [true, false] {
            let dir = tempfile::tempdir().unwrap();
            let mut manifest = write_rows(dir.path(), &[failed(0), failed(1)]);
            let path = dir.path().join("records.jsonl");
            let mut bytes = fs::read(&path).unwrap();
            if missing {
                let previous = bytes[..bytes.len() - 1]
                    .iter()
                    .rposition(|b| *b == b'\n')
                    .unwrap();
                bytes.truncate(previous + 1);
            } else {
                bytes.extend_from_slice(b"{}\n");
            }
            fs::write(&path, &bytes).unwrap();
            manifest.bytes = bytes.len() as u64;
            manifest.artifact.sha256 = sha256_bytes(&bytes);
            assert!(check_rows(dir.path(), &manifest, 2).is_err());
        }
    }

    #[test]
    fn stream_refuses_changed_bytes_campaign_and_semantic_commitment() {
        let dir = tempfile::tempdir().unwrap();
        let mut manifest = write_rows(dir.path(), &[failed(0)]);
        let mut foreign = header(1);
        foreign.campaign = "another-campaign".into();
        assert!(visit(&manifest, dir.path(), &foreign, |_, _| Ok(())).is_err());
        manifest.semantic_sha256 = "0".repeat(64);
        assert!(check_rows(dir.path(), &manifest, 1)
            .unwrap_err()
            .contains("digest"));
        let path = dir.path().join("records.jsonl");
        let bytes = fs::read(&path).unwrap();
        let changed = String::from_utf8(bytes)
            .unwrap()
            .replace("retained AY failure", "replaced AY failure");
        fs::write(&path, changed.as_bytes()).unwrap();
        manifest.bytes = changed.len() as u64;
        assert!(visit(&manifest, dir.path(), &header(1), |_, _| Ok(()))
            .unwrap_err()
            .contains("digest"));
    }

    #[test]
    #[expect(
        clippy::naive_bytecount,
        reason = "the tiny bounded framing fixture asserts its exact newline count"
    )]
    fn incomplete_execution_keeps_durable_rows_without_claiming_completion() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("records.jsonl");
        let mut writer = Writer::create(&path, "records.jsonl".into(), &header(2)).unwrap();
        writer.append(&failed(0)).unwrap();
        // Another descriptor observes both committed lines before drop/finish.
        let bytes = fs::read(&path).unwrap();
        assert_eq!(bytes.iter().filter(|b| **b == b'\n').count(), 2);
        assert!(writer.finish().is_err());
        assert!(Writer::create(&path, "records.jsonl".into(), &header(2)).is_err());
        assert_eq!(fs::read(&path).unwrap(), bytes);
    }

    #[test]
    fn row_framing_rejects_overflow_and_partial_final_line() {
        assert!(encoded_line(&"a".repeat(64), 32).is_err());
        assert!(read_line(&mut std::io::Cursor::new(vec![b'x'; 64]), 32).is_err());
        assert!(read_line(&mut std::io::Cursor::new(b"{}"), 32).is_err());
    }

    #[test]
    fn semantic_commitment_ignores_clock_noise_but_binds_query_identity() {
        let row = failed(0);
        let mut first = Sha256::new();
        update_semantic(&mut first, &row).unwrap();
        let first = first.finalize();
        let mut timing = row.clone();
        timing.ay.observed_ns += 100;
        let mut second = Sha256::new();
        update_semantic(&mut second, &timing).unwrap();
        assert_eq!(first, second.finalize());
        timing.queries[0].prefix_sha256 = "0".repeat(64);
        let mut third = Sha256::new();
        update_semantic(&mut third, &timing).unwrap();
        assert_ne!(first, third.finalize());
    }
}
