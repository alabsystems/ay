// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A durable, ordered corpus stream. Only one bounded row is serialized or
//! decoded at a time. The final manifest commits to the entire byte stream,
//! including its campaign header, row order, and terminating newlines.

use super::*;
use sha2::Digest as _;
use std::io::{BufRead, BufReader, BufWriter, Read, Write};

// A query may retain four 1-MiB capture streams (producer/checker stdout/stderr),
// whose JSON escaping can expand sixfold, plus identities and classifications.
// SAT and UNSAT transcript sets are mutually exclusive. This leaves headroom
// for metadata while bounding parser allocation independently of corpus size.
const MAX_ROW_BYTES: u64 = 32 * 1024 * 1024;
const MAX_HEADER_BYTES: u64 = 64 * 1024;
const SCHEMA: &str = "ay-official-corpus-record-stream/v1";

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
}

impl Header {
    pub(super) fn new(results: &CorpusRunResults, rows: usize) -> Self {
        Self {
            schema: SCHEMA.to_string(),
            campaign: results.campaign_id.clone(),
            profile: results.profile_sha256.clone(),
            inventory: results.inventory_sha256.clone(),
            corpus: results.corpus_manifest_sha256.clone(),
            selection: results.corpus_selection_sha256.clone(),
            ay: results.ay_sha256.clone(),
            z3: results.z3_sha256.clone(),
            envelope: results.resource_envelope.clone(),
            rows,
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
        let file = fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(path)
            .map_err(|error| format!("create corpus record stream {}: {error}", path.display()))?;
        let mut result = Self {
            writer: BufWriter::new(file),
            relative,
            digest: Sha256::new(),
            semantic: Sha256::new(),
            bytes: 0,
            rows: 0,
            expected_rows: header.rows,
        };
        result.append_bytes(&encoded_line(header, MAX_HEADER_BYTES)?)?;
        let parent = path
            .parent()
            .filter(|path| !path.as_os_str().is_empty())
            .unwrap_or_else(|| Path::new("."));
        fs::File::open(parent)
            .and_then(|directory| directory.sync_all())
            .map_err(|error| format!("persist corpus record directory: {error}"))?;
        Ok(result)
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

fn read_line(reader: &mut impl BufRead, limit: u64) -> Result<Vec<u8>, String> {
    let mut line = Vec::new();
    reader
        .take(limit + 1)
        .read_until(b'\n', &mut line)
        .map_err(|error| error.to_string())?;
    if line.len() as u64 > limit {
        return Err("corpus record exceeds its byte bound".into());
    }
    if line.last() != Some(&b'\n') {
        return Err("missing or truncated corpus record".into());
    }
    Ok(line)
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
        }
    }

    fn file(index: usize) -> CorpusFile {
        let input = b"(check-sat)";
        CorpusFile {
            path: format!("QF_UF/{index}.smt2"),
            size: input.len() as u64,
            sha256: sha256_bytes(input),
            queries: scan_queries(input).unwrap(),
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
