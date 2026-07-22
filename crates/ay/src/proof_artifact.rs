// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Lean 4 `proof-artifact-v1` sidecar writer for emitted ay proof files.

use std::collections::BTreeMap;
#[cfg(unix)]
use std::fs::OpenOptions;
use std::fs::{self, File};
use std::io::{self, BufWriter, Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};

use serde::Serialize;
use sha2::{Digest, Sha256};

use crate::{stats_output, ProofConfig, ProofFormat};

const PROOF_ARTIFACT_VERSION: &str = "proof-artifact-v1";
const STREAM_BUFFER_SIZE: usize = 64 * 1024;

pub(crate) type DigestBytes = [u8; 32];

#[derive(Clone, Copy, Debug)]
pub(crate) enum ProofArtifactProblem<'a> {
    Text(&'a str),
    AuthenticatedFilePath { path: &'a str, sha256: DigestBytes },
    Unavailable(&'static str),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub(crate) struct ProofArtifactTheoryMetadata {
    solver_mode: String,
    logic: String,
    theories: Vec<String>,
    details: BTreeMap<String, String>,
}

impl ProofArtifactTheoryMetadata {
    pub(crate) fn dimacs_sat(num_vars: usize, num_original_clauses: usize) -> Self {
        let mut details = BTreeMap::new();
        details.insert("num_vars".to_string(), num_vars.to_string());
        details.insert(
            "num_original_clauses".to_string(),
            num_original_clauses.to_string(),
        );
        Self {
            solver_mode: "dimacs-sat".to_string(),
            logic: "DIMACS-CNF".to_string(),
            theories: vec!["sat".to_string()],
            details,
        }
    }

    pub(crate) fn smt_lib(
        logic: Option<&str>,
        formula_stats: Option<&ay_frontend::FormulaStats>,
    ) -> Self {
        let mut details = BTreeMap::new();
        let mut theories = Vec::new();

        if let Some(stats) = formula_stats {
            details.insert("commands".to_string(), stats.commands.to_string());
            details.insert("terms".to_string(), stats.terms.to_string());
            for (theory, count) in &stats.theory_usage {
                theories.push(theory.clone());
                details.insert(format!("theory.{theory}.uses"), count.to_string());
            }
            for (sort, count) in &stats.sort_distribution {
                details.insert(format!("sort.{sort}.uses"), count.to_string());
            }
        }

        if theories.is_empty() {
            theories.push("unknown".to_string());
        }

        Self {
            solver_mode: "smt-lib".to_string(),
            logic: logic.unwrap_or("SMT-LIB").to_string(),
            theories,
            details,
        }
    }

    fn metadata_strings(&self) -> BTreeMap<String, String> {
        let mut metadata = BTreeMap::new();
        metadata.insert("solver_mode".to_string(), self.solver_mode.clone());
        metadata.insert("logic".to_string(), self.logic.clone());
        metadata.insert("theories".to_string(), self.theories.join(","));
        for (key, value) in &self.details {
            metadata.insert(format!("theory_metadata.{key}"), value.clone());
        }
        metadata
    }
}

/// Publish an SMT proof artifact whose expected digest was captured while AY
/// still owned the proof writer. This prevents a pathname replacement between
/// proof publication and envelope generation from being attributed to AY.
pub(crate) fn write_sealed_proof_artifact(
    problem: ProofArtifactProblem<'_>,
    proof_config: &ProofConfig,
    theory: ProofArtifactTheoryMetadata,
    expected_proof_digest: DigestBytes,
) -> io::Result<Option<(File, PathBuf)>> {
    let Some(path) = proof_config.artifact_path.as_deref() else {
        return Ok(None);
    };
    write_proof_artifact_with_digest(path, problem, proof_config, theory, expected_proof_digest)
        .map(Some)
}

fn write_proof_artifact_with_digest(
    artifact_path: &str,
    problem: ProofArtifactProblem<'_>,
    proof_config: &ProofConfig,
    theory: ProofArtifactTheoryMetadata,
    expected_proof_digest: DigestBytes,
) -> io::Result<(File, PathBuf)> {
    let target = canonical_publish_target(Path::new(artifact_path))?;
    ensure_output_does_not_alias_source(&target, Path::new(&proof_config.path), "proof")?;
    match problem {
        ProofArtifactProblem::AuthenticatedFilePath { path, .. } => {
            ensure_output_does_not_alias_source(&target, Path::new(path), "problem")?;
        }
        ProofArtifactProblem::Text(_) | ProofArtifactProblem::Unavailable(_) => {}
    }
    reject_existing_target(&target)?;

    let (mut problem, input_source, input_digest) = prepare_problem(problem)?;
    let mut proof_file = open_regular_file(Path::new(&proof_config.path), "proof")?;
    let proof_scan = scan_file(&mut proof_file, !proof_config.binary)?;
    if proof_scan.digest != expected_proof_digest {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "proof source no longer matches the proof bytes sealed by this run",
        ));
    }

    let input_hash = digest_prefixed(&input_digest);
    let proof_hash = digest_prefixed(&proof_scan.digest);
    let proof_format = proof_format_name(proof_config.format);
    let proof_encoding = if proof_config.binary {
        "binary"
    } else {
        "text"
    };
    let payload_is_hex = proof_config.binary || !proof_scan.utf8_valid;

    let mut metadata = theory.metadata_strings();
    metadata.insert("input_hash".to_string(), input_hash.clone());
    metadata.insert("input_source".to_string(), input_source);
    metadata.insert("proof_format".to_string(), proof_format.to_string());
    metadata.insert("proof_encoding".to_string(), proof_encoding.to_string());
    metadata.insert("proof_path".to_string(), proof_config.path.clone());
    metadata.insert(
        "model_hash_role".to_string(),
        "same_as_problem_hash_for_ay_solver_input".to_string(),
    );

    let file = crate::run::write_artifact_noreplace_retained(&target, |file| {
        let mut writer = BufWriter::with_capacity(STREAM_BUFFER_SIZE, file);
        write_artifact_json(
            &mut writer,
            &mut problem,
            input_digest,
            &mut proof_file,
            proof_scan.digest,
            payload_is_hex,
            &input_hash,
            &proof_hash,
            proof_format,
            proof_encoding,
            &theory,
            &metadata,
        )?;
        writer.flush()
    })?;
    Ok((file, target))
}

enum PreparedProblem<'a> {
    Text(&'a str),
    File(File),
}

fn prepare_problem(
    problem: ProofArtifactProblem<'_>,
) -> io::Result<(PreparedProblem<'_>, String, DigestBytes)> {
    match problem {
        ProofArtifactProblem::Text(text) => Ok((
            PreparedProblem::Text(text),
            "inline".to_string(),
            sha256_digest(text.as_bytes()),
        )),
        ProofArtifactProblem::AuthenticatedFilePath { path, sha256 } => {
            let mut file = open_regular_file(Path::new(path), "problem")?;
            let scan = scan_file(&mut file, true)?;
            if !scan.utf8_valid {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!("problem source '{path}' is not valid UTF-8"),
                ));
            }
            if scan.digest != sha256 {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!(
                        "problem source '{path}' no longer matches the bytes parsed by the solver"
                    ),
                ));
            }
            Ok((PreparedProblem::File(file), path.to_string(), scan.digest))
        }
        ProofArtifactProblem::Unavailable(reason) => Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("input bytes unavailable for proof-artifact-v1 envelope: {reason}"),
        )),
    }
}

fn open_regular_file(path: &Path, role: &str) -> io::Result<File> {
    #[cfg(unix)]
    let file = {
        use std::os::unix::fs::OpenOptionsExt;

        // Opening a FIFO for reads normally waits forever for a writer. Open
        // nonblocking first, then reject every non-regular descriptor by
        // `fstat` below. `O_NONBLOCK` has no effect on regular-file reads.
        OpenOptions::new()
            .read(true)
            .custom_flags(nix::libc::O_NOFOLLOW | nix::libc::O_NONBLOCK)
            .open(path)?
    };
    #[cfg(not(unix))]
    let file = {
        let metadata = fs::symlink_metadata(path)?;
        // Portable Rust has no common O_NOFOLLOW equivalent. Reject links
        // before opening so an ordinary symlink to a FIFO/device is never
        // deliberately followed; the descriptor metadata check below catches
        // a non-regular replacement in the remaining metadata/open race.
        if !metadata.file_type().is_file() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("{role} source '{}' is not a regular file", path.display()),
            ));
        }
        File::open(path)?
    };
    if !file.metadata()?.is_file() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("{role} source '{}' is not a regular file", path.display()),
        ));
    }
    Ok(file)
}

fn canonical_publish_target(target: &Path) -> io::Result<PathBuf> {
    let file_name = target.file_name().ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidInput,
            "proof artifact target must name a file",
        )
    })?;
    let parent = target
        .parent()
        .filter(|path| !path.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."));
    Ok(fs::canonicalize(parent)?.join(file_name))
}

fn reject_existing_target(target: &Path) -> io::Result<()> {
    match fs::symlink_metadata(target) {
        Ok(_) => Err(io::Error::new(
            io::ErrorKind::AlreadyExists,
            format!(
                "refusing to replace pre-existing proof artifact target '{}'",
                target.display()
            ),
        )),
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(error),
    }
}

fn ensure_output_does_not_alias_source(target: &Path, source: &Path, role: &str) -> io::Result<()> {
    let source_canonical = fs::canonicalize(source)?;
    let target_canonical = match fs::canonicalize(target) {
        Ok(path) => Some(path),
        Err(error) if error.kind() == io::ErrorKind::NotFound => None,
        Err(error) => return Err(error),
    };
    let same_canonical_path = target == source_canonical
        || target_canonical
            .as_ref()
            .is_some_and(|path| path == &source_canonical);
    if same_canonical_path || existing_files_share_identity(target, source)? {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!(
                "proof artifact target '{}' aliases the {role} source '{}'",
                target.display(),
                source.display()
            ),
        ));
    }
    Ok(())
}

#[cfg(unix)]
fn existing_files_share_identity(left: &Path, right: &Path) -> io::Result<bool> {
    use std::os::unix::fs::MetadataExt;

    let left = match fs::metadata(left) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(false),
        Err(error) => return Err(error),
    };
    let right = fs::metadata(right)?;
    Ok(left.dev() == right.dev() && left.ino() == right.ino())
}

#[cfg(not(unix))]
fn existing_files_share_identity(_left: &Path, _right: &Path) -> io::Result<bool> {
    Ok(false)
}

#[allow(clippy::too_many_arguments)]
fn write_artifact_json<W: Write>(
    writer: &mut W,
    problem: &mut PreparedProblem<'_>,
    problem_digest: DigestBytes,
    proof_file: &mut File,
    proof_digest: DigestBytes,
    proof_is_hex: bool,
    problem_hash: &str,
    proof_hash: &str,
    proof_format: &str,
    proof_encoding: &str,
    theory: &ProofArtifactTheoryMetadata,
    metadata: &BTreeMap<String, String>,
) -> io::Result<()> {
    writer.write_all(b"{\n  \"version\": ")?;
    write_json_value(writer, PROOF_ARTIFACT_VERSION)?;
    writer.write_all(b",\n  \"producer\": {\n    \"repo\": ")?;
    write_json_value(writer, env!("CARGO_PKG_REPOSITORY"))?;
    writer.write_all(b",\n    \"commit\": ")?;
    write_json_value(writer, stats_output::BUILD_PROVENANCE.commit)?;
    writer.write_all(b",\n    \"name\": \"ay\",\n    \"version\": ")?;
    write_json_value(writer, stats_output::BUILD_PROVENANCE.version)?;
    writer.write_all(b"\n  },\n  \"source_system\": \"ay\",\n  \"problem_hash\": ")?;
    write_json_value(writer, problem_hash)?;
    writer.write_all(b",\n  \"model_hash\": ")?;
    write_json_value(writer, problem_hash)?;
    writer.write_all(b",\n  \"proof_hash\": ")?;
    write_json_value(writer, proof_hash)?;
    writer.write_all(
        b",\n  \"artifact_kind\": \"ay_proof_artifact\",\n  \"verifier_constants\": [],\n  \"certificate\": {\n    \"format\": ",
    )?;
    write_json_value(writer, &format!("ay-{proof_format}-envelope-v1"))?;
    writer.write_all(b",\n    \"encoding\": \"json\",\n    \"payload_hash\": ")?;
    write_json_value(writer, proof_hash)?;
    writer.write_all(
        b",\n    \"payload\": {\n      \"type\": \"ay_proof_certificate\",\n      \"version\": \"1.0\",\n      \"problem\": ",
    )?;
    let streamed_problem_digest = stream_problem_json_string(writer, problem)?;
    require_stable_source("problem", problem_digest, streamed_problem_digest)?;

    writer.write_all(b",\n      \"proof\": {\n        \"encoding\": ")?;
    write_json_value(writer, if proof_is_hex { "hex" } else { "text" })?;
    writer.write_all(if proof_is_hex {
        b",\n        \"hex\": "
    } else {
        b",\n        \"text\": "
    })?;
    proof_file.seek(SeekFrom::Start(0))?;
    let streamed_proof_digest = if proof_is_hex {
        stream_hex_json_string(writer, proof_file)?
    } else {
        stream_lossy_json_string(writer, proof_file)?
    };
    require_stable_source("proof", proof_digest, streamed_proof_digest)?;

    writer.write_all(b"\n      },\n      \"proof_format\": ")?;
    write_json_value(writer, proof_format)?;
    writer.write_all(b",\n      \"proof_encoding\": ")?;
    write_json_value(writer, proof_encoding)?;
    writer.write_all(b",\n      \"theory_metadata\": ")?;
    write_json_value(writer, theory)?;
    writer.write_all(b"\n    }\n  },\n  \"metadata\": ")?;
    write_json_value(writer, metadata)?;
    writer.write_all(b"\n}\n")
}

fn stream_problem_json_string<W: Write>(
    writer: &mut W,
    problem: &mut PreparedProblem<'_>,
) -> io::Result<DigestBytes> {
    match problem {
        PreparedProblem::Text(text) => {
            let mut cursor = io::Cursor::new(text.as_bytes());
            stream_lossy_json_string(writer, &mut cursor)
        }
        PreparedProblem::File(file) => {
            file.seek(SeekFrom::Start(0))?;
            stream_lossy_json_string(writer, file)
        }
    }
}

fn write_json_value<W: Write, T: Serialize + ?Sized>(writer: &mut W, value: &T) -> io::Result<()> {
    serde_json::to_writer(writer, value).map_err(io::Error::other)
}

fn require_stable_source(
    role: &str,
    expected: DigestBytes,
    streamed: DigestBytes,
) -> io::Result<()> {
    if expected == streamed {
        Ok(())
    } else {
        Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("{role} source changed while proof artifact was being written"),
        ))
    }
}

struct StreamScan {
    digest: DigestBytes,
    utf8_valid: bool,
}

fn scan_file(file: &mut File, validate_utf8: bool) -> io::Result<StreamScan> {
    file.seek(SeekFrom::Start(0))?;
    scan_reader(file, validate_utf8)
}

fn scan_reader(reader: &mut impl Read, validate_utf8: bool) -> io::Result<StreamScan> {
    let mut hasher = Sha256::new();
    let mut validator = validate_utf8.then(Utf8Validator::default);
    let mut buffer = vec![0_u8; STREAM_BUFFER_SIZE];
    loop {
        let read = reader.read(&mut buffer)?;
        if read == 0 {
            break;
        }
        let chunk = &buffer[..read];
        hasher.update(chunk);
        if let Some(validator) = validator.as_mut() {
            validator.feed(chunk);
        }
    }
    let utf8_valid = validator.is_none_or(Utf8Validator::finish);
    Ok(StreamScan {
        digest: hasher.finalize().into(),
        utf8_valid,
    })
}

#[derive(Default)]
struct Utf8Validator {
    pending: Vec<u8>,
    invalid: bool,
}

impl Utf8Validator {
    fn feed(&mut self, bytes: &[u8]) {
        if self.invalid {
            return;
        }
        self.pending.extend_from_slice(bytes);
        match std::str::from_utf8(&self.pending) {
            Ok(_) => self.pending.clear(),
            Err(error) if error.error_len().is_some() => {
                self.pending.clear();
                self.invalid = true;
            }
            Err(error) => {
                let valid = error.valid_up_to();
                self.pending.drain(..valid);
            }
        }
    }

    fn finish(self) -> bool {
        !self.invalid && self.pending.is_empty()
    }
}

fn stream_lossy_json_string(
    writer: &mut impl Write,
    reader: &mut impl Read,
) -> io::Result<DigestBytes> {
    writer.write_all(b"\"")?;
    let mut hasher = Sha256::new();
    let mut buffer = vec![0_u8; STREAM_BUFFER_SIZE];
    let mut pending = Vec::with_capacity(STREAM_BUFFER_SIZE + 3);
    let mut escaped = Vec::with_capacity(STREAM_BUFFER_SIZE);
    loop {
        let read = reader.read(&mut buffer)?;
        if read == 0 {
            break;
        }
        let chunk = &buffer[..read];
        hasher.update(chunk);
        pending.extend_from_slice(chunk);
        write_lossy_pending(writer, &mut pending, false, &mut escaped)?;
    }
    write_lossy_pending(writer, &mut pending, true, &mut escaped)?;
    debug_assert!(pending.is_empty());
    writer.write_all(b"\"")?;
    Ok(hasher.finalize().into())
}

fn write_lossy_pending(
    writer: &mut impl Write,
    pending: &mut Vec<u8>,
    eof: bool,
    escaped: &mut Vec<u8>,
) -> io::Result<()> {
    let mut consumed = 0usize;
    while consumed < pending.len() {
        match std::str::from_utf8(&pending[consumed..]) {
            Ok(text) => {
                write_json_escaped_segment(writer, text, escaped)?;
                consumed = pending.len();
            }
            Err(error) => {
                let valid_end = consumed + error.valid_up_to();
                if valid_end > consumed {
                    let text = std::str::from_utf8(&pending[consumed..valid_end])
                        .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))?;
                    write_json_escaped_segment(writer, text, escaped)?;
                }
                consumed = valid_end;
                match error.error_len() {
                    Some(invalid_len) => {
                        write_json_escaped_segment(writer, "\u{fffd}", escaped)?;
                        consumed += invalid_len;
                    }
                    None if eof => {
                        write_json_escaped_segment(writer, "\u{fffd}", escaped)?;
                        consumed = pending.len();
                    }
                    None => break,
                }
            }
        }
    }
    if consumed > 0 {
        pending.drain(..consumed);
    }
    Ok(())
}

fn write_json_escaped_segment(
    writer: &mut impl Write,
    text: &str,
    escaped: &mut Vec<u8>,
) -> io::Result<()> {
    escaped.clear();
    for &byte in text.as_bytes() {
        match byte {
            b'"' => escaped.extend_from_slice(br#"\""#),
            b'\\' => escaped.extend_from_slice(br#"\\"#),
            b'\x08' => escaped.extend_from_slice(br"\b"),
            b'\x0c' => escaped.extend_from_slice(br"\f"),
            b'\n' => escaped.extend_from_slice(br"\n"),
            b'\r' => escaped.extend_from_slice(br"\r"),
            b'\t' => escaped.extend_from_slice(br"\t"),
            0x00..=0x1f => {
                const HEX: &[u8; 16] = b"0123456789abcdef";
                escaped.extend_from_slice(br"\u00");
                escaped.push(HEX[(byte >> 4) as usize]);
                escaped.push(HEX[(byte & 0x0f) as usize]);
            }
            _ => escaped.push(byte),
        }
    }
    writer.write_all(escaped)
}

fn stream_hex_json_string(
    writer: &mut impl Write,
    reader: &mut impl Read,
) -> io::Result<DigestBytes> {
    const HEX: &[u8; 16] = b"0123456789abcdef";

    writer.write_all(b"\"")?;
    let mut hasher = Sha256::new();
    let mut input = vec![0_u8; STREAM_BUFFER_SIZE];
    let mut output = vec![0_u8; STREAM_BUFFER_SIZE * 2];
    loop {
        let read = reader.read(&mut input)?;
        if read == 0 {
            break;
        }
        let chunk = &input[..read];
        hasher.update(chunk);
        for (index, &byte) in chunk.iter().enumerate() {
            output[index * 2] = HEX[(byte >> 4) as usize];
            output[index * 2 + 1] = HEX[(byte & 0x0f) as usize];
        }
        writer.write_all(&output[..read * 2])?;
    }
    writer.write_all(b"\"")?;
    Ok(hasher.finalize().into())
}

fn sha256_digest(bytes: &[u8]) -> DigestBytes {
    Sha256::digest(bytes).into()
}

fn digest_prefixed(digest: &DigestBytes) -> String {
    format!("sha256:{}", hex_encode(digest))
}

fn proof_format_name(format: ProofFormat) -> &'static str {
    match format {
        ProofFormat::Drat => "drat",
        ProofFormat::Lrat => "lrat",
        ProofFormat::Lean4 => "lean4",
        ProofFormat::Alethe => "alethe",
    }
}

#[cfg(test)]
fn sha256_prefixed(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    format!("sha256:{}", hex_encode(&digest))
}

fn hex_encode(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for &byte in bytes {
        out.push(HEX[(byte >> 4) as usize] as char);
        out.push(HEX[(byte & 0x0f) as usize] as char);
    }
    out
}

#[cfg(test)]
fn write_proof_artifact(
    artifact_path: &str,
    problem: ProofArtifactProblem<'_>,
    proof_config: &ProofConfig,
    theory: ProofArtifactTheoryMetadata,
) -> io::Result<()> {
    let mut proof_file = open_regular_file(Path::new(&proof_config.path), "proof")?;
    let expected = scan_file(&mut proof_file, false)?.digest;
    write_proof_artifact_with_digest(artifact_path, problem, proof_config, theory, expected)
        .map(drop)
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::Value;

    fn proof_config(proof: &Path, artifact: &Path, binary: bool) -> ProofConfig {
        ProofConfig {
            path: proof.to_string_lossy().into_owned(),
            format: ProofFormat::Alethe,
            binary,
            artifact_path: Some(artifact.to_string_lossy().into_owned()),
            is_temp: false,
            synthesized_default: false,
            format_was_explicit: false,
        }
    }

    fn read_artifact(path: &Path) -> Value {
        serde_json::from_slice(&fs::read(path).expect("read proof artifact"))
            .expect("proof artifact must be valid JSON")
    }

    struct ChunkReader<'a> {
        bytes: &'a [u8],
        position: usize,
        chunk_size: usize,
    }

    impl Read for ChunkReader<'_> {
        fn read(&mut self, output: &mut [u8]) -> io::Result<usize> {
            if self.position == self.bytes.len() {
                return Ok(0);
            }
            let count = self
                .chunk_size
                .min(output.len())
                .min(self.bytes.len() - self.position);
            output[..count].copy_from_slice(&self.bytes[self.position..self.position + count]);
            self.position += count;
            Ok(count)
        }
    }

    #[test]
    fn sha256_hashes_are_prefixed_lowercase_hex() {
        assert_eq!(
            sha256_prefixed(b"abc"),
            "sha256:ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
    }

    #[test]
    fn chunked_lossy_json_matches_whole_input_semantics_and_hash() {
        let bytes = b"before \xf0\x9f\x92\xa9 quote=\" slash=\\ bad=\xf0\x9f after=\xff";
        let mut reader = ChunkReader {
            bytes,
            position: 0,
            chunk_size: 1,
        };
        let mut rendered = Vec::new();
        let digest = stream_lossy_json_string(&mut rendered, &mut reader).expect("stream JSON");
        let decoded: String = serde_json::from_slice(&rendered).expect("decode streamed JSON");
        assert_eq!(decoded, String::from_utf8_lossy(bytes));
        assert_eq!(digest, sha256_digest(bytes));
    }

    #[test]
    fn non_utf8_problem_is_rejected_instead_of_lossily_reencoded() {
        let temp = tempfile::tempdir().expect("temporary directory");
        let problem_path = temp.path().join("problem.cnf");
        let proof_path = temp.path().join("proof.alethe");
        let artifact_path = temp.path().join("artifact.json");
        let problem = b"p cnf 1 1\n\xf0\x9f\n\xff\n";
        let proof = [0_u8, 15, 255];
        fs::write(&problem_path, problem).expect("write problem");
        fs::write(&proof_path, proof).expect("write proof");
        let config = proof_config(&proof_path, &artifact_path, false);

        let error = write_proof_artifact(
            artifact_path.to_str().expect("UTF-8 path"),
            ProofArtifactProblem::AuthenticatedFilePath {
                path: problem_path.to_str().expect("UTF-8 path"),
                sha256: sha256_digest(problem),
            },
            &config,
            ProofArtifactTheoryMetadata::dimacs_sat(1, 1),
        )
        .expect_err("invalid UTF-8 problem must not produce a lossy artifact");
        assert_eq!(error.kind(), io::ErrorKind::InvalidData);
        assert!(!artifact_path.exists());
    }

    #[test]
    fn authenticated_problem_digest_rejects_replaced_input() {
        let temp = tempfile::tempdir().expect("temporary directory");
        let problem_path = temp.path().join("problem.cnf");
        let proof_path = temp.path().join("proof.drat");
        let artifact_path = temp.path().join("artifact.json");
        let original = b"p cnf 1 1\n1 0\n";
        fs::write(&problem_path, original).expect("write problem");
        fs::write(&proof_path, b"0\n").expect("write proof");
        let config = proof_config(&proof_path, &artifact_path, false);
        fs::write(&problem_path, b"p cnf 1 1\n-1 0\n").expect("replace problem");

        let error = write_proof_artifact(
            artifact_path.to_str().expect("UTF-8 path"),
            ProofArtifactProblem::AuthenticatedFilePath {
                path: problem_path.to_str().expect("UTF-8 path"),
                sha256: sha256_digest(original),
            },
            &config,
            ProofArtifactTheoryMetadata::dimacs_sat(1, 1),
        )
        .expect_err("artifact must stay bound to the parsed problem bytes");
        assert_eq!(error.kind(), io::ErrorKind::InvalidData);
        assert!(!artifact_path.exists());
    }

    #[test]
    fn sealed_proof_digest_rejects_replaced_proof() {
        let temp = tempfile::tempdir().expect("temporary directory");
        let proof_path = temp.path().join("proof.alethe");
        let artifact_path = temp.path().join("artifact.json");
        let original = b"(step original)\n";
        fs::write(&proof_path, original).expect("write proof");
        let config = proof_config(&proof_path, &artifact_path, false);
        fs::write(&proof_path, b"(step replacement)\n").expect("replace proof");

        let error = write_proof_artifact_with_digest(
            artifact_path.to_str().expect("UTF-8 path"),
            ProofArtifactProblem::Text("(check-sat)\n"),
            &config,
            ProofArtifactTheoryMetadata::smt_lib(Some("QF_UF"), None),
            sha256_digest(original),
        )
        .expect_err("artifact must stay bound to AY's rendered proof bytes");
        assert_eq!(error.kind(), io::ErrorKind::InvalidData);
        assert!(!artifact_path.exists());
    }

    #[test]
    fn large_text_payload_round_trips_across_stream_boundaries() {
        let temp = tempfile::tempdir().expect("temporary directory");
        let proof_path = temp.path().join("proof.alethe");
        let artifact_path = temp.path().join("artifact.json");
        let problem = format!(
            "{}{}\n(assert \"quoted\\value\")\n",
            "x".repeat(STREAM_BUFFER_SIZE - 1),
            "💩"
        );
        let proof = format!(
            "{}{}{}",
            "a".repeat(STREAM_BUFFER_SIZE - 2),
            "💩",
            "\n(step \"quoted\" \\ path)".repeat(8_000)
        );
        fs::write(&proof_path, proof.as_bytes()).expect("write proof");
        let config = proof_config(&proof_path, &artifact_path, false);

        write_proof_artifact(
            artifact_path.to_str().expect("UTF-8 path"),
            ProofArtifactProblem::Text(&problem),
            &config,
            ProofArtifactTheoryMetadata::smt_lib(Some("QF_UF"), None),
        )
        .expect("write artifact");

        let artifact = read_artifact(&artifact_path);
        assert_eq!(artifact["certificate"]["payload"]["problem"], problem);
        assert_eq!(
            artifact["certificate"]["payload"]["proof"]["encoding"],
            "text"
        );
        assert_eq!(artifact["certificate"]["payload"]["proof"]["text"], proof);
        assert_eq!(
            artifact["problem_hash"],
            sha256_prefixed(problem.as_bytes())
        );
        assert_eq!(artifact["proof_hash"], sha256_prefixed(proof.as_bytes()));
    }

    #[test]
    fn artifact_target_cannot_alias_proof_source() {
        let temp = tempfile::tempdir().expect("temporary directory");
        let proof_path = temp.path().join("proof.alethe");
        fs::write(&proof_path, "proof data").expect("write proof");
        let config = proof_config(&proof_path, &proof_path, false);

        let error = write_proof_artifact(
            proof_path.to_str().expect("UTF-8 path"),
            ProofArtifactProblem::Text("problem"),
            &config,
            ProofArtifactTheoryMetadata::smt_lib(None, None),
        )
        .expect_err("artifact must not replace its proof source");
        assert!(error.to_string().contains("aliases the proof source"));
        assert_eq!(
            fs::read_to_string(proof_path).expect("read proof"),
            "proof data"
        );
    }

    #[cfg(unix)]
    #[test]
    fn fifo_source_is_rejected_without_waiting_for_a_writer() {
        use std::time::{Duration, Instant};

        let temp = tempfile::tempdir().expect("temporary directory");
        let fifo = temp.path().join("blocked.fifo");
        nix::unistd::mkfifo(
            &fifo,
            nix::sys::stat::Mode::S_IRUSR | nix::sys::stat::Mode::S_IWUSR,
        )
        .expect("create FIFO");

        let started = Instant::now();
        let error = open_regular_file(&fifo, "proof").expect_err("FIFO must be rejected");
        assert_eq!(error.kind(), io::ErrorKind::InvalidInput);
        assert!(
            started.elapsed() < Duration::from_secs(1),
            "opening a FIFO must not wait for a peer"
        );
    }

    #[cfg(unix)]
    #[test]
    fn atomic_publish_rejects_unrelated_symlink_without_touching_referent() {
        use std::os::unix::fs::symlink;

        let temp = tempfile::tempdir().expect("temporary directory");
        let proof_path = temp.path().join("proof.alethe");
        let artifact_path = temp.path().join("artifact.json");
        let victim_path = temp.path().join("victim.txt");
        fs::write(&proof_path, "proof data").expect("write proof");
        fs::write(&victim_path, "do not overwrite").expect("write victim");
        symlink(&victim_path, &artifact_path).expect("plant artifact symlink");
        let config = proof_config(&proof_path, &artifact_path, false);

        let error = write_proof_artifact(
            artifact_path.to_str().expect("UTF-8 path"),
            ProofArtifactProblem::Text("problem"),
            &config,
            ProofArtifactTheoryMetadata::smt_lib(None, None),
        )
        .expect_err("pre-existing artifact path must not be replaced");

        assert_eq!(error.kind(), io::ErrorKind::AlreadyExists);
        assert!(artifact_path.is_symlink());
        assert_eq!(
            fs::read_to_string(victim_path).expect("read victim"),
            "do not overwrite"
        );
    }
}
