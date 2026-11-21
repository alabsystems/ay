// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

fn sha256_digest(bytes: &[u8]) -> Sha256Digest {
    Sha256::digest(bytes).into()
}

/// Inputs at least this long that the XOR route would refuse are parsed
/// straight from the file (AY-SAT-1).
const STREAM_DIMACS_MIN_BYTES: u64 = 64 << 20;

/// Longest leading comment block the pre-scan reads to find the header.
const STREAM_DIMACS_HEADER_PREFIX_MAX: usize = 1 << 20;

/// What [`prescan_large_dimacs`] decided.
enum LargeDimacsPrescan {
    /// Read the whole file into memory, as for every small input.
    InMemory,
    /// Parse from the file; the whole-buffer facts were gathered line by line.
    Stream {
        sha256: Sha256Digest,
        max_var: usize,
    },
}

enum LargeDimacsPrescanError {
    Io(io::Error),
    Utf8(std::str::Utf8Error),
}

/// Decide whether `path` is parsed from the file, and if so gather, in one
/// pass, the SHA-256 of its bytes, their UTF-8 validity and the largest
/// variable [`scan_max_variable`] would report on the whole buffer.
///
/// Streams only when the file is at least [`STREAM_DIMACS_MIN_BYTES`] long and
/// its header declares more clauses than the XOR route accepts (the route
/// needs the whole text); `--xor-allow-large`, a header not found within
/// [`STREAM_DIMACS_HEADER_PREFIX_MAX`] bytes, or a small header keep the
/// in-memory path. Lines are split at `\n`, which no multi-byte UTF-8
/// sequence contains, and `scan_max_variable` restarts its state at every
/// newline, so checking and scanning each line equals doing it on the whole.
///
/// `min_bytes` is [`STREAM_DIMACS_MIN_BYTES`] in production; tests pass a
/// smaller one to drive the route on a small file.
fn prescan_large_dimacs(
    path: &Path,
    min_bytes: u64,
) -> Result<LargeDimacsPrescan, LargeDimacsPrescanError> {
    let file = open_dimacs_regular_file(path).map_err(LargeDimacsPrescanError::Io)?;
    let len = file.metadata().map_err(LargeDimacsPrescanError::Io)?.len();
    if len < min_bytes || ay_core::misc_cli_flags().xor_allow_large {
        return Ok(LargeDimacsPrescan::InMemory);
    }
    let reader = io::BufReader::with_capacity(1 << 20, file);
    Ok(match prescan_dimacs_lines(reader)? {
        Some((sha256, max_var)) => LargeDimacsPrescan::Stream { sha256, max_var },
        None => LargeDimacsPrescan::InMemory,
    })
}

/// The pass of [`prescan_large_dimacs`] over `reader`: `None` when the
/// header keeps the input in memory, else its SHA-256 and maximum variable.
fn prescan_dimacs_lines<B: io::BufRead>(
    mut reader: B,
) -> Result<Option<(Sha256Digest, usize)>, LargeDimacsPrescanError> {
    let mut hasher = Sha256::new();
    let mut line = Vec::new();
    let mut header_prefix = Vec::new();
    let mut header_decided = false;
    let mut max_var = 0usize;
    let mut max_var_done = false;
    loop {
        line.clear();
        let n = reader
            .read_until(b'\n', &mut line)
            .map_err(LargeDimacsPrescanError::Io)?;
        if n == 0 {
            break;
        }
        std::str::from_utf8(&line).map_err(LargeDimacsPrescanError::Utf8)?;
        hasher.update(&line);
        if !header_decided {
            header_prefix.extend_from_slice(&line);
            let trimmed = String::from_utf8_lossy(&line);
            let trimmed = trimmed.trim();
            let comment = trimmed.is_empty() || trimmed.starts_with('c');
            if !comment || header_prefix.len() > STREAM_DIMACS_HEADER_PREFIX_MAX {
                header_decided = true;
                let header = std::str::from_utf8(&header_prefix)
                    .ok()
                    .and_then(scan_dimacs_header);
                match header {
                    Some((_, clauses)) if clauses > XOR_EXTENSION_MAX_CLAUSES => {
                        header_prefix = Vec::new();
                    }
                    _ => return Ok(None),
                }
            }
        }
        if !max_var_done {
            let first = line
                .iter()
                .find(|&&byte| !matches!(byte, b' ' | b'\t' | b'\r' | b'\n'));
            if first == Some(&b'%') {
                max_var_done = true;
            } else {
                max_var = max_var.max(scan_max_variable(&line));
            }
        }
    }
    if !header_decided {
        return Ok(None);
    }
    Ok(Some((hasher.finalize().into(), max_var)))
}

/// A reader that hashes what it passes on and, at end of input, fails with
/// `InvalidData` unless the bytes match the pre-scan's SHA-256: a file that
/// changed between the pre-scan and the parse ends the run with a parse
/// error (`s UNKNOWN`), never a solve of different bytes (AY-SAT-1).
struct Sha256CheckingReader<R> {
    inner: R,
    hasher: Sha256,
    expected: Sha256Digest,
    checked: bool,
}

impl<R> Sha256CheckingReader<R> {
    fn new(inner: R, expected: Sha256Digest) -> Self {
        Self {
            inner,
            hasher: Sha256::new(),
            expected,
            checked: false,
        }
    }
}

impl<R: Read> Read for Sha256CheckingReader<R> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let n = self.inner.read(buf)?;
        if n > 0 {
            self.hasher.update(&buf[..n]);
        } else if !buf.is_empty() && !self.checked {
            self.checked = true;
            let digest: Sha256Digest = std::mem::take(&mut self.hasher).finalize().into();
            if digest != self.expected {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "DIMACS input changed between its pre-scan and its parse",
                ));
            }
        }
        Ok(n)
    }
}

/// The large-file route's reader: the file again, through the check that its
/// bytes are the pre-scanned ones.
fn open_streamed_dimacs(
    path: &Path,
    sha256: Sha256Digest,
) -> io::Result<io::BufReader<Sha256CheckingReader<File>>> {
    let file = open_dimacs_regular_file(path)?;
    Ok(io::BufReader::with_capacity(
        1 << 20,
        Sha256CheckingReader::new(file, sha256),
    ))
}

/// Read what the parser left (it stops at a `%` line) through the SHA-256
/// check, so every byte of the file is checked before anything is solved.
fn drain_streamed_dimacs<R: Read>(mut reader: R) -> io::Result<()> {
    io::copy(&mut reader, &mut io::sink()).map(drop)
}

fn read_authenticated_dimacs_source(
    path: &str,
    expected_sha256: Sha256Digest,
) -> io::Result<String> {
    let mut file = open_dimacs_regular_file(Path::new(path))?;
    let before = file.metadata()?;
    if !before.is_file() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("DIMACS source '{path}' is not a regular file"),
        ));
    }
    let identity_before = ProofFileIdentity::from_file(&file)?;
    let mut bytes = Vec::new();
    file.read_to_end(&mut bytes)?;
    let after = file.metadata()?;
    if ProofFileIdentity::from_file(&file)? != identity_before
        || before.len() != after.len()
        || bytes.len() as u64 != before.len()
    {
        return Err(io::Error::other(format!(
            "DIMACS source '{path}' changed while it was read"
        )));
    }
    if sha256_digest(&bytes) != expected_sha256 {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("DIMACS source '{path}' no longer matches the input that was parsed"),
        ));
    }
    String::from_utf8(bytes).map_err(|error| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            format!("DIMACS source '{path}' is not valid UTF-8/ASCII: {error}"),
        )
    })
}

fn reject_proof_input_alias(input_path: &str, proof_path: &str) -> io::Result<()> {
    let input = std::fs::canonicalize(input_path)?;
    let output = resolved_dimacs_proof_path(proof_path)?;
    if input == output {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "DIMACS proof output aliases the input problem",
        ));
    }
    #[cfg(unix)]
    if let Ok(output_metadata) = std::fs::metadata(&output) {
        use std::os::unix::fs::MetadataExt as _;
        let input_metadata = std::fs::metadata(&input)?;
        if output_metadata.dev() == input_metadata.dev()
            && output_metadata.ino() == input_metadata.ino()
        {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "DIMACS proof output hard-links the input problem",
            ));
        }
    }
    Ok(())
}

#[derive(Clone, Copy)]
enum DimacsInputSource<'a> {
    Content(&'a str),
    FilePath { path: &'a str, sha256: Sha256Digest },
    Unavailable,
}

impl<'a> DimacsInputSource<'a> {
    fn proof_artifact_problem(self) -> ProofArtifactProblem<'a> {
        match self {
            Self::Content(content) => ProofArtifactProblem::Text(content),
            Self::FilePath { path, sha256 } => {
                ProofArtifactProblem::AuthenticatedFilePath { path, sha256 }
            }
            Self::Unavailable => ProofArtifactProblem::Unavailable("DIMACS stream"),
        }
    }
}

#[derive(Clone, Debug)]
struct GuardCoverSidecarRunStats {
    path: String,
    accepted: bool,
    cuts: u64,
    guards: u64,
    budget_rhs: u64,
    packed_deficit: u64,
    injected_empty_cut: bool,
}

impl GuardCoverSidecarRunStats {
    fn accepted(path: &Path, evidence: GuardCoverPackingEvidence) -> Self {
        Self {
            path: path.display().to_string(),
            accepted: true,
            cuts: evidence.cuts as u64,
            guards: evidence.guards as u64,
            budget_rhs: evidence.budget_rhs,
            packed_deficit: evidence.packed_deficit,
            injected_empty_cut: false,
        }
    }

    fn rejected(path: &Path) -> Self {
        Self {
            path: path.display().to_string(),
            accepted: false,
            cuts: 0,
            guards: 0,
            budget_rhs: 0,
            packed_deficit: 0,
            injected_empty_cut: false,
        }
    }

    fn status_label(&self) -> &'static str {
        if self.accepted {
            "accepted"
        } else {
            "rejected"
        }
    }
}

#[derive(Clone, Debug)]
struct SeparatorCoverSidecarRunStats {
    path: String,
    accepted: bool,
    separator_vars: u64,
    cubes: u64,
    covered_assignments: u64,
    injected_empty_cut: bool,
}

impl SeparatorCoverSidecarRunStats {
    fn accepted(path: &Path, evidence: SeparatorCoverEvidence) -> Self {
        Self {
            path: path.display().to_string(),
            accepted: true,
            separator_vars: evidence.separator_vars as u64,
            cubes: evidence.cubes as u64,
            covered_assignments: evidence.covered_assignments,
            injected_empty_cut: false,
        }
    }

    fn rejected(path: &Path) -> Self {
        Self {
            path: path.display().to_string(),
            accepted: false,
            separator_vars: 0,
            cubes: 0,
            covered_assignments: 0,
            injected_empty_cut: false,
        }
    }

    fn status_label(&self) -> &'static str {
        if self.accepted {
            "accepted"
        } else {
            "rejected"
        }
    }
}

fn reject_dimacs_decision_trace_or_exit() {
    let Some(path) = ay_core::trace_config().decision_trace_path.as_deref() else {
        return;
    };
    if let Err(error) = ay_sat::invalidate_reserved_decision_trace(path) {
        safe_eprintln!(
            "Error: --decision-trace is incompatible with DIMACS solving, and its reserved output could not be invalidated: {error}"
        );
        std::process::exit(1);
    }
    safe_eprintln!(
        "Error: --decision-trace is incompatible with DIMACS solving until every DIMACS route authenticates a terminal trace correlated with its final public verdict"
    );
    std::process::exit(1);
}

pub(crate) fn run_dimacs_proof_from_file(
    path: &str,
    stats_cfg: stats_output::StatsConfig,
    proof: &ProofConfig,
) {
    reject_dimacs_decision_trace_or_exit();
    enforce_required_dimacs_proof_gate(Some(proof));
    exit_if_circuit_multiplier22_retained_sat_model_authority_admits_file(path, stats_cfg);
    if let Err(error) = reject_proof_input_alias(path, &proof.path) {
        safe_eprintln!("Error: unsafe DIMACS proof path {}: {error}", proof.path);
        std::process::exit(1);
    }
    let separator_cover_sidecar = discover_and_check_separator_cover_sidecar_from_file(path);
    if separator_cover_sidecar
        .as_ref()
        .is_some_and(|sidecar| sidecar.accepted)
    {
        cleanup_dimacs_non_unsat_proof_paths(Some(proof));
        fail_closed_satcomp_proof_setup(
            "separator-cover sidecar accepted but proof-mode public artifact replay is not implemented",
        );
    }

    // Read the file into memory so we can size the solver by the variables that
    // ACTUALLY appear (content-driven), rather than trusting the declared header.
    // The raw bytes are O(file size) — the streaming below still avoids
    // materializing parsed clause structures.
    let canonical_input = match std::fs::canonicalize(path) {
        Ok(path) => path,
        Err(error) => {
            safe_eprintln!("Error resolving file '{path}': {error}");
            std::process::exit(1);
        }
    };
    let canonical_input_text = canonical_input.to_string_lossy().into_owned();
    // AY-SAT-1: a large input that the XOR route's header gate refuses is
    // parsed straight from the file, so its bytes are not held in memory
    // while the solver is built and loaded (1.76 GB of the 14400 MiB budget
    // on e85fb114). The pre-scan gathers what the in-memory path computes
    // from the whole buffer (SHA-256, UTF-8 validity, maximum variable).
    match prescan_large_dimacs(&canonical_input, STREAM_DIMACS_MIN_BYTES) {
        Ok(LargeDimacsPrescan::InMemory) => {}
        Ok(LargeDimacsPrescan::Stream { sha256, max_var }) => {
            let reader = match open_streamed_dimacs(&canonical_input, sha256) {
                Ok(reader) => reader,
                Err(error) => {
                    safe_eprintln!("Error reading file '{path}': {error}");
                    std::process::exit(1);
                }
            };
            run_proof_streaming_reader_body_then(
                reader,
                stats_cfg,
                selected_sat_variant(),
                proof,
                DimacsInputSource::FilePath {
                    path: &canonical_input_text,
                    sha256,
                },
                Some(max_var),
                drain_streamed_dimacs,
            );
            return;
        }
        Err(LargeDimacsPrescanError::Utf8(error)) => {
            safe_eprintln!("c Parse error: DIMACS input is not valid UTF-8/ASCII: {error}");
            safe_println!("s UNKNOWN");
            std::process::exit(1);
        }
        Err(LargeDimacsPrescanError::Io(error)) => {
            safe_eprintln!("Error reading file '{path}': {error}");
            std::process::exit(1);
        }
    }
    let bytes = match open_dimacs_regular_file(&canonical_input).and_then(|mut file| {
        let mut bytes = Vec::new();
        file.read_to_end(&mut bytes)?;
        Ok(bytes)
    }) {
        Ok(bytes) => bytes,
        Err(error) => {
            safe_eprintln!("Error reading file '{path}': {error}");
            std::process::exit(1);
        }
    };
    if let Err(error) = std::str::from_utf8(&bytes) {
        safe_eprintln!("c Parse error: DIMACS input is not valid UTF-8/ASCII: {error}");
        safe_println!("s UNKNOWN");
        std::process::exit(1);
    }
    let input_sha256 = sha256_digest(&bytes);
    let content_max_var = scan_max_variable(&bytes);
    // Task #20: XOR/GE-eligible instances route through the extension under
    // the proof surface (see try_run_xor_proof_route). The probe bails on the
    // DIMACS header's clause count BEFORE parsing anything, so on a giant it
    // materializes nothing and the giant-mode memory concern below does not
    // apply. (Eligibility is capped at 50k clauses via
    // XOR_EXTENSION_MAX_CLAUSES; before the header gate the cap was only
    // consulted after parse_dimacs + preprocess_clauses_with_stats had already
    // built two near-copies of the formula.) The UTF-8 check above makes the
    // str conversion infallible.
    if let Ok(content_str) = std::str::from_utf8(&bytes) {
        // AY-SAT-2: a near-pure XOR CNF is answered SAT from the affine
        // solution space of its XOR system, with a checked model and no
        // proof, before the XOR proof route (which declines such CNFs).
        exit_if_parity_space_model_in_content(content_str, stats_cfg, proof);
        if try_run_xor_proof_route(content_str, stats_cfg, selected_sat_variant(), proof) {
            return;
        }
    }
    // Giant-mode memory lever (B1: unconditional; the AY_AB_GIANT_MEM
    // kill-switch is deleted): hand the byte
    // buffer to the reader BY VALUE. `parse_dimacs_events` consumes the
    // reader, so the whole file buffer (3.4GB/7GB for the SC2025 giants
    // 1c21a43a/6ebe9012) is freed as soon as parsing ends, instead of staying
    // resident through watch-init + search (it was ~15-20% of peak RSS on
    // 1c21a43a). The model/proof finalize paths re-read the formula via
    // `DimacsInputSource::FilePath`, NOT this buffer, so this is a pure
    // memory-lifetime change: the parsed byte stream is identical and no
    // certificate gate is touched.
    run_proof_streaming_reader(
        io::Cursor::new(bytes),
        stats_cfg,
        selected_sat_variant(),
        proof,
        DimacsInputSource::FilePath {
            path: &canonical_input_text,
            sha256: input_sha256,
        },
        Some(content_max_var),
    );
}

pub(crate) fn run_dimacs_proof_from_reader<R>(
    reader: R,
    stats_cfg: stats_output::StatsConfig,
    proof: &ProofConfig,
) where
    R: Read,
{
    reject_dimacs_decision_trace_or_exit();
    enforce_required_dimacs_proof_gate(Some(proof));
    run_proof_streaming_reader(
        reader,
        stats_cfg,
        selected_sat_variant(),
        proof,
        DimacsInputSource::Unavailable,
        // True single-pass stream (e.g. proof replay): no pre-scan possible;
        // fall back to the header, bounded by the backstop.
        None,
    );
}

fn exit_if_circuit_multiplier22_retained_sat_model_authority_admits_file(
    path: &str,
    stats_cfg: stats_output::StatsConfig,
) {
    if !circuit_multiplier22_retained_sat_model_authority_requested() {
        return;
    }
    let Ok(bytes) = std::fs::read(path) else {
        return;
    };
    let Ok(content) = std::str::from_utf8(&bytes) else {
        return;
    };
    let Ok(formula) = parse_dimacs(content) else {
        return;
    };
    if let Some(model) = formula.circuit_multiplier22_retained_sat_model_from_env(&bytes) {
        exit_with_circuit_multiplier22_retained_sat_model(&model, stats_cfg);
    }
}

pub(crate) fn run_dimacs_from_file(
    path: &str,
    content: &str,
    stats_cfg: stats_output::StatsConfig,
    proof_config: Option<&ProofConfig>,
) {
    run_dimacs_from_content_impl(content, stats_cfg, proof_config, Some(path));
}

pub(crate) fn run_dimacs_from_content(
    content: &str,
    stats_cfg: stats_output::StatsConfig,
    proof_config: Option<&ProofConfig>,
) {
    run_dimacs_from_content_impl(content, stats_cfg, proof_config, None);
}
