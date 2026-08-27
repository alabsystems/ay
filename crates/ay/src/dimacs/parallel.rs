// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// Run a DIMACS formula using the parallel portfolio solver.
///
/// Parses the formula, creates a `PortfolioSolver` with instance-aware strategy
/// selection, runs `num_threads` solver threads in parallel, and reports the
/// first result. This is the `--parallel N` CLI entry point.
pub(crate) fn run_dimacs_parallel(
    content: &str,
    stats_cfg: stats_output::StatsConfig,
    proof_config: Option<&ProofConfig>,
    num_threads: usize,
) {
    run_dimacs_parallel_body(content, stats_cfg, proof_config, num_threads);
}

/// Write a proof from the portfolio solver to a file (#8428).
///
/// When `raw_lrat_bytes` is available (the forward LRAT proof captured from
/// the winning solver thread's in-memory buffer), uses those bytes directly.
/// For LRAT format, writes the bytes as-is. For DRAT format, converts by
/// stripping clause IDs and hints from each LRAT line. For other formats
/// (Lean4, Alethe) or when raw bytes are unavailable, falls back to
/// materializing from the `ProofCertificate`.
fn write_parallel_proof(
    raw_lrat_bytes: Option<&[u8]>,
    cert: &ProofCertificate,
    proof_config: &ProofConfig,
    original_clauses: &[(u64, Vec<i32>)],
) {
    let file = match create_configured_dimacs_proof_file(proof_config) {
        Ok(file) => file,
        Err(error) => {
            handle_failed_proof_create(proof_config, &error);
            return;
        }
    };
    let mut writer = proof_output_writer(file);

    // Forward LRAT bytes from the winning solver thread are the complete proof
    // (including clauses derived during BCP/preprocessing). Use them directly
    // for LRAT, or convert to DRAT by stripping clause IDs and hints.
    if let Some(bytes) = raw_lrat_bytes {
        let write_result = match proof_config.format {
            ProofFormat::Lrat => writer.write_all(bytes),
            ProofFormat::Drat => lrat_bytes_to_drat(bytes, &mut writer),
            // Lean4/Alethe: fall through to cert-based materialization below
            _ => Err(io::Error::other("use cert fallback")),
        };
        if write_result.is_ok() {
            if let Err(error) = writer.flush() {
                handle_dimacs_proof_io_failure(proof_config, "flush", &error);
                return;
            }
            drop(writer);
            if let Err(error) = seal_owned_dimacs_proof(&proof_config.path) {
                handle_dimacs_proof_io_failure(proof_config, "seal", &error);
            }
            return;
        }
    }

    // Fallback: materialize from the ProofCertificate (backward reconstruction).
    let write_result = match proof_config.format {
        ProofFormat::Drat => cert.write_drat(&mut writer),
        ProofFormat::Lrat => cert.write_lrat(&mut writer),
        ProofFormat::Lean4 => {
            let lean_cert = raw_lrat_bytes
                .map(ProofCertificate::from_lrat_text)
                .transpose()
                .and_then(|parsed| {
                    parsed
                        .as_ref()
                        .unwrap_or(cert)
                        .write_lean4_verified(original_clauses, &mut writer)
                });
            lean_cert
        }
        ProofFormat::Alethe => Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "Alethe proof output is unavailable for DIMACS input; use LRAT or DRAT",
        )),
        // The portfolio fallback materializes from a ProofCertificate, which
        // has no pseudo-Boolean writer. VeriPB output is produced by the
        // streaming single-solver route, so ask for that rather than emit a
        // proof the declared checker cannot read.
        ProofFormat::Veripb => Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "VeriPB proof output is unavailable from the parallel portfolio; \
             run without --parallel, or use LRAT or DRAT",
        )),
    };
    if let Err(error) = write_result {
        handle_dimacs_proof_io_failure(proof_config, "write", &error);
        return;
    }
    if let Err(error) = writer.flush() {
        handle_dimacs_proof_io_failure(proof_config, "flush", &error);
        return;
    }
    drop(writer);
    if let Err(error) = seal_owned_dimacs_proof(&proof_config.path) {
        handle_dimacs_proof_io_failure(proof_config, "seal", &error);
    }
}

/// Convert LRAT text proof bytes to DRAT text format.
///
/// LRAT addition line format: `<id> <lits...> 0 <hints...> 0`
/// DRAT addition line format: `<lits...> 0`
///
/// LRAT deletion lines (`d <ids...> 0`) are ID-based and don't have a direct
/// DRAT equivalent (DRAT deletions are literal-based), so they are skipped.
fn lrat_bytes_to_drat(lrat_bytes: &[u8], w: &mut dyn Write) -> io::Result<()> {
    let text = String::from_utf8_lossy(lrat_bytes);
    for line in text.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        // Skip LRAT deletion lines (ID-based, no DRAT equivalent)
        if line.starts_with("d ") {
            continue;
        }
        // Addition line: "<id> <lits...> 0 <hints...> 0"
        // Strip clause ID (first token) and hints (after first "0").
        let mut tokens = line.split_whitespace();
        let _clause_id = tokens.next(); // skip clause ID
        for tok in tokens {
            if tok == "0" {
                writeln!(w, "0")?;
                break;
            }
            write!(w, "{tok} ")?;
        }
    }
    Ok(())
}

/// Run a DIMACS formula using the cube-and-conquer parallel solver.
///
/// Phase 1 (cube): generates cubes via lookahead on a temporary solver.
/// Phase 2 (conquer): dispatches cubes to CDCL worker threads that solve
/// formula AND cube using assumption-based solving.
///
/// CLI entry point: `ay --cube-and-conquer <depth> file.cnf`
pub(crate) fn run_dimacs_cube_and_conquer(
    content: &str,
    stats_cfg: stats_output::StatsConfig,
    proof_config: Option<&ProofConfig>,
    depth: usize,
    num_threads: usize,
) {
    run_dimacs_cube_and_conquer_body(content, stats_cfg, proof_config, depth, num_threads);
}
