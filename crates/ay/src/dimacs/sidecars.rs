// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

fn discover_and_check_guard_cover_sidecar(
    input_path: Option<&str>,
    cnf_bytes: &[u8],
) -> Option<GuardCoverSidecarRunStats> {
    let input_path = input_path?;
    let sidecar_path = discover_guard_cover_sidecar_path(input_path)?;
    let sidecar_text = match std::fs::read_to_string(&sidecar_path) {
        Ok(text) => text,
        Err(error) => {
            safe_eprintln!(
                "c guard-cover: rejected {}: failed to read sidecar: {error}",
                sidecar_path.display()
            );
            return Some(GuardCoverSidecarRunStats::rejected(&sidecar_path));
        }
    };

    let base_dir = sidecar_path.parent().unwrap_or_else(|| Path::new("."));
    let base_dir = match base_dir.canonicalize() {
        Ok(path) => path,
        Err(error) => {
            safe_eprintln!(
                "c guard-cover: rejected {}: failed to canonicalize sidecar directory: {error}",
                sidecar_path.display()
            );
            return Some(GuardCoverSidecarRunStats::rejected(&sidecar_path));
        }
    };

    let result = guard_cover_sidecar::check_guard_cover_packing_sidecar(
        cnf_bytes,
        &sidecar_text,
        |witness| resolve_guard_cover_hall_witness(&base_dir, witness),
    );
    match result {
        Ok(evidence) => {
            safe_eprintln!(
                "c guard-cover: accepted {} cuts={} guards={} budget_rhs={} packed_deficit={}",
                sidecar_path.display(),
                evidence.cuts,
                evidence.guards,
                evidence.budget_rhs,
                evidence.packed_deficit
            );
            Some(GuardCoverSidecarRunStats::accepted(&sidecar_path, evidence))
        }
        Err(error) => {
            safe_eprintln!(
                "c guard-cover: rejected {}: {}",
                sidecar_path.display(),
                error.detail()
            );
            Some(GuardCoverSidecarRunStats::rejected(&sidecar_path))
        }
    }
}

fn discover_guard_cover_sidecar_path(input_path: &str) -> Option<PathBuf> {
    let path = Path::new(input_path);
    let mut candidates = Vec::with_capacity(2);
    candidates.push(path.with_extension("guard-cover.json"));
    candidates.push(PathBuf::from(format!("{input_path}.guard-cover.json")));
    candidates.into_iter().find(|candidate| candidate.is_file())
}

fn discover_and_check_separator_cover_sidecar_from_file(
    input_path: &str,
) -> Option<SeparatorCoverSidecarRunStats> {
    let sidecar_path = discover_separator_cover_sidecar_path(input_path)?;
    let cnf_bytes = match std::fs::read(input_path) {
        Ok(bytes) => bytes,
        Err(error) => {
            safe_eprintln!(
                "c separator-cover: rejected {}: failed to read DIMACS input: {error}",
                sidecar_path.display()
            );
            return Some(SeparatorCoverSidecarRunStats::rejected(&sidecar_path));
        }
    };
    read_and_check_separator_cover_sidecar(&sidecar_path, &cnf_bytes)
}

fn discover_and_check_separator_cover_sidecar(
    input_path: Option<&str>,
    cnf_bytes: &[u8],
) -> Option<SeparatorCoverSidecarRunStats> {
    let input_path = input_path?;
    let sidecar_path = discover_separator_cover_sidecar_path(input_path)?;
    read_and_check_separator_cover_sidecar(&sidecar_path, cnf_bytes)
}

fn read_and_check_separator_cover_sidecar(
    sidecar_path: &Path,
    cnf_bytes: &[u8],
) -> Option<SeparatorCoverSidecarRunStats> {
    let sidecar_text = match std::fs::read_to_string(sidecar_path) {
        Ok(text) => text,
        Err(error) => {
            safe_eprintln!(
                "c separator-cover: rejected {}: failed to read sidecar: {error}",
                sidecar_path.display()
            );
            return Some(SeparatorCoverSidecarRunStats::rejected(sidecar_path));
        }
    };

    match guard_cover_sidecar::check_separator_cover_sidecar(cnf_bytes, &sidecar_text) {
        Ok(evidence) => {
            safe_eprintln!(
                "c separator-cover: accepted {} separator_vars={} cubes={} covered_assignments={}",
                sidecar_path.display(),
                evidence.separator_vars,
                evidence.cubes,
                evidence.covered_assignments
            );
            Some(SeparatorCoverSidecarRunStats::accepted(
                sidecar_path,
                evidence,
            ))
        }
        Err(error) => {
            safe_eprintln!(
                "c separator-cover: rejected {}: {}",
                sidecar_path.display(),
                error.detail()
            );
            Some(SeparatorCoverSidecarRunStats::rejected(sidecar_path))
        }
    }
}

fn discover_separator_cover_sidecar_path(input_path: &str) -> Option<PathBuf> {
    let path = Path::new(input_path);
    let mut candidates = Vec::with_capacity(2);
    candidates.push(path.with_extension("separator-cover.json"));
    candidates.push(PathBuf::from(format!("{input_path}.separator-cover.json")));
    candidates.into_iter().find(|candidate| candidate.is_file())
}

fn resolve_guard_cover_hall_witness(base_dir: &Path, witness: &str) -> Result<String, String> {
    let witness_path = Path::new(witness);
    if witness_path.is_absolute() {
        return Err("depends_on witness path must be relative".to_string());
    }
    let resolved = base_dir.join(witness_path);
    let resolved = resolved
        .canonicalize()
        .map_err(|error| format!("failed to canonicalize {witness}: {error}"))?;
    if !resolved.starts_with(base_dir) {
        return Err("depends_on witness path escapes sidecar directory".to_string());
    }
    std::fs::read_to_string(&resolved)
        .map_err(|error| format!("failed to read {}: {error}", resolved.display()))
}
