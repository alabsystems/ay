// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::fs;
use std::path::{Path, PathBuf};

fn collect_rs_files(dir: &Path, out: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(dir).unwrap_or_else(|err| {
        panic!("failed to read directory {}: {err}", dir.display());
    }) {
        let entry = entry.unwrap_or_else(|err| {
            panic!("failed to read directory entry in {}: {err}", dir.display());
        });
        let path = entry.path();
        if path.is_dir() {
            collect_rs_files(&path, out);
        } else if path.extension().is_some_and(|ext| ext == "rs") {
            out.push(path);
        }
    }
}

#[test]
fn test_restart_inprocessing_has_single_scheduler_owner() {
    let solver_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("src/solver");
    let duplicate_scheduler = solver_dir.join("inprocessing/schedule.rs");
    assert!(
        !duplicate_scheduler.exists(),
        "duplicate scheduler source reintroduced at {}",
        duplicate_scheduler.display(),
    );

    let mut rs_files = Vec::new();
    collect_rs_files(&solver_dir, &mut rs_files);
    rs_files.sort();

    let mut owners = Vec::new();
    for file in rs_files {
        let source = fs::read_to_string(&file).unwrap_or_else(|err| {
            panic!("failed to read source file {}: {err}", file.display());
        });
        if source.contains("fn run_restart_inprocessing") {
            owners.push(file);
        }
    }

    let expected_owner = solver_dir.join("solve/inprocessing_schedule.rs");
    assert_eq!(
        owners,
        vec![expected_owner],
        "run_restart_inprocessing must have exactly one owner in solve/inprocessing_schedule.rs",
    );
}
