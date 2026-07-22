// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `symbols` subcommand — audits exported-symbol coverage.
//!
//! Reference set: `nm -gU <libz3>` → every exported `Z3_*` symbol. For each,
//! `dlsym` it in the AY library. AY passes iff every libz3 symbol resolves.
//! Both the reference derivation (`nm`) and the presence test (`dlsym`) are
//! done live against the two files the caller supplies — no embedded list.

use std::path::Path;

use crate::loader;

/// Run the `symbols` proof. Returns the process exit code: 0 iff every libz3
/// `Z3_*` symbol is `dlsym`-able in the AY library.
pub(crate) fn run(ay_path: &Path, z3_path: &Path, json: bool) -> i32 {
    let reference = match loader::nm_z3_symbols(z3_path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: {e}");
            return 2;
        }
    };
    let ay_nm = match loader::nm_z3_symbols(ay_path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: {e}");
            return 2;
        }
    };
    let ay_lib = match loader::open_local(ay_path) {
        Ok(l) => l,
        Err(e) => {
            eprintln!("error: {e}");
            return 2;
        }
    };

    let total = reference.len();
    let mut missing: Vec<String> = Vec::new();
    for name in &reference {
        if !loader::has_symbol(&ay_lib, name) {
            missing.push(name.clone());
        }
    }
    missing.sort();
    let covered = total - missing.len();

    // AY-only extras: symbols AY exports that are not in the libz3 reference.
    let extras: Vec<String> = ay_nm.difference(&reference).cloned().collect();

    if json {
        let cert = serde_json::json!({
            "kind": "symbol-parity",
            "z3_lib": z3_path.display().to_string(),
            "ay_lib": ay_path.display().to_string(),
            "z3_symbol_count": total,
            "ay_covers": covered,
            "missing_count": missing.len(),
            "missing": missing,
            "ay_only_count": extras.len(),
            "ay_only": extras,
            "pass": missing.is_empty(),
        });
        println!(
            "{}",
            serde_json::to_string_pretty(&cert).unwrap_or_default()
        );
    } else {
        println!("== ay-z3-parity: symbol parity ==");
        println!("  reference (nm -gU): {}", z3_path.display());
        println!("  under test (dlsym): {}", ay_path.display());
        println!();
        println!("AY covers {covered} / {total} libz3 Z3_* symbols");
        if missing.is_empty() {
            println!("  MISSING: none");
        } else {
            println!("  MISSING ({}):", missing.len());
            for m in &missing {
                println!("    - {m}");
            }
        }
        if extras.is_empty() {
            println!("  AY-only extras: none");
        } else {
            println!("  AY-only extras ({}):", extras.len());
            for e in &extras {
                println!("    + {e}");
            }
        }
        println!();
        if missing.is_empty() {
            println!("RESULT: PASS — AY is a symbol-level drop-in for libz3 (0 missing).");
        } else {
            println!(
                "RESULT: FAIL — {} libz3 symbol(s) are not dlsym-able in AY.",
                missing.len()
            );
        }
    }

    i32::from(!missing.is_empty())
}
