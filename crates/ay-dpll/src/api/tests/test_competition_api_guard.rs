// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #proof-capability B3 — native-API guard against raw competition admissions.
//!
//! The competition-shedding `CompetitionRaw` UNSAT token is scope-authenticated
//! but backed by no checked refutation, so it deliberately carries ZERO
//! verification classes. Two invariants keep it away from the native API:
//!
//! 1. `VerifiedSolveResult::certified_unsat` must never mint a certified
//!    wrapper from a zero-class token — it fails closed to the non-verified
//!    `Unknown` classification instead of panicking the debug build on its
//!    exactly-one-class assertion.
//! 2. The native `api::Solver` surface has no competition setter at all, so
//!    the executor a native solve drives can never shed and the arm stays
//!    unreachable. A source census pins that absence: any future competition
//!    exposure under `src/api/` fails the census and forces a re-vet of the
//!    boundary (including replacing the under-claiming defensive arm with a
//!    real publication decision).

use std::fs;
use std::path::{Path, PathBuf};

use crate::api::{SolveResult, VerifiedSolveResult};
use crate::executor::Executor;

/// Invariant 1: a real shed-mode `CompetitionRaw` token reaching the native
/// result boundary yields the non-verified classification — never a certified
/// UNSAT wrapper, and never a debug-build panic.
#[test]
fn competition_raw_token_never_mints_certified_wrapper_on_native_api() {
    let mut executor = Executor::new();
    executor.set_competition_mode(true);
    let proposition = executor
        .ctx
        .terms
        .mk_var("native_api_guard_p", ay_core::Sort::Bool);
    let not_proposition = executor.ctx.terms.mk_not_raw(proposition);
    executor.ctx.assertions = vec![proposition, not_proposition];
    executor.begin_public_solve(false);
    executor.bind_unsat_query_assumptions(&[]);
    let proposed = executor
        .check_sat()
        .expect("contradictory Boolean units must solve");
    assert!(proposed.is_unsat());
    assert!(executor.competition_shedding_active());

    let published = executor.certify_unsat_for_publication(proposed, &[]);
    let SolveResult::Unsat(proof) = published else {
        panic!("shed-mode UNSAT must publish through the raw admission lane");
    };
    let certificate = executor
        .take_unsat_certificate()
        .expect("the raw token must be consumable while shedding is active");
    assert!(!certificate.strict_proof_verified());
    assert!(!certificate.independently_verified());
    assert!(!certificate.exact_semantic_verified());

    // The zero-class token crosses the native constructor: fail closed.
    let wrapped = VerifiedSolveResult::certified_unsat(proof, certificate);
    assert!(
        wrapped.is_unknown(),
        "a raw admission must yield the non-verified classification, got {wrapped}"
    );
    assert!(!wrapped.is_unsat());
    assert!(!wrapped.has_unsat_emission_witness());
    assert!(!wrapped.has_sat_emission_witness());
    assert!(!wrapped.was_model_validated());
    assert!(!wrapped.was_unsat_strictly_verified());
    assert!(!wrapped.was_unsat_independently_verified());
    assert!(!wrapped.was_unsat_exact_semantically_verified());
}

/// Walk `dir`, collecting production `.rs` sources: skip `*_tests.rs` files
/// and any `tests`/`*_tests` directory component (cfg(test)-only modules),
/// matching the B2 proof-gate census walker.
fn production_sources(dir: &Path, out: &mut Vec<PathBuf>) {
    let entries = fs::read_dir(dir).unwrap_or_else(|e| panic!("read_dir {}: {e}", dir.display()));
    for entry in entries {
        let entry = entry.expect("dir entry");
        let path = entry.path();
        if path.is_dir() {
            if path.file_name().is_some_and(|name| {
                name == "tests" || name.to_str().is_some_and(|name| name.ends_with("_tests"))
            }) {
                continue;
            }
            production_sources(&path, out);
        } else if path.extension().is_some_and(|e| e == "rs")
            && !path
                .file_name()
                .and_then(|n| n.to_str())
                .is_some_and(|n| n.ends_with("_tests.rs"))
        {
            out.push(path);
        }
    }
}

/// Invariant 2: the native API surface has no competition exposure.
///
/// Counts case-insensitive `competition` tokens in the CODE (line comments
/// stripped, so the invariant doc on `certified_unsat` does not count) of
/// every production source under `src/api/`. The count must be ZERO: the
/// native `api::Solver` has no competition setter, no re-export of
/// `Executor::set_competition_mode`, and no competition-conditional routing.
/// If this census fails, competition mode is being exposed on the native API
/// boundary: re-vet `VerifiedSolveResult::certified_unsat` (its zero-class
/// defensive arm under-claims to `Unknown`) before admitting the new surface.
#[test]
fn native_api_surface_has_no_competition_exposure() {
    let api_src = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("src")
        .join("api");
    let mut files = Vec::new();
    production_sources(&api_src, &mut files);
    files.sort();
    assert!(
        files.len() > 50,
        "census walked only {} files — the api source layout moved; fix the \
         walker, do not weaken the census",
        files.len()
    );

    let mut offenders = Vec::new();
    for path in &files {
        let text =
            fs::read_to_string(path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
        for (idx, line) in text.lines().enumerate() {
            let code = match line.find("//") {
                Some(comment) => &line[..comment],
                None => line,
            };
            if code.to_ascii_lowercase().contains("competition") {
                offenders.push(format!("{}:{}: {}", path.display(), idx + 1, line.trim()));
            }
        }
    }
    assert!(
        offenders.is_empty(),
        "competition exposure appeared on the native API surface \
         (#proof-capability B3). A CompetitionRaw token carries zero \
         verification classes and must never mint a certified wrapper; the \
         zero-class arm in VerifiedSolveResult::certified_unsat under-claims \
         to Unknown and was written for an unreachable path — re-vet the \
         boundary before exposing competition mode here.\n{}",
        offenders.join("\n")
    );
}
