// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Negated-proof-gate census (#proof-capability B2, hard gate before B3).
//!
//! `begin_public_solve` arms the proof tracker for every public decision, so
//! on the certified path `produce_proofs_enabled()` is always true and every
//! `!produce_proofs_enabled()` gate is DEAD there. Competition shedding
//! (`competition_shedding_active`) disarms the tracker, which flips every
//! such gate LIVE — including refutation shortcuts that have never been
//! publicly exercised. This census reads the crate's production sources at
//! test time and fails whenever a proof-sensitive gate appears (or moves)
//! without being re-vetted here, so no future edit can silently add a lane
//! that competition shedding would switch on.
//!
//! Three inventories are kept, per production file:
//! - negated `!produce_proofs_enabled()` sites — tracker-sensitive; DEAD on
//!   the certified public path, LIVE under competition shedding. Every one
//!   must be either pure proof bookkeeping, a documented mode divergence, or
//!   a vacuous debug_assert — never an UNSAT-originating lane.
//! - negated `!is_producing_proofs()` sites — keyed to the EXPLICIT user
//!   proof demand, not the tracker; competition shedding does NOT change
//!   them. Inventoried so a tracker-sensitive gate cannot masquerade as one
//!   by a later edit swapping the predicate.
//! - `unvetted_no_proof_lane_allowed()` sites (any polarity) — the two
//!   audited dormant UNSAT-originating lanes, kept dead under shedding.
//!
//! The scan strips `//` line comments, skips `tests.rs`/`*_tests.rs` files and
//! `tests`/`*_tests` directories (cfg(test)-only modules), and matches the exact
//! zero-argument call token, so definitions (`fn ...(&self)`) and prose
//! references do not count. Known limitation: a call inside a `/* */` block
//! comment would still be counted — this crate does not use block comments
//! around these predicates, and overcounting fails safe (census mismatch).

use std::fs;
use std::path::{Path, PathBuf};

/// One vetted production file: (path relative to `src/`, negated
/// `!produce_proofs_enabled()` sites, negated `!is_producing_proofs()`
/// sites, `unvetted_no_proof_lane_allowed()` sites, vetting rationale).
///
/// TO UPDATE THIS LIST you must re-run the B2 audit for the new/changed
/// site: a NEW negated `produce_proofs_enabled` gate is live under
/// competition shedding and must be proof bookkeeping or a documented mode
/// divergence — an UNSAT-originating lane must instead gate on
/// `unvetted_no_proof_lane_allowed()` (kept dead under shedding) until
/// individually vetted for raw publication.
const VETTED: &[(&str, usize, usize, usize, &str)] = &[
    (
        "executor/check_sat.rs",
        2,
        2,
        0,
        "2x vacuous-under-shedding debug_assert postconditions (audited); \
         2x explicit-demand gates (seq corroboration re-solve [B2: KEPT in \
         v1], dense BV array-initializer rewrite); deep QE is separately \
         restricted to the post-Unknown retry and must clear the \
         authored-query publication gates. Re-vet 2026-08-21: the \
         closed-universal precheck gate that was the third entry here moved \
         to executor/qe_route.rs in 6228729e9, which named it \
         closed_universal_precheck_armed; see that entry",
    ),
    (
        "executor/lifecycle.rs",
        0,
        1,
        0,
        "explicit-demand gate: the competition_shedding_active predicate \
         itself (the external-stop finalize gate moved with the \
         unknown-publication split, below)",
    ),
    (
        "executor/lifecycle/proof_access.rs",
        0,
        1,
        0,
        "proof-access accessors (last_proof / install_unsat_proof) relocated \
         from the lifecycle split; the sole !is_producing_proofs site is a \
         test assertion (proof_checking_solve_does_not_expose_proof_without_\
         output_request), not a live UNSAT-routing lane — bookkeeping only",
    ),
    (
        "executor/lifecycle/unknown_publication.rs",
        0,
        1,
        0,
        "explicit-demand bookkeeping gate: tracker disable on external-stop \
         finalization, relocated from lifecycle.rs with the Unknown \
         publication boundary",
    ),
    (
        "executor/proof.rs",
        0,
        1,
        0,
        "an explicit-demand artifact gate (the unvetted_no_proof_lane_allowed \
         definition moved to executor/proof/lane_policy.rs upstream)",
    ),
    (
        "executor/proof/lane_policy.rs",
        1,
        0,
        0,
        "the unvetted_no_proof_lane_allowed definition (the vetted \
         chokepoint), relocated here by the upstream lane-policy refactor",
    ),
    (
        "executor/qe_route.rs",
        0,
        1,
        0,
        "re-vet after 6228729e9 (\"park the closed-universal proof precheck\") \
         moved the closed-universal validity precheck's gate here from an \
         inline `!is_producing_proofs()` in executor/check_sat.rs and named it \
         closed_universal_precheck_armed; same audited explicit-demand gate, \
         new file, semantics unchanged. It stays on !is_producing_proofs() \
         rather than unvetted_no_proof_lane_allowed() DELIBERATELY: proof mode \
         is the default posture, and CLOSED_UNIVERSAL_STALE_GATE_2026-08-21.md \
         records that arming it under proofs regresses authored-scope artifact \
         fidelity, so it is parked there rather than shed-gated. On a public \
          query the precheck fails closed to `unknown`; only a disposable solve \
          takes its verdict-only UNSAT",
    ),
    (
        "executor/quantifier_loop/preprocess.rs",
        3,
        0,
        0,
        "proof bookkeeping: provenance install/registration (skip-safe) + \
         exact-instance materialization (documented e-matching mode \
         divergence, entailed either way)",
    ),
    (
        "executor/quantifier_loop/result_mapping.rs",
        1,
        0,
        0,
        "proof bookkeeping: forall provenance registration only; the \
         assertion rewrite above it runs in both modes",
    ),
    (
        "executor/theories/bv/mod.rs",
        0,
        2,
        0,
        "explicit-demand gates: 2x packed-mux derived-equality arms (moved \
         off produce_proofs_enabled when the certificate became mandatory; \
         see produce_proofs_enabled doc)",
    ),
    (
        "executor/theories/lia/mod.rs",
        0,
        1,
        1,
        "1x explicit-demand incremental-eager arm; 1x eager-assume UNSAT \
         probe dormant lane (B2: kept dead)",
    ),
    (
        "executor/theories/lra/mod.rs",
        0,
        3,
        0,
        "explicit-demand gates: LRA incremental/eager engine routing (2 \
         routing gates + 1 routing-guard debug_assert)",
    ),
    (
        "executor/theories/solve_harness/mod.rs",
        0,
        2,
        0,
        "explicit-demand gates: eq_diffvar, GuardedEqMining. The second \
         variable-substitution round's gate MOVED with the round itself to \
         mod_elim_var_subst.rs (#4751); it is the same site, re-vetted there",
    ),
    (
        "executor/theories/solve_harness/mod_elim_var_subst.rs",
        0,
        1,
        0,
        "explicit-demand gate for the #8736 second variable-substitution \
         round, relocated verbatim out of preprocess_lia_artifacts (#4751). \
         Completeness-only: the round inlines the mod/div decomposition, so \
         skipping it under an explicit proof demand costs `incomplete` \
         results, never a verdict. Its proof-provenance MINT is separately \
         gated on produce_proofs_enabled() -- a POSITIVE site, not counted \
         here -- so a tracker-recording run still gets replayable records",
    ),
    (
        "executor/theories/strings_word_prop.rs",
        0,
        0,
        1,
        "word-eq constant-propagation dormant lane (B2: kept dead)",
    ),
    (
        "executor/unsat_cert.rs",
        0,
        6,
        0,
        "6x post-publication/stop-path tracker disables in the certification \
         funnel (cost hygiene; an explicit proof demand keeps it armed). The \
         6th is `decline_unexportable_assume_scope_under_proof_demand`'s, \
         AUDITED: it is byte-identical to the sibling site in \
         `decline_trust_bearing_unsat_under_strict_proofs` -- same three \
         lines, same `UnknownOrigin::TerminalTrust`, same unconditional \
         `SolveResult::Unknown` return -- and sits on a path that has ALREADY \
         decided to withhold, so it can neither originate nor route an UNSAT",
    ),
];

/// Characters that may form the receiver between `!` and the call token
/// (`self.`, `this.`, `exec.`, a macro's `$self.`, chained paths).
fn is_receiver_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_' || c == '.' || c == '$'
}

/// Count call sites of `needle` (an exact zero-argument call token like
/// `produce_proofs_enabled()`) in `text`, with `//` line comments stripped.
/// When `negated_only`, count only occurrences whose receiver chain is
/// prefixed with `!`.
fn count_sites(text: &str, needle: &str, negated_only: bool) -> usize {
    let mut count = 0;
    for line in text.lines() {
        let code = match line.find("//") {
            Some(idx) => &line[..idx],
            None => line,
        };
        let mut start = 0;
        while let Some(found) = code[start..].find(needle) {
            let at = start + found;
            start = at + needle.len();
            let prefix = &code[..at];
            let receiver_start = prefix
                .rfind(|c: char| !is_receiver_char(c))
                .map_or(0, |i| i + 1);
            let negated = prefix[..receiver_start].ends_with('!');
            if negated_only && !negated {
                continue;
            }
            count += 1;
        }
    }
    count
}

/// Walk `src/`, skipping cfg(test)-only sources: `*_tests.rs` files and any
/// `tests` or `*_tests` directory component. The latter covers crate-level
/// modules such as `executor_tests` and `dpll_tests`, not just nested `tests/`.
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
                // `foo/tests.rs` is the `#[cfg(test)] mod tests;` convention
                // (e.g. `executor/proof/tests.rs`), exactly as cfg(test)-only
                // as a `*_tests.rs` file; counting its asserts as production
                // gates broke the census when c141d3b80 added
                // `assert!(!exec.is_producing_proofs())` there.
                .is_some_and(|n| n.ends_with("_tests.rs") || n == "tests.rs")
        {
            out.push(path);
        }
    }
}

#[test]
fn negated_proof_gate_census_matches_vetted_list() {
    let src = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut files = Vec::new();
    production_sources(&src, &mut files);
    files.sort();
    assert!(
        files.len() > 100,
        "census walked only {} files — the source layout moved; fix the walker, \
         do not weaken the census",
        files.len()
    );

    let mut observed: Vec<(String, usize, usize, usize)> = Vec::new();
    for path in &files {
        let text =
            fs::read_to_string(path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
        let negated_enabled = count_sites(&text, "produce_proofs_enabled()", true);
        let negated_producing = count_sites(&text, "is_producing_proofs()", true);
        let lane_sites = count_sites(&text, "unvetted_no_proof_lane_allowed()", false);
        if negated_enabled + negated_producing + lane_sites > 0 {
            let rel = path
                .strip_prefix(&src)
                .expect("under src/")
                .to_string_lossy()
                .replace(std::path::MAIN_SEPARATOR, "/");
            observed.push((rel, negated_enabled, negated_producing, lane_sites));
        }
    }
    observed.sort();

    let vetted: Vec<(String, usize, usize, usize)> = VETTED
        .iter()
        .map(|&(path, a, b, c, _)| (path.to_string(), a, b, c))
        .collect();
    // VETTED must stay sorted so diffs against `observed` line up.
    {
        let mut sorted = vetted.clone();
        sorted.sort();
        assert_eq!(vetted, sorted, "keep the VETTED list sorted by path");
    }

    if observed != vetted {
        let render = |rows: &[(String, usize, usize, usize)]| {
            rows.iter()
                .map(|(p, a, b, c)| {
                    format!("  {p}: !produce_proofs_enabled={a} !is_producing_proofs={b} unvetted_no_proof_lane_allowed={c}")
                })
                .collect::<Vec<_>>()
                .join("\n")
        };
        panic!(
            "proof-gate census mismatch (#proof-capability B2).\n\
             A proof-sensitive gate was added, removed, or moved without \
             re-vetting. A new `!produce_proofs_enabled()` site goes LIVE \
             under competition shedding: if it can originate or route an \
             UNSAT, gate it on `unvetted_no_proof_lane_allowed()` instead \
             (kept dead under shedding); if it is proof bookkeeping or a \
             vacuous assert, audit it and update the VETTED list with a \
             rationale.\n\nobserved:\n{}\n\nvetted:\n{}",
            render(&observed),
            render(&vetted),
        );
    }
}

/// The dormant-lane predicate semantics (B2 item 1): the two lanes stay
/// exactly as dead as before in every configuration —
/// `unvetted_no_proof_lane_allowed()` equals the old `!produce_proofs_enabled()`
/// whenever competition shedding is inactive, and is additionally FALSE
/// under active shedding.
#[test]
fn unvetted_lane_predicate_is_dead_under_shedding_and_proofs() {
    use super::Executor;

    // Non-competition, tracker off (the internal/nested-solve config where
    // the lanes run today): allowed — byte-identical to the old gates.
    let mut exec = Executor::new();
    assert!(!exec.produce_proofs_enabled());
    assert!(exec.unvetted_no_proof_lane_allowed());

    // Certified public path: begin_public_solve arms the tracker — dead,
    // exactly like the old `!produce_proofs_enabled()` gates.
    exec.begin_public_solve(false);
    assert!(exec.produce_proofs_enabled());
    assert!(!exec.unvetted_no_proof_lane_allowed());

    // Competition shedding: tracker disarmed, produce_proofs_enabled()
    // false — the OLD gates would have gone live; the named predicate keeps
    // the lanes dead.
    let mut exec = Executor::new();
    exec.set_competition_mode(true);
    exec.begin_public_solve(false);
    assert!(!exec.produce_proofs_enabled());
    assert!(exec.competition_shedding_active());
    assert!(!exec.unvetted_no_proof_lane_allowed());

    // Competition mode + explicit proof demand (precedence): certified
    // lanes restored, tracker armed — dead via produce_proofs_enabled().
    let mut exec = Executor::new();
    exec.set_competition_mode(true);
    exec.set_produce_proofs(true);
    exec.begin_public_solve(false);
    assert!(!exec.competition_shedding_active());
    assert!(exec.produce_proofs_enabled());
    assert!(!exec.unvetted_no_proof_lane_allowed());

    // Explicit proof demand without competition mode: dead, as always.
    let mut exec = Executor::new();
    exec.set_produce_proofs(true);
    assert!(!exec.unvetted_no_proof_lane_allowed());
}
