// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! M3a: a nested UNSAT publishes ONLY through its expansion certificate
//! (#qlra-nested-cegqi plan §4.1, §9 M3a); the nested search is on by default.
//!
//! Every positive test asserts three things: the public verdict is `unsat`;
//! the lane itself published it (`qlra.cert = expansion-installed`); and the
//! proof left in `last_proof` is re-checked HERE by the strict checker over
//! the exact authored scope and carries the certificate's quantifier steps.
//!
//! The mutation tests arm a defect in the certificate producer — a lemma
//! flipped into a bare fact, a lossy proxy map with the round-trip check
//! dropped, a forged `forall_inst` tuple — and require the installation
//! boundary (scope + strict checker) to refuse it: the certificate never
//! installs, so the lane never publishes it.

use std::time::Duration;

use ay_frontend::parse;

use crate::executor::{set_expansion_cert_mutation, ExpansionCertMutation};
use crate::Executor;

const QUERY_TIMEOUT: Duration = Duration::from_secs(30);

struct CertRun {
    verdict: String,
    shadow: Option<String>,
    cert: Option<String>,
    cert_decline: Option<String>,
    /// The installed proof re-checks strict-complete over the authored scope.
    strict: bool,
    /// The installed proof carries `forall_inst` / `sko_forall` /
    /// `qnt_neg_exists` steps (the certificate's lemma derivations).
    quantifier_steps: usize,
    /// Deep-QE `Unknown` retries the public solve paid.
    deep_qe_retries: u64,
}

fn run_cert(smt: &str, mutation: ExpansionCertMutation, legacy_ce_free_resolve: bool) -> CertRun {
    run_cert_with(smt, mutation, legacy_ce_free_resolve, false)
}

/// As [`run_cert`], optionally under the CLI's `--z3-mode` posture
/// (competition shedding, no parsed-assertion retention): the first pass's
/// strict obligation lacks the authored roots, so the certificate is built
/// on the lane's memo retry.
fn run_cert_with(
    smt: &str,
    mutation: ExpansionCertMutation,
    legacy_ce_free_resolve: bool,
    z3_mode: bool,
) -> CertRun {
    let flags = ay_core::MiscCliFlags {
        no_qlra_nested: false,
        // The QSAT route (587104eaa) runs first and decides these fixtures;
        // these tests pin the nested-CEGQI lane, so take QSAT out of the way.
        no_qsat: true,
        no_quantifier_ce_free_resolve: !legacy_ce_free_resolve,
        ..ay_core::misc_cli_flags().clone()
    };
    let _flags = ay_core::misc_test_override::set(flags);
    let _mutation = set_expansion_cert_mutation(mutation);
    let commands = parse(smt).expect("parse");
    let mut exec = Executor::new();
    exec.set_timeout(Some(QUERY_TIMEOUT));
    if z3_mode {
        exec.set_competition_mode(true);
        exec.set_retain_parsed_assertions(false);
    }
    let outputs = exec.execute_all(&commands).expect("execute");
    let stats = exec.statistics();
    let text = |key: &str| stats.get_string(key).map(str::to_string);
    let verdict = outputs
        .iter()
        .rev()
        .find(|line| matches!(line.as_str(), "sat" | "unsat" | "unknown"))
        .cloned()
        .unwrap_or_default();
    let (shadow, cert, cert_decline) = (
        text("qlra.shadow_verdict"),
        text("qlra.cert"),
        text("qlra.cert_decline"),
    );
    let quantifier_steps = exec.test_installed_proof_quantifier_steps();
    let strict = exec.test_installed_proof_is_strict_authored();
    let deep_qe_retries = exec.prepass_reachability().deep_qe_unknown_retries;
    CertRun {
        verdict,
        shadow,
        cert,
        cert_decline,
        strict,
        quantifier_steps,
        deep_qe_retries,
    }
}

fn assert_certified(name: &str, smt: &str, legacy_ce_free_resolve: bool) {
    let run = run_cert(smt, ExpansionCertMutation::None, legacy_ce_free_resolve);
    assert_eq!(
        run.shadow.as_deref(),
        Some("unsat"),
        "{name}: shadow verdict"
    );
    assert_eq!(
        run.cert.as_deref(),
        Some("expansion-installed"),
        "{name}: the expansion certificate must install (decline={:?})",
        run.cert_decline
    );
    assert_eq!(run.verdict, "unsat", "{name}: public verdict");
    assert!(
        run.strict,
        "{name}: the installed proof must re-check strict-complete"
    );
    assert!(
        run.quantifier_steps > 0,
        "{name}: the proof must carry the certificate's quantifier steps"
    );
}

/// A mutated certificate is refused by the installation boundary and never
/// published by the lane. The public verdict is never `sat` (every input here
/// is unsat); a legacy route may still publish its OWN certified `unsat`.
fn assert_refused(name: &str, smt: &str, mutation: ExpansionCertMutation, expected: &[&str]) {
    let run = run_cert(smt, mutation, true);
    assert_eq!(
        run.shadow.as_deref(),
        Some("unsat"),
        "{name}: shadow verdict"
    );
    assert_eq!(
        run.cert.as_deref(),
        Some("expansion-declined"),
        "{name} {mutation:?}: a mutated certificate must never install"
    );
    let decline = run.cert_decline.as_deref().unwrap_or_default();
    assert!(
        expected.contains(&decline),
        "{name} {mutation:?}: refused at {decline:?}, expected one of {expected:?}"
    );
    assert_ne!(run.verdict, "sat", "{name} {mutation:?}: WRONG verdict");
    if run.verdict == "unsat" {
        assert!(
            run.strict,
            "{name} {mutation:?}: a published unsat must be strict"
        );
    }
}

const P2: &str =
    "(set-logic LRA)(assert (exists ((y Real)) (forall ((x Real)) (> y x))))(check-sat)";

/// `¬∀x∃y. y > x`: a top effective-∃ (`sko_forall` on the authored forall)
/// over a negated existential (L2: `qnt_neg_exists` + `forall_inst`).
const NEG_FORALL_EXISTS: &str = "(set-logic LRA)(assert (not (forall ((x Real)) \
     (exists ((y Real)) (> y x)))))(check-sat)";

/// `∀x∃y. x < y < x`: the inner existential is empty for every `x`.
const FORALL_EMPTY_EXISTS: &str = "(set-logic LRA)(assert (forall ((x Real)) \
     (exists ((y Real)) (and (> y x) (< y x)))))(check-sat)";

#[test]
fn p2_publishes_with_a_strict_expansion_certificate() {
    assert_certified("p2", P2, true);
}

#[test]
fn negated_forall_exists_publishes_with_a_strict_expansion_certificate() {
    assert_certified("neg-forall-exists", NEG_FORALL_EXISTS, true);
}

#[test]
fn forall_empty_exists_publishes_with_a_strict_expansion_certificate() {
    assert_certified("forall-empty-exists", FORALL_EMPTY_EXISTS, true);
}

macro_rules! fixture {
    ($file:literal) => {
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/quantifier/qlra/",
            $file
        ))
    };
}

#[test]
fn mjollnir3_155_publishes_with_a_strict_expansion_certificate() {
    assert_certified(
        "mjollnir3_155",
        fixture!("mjollnir3_formula_155.smt2"),
        true,
    );
}

/// The legacy re-solve is switched off as in `m2_nested.rs` (its debug
/// assertion on this file is pre-existing and unrelated to the lane).
#[test]
fn mjollnir2_219_publishes_with_a_strict_expansion_certificate() {
    assert_certified(
        "mjollnir2_219",
        fixture!("mjollnir2_formula_219.smt2"),
        false,
    );
}

/// KNOWN GAP, pinned so it cannot regress into a publication: the
/// certificate is built and the probe refutes, but the installation
/// boundary's strict check exhausts its resource envelope (`proof validation
/// resource envelope exhausted`; the Tseitin steps over the renamed
/// quantified atoms carry ~8k-node payloads, charged work x unfolded work).
/// The boundary refuses, so the verdict stays what the legacy path decides.
#[test]
fn mjollnir4_252_is_refused_by_the_strict_envelope_not_published_by_the_lane() {
    let run = run_cert(
        fixture!("mjollnir4_formula_252.smt2"),
        ExpansionCertMutation::None,
        true,
    );
    assert_eq!(run.shadow.as_deref(), Some("unsat"));
    assert_ne!(run.verdict, "sat", "WRONG verdict");
    match run.cert.as_deref() {
        Some("expansion-installed") => assert!(run.strict, "a publication must be strict"),
        _ => assert_eq!(run.cert_decline.as_deref(), Some("install-strict")),
    }
}

#[test]
fn rndpre_4_18_publishes_with_a_strict_expansion_certificate() {
    assert_certified("RNDPRE_4_18", fixture!("RNDPRE_4_18.smt2"), true);
}

#[test]
fn rnd_3_5_publishes_with_a_strict_expansion_certificate() {
    assert_certified("RND_3_5", fixture!("RND_3_5.smt2"), true);
}

/// The installation boundary's refusals a corrupted certificate may hit.
const BOUNDARY: &[&str] = &[
    "install-scope",
    "install-empty-clause",
    "install-strict",
    "install-incomplete",
    "install-internal-check",
];

#[test]
fn a_lemma_flipped_to_a_fact_is_refused_by_the_strict_checker() {
    for (name, smt) in [("p2", P2), ("neg-forall-exists", NEG_FORALL_EXISTS)] {
        assert_refused(
            name,
            smt,
            ExpansionCertMutation::FlipLemmaToFact,
            &["install-strict"],
        );
    }
}

#[test]
fn a_forged_instance_tuple_is_refused_by_the_strict_checker() {
    for (name, smt) in [
        ("p2", P2),
        ("mjollnir3_155", fixture!("mjollnir3_formula_155.smt2")),
    ] {
        assert_refused(
            name,
            smt,
            ExpansionCertMutation::ForgeTuple,
            &["install-strict"],
        );
    }
}

/// A lossy proxy map is caught by the round-trip check; with that check
/// dropped, the installation boundary still refuses the mis-renamed proof.
#[test]
fn a_lossy_proxy_map_is_refused_with_or_without_the_round_trip_check() {
    for (name, smt) in [("p2", P2), ("neg-forall-exists", NEG_FORALL_EXISTS)] {
        assert_refused(
            name,
            smt,
            ExpansionCertMutation::LossyProxy,
            &["proxy-round-trip"],
        );
        assert_refused(name, smt, ExpansionCertMutation::DropRoundTrip, BOUNDARY);
    }
}

/// Under the kill switch (`--no-qlra-nested`) the nested search never runs,
/// so no certificate is ever attempted. (QSAT is off too, so the lane runs
/// and the test is not vacuous.)
#[test]
fn no_certificate_under_the_kill_switch() {
    let _nested_off = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
        no_qlra_nested: true,
        no_qsat: true,
        ..ay_core::misc_cli_flags().clone()
    });
    let commands = parse(P2).expect("parse");
    let mut exec = Executor::new();
    exec.set_timeout(Some(QUERY_TIMEOUT));
    exec.execute_all(&commands).expect("execute");
    let stats = exec.statistics();
    assert_eq!(stats.get_string("qlra.shadow_verdict"), None);
    assert_eq!(stats.get_string("qlra.cert_decline"), None);
    assert_ne!(stats.get_string("qlra.cert"), Some("expansion-installed"));
}

/// keymaera water_tank-node14909: a DEPTH-1 problem whose consequence replay
/// declines (base answers `unknown`); with the switch on, the nested search
/// re-decides it and its expansion certificate publishes.
#[test]
fn water_tank_14909_depth1_replay_decline_is_certified_by_the_expansion() {
    let run = run_cert(
        fixture!("water_tank-node14909.smt2"),
        ExpansionCertMutation::None,
        true,
    );
    assert_eq!(
        run.cert.as_deref(),
        Some("expansion-installed"),
        "decline={:?}",
        run.cert_decline
    );
    assert_eq!(run.verdict, "unsat");
    assert!(run.strict);
    assert!(run.quantifier_steps > 0);
}

/// Under competition shedding the first pass's strict obligation lacks the
/// authored roots: the certificate is built, pre-checked and parked
/// (`expansion-deferred`), and the quantified-trace retry installs it.
#[test]
fn p2_and_rnd_3_5_publish_under_competition_shedding() {
    for (name, smt) in [("p2", P2), ("RND_3_5", fixture!("RND_3_5.smt2"))] {
        let run = run_cert_with(smt, ExpansionCertMutation::None, true, true);
        assert_eq!(
            run.shadow.as_deref(),
            Some("unsat"),
            "{name}: shadow verdict"
        );
        assert_eq!(
            run.cert.as_deref(),
            Some("expansion-installed"),
            "{name}: decline={:?}",
            run.cert_decline
        );
        assert_eq!(run.verdict, "unsat", "{name}");
        assert!(run.strict, "{name}: strict");
    }
}

/// A parked certificate needs only the authored problem obligation the
/// trace-armed retry installs, so that retry runs BEFORE the deep-QE retry:
/// the deep-QE elimination probe used to spend the rest of the deadline first
/// (mjollnir1/formula_134 under `--z3-mode`: parked at 2.4 s, `unknown` at
/// 20 s). mjollnir3/formula_177 parks its certificate on the shed first pass
/// and its authored roots are ones the deep-QE pre-pass rewrites (a ~20 s
/// elimination), so with the old order the deep-QE retry runs first and this
/// count is 1.
#[test]
fn a_parked_certificate_is_installed_before_the_deep_qe_retry_runs() {
    for (name, smt) in [("mjollnir3_177", fixture!("mjollnir3_formula_177.smt2"))] {
        let run = run_cert_with(smt, ExpansionCertMutation::None, true, true);
        assert_eq!(run.verdict, "unsat", "{name}");
        assert_eq!(
            run.cert.as_deref(),
            Some("expansion-installed"),
            "{name}: decline={:?}",
            run.cert_decline
        );
        assert!(run.strict, "{name}: strict");
        assert_eq!(
            run.deep_qe_retries, 0,
            "{name}: the deep-QE retry must not run ahead of the parked certificate"
        );
    }
}

/// A pass whose strict obligation still lacks the authored roots must leave a
/// parked candidate parked (fail-closed: `scope-pending`, nothing installed),
/// so the pass that CAN install it still has it. It used to be consumed and
/// dropped by the first pass that looked at it.
#[test]
fn a_scope_pending_pass_leaves_the_parked_candidate_parked() {
    let _flags = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
        no_qlra_nested: false,
        no_qsat: true,
        ..ay_core::misc_cli_flags().clone()
    });
    let mut exec = Executor::new();
    exec.set_timeout(Some(QUERY_TIMEOUT));
    exec.set_competition_mode(true);
    exec.set_retain_parsed_assertions(false);
    let commands = parse("(set-logic LRA)(assert (exists ((y Real)) (forall ((x Real)) (> y x))))")
        .expect("parse");
    exec.execute_all(&commands).expect("execute");
    let (pending, kept, installed) = exec
        .test_install_parked_while_scope_pending()
        .expect("precondition: the obligation must lack the authored root");
    assert!(
        pending,
        "a scope-pending install must decline with scope-pending"
    );
    assert!(kept, "the parked candidate must stay parked");
    assert!(!installed, "nothing may be installed");
}

/// `∃x. ∀y. y < x` is false over the reals. The nested search refutes it and
/// the expansion certificate installs, but its `sko_forall` over a nested
/// binder is outside the certified Skolem printer's scope, so the
/// problem-scoped document does not render. Under a DEMANDED certificate
/// (`--proof FILE`) the lane must not publish that `unsat`: the CLI would
/// refuse to write the document and exit 1 with no verdict. Under the
/// best-effort sidecar (the CLI default) the verdict stands without a
/// document. (If the printer learns this shape, the first assertion fails:
/// pick a fixture whose certificate still does not render.)
#[test]
fn an_unrenderable_certificate_is_not_published_under_a_demanded_certificate() {
    const AL2: &str = "(set-logic LRA)\
        (assert (exists ((x Real)) (forall ((y Real)) (< y x))))\
        (check-sat)";
    let _flags = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
        no_qlra_nested: false,
        no_qsat: true,
        ..ay_core::misc_cli_flags().clone()
    });
    let solve = |demanded: bool| {
        let mut exec = Executor::new();
        exec.set_timeout(Some(QUERY_TIMEOUT));
        if demanded {
            exec.set_produce_proofs(true);
        } else {
            exec.set_best_effort_produce_proofs(1_000_000);
        }
        let outputs = exec
            .execute_all(&parse(AL2).expect("parse"))
            .expect("execute");
        let verdict = outputs
            .iter()
            .rev()
            .find(|line| matches!(line.as_str(), "sat" | "unsat" | "unknown"))
            .cloned()
            .unwrap_or_default();
        let rendered = matches!(
            exec.try_export_last_proof_alethe_for_problem_scope(),
            Some(Ok(_))
        );
        let cert = exec
            .statistics()
            .get_string("qlra.cert")
            .map(str::to_string);
        (verdict, cert, rendered)
    };

    let (verdict, cert, rendered) = solve(true);
    assert!(
        matches!(
            cert.as_deref(),
            Some("expansion-render-refused" | "expansion-unrendered")
        ),
        "demanded: the lane must decline an unrenderable certificate (cert={cert:?})"
    );
    assert_ne!(verdict, "sat", "the problem is unsat");
    assert!(
        verdict != "unsat" || rendered,
        "demanded: an unsat must come with a document that renders"
    );

    let (verdict, cert, _) = solve(false);
    assert_eq!(cert.as_deref(), Some("expansion-installed"), "best effort");
    assert_eq!(verdict, "unsat", "best effort: the verdict stands");
}
