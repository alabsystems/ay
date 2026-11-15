// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! AY's `--strict-proofs` certificates for external-codegen queries are checkable by
//! the checker external-codegen replays them with.
//!
//! external-codegen promotes an AY `unsat` only after `clean cert verify-external`
//! accepts the exact query and Alethe proof. Measured 2026-09-27 on the 2785
//! distinct queries external-codegen-verify's proof tests send, AY c6a80496e withheld
//! that certificate, or handed over one Clean 414913cce refused, on the 115
//! queries under `fixtures/external_codegen_consumer_certificates/` (`MANIFEST.tsv`
//! names each one's class):
//!
//! * `bitblast_ashr` — the printed shift circuit's overshift layer was zero
//!   filled. That is upstream Carcara 9a352ee's circuit, which is wrong for a
//!   negative operand; Clean's Carcara fills with the sign bit, as SMT-LIB
//!   `bvashr` requires, and compares circuits syntactically. Pinned Carcara
//!   refuses the sign fill, so such a certificate must say
//!   `carcara_surface=clean-dialect`, never `supported`.
//! * `and_simplify` / `or_simplify` — `(= (and true X) X)` with `X` itself a
//!   conjunction (spelled out or behind a `define-fun`). The consumer's rule
//!   compares the surviving operand with the ARGUMENTS of `X` and rejects it.
//! * `problem-*` — a query that declares a `FloatingPoint` constant, or a
//!   constant named `step`, does not parse in Carcara at all, yet the surface
//!   disclosure read only the proof and strict published it.
//! * `whole-query-hole` — the certificate printed the whole-query bit-vector
//!   lemma as `hole`, so strict answered `unknown`, although the complete
//!   bit-blast refutation renders it.
//! * `ring-identity` (13 more, measured after the fixes above) — a commuted or
//!   regrouped `bvmul` chain, which elaboration folds to one term; no lemma
//!   route recognized the nonlinear identity one `poly_simp` step proves, so
//!   strict answered `unknown` (or spent a minute bit-blasting 64-bit products).
//! * `shared-lane-bias` (4 more, 2026-09-29) — external-codegen's per-lane x86
//!   `<16 x i8>` unsigned compares, whose bias constant repeats under 32
//!   `bvxor`s: the whole-query lemma printed as `hole` because the bit-blast
//!   producer sized the lowered lemma as a tree (over its 4,096-node cap) and
//!   charged every term's whole subtree (over its 100,000-node budget).
//! * `authored-literal-spelling` (19 more, 2026-09-29) — array read-over-write
//!   identities written with `(_ bvN w)` literals, which the preprocessor folds
//!   to `false`. The rescues that compare the re-interned root with the
//!   author's text spelling-for-spelling decline on them (the printer spells
//!   the literal in binary), so the certificate was the erasure's `hole` and
//!   strict answered `unknown (incomplete self-check-rejected)`. The raw
//!   ground closure (`authored_ground_closure`), the last fold rescue, now
//!   re-derives every one of them from the raw root.
//! * `word-level-closure` (10 more, 2026-10-02) — external-codegen's x86-64 body
//!   theorems (one nested authored conjunction, last conjunct the negated
//!   claim): AY 57ea58ca3 bit-blasted the whole root (32/64-bit multipliers,
//!   adder chains) to the 30 s timeout or a multi-MB document; the raw ground
//!   closure refutes it by congruence and wiring-checked slice identities, <1 s.
//!
//! What is checked in-repository, for every certificate: `unsat` on a
//! hole-free document (`unproved_steps=0`); that its line says
//! `carcara_surface=clean-dialect` exactly when the document keeps a step
//! pinned Carcara 9a352ee refuses (the sign-filled `bitblast_ashr` layer, a
//! `zero_extend` identity, which `consumer_rules/zero_extend_identity.rs` holds
//! to its one shape, or Clean's divider over a dividend that is not literally
//! zero): measured 2026-09-30, 14 of these certificates
//! carried the `zero_extend` spelling under `supported`; and every command
//! against the consumer-rule mirror (`consumer_rules.rs`, Clean 7330fa6c's
//! checker transcribed rule by rule), whose every refusal fails the test. The
//! mirror decides a step only when its rule is in `MIRRORED` and the
//! transcription covers the instance; a certificate counts as checked only
//! when every command was accepted and the walk re-derived the empty clause
//! from the problem's assertions, never with them all dropped. Measured
//! 2026-09-30 on 1da497c8f: 147 of 147 checked step by step (the corpus
//! prints 67 rules, all among the 98 mirrored), and a Clean built from
//! 7330fa6c's checker source passed all 147. Over 3,107 mutated steps (these
//! certificates and 22 divider ones) the mirror and that Clean never
//! disagreed on a step the mirror decided; it left 28 undecided: 26
//! `resolution` steps without pivots, and 2 `reordering` steps (mirrored
//! since).
//!
//! CORRECTION (2026-09-30): f948c22d9 wrote here that every certificate "is
//! checked against the consumer's rules as mirrored", and 57cef15fd's message
//! reported "147 certificates checked against the consumer-rule mirror";
//! c57bd8481 narrowed the doc to three rules. The mirror then read only
//! `bitblast_ashr` (its final layer), `and_simplify` and `or_simplify` steps
//! and passed every other step unread, so 0 of the 147 had every step checked
//! in-repository (each has `resolution` steps), the 19
//! `authored-literal-spelling` ones no step at all, and no
//! `bitblast_udiv`/`bitblast_urem` step was ever read. The `unsat` verdicts
//! were not in question (all 147 pass Clean); the
//! in-repository coverage claim was. The external replays
//! run when a checker is configured: with `CLEAN_PATH` naming a `clean`
//! binary every certificate is replayed through it, and with pinned Carcara
//! (`CARCARA_PATH`, or `carcara` on `PATH`) every `supported` one must be
//! `valid`. The `clean` binary must be current: the aterm store's Clean 8606
//! (2026-09-16) predates rules these certificates use and refuses 107 of them
//! (`bitblast_shl`, `bitblast_ashr`, `arrays_row`: `unknown rule`; modular
//! bit-vector `poly_simp`; `cong` and `refl` over the `zero_extend` spelling
//! newer Clean parses as `concat`), while Clean 7330fa6c accepts every one.
//! AY's pin since 2026-10-08, 01ffe310, adds `dt_project` (C2) and SMT-LIB read refusals (36-40).

use ntest::timeout;
use std::io::Write as _;
use std::path::PathBuf;
use std::process::Command;

use crate::alethe_dialect_disclosure::pinned_carcara_verdict;
use crate::spawn::OutputTimeout;
use crate::strict_certificate_publication::{verdict_lines, without_script_timeout, QUERY_TIMEOUT};

struct Fixture {
    id: String,
    class: String,
    obligation: String,
    script: String,
}

fn fixture_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/group_soundness/fixtures/external_codegen_consumer_certificates")
}

fn corpus() -> Vec<Fixture> {
    let dir = fixture_dir();
    let manifest = std::fs::read_to_string(dir.join("MANIFEST.tsv")).expect("read MANIFEST.tsv");
    let fixtures: Vec<Fixture> = manifest
        .lines()
        .filter(|line| !line.starts_with('#') && !line.trim().is_empty())
        .map(|line| {
            let mut columns = line.split('\t');
            let id = columns.next().expect("id").to_string();
            let class = columns.next().expect("class").to_string();
            let obligation = columns.next().expect("obligation").to_string();
            let script = std::fs::read_to_string(dir.join(format!("{id}.smt2")))
                .unwrap_or_else(|e| panic!("read {id}.smt2: {e}"));
            Fixture {
                id,
                class,
                obligation,
                script,
            }
        })
        .collect();
    assert_eq!(fixtures.len(), 161, "the measured corpus has 161 queries");
    fixtures
}

struct OneShot {
    verdicts: Vec<String>,
    stderr: String,
    problem: String,
    proof: Option<String>,
    context: String,
}

/// external-codegen's one-shot argv: `-smt2 F --strict-proofs --proof F.alethe
/// --proof-format alethe`, on the script without its own wall-clock budget.
fn run_one_shot(fixture: &Fixture) -> OneShot {
    let problem = without_script_timeout(&fixture.script);
    let dir = tempfile::tempdir().expect("tempdir");
    let smt2 = dir.path().join("query.smt2");
    let proof = dir.path().join("query.smt2.alethe");
    let mut file = std::fs::File::create(&smt2).expect("create query file");
    file.write_all(problem.as_bytes()).expect("write query");
    drop(file);
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .arg("-smt2")
        .arg(&smt2)
        .arg("--strict-proofs")
        .arg("--proof")
        .arg(&proof)
        .args(["--proof-format", "alethe"])
        .output_timeout(QUERY_TIMEOUT);
    // A query that does not answer is this fixture's failure, reported with
    // the others; it must not abort the corpus run.
    let output = match output {
        Ok(output) => output,
        Err(error) => {
            return OneShot {
                verdicts: Vec::new(),
                stderr: String::new(),
                problem,
                proof: None,
                context: format!(
                    "{} [{}] {}: no answer: {error}",
                    fixture.id, fixture.class, fixture.obligation
                ),
            }
        }
    };
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    OneShot {
        verdicts: verdict_lines(&stdout),
        context: format!(
            "{} [{}] {} (exit {:?})\nstdout:\n{stdout}\nstderr:\n{stderr}",
            fixture.id, fixture.class, fixture.obligation, output.status
        ),
        stderr,
        proof: std::fs::read_to_string(&proof).ok(),
        problem,
    }
}

#[path = "external_codegen_consumer_certificates/consumer_rules.rs"]
pub(crate) mod consumer_rules;
use consumer_rules::{
    is_mirrored, mirror_certificate_with_control, pinned_refused_ashr_steps,
    pinned_refused_divider_steps, pinned_refused_zero_extend_steps, zero_extend_identity_defects,
    Coverage,
};

#[path = "external_codegen_consumer_certificates/clean_replay.rs"]
mod clean_replay;
#[path = "external_codegen_consumer_certificates/mirror_controls.rs"]
mod mirror_controls;
use clean_replay::clean_verdict;

/// `supported` certificates pinned Carcara answered on, in this process.
static PINNED_REPLAYS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

/// Pinned Carcara's refusal of the certificate, or `None` when it answers
/// `valid` or no checker runs.
fn pinned_carcara_refusal(problem: &str, proof: &str) -> Option<String> {
    let dir = tempfile::tempdir().expect("tempdir");
    let (smt2, alethe) = (
        dir.path().join("query.smt2"),
        dir.path().join("query.alethe"),
    );
    std::fs::write(&smt2, problem).expect("write the query");
    std::fs::write(&alethe, proof).expect("write the certificate");
    let (verdict, stderr) = pinned_carcara_verdict(&smt2, &alethe)?;
    PINNED_REPLAYS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    (verdict != "valid").then(|| format!("`{verdict}`: {stderr}"))
}

fn certificate_line(stderr: &str) -> Option<&str> {
    stderr
        .lines()
        .find(|line| line.starts_with("c ay.proof.certificate "))
}

/// One fixture's run: why it does not hand external-codegen a checkable certificate
/// (`None` when it does), whether `CLEAN_PATH` replayed it, and what the
/// consumer-rule mirror established about it.
#[derive(Default)]
struct Outcome {
    failure: Option<String>,
    replayed: bool,
    mirror: Option<Coverage>,
    /// The `:rule` names the document prints, read off its text.
    printed_rules: std::collections::BTreeSet<String>,
}

fn failed(why: String) -> Outcome {
    Outcome {
        failure: Some(why),
        ..Outcome::default()
    }
}

fn outcome(fixture: &Fixture) -> Outcome {
    let run = run_one_shot(fixture);
    if run.verdicts != ["unsat"] {
        return failed(format!("expected `unsat`:\n{}", run.context));
    }
    let certificate = certificate_line(&run.stderr).unwrap_or("");
    // `clean-dialect`: pinned Carcara parses the document but refuses a
    // spelling only the consumer's checker accepts; it stays checkable here.
    let surface = certificate
        .split_whitespace()
        .find_map(|field| field.strip_prefix("carcara_surface="))
        .unwrap_or("");
    if !certificate.contains(" unproved_steps=0 ")
        || !matches!(surface, "supported" | "clean-dialect")
    {
        return failed(format!(
            "`unsat` must come with a disclosed hole-free certificate:\n{}",
            run.context
        ));
    }
    let Some(proof) = run.proof.as_deref() else {
        return failed(format!("no certificate was written:\n{}", run.context));
    };
    // `clean-dialect` exactly when the document keeps a step pinned Carcara
    // refuses: a sign-filled `bitblast_ashr` layer, a `zero_extend` identity,
    // or Clean's divider. Both directions are checked.
    let ashr = pinned_refused_ashr_steps(proof);
    let zero_extend = pinned_refused_zero_extend_steps(proof);
    let divider = pinned_refused_divider_steps(proof);
    if (ashr.is_empty() && zero_extend.is_empty() && divider.is_empty())
        == (surface == "clean-dialect")
    {
        return failed(format!(
            "{} [{}]: carcara_surface={surface}, but the steps pinned Carcara refuses are \
             bitblast_ashr {ashr:?}, zero_extend {zero_extend:?} and divider {divider:?}:\n{}",
            fixture.id, fixture.class, run.context
        ));
    }
    // The `zero_extend` reading is relied on only through its `refl` identity.
    if let Some(defect) = zero_extend_identity_defects(proof).into_iter().next() {
        return failed(format!("{} [{}]: {defect}", fixture.id, fixture.class));
    }
    // A `supported` certificate is one pinned Carcara accepts: replayed when a
    // checker runs (`CARCARA_PATH`, or `carcara` on `PATH`).
    if surface == "supported" {
        if let Some(refusal) = pinned_carcara_refusal(&run.problem, proof) {
            return failed(format!(
                "{} [{}]: disclosed carcara_surface=supported, and pinned Carcara refused it: \
                 {refusal}",
                fixture.id, fixture.class
            ));
        }
    }
    let mirror = mirror_certificate_with_control(&run.problem, proof);
    let printed_rules = proof
        .split(":rule ")
        .skip(1)
        .filter_map(|rest| rest.split([' ', ')', '\n']).next())
        .map(str::to_string)
        .collect();
    let mut outcome = Outcome {
        failure: mirror.refused.first().map(|first| {
            format!(
                "{} [{}] {}: {} command(s) the consumer refuses, first: {first}",
                fixture.id,
                fixture.class,
                fixture.obligation,
                mirror.refused.len(),
            )
        }),
        replayed: false,
        mirror: Some(mirror),
        printed_rules,
    };
    if outcome.failure.is_none() {
        match clean_verdict(&run.problem, proof) {
            None => {}
            Some(Ok(())) => outcome.replayed = true,
            Some(Err(transcript)) => {
                outcome.replayed = true;
                outcome.failure = Some(format!(
                    "{} [{}]: CLEAN_PATH refused the certificate:\n{transcript}",
                    fixture.id, fixture.class
                ));
            }
        }
    }
    outcome
}

/// Print how many certificates the mirror checked step by step and which
/// rules kept the others out. A certificate is counted only when every
/// command was decided and accepted, so every rule its text prints must be
/// one the mirror dispatches: that is asserted, not assumed.
fn report_mirror_coverage(outcomes: &[Outcome]) {
    let mut checked = 0;
    let mut blocking: std::collections::BTreeMap<&str, usize> = std::collections::BTreeMap::new();
    for outcome in outcomes {
        let Some(mirror) = &outcome.mirror else {
            continue;
        };
        if mirror.checked() {
            checked += 1;
            let unmirrored: Vec<&String> = outcome
                .printed_rules
                .iter()
                .filter(|rule| !is_mirrored(rule))
                .collect();
            assert!(
                unmirrored.is_empty(),
                "a certificate counted as checked prints rules the mirror does not check: \
                 {unmirrored:?}"
            );
        }
        for rule in mirror.undetermined.keys() {
            *blocking.entry(rule).or_default() += 1;
        }
    }
    let with_certificate = outcomes
        .iter()
        .filter(|outcome| outcome.mirror.is_some())
        .count();
    eprintln!(
        "external-codegen consumer certificates: {checked} of {with_certificate} checked step by step \
         against the consumer-rule mirror; the others are not independently checked here \
         (certificates per undecided rule: {blocking:?})"
    );
}

/// The certificate defects: `unsat` is published on a hole-free certificate
/// every step of which the consumer's rules accept, as far as the mirror
/// decides them.
#[test]
#[timeout(1_800_000)]
fn strict_certificates_for_external_codegen_queries_follow_the_consumer_rules() {
    const WORKERS: usize = 4;
    let fixtures: Vec<Fixture> = corpus()
        .into_iter()
        .filter(|fixture| !fixture.class.starts_with("problem-"))
        .collect();
    let next = std::sync::atomic::AtomicUsize::new(0);
    let outcomes = std::sync::Mutex::new(Vec::new());
    std::thread::scope(|scope| {
        for _ in 0..WORKERS {
            scope.spawn(|| loop {
                let index = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                let Some(fixture) = fixtures.get(index) else {
                    break;
                };
                let outcome = outcome(fixture);
                outcomes
                    .lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner)
                    .push(outcome);
            });
        }
    });
    let outcomes = outcomes
        .into_inner()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    assert_eq!(outcomes.len(), fixtures.len(), "every fixture ran");
    let replayed = outcomes.iter().filter(|outcome| outcome.replayed).count();
    report_mirror_coverage(&outcomes);
    eprintln!(
        "external-codegen consumer certificates: {replayed} replayed through CLEAN_PATH, {} supported \
         ones through pinned Carcara",
        PINNED_REPLAYS.load(std::sync::atomic::Ordering::Relaxed)
    );
    let failures: Vec<String> = outcomes
        .into_iter()
        .filter_map(|outcome| outcome.failure)
        .collect();
    assert!(
        failures.is_empty(),
        "{} of {} certificates:\n\n{}",
        failures.len(),
        fixtures.len(),
        failures.join("\n\n")
    );
}

/// The problem-surface defect: a query whose own declarations the consumer
/// cannot parse is withheld under `--strict-proofs`, with the declaration
/// named, and never published as a checkable `unsat`.
#[test]
#[timeout(300_000)]
fn strict_proofs_withhold_unsat_when_the_problem_itself_is_unparseable() {
    let mut failures = Vec::new();
    for fixture in corpus()
        .iter()
        .filter(|fixture| fixture.class.starts_with("problem-"))
    {
        let run = run_one_shot(fixture);
        let withheld = run.verdicts == ["unknown"]
            && run
                .stderr
                .contains("(:reason-unknown (incomplete proof-trusted))")
            && run.stderr.contains("the problem declares `");
        if !withheld {
            failures.push(format!(
                "expected `unknown` naming the unparseable declaration:\n{}",
                run.context
            ));
        }
        if certificate_line(&run.stderr)
            .is_some_and(|line| line.contains("carcara_surface=supported"))
        {
            failures.push(format!(
                "the certificate of an unparseable problem was disclosed supported:\n{}",
                run.context
            ));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}
