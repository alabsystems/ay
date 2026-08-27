// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Every fake checker in `ci/fake-checkers/` must be rejected, and the
//! rejection is DEMONSTRATED by running the fake.
//!
//! The gates in this workspace all end in some form of "…and VeriPB said so".
//! That sentence is worth exactly as much as the binary behind it, and five
//! separate binaries that are not proof checkers used to satisfy it:
//!
//!   (i)   `verdict-then-exit1.sh` — a REAL checker's verdict, verbatim, then
//!         exit 1. The old rule was "assert on the verdict LINE, never on exit
//!         status", so this passed everything. It is the third fake the
//!         resolver did not catch, after `/usr/bin/true` and `/usr/bin/false`.
//!   (ii)  `silent-exit0.sh` — prints nothing, exits 0.
//!   (iii) `always-unsat.sh` — `s VERIFIED UNSATISFIABLE` for every input,
//!         including satisfiable ones.
//!   (iv)  `parrot.sh` — reads the conclusion the PROOF claims and echoes back
//!         the matching verdict. It "confirms" whatever the caller hoped for,
//!         so exact-conclusion matching does not touch it; only a probe whose
//!         proof states a FALSE conclusion does.
//!   (v)   `comment-verified.sh` — REFUSES the proof (`s NOT VERIFIED`) while
//!         printing the accepting words in a `c` comment above the verdict, and
//!         exits 0. It is the only fake here that is caught by NOTHING about
//!         its verdict or its exit status: both say "refused". It exists
//!         because `veripb_runner::verify_unsat` decided acceptance with
//!         `stdout.contains("VERIFIED UNSATISFIABLE")`, so this fake's REFUSAL
//!         was read as a verification — the one failure mode a verification
//!         path must never have.
//!
//! All five answer `--version` with `veripb 3.0.2`, so the version half of
//! `ci/veripb.pin` cannot distinguish them either. Behaviour is the only
//! identity check that works, which is what [`veripb::self_test`] is.
//!
//! This suite is the Rust half of the demonstration; `scripts/ci/veripb_fake_checker_gate.sh`
//! is the shell half and runs the same five fakes through every shell gate.
//! The `ay-pb-dev certify-unsat --veripb` surface is covered behaviourally by
//! `ay_pb_core::veripb_runner`'s own tests (it is compiled only under `dev-tools`)
//! and structurally by `certify_unsat_cannot_obtain_a_checker_without_self_testing_it`
//! below, which runs unconditionally.

use std::fs;
use std::path::{Path, PathBuf};

use ay_test_support::veripb::{self, pin, Expect};

const SUITE: &str = "ay-pb::veripb_fake_checker_gate";

/// (script, needs a real checker to delegate to)
const FAKES: [(&str, bool); 5] = [
    ("verdict-then-exit1.sh", true),
    ("silent-exit0.sh", false),
    ("always-unsat.sh", false),
    ("parrot.sh", false),
    ("comment-verified.sh", false),
];

fn fake_dir() -> PathBuf {
    pin::repo_root().join("ci/fake-checkers")
}

/// Wrap `fake` in a shim that supplies the delegate environment, so the fake
/// can be handed to APIs that take only a path. Writing a shim beats mutating
/// this process's environment, which is racy across parallel tests.
fn shim_for(fake: &str, needs_delegate: bool, real: &Path, scratch: &Path) -> PathBuf {
    let target = fake_dir().join(fake);
    assert!(
        target.is_file(),
        "committed fake checker is missing: {}",
        target.display()
    );
    let shim = scratch.join(format!("shim-{fake}"));
    let delegate = if needs_delegate {
        format!("AY_FAKE_VERIPB_DELEGATE={} ", real.display())
    } else {
        String::new()
    };
    fs::write(
        &shim,
        format!("#!/bin/sh\n{delegate}exec {} \"$@\"\n", target.display()),
    )
    .expect("write fake-checker shim");
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(&shim, fs::Permissions::from_mode(0o755)).expect("chmod shim");
    }
    shim
}

fn scratch_dir(label: &str) -> PathBuf {
    let directory = std::env::temp_dir().join(format!(
        "ay-fake-checker-{label}-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|elapsed| elapsed.as_nanos())
            .unwrap_or(0)
    ));
    fs::create_dir_all(&directory).expect("create scratch directory");
    directory
}

/// The headline: not one of the four survives the self-test battery.
#[cfg(unix)]
#[test]
fn no_fake_checker_passes_the_self_test() {
    let Some(real) = veripb::require_checker(SUITE) else {
        return;
    };
    let scratch = scratch_dir("selftest");

    let mut survivors = Vec::new();
    for (fake, needs_delegate) in FAKES {
        let shim = shim_for(fake, needs_delegate, &real, &scratch);
        match veripb::self_test(&shim) {
            Ok(()) => survivors.push(fake),
            Err(reason) => println!("   rejected {fake}: {reason}"),
        }
    }

    let _ = fs::remove_dir_all(&scratch);
    assert!(
        survivors.is_empty(),
        "{SUITE}: {} fake checker(s) passed the self-test and would be trusted to \
         certify AY's answers: {survivors:?}. Every gate in this workspace is only \
         as sound as this battery.",
        survivors.len()
    );
}

/// The real checker must still pass, or the battery above proves nothing —
/// a self-test that rejects everything is as useless as one that accepts
/// everything.
#[test]
fn the_real_checker_passes_the_self_test() {
    let Some(real) = veripb::require_checker(SUITE) else {
        return;
    };
    veripb::self_test(&real).unwrap_or_else(|reason| {
        panic!(
            "{SUITE}: the resolved checker {} failed its own self-test: {reason}",
            real.display()
        )
    });
}

/// Fake (i) specifically: its verdict LINE is correct — it comes from a real
/// checker — and the ONLY thing wrong is the exit code. This pins that the
/// exit code is now part of acceptance, which is the rule that changed.
#[cfg(unix)]
#[test]
fn a_correct_verdict_with_a_failing_exit_code_is_rejected() {
    let Some(real) = veripb::require_checker(SUITE) else {
        return;
    };
    let scratch = scratch_dir("exit1");
    let shim = shim_for("verdict-then-exit1.sh", true, &real, &scratch);

    let opb = "* #variable= 1 #constraint= 2\n+1 x1 >= 1 ;\n-1 x1 >= 0 ;\n";
    let proof = "pseudo-Boolean proof version 3.0\nf 2 ;\npol 1 2 +;\nrup >= 1 ;\noutput NONE;\nconclusion UNSAT : 4;\nend pseudo-Boolean proof;\n";

    let genuine = veripb::run_text(&real, "exit1-control", opb, proof, &[]);
    genuine.assert_verified(&Expect::UNSAT, "the control run must verify");

    let faked = veripb::run_text(&shim, "exit1-fake", opb, proof, &[]);
    assert_eq!(
        faked.verdict(),
        genuine.verdict(),
        "the fake is supposed to reprint the real checker's verdict verbatim"
    );
    assert_eq!(faked.exit_code(), Some(1), "the fake is supposed to exit 1");
    assert!(
        !faked.exit_ok(),
        "a non-zero exit must not count as a completed check"
    );
    assert!(
        faked.is_rejected(),
        "a correct verdict from a run that failed is not an acceptance: {}",
        faked.verdict_or_placeholder()
    );

    let _ = fs::remove_dir_all(&scratch);
}

/// Fake (iv) specifically: it defeats every gate that only asks "did the
/// checker confirm the conclusion we expected", because it confirms whatever
/// the proof claims. What kills it is a proof that claims something FALSE —
/// here, `conclusion SAT` with an assignment that falsifies the formula.
#[cfg(unix)]
#[test]
fn the_parrot_agrees_with_a_true_claim_and_is_caught_by_a_false_one() {
    let Some(real) = veripb::require_checker(SUITE) else {
        return;
    };
    let scratch = scratch_dir("parrot");
    let shim = shim_for("parrot.sh", false, &real, &scratch);

    let sat_opb = "* #variable= 2 #constraint= 1\n+1 x1 +1 x2 >= 1 ;\n";
    let true_sat = "pseudo-Boolean proof version 3.0\nf 1 ;\noutput NONE;\nconclusion SAT : x1 ~x2;\nend pseudo-Boolean proof;\n";
    let false_sat = "pseudo-Boolean proof version 3.0\nf 1 ;\noutput NONE;\nconclusion SAT : ~x1 ~x2;\nend pseudo-Boolean proof;\n";

    // On a TRUE claim it is indistinguishable from a real checker. This is the
    // half that makes it dangerous, and it is asserted, not assumed.
    let agreeable = veripb::run_text(&shim, "parrot-true", sat_opb, true_sat, &[]);
    agreeable.assert_verified(
        &Expect::SAT,
        "the parrot passes an exact-conclusion gate on a true claim",
    );

    // On a FALSE claim it agrees just as readily, and the real checker does not.
    let control = veripb::run_text(&real, "parrot-control", sat_opb, false_sat, &[]);
    control.assert_rejected("the real checker must reject a falsifying SAT claim");

    let lying = veripb::run_text(&shim, "parrot-false", sat_opb, false_sat, &[]);
    assert!(
        lying.is_verified(),
        "the parrot is supposed to rubber-stamp the false claim too: {}",
        lying.verdict_or_placeholder()
    );
    assert!(
        veripb::self_test(&shim).is_err(),
        "the self-test battery must therefore reject the parrot"
    );

    let _ = fs::remove_dir_all(&scratch);
}

/// Fake (v) specifically: the SUBSTRING hazard, demonstrated on the committed
/// artifact rather than asserted.
///
/// This fake needs no real checker to be dangerous and none to be caught, so
/// unlike its four siblings this test runs on a host with no VeriPB installed
/// — which is exactly where a substring reader would rot unnoticed.
///
/// Three facts have to hold together for the fixture to mean anything, and all
/// three are asserted: it EXITS 0 (so the exit-status half of the acceptance
/// contract is satisfied and cannot be what rejects it), its verdict line is a
/// REFUSAL, and its stdout nevertheless carries the exact substring that used
/// to be the whole acceptance test in
/// `crates/ay-pb-core/src/veripb_runner.rs`.
#[cfg(unix)]
#[test]
fn a_refusal_that_mentions_the_accepting_words_is_still_a_refusal() {
    let fake = fake_dir().join("comment-verified.sh");
    assert!(
        fake.is_file(),
        "committed fake checker is missing: {}",
        fake.display()
    );

    let opb = "* #variable= 1 #constraint= 2\n+1 x1 >= 1 ;\n-1 x1 >= 0 ;\n";
    let proof = "pseudo-Boolean proof version 3.0\nf 2 ;\npol 1 2 +;\nrup >= 1 ;\noutput NONE;\nconclusion UNSAT : 4;\nend pseudo-Boolean proof;\n";
    let run = veripb::run_text(&fake, "comment-verified", opb, proof, &[]);

    assert!(
        run.exit_ok(),
        "the fake must exit 0, or the exit-status half of the contract is what \
         catches it and the substring hazard goes untested: {:?}",
        run.exit_code()
    );
    assert!(
        run.stdout().contains("VERIFIED UNSATISFIABLE"),
        "anti-vacuity: the fake must carry the substring that used to be the \
         whole acceptance test; got {:?}",
        run.stdout()
    );
    assert_eq!(
        run.verdict(),
        Some("s NOT VERIFIED"),
        "the fake's verdict LINE must be a refusal"
    );
    assert!(
        run.is_rejected(),
        "a refusal that merely mentions the accepting words is a refusal: {}",
        run.verdict_or_placeholder()
    );
    assert!(
        veripb::self_test(&fake).is_err(),
        "the self-test battery must reject it too"
    );
}

/// `ay-pb-dev certify-unsat --veripb` is the one surface here that takes a
/// checker PATH FROM THE USER, and it is the surface this suite could not
/// reach: `ay_pb::veripb_runner` is compiled only under `dev-tools` /
/// `certified-proof-artifacts`, so the behavioural battery for it lives in
/// `crates/ay-pb-core/src/veripb_runner.rs`'s own tests
/// (`self_test_rejects_every_committed_fake_checker`), which run under those
/// features. What runs HERE, unconditionally, is the structural claim that
/// makes those tests load-bearing: that the self-test is actually WIRED IN, and
/// that there is no way to obtain a `CertifyConfig` without passing it.
///
/// Measured, before this was wired: `ay-pb-dev certify-unsat trivial-unsat.opb
/// --veripb ci/fake-checkers/always-unsat.sh` printed
/// `VERIFICATION CAMPAIGN: 1/1 VERIFIED_UNSATISFIABLE` and exited 0, and
/// `parrot.sh` did the same. Neither is a proof checker. The sha256 pin saw
/// nothing wrong, because a pin fixes WHICH bytes ran, not what they do.
#[test]
fn certify_unsat_cannot_obtain_a_checker_without_self_testing_it() {
    let path = pin::repo_root().join("crates/ay-pb/src/bin/dev.rs");
    let source = fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("read {}: {error}", path.display()));

    let start = source
        .find("fn cert_config(")
        .expect("dev.rs must still have a cert_config");
    let body = &source[start..];
    let probe = body.find("veripb_runner::self_test(").expect(
        "cert_config must self-test the checker before returning a CertifyConfig. \
             Without it, ci/fake-checkers/always-unsat.sh and parrot.sh both drive this \
             command to `VERIFICATION CAMPAIGN: 1/1 VERIFIED_UNSATISFIABLE`, exit 0.",
    );
    let build = body
        .find("Ok(CertifyConfig {")
        .expect("cert_config must still construct a CertifyConfig");
    assert!(
        probe < build,
        "the self-test must run BEFORE the CertifyConfig is built, not after"
    );

    // The chokepoint claim. `CertifyConfig` is the only thing `certify_files`
    // accepts, so if it has exactly one construction site and that site
    // self-tests, then every certify-* subcommand self-tests. Two matches:
    // the struct definition and that one site.
    assert_eq!(
        source.matches("CertifyConfig {").count(),
        2,
        "a second CertifyConfig construction site would be a certification path \
         that bypasses the self-test"
    );
}
