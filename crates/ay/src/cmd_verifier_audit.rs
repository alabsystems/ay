// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `ay verifier-audit`: an honest readiness gate for using AY as the single SMT
//! backend behind Rust deductive verifiers — **Creusot** (Rust → WhyML → Why3 →
//! SMT) and **Verus** (Rust → AIR → SMT-LIB → Z3) — in place of the engines they
//! drive today (Z3, CVC5, Alt-Ergo).
//!
//! Unlike `ay z3-audit` (a broad Z3 CLI/parity gate), this command probes the
//! *concrete backend-interface surfaces a Rust verifier exercises*: the SMT-LIB
//! option namespace those tools set, `:pattern`/`:qid`/`:weight` trigger
//! annotations, `:named` + `(get-unsat-core)` goal tracking, quantifier
//! E-matching / MBQI, the axiomatized-recursive-function encoding, datatypes
//! (incl. parametric), bitvectors (Verus `bit_vector`), nonlinear arithmetic
//! (Verus `nonlinear_arith` / Creusot reals), arrays/maps, incremental
//! `push`/`pop`, and AY's differentiating proof-carrying certificate.
//!
//! It is a *characterization* gate: every probe records whether the surface is
//! `Ready` (works today), a tracked `Gap` (a documented current limitation with
//! a workaround), or a `Regression` (a surface that used to work and no longer
//! does). The exit code fails only on regressions by default, so the command
//! doubles as a CI guard; `--strict` also fails while any gap remains, tracking
//! the "fully replace" bar. Machine-readable findings can be written with
//! `--json`.

use std::path::{Path, PathBuf};
use std::process::{Command as ProcessCommand, Stdio};
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

use anyhow::{Context, Result};
use clap::{Args, ValueEnum};

/// Which consumer's backend surfaces to audit.
#[derive(Clone, Copy, Debug, Eq, PartialEq, ValueEnum)]
pub(crate) enum Consumer {
    /// Audit every surface (default).
    All,
    /// Surfaces exercised by Creusot (via Why3): quantified UF+arith, datatypes
    /// (incl. parametric), arrays/maps, axiomatized recursion, unsat cores.
    Creusot,
    /// Surfaces exercised by Verus (direct-to-Z3): trigger annotations, option
    /// namespace, bitvectors, nonlinear arithmetic, incremental solving.
    Verus,
    /// Surfaces exercised by the Why3 driver interface itself: option/`get-info`
    /// handshake, `:reason-unknown`, named-goal unsat cores.
    Why3,
}

impl Consumer {
    fn as_str(self) -> &'static str {
        match self {
            Self::All => "all",
            Self::Creusot => "creusot",
            Self::Verus => "verus",
            Self::Why3 => "why3",
        }
    }
}

#[derive(Args)]
#[command(after_help = "\
This is a backend-readiness characterization gate, not a benchmark runner. It
drives the running `ay` binary on an embedded battery of probes shaped like real
Creusot/Why3 and Verus solver output, and reports each backend surface as Ready,
a tracked Gap, or a Regression. By default it exits non-zero only on a
regression (a surface that used to work). Use `--strict` to also fail while any
tracked gap remains (the 'fully replace' bar), and `--json` to preserve the
complete surface table as machine-readable evidence.")]
pub(crate) struct VerifierAuditArgs {
    /// Consumer whose backend surfaces to audit.
    #[arg(long, value_enum, default_value_t = Consumer::All)]
    consumer: Consumer,

    /// `ay` binary to drive. Defaults to the running executable.
    #[arg(long)]
    ay: Option<PathBuf>,

    /// Also fail (exit non-zero) while any tracked gap remains, not just on regressions.
    #[arg(long)]
    strict: bool,

    /// Per-probe timeout in milliseconds.
    #[arg(long, default_value_t = 15_000)]
    per_probe_timeout_ms: u64,

    /// Print each probe's captured output.
    #[arg(long)]
    verbose: bool,

    /// Write a machine-readable ay-verifier-backend-audit/v1 JSON report.
    #[arg(long, value_name = "FILE")]
    json: Option<PathBuf>,
}

/// What a probe is expected to demonstrate.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Expect {
    /// A decided `unsat` (with any `requires` tokens present).
    Unsat,
    /// A decided `sat` (with any `requires` tokens present).
    Sat,
    /// Accepted and decided (`sat` or `unsat`), no `(error ...)`.
    Accepts,
    /// A currently-documented limitation whose signature (`requires`) is expected.
    KnownGap,
    /// AY's differentiator: emits a machine-checkable Alethe certificate on unsat.
    ProofCarrying,
}

struct Probe {
    id: &'static str,
    surface: &'static str,
    consumers: &'static [Consumer],
    smt2: &'static str,
    expect: Expect,
    /// Substrings that must appear in the combined output for the probe to pass
    /// (for `KnownGap`, the current-limitation signature).
    requires: &'static [&'static str],
    /// Human note: for gaps, the limitation + workaround; else why it matters.
    note: &'static str,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Status {
    Ready,
    Gap,
    GapClosed,
    Regression,
}

impl Status {
    fn glyph(self) -> &'static str {
        match self {
            Self::Ready => "READY",
            Self::Gap => "GAP",
            Self::GapClosed => "GAP-CLOSED",
            Self::Regression => "REGRESSION",
        }
    }
}

/// The embedded probe battery. Every probe is a real SMT-LIB fragment shaped
/// like Creusot/Why3 or Verus solver output; expectations were established by
/// running the fragment through `ay` and recorded here.
const PROBES: &[Probe] = &[
    Probe {
        id: "driver-handshake",
        surface: "driver handshake: Z3/Verus option namespace + get-info + get-value",
        consumers: &[Consumer::Why3, Consumer::Verus],
        smt2: "(set-option :auto_config false)\n(set-option :smt.mbqi false)\n(set-option :smt.case_split 3)\n(set-option :smt.qi.eager_threshold 100.0)\n(set-option :timeout 5000)\n(set-option :rlimit 2000000)\n(set-option :smt.arith.solver 2)\n(set-option :model.compact true)\n(set-option :smt.random_seed 7)\n(set-option :produce-models true)\n(get-info :name)\n(get-info :version)\n(set-logic QF_UFLIA)\n(declare-fun x () Int) (declare-fun y () Int)\n(assert (= (+ x y) 10)) (assert (= x 4))\n(check-sat)\n(get-value (x y))\n",
        expect: Expect::Accepts,
        requires: &["(:version", "((x 4) (y 6))"],
        note: "Why3/Verus set a wide Z3 option namespace and probe get-info before solving; AY must accept every option without erroring and answer get-info/get-value.",
    },
    Probe {
        id: "quant-ematch-inductive",
        surface: "quantified E-matching over UF (inductive goal) + named unsat core",
        consumers: &[Consumer::Why3, Consumer::Creusot, Consumer::Verus],
        smt2: "(set-info :smt-lib-version 2.6)\n(set-option :produce-unsat-cores true)\n(set-logic AUFLIA)\n(declare-fun inv (Int) Bool)\n(assert (! (forall ((k Int)) (=> (inv k) (inv (+ k 1)))) :named H_step))\n(assert (! (inv 0) :named H_init))\n(assert (! (not (inv 3)) :named goal))\n(check-sat)\n(get-unsat-core)\n",
        expect: Expect::Unsat,
        requires: &["H_step"],
        note: "The core Creusot/Why3 workload: discharge a goal from quantified hypotheses via trigger E-matching, and report which named goals form the core.",
    },
    Probe {
        id: "trigger-annotations",
        surface: "trigger annotations: :pattern (multi-pattern), :qid, :weight",
        consumers: &[Consumer::Verus],
        smt2: "(set-logic UFLIA)\n(declare-fun f (Int) Int)\n(declare-fun g (Int) Int)\n(assert (! (forall ((x Int)) (! (= (f (g x)) x) :pattern ((f (g x))) :qid ax_fg :weight 1)) :named ax))\n(assert (not (= (f (g 7)) 7)))\n(check-sat)\n",
        expect: Expect::Unsat,
        requires: &[],
        note: "Verus tunes proofs to Z3's trigger semantics; AY must parse and honor user :pattern/:qid/:weight annotations for instantiation.",
    },
    Probe {
        id: "quant-sat-model",
        surface: "quantifier SAT + model synthesis (MBQI)",
        consumers: &[Consumer::All],
        smt2: "(set-logic UFLIA)\n(set-option :produce-models true)\n(declare-fun p (Int) Bool)\n(assert (forall ((x Int)) (=> (> x 0) (p x))))\n(assert (p 0))\n(check-sat)\n(get-model)\n",
        expect: Expect::Sat,
        requires: &["(model"],
        note: "Counterexample reporting needs a model for satisfiable quantified goals; AY must answer sat and synthesize an interpretation.",
    },
    Probe {
        id: "axiomatized-recursion",
        surface: "axiomatized recursive spec function (uninterpreted fn + defining axiom)",
        consumers: &[Consumer::Creusot, Consumer::Verus],
        smt2: "(set-logic AUFDTLIA)\n(declare-datatypes ((IntList 0)) (((nil) (cons (head Int) (tail IntList)))))\n(declare-fun len (IntList) Int)\n(assert (= (len nil) 0))\n(assert (! (forall ((h Int) (t IntList)) (! (= (len (cons h t)) (+ 1 (len t))) :pattern ((len (cons h t))))) :named len_def))\n(assert (not (= (len (cons 1 (cons 2 nil))) 2)))\n(check-sat)\n",
        expect: Expect::Unsat,
        requires: &[],
        note: "How Creusot(#[logic]) and Verus(spec fn) actually feed recursion to a solver: an uninterpreted function plus a triggered defining axiom. AY discharges this by E-matching.",
    },
    Probe {
        id: "define-fun-rec",
        surface: "SMT-LIB define-fun-rec / define-funs-rec with symbolic recursion",
        consumers: &[Consumer::Why3, Consumer::Verus],
        smt2: "(set-logic ALL)\n(declare-datatypes ((IntList 0)) (((nil) (cons (head Int) (tail IntList)))))\n(define-fun-rec len ((l IntList)) Int\n  (match l ((nil 0) ((cons h t) (+ 1 (len t))))))\n(declare-const xs IntList)\n(assert (= xs (cons 1 (cons 2 nil))))\n(assert (not (= (len xs) 2)))\n(check-sat)\n",
        expect: Expect::KnownGap,
        requires: &["(error"],
        note: "GAP: AY eagerly unfolds a recursive define-fun-rec over symbolic arguments until a recursion-depth error, instead of axiomatizing it. Workaround: emit recursion as an uninterpreted fn + quantified defining axiom (see axiomatized-recursion). Why3 and Verus already prefer the axiom encoding, so this bites only direct define-fun-rec consumers.",
    },
    Probe {
        id: "parametric-datatypes",
        surface: "parametric / polymorphic datatypes (par ...)",
        consumers: &[Consumer::Creusot],
        smt2: "(set-logic ALL)\n(declare-datatypes ((Opt 1)) ((par (T) ((none) (some (val T))))))\n(declare-const o (Opt Int))\n(assert (= o (some 3)))\n(assert (= (val o) 4))\n(check-sat)\n",
        expect: Expect::Unsat,
        requires: &[],
        note: "Creusot's WhyML types are polymorphic (Rust generics). AY parses and solves (par ...) datatypes as long as no recursive define-fun-rec is layered on top.",
    },
    Probe {
        id: "bitvectors",
        surface: "bitvectors (Verus bit_vector mode / Creusot machine-int bitops)",
        consumers: &[Consumer::Verus, Consumer::Creusot],
        smt2: "(set-logic QF_BV)\n(declare-const a (_ BitVec 32))\n(declare-const b (_ BitVec 32))\n(assert (= (bvadd a b) (bvadd b a)))\n(assert (not (= (bvand a b) (bvand b a))))\n(check-sat)\n",
        expect: Expect::Unsat,
        requires: &[],
        note: "Verus bit_vector mode bit-blasts to QF_BV; AY's bit-blaster decides it (and can emit a bit-blast/Lean certificate).",
    },
    Probe {
        id: "nonlinear-arith",
        surface: "nonlinear integer arithmetic (Verus nonlinear_arith / Creusot mul)",
        consumers: &[Consumer::Verus, Consumer::Creusot],
        smt2: "(set-logic QF_NIA)\n(declare-const x Int) (declare-const y Int)\n(assert (> x 1)) (assert (> y 1))\n(assert (= (* x y) 6))\n(check-sat)\n(get-model)\n",
        expect: Expect::Sat,
        requires: &["(model"],
        note: "Verus nonlinear_arith and Creusot reals lean on nonlinear reasoning. AY decides bounded/structured instances but is not a full nlsat; hard nonlinear goals fall to sound unknown (see plan doc).",
    },
    Probe {
        id: "arrays-maps",
        surface: "arrays: select-over-store (Creusot maps / Verus vstd Map & Seq models)",
        consumers: &[Consumer::Creusot, Consumer::Verus],
        smt2: "(set-logic QF_AUFLIA)\n(declare-const a (Array Int Int))\n(declare-const i Int) (declare-const v Int)\n(assert (not (= (select (store a i v) i) v)))\n(check-sat)\n",
        expect: Expect::Unsat,
        requires: &[],
        note: "Creusot maps and parts of Verus vstd model over the array theory; AY decides read-over-write and extensionality.",
    },
    Probe {
        id: "incremental",
        surface: "incremental push/pop + get-value across scopes",
        consumers: &[Consumer::Verus, Consumer::Why3],
        smt2: "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (> x 0))\n(push 1)\n(assert (< x 0))\n(check-sat)\n(pop 1)\n(check-sat)\n(assert (< x 5))\n(check-sat)\n(get-value (x))\n",
        expect: Expect::Accepts,
        requires: &["((x 1))"],
        note: "Verus drives one incremental Z3 process per module; AY must honor push/pop scoping and answer get-value in the current scope.",
    },
    Probe {
        id: "reason-unknown",
        surface: "(get-info :reason-unknown) fidelity",
        consumers: &[Consumer::Why3],
        smt2: "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (= x 1))\n(check-sat)\n(get-info :reason-unknown)\n",
        expect: Expect::KnownGap,
        requires: &["state of the most recent check-sat"],
        note: "GAP: AY returns a fixed placeholder for (get-info :reason-unknown) regardless of the last result. Why3 parses :reason-unknown to classify prover status; AY should return an empty/typed reason after a decided answer and a genuine incompleteness reason after unknown.",
    },
    Probe {
        id: "proof-carrying",
        surface: "proof-carrying Alethe certificate on UNSAT (AY differentiator)",
        consumers: &[Consumer::Creusot, Consumer::Why3, Consumer::Verus],
        smt2: "(set-logic QF_UF)\n(declare-sort U 0)\n(declare-const a U) (declare-const b U) (declare-const c U)\n(assert (= a b)) (assert (= b c)) (assert (not (= a c)))\n(check-sat)\n",
        expect: Expect::ProofCarrying,
        requires: &["(step", "(cl)"],
        note: "DIFFERENTIATOR: every AY unsat can export a machine-checkable Alethe certificate (checkable by Carcara/Lean). Z3 and Alt-Ergo do not; this turns 'trust the solver' into 'check the proof' — a direct upgrade for Creusot/Why3.",
    },
];

fn probe_applies(probe: &Probe, consumer: Consumer) -> bool {
    consumer == Consumer::All
        || probe.consumers.contains(&Consumer::All)
        || probe.consumers.contains(&consumer)
}

enum Captured {
    Done { stdout: String, stderr: String },
    TimedOut,
}

/// A per-process temp path for a probe fixture (no external tempfile crate).
fn temp_path(probe_id: &str, ext: &str) -> PathBuf {
    std::env::temp_dir().join(format!(
        "ay-verifier-{}-{}.{}",
        std::process::id(),
        probe_id,
        ext
    ))
}

/// Drive the `ay` binary on `args`, capturing output with a wall-clock backstop.
fn spawn_and_capture(ay: &Path, args: &[String], timeout: Duration) -> Result<Captured> {
    let child = ProcessCommand::new(ay)
        .args(args)
        // Suppress the provenance session banner so probe output is clean SMT-LIB.
        .env("AY_INTERNAL_PROVENANCE_CHILD", "1")
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .with_context(|| format!("spawn {}", ay.display()))?;
    let pid = child.id();
    let (tx, rx) = mpsc::channel();
    thread::spawn(move || {
        let _ = tx.send(child.wait_with_output());
    });
    match rx.recv_timeout(timeout) {
        Ok(Ok(output)) => Ok(Captured::Done {
            stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
            stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
        }),
        Ok(Err(e)) => Err(e).context("collect ay output"),
        Err(mpsc::RecvTimeoutError::Timeout) => {
            // Backstop: the wait thread still owns the child; kill by pid so it unblocks.
            let _ = ProcessCommand::new("kill")
                .arg("-9")
                .arg(pid.to_string())
                .stdout(Stdio::null())
                .stderr(Stdio::null())
                .status();
            Ok(Captured::TimedOut)
        }
        Err(mpsc::RecvTimeoutError::Disconnected) => Ok(Captured::TimedOut),
    }
}

struct ProbeOutcome {
    status: Status,
    detail: String,
    output: String,
}

fn evaluate(ay: &Path, probe: &Probe, timeout: Duration) -> ProbeOutcome {
    // Write the fragment to a temp file and drive `ay solve`.
    let smt_path = temp_path(probe.id, "smt2");
    if let Err(e) = std::fs::write(&smt_path, probe.smt2) {
        return ProbeOutcome {
            status: Status::Regression,
            detail: format!("could not write probe fixture: {e}"),
            output: String::new(),
        };
    }
    let ms = timeout.as_millis().to_string();
    let path = smt_path.to_string_lossy().into_owned();

    // The proof-carrying probe requests an explicit certificate; others suppress it.
    let proof_path: Option<PathBuf> = if probe.expect == Expect::ProofCarrying {
        Some(temp_path(probe.id, "alethe"))
    } else {
        None
    };
    let args: Vec<String> = if let Some(pp) = &proof_path {
        vec![
            "solve".into(),
            "--proof".into(),
            pp.to_string_lossy().into_owned(),
            "-t".into(),
            ms,
            path.clone(),
        ]
    } else {
        vec![
            "solve".into(),
            "--no-proof".into(),
            "-t".into(),
            ms,
            path.clone(),
        ]
    };

    // Grant the wall-clock backstop a little slack beyond ay's own -t.
    let backstop = timeout + Duration::from_secs(3);
    let captured = spawn_and_capture(ay, &args, backstop);
    // Read any emitted certificate, then clean up temp artifacts regardless of outcome.
    let cert = proof_path
        .as_ref()
        .map(|pp| std::fs::read_to_string(pp).unwrap_or_default())
        .unwrap_or_default();
    let _ = std::fs::remove_file(&smt_path);
    if let Some(pp) = &proof_path {
        let _ = std::fs::remove_file(pp);
    }

    let captured = match captured {
        Ok(c) => c,
        Err(e) => {
            return ProbeOutcome {
                status: Status::Regression,
                detail: format!("failed to run ay: {e:#}"),
                output: String::new(),
            }
        }
    };

    let (stdout, stderr) = match captured {
        Captured::TimedOut => {
            return ProbeOutcome {
                status: Status::Regression,
                detail: format!("timed out after {} ms", timeout.as_millis()),
                output: String::new(),
            }
        }
        Captured::Done { stdout, stderr } => (stdout, stderr),
    };
    let combined = format!("{stdout}\n{stderr}");

    let has_error = combined.contains("(error");
    let has_unsat = combined.lines().any(|l| l.trim() == "unsat");
    let has_sat = combined.lines().any(|l| l.trim() == "sat");
    let reqs_ok = probe.requires.iter().all(|r| combined.contains(r));
    let missing: Vec<&str> = probe
        .requires
        .iter()
        .copied()
        .filter(|r| !combined.contains(r))
        .collect();

    let status = match probe.expect {
        Expect::Unsat => {
            if has_unsat && reqs_ok {
                Status::Ready
            } else {
                Status::Regression
            }
        }
        Expect::Sat => {
            if has_sat && reqs_ok {
                Status::Ready
            } else {
                Status::Regression
            }
        }
        Expect::Accepts => {
            if !has_error && (has_sat || has_unsat) && reqs_ok {
                Status::Ready
            } else {
                Status::Regression
            }
        }
        Expect::KnownGap => {
            if reqs_ok {
                Status::Gap
            } else if (has_sat || has_unsat) && !has_error {
                // The limitation signature is gone and a real answer appeared.
                Status::GapClosed
            } else {
                Status::Gap
            }
        }
        Expect::ProofCarrying => {
            let cert_ok = probe.requires.iter().all(|r| cert.contains(r));
            if has_unsat && cert_ok && !cert.trim().is_empty() {
                Status::Ready
            } else {
                Status::Regression
            }
        }
    };

    let detail = match status {
        Status::Ready => match probe.expect {
            Expect::ProofCarrying => {
                "unsat + machine-checkable Alethe certificate emitted".to_string()
            }
            _ => "surface works".to_string(),
        },
        Status::Gap => "tracked gap present (documented limitation)".to_string(),
        Status::GapClosed => {
            "gap appears CLOSED — this surface now returns a decided answer; update the plan doc"
                .to_string()
        }
        Status::Regression => {
            let mut why = Vec::new();
            if has_error {
                why.push("unexpected (error ...)".to_string());
            }
            if !missing.is_empty() {
                why.push(format!("missing output {missing:?}"));
            }
            if !has_sat && !has_unsat && probe.expect != Expect::ProofCarrying {
                why.push("no sat/unsat verdict".to_string());
            }
            if why.is_empty() {
                why.push("expectation not met".to_string());
            }
            why.join("; ")
        }
    };

    ProbeOutcome {
        status,
        detail,
        output: combined,
    }
}

fn resolve_ay(args: &VerifierAuditArgs) -> Result<PathBuf> {
    if let Some(ay) = &args.ay {
        return Ok(ay.clone());
    }
    std::env::current_exe().context("resolve current ay executable")
}

/// Read `ay --features` for a capability header. Best-effort; never fatal.
fn features_header(ay: &Path) -> Option<(String, usize, Vec<String>)> {
    let output = ProcessCommand::new(ay)
        .arg("--features")
        .env("AY_INTERNAL_PROVENANCE_CHILD", "1")
        .output()
        .ok()?;
    let text = String::from_utf8_lossy(&output.stdout);
    let json: serde_json::Value = serde_json::from_str(text.trim()).ok()?;
    let stamp = json
        .get("build_stamp")
        .and_then(|v| v.as_str())
        .unwrap_or("unknown")
        .to_string();
    let logics = json
        .get("supported_logics")
        .and_then(|v| v.as_array())
        .map(|a| a.len())
        .unwrap_or(0);
    let formats = json
        .get("proof_formats")
        .and_then(|v| v.as_array())
        .map(|a| {
            a.iter()
                .filter_map(|v| v.as_str().map(str::to_string))
                .collect()
        })
        .unwrap_or_default();
    Some((stamp, logics, formats))
}

pub(crate) fn run(args: &VerifierAuditArgs) -> Result<i32> {
    let ay = resolve_ay(args)?;
    let timeout = Duration::from_millis(args.per_probe_timeout_ms);

    println!("ay verifier-audit — backend readiness for Creusot/Why3 & Verus");
    println!("scope: consumer={}", args.consumer.as_str());
    if let Some((stamp, logics, formats)) = features_header(&ay) {
        println!("ay:    {stamp}");
        println!(
            "       {logics} SMT logics recognized; proof formats: {}",
            formats.join(", ")
        );
    }
    println!();

    let selected: Vec<&Probe> = PROBES
        .iter()
        .filter(|p| probe_applies(p, args.consumer))
        .collect();

    let mut ready = 0usize;
    let mut gap = 0usize;
    let mut gap_closed = 0usize;
    let mut regression = 0usize;
    let mut rows = Vec::new();

    for probe in &selected {
        let outcome = evaluate(&ay, probe, timeout);
        match outcome.status {
            Status::Ready => ready += 1,
            Status::Gap => gap += 1,
            Status::GapClosed => gap_closed += 1,
            Status::Regression => regression += 1,
        }
        println!("  [{:>10}] {}", outcome.status.glyph(), probe.surface);
        println!(
            "             id={} consumers={:?}",
            probe.id,
            consumer_names(probe.consumers)
        );
        if outcome.status != Status::Ready {
            println!("             {}", outcome.detail);
        }
        if matches!(outcome.status, Status::Gap | Status::GapClosed) {
            println!("             note: {}", probe.note);
        }
        if args.verbose {
            for line in outcome.output.lines().filter(|l| !l.trim().is_empty()) {
                println!("             | {line}");
            }
        }
        rows.push(serde_json::json!({
            "id": probe.id,
            "surface": probe.surface,
            "consumers": consumer_names(probe.consumers),
            "expect": expect_name(probe.expect),
            "status": outcome.status.glyph(),
            "detail": outcome.detail,
            "note": probe.note,
        }));
    }

    let applicable = selected.len();
    println!();
    println!(
        "summary: {ready} READY, {gap} GAP, {gap_closed} GAP-CLOSED, {regression} REGRESSION (of {applicable} applicable surfaces)"
    );

    // Default verdict fails only on a regression; --strict also fails on any gap.
    let fail = regression > 0 || (args.strict && gap > 0);
    let verdict = if regression > 0 {
        "fail-regression"
    } else if args.strict && gap > 0 {
        "fail-strict-gaps-remain"
    } else if gap > 0 {
        "ready-with-tracked-gaps"
    } else {
        "ready"
    };
    println!("verdict: {verdict}");
    if regression == 0 && gap > 0 && !args.strict {
        println!(
            "(run with --strict to gate on tracked gaps; use --json to save the complete surface table)"
        );
    }

    if let Some(path) = &args.json {
        let report = serde_json::json!({
            "schema": "ay-verifier-backend-audit/v1",
            "consumer": args.consumer.as_str(),
            "verdict": verdict,
            "summary": {
                "ready": ready,
                "gap": gap,
                "gap_closed": gap_closed,
                "regression": regression,
                "applicable": applicable,
            },
            "surfaces": rows,
        });
        std::fs::write(
            path,
            format!("{}\n", serde_json::to_string_pretty(&report)?),
        )
        .with_context(|| format!("write {}", path.display()))?;
        println!("wrote {}", path.display());
    }

    Ok(if fail { 1 } else { 0 })
}

fn consumer_names(consumers: &[Consumer]) -> Vec<&'static str> {
    consumers.iter().map(|c| c.as_str()).collect()
}

fn expect_name(expect: Expect) -> &'static str {
    match expect {
        Expect::Unsat => "unsat",
        Expect::Sat => "sat",
        Expect::Accepts => "accepts",
        Expect::KnownGap => "known-gap",
        Expect::ProofCarrying => "proof-carrying",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_probe_has_stable_metadata() {
        for probe in PROBES {
            assert!(!probe.id.is_empty(), "probe id must be set");
            assert!(
                !probe.surface.is_empty(),
                "surface must be set for {}",
                probe.id
            );
            assert!(
                !probe.consumers.is_empty(),
                "consumers must be set for {}",
                probe.id
            );
            assert!(!probe.note.is_empty(), "note must be set for {}", probe.id);
            assert!(
                probe.smt2.contains("(check-sat)"),
                "probe {} must issue check-sat",
                probe.id
            );
            if probe.expect == Expect::KnownGap {
                assert!(
                    !probe.requires.is_empty(),
                    "known-gap probe {} must record its limitation signature",
                    probe.id
                );
            }
        }
    }

    #[test]
    fn probe_ids_are_unique() {
        let mut ids: Vec<&str> = PROBES.iter().map(|p| p.id).collect();
        ids.sort_unstable();
        let before = ids.len();
        ids.dedup();
        assert_eq!(before, ids.len(), "probe ids must be unique");
    }

    #[test]
    fn consumer_filter_selects_relevant_probes() {
        let verus: Vec<&str> = PROBES
            .iter()
            .filter(|p| probe_applies(p, Consumer::Verus))
            .map(|p| p.id)
            .collect();
        assert!(verus.contains(&"trigger-annotations"));
        assert!(verus.contains(&"bitvectors"));
        // A Creusot-only surface must not appear under the Verus scope.
        assert!(!verus.contains(&"parametric-datatypes"));
    }

    #[test]
    fn all_scope_includes_everything() {
        let all = PROBES
            .iter()
            .filter(|p| probe_applies(p, Consumer::All))
            .count();
        assert_eq!(all, PROBES.len());
    }
}
