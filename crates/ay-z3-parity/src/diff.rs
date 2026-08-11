// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `diff` subcommand — audits behavioral agreement by differential testing.
//!
//! Each `.smt2` file is run through BOTH libraries via
//! `Z3_eval_smtlib2_string`. We extract the ordered `sat`/`unsat`/`unknown`
//! verdict tokens from each output and compare them. The only outcome that
//! fails the build is a `sat`-vs-`unsat` DISAGREEment — a soundness bug for
//! AY's replacement target. `unknown` from AY where libz3 decided is
//! incompleteness, reported but not a failure.

use std::ffi::{CStr, CString};
use std::path::{Path, PathBuf};
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

use crate::loader::{self, SolverApi};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Verdict {
    Sat,
    Unsat,
    Unknown,
}

impl Verdict {
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            Verdict::Sat => "sat",
            Verdict::Unsat => "unsat",
            Verdict::Unknown => "unknown",
        }
    }
}

/// Result of running one script through one solver.
enum Outcome {
    /// Ordered verdict tokens, one per `(check-sat)`.
    Verdicts(Vec<Verdict>),
    /// The evaluation exceeded the per-file timebox.
    Timeout,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Category {
    AgreeSat,
    AgreeUnsat,
    AgreeUnknown,
    AgreeMixed,
    /// AY answered `unknown` where libz3 decided — incompleteness, not a bug.
    AyIncomplete,
    /// AY decided where libz3 answered `unknown` — AY is strictly stronger here.
    AyStronger,
    /// The two solvers produced a different number of verdicts.
    CountMismatch,
    /// One or both solvers timed out.
    Timeout,
    /// Neither solver produced any verdict (e.g. no `(check-sat)`).
    NoVerdict,
    /// `sat` vs `unsat` — a SOUNDNESS BUG. Must be zero.
    Disagree,
}

impl Category {
    fn label(self) -> &'static str {
        match self {
            Category::AgreeSat => "AGREE-sat",
            Category::AgreeUnsat => "AGREE-unsat",
            Category::AgreeUnknown => "AGREE-unknown",
            Category::AgreeMixed => "AGREE-mixed",
            Category::AyIncomplete => "AY-unknown-z3-decided",
            Category::AyStronger => "AY-decided-z3-unknown",
            Category::CountMismatch => "COUNT-MISMATCH",
            Category::Timeout => "TIMEOUT",
            Category::NoVerdict => "NO-VERDICT",
            Category::Disagree => "DISAGREE",
        }
    }

    fn is_agree(self) -> bool {
        matches!(
            self,
            Category::AgreeSat
                | Category::AgreeUnsat
                | Category::AgreeUnknown
                | Category::AgreeMixed
        )
    }
}

struct FileResult {
    file: PathBuf,
    ay: Outcome,
    z3: Outcome,
    category: Category,
}

/// Extract the ordered verdict tokens from a solver's textual output.
///
/// We split on any non-alphanumeric byte and match whole words, so `unsat`
/// never falsely matches the `sat` substring, and model/`(error ...)` text
/// contributes no false verdicts.
pub(crate) fn verdicts_of(output: &str) -> Vec<Verdict> {
    output
        .split(|c: char| !c.is_ascii_alphanumeric())
        .filter_map(|w| match w {
            "sat" => Some(Verdict::Sat),
            "unsat" => Some(Verdict::Unsat),
            "unknown" => Some(Verdict::Unknown),
            _ => None,
        })
        .collect()
}

/// Run one script through one solver end-to-end: fresh config + context, eval,
/// copy the output string out, then tear the context down. The output is
/// copied BEFORE `Z3_del_context` because the returned `Z3_string` is owned by
/// the context.
fn run_script(api: SolverApi, script: &str) -> String {
    let Ok(cscript) = CString::new(script) else {
        // Interior NUL byte — cannot be a valid SMT-LIB2 script.
        return String::new();
    };
    // SAFETY: `api` holds valid function pointers into a still-loaded Z3-ABI
    // library; each is called at its declared signature and the context is
    // created and destroyed within this call.
    unsafe {
        let cfg = (api.mk_config)();
        let ctx = (api.mk_context)(cfg);
        let out_ptr = (api.eval)(ctx, cscript.as_ptr());
        let out = if out_ptr.is_null() {
            String::new()
        } else {
            CStr::from_ptr(out_ptr).to_string_lossy().into_owned()
        };
        (api.del_context)(ctx);
        (api.del_config)(cfg);
        out
    }
}

/// Run a script with a hard wall-clock timebox. On timeout the worker thread is
/// abandoned (the blocking C call cannot be safely interrupted); the library
/// stays loaded for the rest of the run so the leaked thread remains valid.
fn eval_timeboxed(api: SolverApi, script: &str, timeout: Duration) -> Outcome {
    let (tx, rx) = mpsc::channel();
    let owned = script.to_string();
    thread::spawn(move || {
        let out = run_script(api, &owned);
        let _ = tx.send(out);
    });
    match rx.recv_timeout(timeout) {
        Ok(out) => Outcome::Verdicts(verdicts_of(&out)),
        Err(_) => Outcome::Timeout,
    }
}

/// Classify one file's paired outcomes. `ay` is the library under test, `z3`
/// the reference.
fn categorize(ay: &Outcome, z3: &Outcome) -> Category {
    let (av, zv) = match (ay, z3) {
        (Outcome::Timeout, _) | (_, Outcome::Timeout) => return Category::Timeout,
        (Outcome::Verdicts(a), Outcome::Verdicts(z)) => (a, z),
    };
    if av.is_empty() && zv.is_empty() {
        return Category::NoVerdict;
    }

    let n = av.len().max(zv.len());
    let mut worst = Category::AgreeSat; // provisional; upgraded below
    let mut saw_sat = false;
    let mut saw_unsat = false;
    let mut saw_unknown = false;
    let mut agreed_all = true;

    for i in 0..n {
        match (av.get(i), zv.get(i)) {
            (Some(Verdict::Sat), Some(Verdict::Unsat))
            | (Some(Verdict::Unsat), Some(Verdict::Sat)) => return Category::Disagree,
            (Some(a), Some(z)) if a == z => match a {
                Verdict::Sat => saw_sat = true,
                Verdict::Unsat => saw_unsat = true,
                Verdict::Unknown => saw_unknown = true,
            },
            (Some(Verdict::Unknown), Some(_)) => {
                agreed_all = false;
                worst = escalate(worst, Category::AyIncomplete);
            }
            (Some(_), Some(Verdict::Unknown)) => {
                agreed_all = false;
                worst = escalate(worst, Category::AyStronger);
            }
            _ => {
                // One side produced fewer verdicts than the other.
                agreed_all = false;
                worst = escalate(worst, Category::CountMismatch);
            }
        }
    }

    if agreed_all {
        if saw_unknown {
            Category::AgreeUnknown
        } else if saw_sat && !saw_unsat {
            Category::AgreeSat
        } else if saw_unsat && !saw_sat {
            Category::AgreeUnsat
        } else {
            Category::AgreeMixed
        }
    } else {
        worst
    }
}

/// Pick the more severe of two non-agree categories.
fn escalate(a: Category, b: Category) -> Category {
    fn rank(c: Category) -> u8 {
        match c {
            Category::CountMismatch => 3,
            Category::AyIncomplete => 2,
            Category::AyStronger => 1,
            _ => 0,
        }
    }
    if rank(b) > rank(a) {
        b
    } else {
        a
    }
}

/// Recursively collect `.smt2` files from the given paths (files or dirs).
pub(crate) fn collect_smt2(paths: &[PathBuf]) -> Vec<PathBuf> {
    let mut out = Vec::new();
    for p in paths {
        collect_into(p, &mut out);
    }
    out.sort();
    out
}

fn collect_into(path: &Path, out: &mut Vec<PathBuf>) {
    if path.is_dir() {
        if let Ok(entries) = std::fs::read_dir(path) {
            for e in entries.flatten() {
                collect_into(&e.path(), out);
            }
        }
    } else if path.extension().and_then(|e| e.to_str()) == Some("smt2") {
        out.push(path.to_path_buf());
    }
}

/// Run the `diff` proof. Returns the process exit code: non-zero iff any file
/// DISAGREEs (`sat` vs `unsat`).
pub(crate) fn run(
    ay_path: &Path,
    z3_path: &Path,
    corpus: &[PathBuf],
    timeout_secs: u64,
    json: bool,
) -> i32 {
    let files = collect_smt2(corpus);
    if files.is_empty() {
        eprintln!("error: no .smt2 files found under {corpus:?}");
        return 2;
    }

    let ay_lib = match loader::open_local(ay_path) {
        Ok(l) => l,
        Err(e) => {
            eprintln!("error: {e}");
            return 2;
        }
    };
    let z3_lib = match loader::open_local(z3_path) {
        Ok(l) => l,
        Err(e) => {
            eprintln!("error: {e}");
            return 2;
        }
    };
    let ay_api = match loader::load_api(&ay_lib) {
        Ok(a) => a,
        Err(e) => {
            eprintln!("error (AY lib): {e}");
            return 2;
        }
    };
    let z3_api = match loader::load_api(&z3_lib) {
        Ok(a) => a,
        Err(e) => {
            eprintln!("error (z3 lib): {e}");
            return 2;
        }
    };

    let timeout = Duration::from_secs(timeout_secs);
    let mut results: Vec<FileResult> = Vec::with_capacity(files.len());
    for file in &files {
        let script = match std::fs::read_to_string(file) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("warning: skipping {} ({e})", file.display());
                continue;
            }
        };
        // Reference first, then the library under test.
        let z3 = eval_timeboxed(z3_api, &script, timeout);
        let ay = eval_timeboxed(ay_api, &script, timeout);
        let category = categorize(&ay, &z3);
        results.push(FileResult {
            file: file.clone(),
            ay,
            z3,
            category,
        });
    }

    emit(ay_path, z3_path, &results, json)
}

// ===========================================================================
// Hermetic declared-status oracle (`diff --oracle declared`)
// ===========================================================================
//
// A SECOND, self-contained soundness check that needs NO reference solver: run
// each `.smt2` through libay_ffi ONLY, extract AY's verdict tokens, and compare
// them against the file's own `(set-info :status sat|unsat)` ground-truth
// annotation. A `sat` where the file declares `unsat` (or `unsat` where it
// declares `sat`) is a SOUNDNESS FAIL and exits non-zero. `unknown`/timeout is
// tolerated (incompleteness), and files without a decided `:status` contribute
// no judgement. This lets the pre-push gate run with zero z3 dependency.

/// The DECIDED part of a benchmark's own `(set-info :status sat|unsat|unknown)`
/// annotation — ground truth independent of any solver. `None` for `unknown`,
/// for an absent annotation, and for a self-contradicting one: all three are
/// "no usable oracle".
///
/// One parser, in [`crate::bench::parse_declared_status`], for every lane: this
/// used to be a hand-rolled copy that took the first `:status` substring in the
/// raw bytes, which reads the prose inside a `(set-info :source | ... |)` blob
/// as the answer.
pub(crate) fn declared_status_of(text: &str) -> Option<Verdict> {
    crate::bench::parse_declared_status(text).decided()
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum DeclaredCategory {
    /// Every decided AY verdict matches the declared `:status`.
    Correct,
    /// AY answered `unknown` where the file declares a decided status.
    Incomplete,
    /// AY timed out.
    Timeout,
    /// AY produced no verdict at all (e.g. an `(error ...)`), file was decided.
    NoVerdict,
    /// File has no decided `:status` — nothing to check against.
    NoOracle,
    /// AY `sat` vs declared `unsat` (or vice-versa) — a SOUNDNESS BUG.
    Wrong,
}

impl DeclaredCategory {
    fn label(self) -> &'static str {
        match self {
            DeclaredCategory::Correct => "CORRECT",
            DeclaredCategory::Incomplete => "AY-unknown-declared-decided",
            DeclaredCategory::Timeout => "TIMEOUT",
            DeclaredCategory::NoVerdict => "NO-VERDICT",
            DeclaredCategory::NoOracle => "no-declared-status",
            DeclaredCategory::Wrong => "WRONG",
        }
    }
}

struct DeclaredResult {
    file: PathBuf,
    declared: Option<Verdict>,
    ay: Outcome,
    category: DeclaredCategory,
}

/// Classify one file's AY outcome against its declared `:status`.
fn categorize_declared(declared: Option<Verdict>, ay: &Outcome) -> DeclaredCategory {
    let Some(want) = declared else {
        return DeclaredCategory::NoOracle;
    };
    let av = match ay {
        Outcome::Timeout => return DeclaredCategory::Timeout,
        Outcome::Verdicts(v) => v,
    };
    if av.is_empty() {
        return DeclaredCategory::NoVerdict;
    }
    let mut any_unknown = false;
    for v in av {
        match (*v, want) {
            (Verdict::Sat, Verdict::Unsat) | (Verdict::Unsat, Verdict::Sat) => {
                return DeclaredCategory::Wrong;
            }
            (Verdict::Unknown, _) => any_unknown = true,
            _ => {} // matches declared
        }
    }
    if any_unknown {
        DeclaredCategory::Incomplete
    } else {
        DeclaredCategory::Correct
    }
}

/// Run the hermetic declared-status oracle. Returns non-zero iff any file is
/// `WRONG` (AY contradicts its own `(set-info :status ...)`).
pub(crate) fn run_declared(
    ay_path: &Path,
    corpus: &[PathBuf],
    timeout_secs: u64,
    json: bool,
) -> i32 {
    let files = collect_smt2(corpus);
    if files.is_empty() {
        eprintln!("error: no .smt2 files found under {corpus:?}");
        return 2;
    }

    let ay_lib = match loader::open_local(ay_path) {
        Ok(l) => l,
        Err(e) => {
            eprintln!("error: {e}");
            return 2;
        }
    };
    let ay_api = match loader::load_api(&ay_lib) {
        Ok(a) => a,
        Err(e) => {
            eprintln!("error (AY lib): {e}");
            return 2;
        }
    };

    let timeout = Duration::from_secs(timeout_secs);
    let mut results: Vec<DeclaredResult> = Vec::with_capacity(files.len());
    for file in &files {
        let script = match std::fs::read_to_string(file) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("warning: skipping {} ({e})", file.display());
                continue;
            }
        };
        let declared = declared_status_of(&script);
        let ay = eval_timeboxed(ay_api, &script, timeout);
        let category = categorize_declared(declared, &ay);
        results.push(DeclaredResult {
            file: file.clone(),
            declared,
            ay,
            category,
        });
    }

    emit_declared(ay_path, &results, json)
}

fn declared_str(d: Option<Verdict>) -> &'static str {
    match d {
        Some(v) => v.as_str(),
        None => "-",
    }
}

fn emit_declared(ay_path: &Path, results: &[DeclaredResult], json: bool) -> i32 {
    let corpus_size = results.len();
    let count = |c: DeclaredCategory| results.iter().filter(|r| r.category == c).count();
    let correct = count(DeclaredCategory::Correct);
    let incomplete = count(DeclaredCategory::Incomplete);
    let timeouts = count(DeclaredCategory::Timeout);
    let no_verdict = count(DeclaredCategory::NoVerdict);
    let no_oracle = count(DeclaredCategory::NoOracle);
    let wrong_files: Vec<String> = results
        .iter()
        .filter(|r| r.category == DeclaredCategory::Wrong)
        .map(|r| r.file.display().to_string())
        .collect();
    let wrong = wrong_files.len();
    let checked = corpus_size - no_oracle;

    if json {
        let files: Vec<_> = results
            .iter()
            .map(|r| {
                serde_json::json!({
                    "file": r.file.display().to_string(),
                    "declared": declared_str(r.declared),
                    "ay": outcome_str(&r.ay),
                    "category": r.category.label(),
                })
            })
            .collect();
        let cert = serde_json::json!({
            "kind": "declared-status-oracle",
            "ay_lib": ay_path.display().to_string(),
            "corpus_size": corpus_size,
            "checked": checked,
            "correct": correct,
            "incomplete": incomplete,
            "timeouts": timeouts,
            "no_verdict": no_verdict,
            "no_declared_status": no_oracle,
            "wrong": wrong,
            "wrong_files": wrong_files,
            "files": files,
            "pass": wrong == 0,
        });
        println!(
            "{}",
            serde_json::to_string_pretty(&cert).unwrap_or_default()
        );
    } else {
        println!("== ay-z3-parity: declared-status oracle (hermetic, no z3) ==");
        println!("  under test (AY):  {}", ay_path.display());
        println!("  oracle:           each file's own (set-info :status ...)");
        println!();
        println!("{:<40} {:>8} {:>10}   CATEGORY", "FILE", "declared", "ay");
        println!("{}", "-".repeat(84));
        for r in results {
            let name = r.file.file_name().and_then(|n| n.to_str()).unwrap_or("?");
            let mark = if r.category == DeclaredCategory::Wrong {
                " <== SOUNDNESS BUG"
            } else {
                ""
            };
            println!(
                "{:<40} {:>8} {:>10}   {}{}",
                name,
                declared_str(r.declared),
                outcome_str(&r.ay),
                r.category.label(),
                mark
            );
        }
        println!("{}", "-".repeat(84));
        println!("corpus_size          = {corpus_size}");
        println!("checked (has status) = {checked}");
        println!("correct              = {correct}");
        println!("incomplete           = {incomplete}  (AY unknown, file decided)");
        if timeouts > 0 {
            println!("timeouts             = {timeouts}");
        }
        if no_verdict > 0 {
            println!("no_verdict           = {no_verdict}");
        }
        println!("no_declared_status   = {no_oracle}  (skipped, no oracle)");
        println!("wrong                = {wrong}");
        println!();
        if wrong == 0 {
            println!("RESULT: PASS — 0 verdicts contradict the declared :status. AY is sound on every labeled instance.");
        } else {
            println!(
                "RESULT: FAIL — {wrong} soundness violation(s) (AY contradicts its own :status):"
            );
            for f in &wrong_files {
                println!("    {f}");
            }
        }
    }

    i32::from(wrong != 0)
}

fn outcome_str(o: &Outcome) -> String {
    match o {
        Outcome::Timeout => "timeout".to_string(),
        Outcome::Verdicts(v) if v.is_empty() => "-".to_string(),
        Outcome::Verdicts(v) => v.iter().map(|x| x.as_str()).collect::<Vec<_>>().join(","),
    }
}

fn emit(ay_path: &Path, z3_path: &Path, results: &[FileResult], json: bool) -> i32 {
    let corpus_size = results.len();
    let agree = results.iter().filter(|r| r.category.is_agree()).count();
    let ay_incomplete = results
        .iter()
        .filter(|r| r.category == Category::AyIncomplete)
        .count();
    let ay_stronger = results
        .iter()
        .filter(|r| r.category == Category::AyStronger)
        .count();
    let timeouts = results
        .iter()
        .filter(|r| r.category == Category::Timeout)
        .count();
    let count_mismatch = results
        .iter()
        .filter(|r| r.category == Category::CountMismatch)
        .count();
    let no_verdict = results
        .iter()
        .filter(|r| r.category == Category::NoVerdict)
        .count();
    let disagree_files: Vec<String> = results
        .iter()
        .filter(|r| r.category == Category::Disagree)
        .map(|r| r.file.display().to_string())
        .collect();
    let disagree = disagree_files.len();

    if json {
        let files: Vec<_> = results
            .iter()
            .map(|r| {
                serde_json::json!({
                    "file": r.file.display().to_string(),
                    "z3": outcome_str(&r.z3),
                    "ay": outcome_str(&r.ay),
                    "category": r.category.label(),
                })
            })
            .collect();
        let cert = serde_json::json!({
            "kind": "behavioral-parity",
            "ay_lib": ay_path.display().to_string(),
            "z3_lib": z3_path.display().to_string(),
            "corpus_size": corpus_size,
            "agree": agree,
            "ay_incomplete": ay_incomplete,
            "ay_stronger": ay_stronger,
            "count_mismatch": count_mismatch,
            "timeouts": timeouts,
            "no_verdict": no_verdict,
            "disagree": disagree,
            "disagree_files": disagree_files,
            "files": files,
            "pass": disagree == 0,
        });
        println!(
            "{}",
            serde_json::to_string_pretty(&cert).unwrap_or_default()
        );
    } else {
        println!("== ay-z3-parity: behavioral agreement (differential testing) ==");
        println!("  under test (AY):  {}", ay_path.display());
        println!("  reference (z3):   {}", z3_path.display());
        println!();
        println!("{:<26} {:>10} {:>10}   CATEGORY", "FILE", "z3", "ay");
        println!("{}", "-".repeat(72));
        for r in results {
            let name = r.file.file_name().and_then(|n| n.to_str()).unwrap_or("?");
            let mark = if r.category == Category::Disagree {
                " <== SOUNDNESS BUG"
            } else {
                ""
            };
            println!(
                "{:<26} {:>10} {:>10}   {}{}",
                name,
                outcome_str(&r.z3),
                outcome_str(&r.ay),
                r.category.label(),
                mark
            );
        }
        println!("{}", "-".repeat(72));
        println!("corpus_size    = {corpus_size}");
        println!("agree          = {agree}");
        println!("ay_incomplete  = {ay_incomplete}  (AY unknown, z3 decided)");
        if ay_stronger > 0 {
            println!("ay_stronger    = {ay_stronger}  (AY decided, z3 unknown)");
        }
        if count_mismatch > 0 {
            println!("count_mismatch = {count_mismatch}");
        }
        if timeouts > 0 {
            println!("timeouts       = {timeouts}");
        }
        if no_verdict > 0 {
            println!("no_verdict     = {no_verdict}");
        }
        println!("disagree       = {disagree}");
        println!();
        if disagree == 0 {
            println!("RESULT: PASS — 0 sat-vs-unsat disagreements. AY agrees with libz3 on every decided instance.");
        } else {
            println!("RESULT: FAIL — {disagree} soundness disagreement(s):");
            for f in &disagree_files {
                println!("    {f}");
            }
        }
    }

    i32::from(disagree != 0)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn verdicts_do_not_confuse_sat_and_unsat() {
        assert_eq!(
            verdicts_of("sat\nunsat\n"),
            vec![Verdict::Sat, Verdict::Unsat]
        );
        assert_eq!(verdicts_of("unsat"), vec![Verdict::Unsat]);
        assert_eq!(verdicts_of("((x 5))\nsat"), vec![Verdict::Sat]);
        assert_eq!(verdicts_of("(error \"boom\")"), Vec::<Verdict>::new());
    }

    #[test]
    fn disagreement_is_flagged() {
        let ay = Outcome::Verdicts(vec![Verdict::Unsat]);
        let z3 = Outcome::Verdicts(vec![Verdict::Sat]);
        assert_eq!(categorize(&ay, &z3), Category::Disagree);
    }

    #[test]
    fn ay_unknown_is_incomplete_not_a_bug() {
        let ay = Outcome::Verdicts(vec![Verdict::Unknown]);
        let z3 = Outcome::Verdicts(vec![Verdict::Sat]);
        assert_eq!(categorize(&ay, &z3), Category::AyIncomplete);
    }

    #[test]
    fn matching_verdicts_agree() {
        let ay = Outcome::Verdicts(vec![Verdict::Sat]);
        let z3 = Outcome::Verdicts(vec![Verdict::Sat]);
        assert_eq!(categorize(&ay, &z3), Category::AgreeSat);
    }

    // --- declared-status oracle -------------------------------------------

    #[test]
    fn declared_status_parses_whole_word() {
        assert_eq!(
            declared_status_of("(set-info :status unsat)\n(check-sat)"),
            Some(Verdict::Unsat)
        );
        assert_eq!(
            declared_status_of("(set-info :status sat)"),
            Some(Verdict::Sat)
        );
        // `unknown` and absent are both "no usable oracle".
        assert_eq!(declared_status_of("(set-info :status unknown)"), None);
        assert_eq!(declared_status_of("(check-sat)"), None);
    }

    #[test]
    fn declared_wrong_when_ay_contradicts_status() {
        // AY sat, file declares unsat = the shipped wrong-SAT class.
        let ay = Outcome::Verdicts(vec![Verdict::Sat]);
        assert_eq!(
            categorize_declared(Some(Verdict::Unsat), &ay),
            DeclaredCategory::Wrong
        );
        // AY unsat, file declares sat = a spurious-conflict wrong answer.
        let ay = Outcome::Verdicts(vec![Verdict::Unsat]);
        assert_eq!(
            categorize_declared(Some(Verdict::Sat), &ay),
            DeclaredCategory::Wrong
        );
    }

    #[test]
    fn declared_correct_and_incomplete_and_no_oracle() {
        let ay_sat = Outcome::Verdicts(vec![Verdict::Sat]);
        assert_eq!(
            categorize_declared(Some(Verdict::Sat), &ay_sat),
            DeclaredCategory::Correct
        );
        // AY unknown where the file decided = tolerated incompleteness.
        let ay_unk = Outcome::Verdicts(vec![Verdict::Unknown]);
        assert_eq!(
            categorize_declared(Some(Verdict::Unsat), &ay_unk),
            DeclaredCategory::Incomplete
        );
        // No decided :status = nothing to judge against.
        assert_eq!(
            categorize_declared(None, &ay_sat),
            DeclaredCategory::NoOracle
        );
    }
}
