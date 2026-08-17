// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Markdown rendering for differential benchmark reports.

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::time::Duration;

use ay_bench::{ResourcePlan, ENFORCEMENT_RSS_WATCHDOG_V1};

use super::{
    declared_status, host_info, sha256_of, stats_row, utc_now_iso, BenchConfig, Category, DivStats,
    FileRecord, HEADERS, KILL_GRACE, RATIO_FLOOR_SECS, WIN_LOSS_MIN_SECS,
};

mod z3_wins;

pub(super) fn render_report(
    cfg: &BenchConfig,
    records: &[FileRecord],
    divisions: &BTreeMap<String, DivStats>,
    totals: &DivStats,
    ay_version: Option<&str>,
    z3_version: Option<&str>,
    campaign_wall: Duration,
    resource_plan: &ResourcePlan,
    resource_evidence: &serde_json::Value,
) -> String {
    let mut md = String::new();
    write_intro_and_reproduce(&mut md);
    write_provenance(
        &mut md,
        cfg,
        ay_version,
        z3_version,
        campaign_wall,
        resource_plan,
        resource_evidence,
    );
    write_soundness(&mut md, records, totals);
    write_divisions(&mut md, divisions, totals);
    z3_wins::write(&mut md, records, divisions, totals);
    write_ay_wins(&mut md, records, totals);
    write_methodology(&mut md, cfg);
    md
}

fn write_intro_and_reproduce(md: &mut String) {
    let _ = writeln!(md, "# AY vs z3 — differential benchmark report");
    let _ = writeln!(md);
    let _ = writeln!(
        md,
        "Generated {} by `ay-z3-parity bench`. Every number below is mechanically",
        utc_now_iso()
    );
    let _ = writeln!(
        md,
        "derived from the run recorded in the JSON certificate next to this file;"
    );
    // "no file was skipped" is a claim about THIS RUN over the corpus roots it
    // was given. It says nothing about whether those roots are the whole of
    // SMT-LIB, and readers took it to mean exactly that: reports generated over
    // `benchmarks/smtlib-sample` (1,500 files, 5 of 84 divisions) were quoted as
    // corpus-wide parity results. State the scope limit in the artifact itself.
    let _ = writeln!(
        md,
        "nothing is hand-edited. Within the corpus roots listed below, no file was"
    );
    let _ = writeln!(
        md,
        "skipped or sampled. SCOPE: these numbers describe exactly those roots and"
    );
    let _ = writeln!(
        md,
        "are not corpus-wide unless the roots are — `benchmarks/smtlib-sample` is a"
    );
    let _ = writeln!(
        md,
        "1,500-file, 5-division slice of SMT-LIB 2024 (84 divisions); the complete"
    );
    let _ = writeln!(
        md,
        "corpus is `benchmarks/smtlib-all` via `ay-z3-parity fetch`."
    );
    let _ = writeln!(md);
    let _ = writeln!(md, "## Reproduce");
    let _ = writeln!(md);
    let _ = writeln!(md, "```sh");
    let _ = writeln!(
        md,
        "# 1. build the solver library under test (release) and this tool"
    );
    let _ = writeln!(md, "cargo build --release -p ay-ffi");
    let _ = writeln!(md, "cargo build --release -p ay-z3-parity");
    let _ = writeln!(
        md,
        "# 2. fetch the SMT-LIB samples (see benchmarks/smtlib-sample/MANIFEST.md"
    );
    let _ = writeln!(
        md,
        "#    for URLs, checksums, and the deterministic sampling rule)"
    );
    let _ = writeln!(md, "# 3. run the campaign (exact invocation of this run):");
    let _ = writeln!(md, "{}", std::env::args().collect::<Vec<_>>().join(" "));
    let _ = writeln!(md, "```");
    let _ = writeln!(md);
}

fn write_provenance(
    md: &mut String,
    cfg: &BenchConfig,
    ay_version: Option<&str>,
    z3_version: Option<&str>,
    campaign_wall: Duration,
    resource_plan: &ResourcePlan,
    resource_evidence: &serde_json::Value,
) {
    let _ = writeln!(md, "| | |");
    let _ = writeln!(md, "|---|---|");
    let _ = writeln!(md, "| AY library | `{}` |", cfg.ay.display());
    let _ = writeln!(
        md,
        "| AY sha256 | `{}` |",
        sha256_of(&cfg.ay).unwrap_or_else(|| "?".into())
    );
    let _ = writeln!(
        md,
        "| AY `Z3_get_full_version` | {} |",
        ay_version.unwrap_or("?")
    );
    let _ = writeln!(md, "| z3 library | `{}` |", cfg.z3.display());
    let _ = writeln!(
        md,
        "| z3 sha256 | `{}` |",
        sha256_of(&cfg.z3).unwrap_or_else(|| "?".into())
    );
    let _ = writeln!(
        md,
        "| z3 `Z3_get_full_version` | {} |",
        z3_version.unwrap_or("?")
    );
    let _ = writeln!(
        md,
        "| timeout per (file, solver) | {} s |",
        cfg.timeout_secs
    );
    let _ = writeln!(
        md,
        "| hard process-group timeout | {} s |",
        resource_evidence["hard_timeout_secs"]
    );
    let _ = writeln!(
        md,
        "| parallel jobs requested / effective | {} / {} |",
        resource_plan.requested_jobs, resource_plan.jobs
    );
    let _ = writeln!(
        md,
        "| memory per child | {} MiB |",
        resource_plan.memlimit_mb_per_child
    );
    let _ = writeln!(
        md,
        "| NBCORE per child | {} |",
        resource_plan.nbcore_per_child
    );
    let _ = writeln!(
        md,
        "| reserved host headroom | {} MiB |",
        resource_plan.headroom_mb
    );
    let _ = writeln!(
        md,
        "| resource enforcement | `{ENFORCEMENT_RSS_WATCHDOG_V1}` |"
    );
    let _ = writeln!(
        md,
        "| exact execution envelope | `{}` |",
        resource_evidence["external_ffi"]["execution_envelope"]
            .as_str()
            .unwrap_or("?")
    );
    let _ = writeln!(
        md,
        "| campaign wall time | {:.1} s |",
        campaign_wall.as_secs_f64()
    );
    let _ = writeln!(md, "| host | {} |", host_info());
    let _ = writeln!(md);
}

fn write_soundness(md: &mut String, records: &[FileRecord], totals: &DivStats) {
    // Soundness verdict, first and prominent.
    let _ = writeln!(md, "## Soundness: sat-vs-unsat disagreements");
    let _ = writeln!(md);
    if totals.disagree == 0 {
        let _ = writeln!(
            md,
            "**DISAGREE = 0** across {} files. No paired decisive answers conflicted;",
            totals.files
        );
        let _ = writeln!(
            md,
            "unknown, timeout, memout, crash, and missing-verdict cases remain accounted below."
        );
    } else {
        let _ = writeln!(
            md,
            "**DISAGREE = {} — SOUNDNESS BUG(S). This run FAILS.**",
            totals.disagree
        );
        let _ = writeln!(md);
        let _ = writeln!(
            md,
            "The \"declared\" column is the benchmark's own `(set-info :status ...)`"
        );
        let _ = writeln!(
            md,
            "annotation — ground truth independent of both solvers. A solver whose"
        );
        let _ = writeln!(md, "verdict contradicts it has the wrong answer.");
        let _ = writeln!(md);
        let _ = writeln!(md, "| file | declared | z3 | AY |");
        let _ = writeln!(md, "|---|---|---|---|");
        for r in records.iter().filter(|r| r.category == Category::Disagree) {
            let _ = writeln!(
                md,
                "| `{}` | {} | {} | {} |",
                r.file.display(),
                declared_status(&r.file).unwrap_or_else(|| "(none)".into()),
                r.z3.label(),
                r.ay.label()
            );
        }
    }
    let _ = writeln!(md);
}

fn write_divisions(md: &mut String, divisions: &BTreeMap<String, DivStats>, totals: &DivStats) {
    // Per-division table.
    let _ = writeln!(md, "## Per-division results");
    let _ = writeln!(md);
    let _ = writeln!(
        md,
        "{}",
        md_row(&HEADERS.iter().map(|h| h.to_string()).collect::<Vec<_>>())
    );
    let _ = writeln!(md, "|{}", "---|".repeat(HEADERS.len()));
    for (name, s) in divisions {
        let _ = writeln!(md, "{}", md_row(&stats_row(name, s)));
    }
    let _ = writeln!(md, "{}", md_row(&stats_row("**TOTAL**", totals)));
    let _ = writeln!(md);
    let _ = writeln!(
        md,
        "Column key: A-SAT/A-UNSAT/A-MIX = both solvers produced identical decisive"
    );
    let _ = writeln!(
        md,
        "verdicts; BOTH-UNK = identical verdicts containing `unknown`; AY-UNK = AY"
    );
    let _ = writeln!(
        md,
        "`unknown` where z3 decided (AY incompleteness); Z3-UNK = the reverse;"
    );
    let _ = writeln!(md, "T/O a/z/b = timeouts (AY only / z3 only / both);");
    let _ = writeln!(
        md,
        "MEM a/z/b = enforced memory-limit exits; CRASH a/z = solver process died"
    );
    let _ = writeln!(
        md,
        "(either alone or both); OTHER = verdict-count mismatch or no verdicts;"
    );
    let _ = writeln!(
        md,
        "MED/GEO = median / geometric-mean wall ratio AY/z3 over decided-by-both"
    );
    let _ = writeln!(
        md,
        "files (ratio < 1 means AY is faster); W/L 2x = files where AY / z3 was more"
    );
    let _ = writeln!(
        md,
        "than 2x faster and the slower side took at least {} ms.",
        (WIN_LOSS_MIN_SECS * 1000.0) as u64
    );
    let _ = writeln!(md);
}

fn write_ay_wins(md: &mut String, records: &[FileRecord], totals: &DivStats) {
    // ---- Where AY wins (same rules, reversed) ----
    let _ = writeln!(md, "## Where AY wins");
    let _ = writeln!(md);
    let mut ay_wins_any = false;
    let z3_to_ay_decided = records
        .iter()
        .filter(|r| r.category == Category::TimeoutZ3 && r.ay.decided())
        .count();
    if z3_to_ay_decided > 0 {
        ay_wins_any = true;
        let _ = writeln!(
            md,
            "- z3 timed out where AY decided: {z3_to_ay_decided} files"
        );
    }
    let z3_memout_ay_decided = records
        .iter()
        .filter(|r| r.category == Category::MemoutZ3 && r.ay.decided())
        .count();
    if z3_memout_ay_decided > 0 {
        ay_wins_any = true;
        let _ = writeln!(
            md,
            "- z3 exceeded its memory envelope where AY decided: {z3_memout_ay_decided} files"
        );
    }
    if totals.z3_unknown > 0 {
        ay_wins_any = true;
        let _ = writeln!(
            md,
            "- z3 answered `unknown` where AY decided: {} files",
            totals.z3_unknown
        );
    }
    let speedups = records
        .iter()
        .filter(|r| {
            r.ratio.is_some_and(|x| x < 0.5)
                && r.ay.wall.as_secs_f64().max(r.z3.wall.as_secs_f64()) >= WIN_LOSS_MIN_SECS
        })
        .count();
    if speedups > 0 {
        ay_wins_any = true;
        let _ = writeln!(
            md,
            "- AY more than 2x faster (decided-by-both, slower side ≥ {} ms): {} files",
            (WIN_LOSS_MIN_SECS * 1000.0) as u64,
            speedups
        );
    }
    let z3_no_verdict = records
        .iter()
        .filter(|r| r.category == Category::Other && r.z3.no_verdict() && r.ay.decided())
        .count();
    if z3_no_verdict > 0 {
        ay_wins_any = true;
        let _ = writeln!(
            md,
            "- z3 produced no verdict where AY decided: {z3_no_verdict} files"
        );
    }
    let z3_crashes = records
        .iter()
        .filter(|r| matches!(r.category, Category::CrashZ3 | Category::CrashBoth))
        .count();
    if z3_crashes > 0 {
        ay_wins_any = true;
        let _ = writeln!(md, "- z3 crashes: {z3_crashes} files");
    }
    if !ay_wins_any {
        let _ = writeln!(
            md,
            "No AY advantage observed on this corpus under the same rules."
        );
    }
    let _ = writeln!(md);
}

fn write_methodology(md: &mut String, cfg: &BenchConfig) {
    let _ = writeln!(md, "## Methodology");
    let _ = writeln!(md);
    let _ = writeln!(
        md,
        "- Both libraries are `dlopen`ed by path; each (file, solver) pair runs in a"
    );
    let _ = writeln!(
        md,
        "  stopped-exec child process group (`ay-z3-parity bench-one <lib> <file>`)."
    );
    let _ = writeln!(
        md,
        "  `_oom_guard.py` caps jobs and arms a zero-grace RSS watchdog before exec;"
    );
    let _ = writeln!(
        md,
        "  residual descendants are killed before leader reap, and stdout retention is"
    );
    let _ = writeln!(md, "  capped at one MiB.");
    let _ = writeln!(
        md,
        "- Wall time is measured inside the child strictly around"
    );
    let _ = writeln!(
        md,
        "  `Z3_eval_smtlib2_string` — process spawn, `dlopen`, and file reading are"
    );
    let _ = writeln!(md, "  excluded, identically for both solvers.");
    let _ = writeln!(
        md,
        "- Timeout: the child is SIGKILLed {}s after the {}s budget; a child that",
        KILL_GRACE.as_secs(),
        cfg.timeout_secs
    );
    let _ = writeln!(
        md,
        "  finishes in the grace window but whose eval time exceeded the budget is"
    );
    let _ = writeln!(md, "  still recorded as a timeout.");
    let _ = writeln!(
        md,
        "- Verdicts are the ordered whole-word `sat`/`unsat`/`unknown` tokens of each"
    );
    let _ = writeln!(
        md,
        "  solver's output; `sat` never substring-matches `unsat`."
    );
    let _ = writeln!(
        md,
        "- Ratio statistics use only decided-by-both files (identical decisive verdict"
    );
    let _ = writeln!(
        md,
        "  lists), with each side floored at {} ms to keep timer granularity from",
        RATIO_FLOOR_SECS * 1000.0
    );
    let _ = writeln!(md, "  fabricating extreme ratios on trivial files.");
    let _ = writeln!(
        md,
        "- z3 is run first, then AY, for every file; ordering is identical across the"
    );
    let _ = writeln!(md, "  corpus and both solvers see the exact same bytes.");
}

fn md_row(cells: &[String]) -> String {
    format!("| {} |", cells.join(" | "))
}

#[cfg(test)]
mod tests;
