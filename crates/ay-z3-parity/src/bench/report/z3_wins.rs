// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Auto-populated evidence for cases where z3 outperforms AY.

use std::collections::BTreeMap;
use std::fmt::Write as _;

use super::super::{fmt_ms, fmt_ratio, Category, DivStats, FileRecord, WIN_LOSS_MIN_SECS};

pub(super) fn write(
    md: &mut String,
    records: &[FileRecord],
    divisions: &BTreeMap<String, DivStats>,
    totals: &DivStats,
) {
    let _ = writeln!(md, "## Where z3 wins");
    let _ = writeln!(md);
    let mut z3_wins_any = write_ay_crashes(md, records);
    z3_wins_any |= write_ay_timeouts(md, records);
    z3_wins_any |= write_ay_memouts(md, records);
    z3_wins_any |= write_ay_unknowns(md, records, divisions, totals);
    z3_wins_any |= write_ay_no_verdict(md, records);
    z3_wins_any |= write_slowdowns(md, records);
    if !z3_wins_any {
        write_no_advantage(md);
    }
}

fn write_ay_crashes(md: &mut String, records: &[FileRecord]) -> bool {
    let ay_crashes: Vec<&FileRecord> = records
        .iter()
        .filter(|r| matches!(r.category, Category::CrashAy | Category::CrashBoth))
        .collect();
    if ay_crashes.is_empty() {
        return false;
    }

    let _ = writeln!(md, "### AY crashes ({})", ay_crashes.len());
    let _ = writeln!(md);
    for r in ay_crashes.iter().take(30) {
        let detail = r.ay.detail().unwrap_or("?");
        let _ = writeln!(
            md,
            "- `{}` — {} (z3: {})",
            r.file.display(),
            detail,
            r.z3.label()
        );
    }
    if ay_crashes.len() > 30 {
        let _ = writeln!(
            md,
            "- … and {} more (see certificate)",
            ay_crashes.len() - 30
        );
    }
    let _ = writeln!(md);
    true
}

fn write_ay_timeouts(md: &mut String, records: &[FileRecord]) -> bool {
    let ay_to_z3_decided: Vec<&FileRecord> = records
        .iter()
        .filter(|r| r.category == Category::TimeoutAy && r.z3.decided())
        .collect();
    if ay_to_z3_decided.is_empty() {
        return false;
    }

    let _ = writeln!(
        md,
        "### AY timed out where z3 decided ({} files)",
        ay_to_z3_decided.len()
    );
    let _ = writeln!(md);
    let _ = writeln!(md, "| file | z3 verdict | z3 ms |");
    let _ = writeln!(md, "|---|---|---|");
    for r in ay_to_z3_decided.iter().take(20) {
        let _ = writeln!(
            md,
            "| `{}` | {} | {} |",
            r.file.display(),
            r.z3.label(),
            fmt_ms(r.z3.wall)
        );
    }
    if ay_to_z3_decided.len() > 20 {
        let _ = writeln!(
            md,
            "| … and {} more (see certificate) | | |",
            ay_to_z3_decided.len() - 20
        );
    }
    let _ = writeln!(md);
    true
}

fn write_ay_memouts(md: &mut String, records: &[FileRecord]) -> bool {
    let ay_memout_z3_decided: Vec<&FileRecord> = records
        .iter()
        .filter(|r| r.category == Category::MemoutAy && r.z3.decided())
        .collect();
    if ay_memout_z3_decided.is_empty() {
        return false;
    }

    let _ = writeln!(
        md,
        "### AY exceeded its memory envelope where z3 decided ({} files)",
        ay_memout_z3_decided.len()
    );
    let _ = writeln!(md);
    for r in ay_memout_z3_decided.iter().take(20) {
        let _ = writeln!(
            md,
            "- `{}` (z3: {} in {} ms)",
            r.file.display(),
            r.z3.label(),
            fmt_ms(r.z3.wall)
        );
    }
    if ay_memout_z3_decided.len() > 20 {
        let _ = writeln!(
            md,
            "- … and {} more (see certificate)",
            ay_memout_z3_decided.len() - 20
        );
    }
    let _ = writeln!(md);
    true
}

fn write_ay_unknowns(
    md: &mut String,
    records: &[FileRecord],
    divisions: &BTreeMap<String, DivStats>,
    totals: &DivStats,
) -> bool {
    if totals.ay_unknown == 0 {
        return false;
    }

    let _ = writeln!(
        md,
        "### AY answered `unknown` where z3 decided ({} files)",
        totals.ay_unknown
    );
    let _ = writeln!(md);
    for (name, s) in divisions {
        if s.ay_unknown == 0 {
            continue;
        }
        let _ = writeln!(md, "- **{name}**: {} of {} files", s.ay_unknown, s.files);
        for r in records
            .iter()
            .filter(|r| r.division == *name && r.category == Category::AyUnknownZ3Decided)
            .take(8)
        {
            let _ = writeln!(
                md,
                "  - `{}` (z3: {} in {} ms)",
                r.file.display(),
                r.z3.label(),
                fmt_ms(r.z3.wall)
            );
        }
        if s.ay_unknown > 8 {
            let _ = writeln!(md, "  - … and {} more (see certificate)", s.ay_unknown - 8);
        }
    }
    let _ = writeln!(md);
    true
}

fn write_ay_no_verdict(md: &mut String, records: &[FileRecord]) -> bool {
    let ay_no_verdict: Vec<&FileRecord> = records
        .iter()
        .filter(|r| r.category == Category::Other && r.ay.no_verdict() && r.z3.decided())
        .collect();
    if ay_no_verdict.is_empty() {
        return false;
    }

    let _ = writeln!(
        md,
        "### AY produced no verdict where z3 decided ({} files)",
        ay_no_verdict.len()
    );
    let _ = writeln!(md);
    let _ = writeln!(
        md,
        "AY ran to completion but emitted no `sat`/`unsat` token — typically an"
    );
    let _ = writeln!(
        md,
        "`(error ...)`-only reply such as an unsupported logic or command in the"
    );
    let _ = writeln!(
        md,
        "`Z3_eval_smtlib2_string` path. These count as OTHER in the table."
    );
    let _ = writeln!(md);
    for r in ay_no_verdict.iter().take(15) {
        let _ = writeln!(
            md,
            "- `{}` (z3: {} in {} ms)",
            r.file.display(),
            r.z3.label(),
            fmt_ms(r.z3.wall)
        );
    }
    if ay_no_verdict.len() > 15 {
        let _ = writeln!(
            md,
            "- … and {} more (see certificate)",
            ay_no_verdict.len() - 15
        );
    }
    let _ = writeln!(md);
    true
}

fn write_slowdowns(md: &mut String, records: &[FileRecord]) -> bool {
    let mut slowdowns: Vec<&FileRecord> = records
        .iter()
        .filter(|r| {
            r.ratio.is_some_and(|x| x > 2.0)
                && r.ay.wall.as_secs_f64().max(r.z3.wall.as_secs_f64()) >= WIN_LOSS_MIN_SECS
        })
        .collect();
    slowdowns.sort_by(|a, b| b.ratio.partial_cmp(&a.ratio).expect("no NaN ratios"));
    if slowdowns.is_empty() {
        return false;
    }

    let _ = writeln!(
        md,
        "### z3 more than 2x faster (decided-by-both; {} files, top 20 by ratio)",
        slowdowns.len()
    );
    let _ = writeln!(md);
    let _ = writeln!(md, "| file | verdict | z3 ms | AY ms | AY/z3 |");
    let _ = writeln!(md, "|---|---|---|---|---|");
    for r in slowdowns.iter().take(20) {
        let _ = writeln!(
            md,
            "| `{}` | {} | {} | {} | {} |",
            r.file.display(),
            r.z3.label(),
            fmt_ms(r.z3.wall),
            fmt_ms(r.ay.wall),
            fmt_ratio(r.ratio)
        );
    }
    let _ = writeln!(md);
    true
}

fn write_no_advantage(md: &mut String) {
    let _ = writeln!(
        md,
        "No z3 advantage observed on this corpus: no AY crashes, no AY-only"
    );
    let _ = writeln!(
        md,
        "timeouts on z3-decided files, no AY-unknowns where z3 decided, and no"
    );
    let _ = writeln!(
        md,
        "decided-by-both file where z3 was more than 2x faster (with the slower"
    );
    let _ = writeln!(md, "side over {} ms).", (WIN_LOSS_MIN_SECS * 1000.0) as u64);
    let _ = writeln!(md);
}
