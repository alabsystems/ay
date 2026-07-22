// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(
    clippy::print_stderr,
    clippy::print_stdout,
    clippy::cast_possible_truncation
)]

//! CTB Wave-2: Cross-Solver Trajectory Bisect first-divergence comparator.
//!
//! Compares AY and CaDiCaL search trajectories to find the first divergence.
//! Part of #4934.
//!
//! Usage:
//! ```bash
//! AY_DIAGNOSTIC_FILE=ay.jsonl cargo run --release -- input.cnf
//! reference/cadical/build/cadical input.cnf > cadical.txt 2>&1
//! cargo run --release --example compare_search_fingerprint -- ay.jsonl cadical.txt
//! ```

use std::collections::BTreeMap;
use std::fs;
use std::path::Path;

#[derive(Debug, Clone)]
struct Event {
    kind: EventKind,
    conflicts: u64,
    restarts: u64,
    active_vars: u64,
    irredundant: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum EventKind {
    ModeSwitch { entering_stable: bool },
    Reduction,
    Inprocessing,
}

impl EventKind {
    fn name(&self) -> &'static str {
        match self {
            Self::ModeSwitch { .. } => "mode_switch",
            Self::Reduction => "reduction",
            Self::Inprocessing => "inprocessing",
        }
    }
}

fn parse_ay_trace(path: &Path) -> Vec<Event> {
    let content = fs::read_to_string(path).unwrap_or_else(|e| {
        eprintln!("error: cannot read AY trace {}: {e}", path.display());
        std::process::exit(1);
    });
    let mut events = Vec::new();
    let (mut restart_count, mut last_vars, mut last_irred) = (0u64, 0u64, 0u64);

    for line in content.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        let obj: serde_json::Value = match serde_json::from_str(line) {
            Ok(v) => v,
            Err(_) => continue,
        };
        match obj["type"].as_str().unwrap_or("") {
            "restart" => restart_count += 1,
            "mode_switch" => {
                let entering_stable = obj["mode"].as_str() == Some("stable");
                events.push(Event {
                    kind: EventKind::ModeSwitch { entering_stable },
                    conflicts: obj["num_conflicts"].as_u64().unwrap_or(0),
                    restarts: restart_count,
                    active_vars: last_vars,
                    irredundant: last_irred,
                });
            }
            "inprocessing_round" => {
                last_vars = obj["vars_active"].as_u64().unwrap_or(0);
                last_irred = obj["clauses_after"].as_u64().unwrap_or(0);
                events.push(Event {
                    kind: EventKind::Inprocessing,
                    conflicts: obj["num_conflicts"].as_u64().unwrap_or(0),
                    restarts: restart_count,
                    active_vars: last_vars,
                    irredundant: last_irred,
                });
            }
            _ => {}
        }
    }
    events
}

/// Classify a CaDiCaL report type character into an event kind.
/// Reference: cadical/src/report.cpp (type chars documented at top).
fn classify_cadical_report(ch: char) -> Option<EventKind> {
    match ch {
        '[' => Some(EventKind::ModeSwitch {
            entering_stable: true,
        }),
        '{' => Some(EventKind::ModeSwitch {
            entering_stable: false,
        }),
        '-' => Some(EventKind::Reduction),
        'e' | 'p' | 's' | 'u' | 'v' | 'w' | 'x' | 'd' | 't' | '2' | '3' | 'b' | 'c' | 'k' => {
            Some(EventKind::Inprocessing)
        }
        _ => None,
    }
}

/// Parse CaDiCaL's report lines into milestone events.
///
/// Columns (per report.cpp REPORTS macro): seconds, MB, level, reductions,
/// restarts, rate, conflicts, redundant, size/glue, size, glue, tier1,
/// tier2, trail%, irredundant, variables, remaining%.
fn parse_cadical_output(path: &Path) -> Vec<Event> {
    let content = fs::read_to_string(path).unwrap_or_else(|e| {
        eprintln!("error: cannot read CaDiCaL output {}: {e}", path.display());
        std::process::exit(1);
    });
    let mut events = Vec::new();
    // All valid CaDiCaL report type characters from report.cpp.
    const REPORT_CHARS: &str = "[]{}R-.epsuv wxdt23bckfGC/iOF#BWPL*+r10?l~";

    for line in content.lines() {
        let line = line.trim();
        if line.len() < 4 || !line.starts_with("c ") {
            continue;
        }
        let type_char = match line[2..].chars().next() {
            Some(ch) if REPORT_CHARS.contains(ch) => ch,
            _ => continue,
        };
        let cols: Vec<f64> = line[3..]
            .split_whitespace()
            .filter_map(|t| t.trim_end_matches('%').parse().ok())
            .collect();
        if cols.len() < 16 {
            continue;
        }
        if let Some(kind) = classify_cadical_report(type_char) {
            events.push(Event {
                kind,
                conflicts: cols[6] as u64,
                restarts: cols[4] as u64,
                active_vars: cols[15] as u64,
                irredundant: cols[14] as u64,
            });
        }
    }
    events
}

#[derive(Debug)]
struct Divergence {
    class: &'static str,
    event_class: &'static str,
    seq_index: usize,
    ay_conflicts: u64,
    cadical_conflicts: u64,
    detail: String,
    owning_file: &'static str,
}

fn mode_label(kind: EventKind) -> &'static str {
    match kind {
        EventKind::ModeSwitch { entering_stable } => {
            if entering_stable {
                "stable"
            } else {
                "focused"
            }
        }
        _ => "?",
    }
}

fn check_tolerance(a: u64, b: u64, pct_denom: u64, min: u64) -> Option<u64> {
    let tolerance = (a.max(b) / pct_denom).max(min);
    let diff = a.abs_diff(b);
    if diff > tolerance {
        Some(diff)
    } else {
        None
    }
}

fn compare_mode_switches(ay: &[&Event], cad: &[&Event]) -> Option<Divergence> {
    for i in 0..ay.len().min(cad.len()) {
        let (z, c) = (ay[i], cad[i]);
        if z.kind != c.kind {
            return Some(Divergence {
                class: "mode_direction",
                event_class: "mode_switch",
                seq_index: i,
                ay_conflicts: z.conflicts,
                cadical_conflicts: c.conflicts,
                detail: format!(
                    "AY enters {} but CaDiCaL enters {} (AY c={}, CaDiCaL c={})",
                    mode_label(z.kind),
                    mode_label(c.kind),
                    z.conflicts,
                    c.conflicts,
                ),
                owning_file: "crates/ay-sat/src/solver/restart.rs",
            });
        }
        if let Some(d) = check_tolerance(z.conflicts, c.conflicts, 10, 100) {
            return Some(Divergence {
                class: "mode_budget",
                event_class: "mode_switch",
                seq_index: i,
                ay_conflicts: z.conflicts,
                cadical_conflicts: c.conflicts,
                detail: format!("Mode switch #{i}: conflict diff={d}"),
                owning_file: "crates/ay-sat/src/solver/restart.rs",
            });
        }
        if let Some(d) = check_tolerance(z.restarts, c.restarts, 10, 5) {
            return Some(Divergence {
                class: "restart_gate",
                event_class: "mode_switch",
                seq_index: i,
                ay_conflicts: z.conflicts,
                cadical_conflicts: c.conflicts,
                detail: format!("Mode switch #{i}: restart diff={d}"),
                owning_file: "crates/ay-sat/src/solver/restart.rs",
            });
        }
    }
    None
}

fn compare_inprocessing(ay: &[&Event], cad: &[&Event]) -> Option<Divergence> {
    for i in 0..ay.len().min(cad.len()) {
        let (z, c) = (ay[i], cad[i]);
        if let Some(d) = check_tolerance(z.active_vars, c.active_vars, 20, 50) {
            return Some(Divergence {
                class: "variable_elimination",
                event_class: "inprocessing",
                seq_index: i,
                ay_conflicts: z.conflicts,
                cadical_conflicts: c.conflicts,
                detail: format!("Inprocessing #{i}: active var diff={d}"),
                owning_file: "crates/ay-sat/src/solver/inprocessing/bve.rs",
            });
        }
        if let Some(d) = check_tolerance(z.irredundant, c.irredundant, 10, 200) {
            return Some(Divergence {
                class: "clause_divergence",
                event_class: "inprocessing",
                seq_index: i,
                ay_conflicts: z.conflicts,
                cadical_conflicts: c.conflicts,
                detail: format!("Inprocessing #{i}: irredundant diff={d}"),
                owning_file: "crates/ay-sat/src/solver/inprocessing.rs",
            });
        }
        if let Some(d) = check_tolerance(z.conflicts, c.conflicts, 5, 500) {
            return Some(Divergence {
                class: "inprocessing_entry",
                event_class: "inprocessing",
                seq_index: i,
                ay_conflicts: z.conflicts,
                cadical_conflicts: c.conflicts,
                detail: format!("Inprocessing #{i}: conflict diff={d}"),
                owning_file: "crates/ay-sat/src/solver/inprocessing.rs",
            });
        }
    }
    None
}

/// Compare reduction scheduling between AY and CaDiCaL.
///
/// NOTE: AY does not yet emit diagnostic events for reductions, so the AY
/// list will be empty until `emit_diagnostic_reduction()` is added to the
/// reduce_db path. This comparator is pre-wired for when that emission exists.
fn compare_reductions(ay: &[&Event], cad: &[&Event]) -> Option<Divergence> {
    for i in 0..ay.len().min(cad.len()) {
        if let Some(d) = check_tolerance(ay[i].conflicts, cad[i].conflicts, 10, 100) {
            return Some(Divergence {
                class: "reduction_gate",
                event_class: "reduction",
                seq_index: i,
                ay_conflicts: ay[i].conflicts,
                cadical_conflicts: cad[i].conflicts,
                detail: format!("Reduction #{i}: conflict diff={d}"),
                owning_file: "crates/ay-sat/src/solver/reduction.rs",
            });
        }
    }
    None
}

fn filter_events(evts: &[Event], pred: fn(&EventKind) -> bool) -> Vec<&Event> {
    evts.iter().filter(|e| pred(&e.kind)).collect()
}

fn find_divergence(ay: &[Event], cadical: &[Event]) -> Option<Divergence> {
    let is_mode = |k: &EventKind| matches!(k, EventKind::ModeSwitch { .. });
    let is_inproc = |k: &EventKind| matches!(k, EventKind::Inprocessing);
    let is_reduce = |k: &EventKind| matches!(k, EventKind::Reduction);

    let candidates = [
        compare_mode_switches(
            &filter_events(ay, is_mode),
            &filter_events(cadical, is_mode),
        ),
        compare_inprocessing(
            &filter_events(ay, is_inproc),
            &filter_events(cadical, is_inproc),
        ),
        compare_reductions(
            &filter_events(ay, is_reduce),
            &filter_events(cadical, is_reduce),
        ),
    ];
    candidates
        .into_iter()
        .flatten()
        .min_by_key(|d| d.ay_conflicts.min(d.cadical_conflicts))
}

fn print_summary(label: &str, events: &[Event]) {
    let mut counts: BTreeMap<&str, usize> = BTreeMap::new();
    let (mut max_c, mut max_r) = (0u64, 0u64);
    for e in events {
        *counts.entry(e.kind.name()).or_default() += 1;
        max_c = max_c.max(e.conflicts);
        max_r = max_r.max(e.restarts);
    }
    println!(
        "  {label}: {} milestones, max_conflicts={max_c}, max_restarts={max_r}",
        events.len()
    );
    for (name, n) in &counts {
        println!("    {name:20} {n}");
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 3 {
        eprintln!(
            "usage: {} <ay_trace.jsonl> <cadical_output.txt>\n\
             CTB Wave-2: finds first AY/CaDiCaL trajectory divergence.\n\
             Generate: AY_DIAGNOSTIC_FILE=ay.jsonl ./ay input.cnf\n\
             Generate: cadical input.cnf > cadical.txt 2>&1",
            args[0]
        );
        std::process::exit(1);
    }
    let ay_events = parse_ay_trace(Path::new(&args[1]));
    let cadical_events = parse_cadical_output(Path::new(&args[2]));

    println!("=== CTB Wave-2: Search Trajectory Comparator ===\n");
    print_summary("AY", &ay_events);
    print_summary("CaDiCaL", &cadical_events);
    println!();

    match find_divergence(&ay_events, &cadical_events) {
        Some(d) => {
            println!("FIRST DIVERGENCE FOUND");
            println!("  class:       {}", d.class);
            println!("  event:       {} #{}", d.event_class, d.seq_index);
            println!("  AY conf:     {}", d.ay_conflicts);
            println!("  CaDiCaL conf:{}", d.cadical_conflicts);
            println!("  detail:      {}", d.detail);
            println!("\nOWNING FILE: {}", d.owning_file);
        }
        None if ay_events.is_empty() || cadical_events.is_empty() => {
            println!(
                "INSUFFICIENT DATA: AY={}, CaDiCaL={}",
                ay_events.len(),
                cadical_events.len()
            );
        }
        None => {
            println!(
                "NO DIVERGENCE: trajectories match ({} AY, {} CaDiCaL milestones)",
                ay_events.len(),
                cadical_events.len()
            );
        }
    }
}
