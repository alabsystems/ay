// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Statistics on the watchdog's exits (roadmap D5: statistics on every exit).
//!
//! When a solve does not stop within the grace after its deadline or its
//! memory breach, the watchdog thread ends the process. The executor's
//! statistics live on the solver thread, out of the watchdog's reach, so a
//! run ended this way used to print none: the D7 held-out scoreboard
//! (`ay-d7-6e3b2ad92a`, `-T:10`) counted 171 such `--z3-mode` runs in 2,202,
//! and could say nothing about where they were or what they had done.
//!
//! This block is built from what any thread can read: the process-wide work
//! ledger and the mirrored solve phase (`ay_core::resource`), the clock and
//! the allocator. `:resource.hard_exit 1` marks it, so it is never mistaken
//! for a solve that stopped on its own. Its work counters are process totals.

use std::io::{self, Write};
use std::sync::atomic::{AtomicBool, AtomicU8, Ordering};
use std::time::Duration;

const HUMAN: u8 = 1;
const JSON: u8 = 2;

/// Which statistics formats the run asked for (`--stats`/`-st`,
/// `--stats-full`, `--stats-json`).
static REQUESTED: AtomicU8 = AtomicU8::new(0);
/// Whether the solve path already printed its own statistics block.
static PRINTED: AtomicBool = AtomicBool::new(false);

/// Record which statistics formats the run asked for.
pub(crate) fn note_requested(human: bool, json: bool) {
    let mut bits = 0;
    if human {
        bits |= HUMAN;
    }
    if json {
        bits |= JSON;
    }
    REQUESTED.store(bits, Ordering::SeqCst);
}

/// Record that the solve path printed its statistics, so an exit that
/// follows prints no second block.
pub(crate) fn note_printed() {
    PRINTED.store(true, Ordering::SeqCst);
}

/// What ended the run.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum HardExitCause {
    Timeout,
    Memout,
}

impl HardExitCause {
    fn reason(self) -> &'static str {
        match self {
            Self::Timeout => "timeout",
            Self::Memout => "memout",
        }
    }

    fn detail(self, grace: Duration) -> String {
        let limit = match self {
            Self::Timeout => "the deadline",
            Self::Memout => "the memory budget breach",
        };
        format!(
            "the solve did not stop within {:.1} s of {limit}; the watchdog ended the process",
            grace.as_secs_f64()
        )
    }
}

/// Everything the block reports, read at the moment of the exit.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct HardExitReading {
    pub(crate) cause: HardExitCause,
    pub(crate) grace: Duration,
    pub(crate) elapsed: Option<Duration>,
    pub(crate) memory_mb: f64,
    pub(crate) max_memory_mb: f64,
    pub(crate) work: ay_core::resource::WorkSnapshot,
    pub(crate) phase: Option<(String, String)>,
}

impl HardExitReading {
    fn now(cause: HardExitCause, grace: Duration, elapsed: Option<Duration>) -> Self {
        const MB: f64 = 1024.0 * 1024.0;
        Self {
            cause,
            grace,
            elapsed,
            memory_mb: ay_sys::current_footprint_bytes() as f64 / MB,
            max_memory_mb: ay_sys::current_rss_bytes() as f64 / MB,
            work: ay_core::resource::work().snapshot(),
            phase: ay_core::resource::phase_snapshot(),
        }
    }

    fn rows(&self) -> Vec<(&'static str, String)> {
        let (phase, cost_center) = self
            .phase
            .clone()
            .unwrap_or_else(|| ("unattributed".to_string(), "unattributed".to_string()));
        let quoted = |s: &str| format!("\"{}\"", s.replace('\\', "\\\\").replace('"', "\\\""));
        let mut rows = Vec::new();
        if let Some(elapsed) = self.elapsed {
            rows.push((":total-time", format!("{:.3}", elapsed.as_secs_f64())));
        }
        rows.push((":memory", format!("{:.2}", self.memory_mb)));
        rows.push((":max-memory", format!("{:.2}", self.max_memory_mb)));
        rows.push((":all_lanes.conflicts", self.work.sat_conflicts.to_string()));
        rows.push((":all_lanes.decisions", self.work.sat_decisions.to_string()));
        rows.push((
            ":all_lanes.round_trips",
            self.work.split_round_trips.to_string(),
        ));
        rows.push((":resource.hard_exit", "1".to_string()));
        rows.push((":unknown.reason", quoted(self.cause.reason())));
        rows.push((":unknown.phase", quoted(&phase)));
        rows.push((":unknown.cost_center", quoted(&cost_center)));
        rows.push((":unknown.detail", quoted(&self.cause.detail(self.grace))));
        rows
    }

    /// The `(:statistics …)` block, in the `--stats-full` layout.
    pub(crate) fn render_human(&self) -> String {
        let mut out = String::from("(:statistics\n");
        for (key, value) in self.rows() {
            out.push_str(&format!("  {key} {value}\n"));
        }
        out.push_str(")\n");
        out
    }

    /// One JSON object, in the `--stats-json` layout.
    pub(crate) fn render_json(&self) -> String {
        let mut map = serde_json::Map::new();
        map.insert("mode".to_string(), serde_json::json!("smt"));
        map.insert("result".to_string(), serde_json::json!("unknown"));
        for (key, value) in self.rows() {
            let key = key.trim_start_matches(':').to_string();
            let value = match serde_json::from_str::<serde_json::Value>(&value) {
                Ok(parsed) => parsed,
                Err(_) => serde_json::Value::String(value),
            };
            map.insert(key, value);
        }
        format!("{}\n", serde_json::Value::Object(map))
    }
}

/// Print the statistics the run asked for, if the solve path has not, and
/// if the run serves SMT-LIB (the DIMACS route has its own comment grammar).
/// Called from the watchdog's exit paths just before `process::exit`.
pub(crate) fn emit(cause: HardExitCause, grace: Duration, elapsed: Option<Duration>) {
    let requested = REQUESTED.load(Ordering::SeqCst);
    if requested == 0
        || PRINTED.swap(true, Ordering::SeqCst)
        || crate::VerdictGrammarRoute::load() == crate::VerdictGrammarRoute::Dimacs
    {
        return;
    }
    let reading = HardExitReading::now(cause, grace, elapsed);
    let mut text = String::new();
    if requested & HUMAN != 0 {
        text.push_str(&reading.render_human());
    }
    if requested & JSON != 0 {
        text.push_str(&reading.render_json());
    }
    let _ = Write::write_all(&mut io::stderr(), text.as_bytes());
    let _ = Write::flush(&mut io::stderr());
}

/// The statistics of a run the allocator's hard memory ceiling ends
/// (`ay_sys::HardMemoryCeiling::statistics`). It runs INSIDE the global
/// allocator, so it allocates nothing: static bytes, integers formatted on the
/// stack, and atomics. The phase is not readable without a lock, so it is not
/// reported.
pub(crate) fn write_ceiling_block(write: &mut dyn FnMut(&[u8])) {
    if REQUESTED.load(Ordering::SeqCst) & HUMAN == 0
        || PRINTED.swap(true, Ordering::SeqCst)
        || crate::VerdictGrammarRoute::load() == crate::VerdictGrammarRoute::Dimacs
    {
        return;
    }
    let elapsed_ms = crate::START_TIME
        .get()
        .map(|start| u64::try_from(start.elapsed().as_millis()).unwrap_or(u64::MAX));
    render_ceiling_block(ay_core::resource::work().snapshot(), elapsed_ms, write);
}

/// [`write_ceiling_block`]'s text, allocation-free.
fn render_ceiling_block(
    work: ay_core::resource::WorkSnapshot,
    elapsed_ms: Option<u64>,
    write: &mut dyn FnMut(&[u8]),
) {
    write(b"(:statistics\n");
    if let Some(ms) = elapsed_ms {
        write(b"  :total-time ");
        write_u64(write, ms / 1000);
        write(b".");
        let frac = ms % 1000;
        write(&[
            b'0' + (frac / 100) as u8,
            b'0' + (frac / 10 % 10) as u8,
            b'0' + (frac % 10) as u8,
        ]);
        write(b"\n");
    }
    for (key, value) in [
        (&b"  :all_lanes.conflicts "[..], work.sat_conflicts),
        (&b"  :all_lanes.decisions "[..], work.sat_decisions),
        (&b"  :all_lanes.round_trips "[..], work.split_round_trips),
    ] {
        write(key);
        write_u64(write, value);
        write(b"\n");
    }
    write(
        b"  :resource.hard_exit 1\n  :unknown.reason \"memout\"\n  :unknown.phase \"unattributed\"\n  \
          :unknown.detail \"the allocator's hard memory ceiling refused an allocation; the process \
          ended at once\"\n)\n",
    );
}

/// Decimal digits of `value`, formatted on the stack.
fn write_u64(write: &mut dyn FnMut(&[u8]), mut value: u64) {
    let mut digits = [0u8; 20];
    let mut start = digits.len();
    loop {
        start -= 1;
        digits[start] = b'0' + (value % 10) as u8;
        value /= 10;
        if value == 0 {
            break;
        }
    }
    write(&digits[start..]);
}

#[cfg(test)]
mod tests {
    use super::*;

    fn reading() -> HardExitReading {
        HardExitReading {
            cause: HardExitCause::Timeout,
            grace: Duration::from_secs(2),
            elapsed: Some(Duration::from_millis(12_034)),
            memory_mb: 812.5,
            max_memory_mb: 900.25,
            work: ay_core::resource::WorkSnapshot {
                sat_conflicts: 41,
                sat_decisions: 900,
                split_round_trips: 3,
                deadline_shares: 1,
                deadline_shares_spent: 1,
            },
            phase: Some((
                "ground-result-mapping".to_string(),
                "ground-result-mapping".to_string(),
            )),
        }
    }

    /// The block uses the standard S-expression syntax for a
    /// `--stats-full` block: `(:statistics`, one `  :key value` row per line,
    /// `)`; string values quoted.
    #[test]
    fn the_block_is_a_stats_full_block_marked_as_a_hard_exit() {
        let text = reading().render_human();
        let mut lines = text.lines();
        assert_eq!(lines.next(), Some("(:statistics"));
        let rows: Vec<&str> = lines.collect();
        assert_eq!(rows.last(), Some(&")"));
        for row in &rows[..rows.len() - 1] {
            assert!(row.starts_with("  :"), "{row}");
            assert!(row.split_whitespace().count() >= 2, "{row}");
        }
        assert!(text.contains("  :resource.hard_exit 1\n"));
        assert!(text.contains("  :unknown.reason \"timeout\"\n"));
        assert!(text.contains("  :unknown.phase \"ground-result-mapping\"\n"));
        assert!(text.contains("  :all_lanes.round_trips 3\n"));
        assert!(text.contains("  :total-time 12.034\n"));
        assert!(text.contains("within 2.0 s of the deadline"));
    }

    #[test]
    fn an_unattributed_memout_says_so() {
        let mut r = reading();
        r.cause = HardExitCause::Memout;
        r.phase = None;
        r.elapsed = None;
        let text = r.render_human();
        assert!(text.contains("  :unknown.reason \"memout\"\n"));
        assert!(text.contains("  :unknown.phase \"unattributed\"\n"));
        assert!(!text.contains(":total-time"));
        assert!(text.contains("memory budget breach"));
    }

    #[test]
    fn the_ceiling_block_is_a_stats_full_block_built_without_allocating_state() {
        let mut out: Vec<u8> = Vec::new();
        let work = ay_core::resource::WorkSnapshot {
            sat_conflicts: 0,
            sat_decisions: 1_234_567,
            split_round_trips: 42,
            deadline_shares: 0,
            deadline_shares_spent: 0,
        };
        render_ceiling_block(work, Some(7_205), &mut |bytes| out.extend_from_slice(bytes));
        let text = String::from_utf8(out).expect("utf-8");
        assert!(text.starts_with("(:statistics\n"), "{text}");
        assert!(text.ends_with(")\n"), "{text}");
        assert!(text.contains("  :total-time 7.205\n"), "{text}");
        assert!(text.contains("  :all_lanes.conflicts 0\n"), "{text}");
        assert!(text.contains("  :all_lanes.decisions 1234567\n"), "{text}");
        assert!(text.contains("  :resource.hard_exit 1\n"), "{text}");
        assert!(text.contains("  :unknown.reason \"memout\"\n"), "{text}");
        assert!(
            text.contains("  :unknown.detail \"the allocator's hard memory ceiling"),
            "{text}"
        );
        for line in text.lines().skip(1).filter(|l| *l != ")") {
            assert!(line.starts_with("  :"), "{line}");
        }
    }

    #[test]
    fn the_json_line_carries_the_same_facts() {
        let line = reading().render_json();
        let value: serde_json::Value = serde_json::from_str(line.trim()).expect("one JSON object");
        assert_eq!(value["resource.hard_exit"], serde_json::json!(1));
        assert_eq!(value["unknown.reason"], serde_json::json!("timeout"));
        assert_eq!(value["all_lanes.conflicts"], serde_json::json!(41));
        assert_eq!(value["result"], serde_json::json!("unknown"));
    }
}
