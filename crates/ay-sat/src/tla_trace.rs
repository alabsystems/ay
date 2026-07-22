// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! TLA2-format JSONL trace writer for runtime verification.
//!
//! Emits traces in the JSONL format consumed by TLA2's `tla-check trace validate`:
//!
//! ```jsonl
//! {"type":"header","version":"1","module":"cdcl_test","variables":["assignment","trail","state","decisionLevel","learnedClauses"]}
//! {"type":"step","index":0,"state":{"assignment":{"type":"string","value":"..."},...}}
//! {"type":"step","index":1,"state":{...},"action":{"name":"Propagate"}}
//! ```
//!
//! This writer is used by the CDCL solver when the `AY_TRACE_FILE` env var
//! is set.  It is **not** a tracing subscriber — it writes directly to a file
//! to avoid routing every tracing event through JSON serialization.

use std::fs::File;
use std::io::{BufWriter, Write};
use std::sync::Mutex;

/// Writer that emits TLA2-format JSONL trace files.
///
/// Thread-safe via interior `Mutex`.  The typical usage is to store an
/// `Option<TlaTraceWriter>` on the solver struct — when `None`, no trace
/// overhead is incurred beyond the `if let` branch.
pub struct TlaTraceWriter {
    inner: Mutex<TlaTraceInner>,
}

struct TlaTraceInner {
    /// `None` when the trace file could not be created or a write failed;
    /// all subsequent trace output becomes a no-op so an I/O problem with
    /// the (env-var-fed) trace path degrades tracing instead of aborting
    /// the solve.
    writer: Option<BufWriter<File>>,
    step_index: usize,
}

impl TlaTraceWriter {
    /// Create a new trace writer.
    ///
    /// Writes the TLA2 header line immediately.  If the file cannot be
    /// created (or the header cannot be written), logs a one-line warning to
    /// stderr and returns a disabled writer whose steps are no-ops — the
    /// trace path typically comes from the `AY_TRACE_FILE` env var, and a
    /// bad path must not abort the solve.
    pub fn new(path: &str, module: &str, variables: &[&str]) -> Self {
        let writer = match Self::create_writer(path, module, variables) {
            Ok(writer) => Some(writer),
            Err(e) => {
                eprintln!(
                    "warning: failed to create TLA trace file {path}: {e}; TLA tracing disabled"
                );
                None
            }
        };

        Self {
            inner: Mutex::new(TlaTraceInner {
                writer,
                step_index: 0,
            }),
        }
    }

    fn create_writer(
        path: &str,
        module: &str,
        variables: &[&str],
    ) -> std::io::Result<BufWriter<File>> {
        let file = File::create(path)?;
        let mut writer = BufWriter::new(file);

        // Write TLA2-format header
        let header = serde_json::json!({
            "type": "header",
            "version": "1",
            "module": module,
            "variables": variables,
        });
        writeln!(writer, "{header}")?;
        writer.flush()?;
        Ok(writer)
    }

    /// Write a single trace step.
    ///
    /// `state` must be a JSON object whose keys match the `variables` declared
    /// in the header, with values encoded in TLA2's `JsonValue` format
    /// (e.g. `{"type":"int","value":42}`).
    ///
    /// `action` is `None` for the initial state (step 0) and `Some("ActionName")`
    /// for subsequent steps.
    #[allow(clippy::needless_pass_by_value)]
    pub fn write_step(&self, state: serde_json::Value, action: Option<&str>) {
        self.write_step_with_telemetry(state, action, None);
    }

    /// Write a single trace step with optional `telemetry` payload.
    ///
    /// The `telemetry` object is attached at the top-level of the step and is
    /// consumed by CHC/PDR trace validation tests.
    #[allow(clippy::needless_pass_by_value)]
    pub fn write_step_with_telemetry(
        &self,
        state: serde_json::Value,
        action: Option<&str>,
        telemetry: Option<serde_json::Value>,
    ) {
        let mut inner = self.inner.lock().expect("tla trace mutex poisoned");
        if inner.writer.is_none() {
            return;
        }
        let mut step = serde_json::json!({
            "type": "step",
            "index": inner.step_index,
            "state": state,
        });
        if let Some(a) = action {
            step["action"] = serde_json::json!({"name": a});
        }
        if let Some(payload) = telemetry {
            step["telemetry"] = payload;
        }
        let write_ok = inner
            .writer
            .as_mut()
            .is_some_and(|w| writeln!(w, "{step}").is_ok());
        if !write_ok {
            eprintln!("warning: failed to write TLA trace step; TLA tracing disabled");
            inner.writer = None;
            return;
        }
        // Flush periodically (every 64 steps) to avoid data loss on crash
        if inner.step_index.is_multiple_of(64) {
            if let Some(w) = inner.writer.as_mut() {
                let _ = w.flush();
            }
        }
        inner.step_index += 1;
    }

    /// Flush any buffered output and return the number of steps written.
    pub fn finish(&self) -> usize {
        let mut inner = self.inner.lock().expect("tla trace mutex poisoned");
        if let Some(w) = inner.writer.as_mut() {
            let _ = w.flush();
        }
        inner.step_index
    }
}

#[cfg(test)]
#[path = "tla_trace_tests.rs"]
mod tests;
