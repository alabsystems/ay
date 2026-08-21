// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Source scan behind the knob census.
//!
//! Deliberately a source scan and not a macro, for the same reason
//! `tests/env_ledger/source_scan.rs` is: the defect being caught is a knob
//! wired by hand at a fresh call site, and no macro can see a call site that
//! was never written.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

/// The `tune` accessors. Any of these applied to a `Knob` is a READ.
///
/// Ordered longest-first so a prefix never shadows a longer name (`on` must not
/// match the head of `on_strict`).
pub(crate) const ACCESSORS: &[&str] = &[
    "on_unless_zero",
    "on_strict",
    "caller_flag",
    "count_opt",
    "real_opt",
    "count",
    "real",
    "num",
    "on",
];

/// One call site.
#[derive(Debug, Clone)]
pub(crate) struct Site {
    pub(crate) file: String,
    pub(crate) line: usize,
    /// The accessor for a read; `"with"` or `"table"` for a write.
    pub(crate) how: String,
    /// Source text from the call to the end of its statement, trimmed. This is
    /// where a reader's compiled default lives (`unwrap_or(..)`, or the second
    /// argument of `count`/`num`/`real`).
    pub(crate) expr: String,
}

/// One knob's row in the census.
#[derive(Debug, Clone, Default)]
pub(crate) struct Row {
    pub(crate) variant: String,
    /// CLI spelling, from `Knob::label`.
    pub(crate) label: String,
    pub(crate) readers: Vec<Site>,
    /// Writers on an OPERATOR-REACHABLE carrier: `src/opts/`, which is the only
    /// place `EngineEconomics` lowers a typed setting into the `Profile`.
    pub(crate) writers: Vec<Site>,
    /// Writers elsewhere in `src/`: sub-solve overrides and test scaffolding.
    /// These do NOT make a knob reachable by an operator and never satisfy the
    /// gate — `bab.rs` setting `Knob::NodeGmi` for its own guard test is not a
    /// carrier for `--node-gmi`.
    pub(crate) internal_writers: Vec<Site>,
    /// Compiled default, as the reader spells it. Empty when every reader
    /// branches on the `Option` itself.
    pub(crate) default: String,
    /// The reader latches its value in a `OnceLock`, so the FIRST read in the
    /// process wins. That is the lane hazard: if the first read can happen
    /// outside a `tune::activate_caller` frame, the knob is pinned to its
    /// compiled default for the life of the process no matter what is passed
    /// later. `--no-float` is the worked example (`session::float_lane_enabled`).
    pub(crate) cached: bool,
    /// A `tune::activate_caller` frame is installed somewhere in the reader's
    /// own file, or the reader is in a file every entry point frames. Advisory:
    /// full lane reachability is interprocedural and is not decided here.
    pub(crate) file_installs_frame: bool,
}

fn rust_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for e in entries.flatten() {
        let p = e.path();
        if p.is_dir() {
            rust_files(&p, out);
        } else if p.extension().is_some_and(|x| x == "rs") {
            out.push(p);
        }
    }
    out.sort();
}

/// Blank out `//` line comments, preserving byte offsets and line numbers.
///
/// Without this, a doc comment writing `tune::on(Knob::Foo)` as an example
/// would register as a call site — the census would then claim a reader that
/// does not exist, which is the same class of lie it exists to catch.
fn blank_comments(src: &str) -> String {
    let mut out = String::with_capacity(src.len());
    for line in src.split_inclusive('\n') {
        match line.find("//") {
            Some(i) => {
                out.push_str(&line[..i]);
                for c in line[i..].chars() {
                    out.push(if c == '\n' { '\n' } else { ' ' });
                }
            }
            None => out.push_str(line),
        }
    }
    out
}

fn ident_at(s: &str, at: usize) -> &str {
    let bytes = s.as_bytes();
    let mut end = at;
    while end < bytes.len() && (bytes[end].is_ascii_alphanumeric() || bytes[end] == b'_') {
        end += 1;
    }
    &s[at..end]
}

/// Skip whitespace, then an optional `crate::` / `tune::` qualification, then
/// require `Knob::` and return the variant name.
fn knob_after(s: &str, mut at: usize) -> Option<(&str, usize)> {
    let bytes = s.as_bytes();
    while at < bytes.len() && bytes[at].is_ascii_whitespace() {
        at += 1;
    }
    for prefix in ["crate::tune::", "crate::", "tune::"] {
        if s[at..].starts_with(prefix) {
            at += prefix.len();
            break;
        }
    }
    let rest = &s[at..];
    let stripped = rest.strip_prefix("Knob::")?;
    let variant = ident_at(stripped, 0);
    if variant.is_empty() {
        return None;
    }
    Some((variant, at + "Knob::".len() + variant.len()))
}

/// The statement a call site sits in, capped so a scan never quotes a page.
fn statement_from(s: &str, at: usize) -> String {
    let end = s[at..]
        .find(';')
        .map_or(s.len(), |i| (at + i + 1).min(s.len()));
    let end = end.min(at + 400);
    s[at..end].split_whitespace().collect::<Vec<_>>().join(" ")
}

fn line_of(s: &str, at: usize) -> usize {
    s[..at].matches('\n').count() + 1
}

/// The knob variants and their CLI spellings, parsed from `Knob::label`.
///
/// Parsed rather than imported: `Knob` is `pub(crate)`, and an integration test
/// deliberately sits outside the crate so it sees exactly the surface an
/// operator does.
fn labels(root: &Path) -> Vec<(String, String)> {
    let src = std::fs::read_to_string(root.join("src/tune/knob.rs")).expect("knob.rs is readable");
    let src = blank_comments(&src);
    let mut out = Vec::new();
    for line in src.lines() {
        let line = line.trim();
        let Some(rest) = line.strip_prefix("Self::") else {
            continue;
        };
        let Some((variant, tail)) = rest.split_once(" => ") else {
            continue;
        };
        let Some(start) = tail.find('"') else {
            continue;
        };
        let Some(len) = tail[start + 1..].find('"') else {
            continue;
        };
        out.push((
            variant.trim().to_string(),
            tail[start + 1..start + 1 + len].to_string(),
        ));
    }
    out
}

/// Build the census: every knob, its readers, its writers, its default, and
/// whether the read is `OnceLock`-latched.
pub(crate) fn census(root: &Path) -> Vec<Row> {
    let mut rows: BTreeMap<String, Row> = labels(root)
        .into_iter()
        .map(|(variant, label)| {
            (
                variant.clone(),
                Row {
                    variant,
                    label,
                    ..Row::default()
                },
            )
        })
        .collect();

    let mut files = Vec::new();
    rust_files(&root.join("src"), &mut files);
    for path in files {
        let rel = path
            .strip_prefix(root)
            .unwrap_or(&path)
            .to_string_lossy()
            .replace('\\', "/");
        let raw = std::fs::read_to_string(&path).expect("source file is readable");
        let src = blank_comments(&raw);
        let installs_frame = src.contains("tune::activate_caller(");
        // The module that DEFINES the layer is not a user of it: `tune.rs`'s own
        // unit tests set and read knobs to pin the resolution order, and counting
        // those as production sites would let a knob look wired because its own
        // accessor test touched it.
        let is_tune_module = rel == "src/tune.rs" || rel.starts_with("src/tune/");
        // Readers.
        for (i, _) in src.match_indices("tune::") {
            let after = i + "tune::".len();
            let name = ident_at(&src, after);
            if !ACCESSORS.contains(&name) {
                continue;
            }
            let mut j = after + name.len();
            while src.as_bytes().get(j).is_some_and(u8::is_ascii_whitespace) {
                j += 1;
            }
            if src.as_bytes().get(j) != Some(&b'(') {
                continue;
            }
            let Some((variant, _)) = knob_after(&src, j + 1) else {
                continue;
            };
            let Some(row) = rows.get_mut(variant) else {
                continue;
            };
            if is_tune_module {
                continue;
            }
            let stmt = statement_from(&src, i);
            row.cached |= line_context_is_cached(&src, i);
            row.file_installs_frame |= installs_frame;
            row.readers.push(Site {
                file: rel.clone(),
                line: line_of(&src, i),
                how: name.to_string(),
                expr: stmt,
            });
        }
        // WRITERS. Two forms, both matched on `Knob::` and then verified in each
        // direction rather than on a literal `.with(Knob::` / `(Knob::`.
        //
        //   A. `Profile::with(knob, setting)` — the builder call.
        //   B. `(Knob::X, self.field.map(..))` — an entry in a lowering table.
        //
        // Adjacency is NOT safe to assume: rustfmt breaks a long entry across
        // lines, so the paren and the variant are separated for exactly the
        // entries whose expressions are longest. An adjacency scan missed
        // `NoDualChurnBand`, `NoRtBitsKey`, `NoWideBloom`, `NoChainShape`,
        // `NoChainPreorder` and `EagerPerturbMode` — six real carriers reported
        // as defects, which is the failure mode that trains an operator to
        // ignore the gate.
        for (i, _) in src.match_indices("Knob::") {
            let before = src[..i].trim_end();
            let Some(before) = before.strip_suffix('(') else {
                continue;
            };
            let variant = ident_at(&src, i + "Knob::".len());
            let after = src[i + "Knob::".len() + variant.len()..].trim_start();
            let how = if before.trim_end().ends_with(".with") {
                "with"
            } else if after
                .strip_prefix(',')
                .is_some_and(|rest| rest.trim_start().starts_with("self."))
            {
                "table"
            } else {
                continue;
            };
            let Some(row) = rows.get_mut(variant) else {
                continue;
            };
            let site = Site {
                file: rel.clone(),
                line: line_of(&src, i),
                how: how.to_string(),
                expr: statement_from(&src, i),
            };
            if rel.starts_with("src/opts/") {
                row.writers.push(site);
            } else if !is_tune_module {
                row.internal_writers.push(site);
            }
        }
    }

    let mut out: Vec<Row> = rows.into_values().collect();
    for row in &mut out {
        row.default = default_of(row);
    }
    out.sort_by(|a, b| a.variant.cmp(&b.variant));
    out
}

/// Whether the enclosing 400 bytes hold a `OnceLock` latch.
///
/// A window rather than a parse: every latched reader in this crate spells it
/// `static X: OnceLock<..>` immediately above `X.get_or_init(|| ..read..)`.
fn line_context_is_cached(src: &str, at: usize) -> bool {
    let mut lo = at.saturating_sub(400);
    while lo < src.len() && !src.is_char_boundary(lo) {
        lo += 1;
    }
    let mut hi = (at + 200).min(src.len());
    while hi > lo && !src.is_char_boundary(hi) {
        hi -= 1;
    }
    src[lo..hi].contains("get_or_init")
}

/// The compiled default a reader falls back to, as the source spells it.
fn default_of(row: &Row) -> String {
    for site in &row.readers {
        if let Some(i) = site.expr.find("unwrap_or(") {
            let rest = &site.expr[i + "unwrap_or(".len()..];
            if let Some(end) = rest.find(')') {
                return rest[..end].to_string();
            }
        }
        if matches!(site.how.as_str(), "count" | "num" | "real") {
            if let Some(i) = site.expr.find("Knob::") {
                let rest = &site.expr[i..];
                if let Some(c) = rest.find(", ") {
                    let tail = &rest[c + 2..];
                    let end = tail.find(')').unwrap_or(tail.len());
                    return tail[..end].to_string();
                }
            }
        }
        if site.how == "on" {
            return "false".to_string();
        }
        if site.how == "on_unless_zero" {
            return "true".to_string();
        }
    }
    if row.readers.is_empty() {
        String::new()
    } else {
        "None (absent)".to_string()
    }
}
