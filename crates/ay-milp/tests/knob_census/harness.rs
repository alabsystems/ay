// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Source scan behind the HARNESS-FLAG half of the census.
//!
//! [`super::scan`] enumerates `Knob` variants and their `src/` reader/writer
//! chains. That universe cannot see `--lu`, because `--lu` was never a `Knob`:
//! it was a bare name pushed onto `milp_profile`'s local `switch_flags` vector.
//! This scan covers the other axis — the MEASUREMENT SURFACES themselves, in
//! `examples/` and `src/bin/`, which `scan.rs` does not walk for flags at all.

use std::path::{Path, PathBuf};

/// One measurement surface: a file that parses command-line flags.
#[derive(Debug, Clone)]
pub(crate) struct Surface {
    /// Path relative to the crate root, `/`-separated.
    pub(crate) file: String,
    /// The file hands `engine_cli`'s own tables (`VALUE_FLAGS` /
    /// `switch_flags()`) to `Flags::parse`, so it ACCEPTS the whole engine
    /// surface — every `--no-cuts`, `--devex`, `--trace` there parses cleanly.
    pub(crate) declares_engine_surface: bool,
    /// The file calls `engine_cli::apply`, which is the ONLY thing that turns
    /// an accepted engine flag into a `SolveOpts` the engine reads.
    pub(crate) applies_engine_flags: bool,
    /// Flag names the file adds to a parse table BEYOND `engine_cli`'s: the
    /// `switch_flags.push("lu")` family. These have no carrier by construction
    /// — `apply` has never heard of them — so each needs its own reader, and
    /// nothing but a disposition table can check that it has one.
    pub(crate) local_flags: Vec<String>,
    /// The file hands `engine_cli::VALUE_FLAGS` — the `ay-milp solve`
    /// subcommand's table — to the parser, and so accepts the SOLVE-ONLY
    /// names as well as the engine ones.
    ///
    /// `VALUE_FLAGS` is a strict superset of `applied_flags()`. The difference
    /// is the set of names only `solve` itself reads, and a surface that is not
    /// `solve` can carry none of them however faithfully it calls `apply`.
    /// This is the distinction `declares_engine_surface` cannot draw, and the
    /// one `cert_probe --require` fell through.
    pub(crate) uses_solve_value_table: bool,
    /// The file's own comment-blanked text spliced with its `#[path]`
    /// submodules — the same `unit` the two booleans above are decided on.
    ///
    /// Carried so a test can ask whether a name appears as a quoted literal
    /// anywhere in the entry point. That question is DELIBERATELY GENEROUS: a
    /// missed reader would make the gate cry wolf, and this repo has refused
    /// two scanners for exactly that. Over-matching only makes it quieter.
    pub(crate) unit: String,
}

fn rust_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            rust_files(&path, out);
        } else if path.extension().is_some_and(|x| x == "rs") {
            out.push(path);
        }
    }
    out.sort();
}

/// Blank out `//` line comments, preserving byte offsets and line numbers.
///
/// Same reason `scan.rs` does it: this file's OWN doc comment names
/// `engine_cli::apply` and `switch_flags`, and a scan that counted a doc
/// mention as a call site would declare every surface clean — including the
/// one that is not.
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

/// String literals inside the parenthesised argument of a `push`/`extend` call
/// that starts at `at` (the byte index of the opening paren).
///
/// A brace/bracket-depth walk rather than a line scan: rustfmt breaks a long
/// `extend([...])` across lines, and `ay-milp.rs`'s four-name `extend` is
/// exactly that shape.
fn literals_in_call(src: &str, at: usize) -> Vec<String> {
    let bytes = src.as_bytes();
    let mut depth = 0i32;
    let mut out = Vec::new();
    let mut i = at;
    while i < bytes.len() {
        match bytes[i] {
            b'(' => depth += 1,
            b')' => {
                depth -= 1;
                if depth == 0 {
                    break;
                }
            }
            b'"' => {
                let start = i + 1;
                let mut j = start;
                while j < bytes.len() && bytes[j] != b'"' {
                    j += if bytes[j] == b'\\' { 2 } else { 1 };
                }
                if j <= bytes.len() {
                    out.push(src[start..j.min(src.len())].to_string());
                }
                i = j;
            }
            _ => {}
        }
        i += 1;
    }
    out
}

/// Whether the identifier immediately before `.push` / `.extend` names a flag
/// table. Deliberately a NAME test and not a type test: an integration test
/// sees no types, and every flag vector in the crate is spelled one of these.
fn is_flag_table(receiver: &str) -> bool {
    matches!(
        receiver,
        "switch_flags" | "switches" | "value_flags" | "values"
    )
}

fn receiver_before(src: &str, at: usize) -> &str {
    let head = src[..at].trim_end();
    let start = head
        .rfind(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
        .map_or(0, |i| i + 1);
    &head[start..]
}

/// The file's own text plus the text of every `#[path = "…"] mod` it declares.
///
/// WITHOUT THIS THE GATE LIES IN THE DANGEROUS DIRECTION. `src/bin/ay-milp.rs`
/// parses the engine surface in `cmd_solve` and applies it in
/// `ay_milp/solve_options.rs`, a `#[path]` submodule — so a single-file scan
/// sees a parse with no apply and reports the CLI's own solve command as the
/// defect. It happens to also call `apply` in `diag_options`, which would have
/// masked the flaw until the day someone split that out too. Splice the
/// submodules in and the question asked is the real one: can this ENTRY POINT
/// reach `apply` at all.
fn unit_text(root: &Path, path: &Path, src: &str) -> String {
    let mut out = src.to_string();
    let dir = path.parent().unwrap_or(root);
    for (i, _) in src.match_indices("#[path") {
        let Some(open) = src[i..].find('"').map(|k| i + k + 1) else {
            continue;
        };
        let Some(close) = src[open..].find('"').map(|k| open + k) else {
            continue;
        };
        let rel = &src[open..close];
        if let Ok(extra) = std::fs::read_to_string(dir.join(rel)) {
            out.push('\n');
            out.push_str(&blank_comments(&extra));
        }
    }
    out
}

/// Every measurement surface in `examples/` and `src/bin/`.
pub(crate) fn surfaces(root: &Path) -> Vec<Surface> {
    let mut files = Vec::new();
    rust_files(&root.join("examples"), &mut files);
    rust_files(&root.join("src/bin"), &mut files);
    let mut out = Vec::new();
    for path in files {
        let rel = path
            .strip_prefix(root)
            .unwrap_or(&path)
            .to_string_lossy()
            .replace('\\', "/");
        let raw = std::fs::read_to_string(&path).expect("source file is readable");
        let src = blank_comments(&raw);
        // BOTH entry points into the parser, and the second one is here because
        // its absence broke this scan the moment the five harnesses were moved
        // onto it: keyed on `Flags::parse` alone the surface count fell from 6
        // to 1, and only the `len() >= 4` vacuity assert in the tests caught it.
        // A scanner that recognises one spelling of the thing it audits stops
        // auditing the moment the codebase adopts the other.
        if !src.contains("Flags::parse") && !src.contains("parse_applied") {
            continue;
        }
        let unit = unit_text(root, &path, &src);
        // `parse_applied` counts: it hands the parser `applied_flags()`, which
        // IS the engine surface — every `--devex`, `--no-cuts`, `--trace` parses
        // there. So a surface that calls it and never calls `apply` is the same
        // defect `milp_speed` was, and stays caught.
        let declares_engine_surface = src.contains("switch_flags()")
            || src.contains("VALUE_FLAGS")
            || src.contains("parse_applied");
        let applies_engine_flags =
            unit.contains("engine_cli::apply") || unit.contains("engine_flags::apply");
        // Over `unit`, not `src`, for the same reason `applies_engine_flags` is:
        // a `#[path]` submodule of a bin is part of the same entry point, and a
        // declaration hidden there would otherwise be invisible — which is the
        // permissive direction, the one that lets a lever through.
        let mut local_flags = Vec::new();
        for method in [".push", ".extend"] {
            for (i, _) in unit.match_indices(method) {
                if !is_flag_table(receiver_before(&unit, i)) {
                    continue;
                }
                let Some(open) = unit[i..].find('(').map(|k| i + k) else {
                    continue;
                };
                local_flags.extend(literals_in_call(&unit, open));
            }
        }
        // AND the `parse_applied(args, &[..own values..], &[..own switches..])`
        // spelling, which is the canonical one now that the five harnesses use
        // it. Its own-name arguments are INLINE ARRAY LITERALS with no named
        // receiver, so the `.push`/`.extend` scan above cannot see them — the
        // shape a scanner keyed on a variable name always misses. Every string
        // literal inside the call is an own-name by construction: the first
        // argument is the `args` slice, a variable.
        for (i, _) in unit.match_indices("parse_applied") {
            let Some(open) = unit[i..].find('(').map(|k| i + k) else {
                continue;
            };
            local_flags.extend(literals_in_call(&unit, open));
        }
        local_flags.sort();
        local_flags.dedup();
        // Over `src`, not `unit`: the question is what THIS file hands the
        // parser. A `#[path]` submodule mentioning the constant for its own
        // reasons must not make the entry point look like `solve`.
        let uses_solve_value_table = src.contains("VALUE_FLAGS");
        out.push(Surface {
            file: rel,
            declares_engine_surface,
            applies_engine_flags,
            local_flags,
            uses_solve_value_table,
            unit,
        });
    }
    out
}
