// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// Fast streaming DIMACS parser path for large formulas.
///
/// Scan a DIMACS CNF body for the maximum variable index that actually appears
/// — the content-driven variable count, independent of the (untrusted) declared
/// header. Comment (`c`), end-marker (`%`), and `p` header lines are skipped;
/// every other line is clause data whose integer tokens are variable references.
/// Uses saturating arithmetic so an over-long digit run cannot wrap.
fn scan_max_variable(bytes: &[u8]) -> usize {
    let mut max_var: usize = 0;
    let mut pos = 0usize;
    let len = bytes.len();
    while pos < len {
        while pos < len && matches!(bytes[pos], b' ' | b'\t' | b'\r' | b'\n') {
            pos += 1;
        }
        if pos >= len {
            break;
        }
        match bytes[pos] {
            b'c' | b'p' => {
                while pos < len && bytes[pos] != b'\n' {
                    pos += 1;
                }
            }
            b'%' => break,
            _ => {
                // Clause line: read signed integer tokens until end of line.
                while pos < len && bytes[pos] != b'\n' {
                    while pos < len && matches!(bytes[pos], b' ' | b'\t' | b'\r') {
                        pos += 1;
                    }
                    if pos >= len || bytes[pos] == b'\n' {
                        break;
                    }
                    if bytes[pos] == b'-' || bytes[pos] == b'+' {
                        pos += 1;
                    }
                    let mut val: usize = 0;
                    let mut saw_digit = false;
                    while pos < len && bytes[pos].is_ascii_digit() {
                        val = val
                            .saturating_mul(10)
                            .saturating_add((bytes[pos] - b'0') as usize);
                        saw_digit = true;
                        pos += 1;
                    }
                    if saw_digit {
                        max_var = max_var.max(val);
                    }
                    // Skip any trailing non-whitespace so we always make progress.
                    while pos < len && !matches!(bytes[pos], b' ' | b'\t' | b'\r' | b'\n') {
                        pos += 1;
                    }
                }
            }
        }
    }
    max_var
}

/// Parses DIMACS bytes directly into `solver.add_clause()`, skipping all
/// intermediate data structures. On shuffling-2 (98MB, 4.7M clauses),
/// this reduces parse+load from >15s to ~2s.
fn run_streaming(
    content: &str,
    stats_cfg: stats_output::StatsConfig,
    variant: SolverVariant,
    variant_source: DecisionSource,
) {
    run_streaming_body(content, stats_cfg, variant, variant_source)
}
