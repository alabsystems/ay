// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Set variable boolean decomposition round-trip tests for flatzinc-smt.
//!
//! Tests that `var set of lo..hi` boolean decomposition produces correct
//! SMT-LIB2 and solves correctly. With boolean decomposition (no bitvectors),
//! these tests can use z3 directly on the pure QF_LIA formulas.
//!
//! Part of #326 (set constraint soundness), #273 (MiniZinc entry).

use std::io::Write;
use std::process::{Command, Stdio};

use ay_core::kani_compat::{det_hash_map_new, DetHashMap as HashMap};
use ay_flatzinc_smt::translate;

fn translate_fzn(input: &str) -> ay_flatzinc_smt::TranslationResult {
    let model = ay_flatzinc_parser::parse_flatzinc(input).expect("parse failed");
    translate(&model).expect("translate failed")
}

/// Find z3 binary for set encoding verification.
fn z3_path() -> Option<String> {
    if let Ok(p) = std::env::var("Z3_PATH") {
        if std::path::Path::new(&p).exists() {
            return Some(p);
        }
    }
    if let Ok(output) = Command::new("which").arg("z3").output() {
        if output.status.success() {
            let path = String::from_utf8_lossy(&output.stdout).trim().to_string();
            if !path.is_empty() && std::path::Path::new(&path).exists() {
                return Some(path);
            }
        }
    }
    let default = "/opt/homebrew/bin/z3";
    if std::path::Path::new(default).exists() {
        return Some(default.to_string());
    }
    eprintln!("SKIP: z3 binary not found. Set Z3_PATH or install z3.");
    None
}

/// Run z3 on an SMT-LIB2 script. Returns (exit_code, stdout, stderr).
fn run_z3(smtlib: &str) -> Option<(i32, String, String)> {
    let z3 = z3_path()?;
    let mut child = Command::new(&z3)
        .args(["-smt2", "-in"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn z3");

    child
        .stdin
        .as_mut()
        .expect("stdin")
        .write_all(smtlib.as_bytes())
        .expect("write to z3 stdin");

    let output = child.wait_with_output().expect("wait for z3");
    let code = output.status.code().unwrap_or(-1);
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    Some((code, stdout, stderr))
}

/// Parse z3's `(get-value ...)` response into a variable->value map.
fn parse_get_value(line: &str) -> HashMap<String, String> {
    let mut result = det_hash_map_new();
    let trimmed = line.trim();
    let inner = trimmed
        .strip_prefix('(')
        .and_then(|s| s.strip_suffix(')'))
        .unwrap_or(trimmed);

    let mut chars = inner.chars().peekable();
    while let Some(&c) = chars.peek() {
        if c == '(' {
            chars.next();
            let name: String = chars.by_ref().take_while(|&c| c != ' ').collect();
            let mut value = String::new();
            let mut depth = 0;
            for c in chars.by_ref() {
                if c == '(' {
                    depth += 1;
                    value.push(c);
                } else if c == ')' {
                    if depth == 0 {
                        break;
                    }
                    depth -= 1;
                    value.push(c);
                } else {
                    value.push(c);
                }
            }
            let value = value.trim().to_string();
            if !name.is_empty() {
                result.insert(name, value);
            }
        } else {
            chars.next();
        }
    }
    result
}

/// Count true bits from the decomposed boolean set variable model.
fn count_true_bits(values: &HashMap<String, String>, set_name: &str, width: u32) -> usize {
    (0..width)
        .filter(|&i| {
            let key = format!("{set_name}__bit__{i}");
            values.get(&key).map(|v| v == "true").unwrap_or(false)
        })
        .count()
}

/// Check if a specific bit is true in the decomposed boolean set variable model.
fn bit_is_true(values: &HashMap<String, String>, set_name: &str, bit: u32) -> bool {
    let key = format!("{set_name}__bit__{bit}");
    values.get(&key).map(|v| v == "true").unwrap_or(false)
}

// ---- Tests ----

/// Verify set_card constraint: set_card(s, 2) where s is a set of 0..3.
#[test]
fn roundtrip_set_card() {
    let fzn = "var set of 0..3: s;\n\
               constraint set_card(s, 2);\n\
               solve satisfy;\n";
    let result = translate_fzn(fzn);
    let Some((code, stdout, stderr)) = run_z3(&result.smtlib) else {
        return;
    };
    assert_eq!(code, 0, "z3 exit code: stderr={stderr}");

    let lines: Vec<&str> = stdout.lines().collect();
    assert_eq!(
        lines[0], "sat",
        "set_card(s,2) should be sat, got: {stdout}"
    );

    let value_str = lines[1..].join(" ");
    let values = parse_get_value(&value_str);
    let popcount = count_true_bits(&values, "s", 4);
    assert_eq!(
        popcount, 2,
        "set_card(s,2) requires exactly 2 elements, got popcount={popcount}"
    );
}

/// Verify set_union: s3 = s1 union s2 where s1={0}, s2={2}, s3 must contain {0,2}.
#[test]
fn roundtrip_set_union() {
    let fzn = "var set of 0..3: s1;\n\
               var set of 0..3: s2;\n\
               var set of 0..3: s3;\n\
               var bool: b1;\n\
               var bool: b2;\n\
               constraint set_card(s1, 1);\n\
               constraint set_in_reif(0, s1, b1);\n\
               constraint bool_eq(b1, true);\n\
               constraint set_card(s2, 1);\n\
               constraint set_in_reif(2, s2, b2);\n\
               constraint bool_eq(b2, true);\n\
               constraint set_union(s1, s2, s3);\n\
               solve satisfy;\n";
    let result = translate_fzn(fzn);
    let Some((code, stdout, stderr)) = run_z3(&result.smtlib) else {
        return;
    };
    assert_eq!(code, 0, "z3 exit code: stderr={stderr}");

    let lines: Vec<&str> = stdout.lines().collect();
    assert_eq!(lines[0], "sat", "set_union should be sat, got: {stdout}");

    let value_str = lines[1..].join(" ");
    let values = parse_get_value(&value_str);

    let s1_count = count_true_bits(&values, "s1", 4);
    assert_eq!(s1_count, 1, "s1 should have 1 element, got {s1_count}");

    let s3_count = count_true_bits(&values, "s3", 4);
    assert!(
        s3_count >= 2,
        "s3 = s1 union s2 should have >=2 elements, got {s3_count}"
    );
    assert!(bit_is_true(&values, "s3", 0), "element 0 must be in s3");
    assert!(bit_is_true(&values, "s3", 2), "element 2 must be in s3");
}

/// Verify set_in_reif with set variable: b iff (2 in s).
/// Force s = {2} (card 1, element 2 in), then b should be true.
#[test]
fn roundtrip_set_in_reif_var() {
    let fzn = "var set of 0..3: s;\n\
               var bool: b;\n\
               var bool: b_force;\n\
               constraint set_card(s, 1);\n\
               constraint set_in_reif(2, s, b_force);\n\
               constraint bool_eq(b_force, true);\n\
               constraint set_in_reif(2, s, b);\n\
               solve satisfy;\n";
    let result = translate_fzn(fzn);
    let Some((code, stdout, stderr)) = run_z3(&result.smtlib) else {
        return;
    };
    assert_eq!(code, 0, "z3 exit code: stderr={stderr}");

    let lines: Vec<&str> = stdout.lines().collect();
    assert_eq!(lines[0], "sat", "set_in_reif should be sat, got: {stdout}");

    let value_str = lines[1..].join(" ");
    let values = parse_get_value(&value_str);
    let b_val = values.get("b").expect("expected b in model");
    assert_eq!(
        b_val, "true",
        "2 in s forced, so b must be true, got {b_val}"
    );
}

/// Verify set_in_reif negative: b iff (1 in s) where s = {2}.
/// Element 1 is NOT in the set, so b should be false.
#[test]
fn roundtrip_set_in_reif_var_false() {
    let fzn = "var set of 0..3: s;\n\
               var bool: b_2;\n\
               var bool: b_1;\n\
               constraint set_card(s, 1);\n\
               constraint set_in_reif(2, s, b_2);\n\
               constraint bool_eq(b_2, true);\n\
               constraint set_in_reif(1, s, b_1);\n\
               solve satisfy;\n";
    let result = translate_fzn(fzn);
    let Some((code, stdout, stderr)) = run_z3(&result.smtlib) else {
        return;
    };
    assert_eq!(code, 0, "z3 exit code: stderr={stderr}");

    let lines: Vec<&str> = stdout.lines().collect();
    assert_eq!(lines[0], "sat", "should be sat, got: {stdout}");

    let value_str = lines[1..].join(" ");
    let values = parse_get_value(&value_str);
    let b1_val = values.get("b_1").expect("expected b_1 in model");
    assert_eq!(
        b1_val, "false",
        "1 not in {{2}}, so b_1 must be false, got {b1_val}"
    );
}

/// Verify set_card unsat: set_card(s, 5) where s is set of 0..3 (max 4 elements).
#[test]
fn roundtrip_set_card_unsat() {
    let fzn = "var set of 0..3: s;\n\
               constraint set_card(s, 5);\n\
               solve satisfy;\n";
    let result = translate_fzn(fzn);
    let Some((_code, stdout, _stderr)) = run_z3(&result.smtlib) else {
        return;
    };

    let first_line = stdout.lines().next().unwrap_or("");
    assert_eq!(
        first_line, "unsat",
        "set_card(s,5) with width=4 should be unsat, got: {stdout}"
    );
}
