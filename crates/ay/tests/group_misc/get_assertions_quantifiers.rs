// Copyright (c) 2026 Andrew Yates. Licensed under Apache-2.0.
// Author: Andrew Yates
//
// Integration test: `(get-assertions)` must print well-scoped quantifiers.

use ntest::timeout;
use std::process::{Command, Stdio};

fn tokenize_smt2(input: &str) -> Vec<&str> {
    input
        .split(|c: char| c.is_whitespace() || c == '(' || c == ')')
        .filter(|tok| !tok.is_empty())
        .collect()
}

#[test]
#[timeout(60000)]
fn test_get_assertions_quantifiers_are_well_scoped() {
    let ay_path = env!("CARGO_BIN_EXE_ay");

    let test_input = r#"
(set-option :interactive-mode true)
(assert (forall ((x Int)) (> x 0)))
(assert (exists ((y Int)) (< y 5)))
(get-assertions)
"#;

    let mut child = Command::new(ay_path)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("Failed to spawn ay");

    {
        use std::io::Write;
        child
            .stdin
            .as_mut()
            .expect("child stdin must be piped")
            .write_all(test_input.as_bytes())
            .expect("Failed to write to ay stdin");
    }

    let output = child.wait_with_output().expect("Failed to wait on ay");
    assert!(
        output.status.success(),
        "ay exited with {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    let output_str = stdout.trim();
    assert!(
        output_str.contains("forall") && output_str.contains("exists"),
        "Expected quantifiers in get-assertions output, got:\n{output_str}"
    );

    let tokens = tokenize_smt2(output_str);

    let forall_idx = tokens
        .iter()
        .position(|t| *t == "forall")
        .expect("Expected 'forall' token in output");
    let forall_binder = tokens
        .get(forall_idx + 1)
        .expect("Expected binder name token after 'forall'");
    let forall_count = tokens.iter().filter(|t| *t == forall_binder).count();
    assert!(
        forall_count >= 2,
        "Expected forall binder {forall_binder} to appear in body, tokens={tokens:?}"
    );

    let exists_idx = tokens
        .iter()
        .position(|t| *t == "exists")
        .expect("Expected 'exists' token in output");
    let exists_binder = tokens
        .get(exists_idx + 1)
        .expect("Expected binder name token after 'exists'");
    let exists_count = tokens.iter().filter(|t| *t == exists_binder).count();
    assert!(
        exists_count >= 2,
        "Expected exists binder {exists_binder} to appear in body, tokens={tokens:?}"
    );
}
