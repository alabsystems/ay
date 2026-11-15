//! Integration tests for the `--trace-lines`, `--trace-ids` and `--trace-pol` options.
//!
//! These run the compiled `veripb` binary as a subprocess so that the trace
//! output written to stdout can be inspected. The `all_diff` instance is used
//! because its proof derives constraints with predictable IDs:
//!
//! ```text
//! line 1: pseudo-Boolean proof version 3.0
//! line 2: f 15;
//! line 4: pol 3 4 + 5 +;                                  -> ConstraintId 16
//! line 6: pol 14 15 + y_x1_8 + y_x2_8 + y_x1_9 + y_x2_9 +; -> ConstraintId 17
//! line 8: pol 16 17 +;                                    -> ConstraintId 18
//! ```

use std::process::Command;

const FORMULA: &str = "tests/instances/correct/version3/all_diff.opb";
const DERIVATION: &str = "tests/instances/correct/version3/all_diff.pbp";

/// Run the `veripb` binary on the given files with extra arguments; return stdout.
fn run_veripb_on(formula: &str, derivation: &str, extra_args: &[&str]) -> String {
    let output = Command::new(env!("CARGO_BIN_EXE_veripb"))
        .args(extra_args)
        .args([formula, derivation])
        .output()
        .expect("failed to run veripb binary");
    assert!(
        output.status.success(),
        "veripb exited with failure: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).expect("veripb stdout was not valid UTF-8")
}

/// Run the `veripb` binary on the `all_diff` instance with the given extra arguments.
fn run_veripb(extra_args: &[&str]) -> String {
    run_veripb_on(FORMULA, DERIVATION, extra_args)
}

/// Extract the pol-derivation trace table's data rows from trace output as
/// `(depth, operand, top-of-stack)` triples. Data rows are the only lines that
/// begin with a stack depth (an integer); headers, source lines and
/// `ConstraintId` lines all start with a word.
fn table_rows(out: &str) -> Vec<(usize, String, String)> {
    out.lines()
        .filter_map(|line| {
            let mut fields = line.split_whitespace();
            let depth: usize = fields.next()?.parse().ok()?;
            let operand = fields.next()?.to_string();
            Some((depth, operand, fields.collect::<Vec<_>>().join(" ")))
        })
        .collect()
}

/// The operand column of the trace table, which should read top-to-bottom like
/// the tokens of the raw pol line.
fn operand_column(out: &str) -> Vec<String> {
    table_rows(out)
        .into_iter()
        .map(|(_, operand, _)| operand)
        .collect()
}

#[test]
fn trace_lines_selects_only_given_lines() {
    let out = run_veripb(&["--trace-lines", "4"]);
    // Line 4 derives constraint 16, so both should be traced.
    assert!(out.contains("pol 3 4 + 5 +;"), "stdout was:\n{out}");
    assert!(out.contains("ConstraintId 16"), "stdout was:\n{out}");
    // Line 6 (constraint 17) is not selected and must not be traced.
    assert!(
        !out.contains("ConstraintId 17"),
        "unexpected trace of unselected line:\n{out}"
    );
}

#[test]
fn trace_lines_open_ended_range_traces_to_end() {
    let out = run_veripb(&["--trace-lines", "6.."]);
    // Everything from line 6 onwards is traced.
    assert!(out.contains("ConstraintId 17"), "stdout was:\n{out}");
    assert!(out.contains("ConstraintId 18"), "stdout was:\n{out}");
    assert!(
        out.contains("end pseudo-Boolean proof;"),
        "stdout was:\n{out}"
    );
    // Line 4 (constraint 16) is before the range and must not be traced.
    assert!(
        !out.contains("ConstraintId 16"),
        "unexpected trace before range start:\n{out}"
    );
}

#[test]
fn trace_lines_open_start_range_traces_from_beginning() {
    let out = run_veripb(&["--trace-lines", "..=4"]);
    // Everything up to and including line 4 (constraint 16) is traced.
    assert!(out.contains("pol 3 4 + 5 +;"), "stdout was:\n{out}");
    assert!(out.contains("ConstraintId 16"), "stdout was:\n{out}");
    // Line 6 (constraint 17) is after the range and must not be traced.
    assert!(
        !out.contains("ConstraintId 17"),
        "unexpected trace after range end:\n{out}"
    );
}

#[test]
fn trace_lines_exclusive_range_excludes_upper_bound() {
    let out = run_veripb(&["--trace-lines", "..6"]);
    // `..6` is exclusive of line 6, so line 4 (constraint 16) is traced...
    assert!(out.contains("ConstraintId 16"), "stdout was:\n{out}");
    // ...but line 6 (constraint 17) is excluded by the open upper bound.
    assert!(
        !out.contains("ConstraintId 17"),
        "exclusive upper bound should not be traced:\n{out}"
    );
}

#[test]
fn trace_ids_selects_only_given_derived_constraint() {
    let out = run_veripb(&["--trace-ids", "17"]);
    // Constraint 17 is derived on line 6, so that rule should be traced.
    assert!(out.contains("ConstraintId 17"), "stdout was:\n{out}");
    assert!(
        out.contains("pol 14 15 + y_x1_8 + y_x2_8 + y_x1_9 + y_x2_9 +;"),
        "stdout was:\n{out}"
    );
    // Neighbouring derived constraints must not be traced.
    assert!(
        !out.contains("ConstraintId 16"),
        "unexpected trace of unselected constraint:\n{out}"
    );
    assert!(
        !out.contains("ConstraintId 18"),
        "unexpected trace of unselected constraint:\n{out}"
    );
}

#[test]
fn trace_ids_selects_formula_constraints() {
    let out = run_veripb(&["--trace-ids", "3,5"]);
    // Formula constraints 3 and 5 are printed up front.
    assert!(out.contains("ConstraintId 3:"), "stdout was:\n{out}");
    assert!(out.contains("ConstraintId 5:"), "stdout was:\n{out}");
    // Constraint 4 lies between them and must not be traced.
    assert!(
        !out.contains("ConstraintId 4:"),
        "unexpected trace of unselected formula constraint:\n{out}"
    );
}

#[test]
fn trace_pol_prints_step_table() {
    let out = run_veripb(&["--trace-lines", "4", "--trace-pol"]);
    // The pol source line and its derived constraint are still shown...
    assert!(out.contains("pol 3 4 + 5 +;"), "stdout was:\n{out}");
    assert!(out.contains("ConstraintId 16"), "stdout was:\n{out}");
    // ...plus the step-by-step table, with its header and per-step top of stack.
    assert!(out.contains("top of stack"), "stdout was:\n{out}");
    assert!(
        out.contains("1 y_x3_8 1 y_x3_9 >= 1"),
        "expected an intermediate top-of-stack row:\n{out}"
    );
    // The operand column reads top-to-bottom exactly like `pol 3 4 + 5 +`.
    assert_eq!(operand_column(&out), ["3", "4", "+", "5", "+"], "\n{out}");
}

#[test]
fn trace_pol_shows_scalars_transiently() {
    // `pol 3 1 * 4 1 * + s`: each multiplier is shown as a transient stack entry
    // ahead of the `*` that consumes it, so the operand column is the raw line.
    let formula = "tests/instances/correct/version3/conclusion_BOUNDS_infeasible.opb";
    let derivation = "tests/instances/correct/version3/conclusion_BOUNDS_infeasible.pbp";
    let out = run_veripb_on(formula, derivation, &["--trace-lines", "3", "--trace-pol"]);
    assert_eq!(
        operand_column(&out),
        ["3", "1", "*", "4", "1", "*", "+", "s"],
        "\n{out}"
    );
    // The scalar `1` appears on the stack as itself (operand and top both `1`).
    assert!(
        table_rows(&out).contains(&(2, "1".to_string(), "1".to_string())),
        "expected a transient scalar row:\n{out}"
    );
}

#[test]
fn trace_pol_shows_weaken_variables() {
    // `pol 1 x1 w x3 w`: each weakening variable is shown transiently before `w`.
    let formula = "tests/instances/correct/version3/weakening.opb";
    let derivation = "tests/instances/correct/version3/weakening.pbp";
    let out = run_veripb_on(formula, derivation, &["--trace-lines", "7", "--trace-pol"]);
    assert_eq!(operand_column(&out), ["1", "x1", "w", "x3", "w"], "\n{out}");
    assert!(
        table_rows(&out).contains(&(2, "x1".to_string(), "x1".to_string())),
        "expected a transient weakening-variable row:\n{out}"
    );
}

#[test]
fn trace_pol_composes_with_trace_ids() {
    let out = run_veripb(&["--trace-ids", "16", "--trace-pol"]);
    assert!(out.contains("ConstraintId 16"), "stdout was:\n{out}");
    assert!(out.contains("top of stack"), "stdout was:\n{out}");
    // Constraint 17 is not selected, so its derivation must not be traced.
    assert!(
        !out.contains("ConstraintId 17"),
        "unexpected trace of unselected constraint:\n{out}"
    );
}

#[test]
fn trace_pol_requires_a_trace_selection() {
    // On its own the flag is inert: nothing is selected for tracing, so no table.
    let out = run_veripb(&["--trace-pol"]);
    assert!(
        !out.contains("top of stack"),
        "--trace-pol should do nothing without a trace selection:\n{out}"
    );
}

#[test]
fn plain_trace_has_no_step_table() {
    // Tracing a pol rule without the flag still prints its result, but no table.
    let out = run_veripb(&["--trace-lines", "4"]);
    assert!(out.contains("ConstraintId 16"), "stdout was:\n{out}");
    assert!(
        !out.contains("top of stack"),
        "step table should only appear with --trace-pol:\n{out}"
    );
}

#[test]
fn invalid_range_is_rejected() {
    let output = Command::new(env!("CARGO_BIN_EXE_veripb"))
        .args(["--trace-lines", "30..=20", FORMULA, DERIVATION])
        .output()
        .expect("failed to run veripb binary");
    assert!(
        !output.status.success(),
        "veripb should reject an inverted range"
    );
}

#[test]
fn rup_failure_hint_mentions_trace_pol() {
    // A failing RUP check hints at `--trace-failed`. Since a wrong `pol`
    // derivation earlier in the proof can be the real cause, the hint also
    // points the user at `--trace-pol`.
    let output = Command::new(env!("CARGO_BIN_EXE_veripb"))
        .args([
            "tests/instances/incorrect/version3/rup_empty_hints.opb",
            "tests/instances/incorrect/version3/rup_empty_hints.pbp",
        ])
        .output()
        .expect("failed to run veripb binary");
    assert!(!output.status.success(), "the proof is incorrect");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("--trace-failed") && stderr.contains("--trace-pol"),
        "RUP failure hint should mention both --trace-failed and --trace-pol:\n{stderr}"
    );
}
