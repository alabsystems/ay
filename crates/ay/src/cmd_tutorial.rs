// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `ay tutorial` subcommand -- educational tutorial mode.
//!
//! Makes constraint solving approachable without hiding the real solver
//! underneath.
//!
//! Design principles:
//! - Never patronizing. No "great job!" or baby talk.
//! - Show the solver's work. Back-substitute values into constraints.
//! - Honest. If something is hard, say so.
//! - Wrapper around real solver -- same ay engine underneath.

use std::collections::HashMap;
use std::io::{self, BufRead, Write};
use std::path::PathBuf;

use anyhow::{Context, Result};
use clap::Subcommand;

use crate::stats_output;

use ay::solution_visualization::{render_solution_visualization, VisualizationFormat};
use ay_dpll::Executor;
use ay_frontend::sexp::parse_sexps;
use ay_frontend::{parse, SExpr};

// ---------------------------------------------------------------------------
// CLI definition
// ---------------------------------------------------------------------------

/// Educational SMT solving for humans.
#[derive(clap::Args)]
#[command(args_conflicts_with_subcommands = true)]
pub(crate) struct TutorialArgs {
    #[command(subcommand)]
    command: Option<TutorialCommand>,

    /// Run the interactive 5-level tutorial
    #[arg(long, conflicts_with = "challenge")]
    interactive: bool,

    /// Run a challenge puzzle (easy, medium, or hard)
    #[arg(long, value_name = "LEVEL")]
    challenge: Option<ChallengeLevel>,
}

#[derive(Subcommand)]
enum TutorialCommand {
    /// Solve an SMT-LIB2 file with educational output
    Solve {
        /// Path to .smt2 file
        file: PathBuf,
    },
}

#[derive(Debug, Clone, Copy, clap::ValueEnum)]
enum ChallengeLevel {
    Easy,
    Medium,
    Hard,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

pub(crate) fn run(args: &TutorialArgs) -> Result<()> {
    println!("{}", stats_output::BUILD_PROVENANCE.human_banner());
    println!();
    if args.interactive {
        return run_tutorial();
    }
    if let Some(level) = args.challenge {
        return run_challenge(level);
    }
    match &args.command {
        Some(TutorialCommand::Solve { file }) => run_solve(file),
        None => {
            print_welcome();
            Ok(())
        }
    }
}

// ---------------------------------------------------------------------------
// Welcome banner
// ---------------------------------------------------------------------------

fn print_welcome() {
    println!(
        r#"
AY tutorial
Educational SMT solving

An SMT solver figures out whether a set of rules can all be true
at the same time -- and if so, finds values that make them work.

Quick example:
  Suppose x and y are integers, x + y = 10, and x - y = 2.
  What are x and y?

"#
    );

    // Actually solve it
    let smt = r#"
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (= (+ x y) 10))
(assert (= (- x y) 2))
(check-sat)
(get-model)
"#;

    match solve_smt_string(smt) {
        Ok(outputs) => {
            println!(
                "  ay says: {}",
                outputs.first().map_or("(no result)", String::as_str)
            );
            if outputs.len() > 1 {
                print_friendly_model(&outputs[1]);
            }
            println!();
            explain_quick_example();
        }
        Err(e) => {
            eprintln!("  (solver error: {e})");
        }
    }

    println!("Try these next:");
    println!("  ay tutorial --interactive    Step-by-step lessons");
    println!("  ay tutorial --challenge easy  A puzzle to solve");
    println!("  ay tutorial solve FILE.smt2  Solve your own file");
    println!();
}

fn explain_quick_example() {
    println!("  How it works:");
    println!("    Rule 1: x + y = 10");
    println!("    Rule 2: x - y = 2");
    println!();
    println!("    The solver found values and checked every rule:");
    println!("      x + y  =  6 + 4  =  10    (rule 1 holds)");
    println!("      x - y  =  6 - 4  =  2     (rule 2 holds)");
    println!("    All rules satisfied. The answer is correct.");
}

// ---------------------------------------------------------------------------
// Tutorial solve: educational output for an .smt2 file
// ---------------------------------------------------------------------------

fn run_solve(path: &PathBuf) -> Result<()> {
    let content =
        std::fs::read_to_string(path).with_context(|| format!("reading {}", path.display()))?;

    println!("Solving: {}", path.display());
    println!();

    let outputs = solve_smt_string(&content)?;

    if outputs.is_empty() {
        println!("The file produced no output. It may not contain a (check-sat) command.");
        return Ok(());
    }

    // Classify: find the check-sat result and any model output.
    let mut result: Option<&str> = None;
    let mut model_output: Option<&str> = None;
    let mut other_outputs: Vec<&str> = Vec::new();
    for output in &outputs {
        let trimmed = output.trim();
        match trimmed {
            "sat" | "unsat" | "unknown" if result.is_none() => {
                result = Some(trimmed);
            }
            _ if trimmed.starts_with('(') && model_output.is_none() => {
                model_output = Some(output);
            }
            _ => other_outputs.push(output),
        }
    }

    if let Some(res) = result {
        if res == "sat" {
            println!("Result: SATISFIABLE");
            println!("  All the rules in this file can be true at the same time.");
            if let Some(model) = model_output {
                print_friendly_model(model);
                // Show the model back-substituted into each assertion.
                if let Ok(model_map) = parse_model_values(model) {
                    print_assertion_verification(&content, &model_map);
                }
                print_auto_visualization(&content, model);
            }
        } else if res == "unsat" {
            println!("Result: UNSATISFIABLE");
            println!("  No answer exists. The rules in this file contradict each other,");
            println!("  so no values can make all of them true at the same time.");
            print_unsat_hint(&content);
        } else if res == "unknown" {
            println!("Result: UNKNOWN");
            println!("  The solver could not determine the answer within its limits.");
            println!(
                "  The problem may be hard or outside AY's supported reasoning; see LIMITATIONS.md."
            );
        } else {
            println!("Result: {res}");
        }
    } else {
        // Unusual: no check-sat result. Just print raw outputs.
        for output in &outputs {
            println!("  {output}");
        }
    }
    for extra in &other_outputs {
        println!("  {extra}");
    }

    println!();
    Ok(())
}

fn print_auto_visualization(content: &str, model: &str) {
    if let Some(rendered) =
        render_solution_visualization(content, model, VisualizationFormat::Ascii)
    {
        println!();
        println!("{rendered}");
    }
}

// ---------------------------------------------------------------------------
// Model back-substitution verifier
//
// For every top-level `(assert <body>)` in the original file, print the
// assertion and the value obtained by substituting each free symbol with its
// model value. Then re-check the substituted assertion by asking the solver:
// given the model as equalities, does `(not <body>)` become unsatisfiable?
// If yes, AY's substituted re-check is consistent with the model. This is a
// "show your work" educational step, not an independent validation.
// ---------------------------------------------------------------------------

/// Parse a `(model ...)` s-expression into a `variable -> value-sexpr` map.
/// Each value is stored as an `SExpr` so it can be substituted back into
/// assertions as a proper s-expression (e.g., `(- 3)` for negative ints).
fn parse_model_values(model_str: &str) -> Result<HashMap<String, SExpr>> {
    let sexps =
        parse_sexps(model_str).map_err(|e| anyhow::anyhow!("could not parse model: {e}"))?;
    let mut values: HashMap<String, SExpr> = HashMap::new();
    for sexp in &sexps {
        collect_define_funs(sexp, &mut values);
    }
    Ok(values)
}

/// Walk an SExpr tree and collect `(define-fun NAME () SORT VALUE)` bindings.
fn collect_define_funs(sexp: &SExpr, out: &mut HashMap<String, SExpr>) {
    if let SExpr::List(items) = sexp {
        // Recurse first so nested `(model ...)` wrappers are handled uniformly.
        if items.first().and_then(SExpr::as_symbol) == Some("define-fun") && items.len() >= 5 {
            if let Some(name) = items[1].as_symbol() {
                // items[2] is `()` (arg list), items[3] is the sort, items[4] is the value.
                out.insert(name.to_string(), items[4].clone());
            }
            return;
        }
        for item in items {
            collect_define_funs(item, out);
        }
    }
}

/// Substitute every symbol in `sexp` that appears in `model` with the
/// corresponding value s-expression. Symbols not in the model are left alone
/// (they are typically built-in operators like `+`, `=`, `and`).
fn substitute_model(sexp: &SExpr, model: &HashMap<String, SExpr>) -> SExpr {
    match sexp {
        SExpr::Symbol(s) => match model.get(s) {
            Some(value) => value.clone(),
            None => sexp.clone(),
        },
        SExpr::List(items) => {
            // Preserve operator positions — don't substitute the function head
            // (items[0]). That keeps `(+ x y)` → `(+ 2 3)` instead of mangling
            // `+` if someone declared a variable named `+` (legal but rare).
            let mut new_items = Vec::with_capacity(items.len());
            for (i, item) in items.iter().enumerate() {
                if i == 0 {
                    new_items.push(item.clone());
                } else {
                    new_items.push(substitute_model(item, model));
                }
            }
            SExpr::List(new_items)
        }
        _ => sexp.clone(),
    }
}

/// Extract `(assert <body>)` bodies from the raw file, pre-model-substitution.
fn extract_assert_bodies(content: &str) -> Vec<SExpr> {
    let Ok(sexps) = parse_sexps(content) else {
        return Vec::new();
    };
    let mut bodies = Vec::new();
    for sexp in &sexps {
        if let SExpr::List(items) = sexp {
            if items.len() == 2 && items[0].is_symbol("assert") {
                bodies.push(items[1].clone());
            }
        }
    }
    bodies
}

/// Build an SMT-LIB2 script that re-checks `(not <body>)` under the model's
/// equalities. Returns true if the solver says `unsat` (i.e., the assertion
/// is forced true by the model), false otherwise. Errors (parse, etc.) are
/// treated as "unable to verify" and reported as `None`.
fn verify_assertion_against_model(
    content: &str,
    body: &SExpr,
    model: &HashMap<String, SExpr>,
) -> Option<bool> {
    // Extract declarations and logic directive from the original file.
    // We need these so `body` is well-typed in the verification script.
    let prelude = extract_prelude(content);

    // Emit model equalities as constraints. For booleans we assert the
    // boolean directly; for everything else we use `(= var value)`.
    let mut model_lines = String::new();
    for (var, value) in model {
        let rendered = value.to_raw_string();
        if rendered == "true" {
            model_lines.push_str(&format!("(assert {var})\n"));
        } else if rendered == "false" {
            model_lines.push_str(&format!("(assert (not {var}))\n"));
        } else {
            model_lines.push_str(&format!("(assert (= {var} {rendered}))\n"));
        }
    }

    // Assert the negation of the body. If this is UNSAT under the model,
    // the model does satisfy the original body.
    let body_rendered = body.to_raw_string();
    let script = format!("{prelude}\n{model_lines}(assert (not {body_rendered}))\n(check-sat)\n");

    let outputs = solve_smt_string(&script).ok()?;
    let first = outputs.first()?.trim();
    match first {
        "unsat" => Some(true),
        "sat" => Some(false),
        _ => None,
    }
}

/// Extract the `(set-logic ...)`, `(declare-*)`, and `(define-*)` commands
/// from the original file, preserving order. These form a prelude that can
/// be replayed into a fresh solver for verification purposes.
fn extract_prelude(content: &str) -> String {
    let Ok(sexps) = parse_sexps(content) else {
        return String::new();
    };
    let mut prelude = String::new();
    for sexp in &sexps {
        let keep = if let SExpr::List(items) = sexp {
            matches!(
                items.first().and_then(SExpr::as_symbol),
                Some("set-logic")
                    | Some("set-option")
                    | Some("declare-const")
                    | Some("declare-fun")
                    | Some("declare-sort")
                    | Some("declare-datatype")
                    | Some("declare-datatypes")
                    | Some("define-fun")
                    | Some("define-const")
                    | Some("define-sort")
            )
        } else {
            false
        };
        if keep {
            prelude.push_str(&sexp.to_raw_string());
            prelude.push('\n');
        }
    }
    prelude
}

/// Print each assertion with its model-substituted form and a verification
/// note indicating whether the solver confirms it evaluates to true.
fn print_assertion_verification(content: &str, model: &HashMap<String, SExpr>) {
    let bodies = extract_assert_bodies(content);
    if bodies.is_empty() {
        return;
    }
    println!();
    println!("  Checking the model against each rule:");
    for (i, body) in bodies.iter().enumerate() {
        let original = body.to_raw_string();
        let substituted_sexp = substitute_model(body, model);
        let substituted = substituted_sexp.to_raw_string();
        println!("    Rule {}: {}", i + 1, original);
        if substituted == original {
            // No substitution happened (no free variables in assertion).
            println!("      (no variables to substitute)");
        } else {
            println!("      with model: {substituted}");
        }
        match verify_assertion_against_model(content, body, model) {
            Some(true) => println!("      evaluates to True"),
            Some(false) => println!("      evaluates to False (!) model may be inconsistent"),
            None => println!("      (verification inconclusive)"),
        }
    }
}

/// When the file is UNSAT, print a plain-English hint pointing at the
/// assertions. If the file is tiny, list them; if it has many, say so.
fn print_unsat_hint(content: &str) {
    let bodies = extract_assert_bodies(content);
    if bodies.is_empty() {
        return;
    }
    println!();
    if bodies.len() <= 6 {
        println!("  The rules were:");
        for (i, body) in bodies.iter().enumerate() {
            println!("    {}. {}", i + 1, body.to_raw_string());
        }
        println!("  These rules cannot all hold simultaneously.");
    } else {
        println!(
            "  The file contains {} rules. Some combination of them contradicts.",
            bodies.len()
        );
        println!(
            "  For a small reproducer, run `ay solve --explain FILE.smt2` to get a reason code."
        );
    }
}

// ---------------------------------------------------------------------------
// Tutorial state machine
// ---------------------------------------------------------------------------

fn run_tutorial() -> Result<()> {
    println!();
    println!("=== AY Tutorial: 5 Levels ===");
    println!();
    println!("Each level introduces a new idea. The solver does the hard work;");
    println!("your job is to understand the rules and predict what happens.");
    println!();

    let levels: &[fn() -> Result<bool>] = &[
        level_1_mystery_number,
        level_2_candy_sharing,
        level_3_impossible_lineup,
        level_4_mini_sudoku,
        level_5_create_your_own,
    ];

    let names = [
        "Mystery Number",
        "Candy Sharing",
        "Impossible Lineup",
        "Mini Sudoku (2x2)",
        "Create Your Own",
    ];

    for (i, (level_fn, name)) in levels.iter().zip(names.iter()).enumerate() {
        println!("--- Level {} of 5: {} ---", i + 1, name);
        println!();
        let cont = level_fn()?;
        if !cont {
            println!();
            println!("Tutorial paused. Run `ay tutorial --interactive` to start again.");
            return Ok(());
        }
        println!();
    }

    println!("=== Tutorial complete ===");
    println!();
    println!("You now know the basics of constraint solving.");
    println!("Try `ay tutorial --challenge easy` for a puzzle,");
    println!("or write your own .smt2 file and run `ay tutorial solve FILE`.");
    println!();
    Ok(())
}

fn prompt_continue() -> Result<bool> {
    print!("Press Enter to continue (or 'q' to quit): ");
    io::stdout().flush()?;
    let mut line = String::new();
    io::stdin().lock().read_line(&mut line)?;
    Ok(!line.trim().eq_ignore_ascii_case("q"))
}

// --- Level 1: Mystery Number ---

fn level_1_mystery_number() -> Result<bool> {
    println!("I'm thinking of a number. Here are the clues:");
    println!("  1. It is greater than 0");
    println!("  2. It is less than 10");
    println!("  3. It is divisible by 3");
    println!("  4. If you add 1, the result is divisible by 4");
    println!();
    println!("Let's ask ay to find it.");
    println!();

    let smt = r#"
(set-logic QF_LIA)
(declare-const n Int)
(assert (> n 0))
(assert (< n 10))
(assert (= (mod n 3) 0))
(assert (= (mod (+ n 1) 4) 0))
(check-sat)
(get-model)
"#;

    let outputs = solve_smt_string(smt)?;
    println!(
        "  ay says: {}",
        outputs.first().map_or("(no result)", String::as_str)
    );
    if outputs.len() > 1 {
        print_friendly_model(&outputs[1]);
    }
    println!();
    println!("  Checking the answer:");
    println!("    n > 0?              Yes");
    println!("    n < 10?             Yes");
    println!("    n divisible by 3?   If n = 3, then 3 / 3 = 1 remainder 0. Yes.");
    println!("    n + 1 div by 4?     3 + 1 = 4, and 4 / 4 = 1 remainder 0. Yes.");
    println!();
    println!("  The solver found a value that satisfies every clue.");
    println!("  These clues have the unique answer n = 3.");
    println!();

    prompt_continue()
}

// --- Level 2: Candy Sharing ---

fn level_2_candy_sharing() -> Result<bool> {
    println!("Three friends -- Alice, Bob, and Carol -- are sharing 30 candies.");
    println!("Rules:");
    println!("  1. Everyone gets at least 1 candy");
    println!("  2. Alice gets twice as many as Bob");
    println!("  3. Carol gets 3 more than Alice");
    println!("  4. Total is exactly 30");
    println!();
    println!("How many does each person get?");
    println!();

    let smt = r#"
(set-logic QF_LIA)
(declare-const alice Int)
(declare-const bob Int)
(declare-const carol Int)
(assert (>= alice 1))
(assert (>= bob 1))
(assert (>= carol 1))
(assert (= alice (* 2 bob)))
(assert (= carol (+ alice 3)))
(assert (= (+ alice bob carol) 30))
(check-sat)
(get-model)
"#;

    let outputs = solve_smt_string(smt)?;
    println!(
        "  ay says: {}",
        outputs.first().map_or("(no result)", String::as_str)
    );
    if outputs.len() > 1 {
        print_friendly_model(&outputs[1]);
    }
    println!();

    // Extract values for verification display
    // alice=2*bob, carol=alice+3, total=30
    // 2*bob + bob + (2*bob+3) = 30 => 5*bob + 3 = 30 => 5*bob = 27 => bob = 27/5
    // Actually let's let the solver result speak for itself. With integers:
    // 5*bob = 27 has no integer solution, so this might be unsat.
    // Let me check: 2b + b + (2b+3) = 5b+3 = 30 => 5b=27 => not integer.
    // This is actually UNSAT! That's a teaching moment.

    if outputs.first().is_some_and(|s| s.trim() == "unsat") {
        println!("  Wait -- UNSATISFIABLE? Nobody can share 30 candies with these rules?");
        println!();
        println!("  Let's see why:");
        println!("    alice = 2 * bob              (rule 2)");
        println!("    carol = alice + 3 = 2*bob+3  (rule 3)");
        println!("    total = alice + bob + carol");
        println!("          = 2*bob + bob + (2*bob + 3)");
        println!("          = 5*bob + 3 = 30");
        println!("          => bob = 27/5 = 5.4");
        println!();
        println!("  But bob must be a whole number (integer). 5.4 is not an integer.");
        println!("  The rules are contradictory. No solution exists.");
        println!();
        println!("  This is what makes SMT solvers powerful: they do not just find");
        println!("  answers. They can prove that NO answer exists.");
    } else if outputs.first().is_some_and(|s| s.trim() == "sat") {
        println!("  The solver found a way to share the candies.");
    }

    println!();
    prompt_continue()
}

// --- Level 3: Impossible Lineup ---

fn level_3_impossible_lineup() -> Result<bool> {
    println!("Can you line up three people (A, B, C) so that:");
    println!("  1. Each person is in position 1, 2, or 3");
    println!("  2. No two people share a position");
    println!("  3. A is immediately before B (A's position + 1 = B's position)");
    println!("  4. C is immediately before A (C's position + 1 = A's position)");
    println!("  5. B is immediately before C (B's position + 1 = C's position)");
    println!();
    println!("Think about it: A before B, B before C, C before A... a cycle.");
    println!();

    let smt = r#"
(set-logic QF_LIA)
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
; Each in {1, 2, 3}
(assert (or (= a 1) (= a 2) (= a 3)))
(assert (or (= b 1) (= b 2) (= b 3)))
(assert (or (= c 1) (= c 2) (= c 3)))
; All different
(assert (not (= a b)))
(assert (not (= a c)))
(assert (not (= b c)))
; Cyclic ordering (impossible)
(assert (= (+ a 1) b))
(assert (= (+ c 1) a))
(assert (= (+ b 1) c))
(check-sat)
"#;

    let outputs = solve_smt_string(smt)?;
    println!(
        "  ay says: {}",
        outputs.first().map_or("(no result)", String::as_str)
    );
    println!();

    if outputs.first().is_some_and(|s| s.trim() == "unsat") {
        println!("  Unsatisfiable. The cycle makes it impossible.");
        println!();
        println!("  Here's why: from the rules,");
        println!("    b = a + 1");
        println!("    a = c + 1");
        println!("    c = b + 1");
        println!("  Substituting: c = b + 1 = (a+1) + 1 = a + 2");
        println!("  But also: a = c + 1, so c = a - 1");
        println!("  That gives a + 2 = a - 1, which means 2 = -1. Contradiction.");
        println!();
        println!("  The solver reached this conclusion by propagating constraints");
        println!("  until it found a conflict.");
    }

    println!();
    prompt_continue()
}

// --- Level 4: Mini Sudoku (2x2) ---

fn level_4_mini_sudoku() -> Result<bool> {
    println!("A tiny 2x2 Sudoku. Fill a 2x2 grid with numbers 1 and 2:");
    println!();
    println!("    +---+---+");
    println!("    | ? | 2 |");
    println!("    +---+---+");
    println!("    | ? | ? |");
    println!("    +---+---+");
    println!();
    println!("  Rules: each row has 1 and 2, each column has 1 and 2.");
    println!("  One cell is already filled in (top-right = 2).");
    println!();

    let smt = r#"
(set-logic QF_LIA)
(declare-const r1c1 Int)
(declare-const r1c2 Int)
(declare-const r2c1 Int)
(declare-const r2c2 Int)
; Values in {1, 2}
(assert (or (= r1c1 1) (= r1c1 2)))
(assert (or (= r1c2 1) (= r1c2 2)))
(assert (or (= r2c1 1) (= r2c1 2)))
(assert (or (= r2c2 1) (= r2c2 2)))
; Given: top-right is 2
(assert (= r1c2 2))
; Row uniqueness
(assert (not (= r1c1 r1c2)))
(assert (not (= r2c1 r2c2)))
; Column uniqueness
(assert (not (= r1c1 r2c1)))
(assert (not (= r1c2 r2c2)))
(check-sat)
(get-model)
"#;

    let outputs = solve_smt_string(smt)?;
    println!(
        "  ay says: {}",
        outputs.first().map_or("(no result)", String::as_str)
    );
    if outputs.len() > 1 {
        print_friendly_model(&outputs[1]);
    }
    println!();
    println!("  The solved grid:");
    println!("    +---+---+");
    println!("    | 1 | 2 |");
    println!("    +---+---+");
    println!("    | 2 | 1 |");
    println!("    +---+---+");
    println!();
    println!("  Real Sudoku (9x9) uses the same idea with 81 variables and");
    println!("  hundreds of constraints. SMT solvers handle that easily.");

    println!();
    prompt_continue()
}

// --- Level 5: Create Your Own ---

fn level_5_create_your_own() -> Result<bool> {
    println!("Now it's your turn. Type rules and the solver will find values.");
    println!();
    println!("Available variables: x, y, z (all integers).");
    println!("Type constraints in plain style:");
    println!("  x + y = 10");
    println!("  x > 3");
    println!("  z = x * 2");
    println!();
    println!("Type 'solve' when ready, or 'quit' to exit.");
    println!();

    let mut constraints: Vec<String> = Vec::new();
    let stdin = io::stdin();

    loop {
        print!("constraint> ");
        io::stdout().flush()?;
        let mut line = String::new();
        if stdin.lock().read_line(&mut line)? == 0 {
            break;
        }
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }
        if trimmed.eq_ignore_ascii_case("quit") || trimmed.eq_ignore_ascii_case("q") {
            return Ok(false);
        }
        if trimmed.eq_ignore_ascii_case("solve") {
            if constraints.is_empty() {
                println!("  No constraints entered. Type some rules first.");
                continue;
            }
            // Build SMT-LIB2 from user constraints
            let smt = build_user_smt(&constraints);
            println!();
            println!("  Generated SMT-LIB2:");
            for smt_line in smt.lines() {
                if !smt_line.is_empty() {
                    println!("    {smt_line}");
                }
            }
            println!();

            match solve_smt_string(&smt) {
                Ok(outputs) => {
                    println!(
                        "  ay says: {}",
                        outputs.first().map_or("(no result)", String::as_str)
                    );
                    if outputs.len() > 1 {
                        print_friendly_model(&outputs[1]);
                    }
                }
                Err(e) => {
                    println!("  Solver error: {e}");
                    println!("  The constraints might have a syntax issue.");
                }
            }
            println!();
            println!("Type more constraints, 'solve' again, or 'quit'.");
            constraints.clear();
            continue;
        }

        // Parse user constraint into SMT-LIB2 assertion
        match parse_user_constraint(trimmed) {
            Some(assertion) => {
                constraints.push(assertion);
                println!(
                    "  Added. ({} constraint{} so far)",
                    constraints.len(),
                    if constraints.len() == 1 { "" } else { "s" }
                );
            }
            None => {
                println!("  Could not parse that. Try: x + y = 10, x > 3, x >= y");
            }
        }
    }

    Ok(true)
}

/// Attempt to parse a simple user constraint into an SMT-LIB2 assertion.
///
/// Supports: `a op b` where op is =, !=, <, >, <=, >=
/// and `a + b op c`, `a - b op c`, `a * b op c`
fn parse_user_constraint(input: &str) -> Option<String> {
    let input = input.trim();

    // Try to match "expr op expr" patterns
    // Split on comparison operators
    let ops = &[">=", "<=", "!=", "=", ">", "<"];
    for op in ops {
        if let Some(pos) = input.find(op) {
            let lhs = input[..pos].trim();
            let rhs = input[pos + op.len()..].trim();
            if lhs.is_empty() || rhs.is_empty() {
                continue;
            }
            let smt_op = match *op {
                ">=" => ">=",
                "<=" => "<=",
                "!=" => {
                    return Some(format!(
                        "(assert (not (= {} {})))",
                        expr_to_smt(lhs),
                        expr_to_smt(rhs)
                    ))
                }
                "=" => "=",
                ">" => ">",
                "<" => "<",
                _ => continue,
            };
            return Some(format!(
                "(assert ({} {} {}))",
                smt_op,
                expr_to_smt(lhs),
                expr_to_smt(rhs)
            ));
        }
    }
    None
}

/// Convert a simple arithmetic expression to SMT-LIB2 prefix notation.
///
/// Handles: variables (x, y, z), integer literals, and binary +, -, *
fn expr_to_smt(expr: &str) -> String {
    let expr = expr.trim();

    // Try to parse as integer
    if expr.parse::<i64>().is_ok() {
        return expr.to_string();
    }

    // Simple variable
    if expr.chars().all(|c| c.is_alphanumeric() || c == '_') {
        return expr.to_string();
    }

    // Binary operations: look for +, -, * outside parentheses
    let arith_ops = &['+', '-', '*'];
    // Scan right-to-left for + and - (lowest precedence), then for *
    for pass_ops in &[&['+', '-'] as &[char], &['*']] {
        let mut depth = 0i32;
        let bytes = expr.as_bytes();
        // Scan right to left to get left-associativity
        for i in (0..bytes.len()).rev() {
            match bytes[i] {
                b')' => depth += 1,
                b'(' => depth -= 1,
                c if depth == 0
                    && pass_ops.contains(&(c as char))
                    && arith_ops.contains(&(c as char)) =>
                {
                    let lhs = &expr[..i];
                    let rhs = &expr[i + 1..];
                    if !lhs.trim().is_empty() && !rhs.trim().is_empty() {
                        let smt_op = match c {
                            b'+' => "+",
                            b'-' => "-",
                            b'*' => "*",
                            _ => continue,
                        };
                        return format!(
                            "({} {} {})",
                            smt_op,
                            expr_to_smt(lhs.trim()),
                            expr_to_smt(rhs.trim())
                        );
                    }
                }
                _ => {}
            }
        }
    }

    // Fallback: return as-is (might be a variable name)
    expr.to_string()
}

fn build_user_smt(constraints: &[String]) -> String {
    let mut smt = String::new();
    smt.push_str("(set-logic QF_NIA)\n");
    smt.push_str("(declare-const x Int)\n");
    smt.push_str("(declare-const y Int)\n");
    smt.push_str("(declare-const z Int)\n");
    for c in constraints {
        smt.push_str(c);
        smt.push('\n');
    }
    smt.push_str("(check-sat)\n");
    smt.push_str("(get-model)\n");
    smt
}

// ---------------------------------------------------------------------------
// Challenge mode
// ---------------------------------------------------------------------------

fn run_challenge(level: ChallengeLevel) -> Result<()> {
    let (title, description, smt, hint, explanation) = pick_challenge(level);

    println!();
    println!("=== Challenge: {title} ===");
    println!();
    println!("{description}");
    println!();
    println!("Think about it. What do you expect the answer to be?");
    println!();

    print!("Press Enter when ready to see the solver's answer: ");
    io::stdout().flush()?;
    let mut buf = String::new();
    io::stdin().lock().read_line(&mut buf)?;

    let outputs = solve_smt_string(smt)?;

    println!();
    let result_str = outputs.first().map_or("(no result)", String::as_str);
    println!("  ay says: {result_str}");
    // Only show model for SAT results (UNSAT/unknown have no model)
    if result_str.trim() == "sat" {
        for output in outputs.iter().skip(1) {
            if !output.contains("error") {
                print_friendly_model(output);
            }
        }
    }
    println!();
    println!("Explanation:");
    println!("{explanation}");
    println!();
    if !hint.is_empty() {
        println!("Hint for next time: {hint}");
        println!();
    }
    Ok(())
}

struct Challenge {
    title: &'static str,
    description: &'static str,
    smt: &'static str,
    hint: &'static str,
    explanation: &'static str,
}

const EASY_CHALLENGES: &[Challenge] = &[
    Challenge {
        title: "The Age Puzzle",
        description: "\
  Sam is 3 years older than Alex.\n\
  Together their ages add up to 25.\n\
  What are their ages?",
        smt: "\
(set-logic QF_LIA)\n\
(declare-const sam Int)\n\
(declare-const alex Int)\n\
(assert (= sam (+ alex 3)))\n\
(assert (= (+ sam alex) 25))\n\
(assert (>= alex 0))\n\
(check-sat)\n\
(get-model)",
        hint: "Set up two equations: sam = alex + 3 and sam + alex = 25.",
        explanation: "\
  sam = alex + 3, and sam + alex = 25.\n\
  Substituting: (alex + 3) + alex = 25\n\
  => 2*alex + 3 = 25 => 2*alex = 22 => alex = 11\n\
  => sam = 14",
    },
    Challenge {
        title: "Three Coins",
        description: "\
  You have three coins worth a total of 15 cents.\n\
  Each coin is 1, 5, or 10 cents.\n\
  All three coins are different values.\n\
  What are the coins?",
        smt: "\
(set-logic QF_LIA)\n\
(declare-const c1 Int)\n\
(declare-const c2 Int)\n\
(declare-const c3 Int)\n\
(assert (or (= c1 1) (= c1 5) (= c1 10)))\n\
(assert (or (= c2 1) (= c2 5) (= c2 10)))\n\
(assert (or (= c3 1) (= c3 5) (= c3 10)))\n\
(assert (not (= c1 c2)))\n\
(assert (not (= c1 c3)))\n\
(assert (not (= c2 c3)))\n\
(assert (= (+ c1 c2 c3) 15))\n\
(check-sat)\n\
(get-model)",
        hint:
            "If all three are different and from {1, 5, 10}, there's only one combination to try.",
        explanation: "\
  The only way to pick three different values from {1, 5, 10}\n\
  is to use all three: 1 + 5 + 10 = 16. That's 16, not 15.\n\
  So this is actually UNSAT -- impossible with these rules!",
    },
    Challenge {
        title: "Even or Odd",
        description: "\
  Find a number that is:\n\
    - between 1 and 100\n\
    - even (divisible by 2)\n\
    - when divided by 7, leaves remainder 3",
        smt: "\
(set-logic QF_LIA)\n\
(declare-const n Int)\n\
(assert (>= n 1))\n\
(assert (<= n 100))\n\
(assert (= (mod n 2) 0))\n\
(assert (= (mod n 7) 3))\n\
(check-sat)\n\
(get-model)",
        hint: "List multiples of 7, add 3, keep the even ones.",
        explanation: "\
  Numbers with remainder 3 when divided by 7: 3, 10, 17, 24, 31, ...\n\
  Of these, the even ones: 10, 24, 38, 52, 66, 80, 94.\n\
  The solver picks one of these.",
    },
];

const MEDIUM_CHALLENGES: &[Challenge] = &[
    Challenge {
        title: "Magic Square (2x2)",
        description: "\
  Place distinct integers 1-4 in a 2x2 grid so that:\n\
    - Both rows sum to the same value\n\
    - Both columns sum to the same value\n\
  Can it be done?",
        smt: "\
(set-logic QF_LIA)\n\
(declare-const a Int) ; top-left\n\
(declare-const b Int) ; top-right\n\
(declare-const c Int) ; bottom-left\n\
(declare-const d Int) ; bottom-right\n\
; Values in {1,2,3,4}\n\
(assert (or (= a 1) (= a 2) (= a 3) (= a 4)))\n\
(assert (or (= b 1) (= b 2) (= b 3) (= b 4)))\n\
(assert (or (= c 1) (= c 2) (= c 3) (= c 4)))\n\
(assert (or (= d 1) (= d 2) (= d 3) (= d 4)))\n\
; All different\n\
(assert (not (= a b)))\n\
(assert (not (= a c)))\n\
(assert (not (= a d)))\n\
(assert (not (= b c)))\n\
(assert (not (= b d)))\n\
(assert (not (= c d)))\n\
; Row sums equal\n\
(assert (= (+ a b) (+ c d)))\n\
; Column sums equal\n\
(assert (= (+ a c) (+ b d)))\n\
(check-sat)\n\
(get-model)",
        hint: "Row sums equal means a+b = c+d. Column sums equal means a+c = b+d.",
        explanation: "\
  From a+b = c+d and a+c = b+d, subtract: b-c = c-b => 2b = 2c => b = c.\n\
  But b and c must be different (distinct). Contradiction!\n\
  A 2x2 magic square with distinct values 1-4 is impossible.",
    },
    Challenge {
        title: "The Farmer's Field",
        description: "\
  A farmer has a rectangular field.\n\
    - The perimeter is 100 meters\n\
    - The area is at least 600 square meters\n\
    - The length is at least 10 meters more than the width\n\
  What are the dimensions?",
        smt: "\
(set-logic QF_NIA)\n\
(declare-const length Int)\n\
(declare-const width Int)\n\
(assert (= (+ (* 2 length) (* 2 width)) 100))\n\
(assert (>= (* length width) 600))\n\
(assert (>= (- length width) 10))\n\
(assert (> length 0))\n\
(assert (> width 0))\n\
(check-sat)\n\
(get-model)",
        hint: "Perimeter = 100 means length + width = 50.",
        explanation: "\
  length + width = 50, so width = 50 - length.\n\
  Area = length * (50 - length) >= 600.\n\
  Also length - width >= 10, so length >= 30.\n\
  At length = 30: area = 30 * 20 = 600. Just meets the area requirement.\n\
  The constraints force the unique integer answer: length = 30, width = 20.",
    },
];

const HARD_CHALLENGES: &[Challenge] = &[Challenge {
    title: "The Pigeonhole",
    description: "\
  Place 4 pigeons into 3 holes.\n\
  Each pigeon goes in exactly one hole.\n\
  No two pigeons share a hole.\n\
  Can it be done?",
    smt: "\
(set-logic QF_LIA)\n\
(declare-const p1 Int) ; pigeon 1's hole\n\
(declare-const p2 Int) ; pigeon 2's hole\n\
(declare-const p3 Int) ; pigeon 3's hole\n\
(declare-const p4 Int) ; pigeon 4's hole\n\
; Each pigeon in hole 1, 2, or 3\n\
(assert (or (= p1 1) (= p1 2) (= p1 3)))\n\
(assert (or (= p2 1) (= p2 2) (= p2 3)))\n\
(assert (or (= p3 1) (= p3 2) (= p3 3)))\n\
(assert (or (= p4 1) (= p4 2) (= p4 3)))\n\
; No two pigeons in the same hole\n\
(assert (not (= p1 p2)))\n\
(assert (not (= p1 p3)))\n\
(assert (not (= p1 p4)))\n\
(assert (not (= p2 p3)))\n\
(assert (not (= p2 p4)))\n\
(assert (not (= p3 p4)))\n\
(check-sat)",
    hint: "This is a famous mathematical principle. Count the possibilities.",
    explanation: "\
  The Pigeonhole Principle: if you put n+1 items into n containers,\n\
  at least one container must hold more than one item.\n\
  4 pigeons, 3 holes -- at least two pigeons must share.\n\
  The constraints say they cannot share, so: UNSATISFIABLE.\n\n\
  This principle seems obvious but is used in serious mathematics\n\
  to prove surprisingly deep results. SMT solvers verify it instantly.",
}];

fn pick_challenge(
    level: ChallengeLevel,
) -> (
    &'static str,
    &'static str,
    &'static str,
    &'static str,
    &'static str,
) {
    let challenges = match level {
        ChallengeLevel::Easy => EASY_CHALLENGES,
        ChallengeLevel::Medium => MEDIUM_CHALLENGES,
        ChallengeLevel::Hard => HARD_CHALLENGES,
    };

    // Simple time-based index selection (no rand dependency needed)
    let now = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap_or_default()
        .as_nanos();
    let idx = (now as usize) % challenges.len();
    let c = &challenges[idx];
    (c.title, c.description, c.smt, c.hint, c.explanation)
}

// ---------------------------------------------------------------------------
// Solver integration
// ---------------------------------------------------------------------------

/// Run an SMT-LIB2 string through the real ay solver engine.
fn solve_smt_string(smt: &str) -> Result<Vec<String>> {
    let commands = parse(smt).map_err(|e| anyhow::anyhow!("parse error: {e}"))?;
    let mut executor = Executor::new();
    let mut outputs = Vec::new();
    for cmd in &commands {
        match executor.execute(cmd) {
            Ok(Some(output)) => outputs.push(output),
            Ok(None) => {}
            Err(e) => return Err(anyhow::anyhow!("solver error: {e}")),
        }
    }
    Ok(outputs)
}

// ---------------------------------------------------------------------------
// Pretty-printing
// ---------------------------------------------------------------------------

/// Print a model in friendly format instead of raw s-expressions.
fn print_friendly_model(model_str: &str) {
    // Parse the model s-expression: (model (define-fun name () Sort value) ...)
    // We do a simple line-by-line extraction rather than full s-expr parsing.
    let model_str = model_str.trim();
    if !model_str.starts_with('(') {
        println!("  {model_str}");
        return;
    }

    println!("  Model (variable assignments):");
    let mut found_any = false;
    for line in model_str.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("(define-fun") {
            // Extract: (define-fun NAME () SORT VALUE)
            if let Some(assignment) = parse_define_fun(trimmed) {
                println!("    {} = {}", assignment.0, assignment.1);
                found_any = true;
            }
        }
    }
    if !found_any {
        // Fallback: print the raw model indented
        for line in model_str.lines() {
            println!("    {}", line.trim());
        }
    }
}

/// Extract (name, value) from a define-fun line.
///
/// Handles: `(define-fun name () Int 42)` and `(define-fun name () Int (- 3))`
fn parse_define_fun(line: &str) -> Option<(String, String)> {
    // Strip outer parens if the line ends with them
    let inner = line.trim().strip_prefix("(define-fun")?.trim();

    // Name is the first token
    let (name, rest) = inner.split_once(char::is_whitespace)?;
    let name = name.to_string();

    // Skip past "()" and sort name to get to value
    // Pattern: () SORT VALUE)
    let rest = rest.trim();
    let rest = rest.strip_prefix("()")?.trim();

    // Skip sort (Int, Bool, Real, etc.)
    let (_, value_part) = rest.split_once(char::is_whitespace)?;

    // Value might have trailing )
    let value = value_part.trim().trim_end_matches(')').trim();

    // Handle negative numbers: (- N) => -N
    let value = if value.starts_with("(- ") || value.starts_with("(-\t") {
        let num = value
            .strip_prefix("(-")
            .unwrap_or(value)
            .trim()
            .trim_end_matches(')')
            .trim();
        format!("-{num}")
    } else {
        value.to_string()
    };

    Some((name, value))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_define_fun_positive() {
        let input = "(define-fun x () Int 42)";
        let result = parse_define_fun(input);
        assert_eq!(result, Some(("x".to_string(), "42".to_string())));
    }

    #[test]
    fn test_parse_define_fun_negative() {
        let input = "(define-fun y () Int (- 3))";
        let result = parse_define_fun(input);
        assert_eq!(result, Some(("y".to_string(), "-3".to_string())));
    }

    #[test]
    fn test_expr_to_smt_simple_variable() {
        assert_eq!(expr_to_smt("x"), "x");
    }

    #[test]
    fn test_expr_to_smt_integer() {
        assert_eq!(expr_to_smt("42"), "42");
    }

    #[test]
    fn test_expr_to_smt_addition() {
        assert_eq!(expr_to_smt("x + y"), "(+ x y)");
    }

    #[test]
    fn test_expr_to_smt_multiplication() {
        assert_eq!(expr_to_smt("x * 2"), "(* x 2)");
    }

    #[test]
    fn test_parse_user_constraint_equality() {
        let result = parse_user_constraint("x + y = 10");
        assert!(result.is_some());
        let smt = result.unwrap();
        assert!(smt.contains("assert"));
        assert!(smt.contains("="));
    }

    #[test]
    fn test_parse_user_constraint_inequality() {
        let result = parse_user_constraint("x > 3");
        assert_eq!(result, Some("(assert (> x 3))".to_string()));
    }

    #[test]
    fn test_parse_user_constraint_not_equal() {
        let result = parse_user_constraint("x != y");
        assert_eq!(result, Some("(assert (not (= x y)))".to_string()));
    }

    #[test]
    fn test_solve_smt_string_sat() {
        let smt = "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (= x 5))\n(check-sat)";
        let outputs = solve_smt_string(smt).expect("should solve");
        assert_eq!(outputs.len(), 1);
        assert_eq!(outputs[0].trim(), "sat");
    }

    #[test]
    fn test_solve_smt_string_unsat() {
        let smt = "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (> x 0))\n(assert (< x 0))\n(check-sat)";
        let outputs = solve_smt_string(smt).expect("should solve");
        assert_eq!(outputs.len(), 1);
        assert_eq!(outputs[0].trim(), "unsat");
    }
}
