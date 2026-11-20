// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `printed_assume_text` is rendered BOUNDED and classifies exactly as the
//! unbounded render-then-measure did (DR-PROOF-RENDER-BUDGET-20261118).

use ay_frontend::parse;

use super::{Executor, MAX_SHELL_SURFACE_BYTES, MAX_SHELL_TOTAL_BYTES, PRINTED_ASSUME_RENDERS};

/// `(assert (let ((a1 (f x x))) (let ((a2 (f a1 a1))) … (= a_depth c))))`,
/// whose canonical form is a doubling chain of `2^depth - 1` applications,
/// made unsat by an unrelated contradiction.
fn let_rooted_problem(depth: usize) -> String {
    let mut root = String::new();
    let mut close = String::new();
    for i in 1..=depth {
        let previous = if i == 1 {
            "x".to_string()
        } else {
            format!("a{}", i - 1)
        };
        root.push_str(&format!("(let ((a{i} (f {previous} {previous}))) "));
        close.push(')');
    }
    root.push_str(&format!("(= a{depth} c)"));
    root.push_str(&close);
    format!(
        "(set-option :produce-proofs true)\n\
         (set-logic QF_UF)\n\
         (declare-sort U 0)\n\
         (declare-fun f (U U) U)\n\
         (declare-fun x () U)\n\
         (declare-fun c () U)\n\
         (declare-fun zz () Bool)\n\
         (assert {root})\n\
         (assert zz)\n\
         (assert (not zz))\n\
         (check-sat)\n"
    )
}

fn solve(text: &str) -> Executor {
    let commands = parse(text).expect("parse");
    let mut exec = Executor::new();
    assert_eq!(exec.execute_all(&commands).expect("exec"), vec!["unsat"]);
    exec
}

/// The classification the unbounded render-then-measure gave the `let`-rooted
/// assertion: faithful exactly when its printed text fits and is a `let`.
fn unbounded_faithful(exec: &Executor) -> bool {
    let canonical = exec.proof_original_problem_assertions_slice()[0];
    let printed = match exec.proof_export_term_overrides() {
        Some(table) => {
            ay_proof::format_term_alethe_with_overrides(&exec.ctx.terms, canonical, &table)
        }
        None => ay_proof::format_term_alethe(&exec.ctx.terms, canonical),
    };
    printed.len() <= MAX_SHELL_SURFACE_BYTES && printed.starts_with("(let ")
}

#[test]
fn a_small_let_rooted_assertion_classifies_as_the_unbounded_render_did() {
    for depth in [1, 3, 12, 14] {
        let exec = solve(&let_rooted_problem(depth));
        let canonical = exec.proof_original_problem_assertions_slice()[0];
        let spellings = exec.authored_negation_shell_spellings();
        assert_eq!(
            !spellings.unbridgeable.contains(&canonical),
            unbounded_faithful(&exec),
            "depth {depth}"
        );
    }
}

#[test]
fn a_tree_sized_let_rooted_assertion_is_judged_without_rendering_its_tree() {
    // 2^48 applications: the unbounded render needs ~1e15 bytes. The bounded
    // one stops at the per-assertion cap.
    let started = std::time::Instant::now();
    let exec = solve(&let_rooted_problem(48));
    let canonical = exec.proof_original_problem_assertions_slice()[0];
    let bounded = exec.printed_assume_text(canonical, &mut None, &mut false);
    let spellings = exec.authored_negation_shell_spellings();
    assert_eq!(
        !spellings.unbridgeable.contains(&canonical),
        bounded.is_some_and(|text| text.starts_with("(let ")),
    );
    assert!(started.elapsed().as_secs() < 120, "{:?}", started.elapsed());
}

/// `count` independent tree-sized `let`-rooted assertions over distinct
/// bases `x0`, `x1`, …, then ONE small `let`-rooted assertion
/// `(let ((b (f y y))) (= b c))`, made unsat by an unrelated contradiction.
fn tree_sized_then_small_let_problem(count: usize, depth: usize) -> String {
    let mut declarations = String::new();
    let mut assertions = String::new();
    for k in 0..count {
        declarations.push_str(&format!("(declare-fun x{k} () U)\n"));
        let mut root = String::new();
        let mut close = String::new();
        for i in 1..=depth {
            let previous = if i == 1 {
                format!("x{k}")
            } else {
                format!("a{}", i - 1)
            };
            root.push_str(&format!("(let ((a{i} (f {previous} {previous}))) "));
            close.push(')');
        }
        assertions.push_str(&format!("(assert {root}(= a{depth} c){close})\n"));
    }
    format!(
        "(set-option :produce-proofs true)\n\
         (set-logic QF_UF)\n\
         (declare-sort U 0)\n\
         (declare-fun f (U U) U)\n\
         {declarations}\
         (declare-fun y () U)\n\
         (declare-fun c () U)\n\
         (declare-fun zz () Bool)\n\
         {assertions}\
         (assert (let ((b (f y y))) (= b c)))\n\
         (assert zz)\n\
         (assert (not zz))\n\
         (check-sat)\n"
    )
}

#[test]
fn a_let_rooted_assertion_after_many_declined_ones_classifies_as_the_unbounded_render_did() {
    // Review 1 finding 1 (DR-PROOF-RENDER-BUDGET-20261118): an 8 MiB TOTAL
    // on the `let`-rooted branch, charged a whole 64 KiB cap per decline,
    // was spent by the 128th tree-sized assertion, and every `let`-rooted
    // assertion after it was classed unbridgeable unrendered. That reads as
    // a FOREIGN premise and withholds `unsat` under `--strict-proofs` and
    // `--self-check`. Every assertion must be rendered and judged by the
    // per-assertion cap alone, as origin/main judged it.
    //
    // The review's other shape, 200 faithful `let`-rooted asserts of ~50 KB
    // (10 MB), is not a usable fixture: past ~2 MB of input the mandatory
    // strict certification answers `unknown` on origin/main itself
    // (measured on main 324d67d74: `unsat` at 40 x 48 KB, `unknown`,
    // `self-check-rejected`, at 60), and without the proof no `let` override
    // exists to be faithful to. This pins the same aggregate.
    let count = MAX_SHELL_TOTAL_BYTES / MAX_SHELL_SURFACE_BYTES + 12;
    let exec = solve(&tree_sized_then_small_let_problem(count, 48));
    let originals = exec.proof_original_problem_assertions_slice().to_vec();
    PRINTED_ASSUME_RENDERS.with(|renders| renders.set(0));
    let spellings = exec.authored_negation_shell_spellings();
    assert_eq!(
        PRINTED_ASSUME_RENDERS.with(std::cell::Cell::get),
        count + 1,
        "every `let`-rooted assertion is rendered and judged"
    );
    for canonical in &originals[..count] {
        assert!(spellings.unbridgeable.contains(canonical));
    }
    let small = originals[count];
    let printed = match exec.proof_export_term_overrides() {
        Some(table) => ay_proof::format_term_alethe_with_overrides(&exec.ctx.terms, small, &table),
        None => ay_proof::format_term_alethe(&exec.ctx.terms, small),
    };
    let unbounded = printed.len() <= MAX_SHELL_SURFACE_BYTES && printed.starts_with("(let ");
    // Without a `let` override in this export (it prints the eliminated
    // `(= c (f y y))`), both sides class it unbridgeable; what the old total
    // changed is that it was never RENDERED (128 renders, not 141), pinned
    // above. The verdict is the unbounded render's.
    assert_eq!(
        !spellings.unbridgeable.contains(&small),
        unbounded,
        "judged as the unbounded render judged it: {printed}"
    );
}
