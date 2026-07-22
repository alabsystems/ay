// QF_AUFLIA storecomm_invalid false-UNSAT soundness regression (#8785).
//
// Copyright (c) 2026 Andrew Yates Licensed under Apache-2.0.
// Author: Andrew Yates
//
// These guards cover SMT-LIB `storecomm_invalid_*` benchmarks
// (Armando/Bonacina/Ranise/Schulz PDPAR'05). The formulas are SAT:
// two large store towers differ at least at one index, and the Skolem
// witness can select that differing index. Example reproducer shape:
//
//   (declare-fun a1 () (Array Int Int))
//   (declare-fun e1 .. e40 () Int)
//   (declare-fun sk ((Array Int Int) (Array Int Int)) Int)
//   (assert
//     (let ((?v_0 (store ... (store a1 1 e1) ... 39 e39)))
//     (let ((?v_2 (store ... (store a1 8 e8) ... 40 e40)))
//     (let ((k (sk ?v_0 ?v_2)))
//       (not (= (select ?v_0 k) (select ?v_2 k)))))))
//
// `?v_0` builds a 39-store tower on indices 1..39 (no store at 40).
// `?v_2` builds a 39-store tower on a permutation of indices that
// includes index 40. Because `sk` is uninterpreted and `a1[40]` is
// unconstrained, the formula is SAT at `k=40` with `a1[40] != e40`.
//
// Any `unsat` result is therefore a soundness bug. The failure mode
// tracked by #8785 is an invalid theory-conflict chain that projects
// the top-level disequality onto unrelated shared internal store
// prefixes through ROW2/EUF interaction.
//
// These are behavioral soundness fences, not completeness tests:
// they reject `unsat`, but allow `sat` or `unknown`.

use ntest::timeout;
use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Stdio};

fn ay_bin() -> String {
    env!("CARGO_BIN_EXE_ay").to_string()
}

fn repo_root() -> PathBuf {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    // CARGO_MANIFEST_DIR points at crates/ay; repo root is two up.
    manifest
        .parent()
        .and_then(|p| p.parent())
        .map(PathBuf::from)
        .unwrap_or(manifest)
}

fn run_ay_on_file(rel_path: &str) -> (String, String) {
    let path = repo_root().join(rel_path);
    if !path.exists() {
        eprintln!(
            "SKIP: optional storecomm benchmark not found: {}",
            path.display()
        );
        return ("unknown\n".to_string(), String::new());
    }
    let output = Command::new(ay_bin())
        .arg("-t:20000")
        .arg(&path)
        .output()
        .expect("failed to spawn ay");
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    (stdout, stderr)
}

fn run_ay_on_input(input: &str) -> (String, String) {
    let mut child = Command::new(ay_bin())
        .arg("-t:20000")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn ay");
    {
        let stdin = child.stdin.as_mut().expect("stdin pipe");
        stdin
            .write_all(input.as_bytes())
            .expect("failed to write SMT-LIB to ay stdin");
    }
    let output = child.wait_with_output().expect("failed waiting on ay");
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    (stdout, stderr)
}

fn reduced_shared_prefix_storecomm_input_with_tail(
    include_witness_decls: bool,
    tail: &str,
) -> String {
    let lhs_indices = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 1];
    let rhs_indices = [7, 11, 4, 12, 6, 10, 5, 2, 1, 8, 3, 9];
    let mut smt = String::from(
        "(set-logic QF_AUFLIA)\n\
         (declare-fun a1 () (Array Int Int))\n",
    );
    if include_witness_decls {
        smt.push_str(
            "(declare-fun sk ((Array Int Int) (Array Int Int)) Int)\n\
             (declare-fun k () Int)\n",
        );
    }

    for idx in 1..=12 {
        smt.push_str(&format!("(declare-fun e{idx} () Int)\n"));
    }
    for prefix in ["lhs", "rhs"] {
        for step in 1..=12 {
            smt.push_str(&format!(
                "(declare-fun {prefix}_{step} () (Array Int Int))\n"
            ));
        }
    }

    let mut prev = String::from("a1");
    for (step, idx) in lhs_indices.iter().enumerate() {
        let curr = format!("lhs_{}", step + 1);
        smt.push_str(&format!(
            "(assert (= {curr} (store {prev} {idx} e{idx})))\n"
        ));
        prev = curr;
    }

    let mut prev = String::from("a1");
    for (step, idx) in rhs_indices.iter().enumerate() {
        let curr = format!("rhs_{}", step + 1);
        smt.push_str(&format!(
            "(assert (= {curr} (store {prev} {idx} e{idx})))\n"
        ));
        prev = curr;
    }

    smt.push_str(tail);
    smt
}

fn reduced_shared_prefix_storecomm_input() -> String {
    reduced_shared_prefix_storecomm_input_with_tail(
        true,
        "(assert (= k (sk lhs_12 rhs_12)))\n\
         (assert (not (= (select lhs_12 k) (select rhs_12 k))))\n\
         (check-sat)\n",
    )
}

fn reduced_shared_prefix_direct_disequality_storecomm_input() -> String {
    reduced_shared_prefix_storecomm_input_with_tail(
        false,
        "(assert (not (= lhs_12 rhs_12)))\n\
         (check-sat)\n",
    )
}

fn reduced_concrete_prefix_storecomm_input() -> String {
    let lhs_indices = [1, 2, 16, 32, 37, 1];
    let rhs_indices = [1, 37, 40, 32, 2, 16];
    let mut smt = String::from(
        "(set-logic QF_AUFLIA)\n\
         (declare-fun a1 () (Array Int Int))\n\
         (declare-fun sk ((Array Int Int) (Array Int Int)) Int)\n\
         (declare-fun k () Int)\n",
    );

    for idx in [1, 2, 16, 32, 37, 40] {
        smt.push_str(&format!("(declare-fun e{idx} () Int)\n"));
    }
    for prefix in ["lhs", "rhs"] {
        for step in 1..=6 {
            smt.push_str(&format!(
                "(declare-fun {prefix}_{step} () (Array Int Int))\n"
            ));
        }
    }

    let mut prev = String::from("a1");
    for (step, idx) in lhs_indices.iter().enumerate() {
        let curr = format!("lhs_{}", step + 1);
        smt.push_str(&format!(
            "(assert (= {curr} (store {prev} {idx} e{idx})))\n"
        ));
        prev = curr;
    }

    let mut prev = String::from("a1");
    for (step, idx) in rhs_indices.iter().enumerate() {
        let curr = format!("rhs_{}", step + 1);
        smt.push_str(&format!(
            "(assert (= {curr} (store {prev} {idx} e{idx})))\n"
        ));
        prev = curr;
    }

    smt.push_str(
        "(assert (= k (sk lhs_6 rhs_6)))\n\
         (assert (not (= (select lhs_6 k) (select rhs_6 k))))\n\
         (check-sat)\n",
    );
    smt
}

fn reduced_sparse_rhs_root_faithful_storecomm_input() -> String {
    String::from(
        "(set-logic QF_AUFLIA)\n\
         (declare-fun a () (Array Int Int))\n\
         (declare-fun rhs () (Array Int Int))\n\
         (declare-fun lhs () (Array Int Int))\n\
         (declare-fun i () Int)\n\
         (declare-fun j () Int)\n\
         (declare-fun k () Int)\n\
         (declare-fun vi () Int)\n\
         (declare-fun vj () Int)\n\
         (declare-fun vk () Int)\n\
         (declare-fun sk ((Array Int Int) (Array Int Int)) Int)\n\
         (assert (= rhs (store a i vi)))\n\
         (assert (= rhs (store a j vj)))\n\
         (assert (= lhs (store rhs k vk)))\n\
         (assert (= k (sk lhs rhs)))\n\
         (assert (distinct i j))\n\
         (assert (distinct k i))\n\
         (assert (distinct k j))\n\
         (assert (not (= (select lhs k) (select rhs k))))\n\
         (check-sat)\n",
    )
}

fn reduced_symbolic_witness_storecomm_input() -> String {
    let lhs_indices = [1, 2, 3, 4, 5, 6, 1];
    let rhs_indices = [4, 2, 5, 7, 1, 3, 6];

    let mut smt = String::from(
        "(set-logic QF_AUFLIA)\n\
         (declare-fun a1 () (Array Int Int))\n\
         (declare-fun sk ((Array Int Int) (Array Int Int)) Int)\n\
         (declare-fun k () Int)\n",
    );

    for idx in 1..=7 {
        smt.push_str(&format!("(declare-fun i{idx} () Int)\n"));
        smt.push_str(&format!("(declare-fun e{idx} () Int)\n"));
    }
    for lhs in 1..=7 {
        for rhs in (lhs + 1)..=7 {
            smt.push_str(&format!("(assert (distinct i{lhs} i{rhs}))\n"));
        }
    }

    let mut lhs_expr = String::from("a1");
    for idx in lhs_indices {
        lhs_expr = format!("(store {lhs_expr} i{idx} e{idx})");
    }
    let mut rhs_expr = String::from("a1");
    for idx in rhs_indices {
        rhs_expr = format!("(store {rhs_expr} i{idx} e{idx})");
    }

    smt.push_str(&format!(
        "(assert (= k (sk {lhs_expr} {rhs_expr})))\n\
         (assert (not (= (select {lhs_expr} k) (select {rhs_expr} k))))\n\
         (check-sat)\n"
    ));
    smt
}

fn first_line(stdout: &str) -> String {
    stdout.trim().lines().next().unwrap_or("").to_string()
}

/// #8785: 40-store invalid-commutativity reproducer.
/// Historical regression: ay returned `unsat` on this SAT benchmark.
/// This test guards against that false-UNSAT recurring. `sat` or clean
/// `unknown` are acceptable here; `unsat` is a regression.
#[test]
#[timeout(60_000)]
fn auflia_storecomm_invalid_40_003_is_not_unsat() {
    let (stdout, stderr) = run_ay_on_file(
        "benchmarks/smtcomp/QF_AUFLIA/storecomm_invalid_t3_pp_nf_ni_00040_003.cvc.smt2",
    );
    let result = first_line(&stdout);
    assert_ne!(
        result, "unsat",
        "Soundness regression (#8785): AY reported 'unsat' on the \
         40-store invalid-commutativity SAT instance (Z3 proves SAT). \
         The expected answer is 'sat' or 'unknown'; 'unsat' is a \
         soundness bug. stdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// #8785: 40-store invalid-commutativity reproducer (`_002` permutation).
/// Historical regression: ay returned `unsat` on this SAT benchmark too.
/// This test guards against that false-UNSAT recurring. `sat` or clean
/// `unknown` are acceptable here; `unsat` is a regression.
#[test]
#[timeout(60_000)]
fn auflia_storecomm_invalid_40_002_is_not_unsat() {
    let (stdout, stderr) = run_ay_on_file(
        "benchmarks/smtcomp/QF_AUFLIA/storecomm_invalid_t3_pp_nf_ni_00040_002.cvc.smt2",
    );
    let result = first_line(&stdout);
    assert_ne!(
        result, "unsat",
        "Soundness regression (#8785): AY reported 'unsat' on the \
         40-store invalid-commutativity SAT instance (`_002` permutation; \
         Z3 proves SAT). The expected answer is 'sat' or 'unknown'; \
         'unsat' is a soundness bug. stdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// #8785 + #8805: 30-store invalid-commutativity reproducer.
/// Historical regressions: this SAT benchmark previously panicked
/// (#8805) and also returned `unsat` (#8785).
/// This test guards against both failure modes. A crash or `unsat` is
/// a regression; `sat` or clean `unknown` are acceptable here.
#[test]
#[timeout(60_000)]
fn auflia_storecomm_invalid_30_008_is_not_unsat() {
    let (stdout, stderr) = run_ay_on_file(
        "benchmarks/smtcomp/QF_AUFLIA/storecomm_invalid_t1_pp_sf_ni_00030_008.cvc.smt2",
    );
    let result = first_line(&stdout);
    let panicked = stderr.contains("panicked at")
        || stderr.contains("BUG:")
        || stderr.contains("out-of-bounds");
    assert!(
        !panicked,
        "Soundness regression (#8805): AY panicked on the 30-store \
         invalid-commutativity SAT instance. stdout:\n{stdout}\n\
         stderr:\n{stderr}"
    );
    assert_ne!(
        result, "unsat",
        "Soundness regression (#8785): AY reported 'unsat' on the \
         30-store invalid-commutativity SAT instance (Z3 proves SAT). \
         The expected answer is 'sat' or 'unknown'; 'unsat' is a \
         soundness bug. stdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// #8785: 30-store direct-disequality family member.
///
/// Unlike the earlier `00030_008` fence, this benchmark reaches the same
/// invalid-commutativity family through a top-level array disequality rather
/// than a select-witness assertion. It must never return false `unsat`.
#[test]
#[timeout(60_000)]
fn auflia_storecomm_invalid_30_007_direct_disequality_is_not_unsat() {
    let (stdout, stderr) = run_ay_on_file(
        "benchmarks/smtcomp/QF_AUFLIA/storecomm_invalid_t1_np_nf_ni_00030_007.cvc.smt2",
    );
    let result = first_line(&stdout);
    let panicked = stderr.contains("panicked at")
        || stderr.contains("BUG:")
        || stderr.contains("out-of-bounds");
    assert!(
        !panicked,
        "Soundness regression: AY panicked on the 30-store \
         direct-disequality invalid-commutativity SAT instance. stdout:\n{stdout}\n\
         stderr:\n{stderr}"
    );
    assert_ne!(
        result, "unsat",
        "Soundness regression (#8785): AY reported 'unsat' on the \
         30-store direct-disequality invalid-commutativity SAT instance \
         (Z3 proves SAT). The expected answer is 'sat' or 'unknown'; \
         'unsat' is a soundness bug. stdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// Reduced generated family member for #8785.
///
/// This is smaller than the checked-in 30/40-store fixtures but keeps the same
/// shape: two reordered store towers over the same base, one deep repeated
/// write on the left, and one fresh witness index on the right. The formula is
/// SAT because the Skolem witness can pick index 12, where the right tower
/// stores `e12` and the left tower still reads the unconstrained base array.
///
/// This broadens coverage beyond exact benchmark files while still rejecting
/// only false `unsat`.
#[test]
#[timeout(60_000)]
fn auflia_storecomm_reduced_shared_prefix_family_member_is_not_unsat() {
    let input = reduced_shared_prefix_storecomm_input();
    let (stdout, stderr) = run_ay_on_input(&input);
    let result = first_line(&stdout);
    let panicked = stderr.contains("panicked at")
        || stderr.contains("BUG:")
        || stderr.contains("out-of-bounds");
    assert!(
        !panicked,
        "Soundness regression: AY panicked on reduced #8785 family member. \
         stdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert_ne!(
        result, "unsat",
        "Soundness regression (#8785): AY reported 'unsat' on a reduced \
         shared-prefix invalid-commutativity SAT instance. The expected answer \
         is 'sat' or 'unknown'; 'unsat' is a soundness bug. \
         stdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// Parfit's 12-index direct-disequality sibling for #8785.
///
/// This uses the same reduced 12-index store towers as the shared-prefix
/// witness canary above, but reaches the false-UNSAT family through a direct
/// top-level array disequality instead of an explicit Skolem select witness.
/// That keeps coverage on the direct-disequality branch without requiring the
/// larger checked-in `00030_007` benchmark.
#[test]
#[timeout(60_000)]
fn auflia_storecomm_reduced_shared_prefix_direct_disequality_is_not_unsat() {
    let input = reduced_shared_prefix_direct_disequality_storecomm_input();
    let (stdout, stderr) = run_ay_on_input(&input);
    let result = first_line(&stdout);
    let panicked = stderr.contains("panicked at")
        || stderr.contains("BUG:")
        || stderr.contains("out-of-bounds");
    assert!(
        !panicked,
        "Soundness regression: AY panicked on Parfit's reduced 12-index \
         direct-disequality #8785 family member. stdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert_ne!(
        result, "unsat",
        "Soundness regression (#8785): AY reported 'unsat' on Parfit's \
         reduced 12-index direct-disequality invalid-commutativity SAT \
         instance. The expected answer is 'sat' or 'unknown'; 'unsat' is a \
         soundness bug. stdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// Smaller concrete nested-store family member for #8785.
///
/// This instance keeps the repeated left-side write and the fresh right-side
/// witness index, but trims the tower down to six concrete stores. It catches
/// the same false-`unsat` class through an internal shared-prefix collapse:
/// the Skolem witness can pick index 40, where only the right tower writes.
#[test]
#[timeout(60_000)]
fn auflia_storecomm_reduced_concrete_prefix_family_member_is_not_unsat() {
    let input = reduced_concrete_prefix_storecomm_input();
    let (stdout, stderr) = run_ay_on_input(&input);
    let result = first_line(&stdout);
    let panicked = stderr.contains("panicked at")
        || stderr.contains("BUG:")
        || stderr.contains("out-of-bounds");
    assert!(
        !panicked,
        "Soundness regression: AY panicked on reduced concrete #8785 family member. \
         stdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert_ne!(
        result, "unsat",
        "Soundness regression (#8785): AY reported 'unsat' on a reduced \
         concrete-prefix invalid-commutativity SAT instance. The expected answer \
         is 'sat' or 'unknown'; 'unsat' is a soundness bug. \
        stdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// Smaller sparse-RHS/root-faithful family member for #8785.
///
/// `rhs` is constrained by two same-target store equalities over the same root
/// array `a`, but both writes can be faithful write-backs, so `rhs` can still
/// equal `a`. `lhs` then adds one fresh write at `k`, and the extensional
/// witness is forced to that fresh index rather than either write-back index.
///
/// This keeps the live `ROW2` / disjunctive store-target flavor while trimming
/// the reproducer to one named shared target and one sparse extra RHS branch.
#[test]
#[timeout(60_000)]
fn auflia_storecomm_reduced_sparse_rhs_root_faithful_family_member_is_not_unsat() {
    let input = reduced_sparse_rhs_root_faithful_storecomm_input();
    let (stdout, stderr) = run_ay_on_input(&input);
    let result = first_line(&stdout);
    let panicked = stderr.contains("panicked at")
        || stderr.contains("BUG:")
        || stderr.contains("out-of-bounds");
    assert!(
        !panicked,
        "Soundness regression: AY panicked on reduced sparse-RHS/root-faithful #8785 family member. \
         stdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert_ne!(
        result, "unsat",
        "Soundness regression (#8785): AY reported 'unsat' on a reduced \
         sparse-RHS/root-faithful invalid-commutativity SAT instance. The \
         expected answer is 'sat' or 'unknown'; 'unsat' is a soundness bug. \
         stdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// Smaller symbolic-witness family member for #8785 (`t1_pp_nf_ai_00030_002`).
///
/// This keeps the still-live `pp_nf_ai` shape: all indices are symbolic and
/// pairwise distinct, the left tower repeats `i1`, and the right tower is a
/// permutation that introduces one fresh RHS-only index `i7` before replaying
/// the shared root write. The formula is SAT because the Skolem witness can
/// pick `i7`, where only the right tower writes.
#[test]
#[timeout(60_000)]
fn auflia_storecomm_reduced_symbolic_witness_family_member_is_not_unsat() {
    let input = reduced_symbolic_witness_storecomm_input();
    let (stdout, stderr) = run_ay_on_input(&input);
    let result = first_line(&stdout);
    let panicked = stderr.contains("panicked at")
        || stderr.contains("BUG:")
        || stderr.contains("out-of-bounds");
    assert!(
        !panicked,
        "Soundness regression: AY panicked on reduced symbolic-witness #8785 family member. \
         stdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert_ne!(
        result, "unsat",
        "Soundness regression (#8785): AY reported 'unsat' on a reduced \
         symbolic-witness invalid-commutativity SAT instance. The expected \
         answer is 'sat' or 'unknown'; 'unsat' is a soundness bug. \
         stdout:\n{stdout}\nstderr:\n{stderr}"
    );
}
