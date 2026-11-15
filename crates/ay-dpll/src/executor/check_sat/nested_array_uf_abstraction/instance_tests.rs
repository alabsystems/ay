// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The appended axiom instances (#nested-array-checked-rung): the record-boxed
//! MODEL_CHECKER_CONSUMER shapes they let the rung refute, satisfiable twins that must never
//! be refuted (on the abstraction, and with a FORGED engine `unsat` driven
//! straight into the quarantine), each family's UNSAT counterpart, and the
//! capability limit (extensionality). The forgery controls live in the
//! `forgery` child.

use super::*;
use crate::executor::SolveResult;

#[path = "instance_forgery_tests.rs"]
mod forgery;

/// MODEL_CHECKER_CONSUMER's `vec_ancestor_conflict` row (z3: `unsat`): an outer array of
/// `VecIntoIter` records whose `Vec` carries a byte array. Its refutation
/// needs `fld_len (Vec_mk .. 65 ..) = 65`, a selector over a constructor.
const VEC_ANCESTOR: &str = include_str!(
    "../../../../../../benchmarks/smt/model_checker_consumer_nested_residual/vec_ancestor_conflict_unsat.smt2"
);

fn script_body(script: &str) -> String {
    script
        .lines()
        .filter(|line| !line.contains("(check-sat)") && line.trim() != "(exit)")
        .collect::<Vec<_>>()
        .join("\n")
}

fn honest(script: &str) -> (Executor, Vec<TermId>, ArrayUfAbstraction, Box<[TermId]>) {
    let (mut exec, roots, abstraction) = built(&script_body(script));
    assert!(is_pure_renaming(&exec.ctx.terms, &roots, &abstraction));
    let instances = instances::axiom_instances(&mut exec.ctx.terms, &abstraction);
    assert!(instances_are_valid(
        &exec.ctx.terms,
        &abstraction,
        &instances
    ));
    (exec, roots, abstraction, instances)
}

fn strictly_refuted(exec: &mut Executor, problem: Vec<TermId>) -> bool {
    exec.checked_strict_exact_unsat_solve(problem, 5_000)
        .is_some()
}

/// Solve `script` up to its `check-sat`, then hand the quarantine a FORGED
/// engine `unsat` for its hard roots: the one situation in which the rung
/// matters for soundness. `unknown` means the rung withheld it.
fn quarantine_forged_unsat(script: &str) -> SolveResult {
    let (mut exec, roots) = load(&script_body(script));
    exec.begin_public_solve(false);
    exec.bind_unsat_query_assumptions(&[]);
    exec.quarantine_unverified_nested_array_unsat(&roots, Some(&roots), SolveResult::unsat())
}

#[test]
fn the_ancestor_row_is_refuted_through_a_checked_selector_instance() {
    let (mut exec, roots, abstraction, instances) = honest(VEC_ANCESTOR);
    assert_eq!(instances.len(), 1, "fld_len over Vec_mk");
    assert!(
        !strictly_refuted(&mut exec, abstraction.roots().to_vec()),
        "the pure renaming alone forgets the selector axiom"
    );
    assert!(strictly_refuted(
        &mut exec,
        abstract_problem(&abstraction, &instances)
    ));
    assert!(exec.nested_array_uf_abstraction_unsat(&roots));
    assert!(
        quarantine_forged_unsat(VEC_ANCESTOR).is_unsat(),
        "positive control"
    );
}

/// A miss index EQUAL to the written index (`k = 1`, write at 1).
const MISS_AT_WRITTEN_INDEX: &str = "\
    (declare-const m (Array Int (Array Int Int)))(declare-const k Int)\
    (declare-const c (Array Int Int))(assert (= k 1))\
    (assert (= (select (select m 1) 0) 7))(assert (= (select c 0) 5))\
    (assert (= (select (select (store m 1 c) k) 0) 5))";
/// Two fields of one sort; only `l` is read.
const SAME_SORTED_FIELDS: &str = "\
    (declare-datatype P ((mk (l (Array Int Int)) (r (Array Int Int)))))\
    (declare-const t (Array Int P))(declare-const x (Array Int Int))\
    (declare-const y (Array Int Int))(assert (= (select t 0) (mk x y)))\
    (assert (= (select (l (select t 0)) 0) 1))(assert (= (select y 0) 2))";
/// A read of a constant outer array.
const CONSTANT_READ: &str = "\
    (declare-const m (Array Int (Array Int Int)))(declare-const c (Array Int Int))\
    (declare-const d (Array Int Int))\
    (assert (= m ((as const (Array Int (Array Int Int))) c)))\
    (assert (= (select (select m 0) 0) 5))(assert (= (select d 0) 6))";
/// A selector of the OTHER constructor.
const FOREIGN_SELECTOR: &str = "\
    (declare-datatype E ((A (fa (Array Int Int))) (B (fb (Array Int Int)))))\
    (declare-const t (Array Int E))(declare-const x (Array Int Int))\
    (assert (= (select t 0) (A x)))(assert (= (select (fb (select t 0)) 0) 1))\
    (assert (= (select x 0) 2))";
/// A write read at ANOTHER index.
const READ_ELSEWHERE: &str = "\
    (declare-const m (Array Int (Array Int Int)))(declare-const k Int)(assert (= k 2))\
    (assert (not (= (select (select (store m 1 ((as const (Array Int Int)) 5)) k) 0) 5)))";

/// Each family's UNSAT counterpart (z3: `unsat`): the pure renaming alone is
/// not refuted, the renaming plus its checked instances is, on a strict proof.
/// The completeness pin behind each family (dropping one family's instances
/// turns its row red).
#[test]
fn each_family_refutes_its_unsat_counterpart() {
    let miss = "(declare-const m (Array Int (Array Int Int)))(declare-const k Int)(assert (= k 2))\
        (assert (not (= (select (select (store m 1 ((as const (Array Int Int)) 5)) k) 0)\
        (select (select m k) 0))))";
    let constant = "(declare-const m (Array Int (Array Int Int)))(declare-const c (Array Int Int))\
        (assert (= m ((as const (Array Int (Array Int Int))) c)))\
        (assert (not (= (select (select m 0) 0) (select c 0))))";
    let hit = "(declare-const m (Array Int (Array Int Int)))(declare-const k Int)\
        (declare-const c (Array Int Int))(assert (= k 1))(assert (= (select c 0) 5))\
        (assert (= (select (select (store m 1 c) k) 0) 6))";
    let selector = SAME_SORTED_FIELDS.replace("(l (select t 0))", "(r (select t 0))");
    for (label, script) in [
        ("read over write, other index", miss),
        ("read over constant", constant),
        ("read over write, written index", hit),
        ("selector over constructor", selector.as_str()),
    ] {
        let (mut exec, roots, abstraction, instances) = honest(script);
        assert!(!instances.is_empty(), "{label}");
        assert!(
            !strictly_refuted(&mut exec, abstraction.roots().to_vec()),
            "{label}: the renaming alone forgets the axiom"
        );
        assert!(exec.nested_array_uf_abstraction_unsat(&roots), "{label}");
    }
}

/// All six are satisfiable (z3: `sat`), so neither the honest abstraction
/// nor the rung may refute them, whatever the engine claims.
#[test]
fn satisfiable_twins_are_never_refuted() {
    let ancestor_twin = VEC_ANCESTOR.replace("(_ bv66 64)))", "(_ bv65 64)))");
    for (label, script) in [
        ("miss at the written index", MISS_AT_WRITTEN_INDEX),
        ("same-sorted fields", SAME_SORTED_FIELDS),
        ("constant read", CONSTANT_READ),
        ("foreign selector", FOREIGN_SELECTOR),
        ("read elsewhere", READ_ELSEWHERE),
        ("ancestor with len 65", ancestor_twin.as_str()),
    ] {
        let (mut exec, _, abstraction, instances) = honest(script);
        let problem = abstract_problem(&abstraction, &instances);
        assert!(!strictly_refuted(&mut exec, problem.clone()), "{label}");
        assert!(
            exec.checked_exact_unsat_solve(problem, 5_000).is_none(),
            "{label}: the abstraction is satisfiable"
        );
        assert!(quarantine_forged_unsat(script).is_unknown(), "{label}");
    }
}

/// THE RUNG'S NEGATIVE CONTROL (#nested-array-checked-rung; it replaced
/// `array_soundness`'s read-over-write control, which the instances now
/// refute). A CAPABILITY pin, not a soundness one: z3 answers `unsat`, so
/// publishing would be correct, but the refutation needs the outer array's
/// extensionality (equal after one write, equal at the written index, hence
/// equal), which no instance supplies. The abstraction is satisfiable, so the
/// rung must not claim it and the shed posture still withholds the verdict.
#[test]
fn an_extensionality_refutation_stays_withheld() {
    const SCRIPT: &str = "\
        (declare-const a (Array Int (Array Int Int)))\
        (declare-const b (Array Int (Array Int Int)))(declare-const x (Array Int Int))\
        (assert (= (store a 0 x) (store b 0 x)))(assert (= (select a 0) (select b 0)))\
        (assert (not (= a b)))";
    let (mut exec, roots, abstraction, instances) = honest(SCRIPT);
    assert!(!strictly_refuted(
        &mut exec,
        abstract_problem(&abstraction, &instances)
    ));
    assert!(!exec.nested_array_uf_abstraction_unsat(&roots));
    let commands = ay_frontend::parse(&format!("{SCRIPT}(check-sat)")).expect("parses");
    let mut exec = Executor::new();
    exec.set_competition_mode(true);
    let outputs = exec.execute_all(&commands).expect("executes");
    assert_eq!(
        (
            outputs[0].as_str(),
            exec.statistics().get_string("unknown.phase")
        ),
        ("unknown", Some("array-combination-quarantine"))
    );
}

/// Linear time: groundness is decided once per DAG node, never per tree path.
/// The index `k40`, with `k_{i+1} = (f k_i k_i)`, is a 41-node DAG whose tree
/// unfolding has 2^40 paths; a walk without a per-node memo never returns.
#[test]
#[ntest::timeout(60_000)]
fn a_deeply_shared_index_is_abstracted_in_linear_time() {
    let mut script = String::from(
        "(declare-datatype Row ((mk_row (cells (Array (_ BitVec 8) (_ BitVec 8))))))\
         (declare-fun f ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))\
         (declare-const k0 (_ BitVec 8))(declare-const t (Array (_ BitVec 8) Row))",
    );
    for i in 0..40 {
        script.push_str(&format!(
            "(define-fun k{} () (_ BitVec 8) (f k{i} k{i}))",
            i + 1
        ));
    }
    script.push_str(
        "(assert (= (select (cells (select t k40)) #x00) #x05))\
         (assert (= (select (store t k40 (mk_row ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x07)))\
            #x01) (select t #x01)))",
    );
    let (_, _, _, instances) = honest(&script);
    assert!(!instances.is_empty(), "the write at k40 yields instances");
}

/// Bounded work past the cap: `m` is read at 1000 distinct ground indices and
/// written once at a symbolic index, so that one write asks for 1001
/// instances, far past [`instances::MAX_AXIOM_INSTANCES`]. The builder must
/// fall back to the pure renaming (no instances) and stop interning as soon
/// as it passes the cap: about four terms per instance up to the cap, never
/// four per noted index. Measured: without the in-loop cap the write interns
/// 4001 terms before the fallback discards them.
#[test]
#[ntest::timeout(60_000)]
fn an_overflowing_write_interns_at_most_the_cap() {
    let mut script = String::from(
        "(declare-const m (Array Int (Array Int Int)))(declare-const c (Array Int Int))\
         (declare-const w Int)",
    );
    for i in 0..1000 {
        script.push_str(&format!("(assert (= (select (select m {i}) 0) {i}))"));
    }
    script.push_str("(assert (= (select (select (store m w c) 0) 1) 5))");
    let (mut exec, roots, abstraction) = built(&script);
    assert!(is_pure_renaming(&exec.ctx.terms, &roots, &abstraction));
    let before = exec.ctx.terms.len();
    let instances = instances::axiom_instances(&mut exec.ctx.terms, &abstraction);
    let interned = exec.ctx.terms.len() - before;
    assert!(
        instances.is_empty(),
        "past the cap only the pure renaming is refuted"
    );
    assert!(
        interned <= 8 * instances::MAX_AXIOM_INSTANCES,
        "interned {interned} terms for a problem past the cap"
    );
}
