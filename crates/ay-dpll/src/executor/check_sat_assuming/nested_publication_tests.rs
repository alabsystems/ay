// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use std::collections::BTreeSet;

/// END-TO-END pin for the forged-authority defect, run through the REAL
/// mandatory certification gate (`certify_unsat_for_publication` ->
/// `mint_unsat_certificate`) and then through the strict Alethe checker
/// that gate calls.
///
/// Shape (a minimal model of the deductive-checks `*_push_appends_entailed`
/// obligations that surfaced this): a public assumption query whose
/// SAT-level failed-assumption harvest is a MISATTRIBUTED proper subset --
/// the "wrong-but-AUTHENTIC" input `certify_assumption_core` exists to
/// reject. Its disposable exact-subset probe is Unknown, so the original
/// refutation and exact outer authority remain live. The source-presentation
/// resolver must then align the retained parsed ledger with Context's exact
/// concrete-authored rows: proof provenance intentionally contains only the
/// base while the other authored rows are exactly bound assumptions. Treating
/// that narrower provenance vector as the parsed-row index suppresses the
/// promised artifact, and a CORRECT refutation is published as `unknown` /
/// `SelfCheckRejected` even though every reachable source root belongs to the
/// base-or-assumption strict scope.
///
/// A shape-only assertion would not have caught this: the emitted steps
/// were always well-formed. Only running the emitter's own artifact
/// through the gate -- verdict AND `check_proof_strict` -- pins it.
#[test]
fn misattributed_harvest_recheck_keeps_the_authored_proof_authority() {
    // Base assertion is deliberately INDEPENDENT of the quantified pair so
    // the injected subset is satisfiable-but-undecided (Unknown) while the
    // full assumption set is refuted propositionally by `p and not p`.
    let script = r#"
        (set-option :produce-proofs true)
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (declare-fun g (Int) Int)
        (declare-fun h (Int) Int)
        (declare-const p Bool)
        (assert (>= (h 0) 0))
        (assert (forall ((x Int)) (exists ((y Int)) (> (f y) (g x)))))
        (assert (forall ((x Int)) (< (f x) 0)))
        (assert p)
        (assert (not p))
    "#;
    let commands = ay_frontend::parse(script).expect("script parses");
    let mut exec = Executor::new();
    exec.execute_all(commands.as_slice())
        .expect("setup commands execute");

    // Reproduce the named-core redirect's split: the base stays asserted,
    // everything else is assumption-tracked.
    let all = exec.ctx.assertions.clone();
    assert_eq!(all.len(), 5, "setup asserted an unexpected number of roots");
    let base = vec![all[0]];
    let assumed: Vec<TermId> = all[1..].to_vec();
    exec.ctx.assertions = base.clone();

    exec.begin_public_solve(false);
    exec.bind_unsat_query_assumptions(&assumed);
    let first = exec.check_sat_assuming(&assumed);
    assert!(
        matches!(first, Ok(SolveResult::Unsat(_))),
        "setup solve must refute the full assumption set: {first:?}"
    );

    // The misattributed harvest: a proper subset that does NOT re-prove
    // UNSAT (here: undecided). This is the documented defect class the
    // certificate gate exists for, injected rather than waited for.
    exec.last_assumption_core = Some(vec![assumed[0], assumed[1]]);
    let certified = exec
        .certify_assumption_core(&assumed, first)
        .expect("core certification does not error");

    // 1. The authored authority survived the nested re-solves.
    let provenance = exec
        .proof_problem_assertion_provenance
        .as_ref()
        .expect("authored proof authority must not be lost");
    assert_eq!(
        provenance.original_problem_assertions, base,
        "a nested re-solve promoted its own working set to authored authority"
    );

    // 2. The mandatory gate accepts -- this is the exact call the SMT-LIB
    //    dispatcher makes, and the one that returned Unknown downstream.
    let published = exec.certify_unsat_for_publication(certified, &assumed);
    assert!(
        !published.is_unknown(),
        "mandatory certification rejected a correct refutation: {:?}",
        exec.unknown_reason()
    );

    // 3. The emitter's OWN proof passes the strict Alethe checker.
    let proof = exec
        .last_proof
        .clone()
        .expect("a certified UNSAT publishes its proof");
    ay_proof::check_proof_strict(&proof, &exec.ctx.terms)
        .expect("the emitted proof must pass strict Alethe checking");
}

const NESTED_ARRAY_DECLARATIONS: &str = r#"
    (set-logic QF_AX)
    (declare-const named_nested_a (Array Bool (Array Bool Bool)))
    (declare-const named_nested_b (Array Bool (Array Bool Bool)))
    (declare-const named_nested_irrelevant Bool)
    (declare-const user_irrelevant Bool)
"#;

const NAMED_NESTED_ARRAY_ASSERTIONS: [(&str, &str); 5] = [
    ("diseq", "(not (= named_nested_a named_nested_b))"),
    (
        "cell_00",
        "(= (select (select named_nested_a false) false) \
            (select (select named_nested_b false) false))",
    ),
    (
        "cell_01",
        "(= (select (select named_nested_a false) true) \
            (select (select named_nested_b false) true))",
    ),
    (
        "cell_10",
        "(= (select (select named_nested_a true) false) \
            (select (select named_nested_b true) false))",
    ),
    (
        "irrelevant",
        "(or named_nested_irrelevant (not named_nested_irrelevant))",
    ),
];

const UNNAMED_LAST_CELL_ASSERTION: &str = r#"
    (assert (= (select (select named_nested_a true) true)
               (select (select named_nested_b true) true)))
"#;

fn push_named_assertion(script: &mut String, name: &str, body: &str) {
    script.push_str(&format!("(assert (! {body} :named {name}))\n"));
}

fn execute_authored_script(script: &str) -> (Executor, Vec<String>) {
    let commands = ay_frontend::parse(script).expect("nested-array script must parse");
    let mut executor = Executor::new();
    let outputs = commands
        .iter()
        .filter_map(|command| {
            executor
                .execute_authored(command)
                .expect("authored command stream must execute")
        })
        .collect();
    (executor, outputs)
}

fn parse_core_names(core: &str) -> BTreeSet<String> {
    core.trim()
        .strip_prefix('(')
        .and_then(|contents| contents.strip_suffix(')'))
        .expect("get-unsat-core must return a flat list")
        .split_whitespace()
        .map(str::to_string)
        .collect()
}

/// Exercise the caller-authored text boundary, the named-to-assumption
/// redirect, core certification/minimization, the restored outer finite-array
/// quarantine, mandatory UNSAT admission, and `get-unsat-core` as one command
/// stream. The returned core is then reconstructed and solved on its own, so
/// membership authentication alone cannot hide a satisfiable printed core.
#[test]
fn authored_named_core_check_sat_assuming_publishes_sound_nested_array_core() {
    let mut query = format!("(set-option :produce-unsat-cores true)\n{NESTED_ARRAY_DECLARATIONS}");
    for (name, body) in NAMED_NESTED_ARRAY_ASSERTIONS {
        push_named_assertion(&mut query, name, body);
    }
    query.push_str(UNNAMED_LAST_CELL_ASSERTION);
    query.push_str("(check-sat-assuming (user_irrelevant))\n(get-unsat-core)\n");

    let (executor, outputs) = execute_authored_script(&query);
    assert_eq!(outputs.len(), 2, "unexpected text outputs: {outputs:?}");
    assert_eq!(
        outputs[0], "unsat",
        "the public text boundary must admit the exact nested-array refutation"
    );
    assert!(
        executor.last_command_unsat_was_independently_verified()
            || executor.last_command_unsat_was_strictly_verified(),
        "text UNSAT must consume a checked exact-query admission"
    );

    let core = parse_core_names(&outputs[1]);
    assert!(!core.is_empty(), "the named array core must not be empty");
    let offered: BTreeSet<String> = NAMED_NESTED_ARRAY_ASSERTIONS
        .iter()
        .map(|(name, _)| (*name).to_string())
        .chain(["user_irrelevant".to_string()])
        .collect();
    assert!(
        core.is_subset(&offered),
        "printed core escaped the named assertions/user literals: {core:?}"
    );

    // Rebuild precisely unnamed-base + printed named/user members. UNSAT here
    // is the semantic `get-unsat-core` contract; merely checking labels are
    // drawn from the original query would accept a wrong-but-authentic subset.
    let mut core_query = NESTED_ARRAY_DECLARATIONS.to_string();
    core_query.push_str(UNNAMED_LAST_CELL_ASSERTION);
    for (name, body) in NAMED_NESTED_ARRAY_ASSERTIONS {
        if core.contains(name) {
            core_query.push_str(&format!("(assert {body})\n"));
        }
    }
    if core.contains("user_irrelevant") {
        core_query.push_str("(assert user_irrelevant)\n");
    }
    core_query.push_str("(check-sat)\n");
    let (_core_executor, core_outputs) = execute_authored_script(&core_query);
    assert_eq!(
        core_outputs,
        ["unsat"],
        "the exact printed core is not a sound refutation: {}",
        outputs[1]
    );
}
