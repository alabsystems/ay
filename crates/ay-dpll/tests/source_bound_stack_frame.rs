// Copyright 2026 Andrew Yates | Apache-2.0

//! Exact frame-memory proof requests and adversarial instruction mutations.
//! The largest input is the actual source-bound compiler obligation, including
//! both byte transfers, SP writeback and arbitrary memory outside the frame.
//! The other inputs separately locate missing derivations and require real
//! counterexamples for changed values, addresses and writeback.

use ay_dpll::Executor;
use ay_frontend::{command::Command, parse};

fn check(script: &str, expected: &str) {
    let mut commands = parse(script).expect("valid frame formula");
    // Keep the query itself exact; the library harness owns session lifetime.
    commands.retain(|command| !matches!(command, Command::Exit));
    let mut executor = Executor::new();
    executor.set_produce_proofs(true);
    let output = executor
        .execute_all(&commands)
        .expect("execute frame formula");
    assert_eq!(
        output,
        [expected],
        "frame result must survive mandatory certification"
    );
    if expected == "unsat" {
        let proof = executor.last_proof().expect("strict refutation retained");
        let quality = ay_proof::check_proof_strict(proof, executor.terms())
            .expect("frame refutation has no unverified steps");
        assert_eq!(quality.trust_count, 0);
        let command = parse("(get-proof)").unwrap();
        let proof = executor
            .execute_all(&command)
            .expect("export standard checked proof");
        let proof = proof.last().expect("exported proof text");
        assert!(
            !proof.starts_with("(error"),
            "proof export must succeed: {proof}"
        );
        assert!(!proof.contains(":rule trust"));
        assert!(!proof.contains(":rule hole"));
        println!(
            "STACK_PROOF_CERTIFICATE={}",
            serde_json::json!({
                "type": "alethe_certificate", "version": "1.0", "problem": script, "proof": proof
            })
        );
    }
}

macro_rules! case {
    ($name:ident, $file:literal, $expected:literal) => {
        #[test]
        fn $name() {
            check(
                include_str!(concat!(
                    "fixtures/source_bound_stack_frame/",
                    $file,
                    ".smt2"
                )),
                $expected,
            );
        }
    };
}

case!(
    source_bound_frame_refutation_is_exportable,
    "source-bound-frame",
    "unsat"
);
case!(
    both_registers_restore_from_arbitrary_memory,
    "positive-registers",
    "unsat"
);
case!(
    stack_pointer_writeback_has_a_checked_derivation,
    "positive-stack",
    "unsat"
);
case!(
    outside_frame_memory_is_preserved,
    "positive-memory",
    "unsat"
);
case!(
    complete_frame_state_has_a_checked_derivation,
    "positive-whole",
    "unsat"
);
case!(
    changed_second_saved_value_has_counterexample,
    "wrong-second-value",
    "sat"
);
case!(
    changed_second_load_address_has_counterexample,
    "wrong-second-load",
    "sat"
);
case!(
    changed_writeback_has_counterexample,
    "wrong-writeback",
    "sat"
);
case!(
    out_of_frame_store_has_counterexample,
    "out-of-frame-store",
    "sat"
);
