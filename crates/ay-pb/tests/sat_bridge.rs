// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! PB-to-SAT bridge integration tests.

use ay_pb::{parse_opb, verify_all_constraints, CnfEncoder};
use ay_sat::SatResult;

fn original_assignment(model: &[bool], num_pb_vars: u32) -> Vec<bool> {
    (0..num_pb_vars as usize)
        .map(|idx| model.get(idx).copied().unwrap_or(false))
        .collect()
}

#[test]
fn test_encoded_pb_sat_bridge_model_satisfies_original_weighted_constraints() {
    let instance = parse_opb(
        "* #variable= 4 #constraint= 3\n\
         +2 x1 +3 x2 +1 ~x3 +4 x4 >= 6 ;\n\
         +1 ~x1 +1 x3 +1 x4 >= 1 ;\n\
         +1 x1 +1 x2 +1 x3 +1 x4 >= 2 ;\n",
    )
    .expect("weighted OPB should parse");

    let encoded = CnfEncoder::encode_instance(&instance);
    let mut solver = encoded.to_sat_solver();

    match solver.solve().into_inner() {
        SatResult::Sat(model) => {
            let assignment = original_assignment(&model, instance.num_vars);
            assert!(
                verify_all_constraints(&instance.constraints, &assignment),
                "SAT-level model must satisfy original PB constraints: {assignment:?}"
            );
        }
        other => panic!("expected encoded PB formula to be SAT, got {other:?}"),
    }
}

#[test]
fn test_encoded_pb_sat_bridge_reports_unsat_for_contradictory_cardinality() {
    let instance = parse_opb(
        "* #variable= 2 #constraint= 2\n\
         +1 x1 +1 x2 >= 2 ;\n\
         +1 ~x1 +1 ~x2 >= 1 ;\n",
    )
    .expect("contradictory cardinality OPB should parse");

    let encoded = CnfEncoder::encode_instance(&instance);
    let mut solver = encoded.to_sat_solver();
    let result = solver.solve().into_inner();

    assert!(
        result.is_unsat(),
        "expected encoded contradictory PB constraints to be UNSAT, got {result:?}"
    );
}

#[test]
fn test_encoded_pb_sat_bridge_interrupts_during_import() {
    let instance = parse_opb(
        "* #variable= 4 #constraint= 4\n\
         +1 x1 +1 x2 >= 1 ;\n\
         +1 x2 +1 x3 >= 1 ;\n\
         +1 x3 +1 x4 >= 1 ;\n\
         +1 x1 +1 x4 >= 1 ;\n",
    )
    .expect("OPB should parse");

    let encoded = CnfEncoder::encode_instance(&instance);
    let mut polls = 0usize;
    let mut should_stop = || {
        polls += 1;
        polls > 1
    };

    assert!(
        encoded
            .to_sat_solver_interruptible(1, &mut should_stop)
            .is_none(),
        "import should fail closed when interruption is requested"
    );
}
