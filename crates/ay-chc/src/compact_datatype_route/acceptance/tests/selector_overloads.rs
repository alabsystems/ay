// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::ground_derivation::compact::{validate_source, Error, Owner};
use crate::{AdaptiveConfig, AdaptivePortfolio, VerifiedChcResult};

fn overloaded_source(reachable: bool) -> ChcProblem {
    let guard = if reachable { "true" } else { "false" };
    ChcParser::parse(&format!(
        "(set-logic HORN)
         (declare-datatype Range ((range (start (_ BitVec 8)) (end (_ BitVec 8)))))
         (declare-datatype RangeFrom ((range_from (start (_ BitVec 8)))))
         (declare-rel error ())
         (rule (=> {guard} error))
         (query error)"
    ))
    .expect("the parser deliberately accepts cross-datatype selector overloads")
}

#[test]
fn selector_overloads_validate_and_replay_by_domain() {
    let problem = overloaded_source(true);
    assert_eq!(
        validate_source(&problem, &mut Owner::capture().expect("owner")),
        Ok(())
    );
    let Some(ChcEngineResult::Unsafe(candidate)) = run(&problem, None, None, None) else {
        panic!("the original reachable error needs an independently replayable candidate");
    };
    assert!(candidate
        .ground_checks_unsafe(&problem)
        .expect("original replay"));
}

#[test]
fn selector_overloads_preserve_strict_safe_and_unsafe_results() {
    for reachable in [false, true] {
        let mut config = AdaptiveConfig::with_budget(Duration::from_secs(5), false);
        config.strict_proofs = true;
        let result = AdaptivePortfolio::new(overloaded_source(reachable), config).solve();
        assert!(
            matches!(
                (&result, reachable),
                (VerifiedChcResult::Safe(_), false) | (VerifiedChcResult::Unsafe(_), true)
            ),
            "reachable={reachable}: {result:?}"
        );
    }
}

#[test]
fn selector_overloads_do_not_bypass_cancellation() {
    let cancellation = crate::CancellationToken::new();
    cancellation.cancel();
    assert!(matches!(
        run(&overloaded_source(true), None, Some(&cancellation), None),
        Some(ChcEngineResult::Unknown)
    ));
}

#[test]
fn selector_overloads_do_not_bypass_original_resource_limit() {
    let guard = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(0)));
    let _scope = guard.enter();
    assert!(matches!(
        run(&overloaded_source(true), None, None, None),
        Some(ChcEngineResult::Unknown)
    ));
}

#[test]
fn selector_overloads_do_not_legalize_duplicate_fields_in_one_datatype() {
    let problem = ChcParser::parse(
        "(set-logic HORN)
         (declare-datatype Pair ((pair (value Bool) (value Bool))))
         (declare-rel error ()) (rule error) (query error)",
    )
    .expect("retain duplicate declarations for source validation");
    assert_eq!(
        validate_source(&problem, &mut Owner::capture().expect("owner")),
        Err(Error::InvalidSource)
    );
    assert!(matches!(
        run(&problem, None, None, None),
        Some(ChcEngineResult::Unknown)
    ));
}

#[test]
fn selector_overloads_do_not_legalize_constructor_collisions() {
    let problem = ChcParser::parse(
        "(set-logic HORN)
         (declare-datatype A ((a (value Bool))))
         (declare-datatype B ((value (other Bool))))
         (declare-rel error ()) (rule error) (query error)",
    )
    .expect("retain constructor collisions for source validation");
    assert_eq!(
        validate_source(&problem, &mut Owner::capture().expect("owner")),
        Err(Error::InvalidSource)
    );
    assert!(matches!(
        run(&problem, None, None, None),
        Some(ChcEngineResult::Unknown)
    ));
}

fn mixed_declarations(index: usize, malformed: &str) -> ChcProblem {
    ChcParser::parse(&format!(
        "(set-logic HORN)
         (declare-datatype A{index} ((a{index} (shared Bool))))
         (declare-datatype B{index} ((b{index} (shared Bool))))
         (declare-datatype C{index} ({malformed}))
         (declare-rel error ()) (rule error) (query error)"
    ))
    .expect("parser retains datatype declarations for source admission")
}

#[test]
fn selector_overloads_do_not_hide_later_duplicate_fields() {
    // Definitions are hash-indexed: cover different iteration orders so a
    // legitimate overload cannot skip an invalid declaration visited later.
    for index in 0..32 {
        let problem = mixed_declarations(index, "(bad (duplicate Bool) (duplicate Bool))");
        assert_eq!(
            validate_source(&problem, &mut Owner::capture().expect("owner")),
            Err(Error::InvalidSource),
            "declaration-name permutation {index}"
        );
        assert!(matches!(
            run(&problem, None, None, None),
            Some(ChcEngineResult::Unknown)
        ));
    }
}

#[test]
fn selector_overloads_do_not_hide_later_constructor_collisions() {
    for index in 0..32 {
        let problem = mixed_declarations(index, "(shared (other Bool))");
        assert_eq!(
            validate_source(&problem, &mut Owner::capture().expect("owner")),
            Err(Error::InvalidSource),
            "declaration-name permutation {index}"
        );
        assert!(matches!(
            run(&problem, None, None, None),
            Some(ChcEngineResult::Unknown)
        ));
    }
}

fn typed_selector_source(reachable: bool) -> ChcProblem {
    let expected = if reachable { "#x0103" } else { "#x0102" };
    ChcParser::parse(&format!(
        "(set-logic HORN)
         (declare-datatype A ((a (shared (_ BitVec 8)) (a_other Bool))))
         (declare-datatype B ((b (b_other (_ BitVec 16)) (shared Bool))))
         (declare-datatype C ((c (c_left Bool) (c_middle (_ BitVec 8)) (shared (_ BitVec 16)))))
         (declare-var x A) (declare-var y B) (declare-var z C)
         (declare-rel P (A B C)) (declare-rel error ())
         (rule (=> (and (= (shared x) #x05) (= (shared y) false)
                        (= (shared z) #x0102)) (P x y z)))
         (rule (=> (and (P x y z)
                        (not (and (= (shared x) #x05) (= (shared y) false)
                                  (= (shared z) {expected})))) error))
         (query error)"
    ))
    .expect("selectors resolve from their distinct argument datatype")
}

#[test]
fn selector_overloads_read_the_correct_field_index_and_result_sort() {
    let problem = typed_selector_source(true);
    assert_eq!(
        validate_source(&problem, &mut Owner::capture().expect("owner")),
        Ok(())
    );
    let Some(ChcEngineResult::Unsafe(candidate)) = run(&problem, None, None, None) else {
        panic!("different owners, indices and result sorts still yield the real error");
    };
    assert!(candidate
        .ground_checks_unsafe(&problem)
        .expect("typed original replay"));
}

#[test]
fn selector_overloads_never_refute_the_matching_values() {
    let problem = typed_selector_source(false);
    assert_eq!(
        validate_source(&problem, &mut Owner::capture().expect("owner")),
        Ok(())
    );
    assert!(run(&problem, None, None, None).is_none());
}

fn ite_selector_source(selected: &str, expected: &str) -> ChcProblem {
    ChcParser::parse(&format!(
        "(set-logic HORN)
         (declare-datatype A ((a (shared (_ BitVec 8)))))
         (declare-datatype B ((b (shared (_ BitVec 8)))))
         (declare-var x A) (declare-var y A) (declare-var choose Bool)
         (declare-rel P (A A Bool)) (declare-rel error ())
         (rule (=> (and (= (shared x) #x05) (= (shared y) #x09)
                        (= choose false)) (P x y choose)))
         (rule (=> (and (P x y choose)
                        (not (and (= (shared {selected}) {expected})
                                  (= (shared x) #x05) (= choose false)))) error))
         (query error)"
    ))
    .expect("the conditional selector has one authenticated datatype domain")
}

#[test]
fn selector_overloads_replay_the_selected_datatype_ite_arm() {
    use crate::ground_derivation::compact::validate;

    let plain = ite_selector_source("y", "#x05");
    let derivation =
        crate::compact_datatype_route::derive(&plain, &mut Owner::capture().expect("owner"))
            .expect("plain projection")
            .expect("real error with the selected value nine");
    let original = ite_selector_source("(ite choose x y)", "#x05");
    assert_eq!(
        validate_source(&original, &mut Owner::capture().expect("owner")),
        Ok(())
    );
    assert_eq!(
        validate(
            &original,
            &derivation,
            &mut Owner::capture().expect("owner")
        ),
        Ok(())
    );

    // Following the source then-arm establishes only the common type: the
    // concrete value must still come from the selected else-arm.
    let safe = ite_selector_source("(ite choose x y)", "#x09");
    assert_eq!(
        validate_source(&safe, &mut Owner::capture().expect("owner")),
        Ok(())
    );
    assert_eq!(
        validate(&safe, &derivation, &mut Owner::capture().expect("owner")),
        Err(Error::InvalidDerivation)
    );
}

#[test]
fn selector_overloads_typecheck_both_datatype_ite_arms() {
    fn corrupt_else(expr: &mut crate::ChcExpr) -> bool {
        match expr {
            crate::ChcExpr::Op(crate::ChcOp::Ite, args) => {
                args[2] = Arc::new(crate::ChcExpr::Bool(false));
                true
            }
            crate::ChcExpr::Op(_, args) | crate::ChcExpr::FuncApp(_, _, args) => {
                args.iter_mut().any(|arg| corrupt_else(Arc::make_mut(arg)))
            }
            _ => false,
        }
    }
    let mut problem = ite_selector_source("(ite choose x y)", "#x05");
    assert_eq!(
        validate_source(&problem, &mut Owner::capture().expect("owner")),
        Ok(())
    );
    assert!(problem
        .clauses_mut()
        .iter_mut()
        .any(|clause| { clause.body.constraint.as_mut().is_some_and(corrupt_else) }));
    assert_eq!(
        validate_source(&problem, &mut Owner::capture().expect("owner")),
        Err(Error::InvalidSource)
    );
}

#[test]
fn selector_overloads_reject_a_candidate_with_another_datatype_owner() {
    use crate::ground_derivation::compact::{validate, ValueId, ValueNode};

    let problem = typed_selector_source(true);
    let mut derivation =
        crate::compact_datatype_route::derive(&problem, &mut Owner::capture().expect("owner"))
            .expect("typed projection")
            .expect("real error");
    assert_eq!(
        validate(&problem, &derivation, &mut Owner::capture().expect("owner")),
        Ok(())
    );
    let other = derivation
        .arena
        .nodes()
        .iter()
        .enumerate()
        .find_map(|(index, node)| {
            matches!(node, ValueNode::Datatype { sort, .. } if sort == "B")
                .then_some(ValueId(u32::try_from(index).expect("small test arena")))
        })
        .expect("complete other-owner value");
    let mut changed = false;
    for step in &mut derivation.steps {
        for value in step.env.values_mut() {
            if matches!(derivation.arena.get(*value), Some(ValueNode::Datatype { sort, .. }) if sort == "A")
            {
                *value = other;
                changed = true;
                break;
            }
        }
        if changed {
            break;
        }
    }
    assert!(changed, "mutate an actual A binding, not an unused node");
    assert_eq!(
        validate(&problem, &derivation, &mut Owner::capture().expect("owner")),
        Err(Error::InvalidValue)
    );
}
