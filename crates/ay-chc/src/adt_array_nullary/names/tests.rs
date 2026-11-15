// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::ChcParser;
use std::collections::BTreeSet;
use std::time::Duration;

fn fixture() -> (ChcProblem, Vec<MarkerDagNode>, usize) {
    let problem = ChcParser::parse(
        r#"
        (set-logic HORN)
        (declare-datatype Unused ((|ay!nullary!1| (|ay!nullary!2| Bool))))
        (declare-fun |ay!nullary!3| (Bool) (_ BitVec 8))
        (declare-fun P (Bool) Bool)
        (assert (forall ((|ay!nullary!0| Bool))
          (=> (and |ay!nullary!0| (= (|ay!nullary!3| |ay!nullary!0|) #x00))
              (P |ay!nullary!0|))))
        (assert (forall ((q Bool)) (=> (P q) false)))
        (check-sat)
    "#,
    )
    .expect("collision source");
    let predicate = problem.clauses()[0].head.predicate_id().expect("head");
    let nodes = vec![MarkerDagNode {
        predicate,
        clause_idx: 0,
        children: Vec::new(),
    }];
    (problem, nodes, 1)
}

#[test]
fn source_variables_ufs_datatype_members_and_query_names_stay_disjoint() {
    let (problem, nodes, query) = fixture();
    let control = Control::capture(Duration::from_secs(5)).expect("owner");
    let names = Names::capture(&problem, &nodes, query, &control).expect("fresh plan");
    let generated: BTreeSet<_> = names
        .node(0)
        .expect("node")
        .values()
        .chain(names.query().values())
        .map(|expr| match expr {
            ChcExpr::Var(var) => var.name.as_str(),
            _ => unreachable!(),
        })
        .collect();
    assert_eq!(generated.len(), 2);
    for reserved in [
        "ay!nullary!0",
        "ay!nullary!1",
        "ay!nullary!2",
        "ay!nullary!3",
        "q",
        "P",
    ] {
        assert!(!generated.contains(reserved), "source capture: {reserved}");
    }
    assert!(generated.iter().all(|name| !name.starts_with("__ay_")));
}

#[test]
fn repeated_clause_instances_and_query_have_separate_stable_maps() {
    let (problem, mut nodes, query) = fixture();
    nodes.push(MarkerDagNode {
        predicate: nodes[0].predicate,
        clause_idx: 0,
        children: Vec::new(),
    });
    let control = Control::capture(Duration::from_secs(5)).expect("owner");
    let names = Names::capture(&problem, &nodes, query, &control).expect("fresh plan");
    let first = names.node(0).expect("first");
    assert_eq!(first, names.node(0).expect("same stored mapping"));
    assert_ne!(
        first.values().next(),
        names.node(1).expect("second").values().next()
    );
    assert_ne!(first.values().next(), names.query().values().next());
}

#[test]
fn generated_symbols_pass_real_frontend_declarations_and_check_sat() {
    let (problem, nodes, query) = fixture();
    let control = Control::capture(Duration::from_secs(5)).expect("owner");
    let _scope = control.enter();
    let names = Names::capture(&problem, &nodes, query, &control).expect("fresh plan");
    let vars = names
        .node(0)
        .expect("node")
        .values()
        .chain(names.query().values());
    let mut text = String::from(
        "(set-logic ALL)\n\
         (declare-const |ay!nullary!0| Bool)\n\
         (assert (not |ay!nullary!0|))\n\
         (declare-datatype Unused ((|ay!nullary!1| (|ay!nullary!2| Bool))))\n\
         (declare-fun |ay!nullary!3| (Bool) (_ BitVec 8))\n",
    );
    for expr in vars {
        let ChcExpr::Var(var) = expr else {
            unreachable!()
        };
        text.push_str(&format!(
            "(declare-const {} Bool)\n(assert {})\n",
            var.name, var.name
        ));
    }
    text.push_str("(check-sat)\n");
    let commands = ay_frontend::parse(&text).expect("generated text parses");
    let mut executor = crate::smt::executor_adapter::new_search_executor();
    executor.set_timeout(Some(Duration::from_secs(5)));
    assert_eq!(
        executor
            .execute_all(&commands)
            .expect("ordinary namespace elaborates"),
        vec!["sat"]
    );
}

#[test]
fn stopped_original_owner_cannot_mint_a_new_plan() {
    let (problem, nodes, query) = fixture();
    let control = Control::capture(Duration::from_secs(5)).expect("owner");
    assert!(control.refuse::<()>().is_none());
    assert!(Names::capture(&problem, &nodes, query, &control).is_none());
}
