// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]
use super::*;

#[test]
fn all_boolean_gates_have_full_bidirectional_semantics() {
    for op in [
        CountedBuiltin::Not,
        CountedBuiltin::And,
        CountedBuiltin::Or,
        CountedBuiltin::Implies,
        CountedBuiltin::Xor,
        CountedBuiltin::Eq,
        CountedBuiltin::Iff,
        CountedBuiltin::Distinct,
        CountedBuiltin::Ite,
    ] {
        let (mut terms, root, variables) = formula(op);
        let original = ample();
        let cnf = CountedCnf::encode(&mut terms, &[root], &original).unwrap();
        exhaustive(&cnf, &variables);
        cnf.finish().unwrap();
    }
}

#[test]
fn negated_outputs_and_nested_ite_equalities_do_not_get_one_way_definitions() {
    let (mut terms, ite, variables) = formula(CountedBuiltin::Ite);
    let source = ample();
    let mut builder = CountedTermBuilder::new(&mut terms, &source).unwrap();
    let eq = builder
        .apply(CountedBuiltin::Eq, &[ite, variables[1]])
        .unwrap();
    let root = builder.apply(CountedBuiltin::Not, &[eq]).unwrap();
    builder.finish().unwrap();
    let cnf = CountedCnf::encode(&mut terms, &[root], &ample()).unwrap();
    exhaustive(&cnf, &variables);
}

#[test]
fn constants_and_raw_double_negations_keep_source_literal_identities() {
    let (mut terms, not_a, variables) = formula(CountedBuiltin::Not);
    let source = ample();
    let mut builder = CountedTermBuilder::new(&mut terms, &source).unwrap();
    let nn = builder.apply(CountedBuiltin::Not, &[not_a]).unwrap();
    let yes = builder.boolean(true).unwrap();
    let root = builder.apply(CountedBuiltin::Eq, &[nn, yes]).unwrap();
    builder.finish().unwrap();
    let cnf = CountedCnf::encode(&mut terms, &[root], &ample()).unwrap();
    exhaustive(&cnf, &variables);
    assert_eq!(
        cnf.data.term_literals[nn.index()],
        cnf.data.term_literals[variables[0].index()]
    );
    assert!(cnf
        .data
        .steps
        .iter()
        .any(|step| step.clause.iter().any(|lit| lit.term == nn)));
}

#[test]
fn distinct_has_five_exact_bridge_steps_and_no_xor_label() {
    let (mut terms, root, variables) = formula(CountedBuiltin::Distinct);
    let cnf = CountedCnf::encode(&mut terms, &[root], &ample()).unwrap();
    exhaustive(&cnf, &variables);
    let bridge = cnf.data.bridges[0];
    assert_eq!(
        cnf.terms.get(bridge.equality),
        &TermData::App(Symbol::named("="), variables[..2].to_vec())
    );
    assert_eq!(
        cnf.terms.get(bridge.negation),
        &TermData::Not(bridge.equality)
    );
    assert_eq!(
        cnf.terms.get(bridge.equivalence),
        &TermData::App(Symbol::named("="), vec![root, bridge.negation])
    );
    let index = cnf
        .data
        .steps
        .iter()
        .position(|step| step.rule == AletheRule::DistinctElim)
        .unwrap();
    let q = SourceLit::positive(bridge.equivalence);
    assert_eq!(cnf.data.steps[index].clause, [q]);
    assert_eq!(cnf.data.steps[index + 1].rule, AletheRule::EquivPos1);
    assert_eq!(
        cnf.data.steps[index + 1].clause,
        [
            q.negated(),
            SourceLit::positive(root),
            SourceLit::positive(bridge.equality)
        ]
    );
    assert_eq!(cnf.data.steps[index + 2].rule, AletheRule::EquivPos2);
    assert_eq!(
        cnf.data.steps[index + 2].clause,
        [
            q.negated(),
            SourceLit::positive(root).negated(),
            SourceLit::positive(bridge.negation)
        ]
    );
    for (offset, premise) in [(3, 1), (4, 2)] {
        let step = &cnf.data.steps[index + offset];
        assert_eq!(step.rule, AletheRule::Resolution);
        assert_eq!(step.premises, Some([index, index + premise]));
        assert_eq!(step.pivot, Some(bridge.equivalence));
    }
    assert!(cnf.data.steps.iter().all(|step| !matches!(
        step.rule,
        AletheRule::XorPos1 | AletheRule::XorPos2 | AletheRule::XorNeg1 | AletheRule::XorNeg2
    )));
    assert!(cnf.data.rows.iter().all(|row| match row.justification {
        Justification::Root(id) => id == root,
        Justification::Step(step) => step < cnf.data.steps.len(),
    }));
}

#[test]
fn repeated_distinct_and_shared_equalities_are_encoded_once() {
    let (mut terms, distinct, variables) = formula(CountedBuiltin::Distinct);
    let source = ample();
    let mut builder = CountedTermBuilder::new(&mut terms, &source).unwrap();
    let eq = builder.apply(CountedBuiltin::Eq, &variables[..2]).unwrap();
    let root = builder
        .apply(CountedBuiltin::Or, &[eq, distinct, distinct])
        .unwrap();
    builder.finish().unwrap();
    let cnf = CountedCnf::encode(&mut terms, &[root, root], &ample()).unwrap();
    exhaustive(&cnf, &variables);
    assert_eq!(cnf.data.bridges.len(), 1);
    assert_eq!(cnf.data.bridges[0].equality, eq);
    assert_eq!(
        cnf.data
            .rows
            .iter()
            .filter(|row| matches!(row.justification, Justification::Root(_)))
            .count(),
        2
    );
}

#[test]
fn wide_original_root_has_no_131072_node_or_arity_gate() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let root = terms.mk_app(Symbol::named("and"), vec![a; 131_073], Sort::Bool);
    let cnf = CountedCnf::encode(&mut terms, &[root], &ample()).unwrap();
    assert_eq!(cnf.data.num_vars, 2);
    assert_eq!(cnf.data.rows.len(), 131_075);
    assert_eq!(cnf.data.steps.last().unwrap().clause.len(), 131_074);
}

#[test]
fn shared_implication_chain_stays_linear_in_original_dag() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let mut root = a;
    for _ in 0..96 {
        root = terms.mk_app(Symbol::named("=>"), [root, root], Sort::Bool);
    }
    let original = ample();
    let cnf = CountedCnf::encode(&mut terms, &[root], &original).unwrap();
    assert_eq!(cnf.data.num_vars, 97);
    assert_eq!(cnf.data.rows.len(), 289);
    assert!(original.usage().unwrap().work_admitted < 100_000);
}

#[test]
fn empty_and_singleton_native_connectives_keep_exact_tautology_rules() {
    for name in ["and", "or"] {
        for count in 0..=1 {
            let mut terms = TermStore::new();
            let a = terms.mk_var("a", Sort::Bool);
            let root = terms.mk_app(Symbol::named(name), vec![a; count], Sort::Bool);
            let cnf = CountedCnf::encode(&mut terms, &[root], &ample()).unwrap();
            exhaustive(&cnf, &[a]);
            assert!(cnf.data.steps.iter().all(|step| step.source == root));
        }
    }
}
