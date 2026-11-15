// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]
use super::*;

#[test]
fn equal_and_complemented_distinct_operands_preserve_original_semantics() {
    for case in 0..3 {
        let (mut terms, not_a, variables) = formula(CountedBuiltin::Not);
        let source = ample();
        let mut builder = CountedTermBuilder::new(&mut terms, &source).unwrap();
        let args = match case {
            0 => [variables[0], variables[0]],
            1 => [variables[0], not_a],
            _ => [not_a, not_a],
        };
        let root = builder.apply(CountedBuiltin::Distinct, &args).unwrap();
        builder.finish().unwrap();
        let cnf = CountedCnf::encode(&mut terms, &[root], &ample()).unwrap();
        exhaustive(&cnf, &variables);
    }
}

#[test]
fn preexisting_equality_negation_and_equivalence_share_bridge_without_lost_definitions() {
    let (mut terms, d, variables) = formula(CountedBuiltin::Distinct);
    let source = ample();
    let mut builder = CountedTermBuilder::new(&mut terms, &source).unwrap();
    let e = builder.apply(CountedBuiltin::Eq, &variables[..2]).unwrap();
    let n = builder.apply(CountedBuiltin::Not, &[e]).unwrap();
    let q = builder.apply(CountedBuiltin::Eq, &[d, n]).unwrap();
    let root = builder.apply(CountedBuiltin::And, &[q, d]).unwrap();
    builder.finish().unwrap();
    let original_len = terms.len();
    let original_terms: Vec<_> = (0..original_len)
        .map(|index| {
            let id = TermId(index as u32);
            (terms.get(id).clone(), terms.sort(id).clone())
        })
        .collect();
    let cnf = CountedCnf::encode(&mut terms, &[root], &ample()).unwrap();
    for (index, (term, sort)) in original_terms.iter().enumerate() {
        let id = TermId(index as u32);
        assert_eq!(cnf.terms.get(id), term);
        assert_eq!(cnf.terms.sort(id), sort);
    }
    assert!(cnf.terms.len() > original_len);
    assert!((original_len..cnf.terms.len())
        .all(|index| matches!(cnf.terms.get(TermId(index as u32)), TermData::Not(_))));
    assert_eq!(
        cnf.data.bridges[0],
        DistinctBridge {
            source: d,
            equality: e,
            negation: n,
            equivalence: q
        }
    );
    assert_eq!(
        cnf.data.term_literals[n.index()],
        cnf.data.term_literals[e.index()].map(|lit| -lit)
    );
    assert!(cnf.data.term_literals[q.index()].is_some());
    exhaustive(&cnf, &variables);
}

fn resolutions_valid(steps: &[Step]) -> bool {
    for (index, step) in steps.iter().enumerate() {
        if step.rule != AletheRule::Resolution {
            continue;
        }
        let (Some([a, b]), Some(pivot)) = (step.premises, step.pivot) else {
            return false;
        };
        if a >= index || b >= index {
            return false;
        }
        let positive = SourceLit::positive(pivot);
        let negative = positive.negated();
        let Some(left) = steps[a].clause.iter().position(|lit| *lit == positive) else {
            return false;
        };
        let Some(right) = steps[b].clause.iter().position(|lit| *lit == negative) else {
            return false;
        };
        let mut resolvent: Vec<_> = steps[a]
            .clause
            .iter()
            .enumerate()
            .filter(|(i, _)| *i != left)
            .chain(
                steps[b]
                    .clause
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| *i != right),
            )
            .map(|(_, lit)| *lit)
            .collect();
        let mut actual = step.clause.clone();
        resolvent.sort_by_key(|lit| (lit.term.0, lit.positive));
        actual.sort_by_key(|lit| (lit.term.0, lit.positive));
        if resolvent != actual {
            return false;
        }
    }
    true
}

#[test]
fn independent_resolution_replay_rejects_corrupt_premise_pivot_and_conclusion() {
    let (mut terms, root, _) = formula(CountedBuiltin::Distinct);
    let mut cnf = CountedCnf::encode(&mut terms, &[root], &ample()).unwrap();
    assert!(resolutions_valid(&cnf.data.steps));
    let index = cnf
        .data
        .steps
        .iter()
        .position(|step| step.rule == AletheRule::Resolution)
        .unwrap();
    let original = cnf.data.steps[index].premises;
    cnf.data.steps[index].premises = Some([index, index]);
    assert!(!resolutions_valid(&cnf.data.steps));
    cnf.data.steps[index].premises = original;
    cnf.data.steps[index].pivot = Some(root);
    assert!(!resolutions_valid(&cnf.data.steps));
    cnf.data.steps[index].pivot = Some(cnf.data.bridges[0].equivalence);
    cnf.data.steps[index].clause[0] = cnf.data.steps[index].clause[0].negated();
    assert!(!resolutions_valid(&cnf.data.steps));
}
