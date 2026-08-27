// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// Build a pure K_n matching CNF over dense edge variables: one positive ALO
/// per vertex and the complete negative AMO set for every incident-edge group.
fn matching_kn_clauses(n: usize) -> Vec<Vec<Literal>> {
    let mut ids = BTreeMap::new();
    let mut next = 0u32;
    let mut edge = |i: usize, j: usize| -> Variable {
        let key = (i.min(j), i.max(j));
        *ids.entry(key).or_insert_with(|| {
            let variable = Variable(next);
            next += 1;
            variable
        })
    };
    let mut clauses = Vec::new();
    for i in 0..n {
        clauses.push(
            (0..n)
                .filter(|&j| j != i)
                .map(|j| Literal::positive(edge(i, j)))
                .collect(),
        );
    }
    for i in 0..n {
        let incident: Vec<Variable> = (0..n).filter(|&j| j != i).map(|j| edge(i, j)).collect();
        for a in 0..incident.len() {
            for b in (a + 1)..incident.len() {
                clauses.push(vec![
                    Literal::negative(incident[a]),
                    Literal::negative(incident[b]),
                ]);
            }
        }
    }
    clauses
}

fn shared_edge_variable(groups: &[Vec<Literal>], a: usize, b: usize) -> Option<Variable> {
    let group_b = groups.get(b)?;
    groups
        .get(a)?
        .iter()
        .find(|literal| {
            group_b
                .iter()
                .any(|other| other.variable() == literal.variable())
        })
        .copied()
        .map(Literal::variable)
}

/// Preserve all degree and AMO counts while replacing two K_5 edges with
/// parallel copies. This is an odd regular multigraph, not a K_5 incidence.
fn matching_parallel_edge_fixture() -> Option<Vec<Vec<Literal>>> {
    let mut clauses = matching_kn_clauses(5);
    let x02 = shared_edge_variable(&clauses, 0, 2)?;
    let x13 = shared_edge_variable(&clauses, 1, 3)?;
    *clauses
        .get_mut(1)?
        .iter_mut()
        .find(|literal| literal.variable() == x13)? = Literal::positive(x02);
    *clauses
        .get_mut(2)?
        .iter_mut()
        .find(|literal| literal.variable() == x02)? = Literal::positive(x13);
    clauses.truncate(5);
    for group in clauses.clone() {
        for a in 0..group.len() {
            for b in (a + 1)..group.len() {
                clauses.push(vec![
                    Literal::negative(group[a].variable()),
                    Literal::negative(group[b].variable()),
                ]);
            }
        }
    }
    Some(clauses)
}

/// Task #17: recognise odd K_n, retain the expected aux-free SR chain, and
/// reject even, incomplete, or duplicate-AMO lookalikes.
#[test]
fn matching_aux_free_sr_recognises_odd_kn_and_rejects_near_misses() {
    let steps = detect_matching_aux_free_sr(&matching_kn_clauses(5));
    assert!(steps.is_some(), "K_5 matching incidence must be recognised");
    let Some(steps) = steps else { return };
    assert_eq!(steps.len(), 6);
    for step in &steps {
        let LexClause::Sr { clause, witness } = step;
        assert_eq!(clause.len(), 1);
        assert!(!witness.is_empty());
        assert_eq!(witness[0], clause[0], "witness must open with the pivot");
    }

    assert!(detect_matching_aux_free_sr(&matching_kn_clauses(6)).is_none());
    let mut incomplete = matching_kn_clauses(5);
    incomplete.pop();
    assert!(detect_matching_aux_free_sr(&incomplete).is_none());

    // The expected binary count cannot be forged with repeated valid AMOs.
    let mut duplicated = matching_kn_clauses(5);
    let repeated_binary = duplicated[5].clone();
    duplicated[5..].fill(repeated_binary);
    assert!(detect_matching_aux_free_sr(&duplicated).is_none());
}

/// Exact incidence is proof-authority: reject non-K_n endpoints and binaries
/// that do not belong to the unique complete within-group AMO set.
#[test]
fn matching_aux_free_sr_rejects_non_simple_incidence() {
    let parallel = matching_parallel_edge_fixture();
    assert!(
        parallel.is_some(),
        "parallel-edge fixture must be constructible"
    );
    let Some(parallel) = parallel else { return };
    assert!(detect_matching_aux_free_sr(&parallel).is_none());

    let mut stray = matching_kn_clauses(5);
    let v01 = shared_edge_variable(&stray, 0, 1);
    let v23 = shared_edge_variable(&stray, 2, 3);
    assert!(
        v01.is_some() && v23.is_some(),
        "K_5 edge fixtures must exist"
    );
    let (Some(v01), Some(v23)) = (v01, v23) else {
        return;
    };
    let last = stray.len() - 1;
    stray[last] = vec![Literal::negative(v01), Literal::negative(v23)];
    assert!(detect_matching_aux_free_sr(&stray).is_none());

    // An absent owner must fail closed, not panic at a map index.
    let mut unknown = matching_kn_clauses(5);
    let last = unknown.len() - 1;
    unknown[last] = vec![Literal::negative(v01), Literal::negative(Variable(10_000))];
    assert!(detect_matching_aux_free_sr(&unknown).is_none());
}
