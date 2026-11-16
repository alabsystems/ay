// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
#![cfg(test)]

use super::*;

fn operation(store: &mut TermStore, name: &str, a: TermId, b: TermId) -> TermId {
    match name {
        "bvadd" => store.mk_bvadd(vec![a, b]),
        "bvmul" => store.mk_bvmul(vec![a, b]),
        "bvudiv" => store.mk_bvudiv(vec![a, b]),
        "bvurem" => store.mk_bvurem(vec![a, b]),
        _ => unreachable!("test operation"),
    }
}

fn check_equivalences(clauses: &[CnfClause], placeholders: &[CnfLit]) {
    let suffix = &clauses[clauses.len() - 2 * placeholders.len()..];
    let (pairs, remainder) = suffix.as_chunks::<2>();
    assert_eq!(remainder, &[] as &[CnfClause]);
    for (&placeholder, pair) in placeholders.iter().zip(pairs) {
        let forward = pair[0].literals();
        assert_eq!(forward.len(), 2);
        assert_eq!(forward[0], -placeholder);
        let circuit_bit = forward[1];
        assert_ne!(circuit_bit.unsigned_abs(), placeholder.unsigned_abs());
        assert_eq!(pair[1].literals(), &[placeholder, -circuit_bit]);
    }
}

fn check_values(
    solver: &BvSolver<'_>,
    a: &[CnfLit],
    b: &[CnfLit],
    placeholders: &[CnfLit],
    name: &str,
) {
    let mask = (1_u64 << placeholders.len()) - 1;
    let high = 1_u64 << (placeholders.len() - 1);
    let circuit = Circuit::from_clauses(solver.num_vars(), solver.clauses());
    for (av, bv) in [
        (0, 0),
        (mask, 0),
        (mask, 1),
        (mask, 3),
        (high + 19, high + 1),
        (high - 1, high),
    ] {
        let fixes = [fix_word(a, av), fix_word(b, bv)].concat();
        let model = circuit.propagate(&fixes);
        let expected = match name {
            "bvadd" => av.wrapping_add(bv) & mask,
            "bvmul" => av.wrapping_mul(bv) & mask,
            "bvudiv" => av.checked_div(bv).unwrap_or(mask),
            "bvurem" => av.checked_rem(bv).unwrap_or(av),
            _ => unreachable!("test operation"),
        };
        assert_eq!(
            word_value(&model, placeholders),
            expected,
            "{name} {av}/{bv}"
        );
    }
}

#[test]
fn delayed_snapshots_constrain_original_placeholders_after_full_circuit_restoration() {
    // Addition needs 2*width > 64; the other operations need width > 12.
    for (name, width) in [("bvadd", 33), ("bvmul", 13), ("bvudiv", 13), ("bvurem", 13)] {
        let mut store = setup_store();
        let x = store.mk_var("delayed_x", Sort::bitvec(width));
        let y = store.mk_var("delayed_y", Sort::bitvec(width));
        let term = operation(&mut store, name, x, y);
        let mut original = BvSolver::new(&store);
        original.set_delay_enabled(true);
        let placeholders = original.ensure_term_bits(term).expect("BV output");
        assert_eq!(placeholders.len(), width as usize);
        assert_eq!(original.delayed_ops().len(), 1);
        assert!(original.has_unresolved_delayed_ops());
        // Only distinct variable operands and unconstrained result bits exist.
        assert_eq!(original.num_vars(), 3 * width);
        assert_eq!(original.clauses(), &[] as &[CnfClause]);
        let snapshot = original
            .take_delayed_state()
            .expect("actual delayed snapshot");
        assert!(snapshot.has_unresolved());
        assert_eq!(snapshot.delayed_ops()[0].term, term);
        assert_eq!(snapshot.delayed_ops()[0].op, name);
        assert_eq!(snapshot.delayed_ops()[0].result_bits, placeholders);
        let a = snapshot.term_to_bits()[&x].clone();
        let b = snapshot.term_to_bits()[&y].clone();
        let next_var = original.num_vars() + 1;
        drop(original);

        let mut restored = BvSolver::new(&store);
        restored.enable_gate_provenance();
        restored.set_term_to_bits(snapshot.term_to_bits().clone());
        restored.set_delayed_ops(snapshot.delayed_ops().to_vec());
        restored.set_next_var(next_var);
        drop(snapshot);
        let clauses = restored.build_delayed_circuit(0);
        assert!(!restored.has_unresolved_delayed_ops());
        assert!(restored.take_delayed_state().is_none());
        // The public API returns, not retains, CNF.
        assert_eq!(restored.clauses(), &[] as &[CnfClause]);
        assert!(
            !restored.mux_children().is_empty(),
            "{name} must build real gates"
        );
        assert!(clauses.len() > 2 * width as usize);
        check_equivalences(&clauses, &placeholders);
        // Reload the returned clauses exactly as a downstream consumer must.
        for clause in clauses {
            restored.add_clause(clause);
        }
        check_values(&restored, &a, &b, &placeholders, name);
    }
}
