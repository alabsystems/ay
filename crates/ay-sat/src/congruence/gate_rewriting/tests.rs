// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::union_find::UnionFind;
use super::super::CongruenceClosure;
use super::{GateSignature, GateTable};
use crate::clause_arena::ClauseArena;
use crate::gates::GateType;
use crate::literal::{Literal, Variable};
use crate::test_util::lit;
use smallvec::SmallVec;

fn add_xnor3_gate(clauses: &mut ClauseArena, output_var: usize, input_vars: [usize; 3]) {
    let output_var = u32::try_from(output_var).expect("test output var fits in u32");
    let [x0, x1, x2] = input_vars
        .map(|input_var| u32::try_from(input_var).expect("test XOR input var fits in u32"));
    let clause_patterns = [
        [
            lit(output_var, true),
            lit(x0, true),
            lit(x1, true),
            lit(x2, true),
        ],
        [
            lit(output_var, true),
            lit(x0, true),
            lit(x1, false),
            lit(x2, false),
        ],
        [
            lit(output_var, true),
            lit(x0, false),
            lit(x1, true),
            lit(x2, false),
        ],
        [
            lit(output_var, true),
            lit(x0, false),
            lit(x1, false),
            lit(x2, true),
        ],
        [
            lit(output_var, false),
            lit(x0, true),
            lit(x1, true),
            lit(x2, false),
        ],
        [
            lit(output_var, false),
            lit(x0, true),
            lit(x1, false),
            lit(x2, true),
        ],
        [
            lit(output_var, false),
            lit(x0, false),
            lit(x1, true),
            lit(x2, true),
        ],
        [
            lit(output_var, false),
            lit(x0, false),
            lit(x1, false),
            lit(x2, false),
        ],
    ];
    for clause in clause_patterns {
        clauses.add(&clause, false);
    }
}

fn add_equivalence(clauses: &mut ClauseArena, lhs_var: usize, rhs_var: usize) {
    let lhs_var = u32::try_from(lhs_var).expect("test lhs var fits in u32");
    let rhs_var = u32::try_from(rhs_var).expect("test rhs var fits in u32");
    clauses.add(&[lit(lhs_var, false), lit(rhs_var, true)], false);
    clauses.add(&[lit(lhs_var, true), lit(rhs_var, false)], false);
}

fn add_negated_equivalence(clauses: &mut ClauseArena, lhs_var: usize, rhs_var: usize) {
    let lhs_var = u32::try_from(lhs_var).expect("test lhs var fits in u32");
    let rhs_var = u32::try_from(rhs_var).expect("test rhs var fits in u32");
    clauses.add(&[lit(lhs_var, false), lit(rhs_var, false)], false);
    clauses.add(&[lit(lhs_var, true), lit(rhs_var, true)], false);
}

fn edge_connects(edges: &[(Literal, Literal)], lhs: Literal, rhs: Literal) -> bool {
    edges.iter().any(|&(a, b)| {
        (a == lhs && b == rhs)
            || (a == rhs && b == lhs)
            || (a == lhs.negated() && b == rhs.negated())
            || (a == rhs.negated() && b == lhs.negated())
    })
}

/// Machine-checked-parity tie-in: the REAL `reduce_xor_input_pairs` accumulates
/// exactly the GF(2) popcount-parity of its complementary-pair cancellations,
/// matching the deductive-checks-discharged `xor_collapse_parity_verified` invariant
/// (the development proof harness).
///
/// This is the differential test that ties the machine-checked parity FUNCTION
/// to the actual runtime function: for every fully-collapsing XOR input multiset
/// of arity 0..=5 (built from duplicate pairs `{x,x}` and complementary pairs
/// `{x,¬x}` over distinct variables), the imperative `parity_flip` produced by
/// the real reducer equals `(#complementary-pairs) % 2 == 1` — exactly the
/// popcount-parity proven exact and order-independent in `ay-sat-verified`.
#[test]
fn reduce_xor_input_pairs_parity_matches_machine_checked_popcount() {
    // popcount-parity reference (mirrors the deductive-checks ground truth).
    fn popcount_parity_is_odd(n: usize) -> bool {
        n % 2 == 1
    }

    // Enumerate (#dup-pairs d, #comp-pairs p) with total arity 2*(d+p) <= ~5.
    for d in 0usize..=2 {
        for p in 0usize..=2 {
            if 2 * (d + p) > 6 {
                continue;
            }
            // Build the post-find literal multiset over DISTINCT variables so
            // the sort/pair logic is genuinely exercised (no accidental
            // cancellation across groups). Dup pairs use vars 0.., comp pairs
            // use vars 100.. .
            let mut inputs: SmallVec<[usize; 5]> = SmallVec::new();
            for j in 0..d {
                let pos = 2 * j; // positive literal index of var j
                inputs.push(pos);
                inputs.push(pos);
            }
            for j in 0..p {
                let var = 100 + j;
                let pos = 2 * var;
                let neg = pos ^ 1;
                inputs.push(pos);
                inputs.push(neg);
            }

            // Identity union-find sized to cover the largest literal index.
            let max_lit = inputs.iter().copied().max().unwrap_or(0);
            let mut uf = UnionFind::new(max_lit + 2);

            let mut parity_flip = false;
            CongruenceClosure::reduce_xor_input_pairs(&mut inputs, &mut uf, &mut parity_flip);

            assert!(
                inputs.is_empty(),
                "fully-collapsing multiset must reduce to arity 0 (d={d}, p={p}), got {inputs:?}"
            );
            assert_eq!(
                parity_flip,
                popcount_parity_is_odd(p),
                "real reduce_xor_input_pairs parity must equal GF(2) popcount of \
                 complementary pairs (d={d}, p={p})"
            );

            // Close the loop to the SHARED, trust-checked parity core: the real
            // reducer's accumulated bit equals `xor_collapse_parity` (the exact
            // function targo verifies) fed the same `p` complementary-pair
            // contributions. Same source the solver runs — no twin.
            let mut slots = [false; 5];
            for slot in slots.iter_mut().take(p) {
                *slot = true;
            }
            assert_eq!(
                parity_flip,
                ay_sat_congruence_core::xor_collapse_parity(
                    false, slots[0], slots[1], slots[2], slots[3], slots[4],
                ),
                "real reducer parity must equal the trust-checked xor_collapse_parity (d={d}, p={p})"
            );
        }
    }
}

#[test]
fn test_xnor_complementary_inputs_collapse_to_negative_unit() {
    let mut clauses = ClauseArena::new();

    clauses.add(&[lit(0, true), lit(1, true), lit(2, true)], false);
    clauses.add(&[lit(0, true), lit(1, false), lit(2, false)], false);
    clauses.add(&[lit(0, false), lit(1, false), lit(2, true)], false);
    clauses.add(&[lit(0, false), lit(1, true), lit(2, false)], false);

    add_negated_equivalence(&mut clauses, 1, 2);

    let mut cc = CongruenceClosure::new(3);
    let result = cc.run(&mut clauses, None, &[]);

    assert!(
        !result.is_unsat,
        "x ≡ ¬y with XNOR(x, y) is satisfiable and should force only ¬z"
    );
    assert!(
        result.units.contains(&lit(0, false)),
        "XNOR(x, y) with x ≡ ¬y must force ¬z, got units {:?} and edges {:?}",
        result.units,
        result.equivalence_edges
    );
    // #7137-relax: the forced ¬z is a full XOR-collapse (arity-0) unit, so its
    // polarity is the machine-checked-exact parity — it must be reported in the
    // parity-certified channel that the default-off --sat-congruence-parity-trust
    // consumer accepts without post-hoc RUP.
    assert!(
        result.parity_certified_units.contains(&lit(0, false)),
        "XOR-collapse unit ¬z must be parity-certified, got {:?}",
        result.parity_certified_units
    );
    assert!(
        !result.units.contains(&lit(0, true)),
        "XNOR(x, y) with x ≡ ¬y must not force z"
    );
}

#[test]
fn test_xnor_duplicate_pair_reorders_after_uf_canonicalization() {
    let mut clauses = ClauseArena::new();
    add_xnor3_gate(&mut clauses, 0, [1, 2, 3]);
    add_equivalence(&mut clauses, 1, 4);
    add_equivalence(&mut clauses, 3, 4);

    let mut cc = CongruenceClosure::new(5);
    let result = cc.run(&mut clauses, None, &[]);

    let y_pos = Literal::positive(Variable(0));
    let b_pos = Literal::positive(Variable(2));
    let b_neg = Literal::negative(Variable(2));
    assert!(
        edge_connects(&result.equivalence_edges, y_pos, b_neg),
        "XNOR(t, b, t) must collapse to y ≡ ¬b, got edges {:?}",
        result.equivalence_edges
    );
    assert!(
        !edge_connects(&result.equivalence_edges, y_pos, b_pos),
        "XNOR(t, b, t) must not collapse to y ≡ b, got edges {:?}",
        result.equivalence_edges
    );
}

#[test]
fn test_xnor_complementary_pair_reorders_after_uf_canonicalization() {
    let mut clauses = ClauseArena::new();
    add_xnor3_gate(&mut clauses, 0, [1, 2, 3]);
    add_equivalence(&mut clauses, 1, 4);
    add_negated_equivalence(&mut clauses, 3, 4);

    let mut cc = CongruenceClosure::new(5);
    let result = cc.run(&mut clauses, None, &[]);

    let y_pos = Literal::positive(Variable(0));
    let b_pos = Literal::positive(Variable(2));
    let b_neg = Literal::negative(Variable(2));
    assert!(
        edge_connects(&result.equivalence_edges, y_pos, b_pos),
        "XNOR(t, b, ¬t) must collapse to y ≡ b, got edges {:?}",
        result.equivalence_edges
    );
    assert!(
        !edge_connects(&result.equivalence_edges, y_pos, b_neg),
        "XNOR(t, b, ¬t) must not collapse to y ≡ ¬b, got edges {:?}",
        result.equivalence_edges
    );
}

/// The gate table's removal path (B77).
///
/// A gate is rewritten BECAUSE a merge changed one of its inputs'
/// representatives, so recomputing its signature at removal time yields a
/// different key from the one it was filed under: the removal misses and the
/// entry is stranded, one per rewrite, unbounded. On SAT-COMP 2026
/// `post-cbmc-aes-ee-r2` (a 33 MB input that 28 of 31 official solvers solve)
/// that reached 17.6 GB resident and a `c memout` 8 s into a 300 s budget.
fn gate_sig(gate_type: GateType, inputs: &[usize]) -> GateSignature {
    GateSignature {
        gate_type,
        inputs: inputs.iter().copied().collect::<SmallVec<[usize; 5]>>(),
    }
}

#[test]
fn exact_removal_drops_the_entry_the_gate_was_filed_under() {
    let mut table = GateTable::new(4, true);
    let filed = gate_sig(GateType::And, &[2, 4]);
    table.insert(filed.clone(), 1);
    assert_eq!(table.len(), 1);

    // A merge has since demoted input 4, so the caller's recomputed key is a
    // different signature entirely. Exact removal must not consult it.
    table.remove_gate(1, || gate_sig(GateType::And, &[2, 6]));

    assert_eq!(
        table.len(),
        0,
        "the entry the gate was filed under must be gone — recomputing the key \
         after a merge is exactly the case that stranded it"
    );
    assert_eq!(table.get(&filed), None);
}

#[test]
fn legacy_removal_strands_the_entry_when_the_key_moved() {
    let mut table = GateTable::new(4, false);
    let filed = gate_sig(GateType::And, &[2, 4]);
    table.insert(filed.clone(), 1);

    table.remove_gate(1, || gate_sig(GateType::And, &[2, 6]));

    assert_eq!(
        table.len(),
        1,
        "the opt-out arm must reproduce the leak verbatim, or a paired A/B is \
         measuring something other than the fix"
    );
    assert_eq!(table.get(&filed), Some(1));
}

/// Exact removal must be a no-op for a gate that holds no entry, must not touch
/// another gate's entry, and must be idempotent.
#[test]
fn exact_removal_is_scoped_to_one_gate() {
    let mut table = GateTable::new(4, true);
    table.insert(gate_sig(GateType::And, &[2, 4]), 1);
    table.insert(gate_sig(GateType::Xor, &[6, 8]), 2);

    table.remove_gate(3, || gate_sig(GateType::And, &[2, 4]));
    assert_eq!(table.len(), 2, "a gate with no entry must remove nothing");

    table.remove_gate(1, || unreachable!("exact removal must not recompute"));
    assert_eq!(table.len(), 1);
    assert_eq!(table.get(&gate_sig(GateType::Xor, &[6, 8])), Some(2));

    table.remove_gate(1, || unreachable!("exact removal must not recompute"));
    assert_eq!(table.len(), 1, "removing twice must be idempotent");
}
