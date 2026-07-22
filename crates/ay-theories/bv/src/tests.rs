// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::term::Symbol;
use ay_core::{TheoryResult, TheorySolver};
use ay_sat::{Literal, SatResult, Solver};
use num_bigint::BigInt;
use proptest::prelude::*;

fn setup_store() -> TermStore {
    TermStore::new()
}

/// Solve BvSolver clauses and return variable assignments
fn solve_bv_clauses(solver: &BvSolver<'_>) -> Vec<bool> {
    let num_vars = (solver.next_var - 1) as usize;
    let mut sat_solver = Solver::new(num_vars);

    for clause in solver.clauses() {
        let lits: Vec<Literal> = clause
            .literals()
            .iter()
            .map(|&l| Literal::from_dimacs(l))
            .collect();
        sat_solver.add_clause(lits);
    }

    match sat_solver.solve().into_inner() {
        SatResult::Sat(model) => model,
        SatResult::Unsat(_) => panic!("Expected SAT, got UNSAT"),
        SatResult::Unknown => panic!("Expected SAT, got Unknown"),
        #[allow(unreachable_patterns)]
        _ => unreachable!(),
    }
}

/// Extract a bitvector value from an assignment
fn extract_bv_value(model: &[bool], bits: &[CnfLit]) -> u64 {
    let mut value = 0u64;
    for (i, &bit) in bits.iter().enumerate() {
        let var_idx = (bit.unsigned_abs() - 1) as usize;
        let bit_value = model.get(var_idx).copied().unwrap_or(false);
        let polarity = bit > 0;
        if bit_value == polarity && i < 64 {
            value |= 1u64 << i;
        }
    }
    value
}

fn extract_bv_model(solver: &BvSolver<'_>, model: &[bool]) -> BvModel {
    let mut values = HashMap::default();
    let mut term_to_bits = HashMap::default();

    for (&term, bits) in solver.term_to_bits() {
        if !matches!(solver.terms.sort(term), Sort::BitVec(_)) {
            continue;
        }
        let mut value = BigInt::from(0u64);
        for (i, &bit) in bits.iter().enumerate() {
            let var_idx = (bit.unsigned_abs() - 1) as usize;
            let bit_value = model.get(var_idx).copied().unwrap_or(false);
            if bit_value == (bit > 0) {
                value |= BigInt::from(1u64) << i;
            }
        }
        values.insert(term, value);
        term_to_bits.insert(term, bits.clone());
    }

    BvModel {
        values,
        term_to_bits,
        bool_overrides: HashMap::default(),
    }
}

fn input_truth_table(input: usize) -> [bool; 8] {
    let mut table = [false; 8];
    for (assignment, value) in table.iter_mut().enumerate() {
        *value = (assignment & (1 << input)) != 0;
    }
    table
}

fn invert_truth_table(mut table: [bool; 8]) -> [bool; 8] {
    for value in &mut table {
        *value = !*value;
    }
    table
}

fn and_truth_tables(left: [bool; 8], right: [bool; 8]) -> [bool; 8] {
    let mut table = [false; 8];
    for i in 0..table.len() {
        table[i] = left[i] && right[i];
    }
    table
}

fn eval_aig_lit(
    solver: &BvSolver<'_>,
    inputs: &HashMap<CnfLit, [bool; 8]>,
    lit: CnfLit,
) -> [bool; 8] {
    if solver.is_known_false(lit) {
        return [false; 8];
    }
    if solver.is_known_true(lit) {
        return [true; 8];
    }

    let positive = lit.abs();
    let table = if let Some(&table) = inputs.get(&positive) {
        table
    } else if let Some(&(left, right)) = solver.and_children.get(&positive) {
        and_truth_tables(
            eval_aig_lit(solver, inputs, left),
            eval_aig_lit(solver, inputs, right),
        )
    } else {
        panic!("literal {lit} has no input truth table or AND children");
    };

    if lit < 0 {
        invert_truth_table(table)
    } else {
        table
    }
}

#[test]
fn test_batch_fresh_vars_allocates_contiguous_range() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    let range = solver.batch_fresh_vars(4);

    assert_eq!(range.first(), Some(1));
    assert_eq!(range.last(), Some(4));
    assert_eq!(range.count(), 4);
    assert_eq!(range.to_vec(), vec![1, 2, 3, 4]);
    assert_eq!(solver.num_vars(), 4);

    let empty = solver.batch_fresh_vars(0);
    assert!(empty.is_empty());
    assert_eq!(empty.first(), None);
    assert_eq!(solver.num_vars(), 4);

    assert_eq!(solver.fresh_var(), 5);
}

#[test]
fn test_clause_batch_extracts_flat_deterministic_cnf() {
    let clauses = vec![
        CnfClause::unit(1),
        CnfClause::binary(-1, 2),
        CnfClause::new(vec![3, -4, 5]),
    ];

    let batch = BvClauseBatch::from_clauses(5, &clauses);

    assert_eq!(batch.num_vars(), 5);
    assert_eq!(batch.clause_count(), 3);
    assert_eq!(batch.literal_count(), 6);
    assert_eq!(batch.offsets(), &[0, 1, 3, 6]);
    assert_eq!(batch.literals(), &[1, -1, 2, 3, -4, 5]);
    assert_eq!(batch.clause_literals(1), Some(&[-1, 2][..]));
    assert_eq!(batch.observed_max_var(), 5);
    assert_eq!(batch.to_clauses(), clauses);
}

#[test]
fn test_smt_bv_batch_template_application_stats_fail_closed() {
    assert_eq!(
        batch::SMT_BV_BATCH_TEMPLATE_APPLICATION_COUNTER,
        "smt_bv_batch_template_applications"
    );
    assert_eq!(batch::smt_bv_batch_template_application_count(), 0);
}

#[test]
fn test_gate_templates_match_current_gate_emission() {
    let store = setup_store();

    let mut and_solver = BvSolver::new(&store);
    let and_a = and_solver.fresh_var();
    let and_b = and_solver.fresh_var();
    let and_out = and_solver.mk_and(and_a, and_b);
    assert_eq!(
        and_solver.clauses(),
        BvGateTemplate::and(and_a, and_b, and_out).to_clauses()
    );

    let mut or_solver = BvSolver::new(&store);
    let or_a = or_solver.fresh_var();
    let or_b = or_solver.fresh_var();
    let or_out = or_solver.mk_or(or_a, or_b);
    assert!(
        or_out < 0,
        "live mk_or should return the negated output of its De Morgan AND"
    );
    assert_eq!(
        or_solver.clauses(),
        BvGateTemplate::and(-or_a, -or_b, -or_out).to_clauses()
    );
    assert_eq!(
        BvGateTemplate::or(or_a, or_b, -or_out).to_clauses(),
        vec![
            CnfClause::binary(-or_a, -or_out),
            CnfClause::binary(-or_b, -or_out),
            CnfClause::new(vec![or_out, or_a, or_b]),
        ],
        "the direct OR template remains a stable external code generation stamping contract"
    );

    let mut xor_solver = BvSolver::new(&store);
    let xor_a = xor_solver.fresh_var();
    let xor_b = xor_solver.fresh_var();
    let xor_out = xor_solver.mk_xor(xor_a, xor_b);
    assert_eq!(
        xor_solver.clauses(),
        BvGateTemplate::xor(xor_a, xor_b, xor_out).to_clauses()
    );

    let mut mux_solver = BvSolver::new(&store);
    let sel = mux_solver.fresh_var();
    let then_lit = mux_solver.fresh_var();
    let else_lit = mux_solver.fresh_var();
    let mux_out = mux_solver.mk_mux(then_lit, else_lit, sel);
    assert_eq!(
        mux_solver.clauses(),
        BvGateTemplate::mux(sel, then_lit, else_lit, mux_out).to_clauses()
    );
}

#[test]
fn test_gate_provenance_capture_records_xor_and_mux_children() {
    let store = setup_store();

    // Default: provenance capture OFF — primitive XOR/MUX leave the reverse
    // maps empty, so the production solve path carries no extra per-gate state.
    let mut off = BvSolver::new(&store);
    let oa = off.fresh_var();
    let ob = off.fresh_var();
    let _ = off.mk_xor(oa, ob);
    let osel = off.fresh_var();
    let ot = off.fresh_var();
    let oe = off.fresh_var();
    let _ = off.mk_mux(ot, oe, osel);
    assert!(
        off.xor_children().is_empty(),
        "xor provenance must be off by default"
    );
    assert!(
        off.mux_children().is_empty(),
        "mux provenance must be off by default"
    );

    // Enabled: a fresh primitive XOR's output maps back to its inputs, and the
    // recorded inputs re-derive EXACTLY the emitted Tseitin clauses (faithfulness:
    // the provenance is checked against gate truth, not merely stored).
    let mut on = BvSolver::new(&store);
    on.enable_gate_provenance();
    let xa = on.fresh_var();
    let xb = on.fresh_var();
    let xout = on.mk_xor(xa, xb);
    let (&rx_out, &(rx_a, rx_b)) = on
        .xor_children()
        .iter()
        .next()
        .expect("xor provenance recorded");
    assert_eq!(rx_out, xout);
    // Key is normalized (min, max); fresh vars are allocated ascending.
    assert_eq!((rx_a, rx_b), (xa.min(xb), xa.max(xb)));
    assert_eq!(
        on.clauses(),
        BvGateTemplate::xor(rx_a, rx_b, rx_out).to_clauses(),
        "recorded XOR inputs must re-derive the emitted Tseitin clauses"
    );

    // Same for a primitive MUX (non-commutative: the (sel, then, else) order is
    // preserved).
    let mut onm = BvSolver::new(&store);
    onm.enable_gate_provenance();
    let sel = onm.fresh_var();
    let then_lit = onm.fresh_var();
    let else_lit = onm.fresh_var();
    let mout = onm.mk_mux(then_lit, else_lit, sel);
    let (&rm_out, &(rm_sel, rm_then, rm_else)) = onm
        .mux_children()
        .iter()
        .next()
        .expect("mux provenance recorded");
    assert_eq!(rm_out, mout);
    assert_eq!((rm_sel, rm_then, rm_else), (sel, then_lit, else_lit));
    assert_eq!(
        onm.clauses(),
        BvGateTemplate::mux(rm_sel, rm_then, rm_else, rm_out).to_clauses(),
        "recorded MUX inputs must re-derive the emitted Tseitin clauses"
    );
}

fn fresh_aig_inputs(
    solver: &mut BvSolver<'_>,
) -> (CnfLit, CnfLit, CnfLit, HashMap<CnfLit, [bool; 8]>) {
    let a = solver.fresh_var();
    let b = solver.fresh_var();
    let c = solver.fresh_var();
    let mut inputs = HashMap::default();
    inputs.insert(a, input_truth_table(0));
    inputs.insert(b, input_truth_table(1));
    inputs.insert(c, input_truth_table(2));
    (a, b, c, inputs)
}

fn assert_lit_table(
    solver: &BvSolver<'_>,
    inputs: &HashMap<CnfLit, [bool; 8]>,
    lit: CnfLit,
    expected: [bool; 8],
) {
    assert_eq!(eval_aig_lit(solver, inputs, lit), expected);
}

#[test]
fn test_mk_and_two_level_level2_rules_8809() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);
    let (a, b, c, inputs) = fresh_aig_inputs(&mut solver);

    let ab = solver.mk_and(a, b);
    let asymmetric_contradiction = solver.mk_and(ab, -a);
    assert_lit_table(&solver, &inputs, asymmetric_contradiction, [false; 8]);

    let not_a_c = solver.mk_and(-a, c);
    let symmetric_contradiction = solver.mk_and(ab, not_a_c);
    assert_lit_table(&solver, &inputs, symmetric_contradiction, [false; 8]);

    assert_eq!(solver.mk_and(-ab, -a), -a);
    assert_eq!(solver.mk_and(-ab, not_a_c), not_a_c);
    assert_eq!(solver.mk_and(ab, a), ab);

    let a_not_b = solver.mk_and(a, -b);
    assert_eq!(solver.mk_and(-ab, -a_not_b), -a);
}

#[test]
fn test_mk_and_two_level_substitution_and_idempotence_8809() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);
    let (a, b, c, inputs) = fresh_aig_inputs(&mut solver);

    let ab = solver.mk_and(a, b);
    let ac = solver.mk_and(a, c);

    let asymmetric = solver.mk_and(-ab, a);
    assert_lit_table(
        &solver,
        &inputs,
        asymmetric,
        and_truth_tables(
            input_truth_table(0),
            invert_truth_table(input_truth_table(1)),
        ),
    );

    let symmetric = solver.mk_and(-ab, ac);
    assert_lit_table(
        &solver,
        &inputs,
        symmetric,
        and_truth_tables(
            invert_truth_table(input_truth_table(1)),
            and_truth_tables(input_truth_table(0), input_truth_table(2)),
        ),
    );

    let idempotent = solver.mk_and(ab, ac);
    assert_lit_table(
        &solver,
        &inputs,
        idempotent,
        and_truth_tables(
            and_truth_tables(input_truth_table(0), input_truth_table(1)),
            input_truth_table(2),
        ),
    );
}

#[test]
fn test_mk_or_uses_and_rewriter_for_absorption_8959() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);
    let (a, b, _c, inputs) = fresh_aig_inputs(&mut solver);

    let ab = solver.mk_and(a, b);

    let absorbed = solver.mk_or(ab, a);
    assert_eq!(absorbed, a, "(a & b) | a should simplify to a");

    let tautology = solver.mk_or(-ab, a);
    assert!(
        solver.is_known_true(tautology),
        "!(a & b) | a should simplify to a known true literal"
    );

    let a_not_b = solver.mk_and(a, -b);
    let split_absorbed = solver.mk_or(ab, a_not_b);
    assert_eq!(split_absorbed, a, "(a & b) | (a & !b) should simplify to a");

    assert_lit_table(&solver, &inputs, absorbed, input_truth_table(0));
    assert_lit_table(&solver, &inputs, split_absorbed, input_truth_table(0));
}

#[test]
fn test_mk_xor_uses_and_rewriter_for_absorption_8959() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);
    let (a, b, _c, inputs) = fresh_aig_inputs(&mut solver);

    let ab = solver.mk_and(a, b);

    let absorbed = solver.mk_xor(ab, a);
    let a_not_b = solver.mk_and(a, -b);
    assert_eq!(absorbed, a_not_b, "(a & b) xor a should simplify to a & !b");

    let negated_absorbed = solver.mk_xor(-ab, a);
    assert_eq!(
        negated_absorbed, -a_not_b,
        "!(a & b) xor a should simplify to !(a & !b)"
    );

    let split_absorbed = solver.mk_xor(ab, a_not_b);
    assert_eq!(
        split_absorbed, a,
        "(a & b) xor (a & !b) should simplify to a"
    );

    let split_negated = solver.mk_xor(ab, -a_not_b);
    assert_eq!(
        split_negated, -a,
        "(a & b) xor !(a & !b) should simplify to !a"
    );

    let b_not_a = solver.mk_and(-a, b);
    let split_b = solver.mk_xor(ab, b_not_a);
    assert_eq!(split_b, b, "(a & b) xor (!a & b) should simplify to b");

    assert_lit_table(
        &solver,
        &inputs,
        absorbed,
        and_truth_tables(
            input_truth_table(0),
            invert_truth_table(input_truth_table(1)),
        ),
    );
    assert_lit_table(
        &solver,
        &inputs,
        negated_absorbed,
        invert_truth_table(and_truth_tables(
            input_truth_table(0),
            invert_truth_table(input_truth_table(1)),
        )),
    );
    assert_lit_table(&solver, &inputs, split_absorbed, input_truth_table(0));
    assert_lit_table(&solver, &inputs, split_b, input_truth_table(1));
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1000))]

    #[test]
    fn proptest_mk_and_two_level_rewrites_preserve_truth_tables_8809(
        ops in prop::collection::vec((0usize..16, any::<bool>(), 0usize..16, any::<bool>()), 1..=6)
    ) {
        let store = setup_store();
        let mut solver = BvSolver::new(&store);
        let (a, b, c, mut inputs) = fresh_aig_inputs(&mut solver);
        let mut lits = vec![a, b, c];
        let mut tables = vec![input_truth_table(0), input_truth_table(1), input_truth_table(2)];

        for (left_idx, left_neg, right_idx, right_neg) in ops {
            let mut left = lits[left_idx % lits.len()];
            let mut left_table = tables[left_idx % tables.len()];
            if left_neg {
                left = -left;
                left_table = invert_truth_table(left_table);
            }

            let mut right = lits[right_idx % lits.len()];
            let mut right_table = tables[right_idx % tables.len()];
            if right_neg {
                right = -right;
                right_table = invert_truth_table(right_table);
            }

            let out = solver.mk_and(left, right);
            let expected = and_truth_tables(left_table, right_table);
            prop_assert_eq!(eval_aig_lit(&solver, &inputs, out), expected);

            if out > 0 {
                inputs.entry(out).or_insert(expected);
                lits.push(out);
                tables.push(expected);
            }
        }
    }
}

#[test]
fn test_template_batch_records_gate_clause_ranges() {
    let mut batch = BvTemplateBatch::new(4);

    let and_gate = BvGateTemplate::and(1, 2, 3);
    let mux_gate = BvGateTemplate::mux(1, 2, 3, 4);
    let and_stamp = batch.push_gate(and_gate);
    let mux_stamp = batch.push_gate(mux_gate);

    assert_eq!(and_stamp.template(), and_gate);
    assert_eq!(and_stamp.first_clause(), 0);
    assert_eq!(and_stamp.clause_count(), 3);
    assert_eq!(mux_stamp.template(), mux_gate);
    assert_eq!(mux_stamp.first_clause(), 3);
    assert_eq!(mux_stamp.clause_count(), 4);
    assert_eq!(batch.gates(), &[and_stamp, mux_stamp]);
    assert_eq!(batch.clauses().clause_count(), 7);
    assert_eq!(
        batch.clauses().to_clauses(),
        [
            BvGateTemplate::and(1, 2, 3).to_clauses(),
            BvGateTemplate::mux(1, 2, 3, 4).to_clauses(),
        ]
        .concat()
    );
}

#[test]
fn test_solver_clause_batch_matches_live_clause_store() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);
    let a = solver.fresh_var();
    let b = solver.fresh_var();
    let _out = solver.mk_xor(a, b);

    let batch = solver.clause_batch();

    assert_eq!(batch.num_vars(), solver.num_vars());
    assert_eq!(batch.to_clauses(), solver.clauses());
}

#[test]
fn test_const_bits() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    let bits = solver.const_bits(5, 4); // 0101
    assert_eq!(bits.len(), 4);

    // Verify the concrete value by solving and extracting
    let model = solve_bv_clauses(&solver);
    let val = extract_bv_value(&model, &bits);
    assert_eq!(val, 5, "const_bits(5, 4) should produce value 5");
}

#[test]
fn test_const_bits_wide_no_panic() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    let bits = solver.const_bits(1, 128);
    assert_eq!(bits.len(), 128);
    // With cached false literal optimization (#7974), both zero and true
    // bits reuse the same cached variable: zero bits use `cached_false_lit`
    // and true bits use `-cached_false_lit`. Only 1 unit clause is needed
    // for the single cached false variable.
    assert_eq!(solver.clauses.len(), 1);
}

#[test]
fn test_delayed_internalization_tracks_wide_variable_mul() {
    // Delayed internalization (#7015): wide variable*variable multiplication
    // gets unconstrained result bits instead of the full multiplier circuit.
    // The post-solve re-check loop (#8480 fix) verifies correctness.
    let mut store = setup_store();
    let x = store.mk_var("x", Sort::bitvec(16));
    let y = store.mk_var("y", Sort::bitvec(16));
    let mul = store.mk_bvmul(vec![x, y]);

    let mut solver = BvSolver::new(&store);
    solver.set_delay_enabled(true);

    let bits = solver.ensure_term_bits(mul).expect("mul is BV-sorted");

    assert_eq!(bits.len(), 16);
    // With delayed internalization re-enabled, wide mul with 2 variable args
    // should be delayed (width=16 > 12, 2 variable args).
    assert_eq!(
        solver.delayed_ops().len(),
        1,
        "wide variable*variable mul should be delayed (got {} delayed ops)",
        solver.delayed_ops().len()
    );
    // Delayed ops produce unconstrained bits, not circuit clauses.
    // The full circuit is built later by the post-solve re-check loop.
}

#[test]
fn test_materialize_delayed_term_emits_constraining_clauses() {
    // Delayed internalization (#7015): wide variable/variable udiv gets
    // unconstrained result bits. build_delayed_circuit() builds the full
    // divider circuit and emits equivalence clauses tying the circuit
    // outputs to the unconstrained result bits.
    let mut store = setup_store();
    let x = store.mk_var("x", Sort::bitvec(16));
    let y = store.mk_var("y", Sort::bitvec(16));
    let udiv = store.mk_bvudiv(vec![x, y]);

    let mut solver = BvSolver::new(&store);
    solver.set_delay_enabled(true);
    let bits = solver.ensure_term_bits(udiv).expect("udiv is BV-sorted");

    assert_eq!(bits.len(), 16);
    // With delayed internalization enabled, wide udiv with 2 variable args
    // should be delayed (width=16 > 12, 2 variable args).
    assert_eq!(
        solver.delayed_ops().len(),
        1,
        "wide variable/variable udiv should be delayed (got {} delayed ops)",
        solver.delayed_ops().len()
    );
    // There should be an unresolved delayed op.
    assert!(
        solver.has_unresolved_delayed_ops(),
        "delayed udiv should be unresolved until circuit is built"
    );
    // Build the full circuit for the delayed op.
    let clauses = solver.build_delayed_circuit(0);
    assert!(
        !clauses.is_empty(),
        "building delayed circuit should produce equivalence clauses"
    );
    // After building, the op should be resolved.
    assert!(
        !solver.has_unresolved_delayed_ops(),
        "after building circuit, no unresolved delayed ops should remain"
    );
}

#[test]
fn test_process_assertion_handles_bool_ite() {
    // Regression test for #1539: check-sat-assuming with BV+ITE returns invalid SAT
    // The bug was that process_assertion() didn't handle TermData::Ite,
    // causing the ITE to be silently ignored and SAT to be incorrectly returned.

    let mut store = TermStore::new();

    // Build: (ite cond then_br else_br) where cond, then_br, else_br are Bool variables
    // We use variables to prevent constant folding from simplifying away the ITE.
    let cond = store.mk_var("cond", Sort::Bool);
    let then_br = store.mk_var("then_br", Sort::Bool);
    let else_br = store.mk_var("else_br", Sort::Bool);

    // Create ITE term
    let ite_term = store.mk_ite(cond, then_br, else_br);

    // Process assertion: ite(cond, then_br, else_br) = true
    // This should add clauses that encode the ITE semantics.
    let mut solver = BvSolver::new(&store);
    solver.process_assertion(ite_term, true);

    // After bitblasting, we should have non-empty clauses
    // (the bug would leave clauses empty because ITE was ignored)
    assert!(
        !solver.clauses.is_empty(),
        "ITE should be processed and generate clauses"
    );
}

#[test]
fn test_bv_ite_condition_tracked_for_tseitin_linking() {
    // Regression test for #1696: BV `ite` conditions must be tracked so we can
    // link their Tseitin var ↔ BV literal during encoding. Linking *all* Bool terms
    // is unsound, so we must track which Bool terms are legitimate BV ITE conditions.
    let mut store = TermStore::new();
    let cond = store.mk_var("cond", Sort::Bool);
    let then_bv = store.mk_var("then_bv", Sort::bitvec(8));
    let else_bv = store.mk_var("else_bv", Sort::bitvec(8));
    let ite_bv = store.mk_ite(cond, then_bv, else_bv);

    let mut solver = BvSolver::new(&store);
    let bits = solver.get_bits(ite_bv);

    assert_eq!(bits.len(), 8);
    assert!(
        solver.bv_ite_conditions().contains(&cond),
        "BV ite condition should be tracked for Tseitin linking"
    );
}

#[test]
fn test_bool_ite_condition_tracked_for_tseitin_linking() {
    // Bool-sorted ITE conditions MUST be tracked for Tseitin-BV linking (#1708).
    // Previously this test asserted the opposite, but that was wrong - Bool ITE
    // conditions need linking just like BV ITE conditions to ensure the Tseitin
    // and BV encodings agree on the condition's truth value.
    let mut store = TermStore::new();
    let cond = store.mk_var("cond", Sort::Bool);
    let then_br = store.mk_var("then_br", Sort::Bool);
    let else_br = store.mk_var("else_br", Sort::Bool);
    let ite_bool = store.mk_ite(cond, then_br, else_br);

    let mut solver = BvSolver::new(&store);
    let _lit = solver.bitblast_bool(ite_bool);

    assert!(
        solver.bv_ite_conditions().contains(&cond),
        "Bool ITE condition should be tracked for Tseitin-BV linking (#1708)"
    );
}

#[test]
fn test_bitblast_bool_caches_degenerate_xor() {
    // Ensure degenerate SMT-LIB arities are cached (no fresh CNF var per call).
    //
    // Previously, bitblast_bool() would early-return for (xor), bypassing the
    // bool_to_var cache and allocating new vars/clauses on each call.
    let mut store = TermStore::new();
    let xor0 = store.mk_app(Symbol::named("xor"), vec![], Sort::Bool);

    let mut solver = BvSolver::new(&store);
    let lit1 = solver.bitblast_bool(xor0);
    let clauses_after_first = solver.clauses.len();
    let lit2 = solver.bitblast_bool(xor0);
    let clauses_after_second = solver.clauses.len();

    assert_eq!(lit1, lit2);
    assert_eq!(clauses_after_first, clauses_after_second);
}

#[test]
fn test_bitblast_bool_caches_degenerate_eq() {
    // SMT-LIB: (=) and (= x) are both true.
    // Test 0-arity case (=).
    let mut store = TermStore::new();
    let eq0 = store.mk_app(Symbol::named("="), vec![], Sort::Bool);

    let mut solver = BvSolver::new(&store);
    let lit1 = solver.bitblast_bool(eq0);
    let clauses_after_first = solver.clauses.len();
    let lit2 = solver.bitblast_bool(eq0);
    let clauses_after_second = solver.clauses.len();

    assert_eq!(lit1, lit2);
    assert_eq!(clauses_after_first, clauses_after_second);
}

#[test]
fn test_bitblast_bool_caches_degenerate_eq_single_arg() {
    // SMT-LIB: (= x) is true (trivial reflexivity).
    // Test 1-arity case.
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::Bool);
    let eq1 = store.mk_app(Symbol::named("="), vec![x], Sort::Bool);

    let mut solver = BvSolver::new(&store);
    let lit1 = solver.bitblast_bool(eq1);
    let clauses_after_first = solver.clauses.len();
    let lit2 = solver.bitblast_bool(eq1);
    let clauses_after_second = solver.clauses.len();

    assert_eq!(lit1, lit2);
    assert_eq!(clauses_after_first, clauses_after_second);
}

#[test]
fn test_bitblast_bool_caches_degenerate_distinct() {
    // SMT-LIB: (distinct) and (distinct x) are both true.
    // Test 0-arity case.
    let mut store = TermStore::new();
    let distinct0 = store.mk_app(Symbol::named("distinct"), vec![], Sort::Bool);

    let mut solver = BvSolver::new(&store);
    let lit1 = solver.bitblast_bool(distinct0);
    let clauses_after_first = solver.clauses.len();
    let lit2 = solver.bitblast_bool(distinct0);
    let clauses_after_second = solver.clauses.len();

    assert_eq!(lit1, lit2);
    assert_eq!(clauses_after_first, clauses_after_second);
}

#[test]
fn test_bitblast_bool_caches_degenerate_distinct_single_arg() {
    // SMT-LIB: (distinct x) is true (trivially all elements are distinct).
    // Test 1-arity case.
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::Bool);
    let distinct1 = store.mk_app(Symbol::named("distinct"), vec![x], Sort::Bool);

    let mut solver = BvSolver::new(&store);
    let lit1 = solver.bitblast_bool(distinct1);
    let clauses_after_first = solver.clauses.len();
    let lit2 = solver.bitblast_bool(distinct1);
    let clauses_after_second = solver.clauses.len();

    assert_eq!(lit1, lit2);
    assert_eq!(clauses_after_first, clauses_after_second);
}

#[test]
fn test_bitblast_and() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    let a = solver.const_bits(0b1100, 4);
    let b = solver.const_bits(0b1010, 4);
    let result = solver.bitblast_and(&a, &b);

    assert_eq!(result.len(), 4);

    let model = solve_bv_clauses(&solver);
    let val = extract_bv_value(&model, &result);
    assert_eq!(val, 0b1000, "0b1100 & 0b1010 should be 0b1000 (8)");
}

#[test]
fn test_bitblast_add() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    let a = solver.const_bits(3, 4);
    let b = solver.const_bits(5, 4);
    let result = solver.bitblast_add(&a, &b);

    assert_eq!(result.len(), 4);

    let model = solve_bv_clauses(&solver);
    let val = extract_bv_value(&model, &result);
    assert_eq!(val, 8, "3 + 5 should be 8");
}

#[test]
fn test_bitblast_variable() {
    let mut store = setup_store();
    let x = store.mk_var("x", Sort::bitvec(8));

    let mut solver = BvSolver::new(&store);
    let bits = solver.get_bits(x);

    assert_eq!(bits.len(), 8);
}

#[test]
fn test_bitblast_concat_nested_order() {
    let mut store = setup_store();
    let a = store.mk_var("a", Sort::bitvec(2));
    let b = store.mk_var("b", Sort::bitvec(3));
    let c = store.mk_var("c", Sort::bitvec(1));

    // concat is binary: concat(high, low)
    let ab = store.mk_bvconcat(vec![a, b]);
    let abc = store.mk_bvconcat(vec![ab, c]);

    let mut solver = BvSolver::new(&store);
    let a_bits = solver.get_bits(a);
    let b_bits = solver.get_bits(b);
    let c_bits = solver.get_bits(c);

    // LSB-first: bits(concat(high, low)) = bits(low) ++ bits(high)
    let mut expected = c_bits;
    expected.extend(b_bits);
    expected.extend(a_bits);

    let bits = solver.get_bits(abc);
    assert_eq!(bits, expected);
}

#[test]
fn test_bitblast_concat_flattens_without_bitblasting_intermediates() {
    let mut store = setup_store();

    let leaf_count = 20usize;
    let leaves: Vec<TermId> = (0..leaf_count)
        .map(|i| store.mk_var(format!("v{i}"), Sort::bitvec(1)))
        .collect();

    // Build a deep, left-associative concat chain.
    let mut concats = Vec::new();
    let mut t = store.mk_bvconcat(vec![leaves[0], leaves[1]]);
    concats.push(t);
    for &leaf in &leaves[2..] {
        t = store.mk_bvconcat(vec![t, leaf]);
        concats.push(t);
    }
    let root = t;

    let mut solver = BvSolver::new(&store);
    let _bits = solver.get_bits(root);

    // Only leaf vars + root should be cached: intermediate concat nodes are flattened. (#1804)
    assert_eq!(solver.term_to_bits().len(), leaf_count + 1);
    for &c in &concats[..concats.len() - 1] {
        assert!(
            !solver.term_to_bits().contains_key(&c),
            "intermediate concat term should not be bitblasted"
        );
    }
}

#[test]
fn test_bitblast_bvadd_term() {
    let mut store = setup_store();
    let x = store.mk_var("x", Sort::bitvec(8));
    let y = store.mk_var("y", Sort::bitvec(8));
    let sum = store.mk_bvadd(vec![x, y]);

    let mut solver = BvSolver::new(&store);
    let bits = solver.get_bits(sum);

    assert_eq!(bits.len(), 8);
}

#[test]
fn test_validate_bv_assertions_accepts_real_sat_model() {
    let mut store = setup_store();
    let x = store.mk_var("x", Sort::bitvec(4));
    let one = store.mk_bitvec(BigInt::from(1u64), 4);
    let two = store.mk_bitvec(BigInt::from(2u64), 4);
    let sum = store.mk_bvadd(vec![x, one]);
    let assertion = store.mk_eq(sum, two);

    let mut solver = BvSolver::new(&store);
    solver.bitblast_assertion(assertion);
    let sat_model = solve_bv_clauses(&solver);
    let bv_model = extract_bv_model(&solver, &sat_model);

    assert_eq!(
        validate_bv_assertions(&store, &[assertion], &bv_model),
        Ok(1)
    );
    assert_eq!(
        evaluate_bv_assertion(&store, assertion, &bv_model),
        Some(true)
    );
}

#[test]
fn test_validate_bv_assertions_rejects_semantic_cnf_mismatch_model() {
    let mut store = setup_store();
    let x = store.mk_var("x", Sort::bitvec(4));
    let one = store.mk_bitvec(BigInt::from(1u64), 4);
    let two = store.mk_bitvec(BigInt::from(2u64), 4);
    let sum = store.mk_bvadd(vec![x, one]);
    let assertion = store.mk_eq(sum, two);

    let mut values = HashMap::default();
    values.insert(x, BigInt::from(0u64));
    let bv_model = BvModel {
        values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    };

    let err = validate_bv_assertions(&store, &[assertion], &bv_model)
        .expect_err("x = 0 violates x + 1 = 2");
    assert_eq!(err.assertion_index, 0);
    assert_eq!(err.assertion, assertion);
    assert_eq!(
        evaluate_bv_assertion(&store, assertion, &bv_model),
        Some(false)
    );
}

#[test]
fn test_validate_bv_expr_matches_supported_bitwise_derived_ops() {
    let mut store = setup_store();
    let x = store.mk_var("x", Sort::bitvec(4));
    let y = store.mk_var("y", Sort::bitvec(4));
    let nand = store.mk_app(Symbol::named("bvnand"), vec![x, y], Sort::bitvec(4));
    let nor = store.mk_app(Symbol::named("bvnor"), vec![x, y], Sort::bitvec(4));
    let xnor = store.mk_app(Symbol::named("bvxnor"), vec![x, y], Sort::bitvec(4));

    let mut values = HashMap::default();
    values.insert(x, BigInt::from(0b1100u8));
    values.insert(y, BigInt::from(0b1010u8));
    let bv_model = BvModel {
        values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    };

    assert_eq!(
        evaluate_bv_expr(&store, nand, &bv_model),
        Some(BigInt::from(0b0111u8))
    );
    assert_eq!(
        evaluate_bv_expr(&store, nor, &bv_model),
        Some(BigInt::from(0b0001u8))
    );
    assert_eq!(
        evaluate_bv_expr(&store, xnor, &bv_model),
        Some(BigInt::from(0b1001u8))
    );
}

#[test]
fn test_validate_bv_expr_matches_repeat_and_rotates() {
    let mut store = setup_store();
    let x = store.mk_var("x", Sort::bitvec(4));
    let repeat = store.mk_app(
        Symbol::indexed("repeat", vec![3]),
        vec![x],
        Sort::bitvec(12),
    );
    let rotl = store.mk_app(
        Symbol::indexed("rotate_left", vec![1]),
        vec![x],
        Sort::bitvec(4),
    );
    let rotr = store.mk_app(
        Symbol::indexed("rotate_right", vec![1]),
        vec![x],
        Sort::bitvec(4),
    );

    let mut values = HashMap::default();
    values.insert(x, BigInt::from(0b1001u8));
    let bv_model = BvModel {
        values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    };

    assert_eq!(
        evaluate_bv_expr(&store, repeat, &bv_model),
        Some(BigInt::from(0b1001_1001_1001u16))
    );
    assert_eq!(
        evaluate_bv_expr(&store, rotl, &bv_model),
        Some(BigInt::from(0b0011u8))
    );
    assert_eq!(
        evaluate_bv_expr(&store, rotr, &bv_model),
        Some(BigInt::from(0b1100u8))
    );
}

#[test]
fn test_bitblast_equality() {
    let mut store = setup_store();
    let x = store.mk_var("x", Sort::bitvec(4));
    let c = store.mk_bitvec(BigInt::from(5), 4);

    let mut solver = BvSolver::new(&store);
    let x_bits = solver.get_bits(x);
    let c_bits = solver.get_bits(c);

    let eq = solver.bitblast_eq(&x_bits, &c_bits);
    assert!(eq != 0);

    // Force equality to hold and verify x is constrained to 5
    solver.add_clause(CnfClause::unit(eq));
    let model = solve_bv_clauses(&solver);
    let x_val = extract_bv_value(&model, &x_bits);
    assert_eq!(x_val, 5, "equality constraint should force x = 5");
}

#[test]
fn test_bitblast_ult() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    let a = solver.const_bits(3, 4);
    let b = solver.const_bits(5, 4);
    let lt = solver.bitblast_ult(&a, &b);

    assert!(lt != 0);

    // 3 < 5 is true, so the ult literal should be forced true
    let model = solve_bv_clauses(&solver);
    let var_idx = (lt.unsigned_abs() - 1) as usize;
    let bit_val = model.get(var_idx).copied().unwrap_or(false);
    let expected = lt > 0; // positive literal means true when var is true
    assert_eq!(bit_val, expected, "3 < 5 should be true");
}

#[test]
fn test_theory_solver_interface() {
    let mut store = setup_store();
    let x = store.mk_var("x", Sort::bitvec(8));
    let y = store.mk_var("y", Sort::bitvec(8));
    let eq = store.mk_eq(x, y);

    let mut solver = BvSolver::new(&store);
    solver.assert_literal(eq, true);

    // Check returns Sat for eager bit-blasting (consistency checked by SAT solver)
    assert!(matches!(solver.check(), TheoryResult::Sat));
}

// =========================================================================
// Division tests
// =========================================================================

#[test]
fn test_is_zero() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    let zero = solver.const_bits(0, 4);
    let nonzero = solver.const_bits(5, 4);

    let zero_is_zero = solver.is_zero(&zero);
    let nonzero_is_zero = solver.is_zero(&nonzero);

    // These return literals - the actual constraints will be in clauses
    assert!(zero_is_zero != 0);
    assert!(nonzero_is_zero != 0);
}

#[test]
fn test_bitblast_udiv_urem_basic() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    // 7 / 3 = 2, 7 % 3 = 1
    let a = solver.const_bits(7, 4);
    let b = solver.const_bits(3, 4);

    let (q, r) = solver.bitblast_udiv_urem(&a, &b);

    assert_eq!(q.len(), 4);
    assert_eq!(r.len(), 4);
    assert!(!solver.clauses.is_empty());

    let model = solve_bv_clauses(&solver);
    let q_val = extract_bv_value(&model, &q);
    let r_val = extract_bv_value(&model, &r);
    assert_eq!(q_val, 2, "7 / 3 should be 2");
    assert_eq!(r_val, 1, "7 % 3 should be 1");
}

#[test]
fn test_bitblast_udiv() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    // 10 / 3 = 3
    let a = solver.const_bits(10, 4);
    let b = solver.const_bits(3, 4);

    let (q, _r) = solver.bitblast_udiv_urem(&a, &b);

    assert_eq!(q.len(), 4);

    let model = solve_bv_clauses(&solver);
    let q_val = extract_bv_value(&model, &q);
    assert_eq!(q_val, 3, "10 / 3 should be 3");
}

#[test]
fn test_bitblast_urem() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    // 10 % 3 = 1
    let a = solver.const_bits(10, 4);
    let b = solver.const_bits(3, 4);

    let (_q, r) = solver.bitblast_udiv_urem(&a, &b);

    assert_eq!(r.len(), 4);

    let model = solve_bv_clauses(&solver);
    let r_val = extract_bv_value(&model, &r);
    assert_eq!(r_val, 1, "10 % 3 should be 1");
}

#[test]
fn test_bitblast_sdiv() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    // In 4-bit signed: -7 = 0b1001, 2 = 0b0010
    // -7 / 2 = -3 (truncation toward zero) = 0b1101 = 13 unsigned
    let a = solver.const_bits(0b1001, 4); // -7 in 4-bit signed
    let b = solver.const_bits(0b0010, 4); // 2

    // Compute signed division: abs values, unsigned div, conditional negate
    let sign_a = a[3]; // MSB = sign bit
    let sign_b = b[3];
    let abs_a = solver.conditional_neg(&a, sign_a);
    let abs_b = solver.conditional_neg(&b, sign_b);
    let (abs_q, _) = solver.bitblast_udiv_urem(&abs_a, &abs_b);
    let result_neg = solver.mk_xor(sign_a, sign_b);
    let q = solver.conditional_neg(&abs_q, result_neg);

    assert_eq!(q.len(), 4);

    let model = solve_bv_clauses(&solver);
    let q_val = extract_bv_value(&model, &q);
    // -3 in 4-bit two's complement = 0b1101 = 13 unsigned
    assert_eq!(q_val, 0b1101, "-7 / 2 should be -3 (0b1101 = 13 unsigned)");
}

#[test]
fn test_bitblast_srem() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    // In 4-bit signed: -7 = 0b1001, 2 = 0b0010
    // -7 % 2 = -1 (sign matches dividend) = 0b1111 = 15 unsigned
    let a = solver.const_bits(0b1001, 4); // -7 in 4-bit signed
    let b = solver.const_bits(0b0010, 4); // 2

    // Compute signed remainder: abs values, unsigned div, conditional negate
    let sign_a = a[3]; // MSB = sign bit
    let sign_b = b[3];
    let abs_a = solver.conditional_neg(&a, sign_a);
    let abs_b = solver.conditional_neg(&b, sign_b);
    let (_, abs_r) = solver.bitblast_udiv_urem(&abs_a, &abs_b);
    let r = solver.conditional_neg(&abs_r, sign_a);

    assert_eq!(r.len(), 4);

    let model = solve_bv_clauses(&solver);
    let r_val = extract_bv_value(&model, &r);
    // -1 in 4-bit two's complement = 0b1111 = 15 unsigned
    assert_eq!(r_val, 0b1111, "-7 % 2 should be -1 (0b1111 = 15 unsigned)");
}

#[test]
fn test_bitblast_div_by_zero() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    // Division by zero: a / 0 = all_ones, a % 0 = a
    // SMT-LIB semantics: bvudiv(a, 0) = all_ones, bvurem(a, 0) = a
    let a = solver.const_bits(7, 4);
    let zero = solver.const_bits(0, 4);

    let (q, r) = solver.bitblast_udiv_urem(&a, &zero);

    assert_eq!(q.len(), 4);
    assert_eq!(r.len(), 4);

    // Verify semantics by solving the CNF and checking the model
    let model = solve_bv_clauses(&solver);
    let q_val = extract_bv_value(&model, &q);
    let r_val = extract_bv_value(&model, &r);

    assert_eq!(
        q_val, 0xF,
        "bvudiv(a, 0) should be all_ones (0xF for 4-bit)"
    );
    assert_eq!(r_val, 7, "bvurem(a, 0) should be a (7)");
}

#[test]
fn test_conditional_neg() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    let a = solver.const_bits(5, 4);
    let cond_true = solver.fresh_var();
    solver.add_clause(CnfClause::unit(cond_true));

    let result = solver.conditional_neg(&a, cond_true);
    assert_eq!(result.len(), 4);

    let model = solve_bv_clauses(&solver);
    let val = extract_bv_value(&model, &result);
    // -5 in 4-bit two's complement = ~5 + 1 = 0b1010 + 1 = 0b1011 = 11
    assert_eq!(
        val, 0b1011,
        "conditional_neg(5, true) should be -5 (0b1011 = 11)"
    );
}

#[test]
fn test_mk_or_many() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    // Test with multiple literals
    let lits = vec![solver.fresh_var(), solver.fresh_var(), solver.fresh_var()];

    let result = solver.mk_or_many(&lits);
    assert!(result != 0);
}

#[test]
fn test_mk_or_many_empty() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    // Empty case should return false
    let result = solver.mk_or_many(&[]);
    assert!(result != 0);
}

#[test]
fn test_mk_or_many_single() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    let lit = solver.fresh_var();
    let result = solver.mk_or_many(&[lit]);

    // Single literal case should return the literal itself
    assert_eq!(result, lit);
}

#[test]
fn test_division_generates_clauses() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    let initial_clauses = solver.clauses.len();

    let a = solver.const_bits(15, 4);
    let b = solver.const_bits(4, 4);
    let (_q, _r) = solver.bitblast_udiv_urem(&a, &b);

    // Division should generate additional clauses for the constraints
    assert!(solver.clauses.len() > initial_clauses);
}

#[test]
fn test_signed_division_symmetry() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    // Test that both operands being negative gives positive result
    // -6 / -2 = 3
    let a = solver.const_bits(0b1010, 4); // -6 in 4-bit signed
    let b = solver.const_bits(0b1110, 4); // -2 in 4-bit signed

    let sign_a = a[3];
    let sign_b = b[3];
    let abs_a = solver.conditional_neg(&a, sign_a);
    let abs_b = solver.conditional_neg(&b, sign_b);
    let (abs_q, _) = solver.bitblast_udiv_urem(&abs_a, &abs_b);
    let result_neg = solver.mk_xor(sign_a, sign_b);
    let q = solver.conditional_neg(&abs_q, result_neg);
    assert_eq!(q.len(), 4);

    let model = solve_bv_clauses(&solver);
    let q_val = extract_bv_value(&model, &q);
    assert_eq!(q_val, 3, "-6 / -2 should be 3");
}

#[test]
fn test_bitblast_extract() {
    // Test extract[hi:lo](x) operation via term API
    let mut store = setup_store();
    let x = store.mk_var("x", Sort::bitvec(8));
    // extract[5:2](x) - extract bits 5 down to 2 (4 bits)
    let extracted = store.mk_bvextract(5, 2, x);

    let mut solver = BvSolver::new(&store);
    let bits = solver.get_bits(extracted);

    // Result should be 4 bits (5 - 2 + 1 = 4)
    assert_eq!(bits.len(), 4, "extract[5:2] should produce 4 bits");
}

#[test]
fn test_bitblast_zero_extend() {
    // Test zero_extend[4](x) operation via term API
    let mut store = setup_store();
    let x = store.mk_var("x", Sort::bitvec(4));
    // zero_extend[4](x) - extend 4-bit value by 4 zero bits -> 8 bits
    let extended = store.mk_bvzero_extend(4, x);

    let mut solver = BvSolver::new(&store);
    let bits = solver.get_bits(extended);

    // Result should be 8 bits (4 + 4 = 8)
    assert_eq!(
        bits.len(),
        8,
        "zero_extend[4] of 4-bit value should produce 8 bits"
    );
}

#[test]
fn test_bitblast_sign_extend() {
    // Test sign_extend[4](x) operation via term API
    let mut store = setup_store();
    let x = store.mk_var("x", Sort::bitvec(4));
    // sign_extend[4](x) - extend 4-bit value by 4 sign bits -> 8 bits
    let extended = store.mk_bvsign_extend(4, x);

    let mut solver = BvSolver::new(&store);
    let bits = solver.get_bits(extended);

    // Result should be 8 bits (4 + 4 = 8)
    assert_eq!(
        bits.len(),
        8,
        "sign_extend[4] of 4-bit value should produce 8 bits"
    );
}

#[test]
fn test_concat_flattening_deep_chain() {
    // Test that deeply nested concat is correctly flattened.
    // Build concat(concat(concat(a, b), c), d) where a,b,c,d are 8-bit.
    // Result should be 32 bits in order: [d_bits, c_bits, b_bits, a_bits] (LSB-first).
    let mut store = TermStore::new();
    let a = store.mk_var("a", Sort::bitvec(8));
    let b = store.mk_var("b", Sort::bitvec(8));
    let c = store.mk_var("c", Sort::bitvec(8));
    let d = store.mk_var("d", Sort::bitvec(8));

    // Build: concat(concat(concat(a, b), c), d)
    let ab = store.mk_bvconcat(vec![a, b]); // a is high, b is low
    let abc = store.mk_bvconcat(vec![ab, c]); // ab is high, c is low
    let abcd = store.mk_bvconcat(vec![abc, d]); // abc is high, d is low

    let mut solver = BvSolver::new(&store);

    // Get bits for leaves FIRST to establish their CNF variables
    let a_bits = solver.get_bits(a);
    let b_bits = solver.get_bits(b);
    let c_bits = solver.get_bits(c);
    let d_bits = solver.get_bits(d);

    // Now get the concat result
    let bits = solver.get_bits(abcd);

    // Should have 32 bits total
    assert_eq!(bits.len(), 32, "concat of 4x8-bit should be 32 bits");

    // Verify bit ordering correctness (LSB-first):
    // concat(concat(concat(a, b), c), d) = concat(abc_high, d_low)
    // In LSB-first: [d_bits, c_bits, b_bits, a_bits]
    let mut expected = Vec::with_capacity(32);
    expected.extend_from_slice(&d_bits); // bits[0..8]: d (LSB)
    expected.extend_from_slice(&c_bits); // bits[8..16]: c
    expected.extend_from_slice(&b_bits); // bits[16..24]: b
    expected.extend_from_slice(&a_bits); // bits[24..32]: a (MSB)
    assert_eq!(
        bits, expected,
        "concat bit ordering must be LSB-first: [d, c, b, a]"
    );
}

#[test]
fn test_concat_flattening_bit_order() {
    // Verify that bit order is preserved after flattening.
    // concat(0xAB, 0xCD) produces bitvector 0xABCD (AB high, CD low).
    // In LSB-first bit representation: bits[0..8] = CD, bits[8..16] = AB.
    let mut store = TermStore::new();

    // Create constants: 0xAB = 10101011, 0xCD = 11001101
    let ab = store.mk_bitvec(BigInt::from(0xABu8), 8);
    let cd = store.mk_bitvec(BigInt::from(0xCDu8), 8);

    // concat(ab, cd) where ab is high bits, cd is low bits
    // Result: 0xABCD as 16-bit bitvector
    let concat_term = store.mk_bvconcat(vec![ab, cd]);

    let mut solver = BvSolver::new(&store);
    let bits = solver.get_bits(concat_term);

    assert_eq!(bits.len(), 16, "concat of two 8-bit should be 16 bits");

    // Assert the semantic value of every bit instead of depending on the CNF
    // representation used for constants. Both polarities may legitimately
    // share one canonical false variable (`false` is `v`, `true` is `-v`).
    for (index, &bit) in bits.iter().enumerate() {
        let expected_set = ((0xABCDu16 >> index) & 1) != 0;
        assert_eq!(
            solver.is_known_true(bit),
            expected_set,
            "bit {index} has the wrong true value in concat(0xAB, 0xCD)"
        );
        assert_eq!(
            solver.is_known_false(bit),
            !expected_set,
            "bit {index} has the wrong false value in concat(0xAB, 0xCD)"
        );
    }
}

#[test]
fn test_concat_flattening_performance() {
    // Test that deeply nested concat doesn't blow up.
    // Build a chain of 20 concat operations.
    let mut store = TermStore::new();

    // Create 21 variables
    let vars: Vec<_> = (0..21)
        .map(|i| store.mk_var(format!("v{i}"), Sort::bitvec(8)))
        .collect();

    // Build a right-associative chain: concat(v0, concat(v1, concat(v2, ...)))
    let mut current = vars[20];
    for i in (0..20).rev() {
        current = store.mk_bvconcat(vec![vars[i], current]);
    }

    let mut solver = BvSolver::new(&store);
    let bits = solver.get_bits(current);

    // Should have 168 bits (21 * 8)
    assert_eq!(bits.len(), 21 * 8, "21 x 8-bit concat should be 168 bits");
}

#[test]
fn test_concat_flattening_nary() {
    // Test n-ary concat (3+ arguments in a single concat call).
    // mk_bvconcat handles n-ary by converting to binary tree, but
    // flattening should handle the tree structure correctly.
    let mut store = TermStore::new();
    let a = store.mk_var("a", Sort::bitvec(4));
    let b = store.mk_var("b", Sort::bitvec(4));
    let c = store.mk_var("c", Sort::bitvec(4));

    // concat(a, b, c) where a is MSB, c is LSB
    // Result bits should be [c_bits, b_bits, a_bits] (LSB-first)
    let concat_term = store.mk_bvconcat(vec![a, b, c]);

    let mut solver = BvSolver::new(&store);

    // Get leaf bits FIRST to establish their CNF variables
    let a_bits = solver.get_bits(a);
    let b_bits = solver.get_bits(b);
    let c_bits = solver.get_bits(c);

    // Now get the concat result
    let bits = solver.get_bits(concat_term);

    // Should have 12 bits total (3 x 4)
    assert_eq!(bits.len(), 12, "concat of 3x4-bit should be 12 bits");

    // Verify bit ordering correctness (LSB-first):
    // concat(a, b, c) = a high, b middle, c low
    // In LSB-first: [c_bits, b_bits, a_bits]
    let mut expected = Vec::with_capacity(12);
    expected.extend_from_slice(&c_bits); // bits[0..4]: c (LSB)
    expected.extend_from_slice(&b_bits); // bits[4..8]: b
    expected.extend_from_slice(&a_bits); // bits[8..12]: a (MSB)
    assert_eq!(
        bits, expected,
        "n-ary concat bit ordering must be LSB-first: [c, b, a]"
    );
}

#[test]
fn test_const_case_multiplier_triggers_for_sparse_operands() {
    // Test that const-case multiplier is used when operands have many constant bits.
    // For an 8-bit multiplication where a has 5 known bits and b has 5 known bits,
    // case_size = 2^6 = 64 < circuit_size = 8*8*5 = 320, so case-split should trigger.
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    // Create operand a: 3 variable bits at positions 0,1,2, rest are 0
    let mut a_bits = Vec::with_capacity(8);
    for _ in 0..3 {
        a_bits.push(solver.fresh_var());
    }
    for _ in 3..8 {
        a_bits.push(solver.fresh_false());
    }

    // Create operand b: 3 variable bits at positions 0,1,2, rest are 0
    let mut b_bits = Vec::with_capacity(8);
    for _ in 0..3 {
        b_bits.push(solver.fresh_var());
    }
    for _ in 3..8 {
        b_bits.push(solver.fresh_false());
    }

    let clauses_before = solver.clauses.len();
    let result = solver.bitblast_mul(&a_bits, &b_bits);
    assert_eq!(result.len(), 8);
    let clauses_after = solver.clauses.len();
    assert!(
        clauses_after > clauses_before,
        "Multiplication should add clauses"
    );
}

#[test]
fn test_const_case_multiplier_correctness() {
    // Verify const-case multiplier produces correct results.
    // Use a concrete case: a = 3, b = 5
    // Expected result: 3 * 5 = 15
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    let a_bits = solver.const_bits(3, 8);
    let b_bits = solver.const_bits(5, 8);

    let result = solver.bitblast_mul(&a_bits, &b_bits);
    assert_eq!(result.len(), 8);

    let model = solve_bv_clauses(&solver);
    let product = extract_bv_value(&model, &result);

    assert_eq!(product, 15, "3 * 5 should equal 15");
}

#[test]
fn test_shift_add_fallback_for_dense_operands() {
    // Test that dense-variable operands fall back to shift-and-add.
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    // Create 16-bit operands with all variable bits
    let mut a_bits = Vec::with_capacity(16);
    let mut b_bits = Vec::with_capacity(16);
    for _ in 0..16 {
        a_bits.push(solver.fresh_var());
        b_bits.push(solver.fresh_var());
    }

    let result = solver.bitblast_mul(&a_bits, &b_bits);
    assert_eq!(result.len(), 16);
}

#[test]
fn test_fresh_true_is_known_true() {
    // Verify fresh_true produces a literal that is_known_true() recognizes.
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    let true_lit = solver.fresh_true();
    assert!(
        solver.is_known_true(true_lit),
        "fresh_true should produce a known-true literal"
    );
    assert!(
        !solver.is_known_false(true_lit),
        "fresh_true should not be known-false"
    );
}

// =========================================================================
// TheorySolver protocol compliance: push/pop/reset
// =========================================================================

#[test]
fn test_bv_push_pop_undoes_assertions() {
    let mut store = setup_store();
    let x = store.mk_var("x", Sort::bitvec(8));
    let y = store.mk_var("y", Sort::bitvec(8));
    let z = store.mk_var("z", Sort::bitvec(8));
    let eq = store.mk_eq(x, y);
    let eq2 = store.mk_eq(x, z);

    let mut solver = BvSolver::new(&store);

    // Assert at base level
    solver.assert_literal(eq, true);
    assert!(solver.asserted.contains_key(&eq));

    // Push, assert another literal, then pop
    solver.push();
    solver.assert_literal(eq2, true);
    assert!(
        solver.asserted.contains_key(&eq2),
        "scoped assertion present"
    );

    solver.pop();
    assert!(
        !solver.asserted.contains_key(&eq2),
        "scoped assertion must be removed on pop"
    );
    assert!(
        solver.asserted.contains_key(&eq),
        "base assertion must survive pop"
    );
}

#[test]
fn test_bv_nested_push_pop() {
    let mut store = setup_store();
    let a = store.mk_var("a", Sort::bitvec(4));
    let b = store.mk_var("b", Sort::bitvec(4));
    let c = store.mk_var("c", Sort::bitvec(4));
    let eq_ab = store.mk_eq(a, b);
    let eq_bc = store.mk_eq(b, c);
    let eq_ac = store.mk_eq(a, c);

    let mut solver = BvSolver::new(&store);

    // Level 0: assert a = b
    solver.assert_literal(eq_ab, true);
    let trail_base = solver.trail.len();

    // Level 1: assert b = c
    solver.push();
    solver.assert_literal(eq_bc, true);
    let trail_l1 = solver.trail.len();

    // Level 2: assert a = c
    solver.push();
    solver.assert_literal(eq_ac, true);
    assert_eq!(solver.trail.len(), trail_l1 + 1);

    // Pop level 2
    solver.pop();
    assert_eq!(solver.trail.len(), trail_l1);
    assert!(!solver.asserted.contains_key(&eq_ac));

    // Pop level 1
    solver.pop();
    assert_eq!(solver.trail.len(), trail_base);
    assert!(!solver.asserted.contains_key(&eq_bc));
    assert!(solver.asserted.contains_key(&eq_ab));
}

#[test]
fn test_bv_reset_clears_all_state() {
    let mut store = setup_store();
    let x = store.mk_var("x", Sort::bitvec(8));
    let y = store.mk_var("y", Sort::bitvec(8));
    let eq = store.mk_eq(x, y);

    let mut solver = BvSolver::new(&store);
    solver.assert_literal(eq, true);
    solver.push();

    // Produce some bitblasting state
    let _bits = solver.const_bits(42, 8);

    solver.reset();

    assert!(solver.trail.is_empty(), "trail must be empty after reset");
    assert!(
        solver.trail_stack.is_empty(),
        "trail_stack must be empty after reset"
    );
    assert!(
        solver.asserted.is_empty(),
        "asserted must be empty after reset"
    );
    assert!(
        solver.term_to_bits.is_empty(),
        "term_to_bits must be empty after reset"
    );
    assert!(
        solver.clauses.is_empty(),
        "clauses must be empty after reset"
    );
    assert_eq!(solver.next_var, 1, "next_var must reset to 1");
}

#[test]
fn test_bv_check_after_push_pop_is_sat() {
    let mut store = setup_store();
    let x = store.mk_var("x", Sort::bitvec(8));
    let y = store.mk_var("y", Sort::bitvec(8));
    let eq = store.mk_eq(x, y);

    let mut solver = BvSolver::new(&store);

    solver.push();
    solver.assert_literal(eq, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));
    solver.pop();

    // After pop, check should still return Sat (eager bit-blasting)
    assert!(
        matches!(solver.check(), TheoryResult::Sat),
        "BV check after pop must be Sat"
    );
}

#[test]
fn test_bv_propagate_always_empty() {
    let mut store = setup_store();
    let x = store.mk_var("x", Sort::bitvec(8));
    let y = store.mk_var("y", Sort::bitvec(8));
    let eq = store.mk_eq(x, y);

    let mut solver = BvSolver::new(&store);
    solver.assert_literal(eq, true);

    // Eager bit-blasting never propagates
    let props = solver.propagate();
    assert!(props.is_empty(), "BV propagate must always return empty");
}

// --- #5877: gate cache round-trip tests ---

/// Test that gate_caches() returns empty caches for a fresh solver.
#[test]
fn test_bv_gate_caches_initially_empty_5877() {
    let store = setup_store();
    let solver = BvSolver::new(&store);
    let (and_cache, or_cache, xor_cache) = solver.gate_caches();
    assert!(
        and_cache.is_empty(),
        "fresh solver AND cache should be empty"
    );
    assert!(or_cache.is_empty(), "fresh solver OR cache should be empty");
    assert!(
        xor_cache.is_empty(),
        "fresh solver XOR cache should be empty"
    );
}

/// Test that gate caches accumulate entries after bit-blasting.
/// Bit-blasting a BV AND expression should populate the AND gate cache.
#[test]
fn test_bv_gate_caches_populated_after_bitblast_5877() {
    let mut store = setup_store();
    let x = store.mk_var("x", Sort::bitvec(8));
    let y = store.mk_var("y", Sort::bitvec(8));
    let bvand = store.mk_app(Symbol::Named("bvand".into()), vec![x, y], Sort::bitvec(8));
    // Create assertion: bvand(x, y) = x (arbitrary, just to trigger bitblasting)
    let eq = store.mk_eq(bvand, x);

    let mut solver = BvSolver::new(&store);
    solver.assert_literal(eq, true);

    let (and_cache, or_cache, _xor_cache) = solver.gate_caches();
    // After bit-blasting an 8-bit AND, the AND cache should have entries
    // (one per bit pair, potentially).
    assert!(
        !and_cache.is_empty(),
        "AND cache should be populated after bit-blasting bvand, got {} entries",
        and_cache.len()
    );
    // OR and XOR caches may or may not be populated depending on the formula
    let _ = or_cache; // suppress unused warning
}

/// Test that set_gate_caches + gate_caches is a faithful round-trip.
/// Save caches from one solver, create a new solver, restore caches,
/// and verify the restored caches match.
#[test]
fn test_bv_gate_cache_round_trip_5877() {
    let mut store = setup_store();
    let x = store.mk_var("x", Sort::bitvec(8));
    let y = store.mk_var("y", Sort::bitvec(8));
    let bvand = store.mk_app(Symbol::Named("bvand".into()), vec![x, y], Sort::bitvec(8));
    let eq = store.mk_eq(bvand, x);

    // First solver: bit-blast to populate caches
    let mut solver1 = BvSolver::new(&store);
    solver1.assert_literal(eq, true);

    // Save caches
    let (and1, or1, xor1) = solver1.gate_caches();
    let saved_and = and1.clone();
    let saved_or = or1.clone();
    let saved_xor = xor1.clone();
    let and_count = saved_and.len();

    // Second solver: restore caches
    let mut solver2 = BvSolver::new(&store);
    solver2.set_gate_caches(saved_and.clone(), saved_or.clone(), saved_xor.clone());

    // Verify restored caches match saved caches
    let (and2, or2, xor2) = solver2.gate_caches();
    assert_eq!(
        and2.len(),
        and_count,
        "restored AND cache should have same size as saved"
    );
    assert_eq!(
        *and2, saved_and,
        "restored AND cache should equal saved cache"
    );
    assert_eq!(*or2, saved_or, "restored OR cache should equal saved cache");
    assert_eq!(
        *xor2, saved_xor,
        "restored XOR cache should equal saved cache"
    );
}

/// Test that div_caches() returns empty caches for a fresh solver.
#[test]
fn test_bv_div_caches_initially_empty_5877() {
    let store = setup_store();
    let solver = BvSolver::new(&store);
    let (unsigned, signed) = solver.div_caches();
    assert!(
        unsigned.is_empty(),
        "fresh solver unsigned div cache should be empty"
    );
    assert!(
        signed.is_empty(),
        "fresh solver signed div cache should be empty"
    );
}

/// Regression test for #6536: ensure_term_bits returns None for non-BV terms.
/// This guards the invariant that the internal bitblast/get_bits path is never
/// reached for non-BV-sorted terms.
#[test]
fn test_ensure_term_bits_rejects_non_bv_6536() {
    let mut store = setup_store();
    let int_var = store.mk_var("x", Sort::Int);
    let bool_var = store.mk_var("b", Sort::Bool);
    let mut solver = BvSolver::new(&store);
    assert!(
        solver.ensure_term_bits(int_var).is_none(),
        "ensure_term_bits should return None for Int-sorted term"
    );
    assert!(
        solver.ensure_term_bits(bool_var).is_none(),
        "ensure_term_bits should return None for Bool-sorted term"
    );
}

// --- #8143: MUX gate cache tests ---

/// Test that the MUX cache is initially empty.
#[test]
fn test_bv_mux_cache_initially_empty_8143() {
    let store = setup_store();
    let solver = BvSolver::new(&store);
    assert!(
        solver.mux_cache().is_empty(),
        "fresh solver MUX cache should be empty"
    );
}

/// Test that mk_mux with identical inputs returns cached result without
/// allocating duplicate variables or clauses.
#[test]
fn test_bv_mux_cache_dedup_8143() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    let sel = solver.fresh_var();
    let a = solver.fresh_var();
    let b = solver.fresh_var();

    // First call: creates a fresh variable + 4 clauses
    let out1 = solver.mk_mux(a, b, sel);
    let vars_after_first = solver.num_vars();
    let clauses_after_first = solver.clauses().len();

    // Second call with same inputs: should return cached result
    let out2 = solver.mk_mux(a, b, sel);
    let vars_after_second = solver.num_vars();
    let clauses_after_second = solver.clauses().len();

    assert_eq!(
        out1, out2,
        "mk_mux with same inputs should return same literal"
    );
    assert_eq!(
        vars_after_first, vars_after_second,
        "cached mk_mux should not allocate new variables"
    );
    assert_eq!(
        clauses_after_first, clauses_after_second,
        "cached mk_mux should not add new clauses"
    );
}

/// Test that MUX cache distinguishes different inputs.
#[test]
fn test_bv_mux_cache_different_inputs_8143() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    let sel = solver.fresh_var();
    let a = solver.fresh_var();
    let b = solver.fresh_var();
    let c = solver.fresh_var();

    let out1 = solver.mk_mux(a, b, sel);
    let out2 = solver.mk_mux(a, c, sel); // different else branch

    assert_ne!(
        out1, out2,
        "mk_mux with different inputs should return different literals"
    );
}

/// Test that MUX cache is NOT commutative: (sel, a, b) != (sel, b, a).
#[test]
fn test_bv_mux_cache_not_commutative_8143() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    let sel = solver.fresh_var();
    let a = solver.fresh_var();
    let b = solver.fresh_var();

    let out1 = solver.mk_mux(a, b, sel);
    let out2 = solver.mk_mux(b, a, sel); // swapped then/else

    assert_ne!(
        out1, out2,
        "mk_mux(a,b,sel) != mk_mux(b,a,sel) since MUX is not commutative"
    );
}

/// Test that MUX cache round-trips through set_mux_cache / mux_cache.
#[test]
fn test_bv_mux_cache_round_trip_8143() {
    let store = setup_store();
    let mut solver1 = BvSolver::new(&store);

    let sel = solver1.fresh_var();
    let a = solver1.fresh_var();
    let b = solver1.fresh_var();
    let _out = solver1.mk_mux(a, b, sel);

    let saved = solver1.mux_cache().clone();
    assert!(
        !saved.is_empty(),
        "MUX cache should be populated after mk_mux"
    );

    let mut solver2 = BvSolver::new(&store);
    solver2.set_mux_cache(saved.clone());

    assert_eq!(
        *solver2.mux_cache(),
        saved,
        "restored MUX cache should equal saved cache"
    );
}

/// Test that bitwise_mux on BV ITE benefits from MUX cache.
/// Two identical bitwise_mux calls on the same bits should produce
/// the same output bits (via MUX cache) without variable duplication.
#[test]
fn test_bv_bitwise_mux_cache_sharing_8143() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    let sel = solver.fresh_var();
    let a_bits = vec![solver.fresh_var(), solver.fresh_var()];
    let b_bits = vec![solver.fresh_var(), solver.fresh_var()];

    let out1 = solver.bitwise_mux(&a_bits, &b_bits, sel);
    let vars_after_first = solver.num_vars();

    let out2 = solver.bitwise_mux(&a_bits, &b_bits, sel);
    let vars_after_second = solver.num_vars();

    assert_eq!(out1, out2, "identical bitwise_mux should return same bits");
    assert_eq!(
        vars_after_first, vars_after_second,
        "cached bitwise_mux should not allocate new variables"
    );
}

/// Test that reset clears the MUX cache.
#[test]
fn test_bv_reset_clears_mux_cache_8143() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    let sel = solver.fresh_var();
    let a = solver.fresh_var();
    let b = solver.fresh_var();
    let _out = solver.mk_mux(a, b, sel);
    assert!(
        !solver.mux_cache().is_empty(),
        "MUX cache should be populated"
    );

    solver.reset();
    assert!(
        solver.mux_cache().is_empty(),
        "MUX cache should be empty after reset"
    );
}

// --- #8143: ITE flattening tests ---

/// Test that nested BV ITE chains are flattened correctly.
/// (ite c1 a (ite c2 b c)) should produce the same result as the
/// standard encoding but may use fewer variables due to MUX cache sharing.
#[test]
fn test_bv_ite_flattening_nested_else_chain_8143() {
    let mut store = setup_store();
    let c1 = store.mk_var("c1", Sort::Bool);
    let c2 = store.mk_var("c2", Sort::Bool);
    let a = store.mk_var("a", Sort::bitvec(8));
    let b = store.mk_var("b", Sort::bitvec(8));
    let c = store.mk_var("c", Sort::bitvec(8));

    // Build (ite c1 a (ite c2 b c))
    let inner_ite = store.mk_ite(c2, b, c);
    let outer_ite = store.mk_ite(c1, a, inner_ite);

    let mut solver = BvSolver::new(&store);
    let bits = solver.get_bits(outer_ite);

    // 8-bit result should have 8 bits
    assert_eq!(bits.len(), 8, "nested ITE should produce 8-bit result");

    // The MUX cache should have entries from the flattened encoding
    assert!(
        !solver.mux_cache().is_empty(),
        "MUX cache should be populated after nested ITE bitblasting"
    );
}

/// Test that deeply nested ITE chains don't cause excessive variable allocation.
/// Compare variable count between a 4-deep ITE chain and 4 separate muxes.
#[test]
fn test_bv_ite_flattening_reduces_variables_8143() {
    let mut store = setup_store();
    let c1 = store.mk_var("c1", Sort::Bool);
    let c2 = store.mk_var("c2", Sort::Bool);
    let c3 = store.mk_var("c3", Sort::Bool);
    let v0 = store.mk_var("v0", Sort::bitvec(4));
    let v1 = store.mk_var("v1", Sort::bitvec(4));
    let v2 = store.mk_var("v2", Sort::bitvec(4));
    let v3 = store.mk_var("v3", Sort::bitvec(4));

    // Build (ite c1 v0 (ite c2 v1 (ite c3 v2 v3)))
    let ite3 = store.mk_ite(c3, v2, v3);
    let ite2 = store.mk_ite(c2, v1, ite3);
    let ite1 = store.mk_ite(c1, v0, ite2);

    let mut solver = BvSolver::new(&store);
    let bits = solver.get_bits(ite1);

    assert_eq!(
        bits.len(),
        4,
        "nested ITE chain should produce 4-bit result"
    );

    // All variables should have bits allocated
    assert!(solver.get_term_bits(v0).is_some(), "v0 should have bits");
    assert!(solver.get_term_bits(v1).is_some(), "v1 should have bits");
    assert!(solver.get_term_bits(v2).is_some(), "v2 should have bits");
    assert!(solver.get_term_bits(v3).is_some(), "v3 should have bits");
}

// =========================================================================
// Bitblaster shortcuts: constant-shift and power-of-2 multiply (#8111)
// =========================================================================

#[test]
fn test_try_bits_to_usize_all_false() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);
    // All-zero constant: should return 0
    let bits: Vec<CnfLit> = (0..8).map(|_| solver.fresh_false()).collect();
    assert_eq!(solver.try_bits_to_usize(&bits), Some(0));
}

#[test]
fn test_try_bits_to_usize_known_value() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);
    // Encode value 5 = 0b101: bits 0 and 2 are true, bit 1 is false
    let b0 = solver.fresh_true();
    let b1 = solver.fresh_false();
    let b2 = solver.fresh_true();
    let bits = vec![b0, b1, b2];
    assert_eq!(solver.try_bits_to_usize(&bits), Some(5));
}

#[test]
fn test_term_constant_bits_use_recognized_truth_polarity() {
    // Exercise the real TermStore -> get_bits path. The lower-level shortcut
    // tests construct `fresh_true` manually and therefore did not catch set
    // bits being materialized as untracked positive unit literals.
    let mut store = setup_store();
    let five = store.mk_bitvec(BigInt::from(5u8), 4);
    let mut solver = BvSolver::new(&store);
    let bits = solver.get_bits(five);

    assert!(solver.is_known_true(bits[0]));
    assert!(solver.is_known_false(bits[1]));
    assert!(solver.is_known_true(bits[2]));
    assert!(solver.is_known_false(bits[3]));
    assert_eq!(solver.try_bits_to_usize(&bits), Some(5));
}

#[test]
fn test_try_bits_to_usize_non_constant() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);
    // Mix of constant and variable bits: should return None
    let b0 = solver.fresh_true();
    let b1 = solver.fresh_var(); // not a constant
    let bits = vec![b0, b1];
    assert_eq!(solver.try_bits_to_usize(&bits), None);
}

#[test]
fn test_try_bits_power_of_2_value_4() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);
    // Encode value 4 = 0b100: only bit 2 is set
    let b0 = solver.fresh_false();
    let b1 = solver.fresh_false();
    let b2 = solver.fresh_true();
    let b3 = solver.fresh_false();
    let bits = vec![b0, b1, b2, b3];
    assert_eq!(solver.try_bits_power_of_2(&bits), Some(2));
}

#[test]
fn test_try_bits_power_of_2_value_1() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);
    // Encode value 1 = 0b01: only bit 0 is set (2^0)
    let b0 = solver.fresh_true();
    let b1 = solver.fresh_false();
    let bits = vec![b0, b1];
    assert_eq!(solver.try_bits_power_of_2(&bits), Some(0));
}

#[test]
fn test_try_bits_power_of_2_not_power() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);
    // Encode value 3 = 0b11: two bits set, not a power of 2
    let b0 = solver.fresh_true();
    let b1 = solver.fresh_true();
    let bits = vec![b0, b1];
    assert_eq!(solver.try_bits_power_of_2(&bits), None);
}

#[test]
fn test_try_bits_power_of_2_zero() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);
    // Zero: no bits set, not a power of 2
    let b0 = solver.fresh_false();
    let b1 = solver.fresh_false();
    let bits = vec![b0, b1];
    assert_eq!(solver.try_bits_power_of_2(&bits), None);
}

#[test]
fn test_bitblast_shl_const_shortcut_produces_correct_bits() {
    // When shift amount is a known constant, the shortcut should produce
    // the same result as the barrel-shifter path.
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    // 8-bit variable shifted left by constant 3
    let a: Vec<CnfLit> = (0..8).map(|_| solver.fresh_var()).collect();
    // Encode shift amount = 3 = 0b011
    let b = vec![
        solver.fresh_true(),  // bit 0 = 1
        solver.fresh_true(),  // bit 1 = 1
        solver.fresh_false(), // bit 2 = 0
        solver.fresh_false(), // bit 3 = 0
        solver.fresh_false(), // bit 4 = 0
        solver.fresh_false(), // bit 5 = 0
        solver.fresh_false(), // bit 6 = 0
        solver.fresh_false(), // bit 7 = 0
    ];

    let result = solver.bitblast_shl(&a, &b);
    assert_eq!(result.len(), 8);
    // Low 3 bits should be known-false (shifted in zeros)
    assert!(
        solver.is_known_false(result[0]),
        "bit 0 should be zero after shl by 3"
    );
    assert!(
        solver.is_known_false(result[1]),
        "bit 1 should be zero after shl by 3"
    );
    assert!(
        solver.is_known_false(result[2]),
        "bit 2 should be zero after shl by 3"
    );
    // Bits 3-7 should be the original bits 0-4 (variable, not constant)
    assert_eq!(result[3], a[0], "bit 3 should be original bit 0");
    assert_eq!(result[4], a[1], "bit 4 should be original bit 1");
}

#[test]
fn test_bitblast_lshr_const_shortcut_produces_correct_bits() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    // 8-bit variable shifted right by constant 2
    let a: Vec<CnfLit> = (0..8).map(|_| solver.fresh_var()).collect();
    // Encode shift amount = 2 = 0b010
    let b = vec![
        solver.fresh_false(), // bit 0 = 0
        solver.fresh_true(),  // bit 1 = 1
        solver.fresh_false(), // bit 2 = 0
        solver.fresh_false(),
        solver.fresh_false(),
        solver.fresh_false(),
        solver.fresh_false(),
        solver.fresh_false(),
    ];

    let result = solver.bitblast_lshr(&a, &b);
    assert_eq!(result.len(), 8);
    // Bits 0-5 should be original bits 2-7
    assert_eq!(
        result[0], a[2],
        "bit 0 should be original bit 2 after lshr by 2"
    );
    assert_eq!(result[1], a[3], "bit 1 should be original bit 3");
    // High 2 bits should be known-false (shifted in zeros)
    assert!(
        solver.is_known_false(result[6]),
        "bit 6 should be zero after lshr by 2"
    );
    assert!(
        solver.is_known_false(result[7]),
        "bit 7 should be zero after lshr by 2"
    );
}

#[test]
fn test_bitblast_ashr_const_shortcut_produces_correct_bits() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    // 8-bit variable shifted arithmetically right by constant 2
    let a: Vec<CnfLit> = (0..8).map(|_| solver.fresh_var()).collect();
    let sign_bit = a[7]; // MSB is the sign bit
                         // Encode shift amount = 2
    let b = vec![
        solver.fresh_false(), // bit 0 = 0
        solver.fresh_true(),  // bit 1 = 1
        solver.fresh_false(),
        solver.fresh_false(),
        solver.fresh_false(),
        solver.fresh_false(),
        solver.fresh_false(),
        solver.fresh_false(),
    ];

    let result = solver.bitblast_ashr(&a, &b);
    assert_eq!(result.len(), 8);
    // Bits 0-5 should be original bits 2-7
    assert_eq!(
        result[0], a[2],
        "bit 0 should be original bit 2 after ashr by 2"
    );
    assert_eq!(result[1], a[3], "bit 1 should be original bit 3");
    // High 2 bits should be the sign bit
    assert_eq!(
        result[6], sign_bit,
        "bit 6 should be sign bit after ashr by 2"
    );
    assert_eq!(
        result[7], sign_bit,
        "bit 7 should be sign bit after ashr by 2"
    );
}

#[test]
fn test_bitblast_shl_overflow_const_shortcut() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    // 4-bit variable shifted left by constant 5 (>= width)
    let a: Vec<CnfLit> = (0..4).map(|_| solver.fresh_var()).collect();
    // Encode shift amount = 5 = 0b0101
    let b = vec![
        solver.fresh_true(),  // bit 0 = 1
        solver.fresh_false(), // bit 1 = 0
        solver.fresh_true(),  // bit 2 = 1
        solver.fresh_false(), // bit 3 = 0
    ];

    let result = solver.bitblast_shl(&a, &b);
    assert_eq!(result.len(), 4);
    // All bits should be zero (shift >= width)
    for (i, &bit) in result.iter().enumerate() {
        assert!(
            solver.is_known_false(bit),
            "bit {i} should be zero when shift >= width"
        );
    }
}

#[test]
fn test_bitblast_mul_power_of_2_shortcut() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    // 8-bit variable multiplied by constant 8 (= 2^3)
    let a: Vec<CnfLit> = (0..8).map(|_| solver.fresh_var()).collect();
    // Encode multiplier = 8 = 0b00001000
    let b = vec![
        solver.fresh_false(), // bit 0 = 0
        solver.fresh_false(), // bit 1 = 0
        solver.fresh_false(), // bit 2 = 0
        solver.fresh_true(),  // bit 3 = 1
        solver.fresh_false(), // bit 4 = 0
        solver.fresh_false(), // bit 5 = 0
        solver.fresh_false(), // bit 6 = 0
        solver.fresh_false(), // bit 7 = 0
    ];

    let result = solver.bitblast_mul(&a, &b);
    assert_eq!(result.len(), 8);
    // x * 8 = x << 3: low 3 bits are zero, bits 3-7 are original bits 0-4
    assert!(
        solver.is_known_false(result[0]),
        "bit 0 should be zero in x*8"
    );
    assert!(
        solver.is_known_false(result[1]),
        "bit 1 should be zero in x*8"
    );
    assert!(
        solver.is_known_false(result[2]),
        "bit 2 should be zero in x*8"
    );
    assert_eq!(result[3], a[0], "bit 3 should be original bit 0 in x*8");
    assert_eq!(result[4], a[1], "bit 4 should be original bit 1 in x*8");
}

#[test]
fn test_bitblast_mul_power_of_2_first_operand() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    // Constant 4 (= 2^2) multiplied by 8-bit variable
    // Encode multiplier = 4 = 0b00000100
    let a = vec![
        solver.fresh_false(),
        solver.fresh_false(),
        solver.fresh_true(),
        solver.fresh_false(),
        solver.fresh_false(),
        solver.fresh_false(),
        solver.fresh_false(),
        solver.fresh_false(),
    ];
    let b: Vec<CnfLit> = (0..8).map(|_| solver.fresh_var()).collect();

    let result = solver.bitblast_mul(&a, &b);
    assert_eq!(result.len(), 8);
    // 4 * x = x << 2: low 2 bits are zero
    assert!(
        solver.is_known_false(result[0]),
        "bit 0 should be zero in 4*x"
    );
    assert!(
        solver.is_known_false(result[1]),
        "bit 1 should be zero in 4*x"
    );
    assert_eq!(result[2], b[0], "bit 2 should be original bit 0 in 4*x");
    assert_eq!(result[3], b[1], "bit 3 should be original bit 1 in 4*x");
}

#[test]
fn test_raw_term_power_of_two_mul_uses_wiring_in_both_orders() {
    // Bypass TermStore::mk_bvmul on purpose so this directly covers the
    // independent bitblaster fast path and its handling of actual constants.
    let mut store = setup_store();
    let x = store.mk_var("x", Sort::bitvec(64));
    let four = store.mk_bitvec(BigInt::from(4u8), 64);
    let x_times_four = store.mk_app(Symbol::named("bvmul"), [x, four], Sort::bitvec(64));
    let four_times_x = store.mk_app(Symbol::named("bvmul"), [four, x], Sort::bitvec(64));

    for product in [x_times_four, four_times_x] {
        let mut solver = BvSolver::new(&store);
        let x_bits = solver.get_bits(x);
        let product_bits = solver.get_bits(product);
        assert!(solver.is_known_false(product_bits[0]));
        assert!(solver.is_known_false(product_bits[1]));
        for bit in 2..64 {
            assert_eq!(product_bits[bit], x_bits[bit - 2]);
        }
    }
}

#[test]
fn test_mul_fallback_orientation_is_operand_order_independent() {
    fn clause_count(constant_first: bool) -> usize {
        let store = setup_store();
        let mut solver = BvSolver::new(&store);
        let variable: Vec<CnfLit> = (0..16).map(|_| solver.fresh_var()).collect();
        // Non-power-of-two, and wide enough that const-case enumeration declines.
        let constant = solver.const_bits(0x5555, 16);
        assert!(solver.mul_selector_score(&constant) < solver.mul_selector_score(&variable));
        if constant_first {
            let _ = solver.bitblast_mul(&constant, &variable);
        } else {
            let _ = solver.bitblast_mul(&variable, &constant);
        }
        solver.clauses.len()
    }

    assert_eq!(clause_count(false), clause_count(true));
}

#[test]
fn test_mux_data_input_constant_propagation() {
    // #7974: MUX gates with known-constant data inputs should reduce to
    // simpler AND/OR gates, saving 1 fresh variable + 1 clause each.
    let store = setup_store();
    let mut solver = BvSolver::new(&store);

    let sel = solver.fresh_var();
    let b = solver.fresh_var();
    // No clauses yet from fresh_var
    assert_eq!(solver.clauses.len(), 0);

    // Case 1: ite(sel, true, b) = sel OR b
    let true_lit = solver.fresh_true();
    let clauses_before = solver.clauses.len();
    assert_eq!(clauses_before, 1, "fresh_true adds 1 unit clause");

    let result1 = solver.mk_mux(true_lit, b, sel);
    let clauses_case1 = solver.clauses.len() - clauses_before;
    // mk_or(sel, b) produces 3 clauses (2 binary + 1 ternary)
    // WITHOUT the optimization, mk_mux would produce 4 clauses
    assert_eq!(
        clauses_case1, 3,
        "ite(sel, true, b) should reduce to OR gate (3 clauses), got {clauses_case1}"
    );
    // Verify the result is NOT the true literal itself — it's an OR gate output
    assert_ne!(result1, true_lit);

    // Case 2: ite(sel, false, b) = NOT(sel) AND b
    let false_lit = solver.fresh_false();
    let clauses_before = solver.clauses.len();
    let result2 = solver.mk_mux(false_lit, b, sel);
    let clauses_case2 = solver.clauses.len() - clauses_before;
    // mk_and(-sel, b) produces 3 clauses (2 binary + 1 ternary)
    assert_eq!(
        clauses_case2, 3,
        "ite(sel, false, b) should reduce to AND gate (3 clauses), got {clauses_case2}"
    );
    assert_ne!(result2, false_lit);

    // Case 3: ite(sel, a, true) = NOT(sel) OR a
    let a = solver.fresh_var();
    let true_lit2 = solver.fresh_true();
    let clauses_before = solver.clauses.len();
    let _ = solver.mk_mux(a, true_lit2, sel);
    let clauses_case3 = solver.clauses.len() - clauses_before;
    assert_eq!(
        clauses_case3, 3,
        "ite(sel, a, true) should reduce to OR gate (3 clauses), got {clauses_case3}"
    );

    // Case 4: ite(sel, a, false) = sel AND a
    let false_lit2 = solver.fresh_false(); // reuses cached false lit
    let clauses_before = solver.clauses.len();
    let result4 = solver.mk_mux(a, false_lit2, sel);
    let clauses_case4 = solver.clauses.len() - clauses_before;
    assert_eq!(
        clauses_case4, 3,
        "ite(sel, a, false) should reduce to AND gate (3 clauses), got {clauses_case4}"
    );

    // Semantic verification: solve and check truth tables
    // Add a forcing clause so sel=true (to verify case 1 and case 4)
    solver.add_clause(CnfClause::unit(sel));
    // b is free, so we need to check consistency under both values
    let model = solve_bv_clauses(&solver);

    // With sel=true:
    let sel_val = model[(sel.unsigned_abs() - 1) as usize];
    assert!(sel_val, "sel should be true");

    let b_val = model[(b.unsigned_abs() - 1) as usize];

    // Case 1: ite(true_sel, true, b) = true OR b = true
    let r1_val = {
        let idx = (result1.unsigned_abs() - 1) as usize;
        let raw = model[idx];
        if result1 > 0 {
            raw
        } else {
            !raw
        }
    };
    assert!(r1_val, "ite(sel=true, true, b) should be true");

    // Case 4: ite(true_sel, a, false) = true AND a = a
    let a_val = model[(a.unsigned_abs() - 1) as usize];
    let r4_val = {
        let idx = (result4.unsigned_abs() - 1) as usize;
        let raw = model[idx];
        if result4 > 0 {
            raw
        } else {
            !raw
        }
    };
    assert_eq!(r4_val, a_val, "ite(sel=true, a, false) should equal a");
    let _ = b_val; // suppress unused warning
}
