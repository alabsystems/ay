// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{
    generate_fc_axiom_clauses, CegarArrayBuild, CegarArrayCheck, Executor, FcAuditLits,
    FcConcreteSelect,
};
use crate::executor::theories::ChainSpend;
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{Sort, TermId, TermStore};
use ay_sat::{SatResult, Solver as SatSolver};
use num_bigint::BigInt;
use std::collections::BTreeMap;

/// A Bool-element select has no term bits; its value is the bit-blaster's
/// atom (offset into final numbering), else the skeleton's atom (already
/// final). A Bool term in neither map has no value to audit.
#[test]
fn bool_terms_resolve_to_their_single_atom_literal() {
    let mut terms = TermStore::new();
    let array_sort = Sort::array(Sort::bitvec(8), Sort::Bool);
    let array = terms.mk_var("a", array_sort);
    let index = terms.mk_var("i", Sort::bitvec(8));
    let blasted = terms.mk_select(array, index);
    let one = terms.mk_bitvec(BigInt::from(1), 8);
    let skeleton = terms.mk_select(array, one);
    let two = terms.mk_bitvec(BigInt::from(2), 8);
    let unencoded = terms.mk_select(array, two);

    let mut term_bits = HashMap::default();
    term_bits.insert(index, vec![1, -2, 3, 4, 5, 6, 7, 8]);
    let mut bv_bool_to_var = HashMap::default();
    bv_bool_to_var.insert(blasted, -9);
    let mut tseitin_term_to_var = BTreeMap::new();
    tseitin_term_to_var.insert(skeleton, 4u32);
    let var_offset = 10;
    let lits = FcAuditLits::new(
        &term_bits,
        &bv_bool_to_var,
        &tseitin_term_to_var,
        var_offset,
    );

    assert_eq!(
        lits.scalar_lits(&terms, index),
        Some(vec![11, -12, 13, 14, 15, 16, 17, 18])
    );
    assert_eq!(lits.scalar_lits(&terms, blasted), Some(vec![-19]));
    assert_eq!(lits.scalar_lits(&terms, skeleton), Some(vec![4]));
    assert_eq!(lits.scalar_lits(&terms, unencoded), None);
    assert_eq!(lits.scalar_lits(&terms, array), None);
}

/// A one-bit result pair yields the same shape the BitVec path produces:
/// per differing index bit an XOR definition, one eq_idx, and the two
/// implication clauses forcing the atoms equal under eq_idx.
#[test]
fn single_atom_results_get_fc_implications() {
    let mut next_var = 100;
    let clauses =
        generate_fc_axiom_clauses(&[1, 2], &[1, -3], &[7], &[-8], &[], &[], &mut next_var);
    // One differing index bit: 4 XOR clauses + 1 (eq -> !diff) + 1 (diff | eq)
    // + 2 value implications.
    assert_eq!(clauses.len(), 8);
    assert_eq!(next_var, 102);

    let mut next_var = 100;
    let identical =
        generate_fc_axiom_clauses(&[1, 2], &[1, 2], &[7], &[-8], &[], &[], &mut next_var);
    assert_eq!(identical.len(), 2);
    assert_eq!(next_var, 100);
}

#[test]
fn fc_refinement_checks_linear_edges_in_dense_alias_group() {
    // The old all-pairs scan exceeded MAX_PAIR_ATTEMPTS at 182 selects,
    // even though only the last select disagrees with the other 181.
    let mut group: Vec<_> = (0..182u32)
        .map(|i| FcConcreteSelect {
            select: TermId(i + 1),
            index_lits: vec![1],
            value_lits: vec![i as i32 + 2],
            index_value: BigInt::from(0u8),
            value: BigInt::from(u8::from(i == 181)),
        })
        .collect();
    let mut build = CegarArrayBuild {
        clauses: Vec::new(),
        next_var: 200,
        new_vars: 0,
        inspected_bits: 0,
        pair_attempts: 0,
        newly_covered: HashSet::default(),
        budget_exhausted: false,
    };

    assert!(Executor::new().append_fc_group_refinement(&group, &HashSet::default(), &mut build,));
    assert_eq!(build.pair_attempts, 181);
    assert_eq!(build.newly_covered.len(), 181);
    assert!(build
        .newly_covered
        .contains(&(TermId(1), TermId(182), Vec::new(), Vec::new())));
    assert!(build
        .newly_covered
        .contains(&(TermId(2), TermId(182), Vec::new(), Vec::new())));
    assert_eq!(build.clauses.len(), 362);

    for entry in &mut group {
        entry.value = BigInt::from(0u8);
    }
    build.clauses.clear();
    build.newly_covered.clear();
    build.pair_attempts = 0;
    assert!(Executor::new().append_fc_group_refinement(&group, &HashSet::default(), &mut build,));
    assert_eq!(build.pair_attempts, 0);
    assert_eq!(build.clauses, [] as [Vec<ay_sat::Literal>; 0]);
}

#[test]
fn fc_refinement_ignores_equal_cached_pair_but_rejects_violated_cached_pair() {
    let group: Vec<_> = [0u8, 0, 1, 2]
        .into_iter()
        .enumerate()
        .map(|(i, value)| FcConcreteSelect {
            select: TermId(i as u32 + 1),
            index_lits: vec![1],
            value_lits: vec![i as i32 * 2 + 2, i as i32 * 2 + 3],
            index_value: BigInt::from(0u8),
            value: BigInt::from(value),
        })
        .collect();
    let mut build = CegarArrayBuild {
        clauses: Vec::new(),
        next_var: 20,
        new_vars: 0,
        inspected_bits: 0,
        pair_attempts: 0,
        newly_covered: HashSet::default(),
        budget_exhausted: false,
    };
    let mut already_covered = HashSet::default();
    already_covered.insert((TermId(1), TermId(2), Vec::new(), Vec::new()));

    let mut executor = Executor::new();
    assert!(executor.append_fc_group_refinement(&group, &already_covered, &mut build));
    assert!(build
        .newly_covered
        .contains(&(TermId(1), TermId(3), Vec::new(), Vec::new())));
    assert!(build
        .newly_covered
        .contains(&(TermId(1), TermId(4), Vec::new(), Vec::new())));
    assert!(build
        .newly_covered
        .contains(&(TermId(2), TermId(3), Vec::new(), Vec::new())));
    assert_eq!(build.clauses.len(), 12);

    already_covered.insert((TermId(1), TermId(3), Vec::new(), Vec::new()));
    assert!(!executor.append_fc_group_refinement(&group, &already_covered, &mut build));
}

struct DenseFcFixture {
    executor: Executor,
    term_bits: HashMap<TermId, Vec<i32>>,
    solver: SatSolver,
}

impl DenseFcFixture {
    fn new(last_index: u8) -> Self {
        const READS: u32 = 182;
        let mut executor = Executor::new();
        let array = executor
            .ctx
            .terms
            .mk_var("dense_array", Sort::array(Sort::bitvec(1), Sort::bitvec(1)));
        let mut term_bits = HashMap::default();
        let mut solver = SatSolver::new((READS * 2) as usize);

        for i in 0..READS {
            let index_value = if i == READS - 1 { last_index } else { 0 };
            let read_value = u8::from(i == READS - 1);
            let index = executor
                .ctx
                .terms
                .mk_var(format!("dense_index_{i}"), Sort::bitvec(1));
            let select = executor.ctx.terms.mk_select(array, index);
            let index_constant = executor.ctx.terms.mk_bitvec(BigInt::from(index_value), 1);
            let value_constant = executor.ctx.terms.mk_bitvec(BigInt::from(read_value), 1);
            let index_assertion = executor.ctx.terms.mk_eq(index, index_constant);
            let value_assertion = executor.ctx.terms.mk_eq(select, value_constant);
            executor
                .ctx
                .assertions
                .extend([index_assertion, value_assertion]);

            let index_var = i as i32 + 1;
            let value_var = READS as i32 + index_var;
            term_bits.insert(index, vec![index_var]);
            term_bits.insert(select, vec![value_var]);
            let index_unit = if index_value == 1 {
                index_var
            } else {
                -index_var
            };
            let value_unit = if read_value == 1 {
                value_var
            } else {
                -value_var
            };
            assert!(solver.add_clause(vec![crate::cnf_lit_to_sat(index_unit)]));
            assert!(solver.add_clause(vec![crate::cnf_lit_to_sat(value_unit)]));
        }

        Self {
            executor,
            term_bits,
            solver,
        }
    }
}

#[test]
fn dense_equal_indices_refine_to_unsat_in_one_round() {
    let mut fixture = DenseFcFixture::new(0);
    let bool_lits = HashMap::default();
    let tseitin_lits = BTreeMap::new();
    let lits = FcAuditLits::new(&fixture.term_bits, &bool_lits, &tseitin_lits, 0);
    let initial = fixture.solver.solve().into_inner();
    let SatResult::Sat(ref model) = initial else {
        panic!("the unrefined bit-level constraints must be satisfiable");
    };
    let mut already_covered = HashSet::default();
    let audit =
        fixture
            .executor
            .check_array_fc_violations(model, &lits, &[], 364, &mut already_covered);
    let CegarArrayCheck::Refinement(batch) = audit else {
        panic!("dense equal-index group needs an FC refinement");
    };
    assert_eq!(already_covered.len(), 181);
    // Each syntactically distinct one-bit index pair needs one XOR variable,
    // one equality guard, and eight clauses for its guarded value equality.
    assert_eq!(batch.num_new_vars, 362);
    assert_eq!(batch.clauses.len(), 1448);

    let result = fixture.executor.refine_array_fc_model(
        initial,
        &lits,
        &[],
        364,
        &mut fixture.solver,
        16,
        &mut ChainSpend::default(),
    );
    assert!(matches!(result, SatResult::Unsat(_)));
    assert_eq!(
        fixture
            .executor
            .statistics()
            .get_int("smt.abv.array_fc_cegar.refinement_rounds"),
        Some(1)
    );
}

#[test]
fn dense_distinct_index_model_remains_sat_after_final_audit() {
    let mut fixture = DenseFcFixture::new(1);
    let bool_lits = HashMap::default();
    let tseitin_lits = BTreeMap::new();
    let lits = FcAuditLits::new(&fixture.term_bits, &bool_lits, &tseitin_lits, 0);
    let initial = fixture.solver.solve().into_inner();
    let SatResult::Sat(ref model) = initial else {
        panic!("the distinct-index bit-level constraints must be satisfiable");
    };
    assert!(matches!(
        fixture
            .executor
            .check_array_fc_violations(model, &lits, &[], 364, &mut HashSet::default()),
        CegarArrayCheck::Consistent
    ));

    let result = fixture.executor.refine_array_fc_model(
        initial,
        &lits,
        &[],
        364,
        &mut fixture.solver,
        16,
        &mut ChainSpend::default(),
    );
    let SatResult::Sat(model) = result else {
        panic!("different indices allow different array values");
    };
    assert!(matches!(
        fixture.executor.check_array_fc_violations(
            &model,
            &lits,
            &[],
            364,
            &mut HashSet::default()
        ),
        CegarArrayCheck::Consistent
    ));
    assert_eq!(
        fixture
            .executor
            .statistics()
            .get_int("smt.abv.array_fc_cegar.refinement_rounds"),
        Some(0)
    );
}

/// With guards, only the value-implication clauses gain the
/// negated guard literals; the diff/eq definitions (fresh
/// variables) stay unguarded equivalences.
#[test]
fn guarded_fc_clauses_carry_the_equality_guard() {
    // Same clause count as unguarded; the two value implications
    // (last two clauses) each gain exactly the two guard literals
    // and share their first (guard) literal.
    let mut plain_var = 100;
    let plain = generate_fc_axiom_clauses(&[1, 2], &[1, -3], &[7], &[-8], &[], &[], &mut plain_var);
    let mut next_var = 100;
    let guarded = generate_fc_axiom_clauses(
        &[1, 2],
        &[1, -3],
        &[7],
        &[-8],
        &[42, 43],
        &[],
        &mut next_var,
    );
    assert_eq!(guarded.len(), plain.len());
    let widened: Vec<usize> = guarded
        .iter()
        .zip(&plain)
        .enumerate()
        .filter(|(_, (g, p))| g.len() == p.len() + 2)
        .map(|(i, _)| i)
        .collect();
    assert_eq!(widened, vec![plain.len() - 2, plain.len() - 1]);
    assert_eq!(guarded[widened[0]][0], guarded[widened[1]][0]);
}

/// A stored index to avoid adds its own diff/eq definition
/// (one differing bit: 2 fresh vars, 6 clauses) and exactly
/// one extra literal — the POSITIVE eq literal, so the value
/// clauses are vacuous exactly when `idx_a` equals the stored
/// index — to each value implication. The clause/var counts
/// must match `budget::pair_cost` for the same inputs.
#[test]
fn stored_diseq_fc_clauses_carry_positive_eq_literal() {
    let stored = vec![vec![1, -9]];
    let mut next_var = 100;
    let clauses =
        generate_fc_axiom_clauses(&[1, 2], &[1, -3], &[7], &[-8], &[], &stored, &mut next_var);
    // Main pair: 8 clauses / 2 fresh vars (as unguarded above);
    // stored: 4 XOR + 1 (eq -> !diff) + 1 (diff | eq) = 6
    // clauses / 2 fresh vars. Fresh-var draw order is main
    // diff (100), stored diff (101), stored eq (102), main eq
    // (103), so the value clauses end the list and carry
    // +eq_stored as their extra literal.
    assert_eq!(clauses.len(), 14);
    assert_eq!(next_var, 104);
    let eq_stored = crate::cnf_lit_to_sat(102);
    let mut plain_var = 100;
    let plain = generate_fc_axiom_clauses(&[1, 2], &[1, -3], &[7], &[-8], &[], &[], &mut plain_var);
    for (with_s, without) in clauses[clauses.len() - 2..]
        .iter()
        .zip(&plain[plain.len() - 2..])
    {
        assert_eq!(with_s.len(), without.len() + 1);
        assert!(with_s.contains(&eq_stored));
    }
    assert_eq!(
        super::budget::pair_cost(&vec![1, 2], &vec![1, -3], &vec![7], &vec![-8], &stored),
        Some((4, 14))
    );
}
