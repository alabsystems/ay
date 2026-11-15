// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Actual ROW producer checks, independent finite CNF semantics, and public
//! strict-proof controls. No recorded proof entry or capability is fabricated.

use super::*;

#[derive(Clone, Copy, Debug)]
enum Indices {
    StoreConstant(u64),
    ReadConstant(u64),
    Symbolic,
}

struct Encoding {
    base: Vec<Vec<i32>>,
    rows: Vec<Vec<i32>>,
    base_variables: u32,
    row_variables: u32,
    offset: u32,
    store_index: Vec<i32>,
    read_index: Vec<i32>,
    selected: i32,
    stored: i32,
    read: Option<i32>,
}

fn encode(width: u32, indices: Indices, negative: bool, base_read: bool) -> Encoding {
    let mut executor = Executor::new();
    let terms = &mut executor.ctx.terms;
    let sort = Sort::bitvec(width);
    let array = terms.mk_var("a", Sort::array(sort.clone(), Sort::bitvec(1)));
    let symbol = terms.mk_var("symbolic index", sort.clone());
    let symbol = if negative {
        terms.mk_app(Symbol::named("bvnot"), [symbol], sort.clone())
    } else {
        symbol
    };
    let (i, j) = match indices {
        Indices::StoreConstant(value) => (terms.mk_bitvec(value.into(), width), symbol),
        Indices::ReadConstant(value) => (symbol, terms.mk_bitvec(value.into(), width)),
        Indices::Symbolic => (symbol, terms.mk_var("other index", sort)),
    };
    let value = terms.mk_var("stored value", Sort::bitvec(1));
    let store = terms.mk_store(array, i, value);
    // Preserve the residual syntax this bit-level producer consumes. Calling
    // mk_select here could discharge ROW before the tested producer runs.
    let selected = terms.mk_app(Symbol::named("select"), [store, j], Sort::bitvec(1));
    let mut roots = vec![selected];
    let read = base_read.then(|| {
        let read = terms.mk_app(Symbol::named("select"), [array, j], Sort::bitvec(1));
        roots.push(read);
        read
    });
    let mut bv = BvSolver::new(&executor.ctx.terms);
    for term in [i, j, value, selected].into_iter().chain(read) {
        assert!(bv.ensure_term_bits(term).is_some());
    }
    let offset = 7;
    let shift = |literal: i32| {
        if literal > 0 {
            literal + offset as i32
        } else {
            literal - offset as i32
        }
    };
    let bits = |term| {
        bv.get_term_bits(term)
            .unwrap()
            .iter()
            .copied()
            .map(shift)
            .collect::<Vec<_>>()
    };
    let store_index = bits(i);
    let read_index = bits(j);
    let selected = bits(selected)[0];
    let stored = bits(value)[0];
    let read = read.map(|term| bits(term)[0]);
    let base_variables = bv.num_vars();
    let base = bv
        .clauses()
        .iter()
        .map(|clause| clause.0.iter().copied().map(shift).collect())
        .collect();
    let result = executor.generate_array_bv_axioms(
        &bv,
        offset,
        offset + base_variables,
        &roots,
        &BTreeMap::new(),
        None,
    );
    Encoding {
        base,
        rows: result.clauses.into_iter().map(|clause| clause.0).collect(),
        base_variables,
        row_variables: result.num_vars,
        offset,
        store_index,
        read_index,
        selected,
        stored,
        read,
    }
}

fn literal_value(literal: i32, assignment: &[bool]) -> bool {
    assert_ne!(literal, 0);
    assignment[literal.unsigned_abs() as usize] == (literal > 0)
}

fn satisfied(clauses: &[Vec<i32>], assignment: &[bool]) -> bool {
    clauses.iter().all(|clause| {
        clause
            .iter()
            .any(|&literal| literal_value(literal, assignment))
    })
}

/// Independently compare existential auxiliary-CNF satisfiability with the
/// two ROW implications on every base assignment. Constant unit clauses from
/// the real BV encoder are part of the premises, not an oracle assumption.
fn check_row_semantics(encoding: &Encoding) {
    assert!(encoding.base_variables < 12);
    assert!(encoding.row_variables < 4);
    let first_auxiliary = encoding.offset + encoding.base_variables + 1;
    let mut assignment = vec![false; (first_auxiliary + encoding.row_variables) as usize];
    let mut checked = 0;
    for mask in 0..(1u32 << encoding.base_variables) {
        for bit in 0..encoding.base_variables {
            assignment[(encoding.offset + bit + 1) as usize] = mask & (1 << bit) != 0;
        }
        if !satisfied(&encoding.base, &assignment) {
            continue;
        }
        checked += 1;
        let equal_indices = encoding
            .store_index
            .iter()
            .zip(&encoding.read_index)
            .all(|(&i, &j)| literal_value(i, &assignment) == literal_value(j, &assignment));
        let selected = literal_value(encoding.selected, &assignment);
        let expected = if equal_indices {
            selected == literal_value(encoding.stored, &assignment)
        } else {
            encoding
                .read
                .is_none_or(|read| selected == literal_value(read, &assignment))
        };
        let mut admitted = false;
        for auxiliary in 0..(1u32 << encoding.row_variables) {
            for bit in 0..encoding.row_variables {
                assignment[(first_auxiliary + bit) as usize] = auxiliary & (1 << bit) != 0;
            }
            admitted |= satisfied(&encoding.rows, &assignment);
        }
        assert_eq!(admitted, expected, "base assignment {mask}");
    }
    assert!(checked > 0, "the real BV premises must be satisfiable");
}

#[test]
fn one_constant_index_matches_row_semantics_for_both_polarities_orders_and_signs() {
    for constant in 0..4 {
        for indices in [
            Indices::StoreConstant(constant),
            Indices::ReadConstant(constant),
        ] {
            for negative in [false, true] {
                for base_read in [false, true] {
                    let encoding = encode(2, indices, negative, base_read);
                    assert_eq!(encoding.row_variables, u32::from(base_read));
                    let symbolic = match indices {
                        Indices::StoreConstant(_) => &encoding.read_index,
                        _ => &encoding.store_index,
                    };
                    assert!(symbolic.iter().all(|&bit| (bit < 0) == negative));
                    check_row_semantics(&encoding);
                }
            }
        }
    }
}

#[test]
fn literal_bv64_index_removes_only_the_sixty_four_xor_gates() {
    for indices in [Indices::StoreConstant(0x35), Indices::ReadConstant(0x35)] {
        let encoding = encode(64, indices, false, true);
        // One-bit values: ROW1=2, summary=65, ROW2=2. The former
        // 64 fresh XORs / 256 defining clauses are absent, not just tautologies.
        assert_eq!(encoding.row_variables, 1);
        assert_eq!(encoding.rows.len(), 69);
        let missing = encode(64, indices, true, false);
        assert_eq!(missing.row_variables, 0);
        assert_eq!(missing.rows.len(), 2);
    }
}

#[test]
fn unknown_index_bits_keep_the_original_xor_encoding() {
    for negative in [false, true] {
        for base_read in [false, true] {
            let encoding = encode(2, Indices::Symbolic, negative, base_read);
            assert_eq!(encoding.row_variables, 2 + u32::from(base_read));
            assert_eq!(encoding.rows.len(), if base_read { 15 } else { 10 });
            // The independent oracle includes equal concrete assignments to
            // these unknown bits; candidate values never justify gate removal.
            check_row_semantics(&encoding);
        }
    }
}

// Complementary publication controls: normal preprocessing may discharge ROW
// before the bit-level emitter. Exact changed-emitter coverage and gate counts
// come from encode/check_row_semantics above, not from these public solves.
fn execute_row(extra: &str, expected: &str) {
    let input = format!(
        "(set-logic QF_ABV)
         (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
         (declare-const i (_ BitVec 8))
         (declare-const v (_ BitVec 8))
         {extra}"
    );
    let mut executor = Executor::new();
    executor.set_self_check(true);
    executor.set_produce_proofs(true);
    assert!(executor
        .execute_all(&ay_frontend::parse(&input).unwrap())
        .unwrap()
        .is_empty());
    let originals = executor.ctx.assertions.clone();
    executor.set_deadline(Some(
        ay_core::time::Instant::now() + std::time::Duration::from_secs(5),
    ));
    let output = executor
        .execute_all(&ay_frontend::parse("(check-sat)").unwrap())
        .unwrap();
    assert_eq!(output, [expected], "{input}");
    if expected == "unsat" {
        assert!(executor.last_command_unsat_was_strictly_verified());
        let proof = executor.last_proof().expect("actual strict ROW refutation");
        // The guarded BV collapse refutes the exact parsed source form, which
        // it re-interns raw where elaboration rewrote it
        // (`record_raw_authored_problem_assertion`). Over an 8-bit index it
        // publishes that refutation since the strict checker reads such an
        // array through its store chain, as it already did over a 16-bit one.
        let mut scope = originals;
        scope.extend(executor.last_proof_raw_original_assertions.iter().copied());
        ay_proof::validate_reachable_assumes_in_problem_scope(proof, &scope).unwrap();
        let quality = ay_proof::check_proof_strict(proof, executor.terms()).unwrap();
        assert!(quality.is_complete(), "{quality}");
        assert_eq!(quality.trust_count, 0);
    } else {
        assert!(executor.was_model_validated());
        assert!(executor.last_proof().is_none());
    }
}

#[test]
fn parsed_row_guards_retain_strict_original_source_proofs() {
    execute_row(
        "(assert (= i #x35))
         (assert (distinct (select (store a #x35 v) i) v))",
        "unsat",
    );
    execute_row(
        "(assert (distinct i #x35))
         (assert (distinct (select (store a #x35 v) i) (select a i)))",
        "unsat",
    );
}

#[test]
fn parsed_row_guards_do_not_turn_the_opposite_branches_into_axioms() {
    execute_row(
        "(assert (= i #x35))
         (assert (distinct v (select a i)))
         (assert (distinct (select (store a #x35 v) i) (select a i)))",
        "sat",
    );
    execute_row(
        "(assert (distinct i #x35))
         (assert (distinct (select a i) v))
         (assert (distinct (select (store a #x35 v) i) v))",
        "sat",
    );
}
