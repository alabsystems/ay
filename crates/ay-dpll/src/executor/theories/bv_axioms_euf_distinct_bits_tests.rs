// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::Sort;

fn offset(exec: &mut Executor, base: TermId, value: u128, width: u32) -> TermId {
    let constant = exec.ctx.terms.mk_bitvec(value.into(), width);
    // Preserve the original operation even for zero: the generator must keep
    // congruence for different source terms with equal encoded arguments.
    exec.ctx.terms.mk_app(
        Symbol::named("bvadd"),
        [base, constant],
        Sort::bitvec(width),
    )
}

fn pair_clauses(exec: &mut Executor, left: TermId, right: TermId, width: u32) -> usize {
    let first = exec
        .ctx
        .terms
        .mk_app(Symbol::named("memory"), [left], Sort::bitvec(8));
    let second = exec
        .ctx
        .terms
        .mk_app(Symbol::named("memory"), [right], Sort::bitvec(8));
    exec.ctx.assertions.extend([first, second]);
    let mut solver = BvSolver::new(&exec.ctx.terms);
    for term in [left, right, first, second] {
        assert!(solver.ensure_term_bits(term).is_some(), "width {width}");
    }
    let result = exec.generate_euf_bv_axioms_debug(&solver, solver.num_vars(), 0, false, &[]);
    assert!(result.bail.is_none());
    result.clauses.len()
}

#[test]
fn distinct_address_offsets_allocate_no_congruence_cnf() {
    for width in [8, 64, 128] {
        let mask = if width == 128 {
            u128::MAX
        } else {
            (1u128 << width) - 1
        };
        for (a, b) in [(0, 1), (8, 16), (mask - 79, mask - 71)] {
            let mut exec = Executor::new();
            let base = exec.ctx.terms.mk_var("sp", Sort::bitvec(width));
            let left = offset(&mut exec, base, a, width);
            let right = offset(&mut exec, base, b, width);
            assert_eq!(
                pair_clauses(&mut exec, left, right, width),
                0,
                "{width}: {a}/{b}"
            );
        }
    }
}

#[test]
fn equal_or_possibly_aliasing_addresses_retain_congruence() {
    for width in [8, 64, 128] {
        let mut exec = Executor::new();
        let base = exec.ctx.terms.mk_var("sp", Sort::bitvec(width));
        let same = offset(&mut exec, base, 0, width);
        assert_ne!(base, same);
        // Identical encoded addresses require only the two result
        // implications per bit, even at 128-bit address width.
        assert_eq!(pair_clauses(&mut exec, base, same, width), 16);

        let mut exec = Executor::new();
        let left = exec.ctx.terms.mk_var("sp", Sort::bitvec(width));
        let right = exec.ctx.terms.mk_var("other_sp", Sort::bitvec(width));
        assert!(pair_clauses(&mut exec, left, right, width) > 0);
    }
}

#[test]
fn ordinary_solver_preserves_offset_alias_and_distinct_address_verdicts() {
    for (body, expected) in [
        ("(distinct (memory sp) (memory (bvadd sp #x01)))", "sat"),
        ("(distinct (memory sp) (memory (bvadd sp #x00)))", "unsat"),
        (
            "(and (= sp #xff) (distinct (memory #x00) (memory (bvadd sp #x01))))",
            "unsat",
        ),
    ] {
        let text = format!("(set-logic QF_UFBV)\n(declare-const sp (_ BitVec 8))\n(declare-fun memory ((_ BitVec 8)) (_ BitVec 8))\n(assert {body})\n(check-sat)\n(exit)\n");
        let commands = ay_frontend::parse(&text).expect("original solver query");
        let mut exec = Executor::new();
        assert_eq!(
            exec.execute_all(&commands)
                .expect("ordinary solver execution"),
            [expected, "exit"]
        );
    }
}
