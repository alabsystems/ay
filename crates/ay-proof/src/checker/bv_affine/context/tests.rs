// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn clause(terms: &mut TermStore, guard: TermId, left: TermId, right: TermId) -> TermId {
    let eq = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);
    let neq = terms.mk_not_raw(eq);
    let root = terms.mk_app(Symbol::named("and"), [guard, neq], Sort::Bool);
    terms.mk_not_raw(root)
}

fn accepted(terms: &TermStore, term: TermId) -> bool {
    context_identity(terms, &[term], &mut |_, _| true)
        .unwrap()
        .is_some()
}

#[test]
fn conditional_constants_match_exhaustive_guard_and_word_evaluation() {
    let mut cases = 0;
    for width in 1..=4 {
        let modulus = 1u128 << width;
        for dedicated in [false, true] {
            for flip in [false, true] {
                for yes in 0..modulus {
                    for no in 0..modulus {
                        let mut terms = TermStore::new();
                        let g = terms.mk_var("g", Sort::Bool);
                        let condition = if flip { terms.mk_not_raw(g) } else { g };
                        let y = terms.mk_bitvec(yes.into(), width);
                        let n = terms.mk_bitvec(no.into(), width);
                        let rhs = if dedicated {
                            terms.mk_ite_raw(condition, y, n)
                        } else {
                            terms.mk_app(
                                Symbol::named("ite"),
                                [condition, y, n],
                                Sort::bitvec(width),
                            )
                        };
                        let sum =
                            terms.mk_app(Symbol::named("bvadd"), [rhs, n], Sort::bitvec(width));
                        let left = terms.mk_bitvec(((yes + no) % modulus).into(), width);
                        let root = clause(&mut terms, g, left, sum);
                        let expected = [false, true].into_iter().all(|g| {
                            !g || (yes + no) % modulus
                                == ((if g != flip { yes } else { no }) + no) % modulus
                        });
                        assert_eq!(
                            accepted(&terms, root),
                            expected,
                            "width={width} dedicated={dedicated} flip={flip} yes={yes} no={no}"
                        );
                        cases += 1;
                    }
                }
            }
        }
    }
    assert_eq!(cases, 1360);
}

#[test]
fn validate_unused_conditional_branches_and_guards_before_reducing() {
    let mut terms = TermStore::new();
    let g = terms.mk_var("g", Sort::Bool);
    let x = terms.mk_var("x", Sort::bitvec(64));
    let other = terms.mk_var("other", Sort::bitvec(32));
    let zero = terms.mk_bitvec(0.into(), 64);
    let mut deep = x;
    for _ in 0..=MAX_DEPTH {
        deep = terms.mk_app(Symbol::named("bvadd"), [deep, zero], Sort::bitvec(64));
    }
    let mut wide = x;
    for _ in 0..12 {
        wide = terms.mk_app(Symbol::named("bvadd"), [wide, wide], Sort::bitvec(64));
    }
    let malformed = [
        terms.mk_app(Symbol::named("bvadd"), [x, other], Sort::bitvec(64)),
        terms.mk_app(Symbol::named("bvadd"), [x], Sort::bitvec(64)),
        terms.mk_app(Symbol::named("unmodeled"), [x], Sort::bitvec(64)),
        terms.mk_app(Symbol::named("ite"), [g, x], Sort::bitvec(64)),
        terms.mk_app(Symbol::named("ite"), [x, x, zero], Sort::bitvec(64)),
        deep,
        wide,
    ];
    for bad in malformed {
        let rhs = terms.mk_app(Symbol::named("ite"), [g, x, bad], Sort::bitvec(64));
        let root = clause(&mut terms, g, x, rhs);
        assert!(!accepted(&terms, root));
        let bad_guard = terms.mk_app(Symbol::named("="), [bad, bad], Sort::Bool);
        let guard = terms.mk_app(Symbol::named("and"), [g, bad_guard], Sort::Bool);
        let root = clause(&mut terms, guard, x, x);
        assert!(!accepted(&terms, root));
    }
    let rhs = terms.mk_ite_raw(g, x, zero);
    let root = clause(&mut terms, g, x, rhs);
    assert!(accepted(&terms, root));
    let mut charges = Vec::new();
    assert!(context_identity(&terms, &[root], &mut |work, bytes| {
        charges.push((work, bytes));
        false
    })
    .is_err());
    assert_eq!(charges, [(MAX_WORK, MAX_ALLOCATION)]);
    assert!(!accepted(&terms, TermId(u32::MAX)));
}

#[test]
fn guard_facts_do_not_escape_their_own_conjunction() {
    let mut terms = TermStore::new();
    let g = terms.mk_var("g", Sort::Bool);
    let h = terms.mk_var("h", Sort::Bool);
    let x = terms.mk_var("x", Sort::bitvec(64));
    let y = terms.mk_var("y", Sort::bitvec(64));
    let rhs = terms.mk_ite_raw(g, x, y);
    let good = clause(&mut terms, g, x, rhs);
    let unrelated = clause(&mut terms, h, x, rhs);
    assert!(accepted(&terms, good));
    assert!(!accepted(&terms, unrelated));
    assert!(accepted(&terms, good));
    assert!(!accepted(&terms, unrelated));
}
