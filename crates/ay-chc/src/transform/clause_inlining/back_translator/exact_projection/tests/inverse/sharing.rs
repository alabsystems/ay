// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[derive(Clone, Copy)]
enum SharedContext {
    Negation,
    Equality,
    Conditional,
}

pub(super) fn alternatives(width: u32) -> (ChcExpr, Vec<ChcVar>) {
    let x = var("x", width);
    let r = var("r", width);
    let t = var("t", width);
    let flag = ChcVar::new("flag", ChcSort::Bool);
    let guard = op(ChcOp::BvULt, vec![expr(&x), ChcExpr::BitVec(1, width)]);
    let formula = op(
        ChcOp::And,
        vec![
            eq(expr(&flag), op(ChcOp::BvULt, vec![expr(&x), expr(&t)])),
            op(
                ChcOp::Or,
                vec![
                    op(
                        ChcOp::And,
                        vec![
                            eq(expr(&r), arithmetic(Form::AddLeft, expr(&x), expr(&t))),
                            guard.clone(),
                        ],
                    ),
                    op(
                        ChcOp::And,
                        vec![
                            eq(expr(&r), arithmetic(Form::SubRight, expr(&x), expr(&t))),
                            op(ChcOp::Not, vec![guard]),
                        ],
                    ),
                ],
            ),
        ],
    );
    (formula, vec![r, t, flag])
}

#[test]
fn each_alternative_keeps_the_entire_common_context_and_its_own_inverse() {
    for width in 1..=4 {
        let size = 1u128 << width;
        let (formula, keep) = alternatives(width);
        let projected = closed(&formula, &keep);
        for r in 0..size {
            for t in 0..size {
                for flag in 0..2 {
                    let values = [("r", r), ("t", t), ("flag", flag)];
                    let exists = (0..size).any(|x| {
                        oracle::truth(&formula, &[values[0], values[1], values[2], ("x", x)])
                    });
                    assert_eq!(oracle::truth(&projected, &values), exists);
                }
            }
        }
    }
}

#[test]
fn duplicate_reversed_and_negative_equalities_preserve_alias_correlations() {
    let x = var("x", 3);
    let r = var("r", 3);
    let t = var("t", 3);
    let alias = var("alias", 3);
    let flag = ChcVar::new("flag", ChcSort::Bool);
    let expression = arithmetic(Form::AddLeft, expr(&x), expr(&t));
    let binding = eq(expr(&r), expression.clone());
    let formula = op(
        ChcOp::And,
        vec![
            binding.clone(),
            eq(expression.clone(), expr(&r)),
            eq(expr(&alias), expression),
            op(
                ChcOp::Ite,
                vec![
                    binding.clone(),
                    expr(&flag),
                    op(ChcOp::Not, vec![expr(&flag)]),
                ],
            ),
        ],
    );
    // Reusing the source expression is a structural duplicate, not evidence
    // of shared arena IDs: read() admits each occurrence independently.
    let contradiction = op(
        ChcOp::And,
        vec![formula.clone(), op(ChcOp::Not, vec![binding])],
    );
    let keep = vec![r, t, alias, flag];
    for source in [formula, contradiction] {
        let projected = closed(&source, &keep);
        for r in 0..8 {
            for t in 0..8 {
                for alias in 0..8 {
                    for flag in 0..2 {
                        let values = [("r", r), ("t", t), ("alias", alias), ("flag", flag)];
                        let exists = (0..8).any(|x| {
                            oracle::truth(
                                &source,
                                &[values[0], values[1], values[2], values[3], ("x", x)],
                            )
                        });
                        assert_eq!(oracle::truth(&projected, &values), exists);
                    }
                }
            }
        }
    }
}

#[test]
fn discharging_one_positive_atom_does_not_poison_a_shared_arena_memo_entry() {
    let x = var("x", 2);
    let r = var("r", 2);
    let t = var("t", 2);
    let flag = ChcVar::new("flag", ChcSort::Bool);
    let binding = eq(expr(&r), arithmetic(Form::AddLeft, expr(&x), expr(&t)));
    let flag_expr = expr(&flag);
    let keep = vec![r, t, flag];
    for context in [
        SharedContext::Negation,
        SharedContext::Equality,
        SharedContext::Conditional,
    ] {
        let mut scope = Scope::new(Limits::default(), &|| true);
        let mut arena = Arena::new(&keep, &mut scope).unwrap();
        let definition = arena.read(&binding, 0, &mut scope).unwrap();
        let flag = arena.read(&flag_expr, 0, &mut scope).unwrap();
        // Deliberately share the SAME admitted Eq ID below a second atom.
        // No direct variable equality or joint image can handle the sole
        // BV local here: the other Add operand is retained, forcing inverse.
        let observation = match context {
            SharedContext::Negation => arena.operation(ChcOp::Not, vec![definition], &mut scope),
            SharedContext::Equality => {
                arena.operation(ChcOp::Eq, vec![flag, definition], &mut scope)
            }
            SharedContext::Conditional => {
                let negative = arena.operation(ChcOp::Not, vec![flag], &mut scope).unwrap();
                arena.operation(ChcOp::Ite, vec![definition, flag, negative], &mut scope)
            }
        }
        .unwrap();
        // normalize() pops its input. Both orders exercise a memo populated
        // before AND after the selected top-level equality is discharged.
        for atoms in [vec![definition, observation], vec![observation, definition]] {
            let root =
                super::super::super::eliminate::close(atoms, &mut arena, &mut scope).unwrap();
            let projected = arena.export(root, &mut scope).unwrap();
            let ChcExpr::Op(_, arguments) = &projected else {
                panic!("the other observation must retain its ordinary rewrite");
            };
            let observed_definition = match context {
                SharedContext::Equality => &arguments[1],
                SharedContext::Negation | SharedContext::Conditional => &arguments[0],
            };
            assert!(matches!(
                observed_definition.as_ref(),
                ChcExpr::Op(ChcOp::Eq, _)
            ));
            for r in 0..4 {
                for t in 0..4 {
                    for flag in 0..2 {
                        assert_eq!(
                            oracle::truth(&projected, &[("r", r), ("t", t), ("flag", flag)]),
                            !matches!(context, SharedContext::Negation) && flag != 0,
                        );
                    }
                }
            }
        }
    }
}
