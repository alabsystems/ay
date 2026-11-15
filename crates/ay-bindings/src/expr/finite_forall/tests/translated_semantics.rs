// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

mod oracle;
use oracle::{bit, truth, Model};

#[derive(Clone, Copy, Debug)]
enum Translation {
    AddAfter,
    AddBefore,
    SubtractAfter,
    SubtractBefore,
}

const TRANSLATIONS: [Translation; 4] = [
    Translation::AddAfter,
    Translation::AddBefore,
    Translation::SubtractAfter,
    Translation::SubtractBefore,
];

impl Translation {
    fn expression(self, offset: Expr) -> Expr {
        match self {
            Self::AddAfter => small_index().bvadd(offset),
            Self::AddBefore => offset.bvadd(small_index()),
            Self::SubtractAfter => small_index().bvsub(offset),
            Self::SubtractBefore => offset.bvsub(small_index()),
        }
    }

    fn location(self, index: u8, offset: u8) -> u8 {
        match self {
            Self::AddAfter | Self::AddBefore => (u16::from(index) + u16::from(offset)) as u8 % 4,
            Self::SubtractAfter => (u16::from(index) + 4 - u16::from(offset)) as u8 % 4,
            Self::SubtractBefore => (u16::from(offset) + 4 - u16::from(index)) as u8 % 4,
        }
    }
}

fn small_index() -> Expr {
    Expr::var("i", Sort::bitvec(2))
}

fn small_array(name: &str) -> Expr {
    Expr::var(name, Sort::array(Sort::bitvec(2), Sort::bool()))
}

fn prefix(upper: u8) -> Expr {
    if upper == 4 {
        small_index().bvule(Expr::bitvec_const(3u8, 2))
    } else {
        small_index().bvult(Expr::bitvec_const(upper, 2))
    }
}

fn formulas(body: Expr) -> (Expr, Expr) {
    let vars = vec![("i".to_owned(), Sort::bitvec(2))];
    // Bypass the constructor under test when constructing the reference.
    let original = boolean(ExprValue::Forall {
        vars: vars.clone(),
        body: body.clone(),
        triggers: Vec::new(),
    });
    let normalized = Expr::forall(vars, body);
    assert!(!matches!(normalized.value(), ExprValue::Forall { .. }));
    (original, normalized)
}

fn assert_model(formulas: &(Expr, Expr), model: Model, expected: bool) {
    assert_eq!(truth(&formulas.0, model), expected, "raw: {model:?}");
    assert_eq!(truth(&formulas.1, model), expected, "new: {model:?}");
}

#[test]
fn free_offsets_match_raw_forall_for_all_small_arrays_and_modular_orientations() {
    for left in TRANSLATIONS {
        for right in TRANSLATIONS {
            for upper in 0..=4 {
                let equality = small_array("a")
                    .select(left.expression(Expr::var("x", Sort::bitvec(2))))
                    .eq(small_array("b").select(right.expression(Expr::var("y", Sort::bitvec(2)))));
                let formulas = formulas(prefix(upper).implies(equality));
                for a in 0..16 {
                    for b in 0..16 {
                        for x in 0..4 {
                            for y in 0..4 {
                                let model = Model {
                                    a,
                                    b,
                                    x,
                                    y,
                                    fill: false,
                                    index: 0,
                                };
                                let expected = (0..upper).all(|i| {
                                    bit(a, left.location(i, x)) == bit(b, right.location(i, y))
                                });
                                assert_model(&formulas, model, expected);
                            }
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn literal_offsets_match_raw_forall_across_wrapping_and_reflected_indices() {
    for left in TRANSLATIONS {
        for right in TRANSLATIONS {
            for upper in 0..=4 {
                let equality = small_array("a")
                    .select(left.expression(Expr::bitvec_const(1u8, 2)))
                    .eq(small_array("b").select(right.expression(Expr::bitvec_const(3u8, 2))));
                let formulas = formulas(prefix(upper).implies(equality));
                for a in 0..16 {
                    for b in 0..16 {
                        let model = Model {
                            a,
                            b,
                            x: 0,
                            y: 0,
                            fill: false,
                            index: 0,
                        };
                        let expected = (0..upper)
                            .all(|i| bit(a, left.location(i, 1)) == bit(b, right.location(i, 3)));
                        assert_model(&formulas, model, expected);
                    }
                }
            }
        }
    }
}

fn contexts(formula: Expr) -> [Expr; 4] {
    let free = Expr::var("fill", Sort::bool());
    [
        formula.clone().not(),
        formula.clone().or(free.clone()),
        formula.clone().implies(free.clone()),
        free.implies(formula),
    ]
}

#[test]
fn translated_fill_preserves_interval_tail_freedom_and_outer_boolean_polarity() {
    for translation in TRANSLATIONS {
        for (lower, upper) in [(0u8, 0u8), (0, 2), (2, 4), (3, 1)] {
            let guard = prefix(upper).and(Expr::bitvec_const(lower, 2).bvule(small_index()));
            let equality = small_array("a")
                .select(translation.expression(Expr::var("x", Sort::bitvec(2))))
                .eq(Expr::var("fill", Sort::bool()));
            let pair = formulas(guard.implies(equality));
            let raw_contexts = contexts(pair.0.clone());
            let normalized_contexts = contexts(pair.1.clone());
            for a in 0..16 {
                for x in 0..4 {
                    for fill in [false, true] {
                        let model = Model {
                            a,
                            b: 0,
                            x,
                            y: 0,
                            fill,
                            index: 0,
                        };
                        let expected =
                            (lower..upper).all(|i| bit(a, translation.location(i, x)) == fill);
                        assert_model(&pair, model, expected);
                        let contextual = [
                            !expected,
                            expected || fill,
                            !expected || fill,
                            !fill || expected,
                        ];
                        for position in 0..4 {
                            assert_eq!(truth(&raw_contexts[position], model), contextual[position]);
                            assert_eq!(
                                truth(&normalized_contexts[position], model),
                                contextual[position]
                            );
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn translated_and_direct_reads_of_the_same_array_keep_aliases_exact() {
    for translation in TRANSLATIONS {
        for upper in 0..=4 {
            let read = small_array("a");
            let equality = read
                .clone()
                .select(translation.expression(Expr::var("x", Sort::bitvec(2))))
                .eq(read.select(small_index()));
            let pair = formulas(prefix(upper).implies(equality));
            for a in 0..16 {
                for x in 0..4 {
                    let model = Model {
                        a,
                        b: 0,
                        x,
                        y: 0,
                        fill: false,
                        index: 0,
                    };
                    let expected =
                        (0..upper).all(|i| bit(a, translation.location(i, x)) == bit(a, i));
                    assert_model(&pair, model, expected);
                }
            }
        }
    }
}
