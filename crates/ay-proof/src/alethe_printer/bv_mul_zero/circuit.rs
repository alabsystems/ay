// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! DAG-shared Boolean circuit matching Carcara's `bitblast_mult` rule.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{quote_symbol, ProofId};
use std::fmt::Write as _;
use std::rc::Rc;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum BoolGate {
    And,
    Or,
    Xor,
}

impl BoolGate {
    const fn name(self) -> &'static str {
        match self {
            Self::And => "and",
            Self::Or => "or",
            Self::Xor => "xor",
        }
    }
}

#[derive(Debug)]
pub(super) struct BoolExpr {
    key: usize,
    kind: BoolExprKind,
}

#[derive(Debug)]
enum BoolExprKind {
    False,
    Atom(String),
    App {
        gate: BoolGate,
        args: [Rc<BoolExpr>; 2],
        definition: usize,
    },
}

pub(super) struct MulCircuit {
    prefix: String,
    next_key: usize,
    definitions: Vec<Rc<BoolExpr>>,
    apps: HashMap<(BoolGate, [usize; 2]), Rc<BoolExpr>>,
    false_expr: Rc<BoolExpr>,
}

pub(super) enum FalseWitness {
    Literal,
    Step(String),
}

impl MulCircuit {
    pub(super) fn new(prefix: String) -> Self {
        let false_expr = Rc::new(BoolExpr {
            key: 0,
            kind: BoolExprKind::False,
        });
        Self {
            prefix,
            next_key: 1,
            definitions: Vec::new(),
            apps: HashMap::default(),
            false_expr,
        }
    }

    pub(super) fn false_expr(&self) -> Rc<BoolExpr> {
        Rc::clone(&self.false_expr)
    }

    pub(super) fn atom(&mut self, text: String) -> Rc<BoolExpr> {
        let expr = Rc::new(BoolExpr {
            key: self.next_key,
            kind: BoolExprKind::Atom(text),
        });
        self.next_key += 1;
        expr
    }

    fn app(&mut self, gate: BoolGate, left: Rc<BoolExpr>, right: Rc<BoolExpr>) -> Rc<BoolExpr> {
        let key = (gate, [left.key, right.key]);
        if let Some(existing) = self.apps.get(&key) {
            return Rc::clone(existing);
        }
        let definition = self.definitions.len();
        let expr = Rc::new(BoolExpr {
            key: self.next_key,
            kind: BoolExprKind::App {
                gate,
                args: [left, right],
                definition,
            },
        });
        self.next_key += 1;
        self.definitions.push(Rc::clone(&expr));
        self.apps.insert(key, Rc::clone(&expr));
        expr
    }

    pub(super) fn reference(&self, expr: &BoolExpr) -> String {
        match &expr.kind {
            BoolExprKind::False => "false".to_string(),
            BoolExprKind::Atom(text) => text.clone(),
            BoolExprKind::App { definition, .. } => {
                quote_symbol(&format!("{}d{definition}", self.prefix))
            }
        }
    }

    pub(super) fn append_definitions(&self, out: &mut String) {
        for expr in &self.definitions {
            let BoolExprKind::App {
                gate,
                args: [left, right],
                ..
            } = &expr.kind
            else {
                continue;
            };
            let name = self.reference(expr);
            let left = self.reference(left);
            let right = self.reference(right);
            let _ = writeln!(
                out,
                "(define-fun {name} () Bool ({} {left} {right}))",
                gate.name()
            );
        }
    }

    pub(super) fn operand_bits(
        &mut self,
        width: u32,
        zero_operand: usize,
        operands: &[String; 2],
    ) -> [Vec<Rc<BoolExpr>>; 2] {
        let false_expr = self.false_expr();
        std::array::from_fn(|operand| {
            if operand == zero_operand {
                vec![Rc::clone(&false_expr); width as usize]
            } else {
                (0..width)
                    .map(|bit| self.atom(format!("((_ @bit_of {bit}) {})", operands[operand])))
                    .collect()
            }
        })
    }

    /// Build the exact shift/add network implemented by pinned Carcara's
    /// `bitblast_mult`. Changing this topology without changing that checker
    /// rule makes the resulting proof invalid, even if the new circuit is
    /// extensionally equivalent.
    pub(super) fn build(&mut self, x: &[Rc<BoolExpr>], y: &[Rc<BoolExpr>]) -> Vec<Rc<BoolExpr>> {
        let width = x.len();
        debug_assert_eq!(width, y.len());
        let f = self.false_expr();
        let mut shift = Vec::with_capacity(width);
        for (j, y_bit) in y.iter().enumerate() {
            let mut row = Vec::with_capacity(width);
            for i in 0..width {
                row.push(if j <= i {
                    self.app(BoolGate::And, Rc::clone(y_bit), Rc::clone(&x[i - j]))
                } else {
                    Rc::clone(&f)
                });
            }
            shift.push(row);
        }

        let mut carry = vec![vec![Rc::clone(&f); width]];
        let mut result = vec![shift[0].clone()];
        for j in 1..width {
            let mut carry_row = vec![Rc::clone(&f)];
            for i in 1..width {
                let bit = if j < i {
                    let left = self.app(
                        BoolGate::And,
                        Rc::clone(&result[j - 1][i - 1]),
                        Rc::clone(&shift[j][i - 1]),
                    );
                    let xor = self.app(
                        BoolGate::Xor,
                        Rc::clone(&result[j - 1][i - 1]),
                        Rc::clone(&shift[j][i - 1]),
                    );
                    let right = self.app(BoolGate::And, xor, Rc::clone(&carry_row[i - 1]));
                    self.app(BoolGate::Or, left, right)
                } else {
                    Rc::clone(&f)
                };
                carry_row.push(bit);
            }
            carry.push(carry_row);

            let mut result_row = Vec::with_capacity(width);
            for i in 0..width {
                let bit = if i == 0 {
                    Rc::clone(&shift[0][0])
                } else if j > i {
                    Rc::clone(&result[i][i])
                } else {
                    let inner = self.app(
                        BoolGate::Xor,
                        Rc::clone(&result[j - 1][i]),
                        Rc::clone(&shift[j][i]),
                    );
                    self.app(BoolGate::Xor, inner, Rc::clone(&carry[j][i]))
                };
                result_row.push(bit);
            }
            result.push(result_row);
        }
        result[width - 1].clone()
    }

    pub(super) fn prove_false(
        &self,
        id: ProofId,
        expr: &Rc<BoolExpr>,
        out: &mut String,
        memo: &mut HashMap<usize, String>,
    ) -> Option<FalseWitness> {
        match &expr.kind {
            BoolExprKind::False => return Some(FalseWitness::Literal),
            BoolExprKind::Atom(_) => return None,
            BoolExprKind::App { .. } => {}
        }
        let BoolExprKind::App {
            gate,
            args,
            definition,
        } = &expr.kind
        else {
            return None;
        };
        let definition = *definition;
        if let Some(step) = memo.get(&definition) {
            return Some(FalseWitness::Step(step.clone()));
        }
        let final_step = format!("{id}.mz.p{definition}");
        let original = self.reference(expr);

        if *gate == BoolGate::And {
            let mut witness = None;
            for (index, arg) in args.iter().enumerate() {
                if let Some(found) = self.prove_false(id, arg, out, memo) {
                    witness = Some((index, found));
                    break;
                }
            }
            let (false_index, false_witness) = witness?;
            match false_witness {
                FalseWitness::Literal => {
                    let _ = writeln!(
                        out,
                        "(step {final_step} (cl (= {original} false)) :rule and_simplify)"
                    );
                }
                FalseWitness::Step(premise) => {
                    let mut reduced = [self.reference(&args[0]), self.reference(&args[1])];
                    reduced[false_index] = "false".to_string();
                    let reduced = format!("(and {} {})", reduced[0], reduced[1]);
                    let _ = writeln!(
                        out,
                        "(step {id}.mz.g{definition} (cl (= {original} {reduced})) :rule cong :premises ({premise}))"
                    );
                    let _ = writeln!(
                        out,
                        "(step {id}.mz.e{definition} (cl (= {reduced} false)) :rule and_simplify)"
                    );
                    let _ = writeln!(
                        out,
                        "(step {final_step} (cl (= {original} false)) :rule trans :premises ({id}.mz.g{definition} {id}.mz.e{definition}))"
                    );
                }
            }
        } else {
            let mut premises = Vec::new();
            for arg in args {
                match self.prove_false(id, arg, out, memo)? {
                    FalseWitness::Literal => {}
                    FalseWitness::Step(step) => premises.push(step),
                }
            }
            if premises.is_empty() {
                let _ = writeln!(
                    out,
                    "(step {final_step} (cl (= {original} false)) :rule evaluate)"
                );
            } else {
                let ground = format!("({} false false)", gate.name());
                let _ = writeln!(
                    out,
                    "(step {id}.mz.g{definition} (cl (= {original} {ground})) :rule cong :premises ({}))",
                    premises.join(" ")
                );
                let _ = writeln!(
                    out,
                    "(step {id}.mz.e{definition} (cl (= {ground} false)) :rule evaluate)"
                );
                let _ = writeln!(
                    out,
                    "(step {final_step} (cl (= {original} false)) :rule trans :premises ({id}.mz.g{definition} {id}.mz.e{definition}))"
                );
            }
        }
        memo.insert(definition, final_step.clone());
        Some(FalseWitness::Step(final_step))
    }
}
