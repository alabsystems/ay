// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SMT-LIB display formatting for CHC expressions.
//!
//! Implements `fmt::Display` for `ChcExpr`, producing SMT-LIB2 S-expression syntax.

use std::fmt;
use std::sync::Arc;

use super::super::{maybe_grow_expr_stack, ChcExpr, ChcOp, ChcSort};

fn write_smtlib_int_atom(f: &mut fmt::Formatter<'_>, value: i128) -> fmt::Result {
    if value < 0 {
        write!(f, "(- {})", -value)
    } else {
        write!(f, "{value}")
    }
}

fn write_smtlib_real(f: &mut fmt::Formatter<'_>, numerator: i64, denominator: i64) -> fmt::Result {
    let mut numerator = i128::from(numerator);
    let mut denominator = i128::from(denominator);
    if denominator < 0 {
        numerator = -numerator;
        denominator = -denominator;
    }

    write!(f, "(/ ")?;
    write_smtlib_int_atom(f, numerator)?;
    write!(f, " ")?;
    write_smtlib_int_atom(f, denominator)?;
    write!(f, ")")
}

fn is_smtlib_builtin_func_app(name: &str, args: &[Arc<ChcExpr>]) -> bool {
    matches!(name, "to_real" | "to_int" | "is_int") && args.len() == 1
}

fn is_semantically_real(expr: &ChcExpr) -> bool {
    maybe_grow_expr_stack(|| {
        if expr.sort() == ChcSort::Real {
            return true;
        }

        match expr {
            ChcExpr::FuncApp(name, _, args) => name == "to_real" && args.len() == 1,
            ChcExpr::Op(ChcOp::Add | ChcOp::Sub | ChcOp::Mul | ChcOp::Div | ChcOp::Neg, args) => {
                args.iter().any(|arg| is_semantically_real(arg))
            }
            ChcExpr::Op(ChcOp::Ite, args) => args
                .get(1..)
                .is_some_and(|branches| branches.iter().any(|arg| is_semantically_real(arg))),
            _ => false,
        }
    })
}

impl fmt::Display for ChcExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Intentionally no depth bail-out: SMT-LIB rendering should remain exact;
        // stack growth is handled by `maybe_grow_expr_stack`.
        maybe_grow_expr_stack(|| match self {
            Self::Bool(b) => write!(f, "{b}"),
            Self::Int(n) => write!(f, "{n}"),
            Self::Real(n, d) => write_smtlib_real(f, *n, *d),
            Self::BitVec(val, width) => write!(f, "(_ bv{val} {width})"),
            Self::Var(v) => write!(f, "{v}"),
            Self::PredicateApp(name, id, args) => {
                write!(f, "({name}#{}", id.index())?;
                for arg in args {
                    write!(f, " {arg}")?;
                }
                write!(f, ")")
            }
            Self::FuncApp(name, sort, args) => {
                if is_smtlib_builtin_func_app(name, args) {
                    write!(f, "({name}")?;
                    for arg in args {
                        write!(f, " {arg}")?;
                    }
                    return write!(f, ")");
                }
                write!(f, "({name}:{sort}")?;
                for arg in args {
                    write!(f, " {arg}")?;
                }
                write!(f, ")")
            }
            Self::Op(op, args) => {
                // Indexed BV ops use (_ op N) syntax
                match op {
                    ChcOp::BvExtract(hi, lo) => {
                        write!(f, "((_ extract {hi} {lo})")?;
                        for arg in args {
                            write!(f, " {arg}")?;
                        }
                        return write!(f, ")");
                    }
                    ChcOp::BvZeroExtend(n) => {
                        write!(f, "((_ zero_extend {n})")?;
                        for arg in args {
                            write!(f, " {arg}")?;
                        }
                        return write!(f, ")");
                    }
                    ChcOp::BvSignExtend(n) => {
                        write!(f, "((_ sign_extend {n})")?;
                        for arg in args {
                            write!(f, " {arg}")?;
                        }
                        return write!(f, ")");
                    }
                    ChcOp::BvRotateLeft(n) => {
                        write!(f, "((_ rotate_left {n})")?;
                        for arg in args {
                            write!(f, " {arg}")?;
                        }
                        return write!(f, ")");
                    }
                    ChcOp::BvRotateRight(n) => {
                        write!(f, "((_ rotate_right {n})")?;
                        for arg in args {
                            write!(f, " {arg}")?;
                        }
                        return write!(f, ")");
                    }
                    ChcOp::BvRepeat(n) => {
                        write!(f, "((_ repeat {n})")?;
                        for arg in args {
                            write!(f, " {arg}")?;
                        }
                        return write!(f, ")");
                    }
                    ChcOp::Int2Bv(w) => {
                        write!(f, "((_ int2bv {w})")?;
                        for arg in args {
                            write!(f, " {arg}")?;
                        }
                        return write!(f, ")");
                    }
                    _ => {}
                }
                let op_str = match op {
                    ChcOp::Not => "not",
                    ChcOp::And => "and",
                    ChcOp::Or => "or",
                    ChcOp::Implies => "=>",
                    ChcOp::Iff => "iff",
                    ChcOp::Add => "+",
                    ChcOp::Sub => "-",
                    ChcOp::Mul => "*",
                    ChcOp::Div if args.iter().any(|arg| is_semantically_real(arg)) => "/",
                    ChcOp::Div => "div",
                    ChcOp::Mod => "mod",
                    ChcOp::Neg => "-",
                    ChcOp::Eq => "=",
                    ChcOp::Ne => "distinct",
                    ChcOp::Lt => "<",
                    ChcOp::Le => "<=",
                    ChcOp::Gt => ">",
                    ChcOp::Ge => ">=",
                    ChcOp::Ite => "ite",
                    ChcOp::Select => "select",
                    ChcOp::Store => "store",
                    ChcOp::BvAdd => "bvadd",
                    ChcOp::BvSub => "bvsub",
                    ChcOp::BvMul => "bvmul",
                    ChcOp::BvUDiv => "bvudiv",
                    ChcOp::BvURem => "bvurem",
                    ChcOp::BvSDiv => "bvsdiv",
                    ChcOp::BvSRem => "bvsrem",
                    ChcOp::BvSMod => "bvsmod",
                    ChcOp::BvAnd => "bvand",
                    ChcOp::BvOr => "bvor",
                    ChcOp::BvXor => "bvxor",
                    ChcOp::BvNand => "bvnand",
                    ChcOp::BvNor => "bvnor",
                    ChcOp::BvXnor => "bvxnor",
                    ChcOp::BvNot => "bvnot",
                    ChcOp::BvNeg => "bvneg",
                    ChcOp::BvShl => "bvshl",
                    ChcOp::BvLShr => "bvlshr",
                    ChcOp::BvAShr => "bvashr",
                    ChcOp::BvULt => "bvult",
                    ChcOp::BvULe => "bvule",
                    ChcOp::BvUGt => "bvugt",
                    ChcOp::BvUGe => "bvuge",
                    ChcOp::BvSLt => "bvslt",
                    ChcOp::BvSLe => "bvsle",
                    ChcOp::BvSGt => "bvsgt",
                    ChcOp::BvSGe => "bvsge",
                    ChcOp::BvComp => "bvcomp",
                    ChcOp::BvConcat => "concat",
                    ChcOp::Bv2Nat => "bv2nat",
                    // Indexed ops handled above; fallback for new variants (#6091)
                    other => {
                        write!(f, "({other:?}")?;
                        for arg in args {
                            write!(f, " {arg}")?;
                        }
                        return write!(f, ")");
                    }
                };
                write!(f, "({op_str}")?;
                for arg in args {
                    write!(f, " {arg}")?;
                }
                write!(f, ")")
            }
            Self::ConstArrayMarker(_) => write!(f, "(as const)"),
            Self::IsTesterMarker(name) => write!(f, "(_ is {name})"),
            Self::ConstArray(key_sort, val) => {
                // Output in SMT-LIB2 format for constant arrays
                write!(f, "((as const (Array {key_sort} {})) {})", val.sort(), val)
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use super::super::super::ChcVar;
    use super::*;

    fn arc(expr: ChcExpr) -> Arc<ChcExpr> {
        Arc::new(expr)
    }

    fn var(name: &str, sort: ChcSort) -> ChcExpr {
        ChcExpr::Var(ChcVar::new(name, sort))
    }

    #[test]
    fn display_real_literals_as_smtlib_rationals() {
        assert_eq!(ChcExpr::Real(3, 4).to_string(), "(/ 3 4)");
        assert_eq!(ChcExpr::Real(-3, 4).to_string(), "(/ (- 3) 4)");
        assert_eq!(ChcExpr::Real(0, 4).to_string(), "(/ 0 4)");
        assert_eq!(ChcExpr::Real(7, 1).to_string(), "(/ 7 1)");
        assert_eq!(ChcExpr::Real(3, -4).to_string(), "(/ (- 3) 4)");
    }

    #[test]
    fn display_builtin_func_apps_as_smtlib_builtins() {
        let i = arc(var("i", ChcSort::Int));
        let r = arc(var("r", ChcSort::Real));

        let to_real = ChcExpr::FuncApp("to_real".to_string(), ChcSort::Real, vec![i]);
        let to_int = ChcExpr::FuncApp("to_int".to_string(), ChcSort::Int, vec![r.clone()]);
        let is_int = ChcExpr::FuncApp("is_int".to_string(), ChcSort::Bool, vec![r]);

        assert_eq!(to_real.to_string(), "(to_real i)");
        assert_eq!(to_int.to_string(), "(to_int r)");
        assert_eq!(is_int.to_string(), "(is_int r)");
    }

    #[test]
    fn display_div_uses_real_division_for_any_semantic_real_argument() {
        let i = var("i", ChcSort::Int);
        let r = var("r", ChcSort::Real);

        let int_div = ChcExpr::Op(ChcOp::Div, vec![arc(i.clone()), arc(ChcExpr::Int(2))]);
        assert_eq!(int_div.to_string(), "(div i 2)");

        let mixed_div = ChcExpr::Op(ChcOp::Div, vec![arc(i.clone()), arc(r.clone())]);
        assert_eq!(mixed_div.to_string(), "(/ i r)");

        let mixed_sum = ChcExpr::Op(ChcOp::Add, vec![arc(i), arc(r)]);
        let nested_mixed_div = ChcExpr::Op(ChcOp::Div, vec![arc(mixed_sum), arc(ChcExpr::Int(2))]);
        assert_eq!(nested_mixed_div.to_string(), "(/ (+ i r) 2)");
    }
}
