// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl LiaSolver<'_> {
    /// Check if a candidate solution satisfies all asserted literals.
    pub(crate) fn check_solution_satisfies_asserted(
        &self,
        solution: &[(usize, BigInt)],
        idx_to_term: &[TermId],
        debug: bool,
    ) -> Option<bool> {
        let mut values: HashMap<TermId, BigInt> = Default::default();
        for &(col, ref val) in solution {
            if col < idx_to_term.len() {
                values.insert(idx_to_term[col], val.clone());
            }
        }

        for &(literal, value) in &self.asserted {
            let (name, args) = match self.terms.get(literal) {
                TermData::Const(Constant::Bool(b)) => {
                    if value != *b {
                        return Some(false);
                    }
                    continue;
                }
                TermData::App(Symbol::Named(name), args) => (name, args),
                _ => return None,
            };

            if name == "distinct" {
                let mut seen = HashSet::default();
                let mut atom_holds = true;
                for &arg in args {
                    let arg_value = self.evaluate_linear_expr(&values, arg)?;
                    if !seen.insert(arg_value) {
                        atom_holds = false;
                        break;
                    }
                }
                if atom_holds != value {
                    if debug {
                        safe_eprintln!(
                            "[ENUM] Solution violates distinct {:?}: got {}, want {}",
                            literal,
                            atom_holds,
                            value
                        );
                    }
                    return Some(false);
                }
                continue;
            }

            if args.len() != 2 {
                return None;
            }

            let lhs = self.evaluate_linear_expr(&values, args[0])?;
            let rhs = self.evaluate_linear_expr(&values, args[1])?;

            let atom_holds = match name.as_str() {
                ">=" => lhs >= rhs,
                "<=" => lhs <= rhs,
                ">" => lhs > rhs,
                "<" => lhs < rhs,
                "=" => lhs == rhs,
                _ => return None,
            };

            if atom_holds != value {
                if debug {
                    safe_eprintln!(
                        "[ENUM] Solution violates: {:?} {} {} {} = {} (want {})",
                        literal,
                        lhs,
                        name,
                        rhs,
                        atom_holds,
                        value
                    );
                }
                return Some(false);
            }
        }

        Some(true)
    }

    /// Evaluate a linear integer expression under a partial assignment.
    pub(crate) fn evaluate_linear_expr(
        &self,
        values: &HashMap<TermId, BigInt>,
        term: TermId,
    ) -> Option<BigInt> {
        if let Some(v) = values.get(&term) {
            return Some(v.clone());
        }

        match self.terms.get(term) {
            TermData::Const(Constant::Int(n)) => Some(n.clone()),
            TermData::Const(Constant::Rational(r)) => {
                if r.0.denom().is_one() {
                    Some(r.0.numer().clone())
                } else {
                    None
                }
            }
            TermData::App(Symbol::Named(name), args) => match name.as_str() {
                "+" => {
                    let mut sum = BigInt::zero();
                    for &arg in args {
                        sum += self.evaluate_linear_expr(values, arg)?;
                    }
                    Some(sum)
                }
                "-" if args.len() == 1 => Some(-self.evaluate_linear_expr(values, args[0])?),
                "-" if args.len() >= 2 => {
                    let mut result = self.evaluate_linear_expr(values, args[0])?;
                    for &arg in &args[1..] {
                        result -= self.evaluate_linear_expr(values, arg)?;
                    }
                    Some(result)
                }
                "*" => {
                    let mut product = BigInt::one();
                    for &arg in args {
                        product *= self.evaluate_linear_expr(values, arg)?;
                    }
                    Some(product)
                }
                _ => None,
            },
            _ => None,
        }
    }

    /// Convert column-indexed solution to LiaModel with TermId keys.
    pub(crate) fn solution_to_model(
        solution: &[(usize, BigInt)],
        idx_to_term: &[TermId],
    ) -> LiaModel {
        let mut values = HashMap::default();
        for &(col, ref val) in solution {
            if col < idx_to_term.len() {
                values.insert(idx_to_term[col], val.clone());
            }
        }
        LiaModel { values }
    }

    /// Build a conflict clause from all asserted literals.
    pub(crate) fn conflict_from_asserted(&self) -> Vec<ay_core::TheoryLit> {
        use ay_core::TheoryLit;

        self.asserted
            .iter()
            .map(|&(lit, val)| TheoryLit::new(lit, val))
            .collect()
    }
}
