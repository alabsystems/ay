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
            let (name, args) = match self.terms().get(literal) {
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

    /// Violated asserted literals of a candidate solution that the
    /// dive-repair loop can steer against (#lia-dive-repair):
    /// `Some(lits)` when every asserted literal evaluates and every
    /// violated one is a disequality (`(= l r)` asserted false, or
    /// two-argument `distinct` asserted true) — `lits` is then the
    /// violated disequality literals (empty when the solution
    /// satisfies everything); `None` when any literal cannot be
    /// evaluated or a violated literal is not a disequality.
    pub(crate) fn violated_disequalities(
        &self,
        solution: &[(usize, BigInt)],
        idx_to_term: &[TermId],
    ) -> Option<Vec<TermId>> {
        let mut values: HashMap<TermId, BigInt> = Default::default();
        for &(col, ref val) in solution {
            if col < idx_to_term.len() {
                values.insert(idx_to_term[col], val.clone());
            }
        }
        let mut violated = Vec::new();
        for &(literal, value) in &self.asserted {
            let (name, args) = match self.terms().get(literal) {
                TermData::Const(Constant::Bool(b)) => {
                    if value != *b {
                        return None;
                    }
                    continue;
                }
                TermData::App(Symbol::Named(name), args) => (name, args),
                _ => return None,
            };
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
                "distinct" => lhs != rhs,
                _ => return None,
            };
            if atom_holds != value {
                let is_disequality =
                    (name.as_str() == "=" && !value) || (name.as_str() == "distinct" && value);
                if !is_disequality {
                    return None;
                }
                violated.push(literal);
            }
        }
        Some(violated)
    }

    /// Exact integer coefficients of a linear expression over the
    /// leaves assigned in `values` (same shapes as
    /// `evaluate_linear_expr`, with `*` restricted to constant
    /// scaling): `term == sum(coeffs * leaf) + constant`.
    pub(crate) fn linear_coeffs(
        &self,
        values: &HashMap<TermId, BigInt>,
        term: TermId,
    ) -> Option<(HashMap<TermId, BigInt>, BigInt)> {
        if values.contains_key(&term) {
            let mut coeffs = HashMap::default();
            coeffs.insert(term, BigInt::one());
            return Some((coeffs, BigInt::zero()));
        }
        match self.terms().get(term) {
            TermData::Const(Constant::Int(n)) => Some((HashMap::default(), n.clone())),
            TermData::Const(Constant::Rational(r)) if r.0.denom().is_one() => {
                Some((HashMap::default(), r.0.numer().clone()))
            }
            TermData::App(Symbol::Named(name), args) => match name.as_str() {
                "+" => {
                    let mut coeffs: HashMap<TermId, BigInt> = HashMap::default();
                    let mut constant = BigInt::zero();
                    for &arg in args {
                        let (c, k) = self.linear_coeffs(values, arg)?;
                        for (v, coeff) in c {
                            *coeffs.entry(v).or_insert_with(BigInt::zero) += coeff;
                        }
                        constant += k;
                    }
                    Some((coeffs, constant))
                }
                "-" if args.len() == 1 => {
                    let (c, k) = self.linear_coeffs(values, args[0])?;
                    Some((c.into_iter().map(|(v, coeff)| (v, -coeff)).collect(), -k))
                }
                "-" if args.len() >= 2 => {
                    let (mut coeffs, mut constant) = self.linear_coeffs(values, args[0])?;
                    for &arg in &args[1..] {
                        let (c, k) = self.linear_coeffs(values, arg)?;
                        for (v, coeff) in c {
                            *coeffs.entry(v).or_insert_with(BigInt::zero) -= coeff;
                        }
                        constant -= k;
                    }
                    Some((coeffs, constant))
                }
                "*" => {
                    let mut scale: Option<BigInt> = None;
                    let mut form: Option<(HashMap<TermId, BigInt>, BigInt)> = None;
                    for &arg in args {
                        let (c, k) = self.linear_coeffs(values, arg)?;
                        if c.is_empty() {
                            scale = Some(match scale {
                                Some(sc) => sc * k,
                                None => k,
                            });
                        } else if form.is_none() {
                            form = Some((c, k));
                        } else {
                            return None;
                        }
                    }
                    let sc = scale.unwrap_or_else(BigInt::one);
                    match form {
                        Some((c, k)) => Some((
                            c.into_iter().map(|(v, coeff)| (v, coeff * &sc)).collect(),
                            k * &sc,
                        )),
                        None => Some((HashMap::default(), sc)),
                    }
                }
                _ => None,
            },
            _ => None,
        }
    }

    /// Whether `model` definitively falsifies one of this solver's asserted
    /// linear literals. A literal the linear evaluator cannot read (a
    /// nonlinear term, a variable `model` does not assign) is not counted:
    /// this is a refutation test, not a certificate.
    #[must_use]
    pub fn model_falsifies_asserted(&self, model: &LiaModel) -> bool {
        self.asserted.iter().any(|&(literal, value)| {
            let TermData::App(Symbol::Named(name), args) = self.terms().get(literal) else {
                return false;
            };
            let [lhs, rhs] = args.as_slice() else {
                return false;
            };
            let (Some(lhs), Some(rhs)) = (
                self.evaluate_linear_expr(&model.values, *lhs),
                self.evaluate_linear_expr(&model.values, *rhs),
            ) else {
                return false;
            };
            let holds = match name.as_str() {
                ">=" => lhs >= rhs,
                "<=" => lhs <= rhs,
                ">" => lhs > rhs,
                "<" => lhs < rhs,
                "=" => lhs == rhs,
                _ => return false,
            };
            holds != value
        })
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

        match self.terms().get(term) {
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

    /// One repair fixing for a violated disequality literal
    /// (#lia-dive-repair): a variable of the literal's difference
    /// form (unit coefficient preferred, then smallest `TermId`
    /// for determinism) that is not already pre-fixed, set one
    /// step above its witness value. Any single-variable integer
    /// step moves the difference off zero by that variable's
    /// nonzero coefficient, so the re-dive cannot reproduce the
    /// same equality point through this variable; the loop's
    /// exact re-verification remains the acceptance gate.
    pub(crate) fn disequality_repair_fixing(
        &self,
        literal: TermId,
        values: &HashMap<TermId, BigInt>,
        prefixed: &[(TermId, BigInt)],
    ) -> Option<(TermId, BigInt)> {
        let TermData::App(Symbol::Named(_), args) = self.terms().get(literal) else {
            return None;
        };
        if args.len() != 2 {
            return None;
        }
        let (lc, _) = self.linear_coeffs(values, args[0])?;
        let (rc, _) = self.linear_coeffs(values, args[1])?;
        let mut diff = lc;
        for (v, coeff) in rc {
            *diff.entry(v).or_insert_with(BigInt::zero) -= coeff;
        }
        diff.retain(|_, coeff| !coeff.is_zero());
        let mut candidates: Vec<(bool, TermId)> = diff
            .iter()
            .filter(|(v, _)| !prefixed.iter().any(|(p, _)| p == *v))
            .map(|(v, coeff)| (!(coeff.is_one() || *coeff == -BigInt::one()), *v))
            .collect();
        candidates.sort();
        let var = candidates.first().map(|&(_, v)| v)?;
        let witness_value = values.get(&var)?;
        Some((var, witness_value + BigInt::one()))
    }

    /// Whether a stored witness model still satisfies the CURRENT
    /// asserted set and shared equalities, verified exactly the
    /// same way as at storage time (#lia-dive-repair). Fail-closed
    /// on a hidden interface or any shared disequality (the stored
    /// witnesses were not verified against those), on a model
    /// variable the current index does not know, and on any
    /// literal the exact checker cannot evaluate.
    pub(crate) fn stored_witness_still_valid(&self, model: &LiaModel) -> bool {
        if self.hidden_interface || !self.shared_disequalities.is_empty() {
            return false;
        }
        let (term_to_idx, idx_to_term) = self.build_var_index();
        let mut solution: Vec<(usize, BigInt)> = Vec::with_capacity(model.values.len());
        for (term, val) in &model.values {
            let Some(&idx) = term_to_idx.get(term) else {
                return false;
            };
            solution.push((idx, val.clone()));
        }
        if self.check_solution_satisfies_asserted(&solution, &idx_to_term, false) != Some(true) {
            return false;
        }
        // Strict shared-equality verification: unlike
        // `witness_satisfies_shared_equalities` (whose unverifiable
        // pairs pass, for the dieted enumeration lanes), an
        // early-Sat shortcut must positively evaluate EVERY shared
        // pair equal under the witness — an unverifiable pair is
        // exactly how an interface obligation could be skipped.
        let mut values: HashMap<TermId, BigInt> = Default::default();
        for &(col, ref val) in &solution {
            if col < idx_to_term.len() {
                values.insert(idx_to_term[col], val.clone());
            }
        }
        self.shared_equalities.iter().all(|(lhs, rhs, _)| {
            match (
                self.evaluate_linear_expr(&values, *lhs),
                self.evaluate_linear_expr(&values, *rhs),
            ) {
                (Some(l), Some(r)) => l == r,
                _ => {
                    values.get(lhs).is_some()
                        && values.get(lhs) == values.get(rhs)
                        && values.contains_key(rhs)
                }
            }
        })
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
