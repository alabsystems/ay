// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Asserted-literal reasons for entailed variable-difference equalities.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::TheoryLit;
use num_traits::Zero;

use crate::{LinearExpr, LraSolver, Rational};

impl LraSolver {
    /// Resolve asserted reasons that entail `a - b == 0` for each variable pair.
    ///
    /// The first asserted equality resolves a pair immediately. Otherwise the
    /// first non-strict inequality in each direction is retained, and the pair
    /// is frozen as soon as both directions have been observed.
    pub(super) fn difference_pair_reasons(&self) -> HashMap<(u32, u32), Vec<TheoryLit>> {
        let mut partial: HashMap<(u32, u32), (Option<TheoryLit>, Option<TheoryLit>)> =
            HashMap::default();
        let mut resolved: HashMap<(u32, u32), Vec<TheoryLit>> = HashMap::default();

        for (&atom_term, &atom_value) in &self.asserted {
            let info = match self.atom_cache.get(&atom_term) {
                Some(Some(info)) => info,
                _ => continue,
            };
            let Some((pair, coefficient)) = Self::normalized_difference_pair(&info.expr) else {
                continue;
            };
            if resolved.contains_key(&pair) {
                continue;
            }

            // Equality atom `expr = 0` asserted true ⟹ k*(a-b) = 0 ⟹ a = b.
            if info.is_eq && !info.is_distinct {
                if atom_value {
                    partial.remove(&pair);
                    resolved.insert(pair, vec![TheoryLit::new(atom_term, true)]);
                }
                continue;
            }
            if info.is_distinct || info.strict || !atom_value {
                continue;
            }

            // Dividing by a negative coefficient reverses the inequality.
            let entails_le = if info.is_le {
                coefficient.is_positive()
            } else {
                coefficient.is_negative()
            };
            let lit = TheoryLit::new(atom_term, atom_value);
            let entry = partial.entry(pair).or_default();
            if entails_le {
                if entry.0.is_none() {
                    entry.0 = Some(lit);
                }
            } else if entry.1.is_none() {
                entry.1 = Some(lit);
            }
            if let (Some(le), Some(ge)) = *entry {
                partial.remove(&pair);
                let reasons = if le.term == ge.term && le.value == ge.value {
                    vec![le]
                } else {
                    vec![le, ge]
                };
                resolved.insert(pair, reasons);
            }
        }

        resolved
    }

    /// Recognize `k*(a-b)` and return `(min(a,b), max(a,b))` plus normalized `k`.
    fn normalized_difference_pair(expr: &LinearExpr) -> Option<((u32, u32), &Rational)> {
        if !expr.constant.is_zero() {
            return None;
        }
        let mut nonzero = expr
            .coeffs
            .iter()
            .filter(|(_, coefficient)| !coefficient.is_zero());
        let (first_var, first_coeff) = nonzero.next()?;
        let (second_var, second_coeff) = nonzero.next()?;
        if nonzero.next().is_some()
            || first_var == second_var
            || (first_coeff + second_coeff) != Rational::zero()
        {
            return None;
        }

        if first_var < second_var {
            Some(((*first_var, *second_var), first_coeff))
        } else {
            Some(((*second_var, *first_var), second_coeff))
        }
    }
}
