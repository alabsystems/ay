// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Typed prime-field constructors. Foreign/stale handles are rejected normally.
use super::{Solver, SolverError, Term};
use ay_core::{FiniteFieldSort, Sort};
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::ToPrimitive;
impl Solver {
    /// Construct a canonical residue in a checked prime field.
    pub fn finite_field_const(&mut self, value: &BigInt, field: FiniteFieldSort) -> Term {
        // mod_floor is in 0..p, and the authenticated modulus fits u32.
        let residue = value.mod_floor(&BigInt::from(field.modulus()));
        let value = residue.to_u32().unwrap_or(0);
        let t = self.terms_mut().mk_finite_field(value, field);
        self.wrap_term(t)
    }
    /// Render a canonical field residue without capturing a live declaration.
    /// Returns `None` for a noncanonical value or exhausted output controls.
    pub fn format_finite_field_literal(
        &self,
        value: u32,
        field: FiniteFieldSort,
    ) -> Option<String> {
        self.executor.format_field_literal_checked(value, field)
    }

    /// Render a residue while also avoiding the caller's public declaration
    /// namespace. Native adapters can use private engine identities for names
    /// that still capture numeral tokens at their public boundary.
    /// Returns `None` when the bounded search or output controls refuse.
    pub fn format_finite_field_literal_with_bindings(
        &self,
        value: u32,
        field: FiniteFieldSort,
        occupied: impl FnMut(&str) -> bool,
    ) -> Option<String> {
        self.executor
            .format_field_literal_in_namespace_checked(value, field, occupied)
    }

    /// Reuse the same collision-safe literal formatter with the adapter's
    /// original construction owner. This supplies no read or solve authority.
    pub fn format_finite_field_literal_with_admission(
        &self,
        value: u32,
        field: FiniteFieldSort,
        occupied: impl FnMut(&str) -> bool,
        owner: &dyn ay_core::term::TermConstructionAdmission,
    ) -> Option<String> {
        let text = crate::executor_format::format_field_literal_owned(
            &self.executor.ctx,
            value,
            field,
            Some(owner),
            || self.executor.check_evaluation_read().is_ok(),
            occupied,
        );
        owner.check().ok()?;
        text
    }

    /// Evaluate closed arithmetic in one supported field using the independent
    /// model checker. Admission bounds 1024 nodes, 4096 edges/pending entries
    /// and depth 128; free leaves and other operators return `None`.
    pub fn independent_closed_finite_field(&mut self, term: Term) -> Option<Term> {
        use ay_core::kani_compat::{DetHashMap, DetHashSet};
        use ay_core::{Constant, Symbol, TermData};
        let root = self
            .resolve_term("independent_closed_finite_field", term)
            .ok()?;
        let Sort::FiniteField(field) = *self.terms().sort(root) else {
            return None;
        };
        let mut heights = DetHashMap::default();
        let mut active = DetHashSet::default();
        let mut pending = vec![(root, false)];
        let mut edges = 0usize;
        while let Some((id, exiting)) = pending.pop() {
            self.executor.check_evaluation_read().ok()?;
            if id.index() >= self.terms().len()
                || self.terms().sort(id) != &Sort::FiniteField(field)
            {
                return None;
            }
            match self.terms().get(id) {
                TermData::Const(Constant::FiniteField { value, field: q })
                    if q == &field && *value < field.modulus() =>
                {
                    if !heights.contains_key(&id) && heights.len() + active.len() >= 1024 {
                        return None;
                    }
                    heights.insert(id, 1usize);
                }
                TermData::App(Symbol::Named(name), args)
                    if matches!(name.as_str(), "ff.add" | "ff.mul" | "ff.neg" | "ff.bitsum")
                        && (if name == "ff.neg" {
                            args.len() == 1
                        } else {
                            args.len() >= 2
                        })
                        && args.len() <= 1024 =>
                {
                    if exiting {
                        let mut height = 0usize;
                        for a in args {
                            height = height.max(*heights.get(a)?);
                        }
                        let height = height.checked_add(1)?;
                        if height > 128 {
                            return None;
                        }
                        active.remove(&id);
                        heights.insert(id, height);
                    } else if !heights.contains_key(&id) {
                        if active.contains(&id) || heights.len() + active.len() >= 1024 {
                            return None;
                        }
                        edges = edges.checked_add(args.len())?;
                        if edges > 4096
                            || pending.len().checked_add(args.len())?.checked_add(1)? > 4096
                        {
                            return None;
                        }
                        active.insert(id);
                        pending.push((id, true));
                        pending.extend(args.iter().map(|&a| (a, false)));
                    }
                }
                _ => return None,
            }
        }
        struct ClosedView;
        impl ay_model_check::ModelView for ClosedView {
            fn leaf_value(&self, _: ay_core::TermId) -> Option<ay_model_check::ModelValue> {
                None
            }
        }
        // With the admitted depth and edge bounds, the independent memo's
        // depth-sensitive revisits stay below the field slice's 4M visits.
        let outcome = ay_model_check::evaluate_term(self.terms(), &ClosedView, root);
        self.executor.check_evaluation_read().ok()?;
        let ay_model_check::EvalOutcome::Value(ay_model_check::ModelValue::Int(value)) = outcome
        else {
            return None;
        };
        if value < BigInt::from(0) || value >= BigInt::from(field.modulus()) {
            return None;
        }
        Some(self.finite_field_const(&value, field))
    }

    /// Construct addition, multiplication, negation, or positional weighted bitsum.
    pub fn try_finite_field_app(
        &mut self,
        operation: &'static str,
        args: &[Term],
    ) -> Result<Term, SolverError> {
        let mut ids = Vec::with_capacity(args.len());
        for &arg in args {
            ids.push(self.resolve_term(operation, arg)?);
        }
        let term = self.terms_mut().mk_ff_app(operation, &ids).ok_or_else(|| {
            SolverError::SortMismatch {
                operation,
                expected:
                    "one prime field; negation arity 1, other field operators arity at least 2",
                got: ids.iter().map(|&t| self.terms().sort(t).clone()).collect(),
            }
        })?;
        Ok(self.wrap_term(term))
    }
}
