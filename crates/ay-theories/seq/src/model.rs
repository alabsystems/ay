// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Concrete model extraction for structural sequence terms.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::{Constant, TermData, TermId, TermStore};
use num_bigint::BigInt;

use super::{SeqModel, SeqSolver};

impl SeqSolver<'_> {
    /// Extract a model for Seq-sorted variables.
    ///
    /// Builds concrete sequence values from asserted equalities and the
    /// structure of unit/concat/empty terms.
    pub fn extract_model(&self) -> SeqModel {
        let mut values = HashMap::default();

        // For each Seq-sorted variable, try to determine its concrete value
        // from asserted equalities.
        for (&eq_term, &(lhs, rhs)) in &self.equality_cache {
            if self.assigns.get(&eq_term) != Some(&true) {
                continue;
            }
            Self::try_insert_seq_value(&mut values, lhs, rhs, self.terms, self);
            Self::try_insert_seq_value(&mut values, rhs, lhs, self.terms, self);
        }

        // Also check shared equalities from Nelson-Oppen exchange (EUF → Seq).
        // These are equalities discovered by EUF congruence/transitivity that
        // involve Seq-sorted terms but were never direct assertion atoms.
        for (lhs, rhs, _reason) in &self.shared_equalities {
            Self::try_insert_seq_value(&mut values, *lhs, *rhs, self.terms, self);
            Self::try_insert_seq_value(&mut values, *rhs, *lhs, self.terms, self);
        }

        SeqModel { values }
    }

    /// If `candidate` is a Seq-sorted variable and `value_term` can be
    /// concretized, insert the mapping into `values`.
    fn try_insert_seq_value(
        values: &mut HashMap<TermId, Vec<String>>,
        candidate: TermId,
        value_term: TermId,
        terms: &TermStore,
        solver: &Self,
    ) {
        if let TermData::Var(_, _) = terms.get(candidate) {
            if terms.sort(candidate).is_seq() {
                if let Some(elems) = solver.extract_seq_value(value_term) {
                    values.insert(candidate, elems);
                }
            }
        }
    }

    /// Try to extract a concrete sequence value from a term.
    /// Returns `Some(vec_of_element_strings)` for constructible terms,
    /// `None` for symbolic terms that can't be concretized.
    pub(super) fn extract_seq_value(&self, term: TermId) -> Option<Vec<String>> {
        // seq.empty → []
        if self.empty_cache.contains(&term) {
            return Some(Vec::new());
        }
        // seq.unit(x) → [format(x)]
        if let Some(&elem) = self.unit_cache.get(&term) {
            return Some(vec![self.format_term_value(elem)]);
        }
        // seq.++(a, b) → extract(a) ++ extract(b)
        if let Some(args) = self.concat_cache.get(&term) {
            let mut result = Vec::new();
            for &arg in args {
                let sub = self.extract_seq_value(arg)?;
                result.extend(sub);
            }
            return Some(result);
        }
        None
    }

    /// Format a term's value for SMT-LIB model output.
    fn format_term_value(&self, term: TermId) -> String {
        match self.terms.get(term) {
            TermData::Const(c) => match c {
                Constant::Bool(b) => format!("{b}"),
                Constant::Int(n) => {
                    if *n < BigInt::from(0) {
                        format!("(- {})", -n)
                    } else {
                        format!("{n}")
                    }
                }
                Constant::Rational(r) => {
                    let n = r.0.numer();
                    let d = r.0.denom();
                    if *d == BigInt::from(1) {
                        format!("{n}")
                    } else {
                        format!("(/ {n} {d})")
                    }
                }
                Constant::BitVec { value, width } => {
                    format!("(_ bv{value} {width})")
                }
                Constant::String(s) => format!("\"{s}\""),
                _ => format!("{c:?}"),
            },
            TermData::Var(name, _) => name.clone(),
            _ => format!("t{}", term.0),
        }
    }
}
