// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Typed structural sequence nodes, separate from the general producer fragment.

use super::*;
use crate::term::Symbol;

impl TermStore {
    /// Inspect the exact declared-function registry before interpreting a
    /// sequence head or its length-addition head. A user-owned identity is
    /// never a builtin operation.
    /// This is current structural data, with no declaration or proof grant.
    pub fn try_sequence_head_is_builtin_with_progress(
        &self,
        name: &str,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> std::result::Result<bool, ControlledTermInternError> {
        let mut admission = Admission {
            progress,
            refused: false,
        };
        admission.pay(0, 0)?;
        let result = self.sequence_head_is_builtin(name, &mut admission);
        let final_poll = admission.pay(0, 0);
        match (result, final_poll) {
            (Ok(value), Ok(())) => Ok(value),
            (Err(error), _) | (_, Err(error)) => Err(error),
        }
    }

    fn sequence_head_is_builtin(&self, name: &str, admission: &mut Admission<'_>) -> Result<bool> {
        admission.pay(name.len(), 0)?;
        if !matches!(name, "seq.empty" | "seq.unit" | "seq.++" | "seq.len" | "+") {
            return Ok(false);
        }
        // HashSet stores the same (String, ()) headers as its backing map.
        // Use the checked complete-domain price, including small mirrors,
        // tombstones and the actual incoming hash/equality byte work.
        let cost = crate::kani_compat::hash_table_cost::string_lookup::<(String, ())>(
            self.declared_functions.allocation_size(),
            self.declared_functions.len(),
            name.len(),
        )
        .ok_or(ControlledTermInternError::ResourceLimit)?;
        admission.pay(cost, 0)?;
        Ok(!self.is_declared_function(name))
    }

    /// Construct exactly `seq.unit`, binary `seq.++`, or unary `seq.len`.
    /// The actual live child sorts and complete physical result sort are
    /// admitted before comparison, hashing, copying and reservation. This is
    /// structural construction only; no rewrite or source/proof grant occurs.
    pub fn try_intern_sequence_with_progress(
        &mut self,
        term: &TermData,
        sort: &Sort,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> std::result::Result<TermId, ControlledTermInternError> {
        let mut admission = Admission {
            progress,
            refused: false,
        };
        admission.pay(0, 0)?;
        let result = self.intern_sequence(term, sort, &mut admission);
        let final_poll = admission.pay(0, 0);
        match (result, final_poll) {
            (Ok(id), Ok(())) => Ok(id),
            (Err(error), _) | (_, Err(error)) => Err(error),
        }
    }

    fn intern_sequence(
        &mut self,
        term: &TermData,
        sort: &Sort,
        admission: &mut Admission<'_>,
    ) -> Result<TermId> {
        if self.store_role != StoreRole::Producer {
            return Err(ControlledTermInternError::ReadOnlySnapshot);
        }
        admission.pay(1, 0)?;
        let TermData::App(Symbol::Named(name), args) = term else {
            return Err(ControlledTermInternError::UnsupportedFragment);
        };
        admission.pay(name.len(), 0)?;
        if !matches!(name.as_str(), "seq.unit" | "seq.++" | "seq.len") {
            return Err(ControlledTermInternError::UnsupportedFragment);
        }
        // Exact producer identities, including user declarations with a
        // builtin spelling, are distinguished before interpreting the head.
        if !self.sequence_head_is_builtin(name, admission)? {
            return Err(ControlledTermInternError::UnsupportedFragment);
        }
        if args.len() > 2 || args.iter().any(|&id| self.entry_stamp(id).is_none()) {
            return Err(ControlledTermInternError::InvalidInput);
        }
        let cost = shape::admit_owned_sort(sort, admission)?;
        for &id in args {
            let child = shape::admit_owned_sort(self.sort(id), admission)?;
            // Equality below can traverse both complete sort descriptions.
            admission.pay(child.work.saturating_add(cost.work), 0)?;
        }
        let well_typed = match (name.as_str(), args.as_slice(), sort) {
            ("seq.unit", [element], Sort::Seq(expected)) => {
                self.sort(*element) == expected.as_ref()
            }
            ("seq.++", [left, right], Sort::Seq(_)) => {
                self.sort(*left) == sort && self.sort(*right) == sort
            }
            ("seq.len", [sequence], Sort::Int) => matches!(self.sort(*sequence), Sort::Seq(_)),
            _ => false,
        };
        if !well_typed {
            return Err(ControlledTermInternError::InvalidInput);
        }
        self.intern_controlled_validated(term, sort, Some(&cost), admission)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn controlled_sequence_structural_nodes_preserve_actual_nested_sorts() {
        let mut terms = TermStore::new();
        let element_sort = Sort::array(Sort::Int, Sort::Uninterpreted("owned".into()));
        let element = terms.mk_var("element", element_sort.clone());
        let sort = Sort::seq(element_sort);
        let unit_data = TermData::App(Symbol::named("seq.unit"), vec![element]);
        let unit = terms
            .try_intern_sequence_with_progress(&unit_data, &sort, &mut |_, _| true)
            .unwrap();
        assert_eq!(terms.get(unit), &unit_data);
        assert_eq!(terms.sort(unit), &sort);
        let concat_data = TermData::App(Symbol::named("seq.++"), vec![unit, unit]);
        let concat = terms
            .try_intern_sequence_with_progress(&concat_data, &sort, &mut |_, _| true)
            .unwrap();
        let len_data = TermData::App(Symbol::named("seq.len"), vec![concat]);
        let len = terms
            .try_intern_sequence_with_progress(&len_data, &Sort::Int, &mut |_, _| true)
            .unwrap();
        assert_eq!(terms.get(len), &len_data);
        assert_eq!(terms.sort(len), &Sort::Int);
        // The existing general construction fragment is deliberately unchanged.
        assert_eq!(
            terms.try_intern_with_progress(&unit_data, &sort, &mut |_, _| true),
            Err(ControlledTermInternError::UnsupportedFragment)
        );
    }

    #[test]
    fn controlled_sequence_rejects_wrong_arity_sorts_uf_heads_and_cancelled_copy() {
        let mut terms = TermStore::new();
        let boolean = terms.true_term();
        let before = terms.len();
        for (name, args, sort) in [
            ("seq.unit", vec![boolean], Sort::seq(Sort::Int)),
            ("seq.++", vec![boolean, boolean], Sort::seq(Sort::Bool)),
            ("seq.len", vec![boolean], Sort::Int),
            ("seq.unit", vec![], Sort::seq(Sort::Bool)),
            ("seq.len", vec![boolean, boolean], Sort::Int),
        ] {
            assert!(terms
                .try_intern_sequence_with_progress(
                    &TermData::App(Symbol::named(name), args),
                    &sort,
                    &mut |_, _| true
                )
                .is_err());
        }
        let input = TermData::App(Symbol::named("seq.unit"), vec![boolean]);
        assert_eq!(
            terms.try_intern_sequence_with_progress(
                &input,
                &Sort::seq(Sort::Bool),
                &mut |_, bytes| bytes < 8192
            ),
            Err(ControlledTermInternError::ResourceLimit)
        );
        assert_eq!(terms.len(), before);
        terms.register_declared_function("seq.unit");
        assert_eq!(
            terms.try_intern_sequence_with_progress(&input, &Sort::seq(Sort::Bool), &mut |_, _| {
                true
            }),
            Err(ControlledTermInternError::UnsupportedFragment)
        );
    }
}
