// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Reconnect eliminated datatype definitions before allocating model carriers.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::TermData;
use ay_core::TermId;

use super::carrier_sort_key;
use crate::executor::Executor;

impl Executor {
    /// A datatype variable eliminated by preprocessing still denotes its exact
    /// replacement. The restored source equality may mention an ITE, while the
    /// final replacement is a reduced constructor term absent from those roots.
    /// Allocate one candidate carrier for both, rather than unrelated defaults.
    /// Called only for terms reached by the current carrier collection; follow
    /// replacement dependencies through that same visited set and scope.
    /// This adds no SAT authority: conflicting existing values remain blocked,
    /// and every original assertion still passes the unchanged model gates.
    pub(super) fn datatype_carrier_definition(
        &self,
        from: TermId,
        allow_uninterpreted: bool,
        authenticated: Option<&HashSet<TermId>>,
    ) -> Option<TermId> {
        let &to = self.recorded_var_substitutions.get(&from)?;
        let eligible = |term| {
            carrier_sort_key(
                self.ctx.terms.sort(term),
                allow_uninterpreted || authenticated.is_some_and(|terms| terms.contains(&term)),
            )
            .is_some()
        };
        (matches!(self.ctx.terms.get(from), TermData::Var(..))
            && self.datatype_sort_name(self.ctx.terms.sort(from)).is_some()
            && self.ctx.terms.sort(from) == self.ctx.terms.sort(to)
            && eligible(from)
            && eligible(to))
        .then_some(to)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::executor::model::{EvalValue, Model};
    use ay_core::term::Symbol;
    use ay_core::Sort;

    fn fixture() -> (Executor, Model, TermId, TermId) {
        let mut exec = Executor::new();
        let commands = ay_frontend::parse(
            "(declare-datatype Cell ((cell (bits (_ BitVec 8))) (other)))
             (declare-const eliminated Cell)",
        )
        .expect("valid carrier declarations");
        exec.execute_all(&commands).expect("declarations execute");
        let from = exec.ctx.symbol_info("eliminated").unwrap().term.unwrap();
        // A single-constructor declaration expands to a constructor over
        // fresh fields. Match the real multi-constructor R carrier instead.
        assert!(matches!(exec.ctx.terms.get(from), TermData::Var(..)));
        let sort = exec.ctx.terms.sort(from).clone();
        let bits = exec.ctx.terms.mk_bitvec(3.into(), 8);
        let to = exec
            .ctx
            .terms
            .mk_app(Symbol::named("cell"), vec![bits], sort);
        exec.recorded_var_substitutions.insert(from, to);
        assert_eq!(exec.datatype_carrier_definition(from, true, None), Some(to));
        let root = exec
            .ctx
            .terms
            .mk_app(Symbol::named("="), vec![from, from], Sort::Bool);
        exec.ctx.assertions.push(root);
        let mut model = Model::empty();
        model.bv_model = Some(ay_bv::BvModel {
            values: Default::default(),
            term_to_bits: Default::default(),
            bool_overrides: Default::default(),
        });
        model
            .completed_values
            .insert(from, EvalValue::Element("(cell #x03)".into()));
        (exec, model, from, to)
    }

    #[test]
    fn concrete_recovery_keeps_recorded_datatype_class_link() {
        let (mut exec, mut model, from, to) = fixture();
        let concrete = model.completed_values[&from].clone();
        assert_eq!(exec.evaluate_term(&model, from), concrete);
        assert!(model.euf_model.is_none(), "match the BV producer");
        let epoch = model.seal_cegqi_uf_recompletion();
        exec.complete_uninterpreted_sort_model(&mut model, &[], None);
        assert!(!model.carries_cegqi_uf_recompletion(&epoch));
        let classes = &model.euf_model.as_ref().unwrap().term_values;
        assert_eq!(classes.get(&from), classes.get(&to));
        assert_eq!(classes[&from], "@Cell!0");
        assert_eq!(model.completed_values[&from], concrete);
        assert!(model.dt_ground.is_empty() && model.dt_pins.is_empty());
        assert_eq!(
            exec.dt_egraph_value(&model, from).as_deref(),
            Some("(cell #x03)")
        );
    }

    #[test]
    fn recorded_datatype_link_preserves_existing_class_conflict() {
        let (mut exec, mut model, from, to) = fixture();
        let mut euf = ay_euf::EufModel::default();
        euf.term_values.insert(to, "@Cell!existing".into());
        euf.term_values.insert(from, "@Cell!conflict".into());
        model.euf_model = Some(euf);
        let before = model.euf_model.as_ref().unwrap().term_values.clone();
        let _ = exec.dt_egraph_value(&model, from);
        let cached = exec
            .dt_egraph_assignment
            .borrow()
            .clone()
            .expect("seeded assignment");
        let epoch = model.seal_cegqi_uf_recompletion();
        exec.complete_uninterpreted_sort_model(&mut model, &[], None);
        assert!(model.carries_cegqi_uf_recompletion(&epoch));
        assert_eq!(model.euf_model.as_ref().unwrap().term_values, before);
        assert!(std::sync::Arc::ptr_eq(
            &cached,
            exec.dt_egraph_assignment.borrow().as_ref().unwrap()
        ));
    }

    #[test]
    fn historical_datatype_definition_does_not_create_class_link() {
        let (mut exec, mut model, _, _) = fixture();
        exec.ctx.assertions.clear();
        exec.complete_uninterpreted_sort_model(&mut model, &[], None);
        assert!(model.euf_model.is_none());
    }

    #[test]
    fn conflicting_concrete_recovery_does_not_acquire_raw_class() {
        let (mut exec, mut model, from, _) = fixture();
        let conflicting = EvalValue::Element("(cell #x04)".into());
        model.completed_values.insert(from, conflicting.clone());
        model.dt_pins.insert(from, conflicting.clone());
        assert_eq!(exec.evaluate_term(&model, from), conflicting);
        exec.complete_uninterpreted_sort_model(&mut model, &[], None);
        assert!(model.euf_model.is_none());
        assert_eq!(model.completed_values[&from], conflicting);
        assert_eq!(exec.evaluate_term(&model, from), conflicting);
    }

    #[test]
    fn mismatched_sort_definition_does_not_acquire_raw_class() {
        let (mut exec, mut model, from, _) = fixture();
        let wrong_sort = exec.ctx.terms.mk_int(3.into());
        exec.recorded_var_substitutions.insert(from, wrong_sort);
        assert_eq!(exec.datatype_carrier_definition(from, true, None), None);
        let concrete = model.completed_values[&from].clone();
        assert_eq!(exec.evaluate_term(&model, from), concrete);
        exec.complete_uninterpreted_sort_model(&mut model, &[], None);
        assert!(model.euf_model.is_none());
        assert_eq!(exec.evaluate_term(&model, from), concrete);
    }

    #[test]
    fn inserted_datatype_class_link_retires_the_previous_assignment() {
        let (mut exec, mut model, from, to) = fixture();
        model.euf_model = Some(Default::default());
        let _ = exec.dt_egraph_value(&model, from);
        let cached = exec
            .dt_egraph_assignment
            .borrow()
            .clone()
            .expect("seeded assignment");
        let concrete = model.completed_values[&from].clone();
        assert_eq!(exec.evaluate_term(&model, from), concrete);
        assert_eq!(exec.evaluate_term(&model, to), concrete);
        exec.complete_uninterpreted_sort_model(&mut model, &[], None);
        let classes = &model.euf_model.as_ref().unwrap().term_values;
        assert_eq!(classes.get(&from), classes.get(&to));
        assert!(
            classes.contains_key(&to),
            "the constructor owns a raw class entry"
        );
        assert!(exec.dt_egraph_assignment.borrow().is_none());
        assert_eq!(
            exec.dt_egraph_value(&model, from).as_deref(),
            Some("(cell #x03)")
        );
        assert!(!std::sync::Arc::ptr_eq(
            &cached,
            exec.dt_egraph_assignment.borrow().as_ref().unwrap()
        ));
    }
}
