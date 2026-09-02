// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact observed-field installation for datatype construction.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::TermId;
use ay_model_check::ModelValue;

use super::super::datatype_array_fields::ExactDatatypeArrayFields;
use super::{
    dt_canonical_pin_supported, dt_canonical_string, eval_to_mv, exact_datatype_sort_name,
    mv_to_eval, DtBuilder, DtConstructionResult, EvalValue,
};

impl DtBuilder<'_> {
    pub(super) fn finish_forced_datatype(
        &mut self,
        root: usize,
        ctor: &str,
        args: Vec<ModelValue>,
        path: &mut Vec<usize>,
        fuel: u32,
    ) -> Option<ModelValue> {
        self.finish_constructed_datatype(
            root,
            ModelValue::Datatype {
                ctor: ctor.to_string(),
                args,
            },
            path,
            fuel,
        )
    }

    pub(super) fn finish_constructed_datatype(
        &mut self,
        root: usize,
        candidate: ModelValue,
        path: &mut Vec<usize>,
        fuel: u32,
    ) -> Option<ModelValue> {
        self.apply_committed_fields(root, candidate, path, fuel)
    }

    /// Overwrite observed fields with values already committed by their
    /// selector applications. Exact array fields use the class reconstruction
    /// certificate; partial or contradictory class evidence fails closed.
    fn apply_committed_fields(
        &mut self,
        root: usize,
        candidate: ModelValue,
        path: &mut Vec<usize>,
        fuel: u32,
    ) -> Option<ModelValue> {
        let ModelValue::Datatype { ctor, mut args } = candidate else {
            return Some(candidate);
        };
        let fields = self.bounded_constructor_fields(&ctor)?;
        if !self
            .work_budget
            .charge_field_scans(fields.len(), self.sel_apps.len(), 0)
        {
            return None;
        }
        let members: HashSet<TermId> = self
            .members
            .get(&root)
            .into_iter()
            .flatten()
            .map(|&member| self.terms[member])
            .collect();
        self.exact_array_classes.remove(&root);
        if self.exact_array_class_rejected {
            return None;
        }
        let (exact_arrays, exact_authority) = match self.exec.exact_datatype_array_fields(
            self.model,
            &members,
            &ctor,
            &args,
            &mut self.exact_array_field_work,
        ) {
            ExactDatatypeArrayFields::NotApplicable => (HashMap::default(), None),
            ExactDatatypeArrayFields::Complete(completion) => {
                (completion.fields, Some(completion.authority))
            }
            ExactDatatypeArrayFields::Rejected => {
                self.exact_array_class_rejected = true;
                return None;
            }
        };
        for (index, (selector, sort)) in fields.iter().enumerate() {
            if let Some(value) = exact_arrays.get(&index) {
                *args.get_mut(index)? = value.clone();
                continue;
            }
            if exact_datatype_sort_name(sort).is_some() {
                self.install_datatype_field(index, selector, &members, &mut args, path, fuel);
            } else {
                self.install_scalar_field(index, selector, sort, &members, &mut args);
            }
        }
        if let Some(authority) = exact_authority {
            self.exact_array_classes.insert(root, authority);
        }
        Some(ModelValue::Datatype { ctor, args })
    }

    fn install_datatype_field(
        &mut self,
        index: usize,
        selector: &str,
        members: &HashSet<TermId>,
        args: &mut [ModelValue],
        path: &mut Vec<usize>,
        fuel: u32,
    ) {
        let field_class = self
            .sel_apps
            .iter()
            .filter(|(_, candidate, arg)| candidate == selector && members.contains(arg))
            .find_map(|(app, _, _)| self.index.get(app).copied())
            .map(|term| self.class_of[term]);
        let Some(value) =
            field_class.and_then(|class| self.construct_class(class, path, fuel.saturating_sub(1)))
        else {
            return;
        };
        if let Some(slot) = args.get_mut(index) {
            *slot = value;
        }
    }

    fn install_scalar_field(
        &self,
        index: usize,
        selector: &str,
        sort: &ay_core::Sort,
        members: &HashSet<TermId>,
        args: &mut [ModelValue],
    ) {
        let mut committed = None;
        for (app, candidate, arg) in &self.sel_apps {
            if candidate != selector || !members.contains(arg) {
                continue;
            }
            let value = self.scalar_term_value(*app);
            if matches!(value, EvalValue::Unknown) {
                continue;
            }
            let Some(value) = eval_to_mv(&value, sort) else {
                continue;
            };
            match &committed {
                Some(previous) if dt_canonical_string(previous) != dt_canonical_string(&value) => {
                    return;
                }
                Some(_) => {}
                None => committed = Some(value),
            }
        }
        if let (Some(value), Some(slot)) = (committed, args.get_mut(index)) {
            *slot = value;
        }
    }
}

impl DtBuilder<'_> {
    /// Produce the constructed ground values and evaluation pins to commit
    /// into the model: `(ground, pins)` where `ground` maps datatype-sorted
    /// terms to their structured values and `pins` carries every evaluation
    /// pin (canonical Elements, scalar selector projections, tester Bools).
    pub(super) fn finish(&mut self) -> Option<DtConstructionResult> {
        // All pins are computed before any is inserted, so committed lookups
        // cannot read half-committed state.
        let mut pins = self.finish_scalar_selector_pins()?;
        pins.extend(self.finish_tester_pins()?);
        let ground = self.finish_ground_values(&mut pins)?;
        let mut roots: Vec<_> = self.exact_array_classes.keys().copied().collect();
        roots.sort_unstable();
        let array_field_classes = if self.exact_array_class_rejected {
            Vec::new()
        } else {
            roots
                .into_iter()
                .filter(|root| matches!(self.values.get(root), Some(Some(_))))
                .filter_map(|root| self.exact_array_classes.get(&root).cloned())
                .collect()
        };
        Some(DtConstructionResult {
            ground,
            pins,
            array_field_classes,
        })
    }

    fn scalar_selector_groups(&self) -> HashMap<(String, usize), Vec<TermId>> {
        let mut groups: HashMap<(String, usize), Vec<TermId>> = HashMap::default();
        for (app, sel, arg) in &self.sel_apps {
            if self.index.contains_key(app) {
                continue; // datatype-sorted selector app: valued via its class
            }
            let Some(&ai) = self.index.get(arg) else {
                continue;
            };
            let root = self.class_of[ai];
            groups.entry((sel.clone(), root)).or_default().push(*app);
        }
        groups
    }

    fn finish_scalar_selector_pins(&mut self) -> Option<Vec<(TermId, EvalValue)>> {
        let mut pins = Vec::new();
        let mut groups = self.scalar_selector_groups();
        let mut group_keys: Vec<(String, usize)> = groups.keys().cloned().collect();
        group_keys.sort();
        for key in group_keys {
            let mut apps = groups.remove(&key).unwrap_or_default();
            apps.sort_by_key(|t| t.index());
            apps.dedup();
            let Some(pin) = self.scalar_selector_group_pin(&key.0, key.1, &apps)? else {
                continue;
            };
            for app in apps {
                if !self.work_budget.charge_scalar_pin(&pin) {
                    return None;
                }
                pins.push((app, pin.clone()));
            }
        }
        Some(pins)
    }

    fn scalar_selector_group_pin(
        &mut self,
        selector: &str,
        root: usize,
        apps: &[TermId],
    ) -> Option<Option<EvalValue>> {
        let Some(Some(ModelValue::Datatype { ctor, args })) = self.values.get(&root) else {
            return Some(None);
        };
        let selectors = self.exec.ctx.constructor_selectors(ctor).unwrap_or(&[]);
        if let Some(field) = selectors
            .iter()
            .position(|candidate| candidate == selector)
            .and_then(|index| args.get(index))
        {
            if !self.work_budget.charge_value(field) {
                return None;
            }
            let pin = mv_to_eval(field);
            // `EvalValue` cannot carry an array and the active opaque lane
            // deliberately does not admit sequence-valued scalar pins.  Do
            // not let one such selector discard the completed datatype model
            // for every independent component: retain the exact structured
            // field in `dt_ground`, where the independent gate projects it
            // from the constructor value itself, and omit only the lossy
            // evaluator pin.  No value is coerced or defaulted here.
            return Some(
                matches!(
                    &pin,
                    EvalValue::Bool(_)
                        | EvalValue::BitVec { .. }
                        | EvalValue::Rational(_)
                        | EvalValue::Element(_)
                        | EvalValue::String(_)
                )
                .then_some(pin),
            );
        }
        for &app in apps {
            let value = self.scalar_term_value(app);
            if !matches!(value, EvalValue::Unknown) {
                return self
                    .work_budget
                    .charge_scalar_pin(&value)
                    .then_some(Some(value));
            }
        }
        let Some(&first) = apps.first() else {
            return Some(None);
        };
        let sort = self.exec.ctx.terms.sort(first).clone();
        let Some(value) = self.base_default(&sort, &mut Vec::new()) else {
            return Some(None);
        };
        if !self.work_budget.charge_value(&value) {
            return None;
        }
        let pin = mv_to_eval(&value);
        Some(
            matches!(
                &pin,
                EvalValue::Bool(_)
                    | EvalValue::BitVec { .. }
                    | EvalValue::Rational(_)
                    | EvalValue::Element(_)
                    | EvalValue::String(_)
            )
            .then_some(pin),
        )
    }

    fn finish_tester_pins(&mut self) -> Option<Vec<(TermId, EvalValue)>> {
        let mut pins = Vec::new();
        for (app, ctor, arg) in &self.tester_apps {
            let Some(&ai) = self.index.get(arg) else {
                continue;
            };
            let root = self.class_of[ai];
            if let Some(Some(ModelValue::Datatype { ctor: assigned, .. })) = self.values.get(&root)
            {
                if !self.work_budget.charge_bytes(1) {
                    return None;
                }
                pins.push((*app, EvalValue::Bool(assigned == ctor)));
            }
        }
        Some(pins)
    }

    fn finish_ground_values(
        &mut self,
        pins: &mut Vec<(TermId, EvalValue)>,
    ) -> Option<Vec<(TermId, ModelValue)>> {
        let mut ground: Vec<(TermId, ModelValue)> = Vec::new();
        let mut roots: Vec<usize> = self.values.keys().copied().collect();
        roots.sort_unstable();
        for root in roots {
            let Some(Some(value)) = self.values.get(&root) else {
                continue;
            };
            let canon = if dt_canonical_pin_supported(value) {
                if !self.work_budget.charge_render(value) {
                    return None;
                }
                Some(dt_canonical_string(value))
            } else {
                None
            };
            for &m in self.members.get(&root).into_iter().flatten() {
                let t = self.terms[m];
                if !self.work_budget.charge_value(value) {
                    return None;
                }
                ground.push((t, value.clone()));
                if let Some(canon) = &canon {
                    if !self.work_budget.charge_bytes(canon.len()) {
                        return None;
                    }
                    pins.push((t, EvalValue::Element(canon.clone())));
                }
            }
        }
        Some(ground)
    }
}
