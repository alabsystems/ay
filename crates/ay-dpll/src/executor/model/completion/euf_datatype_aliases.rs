// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Recover opaque variable leaves from complete, agreeing constructor members
//! of their current typed EUF class. This supplies candidate model values, not
//! equality evidence or a verdict. Every ordinary validator still runs.

use super::*;
use ay_core::term::Constant;
use ay_model_check::ModelValue;

const MAX_ALIAS_NODES: usize = 4096;
const MAX_ALIAS_TERMS: usize = 1024;
const MAX_ALIAS_ROUNDS: usize = 32;
const MAX_ALIAS_WORK: usize = 65_536;
const MAX_ALIAS_BYTES: usize = 1_048_576;
const MAX_CONSTRUCTOR_DEPTH: usize = 64;

#[derive(Default)]
struct ConstructorClass {
    members: Vec<TermId>,
    constructors: Vec<TermId>,
    non_nullary: bool,
}

#[derive(Default)]
struct AliasBudget {
    nodes: usize,
    bytes: usize,
    exhausted: bool,
}

impl AliasBudget {
    fn spend(&mut self, bytes: usize) -> bool {
        self.nodes = self.nodes.saturating_add(1);
        self.bytes = self.bytes.saturating_add(bytes);
        self.exhausted |= self.nodes > MAX_ALIAS_WORK || self.bytes > MAX_ALIAS_BYTES;
        !self.exhausted
    }

    // Charge the expanded tree before cloning it or rendering a canonical pin.
    fn value(&mut self, value: &ModelValue, depth: usize) -> bool {
        if depth >= MAX_CONSTRUCTOR_DEPTH {
            self.exhausted = true;
            return false;
        }
        match value {
            ModelValue::Bool(_) => self.spend(5),
            ModelValue::BitVec { width, .. } => self.spend(*width as usize + 2),
            ModelValue::Datatype { ctor, args } => {
                self.spend(ctor.len().saturating_add(args.len()).saturating_add(3))
                    && args.iter().all(|value| self.value(value, depth + 1))
            }
            _ => false,
        }
    }
}

// Compare only the exact value shapes this producer admits. The candidate is
// already construction-budgeted; a mismatched shape or depth refuses recovery.
fn exact_alias_value_eq(left: &ModelValue, right: &ModelValue, depth: usize) -> bool {
    if depth >= MAX_CONSTRUCTOR_DEPTH {
        return false;
    }
    match (left, right) {
        (ModelValue::Bool(left), ModelValue::Bool(right)) => left == right,
        (
            ModelValue::BitVec {
                width: left_width,
                value: left_value,
            },
            ModelValue::BitVec {
                width: right_width,
                value: right_value,
            },
        ) => left_width == right_width && left_value == right_value,
        (
            ModelValue::Datatype {
                ctor: left_ctor,
                args: left_args,
            },
            ModelValue::Datatype {
                ctor: right_ctor,
                args: right_args,
            },
        ) => {
            left_ctor == right_ctor
                && left_args.len() == right_args.len()
                && left_args
                    .iter()
                    .zip(right_args)
                    .all(|(left, right)| exact_alias_value_eq(left, right, depth + 1))
        }
        _ => false,
    }
}

impl Executor {
    pub(in crate::executor::model) fn complete_euf_datatype_constructor_aliases(
        &self,
        model: &mut Model,
        extra_roots: &[TermId],
    ) -> usize {
        // Preserve the exported/lazy datatype engine's single-source ownership.
        if self.ctx.datatype_iter().next().is_none()
            || self.dt_theory_model.is_some()
            || self.dt_lazy_splits.is_some()
        {
            return 0;
        }
        let Some(classes) = self.collect_euf_constructor_classes(model, extra_roots) else {
            return 0;
        };
        let mut budget = AliasBudget::default();
        let Some(recovered) = self.derive_euf_constructor_aliases(model, &classes, &mut budget)
        else {
            return 0;
        };
        let Some(prepared) = self.prepare_euf_alias_pins(model, recovered, &mut budget) else {
            return 0;
        };
        if self.poll_evaluation_stop().is_err() {
            return 0;
        }
        // Never pin constructor applications, ITEs or array selects: their
        // syntax and array interpretation must remain independently checked.
        let mut installed = 0;
        for (term, value, pin) in prepared {
            if installed == 0 {
                // Model-relative authority cannot survive a semantic write.
                model.revoke_all_quantified_model_seals();
                super::super::eval_memo_clear();
            }
            model.dt_ground.insert(term, value);
            model.dt_pins.insert(term, pin);
            installed += 1;
        }
        installed
    }

    fn prepare_euf_alias_pins(
        &self,
        model: &Model,
        recovered: HashMap<TermId, ModelValue>,
        budget: &mut AliasBudget,
    ) -> Option<Vec<(TermId, ModelValue, EvalValue)>> {
        let mut prepared = Vec::new();
        for (term, value) in recovered {
            if model.dt_ground.contains_key(&term) || model.dt_pins.contains_key(&term) {
                continue;
            }
            if !budget.value(&value, 0) {
                return None;
            }
            let pin = super::super::dt_construct::mv_to_eval(&value);
            prepared.push((term, value, pin));
        }
        prepared.sort_by_key(|(term, _, _)| term.index());
        Some(prepared)
    }

    /// Build one current-root index, rather than scanning all terms per leaf.
    fn collect_euf_constructor_classes(
        &self,
        model: &Model,
        extra_roots: &[TermId],
    ) -> Option<Vec<ConstructorClass>> {
        let euf = model.euf_model.as_ref()?;
        let mut classes: HashMap<(Sort, String), ConstructorClass> = HashMap::default();
        let mut seen = HashSet::default();
        let mut stack = self.datatype_model_collection_roots(extra_roots)?;
        if stack.len() > MAX_ALIAS_NODES {
            return None;
        }
        let mut datatype_terms = 0;
        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            if seen.len() > MAX_ALIAS_NODES || self.evaluation_stop_origin().is_some() {
                return None;
            }
            let sort = self.ctx.terms.sort(term);
            if let Some(datatype) = self.datatype_sort_name(sort) {
                if datatype.len() > 256 {
                    return None;
                }
                if let Some(element) = euf.term_values.get(&term) {
                    if element.len() > 1024 {
                        return None;
                    }
                    datatype_terms += 1;
                    if datatype_terms > MAX_ALIAS_TERMS {
                        return None;
                    }
                    let class = classes.entry((sort.clone(), element.clone())).or_default();
                    class.members.push(term);
                    match self.ctx.terms.get(term) {
                        TermData::App(Symbol::Named(name), args)
                            if self.ctx.is_live_datatype_member_identity(name)
                                && self.ctx.is_constructor(name).is_some() =>
                        {
                            class.constructors.push(term);
                            class.non_nullary |= !args.is_empty();
                        }
                        TermData::Var(name, _)
                            if self.ctx.is_live_datatype_member_identity(name)
                                && self.ctx.is_constructor(name).is_some() =>
                        {
                            // A nullary constructor is a Var, and must still
                            // refute a different constructor in this class.
                            class.constructors.push(term);
                        }
                        _ => {}
                    }
                }
            }
            match self.ctx.terms.get(term) {
                TermData::Forall(..) | TermData::Exists(..) | TermData::Let(..) => {}
                _ => {
                    let children = self.ctx.terms.children(term);
                    if stack.len().saturating_add(children.len()) > MAX_ALIAS_NODES {
                        return None;
                    }
                    stack.extend(children);
                }
            }
        }
        let mut classes: Vec<_> = classes.into_values().filter(|c| c.non_nullary).collect();
        for class in &mut classes {
            class.members.sort_by_key(|term| term.index());
            class.constructors.sort_by_key(|term| term.index());
        }
        classes.sort_by_key(|class| class.members[0].index());
        Some(classes)
    }

    /// Resolve complete class values in a bounded fixed point before any write.
    fn derive_euf_constructor_aliases(
        &self,
        model: &Model,
        classes: &[ConstructorClass],
        budget: &mut AliasBudget,
    ) -> Option<HashMap<TermId, ModelValue>> {
        let mut done = vec![false; classes.len()];
        let mut recovered = HashMap::default();
        for _ in 0..MAX_ALIAS_ROUNDS {
            if self.poll_evaluation_stop().is_err() {
                return None;
            }
            let mut progress = false;
            for (index, class) in classes.iter().enumerate() {
                if done[index] {
                    continue;
                }
                let mut candidate = None;
                let mut complete = true;
                let mut conflict = false;
                for &constructor in &class.constructors {
                    let Some(value) =
                        self.euf_constructor_candidate(model, &recovered, constructor, 0, budget)
                    else {
                        complete = false;
                        break;
                    };
                    if candidate
                        .as_ref()
                        .is_some_and(|previous| !exact_alias_value_eq(previous, &value, 0))
                    {
                        conflict = true;
                        break;
                    }
                    candidate = Some(value);
                }
                if budget.exhausted {
                    return None;
                }
                if !complete {
                    continue;
                }
                let Some(value) = candidate else { continue };
                if !budget.value(&value, 0) {
                    return None;
                }
                let pin = super::super::dt_construct::mv_to_eval(&value);
                conflict |= class.members.iter().any(|term| {
                    model
                        .dt_ground
                        .get(term)
                        .is_some_and(|old| !exact_alias_value_eq(old, &value, 0))
                        || model.dt_pins.get(term).is_some_and(|old| old != &pin)
                });
                done[index] = true;
                if conflict {
                    continue;
                }
                for &term in &class.members {
                    if let TermData::Var(name, _) = self.ctx.terms.get(term) {
                        if self.ctx.is_constructor(name).is_none() {
                            if !budget.value(&value, 0) {
                                return None;
                            }
                            recovered.insert(term, value.clone());
                            progress = true;
                        }
                    }
                }
            }
            if !progress {
                break;
            }
        }
        Some(recovered)
    }

    fn euf_constructor_candidate(
        &self,
        model: &Model,
        recovered: &HashMap<TermId, ModelValue>,
        term: TermId,
        depth: usize,
        budget: &mut AliasBudget,
    ) -> Option<ModelValue> {
        if !budget.spend(0) {
            return None;
        }
        if depth >= MAX_CONSTRUCTOR_DEPTH {
            budget.exhausted = true;
            return None;
        }
        let sort = self.ctx.terms.sort(term);
        let datatype = self.datatype_sort_name(sort)?;
        let (name, arguments) = match self.ctx.terms.get(term) {
            TermData::Var(name, _) => {
                if self.ctx.is_constructor(name).is_none() {
                    // Only values derived by this pass may supply a nested
                    // alias; never inherit another completion's free defaults.
                    let value = recovered.get(&term)?;
                    if !budget.value(value, depth) {
                        return None;
                    }
                    return Some(value.clone());
                }
                (name.as_str(), &[][..])
            }
            TermData::App(Symbol::Named(name), arguments) => (name.as_str(), arguments.as_slice()),
            _ => return None,
        };
        if name.len() > 256 || !self.ctx.is_live_datatype_member_identity(name) {
            return None;
        }
        let (declared_datatype, constructor) = self.ctx.is_constructor(name)?;
        if declared_datatype != datatype {
            return None;
        }
        let fields = self.ctx.constructor_selector_info(&constructor)?;
        if fields.len() != arguments.len() {
            return None;
        }
        if !budget.spend(
            constructor
                .len()
                .saturating_add(arguments.len())
                .saturating_add(3),
        ) {
            return None;
        }
        let mut values = Vec::with_capacity(arguments.len());
        for (&argument, (_, field_sort)) in arguments.iter().zip(fields) {
            if self.ctx.terms.sort(argument) != field_sort {
                return None;
            }
            let value = if self.datatype_sort_name(field_sort).is_some() {
                self.euf_constructor_candidate(model, recovered, argument, depth + 1, budget)?
            } else {
                // Only exact scalar values are admitted; no printed defaults,
                // opaque datatype tokens, arrays or uncommitted scalar fields.
                self.euf_constructor_scalar(model, argument, field_sort, budget)?
            };
            values.push(value);
        }
        Some(ModelValue::Datatype {
            ctor: constructor,
            args: values,
        })
    }

    fn euf_constructor_scalar(
        &self,
        model: &Model,
        term: TermId,
        sort: &Sort,
        budget: &mut AliasBudget,
    ) -> Option<ModelValue> {
        // Read only literal or producer-committed Bool/BV values. The general
        // evaluator can prefer completion pins or invent a scalar default.
        let value = match sort {
            Sort::Bool => {
                let literal = match self.ctx.terms.get(term) {
                    TermData::Const(Constant::Bool(value)) => Some(*value),
                    _ => None,
                };
                let sources = [
                    literal,
                    self.term_value(&model.sat_model, &model.term_to_var, term),
                    model.bool_overrides.get(&term).copied(),
                    model
                        .bv_model
                        .as_ref()
                        .and_then(|bv| bv.bool_overrides.get(&term).copied()),
                ];
                let value = sources.iter().flatten().copied().next()?;
                if sources.iter().flatten().any(|other| *other != value) {
                    return None;
                }
                if !budget.spend(5) {
                    return None;
                }
                ModelValue::Bool(value)
            }
            Sort::BitVec(bits) => {
                let literal = match self.ctx.terms.get(term) {
                    TermData::Const(Constant::BitVec { value, width }) if *width == bits.width => {
                        Some(value)
                    }
                    _ => None,
                };
                let raw = model.bv_model.as_ref().and_then(|bv| bv.values.get(&term));
                if literal.zip(raw).is_some_and(|(a, b)| a != b) {
                    return None;
                }
                let value = literal.or(raw)?;
                if value.sign() == num_bigint::Sign::Minus || value.bits() > u64::from(bits.width) {
                    return None;
                }
                if !budget.spend(bits.width as usize + 2) {
                    return None;
                }
                super::super::dt_construct::eval_to_mv(
                    &EvalValue::BitVec {
                        value: value.clone(),
                        width: bits.width,
                    },
                    sort,
                )?
            }
            _ => return None,
        };
        let expected = super::super::dt_construct::mv_to_eval(&value);
        if model.dt_pins.get(&term).is_some_and(|pin| pin != &expected) {
            return None;
        }
        Some(value)
    }
}
