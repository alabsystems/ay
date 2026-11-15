// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Positive-only structural evaluation of exact datatype constructors.
//! Opaque EUF labels are not the value of an explicit constructor application.
//! Unsupported or incomplete fields retain the existing evaluator path.

use super::{EvalValue, Executor, Model, Sort, Symbol, TermData, TermId};
use ay_core::term::Constant;
use ay_model_check::ModelValue;
use std::borrow::Cow;
use std::cell::OnceCell;

use super::rendered_dt_guard::RenderedDatatypeGuard;

const MAX_NODES: usize = 65_536;
const MAX_BYTES: usize = 1_048_576;
const MAX_DEPTH: usize = 64;
const MAX_NAME_BYTES: usize = 256;

#[derive(Default)]
pub(in crate::executor::model) struct ConstructorBudget {
    nodes: usize,
    bytes: usize,
    exhausted: bool,
    rendered_guard: OnceCell<RenderedDatatypeGuard>,
}

impl ConstructorBudget {
    pub(in crate::executor::model) fn charge(&mut self, bytes: usize, depth: usize) -> Option<()> {
        self.nodes = self.nodes.saturating_add(1);
        self.bytes = self.bytes.saturating_add(bytes);
        self.exhausted |= depth >= MAX_DEPTH || self.nodes > MAX_NODES || self.bytes > MAX_BYTES;
        (!self.exhausted).then_some(())
    }

    pub(in crate::executor::model) fn exhausted(&self) -> bool {
        self.exhausted
    }

    fn can_hold_children(&mut self, count: usize) -> bool {
        let fits = count <= MAX_NODES.saturating_sub(self.nodes);
        self.exhausted |= !fits;
        fits
    }
}

impl Executor {
    /// Prefer a fully known constructor value over the constructor's raw EUF
    /// class label. This neither installs a pin nor grants model authority.
    /// Malformed exact applications refuse; unavailable fields keep the old
    /// path, including its ordinary fail-closed validation.
    pub(super) fn evaluate_exact_datatype_constructor(
        &self,
        model: &Model,
        term: TermId,
    ) -> Option<EvalValue> {
        // A model-owned certificate or contextual materializer may interpret
        // a field ahead of ordinary raw slots. Preserve that existing owner.
        if super::scoped_term_evaluation_override_active()
            || model.residual_arrays.is_some()
            || !model.certified_const_interp_entries().is_empty()
            || !model.certified_total_ufs.by_symbol.is_empty()
            || !model.certified_total_ufs.ground_pins.is_empty()
            || model.projection_ufs.has_interpretations()
            || !model.formula_neutral_function_default_entries().is_empty()
        {
            return None;
        }
        let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(term) else {
            return None;
        };
        if name.len() > MAX_NAME_BYTES || !self.ctx.is_live_datatype_member_identity(name) {
            return None;
        }
        let sort = self.ctx.terms.sort(term);
        // Named registry carriers are the proven fragment. Do not interpret
        // inline/parameterized datatype sorts by their name alone.
        if !matches!(sort, Sort::Uninterpreted(_)) {
            return None;
        }
        let (datatype, constructor) = self.ctx.is_constructor(name)?;
        let Some(fields) = self.ctx.constructor_selector_info(&constructor) else {
            return Some(EvalValue::Unknown);
        };
        // Apply the work cap before scanning either attacker-sized slice.
        if args.len() > MAX_NODES || fields.len() > MAX_NODES {
            return None;
        }
        if !Self::constructor_sort_matches(sort, &datatype) || fields.len() != args.len() {
            return Some(EvalValue::Unknown);
        }
        if args.is_empty() {
            return None;
        }
        if args.iter().zip(fields).any(|(&arg, (_, expected))| {
            self.ctx.terms.entry_stamp(arg).is_none() || self.ctx.terms.sort(arg) != expected
        }) {
            return Some(EvalValue::Unknown);
        }
        let mut budget = ConstructorBudget::default();
        let value = self.read_constructor_value(model, term, sort, 0, &mut budget)?;
        // Charge the expanded result again before recursive rendering. Each
        // ground subtree was already checked before cloning into this value.
        self.check_constructor_value(&value, sort, 0, &mut budget)?;
        self.format_gate_model_value(&value, sort)
            .map(EvalValue::Element)
    }

    fn constructor_sort_matches(sort: &Sort, datatype: &str) -> bool {
        match sort {
            Sort::Uninterpreted(name) => name == datatype,
            _ => false,
        }
    }

    fn constructor_shape<'a>(
        &'a self,
        name: &str,
        sort: &Sort,
        count: usize,
    ) -> Option<(String, &'a [(String, Sort)], usize)> {
        if name.len() > MAX_NAME_BYTES || !self.ctx.is_live_datatype_member_identity(name) {
            return None;
        }
        let (declared_datatype, constructor) = self.ctx.is_constructor(name)?;
        if !Self::constructor_sort_matches(sort, &declared_datatype)
            || constructor.len() > MAX_NAME_BYTES
        {
            return None;
        }
        let fields = self.ctx.constructor_selector_info(&constructor)?;
        let surface = self.dt_surface(&constructor);
        if fields.len() != count
            || surface.len() > MAX_NAME_BYTES
            || ay_core::quote_symbol(surface) != surface
        {
            return None;
        }
        let bytes = constructor
            .len()
            .checked_add(surface.len())?
            .checked_add(count)?
            .checked_add(3)?;
        Some((constructor, fields, bytes))
    }

    fn read_constructor_value(
        &self,
        model: &Model,
        term: TermId,
        sort: &Sort,
        depth: usize,
        budget: &mut ConstructorBudget,
    ) -> Option<ModelValue> {
        if self.ctx.terms.entry_stamp(term).is_none() || self.ctx.terms.sort(term) != sort {
            return None;
        }
        if matches!(sort, Sort::Bool | Sort::BitVec(_)) {
            return self.read_constructor_scalar(model, term, sort, depth, budget);
        }
        if !matches!(sort, Sort::Uninterpreted(_)) {
            return None;
        }
        let (name, args): (&str, &[TermId]) = match self.ctx.terms.get(term) {
            TermData::Var(name, _) if self.ctx.is_constructor(name).is_none() => {
                return self.read_constructor_leaf(model, term, sort, depth, budget);
            }
            TermData::Var(name, _) => (name, &[]),
            TermData::App(Symbol::Named(name), args)
                if name.len() <= MAX_NAME_BYTES
                    && self
                        .ctx
                        .exact_datatype_member_info(name)
                        .is_some_and(|info| {
                            info.declaration_kind()
                                == ay_frontend::DeclarationKind::DatatypeSelector
                        }) =>
            {
                // Only an exact observed selector with a typed ground value
                // may join constructor rebuilding. Never interpret raw UF
                // text or a term-only pin as a selector's aggregate value.
                let [argument] = args.as_slice() else {
                    return None;
                };
                let info = self.ctx.exact_datatype_member_info(name)?;
                if name.len() > MAX_NAME_BYTES
                    || !self.ctx.is_live_datatype_member_identity(name)
                    || self.ctx.terms.entry_stamp(*argument).is_none()
                    || info.arg_sorts.len() != 1
                    || info.arg_sorts.first() != Some(self.ctx.terms.sort(*argument))
                    || &info.sort != sort
                    || !model.dt_ground.contains_key(&term)
                {
                    return None;
                }
                return self.read_constructor_leaf(model, term, sort, depth, budget);
            }
            TermData::App(Symbol::Named(name), args) => (name, args),
            _ => return None,
        };
        let (constructor, fields, bytes) = self.constructor_shape(name, sort, args.len())?;
        budget.charge(bytes, depth)?;
        if !budget.can_hold_children(args.len()) {
            return None;
        }
        let mut values = Vec::with_capacity(args.len());
        for (&arg, (_, field_sort)) in args.iter().zip(fields) {
            values.push(self.read_constructor_value(model, arg, field_sort, depth + 1, budget)?);
        }
        Some(ModelValue::Datatype {
            ctor: constructor,
            args: values,
        })
    }

    /// Read this exact term's already structured model value. An opaque
    /// EUF class token supplies no constructor evidence and cannot be expanded.
    ///
    /// Neither does a raw slot holding a bare nullary constructor: that is an
    /// element label (the finite-domain lane exports every enum value by its
    /// constructor's name), not structure. Rebuilding an application over it
    /// sets the application apart from its own EUF class, whose other members
    /// keep the class element: in that lane's accepted model
    /// `(= q1!rl (cons e1 (cons e1 x2)))` compared `@dtfd!7` with
    /// `(cons K3 (cons K3 (cons K3 nil)))`, and a genuine SAT degraded. The
    /// completion's seeding reads raw text as structure on the same terms
    /// (`completion/structured_datatypes.rs`: parenthesized text only).
    ///
    /// Declining is the reading this evaluator had before raw slots were read
    /// at all, so this reader no longer tells two applications of one class
    /// apart by their leaves' labels (`(MkPair t t)` and `(MkPair s s)` with
    /// `t = Red` and `s = Green`), as it did not before. Such a model is
    /// refused where acceptance is decided: the independent gate composes
    /// every constructor application from its arguments on its own
    /// (`ay_model_check` `eval_datatype`) and does not confirm it
    /// (`raw_labels` tests).
    fn read_constructor_leaf(
        &self,
        model: &Model,
        term: TermId,
        sort: &Sort,
        depth: usize,
        budget: &mut ConstructorBudget,
    ) -> Option<ModelValue> {
        let value = if let Some(value) = model.dt_ground.get(&term) {
            self.check_constructor_value(value, sort, depth, budget)?;
            Cow::Borrowed(value)
        } else {
            let value =
                self.read_structured_euf_datatype_value(model, term, sort, depth, budget)?;
            if matches!(&value, ModelValue::Datatype { args, .. } if args.is_empty()) {
                return None;
            }
            Cow::Owned(value)
        };
        // Preserve the current higher-priority slot consistency checks. This
        // extension changes only where a missing typed ground value is read.
        for pin in model
            .dt_pins
            .get(&term)
            .into_iter()
            .chain(model.completed_values.get(&term))
        {
            self.check_constructor_value(&value, sort, depth, budget)?;
            if pin != &super::dt_construct::mv_to_eval(&value) {
                return None;
            }
        }
        Some(value.into_owned())
    }

    /// Parse only this term's own structured EUF value, with the same type
    /// and resource checks as ordinary constructor evaluation.
    pub(in crate::executor::model) fn read_structured_euf_datatype_value(
        &self,
        model: &Model,
        term: TermId,
        sort: &Sort,
        depth: usize,
        budget: &mut ConstructorBudget,
    ) -> Option<ModelValue> {
        let text = model.euf_model.as_ref()?.term_values.get(&term)?;
        // Charge before parsing/cloning; the parser also bounds its syntax
        // tree before allocation and rejects non-constructor datatype tokens.
        budget.charge(text.len(), depth)?;
        let guard = budget
            .rendered_guard
            .get_or_init(|| RenderedDatatypeGuard::new(self));
        let value = self.parse_rendered_dt_value_cached(text, sort, guard)?;
        self.check_constructor_value(&value, sort, depth, budget)?;
        Some(value)
    }

    /// Validate type, expanded size, and scalar representation before cloning
    /// a model-owned ground tree or rendering the final result.
    pub(in crate::executor::model) fn check_constructor_value(
        &self,
        value: &ModelValue,
        sort: &Sort,
        depth: usize,
        budget: &mut ConstructorBudget,
    ) -> Option<()> {
        match (value, sort) {
            (ModelValue::Bool(_), Sort::Bool) => budget.charge(5, depth),
            (ModelValue::BitVec { width, value }, Sort::BitVec(bits))
                if *width == bits.width
                    && value.sign() != num_bigint::Sign::Minus
                    && value.bits() <= u64::from(*width) =>
            {
                budget.charge(usize::try_from(*width).ok()?.checked_add(2)?, depth)
            }
            (ModelValue::Datatype { ctor, args }, _) => {
                let (_, fields, bytes) = self.constructor_shape(ctor, sort, args.len())?;
                budget.charge(bytes, depth)?;
                if !budget.can_hold_children(args.len()) {
                    return None;
                }
                for (arg, (_, field_sort)) in args.iter().zip(fields) {
                    self.check_constructor_value(arg, field_sort, depth + 1, budget)?;
                }
                Some(())
            }
            _ => None,
        }
    }

    /// A semantic datatype pin precedes raw theory slots in evaluate_term.
    /// Constructor rebuilding must read that same scalar assignment. A bad
    /// pin refuses this structural attempt; it is never replaced by raw data.
    fn read_pinned_constructor_scalar(
        &self,
        term: TermId,
        pin: &EvalValue,
        sort: &Sort,
        depth: usize,
        budget: &mut ConstructorBudget,
    ) -> Option<ModelValue> {
        match (pin, sort) {
            (EvalValue::Bool(value), Sort::Bool) => {
                match self.ctx.terms.get(term) {
                    TermData::Const(Constant::Bool(literal)) if literal == value => {}
                    TermData::Const(_) => return None,
                    _ => {}
                }
                budget.charge(5, depth)?;
                Some(ModelValue::Bool(*value))
            }
            (EvalValue::BitVec { value, width }, Sort::BitVec(bits)) => {
                if *width != bits.width
                    || value.sign() == num_bigint::Sign::Minus
                    || value.bits() > u64::from(*width)
                {
                    return None;
                }
                match self.ctx.terms.get(term) {
                    TermData::Const(Constant::BitVec {
                        value: literal,
                        width: literal_width,
                    }) if literal_width == width && literal == value => {}
                    TermData::Const(_) => return None,
                    _ => {}
                }
                // Check width/sign/magnitude and charge before the BigInt clone.
                budget.charge(usize::try_from(*width).ok()?.checked_add(2)?, depth)?;
                Some(ModelValue::BitVec {
                    width: *width,
                    value: value.clone(),
                })
            }
            _ => None,
        }
    }

    fn read_constructor_scalar(
        &self,
        model: &Model,
        term: TermId,
        sort: &Sort,
        depth: usize,
        budget: &mut ConstructorBudget,
    ) -> Option<ModelValue> {
        if let Some(pin) = model.dt_pins.get(&term) {
            return self.read_pinned_constructor_scalar(term, pin, sort, depth, budget);
        }
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
                budget.charge(5, depth)?;
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
                if literal.zip(raw).is_some_and(|(left, right)| left != right) {
                    return None;
                }
                let value = literal.or(raw)?;
                if value.sign() == num_bigint::Sign::Minus || value.bits() > u64::from(bits.width) {
                    return None;
                }
                budget.charge(usize::try_from(bits.width).ok()?.checked_add(2)?, depth)?;
                ModelValue::BitVec {
                    width: bits.width,
                    value: value.clone(),
                }
            }
            _ => return None,
        };
        let agrees = |pin: &EvalValue| match (&value, pin) {
            (ModelValue::Bool(value), EvalValue::Bool(pin)) => value == pin,
            (
                ModelValue::BitVec { width, value },
                EvalValue::BitVec {
                    width: pin_width,
                    value: pin_value,
                },
            ) => width == pin_width && value == pin_value,
            _ => false,
        };
        let conflicting_pin = model.dt_pins.get(&term).is_some_and(|pin| !agrees(pin))
            || model
                .completed_values
                .get(&term)
                .is_some_and(|pin| !agrees(pin));
        (!conflicting_pin).then_some(value)
    }
}
