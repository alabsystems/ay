// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact fresh scalar observations through array-bearing datatype values.
//! The independent evaluator composes values; source syntax and printed text
//! never stand in for an evaluated query. Unrelated scalar lanes are unchanged.

use super::super::rendered_dt_limits::SchemaSourceBudget;
use super::*;

const MAX_READ_WORK: usize = 65_536;
const MAX_READ_DEPTH: usize = 128;

impl Executor {
    pub(in crate::executor::model) fn independent_aggregate_read_values(
        &self,
        model: &Model,
        requested: &[(String, TermId)],
    ) -> Result<HashMap<TermId, String>, String> {
        self.check_evaluation_read()?;
        let mut budget = ReadBudget::new();
        let mut candidates = Vec::new();
        let mut output = HashMap::new();
        for (_, term) in requested {
            self.check_evaluation_read()?;
            if self.ctx.terms.entry_stamp(*term).is_none() {
                return Err("model value term is not live".into());
            }
            if scalar_sort(self.ctx.terms.sort(*term)) && model.has_residual_arrays() {
                // The retained owner precedes even classification-time
                // projection validation on the original requested application.
                match self.completed_model_value(model, *term) {
                    Ok(Some(value)) => {
                        budget.charge(self, 1)?;
                        output.try_reserve(1).map_err(|_| resource(self))?;
                        output.insert(*term, render_scalar(self, *term, value, &mut budget)?);
                        continue;
                    }
                    Err(()) => return Err("retained array model value is unavailable".into()),
                    Ok(None) => {}
                }
            }
            if candidate(self, model, *term, &mut budget)? {
                if candidates.len() >= 4096 {
                    return Err(resource(self));
                }
                candidates.try_reserve(1).map_err(|_| resource(self))?;
                candidates.push(*term);
            }
        }
        if candidates.is_empty() {
            self.check_evaluation_read()?;
            return Ok(output);
        }
        if super::super::scoped_term_evaluation_override_active() {
            return Err("aggregate query has an active lexical evaluation scope".into());
        }
        let _caches = GateViewCacheSession::new();
        let view = IndependentModelView::new(self, model);
        preflight_sources(self, &mut budget)?;
        self.check_evaluation_read()?;
        view.ensure_def_index()
            .map_err(|origin| format!("definition roots unavailable: {origin:?}"))?;
        self.check_evaluation_read()?;
        let evaluator = Evaluator::new(&self.ctx.terms, &view);
        output
            .try_reserve(candidates.len())
            .map_err(|_| resource(self))?;
        for term in candidates {
            budget.charge(self, 1)?;
            if output.contains_key(&term) {
                continue;
            }
            // Residual authority is checked on the original application before
            // projection peeling, egraph inspection, or ordinary reconstruction.
            let value = match self.completed_model_value(model, term) {
                Ok(Some(value)) => value,
                Err(()) => return Err("retained array model value is unavailable".into()),
                Ok(None) => {
                    check_boundaries(&view, &evaluator, term, &mut budget)?;
                    exact_value(&view, &evaluator, term, &mut budget)?
                }
            };
            output.insert(term, render_scalar(self, term, value, &mut budget)?);
        }
        self.check_evaluation_read()?;
        Ok(output)
    }
}

fn candidate(
    exec: &Executor,
    model: &Model,
    term: TermId,
    budget: &mut ReadBudget,
) -> Result<bool, String> {
    if exec.ctx.terms.entry_stamp(term).is_none() {
        return Err("model value term is not live".into());
    }
    if !scalar_sort(exec.ctx.terms.sort(term)) {
        return Ok(false);
    }
    let term = peel(exec, model, term)?;
    if selector_receiver(exec, term, budget)?.is_some() {
        return Ok(true);
    }
    let TermData::App(Symbol::Named(name), args) = exec.ctx.terms.get(term) else {
        return Ok(false);
    };
    if name != "select" || !theory_symbol(exec, name) {
        return Ok(false);
    }
    let [array, index] = args.as_slice() else {
        return Ok(false);
    };
    if exec.ctx.terms.entry_stamp(*array).is_none() {
        return Err("aggregate select receiver is not live".into());
    }
    budget.sort(exec, exec.ctx.terms.sort(*array))?;
    let array = peel(exec, model, *array)?;
    if selector_receiver(exec, array, budget)?.is_none() {
        return Ok(false);
    }
    let Sort::Array(sort) = exec.ctx.terms.sort(array) else {
        return Err("aggregate select receiver is not an array".into());
    };
    if exec.ctx.terms.entry_stamp(*index).is_none()
        || exec.ctx.terms.sort(*index) != &sort.index_sort
        || exec.ctx.terms.sort(term) != &sort.element_sort
    {
        return Err("aggregate select signature mismatch".into());
    }
    Ok(true)
}

fn scalar_sort(sort: &Sort) -> bool {
    matches!(
        sort,
        Sort::Bool | Sort::Int | Sort::Real | Sort::String | Sort::BitVec(_)
    )
}

fn render_scalar(
    exec: &Executor,
    term: TermId,
    value: ModelValue,
    budget: &mut ReadBudget,
) -> Result<String, String> {
    let sort = exec.ctx.terms.sort(term);
    if !scalar_matches(&value, sort) {
        return Err("aggregate query has no exact scalar value of the requested sort".into());
    }
    if !budget.parse.charge_value(&value) {
        return Err(resource(exec));
    }
    if let ModelValue::BitVec { width, .. } = &value {
        // Preserve wider existing residual scalar values, but prepay their
        // full binary rendering width before formatting (hex is cheaper).
        let width = usize::try_from(*width).map_err(|_| resource(exec))?;
        budget.charge(exec, width.div_ceil(64))?;
    }
    let rendered = exec
        .format_gate_model_value(&value, sort)
        .ok_or_else(|| "aggregate query value cannot be rendered exactly".to_string())?;
    if !budget.parse.charge_text(&rendered) {
        return Err(resource(exec));
    }
    exec.check_evaluation_read()?;
    Ok(rendered)
}

fn selector_receiver(
    exec: &Executor,
    term: TermId,
    budget: &mut ReadBudget,
) -> Result<Option<TermId>, String> {
    let TermData::App(Symbol::Named(name), args) = exec.ctx.terms.get(term) else {
        return Ok(None);
    };
    let Some(info) = exec.ctx.exact_datatype_member_info(name) else {
        return Ok(None);
    };
    if info.declaration_kind() != DeclarationKind::DatatypeSelector {
        return Ok(None);
    }
    let [receiver] = args.as_slice() else {
        return Err("aggregate selector arity mismatch".into());
    };
    if exec.ctx.terms.entry_stamp(*receiver).is_none() {
        return Err("aggregate selector receiver is not live".into());
    }
    for sort in info.arg_sorts.iter().chain([
        &info.sort,
        exec.ctx.terms.sort(*receiver),
        exec.ctx.terms.sort(term),
    ]) {
        budget.sort(exec, sort)?;
    }
    if info.arg_sorts.len() != 1
        || info.arg_sorts.first() != Some(exec.ctx.terms.sort(*receiver))
        || &info.sort != exec.ctx.terms.sort(term)
    {
        return Err("aggregate selector signature mismatch".into());
    }
    Ok(exec
        .datatype_sort_carries_array_field(exec.ctx.terms.sort(*receiver))
        .then_some(*receiver))
}

fn theory_symbol(exec: &Executor, name: &str) -> bool {
    exec.ctx.symbol_info_by_identity(name).is_none_or(|info| {
        exec.ctx.effective_declaration_kind(info.declaration_id()) == Some(DeclarationKind::Theory)
    })
}

fn peel(exec: &Executor, model: &Model, term: TermId) -> Result<TermId, String> {
    model
        .projection_ufs
        .peel_application_chain(&exec.ctx.terms, term)
        .map(|selected| selected.unwrap_or(term))
        .map_err(|error| error.to_string())
}

struct ReadBudget {
    remaining: usize,
    parse: TypedArrayParseBudget,
    semantic: SemanticNormalizationBudget,
}

impl ReadBudget {
    fn new() -> Self {
        Self {
            remaining: MAX_READ_WORK,
            parse: TypedArrayParseBudget::new(),
            semantic: SemanticNormalizationBudget::new(),
        }
    }

    fn charge(&mut self, exec: &Executor, work: usize) -> Result<(), String> {
        exec.check_evaluation_read()?;
        self.remaining = self
            .remaining
            .checked_sub(work)
            .ok_or_else(|| resource(exec))?;
        Ok(())
    }

    fn sort(&mut self, exec: &Executor, sort: &Sort) -> Result<(), String> {
        exec.check_evaluation_read()?;
        // The 1024-node descriptor bound applies to ONE borrowed descriptor;
        // repeated uses charge the shared query work, not a new model-wide
        // 1024-node ceiling. No descriptor clone or recursive hash is needed.
        let mut source = SchemaSourceBudget::new();
        if !source.charge_sort(sort) {
            return Err(resource(exec));
        }
        let work = source.work().ok_or_else(|| resource(exec))?;
        self.charge(exec, work.div_ceil(64))
    }
}

fn resource(exec: &Executor) -> String {
    exec.record_evaluation_stop(crate::executor_types::UnknownOrigin::DeterministicResourceBudget);
    "aggregate model query resource limit".into()
}

fn exact_value(
    view: &IndependentModelView<'_>,
    evaluator: &Evaluator<'_>,
    term: TermId,
    budget: &mut ReadBudget,
) -> Result<ModelValue, String> {
    budget.charge(view.exec, 1)?;
    let result = evaluator.evaluate(term);
    view.exec.check_evaluation_read()?;
    match result {
        EvalOutcome::Value(value) => Ok(value),
        EvalOutcome::Unevaluable(reason) => {
            Err(format!("aggregate model query is unavailable: {reason}"))
        }
    }
}

fn check_boundaries(
    view: &IndependentModelView<'_>,
    evaluator: &Evaluator<'_>,
    root: TermId,
    budget: &mut ReadBudget,
) -> Result<(), String> {
    let exec = view.exec;
    let mut pending = vec![(root, 0usize)];
    let mut seen = HashSet::new();
    let mut boundaries = Vec::new();
    while let Some((term, depth)) = pending.pop() {
        budget.charge(exec, 1)?;
        if depth > MAX_READ_DEPTH || exec.ctx.terms.entry_stamp(term).is_none() {
            return Err(resource(exec));
        }
        seen.try_reserve(1).map_err(|_| resource(exec))?;
        if !seen.insert(term) {
            continue;
        }
        budget.sort(exec, exec.ctx.terms.sort(term))?;
        if let Some(index) = view
            .projection_argument(term)
            .map_err(|error| error.to_string())?
        {
            let TermData::App(_, args) = exec.ctx.terms.get(term) else {
                return Err("projection is not an application".into());
            };
            let selected = *args.get(index).ok_or("projection argument is missing")?;
            pending.push((selected, depth + 1));
            continue;
        }
        if exec.datatype_sort_name(exec.ctx.terms.sort(term)).is_some() {
            budget.sort(exec, exec.ctx.terms.sort(term))?;
            boundaries.try_reserve(1).map_err(|_| resource(exec))?;
            boundaries.push(term);
        }
        let branches;
        let children: &[TermId] = match exec.ctx.terms.get(term) {
            TermData::Const(_) | TermData::Var(_, _) => &[],
            TermData::App(_, args) => args,
            TermData::Not(child) => std::slice::from_ref(child),
            TermData::Let(bindings, body) if bindings.is_empty() => std::slice::from_ref(body),
            TermData::Ite(condition, yes, no) => {
                branches = [*condition, *yes, *no];
                &branches
            }
            // This admission slice is deliberately binder-free. The
            // existing independent evaluator still handles exact definitions;
            // no contextual value may be evaluated in a fresh empty scope here.
            _ => return Err("aggregate query dependency shape is unsupported".into()),
        };
        let definitions = view.def_index.borrow();
        let definitions = definitions.as_ref().and_then(|index| index.get(&term));
        let count = children
            .len()
            .checked_add(definitions.map_or(0, Vec::len))
            .ok_or_else(|| resource(exec))?;
        budget.charge(exec, count)?;
        pending.try_reserve(count).map_err(|_| resource(exec))?;
        pending.extend(children.iter().map(|&child| (child, depth + 1)));
        if let Some(definitions) = definitions {
            pending.extend(definitions.iter().map(|&value| (value, depth + 1)));
        }
    }
    // No compositional/egraph value is evaluated until the complete syntactic
    // and indexed-definition cone has been censused and charged.
    for term in boundaries {
        budget.charge(exec, 1)?;
        if exec.dt_egraph_class_poisoned(view.model, term) {
            return Err("datatype model class is incoherent".into());
        }
        if let Some(rendered) = exec.dt_egraph_value(view.model, term) {
            let committed = exec
                .parse_rendered_value_with_budget(
                    &rendered,
                    exec.ctx.terms.sort(term),
                    view.datatype_guard(),
                    0,
                    &mut budget.parse,
                )
                .ok_or("committed datatype value cannot be decoded exactly")?;
            let computed = exact_value(view, evaluator, term, budget)?;
            let left = normalize_datatype_array_value(&committed, &mut budget.semantic)
                .ok_or_else(|| resource(exec))?;
            let right = normalize_datatype_array_value(&computed, &mut budget.semantic)
                .ok_or_else(|| resource(exec))?;
            if left != right {
                return Err("aggregate query disagrees with committed datatype value".into());
            }
        }
    }
    exec.check_evaluation_read()
}

fn scalar_matches(value: &ModelValue, sort: &Sort) -> bool {
    match (value, sort) {
        (ModelValue::Bool(_), Sort::Bool)
        | (ModelValue::Int(_), Sort::Int)
        | (ModelValue::Str(_), Sort::String) => true,
        (ModelValue::Real(value), Sort::Real) => value.denom() > &num_bigint::BigInt::from(0),
        (ModelValue::BitVec { value, width }, Sort::BitVec(expected)) => {
            *width > 0
                && *width == expected.width
                && value.sign() != num_bigint::Sign::Minus
                && value.bits() <= u64::from(*width)
        }
        _ => false,
    }
}

fn preflight_sources(exec: &Executor, budget: &mut ReadBudget) -> Result<(), String> {
    let roots = exec
        .independent_gate_authored_assertions
        .as_deref()
        .unwrap_or(&exec.ctx.assertions);
    let assumptions = exec.last_assumptions.as_deref().unwrap_or_default();
    let count = roots
        .len()
        .checked_add(assumptions.len())
        .ok_or_else(|| resource(exec))?;
    let comparisons = assumptions
        .len()
        .checked_mul(count)
        .ok_or_else(|| resource(exec))?;
    budget.charge(
        exec,
        count
            .checked_add(comparisons)
            .ok_or_else(|| resource(exec))?,
    )?;
    let mut pending = Vec::new();
    pending
        .try_reserve_exact(count)
        .map_err(|_| resource(exec))?;
    pending.extend(roots.iter().chain(assumptions).map(|&term| (term, 0usize)));
    let mut seen = HashSet::new();
    while let Some((term, depth)) = pending.pop() {
        budget.charge(exec, 1)?;
        if depth > MAX_READ_DEPTH || exec.ctx.terms.entry_stamp(term).is_none() {
            return Err(resource(exec));
        }
        seen.try_reserve(1).map_err(|_| resource(exec))?;
        if !seen.insert(term) {
            continue;
        }
        budget.sort(exec, exec.ctx.terms.sort(term))?;
        let mut push = |child| -> Result<(), String> {
            budget.charge(exec, 1)?;
            pending.try_reserve(1).map_err(|_| resource(exec))?;
            pending.push((child, depth + 1));
            Ok(())
        };
        match exec.ctx.terms.get(term) {
            TermData::Const(_) | TermData::Var(_, _) => {}
            TermData::App(_, args) => {
                for &arg in args {
                    push(arg)?;
                }
            }
            TermData::Not(child) => push(*child)?,
            TermData::Ite(condition, yes, no) => {
                push(*condition)?;
                push(*yes)?;
                push(*no)?;
            }
            TermData::Let(bindings, body) => {
                for (_, value) in bindings {
                    push(*value)?;
                }
                push(*body)?;
            }
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => push(*body)?,
            _ => return Err("aggregate query source shape is unsupported".into()),
        }
    }
    exec.check_evaluation_read()
}

#[cfg(test)]
mod tests;
