// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Independent evaluation of closed total model function bodies. Ambient
//! application pins never supply a value inside a symbolic parameter frame.

use super::*;

struct SymbolicCallGuard<'a>(&'a RefCell<Vec<Symbol>>, usize);
impl Drop for SymbolicCallGuard<'_> {
    fn drop(&mut self) {
        self.0.borrow_mut().truncate(self.1);
    }
}

mod numeric;
#[cfg(test)]
mod tests;

impl Evaluator<'_> {
    pub(super) fn validate_symbolic_currency(&self) -> EvalResult<()> {
        let count = self.symbolic_definitions.borrow().len();
        for index in 0..count {
            self.admit_evaluation(1, 0)?;
            let origin = self
                .symbolic_definitions
                .borrow()
                .get(index)
                .map(|entry| entry.3)
                .ok_or("symbolic definition ledger changed during currency check")?;
            // No ledger borrow crosses either externally implemented hook or
            // admission callback. Cached parents owe the same currentness as
            // direct function applications, even when their DAG is memoized.
            let view = self
                .model
                .symbolic_function(origin)?
                .ok_or("symbolic function interpretation disappeared before memo reuse")?;
            self.charge_sequence_work(
                view.symbol
                    .name()
                    .len()
                    .saturating_add(view.parameters.len())
                    .saturating_add(1),
            )?;
            let definitions = self.symbolic_definitions.borrow();
            let Some((head, parameters, body, recorded_origin)) = definitions.get(index) else {
                return Err("symbolic definition ledger changed during currency check".into());
            };
            if definitions.len() != count
                || *recorded_origin != origin
                || head != view.symbol
                || parameters.as_slice() != view.parameters
                || *body != view.body
            {
                return Err("symbolic function interpretation changed before memo reuse".into());
            }
        }
        Ok(())
    }

    pub(super) fn require_symbolic_function_absent(&self, name: &str) -> EvalResult<()> {
        let count = self.symbolic_definitions.borrow().len();
        self.charge_sequence_work(count.saturating_mul(name.len().saturating_add(1)))?;
        if self
            .symbolic_definitions
            .borrow()
            .iter()
            .any(|(head, _, _, _)| head.name() == name)
        {
            return Err("symbolic function interpretation disappeared during evaluation".into());
        }
        Ok(())
    }

    pub(super) fn eval_symbolic_application(
        &self,
        application: TermId,
        arguments: &[TermId],
        depth: usize,
        view: crate::SymbolicFunctionView<'_>,
    ) -> EvalResult<ModelValue> {
        let TermData::App(symbol, _) = self.terms.get(application) else {
            return Err("symbolic function does not own an application".into());
        };
        let (Symbol::Named(actual), Symbol::Named(expected)) = (symbol, view.symbol) else {
            return Err("symbolic function requires a named core identity".into());
        };
        self.admit_evaluation(
            actual.len().saturating_add(expected.len()),
            arguments
                .len()
                .saturating_mul(std::mem::size_of::<LocalBinding>()),
        )?;
        self.charge_sequence_work(
            arguments
                .len()
                .saturating_add(actual.len())
                .saturating_add(expected.len()),
        )?;
        if actual != expected
            || arguments.len() != view.parameters.len()
            || arguments.len() > 256
            || view.parameters.is_empty()
            || self.terms.entry_stamp(view.body).is_none()
            || !self.sequence_instance_sorts_equal(
                self.terms.sort(application),
                self.terms.sort(view.body),
            )?
        {
            return Err("symbolic function head, arity or result sort mismatch".into());
        }
        for (index, (&parameter, &argument)) in view.parameters.iter().zip(arguments).enumerate() {
            self.charge_sequence_work(index.saturating_add(1))?;
            if self.terms.entry_stamp(parameter).is_none()
                || self.terms.entry_stamp(argument).is_none()
                || !matches!(self.terms.get(parameter), TermData::Var(..))
                || view.parameters[..index].contains(&parameter)
                || !self.sequence_instance_sorts_equal(
                    self.terms.sort(parameter),
                    self.terms.sort(argument),
                )?
            {
                return Err("symbolic function formal identity or argument sort mismatch".into());
            }
        }
        self.admit_symbolic_body(view.body, view.parameters)?;
        let graph_len = self.uf_graph.borrow().len();
        self.charge_sequence_work(graph_len.saturating_mul(actual.len().saturating_add(1)))?;
        if self
            .uf_graph
            .borrow()
            .iter()
            .any(|(head, _, _, _)| head == actual)
        {
            return Err("symbolic function appeared after a model-backed interpretation".into());
        }

        // A ModelView may be implemented by an external consumer. A mutable
        // callback cannot change a function between two applications and make
        // contradictory constraints each observe a different total function.
        let (definition_count, definition_capacity) = {
            let definitions = self.symbolic_definitions.borrow();
            (definitions.len(), definitions.capacity())
        };
        self.charge_sequence_work(
            definition_count.saturating_mul(
                actual
                    .len()
                    .saturating_add(view.parameters.len())
                    .saturating_add(1),
            ),
        )?;
        let prior = {
            let definitions = self.symbolic_definitions.borrow();
            if definitions.len() != definition_count {
                return Err("symbolic definition ledger changed during admission".into());
            }
            definitions.iter().find_map(|(head, parameters, body, _)| {
                (head == view.symbol)
                    .then_some((parameters.as_slice() == view.parameters && *body == view.body))
            })
        };
        match prior {
            Some(false) => {
                return Err("symbolic function interpretation changed during evaluation".into())
            }
            Some(true) => {}
            None => {
                let bytes = std::mem::size_of::<(Symbol, Vec<TermId>, TermId, TermId)>()
                    .saturating_mul(
                        definition_count
                            .saturating_add(1)
                            .saturating_add(definition_capacity),
                    )
                    .saturating_add(actual.len())
                    .saturating_add(
                        view.parameters
                            .len()
                            .saturating_mul(std::mem::size_of::<TermId>()),
                    );
                self.admit_evaluation(view.parameters.len().saturating_add(actual.len()), bytes)?;
                let entry = (
                    view.symbol.clone(),
                    view.parameters.to_vec(),
                    view.body,
                    application,
                );
                let mut definitions = self.symbolic_definitions.borrow_mut();
                definitions
                    .try_reserve_exact(1)
                    .map_err(|_| "symbolic function ledger allocation refused")?;
                definitions.push(entry);
            }
        }

        // Nested source applications in arguments complete before entering the
        // function's body. Thus f(f(7)) is finite syntax, while a body edge back
        // to an active head is a refused recursive interpretation.
        let values = self.eval_all(arguments, depth)?;
        for (&parameter, value) in view.parameters.iter().zip(&values) {
            self.ensure_value_inhabits_sort(value, self.terms.sort(parameter))?;
        }
        let (active_len, active_capacity) = {
            let active = self.symbolic_active.borrow();
            (active.len(), active.capacity())
        };
        self.admit_evaluation(
            active_len.saturating_mul(actual.len().saturating_add(1)),
            active_len
                .saturating_add(1)
                .saturating_add(active_capacity)
                .saturating_mul(std::mem::size_of::<Symbol>())
                .saturating_add(actual.len()),
        )?;
        self.charge_sequence_work(active_len.saturating_mul(actual.len().saturating_add(1)))?;
        {
            let mut active = self.symbolic_active.borrow_mut();
            if active.len() != active_len || active_len >= 64 || active.contains(view.symbol) {
                return Err("symbolic function has a recursive or excessive call graph".into());
            }
            active
                .try_reserve_exact(1)
                .map_err(|_| "symbolic call guard allocation refused")?;
            active.push(view.symbol.clone());
        }
        let _call = SymbolicCallGuard(&self.symbolic_active, active_len);

        let (restore_len, restore_capacity) = {
            let bindings = self.local_bindings.borrow();
            (bindings.len(), bindings.capacity())
        };
        let _guard = LocalBindingGuard {
            bindings: &self.local_bindings,
            restore_len,
        };
        // Copies run before each mutable borrow, with the original admission
        // owner active. The guard also restores a partially installed frame.
        self.admit_evaluation(
            restore_len,
            restore_len
                .saturating_add(values.len())
                .saturating_add(restore_capacity)
                .saturating_mul(std::mem::size_of::<LocalBinding>()),
        )?;
        if self.local_bindings.borrow().len() != restore_len {
            return Err("symbolic binding frame changed during admission".into());
        }
        self.local_bindings
            .borrow_mut()
            .try_reserve_exact(values.len())
            .map_err(|_| "symbolic formal frame allocation refused")?;
        for (&parameter, value) in view.parameters.iter().zip(&values) {
            let value = self.clone_value(value)?;
            self.local_bindings.borrow_mut().push(LocalBinding {
                variable: LocalVariable::Term(parameter),
                value,
            });
        }
        let value = self.eval(view.body, depth.saturating_add(1))?;
        self.ensure_value_inhabits_sort(&value, self.terms.sort(application))?;
        Ok(value)
    }

    fn admit_symbolic_body(&self, body: TermId, parameters: &[TermId]) -> EvalResult<()> {
        self.admit_evaluation(1, std::mem::size_of::<(TermId, usize)>())?;
        let mut pending = vec![(body, 0usize)];
        let mut occurrences = 0usize;
        while let Some((term, depth)) = pending.pop() {
            self.charge_sequence_work(1)?;
            occurrences = occurrences
                .checked_add(1)
                .ok_or("symbolic body occurrence overflow")?;
            if depth >= 64 || occurrences > 4096 || self.terms.entry_stamp(term).is_none() {
                return Err("symbolic body has an invalid or excessive term path".into());
            }
            self.sequence_instance_sorts_equal(self.terms.sort(term), self.terms.sort(term))?;
            let mut push = |children: &[TermId]| -> EvalResult<()> {
                let bytes = pending
                    .len()
                    .saturating_add(children.len())
                    .saturating_add(pending.capacity())
                    .saturating_mul(std::mem::size_of::<(TermId, usize)>());
                self.admit_evaluation(children.len(), bytes)?;
                self.charge_sequence_work(children.len())?;
                pending
                    .try_reserve_exact(children.len())
                    .map_err(|_| "symbolic body admission allocation refused")?;
                pending.extend(children.iter().map(|&child| (child, depth + 1)));
                Ok(())
            };
            match self.terms.get(term) {
                TermData::Var(..) => {
                    self.charge_sequence_work(parameters.len())?;
                    if !parameters.contains(&term) {
                        return Err("symbolic body contains an unbound variable identity".into());
                    }
                }
                TermData::Const(constant) => {
                    let valid = match constant {
                        ay_core::term::Constant::Bool(_) => self.terms.sort(term) == &Sort::Bool,
                        ay_core::term::Constant::Int(value) => {
                            self.admit_evaluation(
                                usize::try_from(value.bits())
                                    .map_err(|_| "symbolic integer size overflow")?,
                                0,
                            )?;
                            self.terms.sort(term) == &Sort::Int
                        }
                        ay_core::term::Constant::Rational(value) => {
                            use num_traits::Signed;
                            let bits = value
                                .0
                                .numer()
                                .bits()
                                .checked_add(value.0.denom().bits())
                                .and_then(|bits| usize::try_from(bits).ok())
                                .ok_or("symbolic rational size overflow")?;
                            self.admit_evaluation(bits, 0)?;
                            self.terms.sort(term) == &Sort::Real && value.0.denom().is_positive()
                        }
                        _ => false,
                    };
                    if !valid {
                        return Err("symbolic constant has conflicting or unsupported sort".into());
                    }
                }
                TermData::App(Symbol::Named(name), args) => {
                    if name.len() > 256 || args.len() > 256 {
                        return Err("symbolic body application exceeds bounded shape".into());
                    }
                    self.charge_sequence_work(
                        self.terms
                            .declared_function_lookup_work(name.len())
                            .ok_or("symbolic declaration lookup layout is unsupported")?,
                    )?;
                    self.charge_sequence_work(name.len().saturating_add(args.len()))?;
                    for &child in args {
                        self.terms
                            .entry_stamp(child)
                            .ok_or("symbolic child identity is invalid")?;
                        self.sequence_instance_sorts_equal(
                            self.terms.sort(child),
                            self.terms.sort(child),
                        )?;
                    }
                    if !symbolic_operator_typed(self.terms, term, name, args) {
                        return Err("symbolic native operator signature is malformed".into());
                    }
                    push(args)?;
                }
                TermData::Not(inner) => {
                    self.terms
                        .entry_stamp(*inner)
                        .ok_or("symbolic Not child is invalid")?;
                    if self.terms.sort(term) != &Sort::Bool
                        || self.terms.sort(*inner) != &Sort::Bool
                    {
                        return Err("symbolic Not is not Boolean".into());
                    }
                    push(std::slice::from_ref(inner))?;
                }
                TermData::Ite(c, t, e) => {
                    for &child in [*c, *t, *e].iter() {
                        self.terms
                            .entry_stamp(child)
                            .ok_or("symbolic Ite child is invalid")?;
                    }
                    if self.terms.sort(*c) != &Sort::Bool
                        || self.terms.sort(*t) != self.terms.sort(term)
                        || self.terms.sort(*e) != self.terms.sort(term)
                    {
                        return Err("symbolic Ite has conflicting branch sorts".into());
                    }
                    push(&[*c, *t, *e])?;
                }
                _ => return Err("symbolic body has an unsupported binder or node".into()),
            }
        }
        Ok(())
    }
}

fn symbolic_operator_typed(terms: &TermStore, term: TermId, name: &str, args: &[TermId]) -> bool {
    if terms.is_declared_function(name) {
        // The internal producer expands acyclic UF dependencies first. A raw
        // ModelView supplies no declaration-signature witness for a remaining
        // UF body node, so an unknown signature cannot gain native meaning.
        return false;
    }
    let result = terms.sort(term);
    let same = |sort: &Sort| args.iter().all(|&argument| terms.sort(argument) == sort);
    match name {
        "+" | "-" | "*" => {
            !args.is_empty() && matches!(result, Sort::Int | Sort::Real) && same(result)
        }
        "/" => args.len() == 2 && result == &Sort::Real && same(&Sort::Real),
        "div" | "mod" => args.len() == 2 && result == &Sort::Int && same(&Sort::Int),
        "abs" => args.len() == 1 && matches!(result, Sort::Int | Sort::Real) && same(result),
        "to_int" => args.len() == 1 && result == &Sort::Int && same(&Sort::Real),
        "and" | "or" => result == &Sort::Bool && same(&Sort::Bool),
        "xor" => args.len() >= 2 && result == &Sort::Bool && same(&Sort::Bool),
        "=>" => args.len() >= 2 && result == &Sort::Bool && same(&Sort::Bool),
        "not" => args.len() == 1 && result == &Sort::Bool && same(&Sort::Bool),
        "=" | "distinct" => args.len() >= 2 && result == &Sort::Bool && same(terms.sort(args[0])),
        "<" | "<=" | ">" | ">=" => {
            args.len() == 2
                && result == &Sort::Bool
                && matches!(terms.sort(args[0]), Sort::Int | Sort::Real)
                && same(terms.sort(args[0]))
        }
        "select" => {
            args.len() == 2
                && matches!(terms.sort(args[0]),Sort::Array(array)
            if terms.sort(args[1])==&array.index_sort && result==&array.element_sort)
        }
        "store" => {
            args.len() == 3
                && matches!(terms.sort(args[0]),Sort::Array(array)
            if result==terms.sort(args[0]) && terms.sort(args[1])==&array.index_sort && terms.sort(args[2])==&array.element_sort)
        }
        "const-array" => {
            args.len() == 1
                && matches!(result,Sort::Array(array) if terms.sort(args[0])==&array.element_sort)
        }
        "to_real" => args.len() == 1 && result == &Sort::Real && same(&Sort::Int),
        "is_int" => args.len() == 1 && result == &Sort::Bool && same(&Sort::Real),
        _ => false,
    }
}
