// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::ChcOp;

fn require_boolean(term: &Term) -> ChcResult<()> {
    if matches!(term, Term::Value(_, sort) if *sort != ChcSort::Bool) {
        return Err(invalid("expected Boolean formula"));
    }
    Ok(())
}

impl Parser<'_> {
    pub(super) fn term(&mut self, expr: &SExpr, depth: usize) -> ChcResult<Arc<Term>> {
        self.budget.enter(depth)?;
        if let Some(value) = value::literal(expr, &mut self.budget)? {
            let sort = value.sort();
            return Ok(Arc::new(Term::Value(value, sort)));
        }
        if let SExpr::Symbol(name) = expr {
            if let Some(value) = self.bindings.get(name) {
                return Ok(Arc::clone(value));
            }
            if self.declarations.lookup_predicate(name).is_some() {
                return self.relation(name, &[], depth);
            }
            let (value, sort) = self.source_application(expr, Vec::new(), &[])?;
            return Ok(Arc::new(Term::Value(value, sort)));
        }
        let items = list(expr)?;
        let Some((head, args)) = items.split_first() else {
            return Err(invalid("empty term application"));
        };
        self.budget
            .charge(args.len(), args.len().saturating_mul(128))?;
        match (head.as_symbol(), args) {
            (Some("let"), [bindings, body]) => self.let_term(bindings, body, depth + 1),
            (Some("forall"), [binders, body]) => self.forall(binders, body, depth + 1),
            (Some("and"), args) if args.len() >= 2 => {
                let children = args
                    .iter()
                    .map(|a| self.term(a, depth + 1))
                    .collect::<ChcResult<Vec<_>>>()?;
                for child in &children {
                    require_boolean(child)?;
                }
                Ok(Arc::new(Term::And(children)))
            }
            (Some("=>"), [body, head]) => {
                let body = self.term(body, depth + 1)?;
                let head = self.term(head, depth + 1)?;
                require_boolean(&body)?;
                require_boolean(&head)?;
                Ok(Arc::new(Term::Implies(body, head)))
            }
            (Some(name), _) if self.bindings.contains_key(name) => {
                Err(invalid("a lexical variable or let alias is not a function"))
            }
            (Some(name), _) if self.declarations.lookup_predicate(name).is_some() => {
                self.relation(name, args, depth + 1)
            }
            _ => {
                let (values, sorts) = self.arguments(args, depth + 1)?;
                let (value, sort) = self.source_application(head, values, &sorts)?;
                Ok(Arc::new(Term::Value(value, sort)))
            }
        }
    }

    fn arguments(
        &mut self,
        args: &[SExpr],
        depth: usize,
    ) -> ChcResult<(Vec<Arc<ChcExpr>>, Vec<ChcSort>)> {
        let mut values = Vec::new();
        let mut sorts = Vec::new();
        self.budget
            .charge(args.len(), args.len().saturating_mul(128))?;
        for arg in args {
            let parsed = self.term(arg, depth)?;
            let (value, sort) = self.value(&parsed, 0)?;
            values.push(value);
            sorts.push(sort);
        }
        Ok((values, sorts))
    }

    fn relation(&mut self, name: &str, args: &[SExpr], depth: usize) -> ChcResult<Arc<Term>> {
        let predicate = self
            .declarations
            .lookup_predicate(name)
            .ok_or_else(|| invalid("undeclared source symbol"))?;
        let (values, sorts) = self.arguments(args, depth)?;
        let declared = self
            .declarations
            .get_predicate(predicate)
            .ok_or_else(|| invalid("predicate registry mismatch"))?;
        if declared.arg_sorts != sorts {
            return Err(invalid("predicate argument arity or sort mismatch"));
        }
        Ok(Arc::new(Term::Predicate(predicate, values)))
    }

    fn let_term(&mut self, bindings: &SExpr, body: &SExpr, depth: usize) -> ChcResult<Arc<Term>> {
        let bindings = list(bindings)?;
        if bindings.is_empty() {
            return Err(invalid("empty let binding list"));
        }
        self.budget
            .charge(bindings.len(), bindings.len().saturating_mul(128))?;
        let mut values = Vec::new();
        let mut names = BTreeSet::new();
        for binding in bindings {
            let [name, rhs] = list(binding)? else {
                return Err(invalid("invalid let binding"));
            };
            let name = symbol(name)?;
            self.budget.name(name)?;
            if self.functions.contains(name) {
                return Err(invalid("let binder shadows a declared function"));
            }
            if !names.insert(name) {
                return Err(invalid("duplicate let binder"));
            }
            // All RHSs are parsed in the incoming scope, including unused RHSs.
            // Values retain resolved variables and quantified binders, not a
            // textual macro that could capture names at the later use site.
            values.push((name.to_owned(), self.term(rhs, depth)?));
        }
        self.scoped(values, body, depth)
    }

    fn forall(&mut self, binders: &SExpr, body: &SExpr, depth: usize) -> ChcResult<Arc<Term>> {
        let binders = list(binders)?;
        if binders.is_empty() {
            return Err(invalid("empty forall binder list"));
        }
        self.budget
            .charge(binders.len(), binders.len().saturating_mul(256))?;
        let mut vars = Vec::new();
        let mut values = Vec::new();
        let mut names = BTreeSet::new();
        for binder in binders {
            let [name, sort] = list(binder)? else {
                return Err(invalid("invalid forall binder"));
            };
            let name = symbol(name)?;
            self.budget.name(name)?;
            if self.functions.contains(name) {
                return Err(invalid("forall binder shadows a declared function"));
            }
            if !names.insert(name) {
                return Err(invalid("duplicate forall binder"));
            }
            let sort = self.source_sort(sort)?;
            self.budget.sort_copy(&sort)?;
            self.budget.sort_copy(&sort)?;
            let var = ChcVar::new(self.fresh_name()?, sort.clone());
            values.push((
                name.to_owned(),
                Arc::new(Term::Value(Arc::new(ChcExpr::var(var.clone())), sort)),
            ));
            vars.push(var);
        }
        let body = self.scoped(values, body, depth)?;
        require_boolean(&body)?;
        Ok(Arc::new(Term::Forall(vars, body)))
    }

    fn fresh_name(&mut self) -> ChcResult<String> {
        loop {
            self.budget.charge(1, 64)?;
            let name = format!("ay!source!{}", self.fresh);
            self.fresh = self
                .fresh
                .checked_add(1)
                .ok_or_else(|| invalid("fresh-name limit"))?;
            if !self.reserved.contains(name.as_str()) {
                return Ok(name);
            }
        }
    }

    fn scoped(
        &mut self,
        values: Vec<(String, Arc<Term>)>,
        body: &SExpr,
        depth: usize,
    ) -> ChcResult<Arc<Term>> {
        let mut previous = Vec::new();
        for (name, value) in values {
            let old = self.bindings.insert(name.clone(), value);
            previous.push((name, old));
        }
        let result = self.term(body, depth);
        for (name, old) in previous.into_iter().rev() {
            if let Some(old) = old {
                self.bindings.insert(name, old);
            } else {
                self.bindings.remove(&name);
            }
        }
        result
    }

    pub(super) fn value(
        &mut self,
        term: &Arc<Term>,
        depth: usize,
    ) -> ChcResult<(Arc<ChcExpr>, ChcSort)> {
        self.budget.enter(depth)?;
        if let Term::Value(expr, sort) = term.as_ref() {
            self.budget.sort_copy(sort)?;
            return Ok((Arc::clone(expr), sort.clone()));
        }
        let id = Arc::as_ptr(term);
        if let Some((_, expr, sort)) = self.qf.get(&id) {
            return Ok((Arc::clone(expr), sort.clone()));
        }
        let (op, children): (ChcOp, &[Arc<Term>]) = match term.as_ref() {
            Term::And(children) => (ChcOp::And, children),
            Term::Implies(left, right) => {
                let (left, left_sort) = self.value(left, depth + 1)?;
                let (right, right_sort) = self.value(right, depth + 1)?;
                if left_sort != ChcSort::Bool || right_sort != ChcSort::Bool {
                    return Err(invalid("non-Boolean implication"));
                }
                let expr = Arc::new(ChcExpr::Op(ChcOp::Implies, vec![left, right]));
                self.qf
                    .insert(id, (Arc::clone(term), Arc::clone(&expr), ChcSort::Bool));
                return Ok((expr, ChcSort::Bool));
            }
            _ => return Err(invalid("predicate or quantifier in a theory expression")),
        };
        self.budget
            .charge(children.len(), children.len().saturating_mul(64))?;
        let mut values = Vec::new();
        for child in children {
            let (value, sort) = self.value(child, depth + 1)?;
            if sort != ChcSort::Bool {
                return Err(invalid("non-Boolean conjunction"));
            }
            values.push(value);
        }
        let value = Arc::new(ChcExpr::Op(op, values));
        self.qf
            .insert(id, (Arc::clone(term), Arc::clone(&value), ChcSort::Bool));
        Ok((value, ChcSort::Bool))
    }
}
