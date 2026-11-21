// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::TermStore;

enum Bindings<'a> {
    Authored {
        names: &'a [String],
        parameters: &'a [TermId],
    },
    Exact {
        parameters: &'a [TermId],
        arguments: &'a [TermId],
    },
    Query,
}

fn is_operator(terms: &TermStore, name: &str) -> bool {
    !terms.is_declared_function(name)
        && matches!(
            name,
            "+" | "-"
                | "*"
                | "/"
                | "div"
                | "mod"
                | "abs"
                | "to_int"
                | "and"
                | "or"
                | "xor"
                | "=>"
                | "not"
                | "="
                | "distinct"
                | "<"
                | "<="
                | ">"
                | ">="
                | "to_real"
                | "is_int"
                | "select"
                | "store"
                | "const-array"
        )
}

pub(super) fn dependencies_ready(
    executor: &Executor,
    root: TermId,
    compiled: &[SymbolicUfDefinition],
    names: &[String],
    owner: &SymbolicAdmission,
) -> Option<bool> {
    admission::source_body(&executor.ctx.terms, root, names, owner)?;
    let mut pending = Vec::new();
    owner.reserve(&mut pending, 1)?;
    pending.push(root);
    while let Some(term) = pending.pop() {
        if !owner.pay(1, 0) {
            return None;
        }
        match executor.ctx.terms.get(term) {
            TermData::App(symbol @ Symbol::Named(name), args) => {
                owner
                    .pay(
                        executor
                            .ctx
                            .terms
                            .declared_function_lookup_work(name.len())?,
                        0,
                    )
                    .then_some(())?;
                if !is_operator(&executor.ctx.terms, name) {
                    owner
                        .pay(compiled.len().checked_mul(name.len().checked_add(256)?)?, 0)
                        .then_some(())?;
                    let Some(definition) = compiled
                        .iter()
                        .find(|definition| definition.binding.symbol() == symbol)
                    else {
                        return Some(false);
                    };
                    if definition.binding.parameter_sorts().len() != args.len()
                        || definition.binding.result_sort() != executor.ctx.terms.sort(term)
                        || args
                            .iter()
                            .zip(definition.binding.parameter_sorts())
                            .any(|(&arg, sort)| executor.ctx.terms.sort(arg) != sort)
                    {
                        return None;
                    }
                }
                owner.reserve(&mut pending, args.len())?;
                pending.extend_from_slice(args);
            }
            TermData::Not(inner) => {
                owner.reserve(&mut pending, 1)?;
                pending.push(*inner);
            }
            TermData::Ite(c, t, e) => {
                owner.reserve(&mut pending, 3)?;
                pending.extend([*c, *t, *e]);
            }
            _ => {}
        }
    }
    Some(true)
}

pub(super) fn compile(
    terms: &mut TermStore,
    root: TermId,
    names: &[String],
    parameters: &[TermId],
    compiled: &[SymbolicUfDefinition],
    owner: &SymbolicAdmission,
) -> Option<TermId> {
    expand(
        terms,
        root,
        &Bindings::Authored { names, parameters },
        compiled,
        &[],
        owner,
        0,
    )
}

pub(super) fn instantiate_query(
    terms: &mut TermStore,
    root: TermId,
    symbolic: &SymbolicUfModel,
    tables: &[UfTable],
    owner: &SymbolicAdmission,
) -> Option<TermId> {
    expand(
        terms,
        root,
        &Bindings::Query,
        symbolic.definitions(),
        tables,
        owner,
        0,
    )
}

fn expand(
    terms: &mut TermStore,
    root: TermId,
    bindings: &Bindings<'_>,
    definitions: &[SymbolicUfDefinition],
    tables: &[UfTable],
    owner: &SymbolicAdmission,
    depth: usize,
) -> Option<TermId> {
    if depth > 64 || !owner.pay(1, 0) {
        return None;
    }
    terms.entry_stamp(root)?;
    match terms.get(root) {
        TermData::Var(name, _) => {
            return match bindings {
                Bindings::Query => Some(root),
                Bindings::Authored { names, parameters } => {
                    owner
                        .pay(names.len().checked_mul(name.len().checked_add(256)?)?, 0)
                        .then_some(())?;
                    let index = names.iter().position(|candidate| candidate == name)?;
                    let argument = *parameters.get(index)?;
                    (terms.sort(root) == terms.sort(argument)).then_some(argument)
                }
                Bindings::Exact {
                    parameters,
                    arguments,
                } => {
                    owner.pay(parameters.len(), 0).then_some(())?;
                    let index = parameters.iter().position(|&parameter| parameter == root)?;
                    let argument = *arguments.get(index)?;
                    (terms.sort(root) == terms.sort(argument)).then_some(argument)
                }
            };
        }
        TermData::Const(_) => return Some(root),
        _ => {}
    }
    enum Node {
        Not(TermId),
        Ite(TermId, TermId, TermId),
        App(Symbol, Vec<TermId>),
    }
    let node = match terms.get(root) {
        TermData::Not(inner) => Node::Not(*inner),
        TermData::Ite(c, t, e) => Node::Ite(*c, *t, *e),
        TermData::App(Symbol::Named(name), args) if args.len() <= MAX_TABLE_ROWS => {
            let name = admission::text(name, owner)?;
            let mut copied = Vec::new();
            owner.reserve(&mut copied, args.len())?;
            copied.extend_from_slice(args);
            Node::App(Symbol::named(name), copied)
        }
        _ => return None,
    };
    match node {
        Node::Not(inner) => {
            let changed = expand(
                terms,
                inner,
                bindings,
                definitions,
                tables,
                owner,
                depth + 1,
            )?;
            if changed == inner {
                return Some(root);
            }
            intern(terms, TermData::Not(changed), &Sort::Bool, owner)
        }
        Node::Ite(c, t, e) => {
            let nc = expand(terms, c, bindings, definitions, tables, owner, depth + 1)?;
            let nt = expand(terms, t, bindings, definitions, tables, owner, depth + 1)?;
            let ne = expand(terms, e, bindings, definitions, tables, owner, depth + 1)?;
            if (nc, nt, ne) == (c, t, e) {
                return Some(root);
            }
            let sort = admission::copy_sort(terms.sort(root), owner)?;
            intern(terms, TermData::Ite(nc, nt, ne), &sort, owner)
        }
        Node::App(symbol, args) => {
            let mut actual = Vec::new();
            owner.reserve(&mut actual, args.len())?;
            for &argument in &args {
                actual.push(expand(
                    terms,
                    argument,
                    bindings,
                    definitions,
                    tables,
                    owner,
                    depth + 1,
                )?);
            }
            owner
                .pay(
                    definitions
                        .len()
                        .checked_add(tables.len())?
                        .checked_mul(symbol.name().len().checked_add(256)?)?,
                    0,
                )
                .then_some(())?;
            if let Some(definition) = definitions
                .iter()
                .find(|definition| definition.binding.symbol() == &symbol)
            {
                if actual.len() != definition.parameters.len()
                    || definition.binding.result_sort() != terms.sort(root)
                    || actual
                        .iter()
                        .zip(definition.binding.parameter_sorts())
                        .any(|(&argument, sort)| terms.sort(argument) != sort)
                {
                    return None;
                }
                return expand(
                    terms,
                    definition.body,
                    &Bindings::Exact {
                        parameters: &definition.parameters,
                        arguments: &actual,
                    },
                    &[],
                    &[],
                    owner,
                    depth + 1,
                );
            }
            if let Some(table) = tables.iter().find(|table| table.symbol == symbol) {
                return table_application(terms, table, &actual, owner);
            }
            if actual == args {
                return Some(root);
            }
            let sort = admission::copy_sort(terms.sort(root), owner)?;
            intern(terms, TermData::App(symbol, actual), &sort, owner)
        }
    }
}

fn intern(
    terms: &mut TermStore,
    node: TermData,
    sort: &Sort,
    owner: &SymbolicAdmission,
) -> Option<TermId> {
    terms
        .try_intern_symbolic_with_progress(&node, sort, &mut |work, bytes| owner.pay(work, bytes))
        .ok()
}

fn table_application(
    terms: &mut TermStore,
    table: &UfTable,
    arguments: &[TermId],
    owner: &SymbolicAdmission,
) -> Option<TermId> {
    if table.arg_sorts.len() != arguments.len() || table.rows.len() > MAX_TABLE_ROWS {
        return None;
    }
    for (&argument, sort) in arguments.iter().zip(&table.arg_sorts) {
        terms.entry_stamp(argument)?;
        admission::sort(terms.sort(argument), owner, 0)?;
        admission::sort(sort, owner, 0)?;
        if terms.sort(argument) != sort {
            return None;
        }
    }
    terms.entry_stamp(table.default)?;
    if terms.sort(table.default) != &table.result_sort {
        return None;
    }
    let mut body = table.default;
    for (keys, value) in table.rows.iter().rev() {
        if !owner.pay(1, 0) || keys.len() != arguments.len() {
            return None;
        }
        terms.entry_stamp(*value)?;
        if terms.sort(*value) != &table.result_sort {
            return None;
        }
        if *value == table.default {
            continue;
        }
        let mut condition = terms.true_term();
        for ((&key, &argument), sort) in keys.iter().zip(arguments).zip(&table.arg_sorts) {
            terms.entry_stamp(key)?;
            admission::sort(terms.sort(key), owner, 0)?;
            if terms.sort(key) != sort {
                return None;
            }
            let equality = if key == argument {
                terms.true_term()
            } else {
                intern(
                    terms,
                    TermData::App(Symbol::named("="), vec![key, argument]),
                    &Sort::Bool,
                    owner,
                )?
            };
            if condition == terms.true_term() {
                condition = equality;
            } else {
                condition = intern(
                    terms,
                    TermData::App(Symbol::named("and"), vec![condition, equality]),
                    &Sort::Bool,
                    owner,
                )?;
            }
        }
        body = intern(
            terms,
            TermData::Ite(condition, *value, body),
            &table.result_sort,
            owner,
        )?;
    }
    Some(body)
}
