// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::functions::Functions;
use super::records::{registry_bytes, sort_bytes, Registry};
use super::*;
use crate::smt::executor_adapter::sort_to_smtlib;
use crate::{ChcError, ChcSort, ClauseHead, InvariantModel, PredicateId};
use ay_core::quote_symbol;
use std::collections::{BTreeMap, BTreeSet};

mod binders;
mod types;
use binders::variables;
use types::expression_sort;
#[cfg(test)]
mod resource_tests;

pub(super) const MAX_NODES: usize = 65_536;
const MAX_DEPTH: usize = 64;
pub(super) const MAX_BYTES: usize = 16 * 1024 * 1024;
pub(super) const MAX_DECLARATIONS: usize = 1_024;
const MAX_CLAUSES: usize = 2_048;
const MAX_PREMISES: usize = 4_096;

fn invalid(message: &str) -> ChcError {
    ChcError::Verification(format!("quantified source: {message}"))
}

#[derive(Default)]
struct Budget {
    nodes: usize,
    bytes: usize,
}

impl Budget {
    fn charge(&mut self, nodes: usize, bytes: usize) -> ChcResult<()> {
        self.nodes = self
            .nodes
            .checked_add(nodes)
            .ok_or_else(|| invalid("work limit"))?;
        self.bytes = self
            .bytes
            .checked_add(bytes)
            .ok_or_else(|| invalid("output limit"))?;
        if self.nodes > MAX_NODES || self.bytes > MAX_BYTES {
            return Err(invalid("source work/output limit"));
        }
        Ok(())
    }

    fn name(&mut self, name: &str) -> ChcResult<()> {
        if name.is_empty()
            || name.len() > 16_384
            || theory_symbol(name)
            || name
                .bytes()
                .any(|b| b.is_ascii_control() || b == b'|' || b == b'\\')
        {
            return Err(invalid("invalid or oversized symbol"));
        }
        self.charge(1, 256 + name.len() * 2)
    }

    fn sort(&mut self, sort: &ChcSort, registry: &Registry, depth: usize) -> ChcResult<()> {
        if !super::records::small_copy_sort(sort) {
            // Embedded records under arrays are cloned by enclosing sort copies
            // too; charge their complete metadata before recursive consumers.
            // Wide scalar/key payloads have explicit limb-sized allowances;
            // preserve the existing allowance only for the narrow fragment.
            let bytes = sort_bytes(sort)
                .and_then(|n| n.checked_mul(depth + 1))
                .ok_or_else(|| invalid("sort metadata/copy limit"))?;
            self.charge(1, bytes)?;
        }
        registry.validate_sort(sort)
    }

    fn expression(
        &mut self,
        root: &ChcExpr,
        registry: &Registry,
        functions: &Functions,
    ) -> ChcResult<()> {
        let mut pending = vec![(root, 0usize)];
        while let Some((expr, depth)) = pending.pop() {
            if depth > MAX_DEPTH {
                return Err(invalid("expression depth limit"));
            }
            self.charge(1, 256)?;
            match expr {
                ChcExpr::Bool(_) => {}
                ChcExpr::BitVec(value, width)
                    if (1..=crate::MAX_BITVECTOR_WIDTH).contains(width)
                        && (*width >= 128 || *value < (1u128 << width)) =>
                {
                    self.sort(&ChcSort::BitVec(*width), registry, depth)?;
                }
                ChcExpr::Var(var) => {
                    self.sort(&var.sort, registry, depth)?;
                    self.name(&var.name)?;
                    if registry.contains_term_symbol(&var.name) || functions.contains(&var.name) {
                        return Err(invalid("variable shadows declared operation"));
                    }
                }
                ChcExpr::FuncApp(name, sort, args) => {
                    self.name(name)?;
                    self.sort(sort, registry, depth)?;
                    if !registry.contains_term_symbol(name) && !functions.contains(name) {
                        return Err(invalid("undeclared operation"));
                    }
                    self.charge(args.len(), 0)?;
                    pending.extend(args.iter().rev().map(|a| (a.as_ref(), depth + 1)));
                }
                ChcExpr::Op(_, args) => {
                    self.charge(args.len(), 0)?;
                    pending.extend(args.iter().rev().map(|a| (a.as_ref(), depth + 1)));
                }
                ChcExpr::ConstArray(key, value) => {
                    if !matches!(key, ChcSort::BitVec(1..=crate::MAX_BITVECTOR_WIDTH)) {
                        return Err(invalid("constant array requires a bounded bitvector key"));
                    }
                    self.sort(key, registry, depth)?;
                    pending.push((value, depth + 1));
                }
                _ => return Err(invalid("unsupported expression family")),
            }
        }
        Ok(())
    }
}

// Quoting changes lexical spelling, not SMT symbol identity. Do not allow a
// source declaration/binder to shadow the operators used by our serialization.
pub(super) fn theory_symbol(name: &str) -> bool {
    const SYMBOLS: &[&str] = &[
        "true",
        "false",
        "Bool",
        "BitVec",
        "Array",
        "Int",
        "Real",
        "not",
        "and",
        "or",
        "xor",
        "=>",
        "=",
        "distinct",
        "ite",
        "select",
        "store",
        "const",
        "+",
        "-",
        "*",
        "/",
        "div",
        "mod",
        "<",
        "<=",
        ">",
        ">=",
        "bvadd",
        "bvsub",
        "bvmul",
        "bvudiv",
        "bvurem",
        "bvsdiv",
        "bvsrem",
        "bvsmod",
        "bvand",
        "bvor",
        "bvxor",
        "bvnand",
        "bvnor",
        "bvxnor",
        "bvnot",
        "bvneg",
        "bvshl",
        "bvlshr",
        "bvashr",
        "bvult",
        "bvule",
        "bvugt",
        "bvuge",
        "bvslt",
        "bvsle",
        "bvsgt",
        "bvsge",
        "bvcomp",
        "concat",
        "extract",
        "zero_extend",
        "sign_extend",
        "rotate_left",
        "rotate_right",
        "repeat",
        "bv2nat",
        "bv2int",
        "int2bv",
        // SMT-LIB 2.7 names of the same conversions (AY-SMT-10).
        "ubv_to_int",
        "sbv_to_int",
        "int_to_bv",
    ];
    SYMBOLS.contains(&name)
}

fn bv_sort(sort: &ChcSort) -> ChcResult<()> {
    match sort {
        ChcSort::BitVec(width) if (1..=64).contains(width) => Ok(()),
        _ => Err(invalid("expected BV width 1..64")),
    }
}

type Variables<'a> = BTreeMap<&'a str, &'a ChcSort>;

fn clause_expressions(clause: &HornClause) -> impl Iterator<Item = &ChcExpr> {
    clause
        .body
        .predicates
        .iter()
        .flat_map(|(_, args)| args.iter())
        .chain(clause.body.constraint.iter())
        .chain(
            match &clause.head {
                ClauseHead::Predicate(_, args) => args.as_slice(),
                _ => &[],
            }
            .iter(),
        )
}

fn application(
    problem: &ChcProblem,
    registry: &Registry,
    functions: &Functions,
    id: PredicateId,
    args: &[ChcExpr],
    budget: &mut Budget,
) -> ChcResult<String> {
    let pred = problem
        .get_predicate(id)
        .ok_or_else(|| invalid("unknown predicate ID"))?;
    if pred.arg_sorts.len() != args.len() {
        return Err(invalid("predicate arity mismatch"));
    }
    for (arg, expected) in args.iter().zip(&pred.arg_sorts) {
        if expression_sort(arg, registry, functions, budget)? != *expected {
            return Err(invalid("predicate argument sort mismatch"));
        }
    }
    let name = quote_symbol(&pred.name);
    if args.is_empty() {
        return Ok(name);
    }
    let args = args
        .iter()
        .map(InvariantModel::expr_to_smtlib)
        .collect::<Vec<_>>()
        .join(" ");
    Ok(format!("({name} {args})"))
}

fn render_clause(
    problem: &ChcProblem,
    registry: &Registry,
    functions: &Functions,
    item: &QuantifiedHornClause,
    budget: &mut Budget,
) -> ChcResult<String> {
    let mut vars = Variables::new();
    for expr in clause_expressions(&item.clause) {
        variables(expr, None, &mut vars)?;
    }
    for premise in &item.premises {
        variables(&premise.matrix, Some(premise), &mut vars)?;
    }
    if vars.keys().any(|name| {
        problem.lookup_predicate(name).is_some()
            || registry.contains_term_symbol(name)
            || functions.contains(name)
    }) {
        return Err(invalid("free variable shadows predicate declaration"));
    }
    let mut parts = Vec::new();
    for (id, args) in &item.clause.body.predicates {
        parts.push(application(
            problem, registry, functions, *id, args, budget,
        )?);
    }
    if let Some(constraint) = &item.clause.body.constraint {
        if expression_sort(constraint, registry, functions, budget)? != ChcSort::Bool {
            return Err(invalid("non-Boolean clause body"));
        }
        parts.push(InvariantModel::expr_to_smtlib(constraint));
    }
    for premise in &item.premises {
        if expression_sort(&premise.matrix, registry, functions, budget)? != ChcSort::Bool {
            return Err(invalid("non-Boolean matrix"));
        }
        parts.push(format!(
            "(forall ({}) {})",
            binders::render(premise),
            InvariantModel::expr_to_smtlib(&premise.matrix)
        ));
    }
    let body = match parts.len() {
        0 => "true".into(),
        1 => parts.remove(0),
        _ => format!("(and {})", parts.join(" ")),
    };
    let head = match &item.clause.head {
        ClauseHead::False => "false".into(),
        ClauseHead::Predicate(id, args) => {
            application(problem, registry, functions, *id, args, budget)?
        }
    };
    let formula = format!("(=> {body} {head})");
    if vars.is_empty() {
        return Ok(format!("(assert {formula})\n"));
    }
    let bindings = vars
        .into_iter()
        .map(|(name, sort)| format!("({} {})", quote_symbol(name), sort_to_smtlib(sort)))
        .collect::<Vec<_>>()
        .join(" ");
    Ok(format!("(assert (forall ({bindings}) {formula}))\n"))
}

fn preflight(
    declarations: &ChcProblem,
    registry: &Registry,
    functions: &Functions,
    clauses: &[QuantifiedHornClause],
) -> ChcResult<Budget> {
    if !declarations.action_names().is_empty()
        || declarations
            .predicates()
            .len()
            .saturating_add(functions.declarations().len())
            > MAX_DECLARATIONS
        || clauses.len() > MAX_CLAUSES
    {
        return Err(invalid("unsupported or oversized declarations/clauses"));
    }
    let mut budget = Budget::default();
    budget.charge(functions.work(), functions.copy_bytes())?;
    budget.charge(
        0,
        registry_bytes(declarations).ok_or_else(|| invalid("record declaration limit"))?,
    )?;
    let mut names = BTreeSet::new();
    for (index, pred) in declarations.predicates().iter().enumerate() {
        budget.name(&pred.name)?;
        let sort_bytes = pred
            .arg_sorts
            .len()
            .checked_mul(128)
            .ok_or_else(|| invalid("declaration limit"))?;
        budget.charge(pred.arg_sorts.len(), sort_bytes)?;
        if pred.id.index() != index
            || !names.insert(pred.name.as_str())
            || registry.contains_term_symbol(&pred.name)
            || functions.contains(&pred.name)
        {
            return Err(invalid("duplicate or inconsistent predicate declaration"));
        }
        for sort in &pred.arg_sorts {
            budget.sort(sort, registry, 0)?;
        }
    }
    let mut premise_count = 0usize;
    for item in clauses {
        budget.charge(1, 256)?;
        if item.clause.action_id.is_some() || item.clause.source_query_ordinal.is_some() {
            return Err(invalid("expected raw unregistered clause"));
        }
        premise_count = premise_count
            .checked_add(item.premises.len())
            .ok_or_else(|| invalid("premise limit"))?;
        if premise_count > MAX_PREMISES {
            return Err(invalid("premise limit"));
        }
        for (id, args) in item
            .clause
            .body
            .predicates
            .iter()
            .map(|(id, args)| (id, args))
            .chain(match &item.clause.head {
                ClauseHead::Predicate(id, args) => Some((id, args)),
                _ => None,
            })
        {
            let pred = declarations
                .get_predicate(*id)
                .ok_or_else(|| invalid("unknown predicate ID"))?;
            budget.name(&pred.name)?;
            budget.charge(args.len(), 0)?;
        }
        for expr in clause_expressions(&item.clause) {
            budget.expression(expr, registry, functions)?;
        }
        for premise in &item.premises {
            binders::preflight(premise, registry, functions, &mut budget)?;
            budget.expression(&premise.matrix, registry, functions)?;
        }
    }
    if !clauses.iter().any(|c| c.clause.is_query()) {
        return Err(ChcError::NoQuery);
    }
    Ok(budget)
}

pub(super) fn construct(
    declarations: ChcProblem,
    functions: Vec<QuantifiedChcFunction>,
    clauses: Vec<QuantifiedHornClause>,
) -> ChcResult<QuantifiedChcProblem> {
    // Also checks otherwise invisible stale query-source/ordinal state before
    // traversing or formatting any input. This moves, rather than clones, it.
    let declarations = declarations.with_raw_source_clauses(Vec::new())?;
    let registry = Registry::new(&declarations)?;
    let functions = Functions::new(functions, &declarations, &registry)?;
    let mut budget = preflight(&declarations, &registry, &functions, &clauses)?;
    let mut smtlib = format!(
        "; ay.quantified-chc-source/v1\n; fixedpoint={}\n(set-logic HORN)\n",
        declarations.is_fixedpoint_format()
    );
    smtlib.push_str(&registry.declarations_smtlib()?);
    smtlib.push_str(&functions.declarations_smtlib()?);
    for pred in declarations.predicates() {
        let sorts = pred
            .arg_sorts
            .iter()
            .map(sort_to_smtlib)
            .collect::<Vec<_>>()
            .join(" ");
        smtlib.push_str(&format!(
            "(declare-fun {} ({sorts}) Bool)\n",
            quote_symbol(&pred.name)
        ));
    }
    for clause in &clauses {
        smtlib.push_str(&render_clause(
            &declarations,
            &registry,
            &functions,
            clause,
            &mut budget,
        )?);
    }
    smtlib.push_str("(check-sat)\n");
    if smtlib.len() > MAX_BYTES {
        return Err(invalid("source output limit"));
    }
    let (raw, premises) = clauses.into_iter().map(|c| (c.clause, c.premises)).unzip();
    let source = declarations.with_raw_source_clauses(raw)?;
    Ok(QuantifiedChcProblem {
        source,
        premises,
        smtlib,
        functions,
        datatype_declarations: registry.into_record_sorts(),
    })
}
