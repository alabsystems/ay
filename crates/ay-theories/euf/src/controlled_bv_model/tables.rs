// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

type Row = (Vec<String>, String);

#[derive(Clone, Copy)]
enum Kind {
    Function,
    Predicate,
}

impl Kind {
    fn is_predicate(self) -> bool {
        matches!(self, Self::Predicate)
    }
}

pub(super) fn build(
    source: &EufSolver<'_>,
    terms: &[TermId],
    model: &mut EufModel,
    value_buckets: usize,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    let name_buckets = owned::reserve_table::<(String, Vec<Row>)>(4, work)?;
    model
        .function_tables
        .try_reserve(4)
        .map_err(|_| work.refuse_exhaustion())?;
    let source_buckets = owned::reserve_table::<(String, Vec<TermId>)>(4, work)?;
    model
        .function_table_terms
        .try_reserve(4)
        .map_err(|_| work.refuse_exhaustion())?;
    // Legacy BTreeMap name order and separate function-then-predicate overwrite.
    for kind in [Kind::Function, Kind::Predicate] {
        for name in ["const-array", "default", "select", "store"] {
            let (rows, origins) = one(source, terms, model, value_buckets, name, kind, work)?;
            if rows.is_empty() {
                drop(rows);
                drop(origins);
                continue;
            }
            let key = owned::text(name, work)?;
            let origin_key = owned::text(name, work)?;
            owned::name_probe(name_buckets, work)?;
            let old_rows = model.function_tables.insert(key, rows);
            owned::name_probe(source_buckets, work)?;
            let old_origins = model.function_table_terms.insert(origin_key, origins);
            // Old rows/strings were prepaid at creation, including disposal.
            drop(old_rows);
            drop(old_origins);
            work.charge(0)?;
        }
    }
    Ok(())
}

fn one(
    source: &EufSolver<'_>,
    terms: &[TermId],
    model: &EufModel,
    buckets: usize,
    name: &str,
    kind: Kind,
    work: &mut WorkBudget<'_>,
) -> Result<(Vec<Row>, Vec<TermId>), QueryError> {
    let mut rows = owned::reserve_vec::<Row>(terms.len(), work)?;
    let mut origins = owned::reserve_vec::<TermId>(terms.len(), work)?;
    for index in 0..terms.len() {
        work.charge(64)?;
        let term = terms[index];
        let TermData::App(Symbol::Named(symbol), args) = source.terms.get(term) else {
            continue;
        };
        if symbol.as_ref() != name
            || matches!(source.terms.sort(term), Sort::Bool) != kind.is_predicate()
        {
            continue;
        }
        let mut values = owned::reserve_vec::<String>(args.len(), work)?;
        for position in 0..args.len() {
            work.charge(32)?;
            values.push(argument(source, model, buckets, args[position], work)?);
        }
        let result = if kind.is_predicate() {
            let assigned = owned::lookup(&source.assigns, term, work)?.copied();
            owned::text(
                if assigned == Some(true) {
                    "true"
                } else {
                    "false"
                },
                work,
            )?
        } else {
            result(model, buckets, term, work)?
        };
        if duplicate(&rows, &values, work)? {
            drop(values);
            drop(result);
            work.charge(0)?;
            continue;
        }
        work.charge(64)?;
        rows.push((values, result));
        origins.push(term);
    }
    Ok((rows, origins))
}

fn argument(
    source: &EufSolver<'_>,
    model: &EufModel,
    buckets: usize,
    term: TermId,
    work: &mut WorkBudget<'_>,
) -> Result<String, QueryError> {
    work.charge(32)?;
    if matches!(source.terms.sort(term), Sort::Bool) {
        if let Some(&value) = owned::lookup(&source.assigns, term, work)? {
            return owned::text(if value { "true" } else { "false" }, work);
        }
        owned::probe(buckets, work)?;
        if let Some(raw) = model.term_values.get(&term) {
            work.charge(2 * raw.len() + 8)?;
            if raw == "true" || raw == "false" {
                return owned::text(raw, work);
            }
        }
        return literal::placeholder(term, work);
    }
    result(model, buckets, term, work)
}

fn result(
    model: &EufModel,
    buckets: usize,
    term: TermId,
    work: &mut WorkBudget<'_>,
) -> Result<String, QueryError> {
    owned::probe(buckets, work)?;
    if let Some(value) = model.term_values.get(&term) {
        owned::text(value, work)
    } else {
        literal::placeholder(term, work)
    }
}

fn duplicate(
    rows: &[Row],
    values: &[String],
    work: &mut WorkBudget<'_>,
) -> Result<bool, QueryError> {
    for index in 0..rows.len() {
        work.charge(64)?;
        let old = &rows[index].0;
        if old.len() != values.len() {
            continue;
        }
        let mut same = true;
        for arg in 0..old.len() {
            work.charge(32)?;
            let visits = owned::checked(
                old[arg]
                    .len()
                    .checked_add(values[arg].len())
                    .and_then(|n| n.checked_add(16)),
                work,
            )?;
            work.charge(visits)?;
            if old[arg] != values[arg] {
                same = false;
                break;
            }
        }
        if same {
            return Ok(true);
        }
    }
    Ok(false)
}

pub(super) fn tracked(
    source: &EufSolver<'_>,
    model: &mut EufModel,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    work.charge(64)?;
    let _ = owned::scan_table::<(TermId, TermId)>(source.func_app_values.allocation_size(), work)?;
    let buckets = owned::reserve_table::<(TermId, TermId)>(source.func_app_values.len(), work)?;
    model
        .func_app_const_terms
        .try_reserve(source.func_app_values.len())
        .map_err(|_| work.refuse_exhaustion())?;
    for (&app, &partner) in &source.func_app_values {
        shape::live(source, app, work)?;
        shape::live(source, partner, work)?;
        work.charge(64)?;
        let TermData::App(Symbol::Named(name), args) = source.terms.get(app) else {
            return Err(work.refuse_exhaustion());
        };
        if !matches!(name.as_ref(), "select" | "default")
            || args.is_empty()
            || !matches!(source.terms.sort(app), Sort::BitVec(_))
        {
            return Err(work.refuse_exhaustion());
        }
        work.charge(32)?;
        if !matches!(
            source.terms.get(partner),
            TermData::Var(..) | TermData::Const(Constant::BitVec { .. })
        ) || source.terms.sort(app) != source.terms.sort(partner)
        {
            return Err(work.refuse_exhaustion());
        }
        owned::probe(buckets, work)?;
        model.func_app_const_terms.insert(app, partner);
    }
    Ok(())
}
