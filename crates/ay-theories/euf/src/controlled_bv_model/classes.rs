// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[derive(Clone, Copy)]
pub(super) struct Class {
    width: u32,
    rep: u32,
    literal: Option<u128>,
    value: Option<u128>,
}

pub(super) fn prepare(
    source: &EufSolver<'_>,
    terms: &[TermId],
    work: &mut WorkBudget<'_>,
) -> Result<Vec<Class>, QueryError> {
    let mut rows = owned::reserve_vec::<Class>(terms.len(), work)?;
    for index in 0..terms.len() {
        work.charge(32)?;
        let term = terms[index];
        if let Sort::BitVec(bits) = source.terms.sort(term) {
            let rep = shape::representative(source, term, work)?;
            let position = insert(&mut rows, bits.width, rep, work)?;
            work.charge(32)?;
            if rows[position].literal.is_none() {
                if let TermData::Const(Constant::BitVec { value, width }) = source.terms.get(term) {
                    let literal = literal::magnitude(value, *width, work)?;
                    work.charge(32)?;
                    rows[position].literal = Some(literal);
                }
            }
        }
    }
    for index in 0..rows.len() {
        work.charge(64)?;
        if rows[index].literal.is_none() {
            rows[index].literal = class_literal(source, rows[index].rep, rows[index].width, work)?;
        }
        work.charge(32)?;
        rows[index].value = rows[index].literal;
    }
    complete(source, &mut rows, work)?;
    Ok(rows)
}

fn insert(
    rows: &mut Vec<Class>,
    width: u32,
    rep: u32,
    work: &mut WorkBudget<'_>,
) -> Result<usize, QueryError> {
    let mut position = rows.len();
    for index in 0..rows.len() {
        work.charge(64)?;
        let old = (rows[index].width, rows[index].rep);
        if old == (width, rep) {
            return Ok(index);
        }
        if old > (width, rep) {
            position = index;
            break;
        }
    }
    if rows.len() == rows.capacity() {
        return Err(work.refuse_exhaustion());
    }
    work.admit(64, 2 * std::mem::size_of::<Class>())?;
    rows.push(Class {
        width,
        rep,
        literal: None,
        value: None,
    });
    // Stable insertion order matches legacy BTreeMap (width, representative).
    // Every shift is separately offered: reserve pricing is NOT an O(n^2) move fee.
    let mut index = rows.len() - 1;
    while index > position {
        work.admit(64, 2 * std::mem::size_of::<Class>())?;
        rows[index] = rows[index - 1];
        index -= 1;
    }
    work.admit(64, 2 * std::mem::size_of::<Class>())?;
    rows[position] = Class {
        width,
        rep,
        literal: None,
        value: None,
    };
    Ok(position)
}

fn class_literal(
    source: &EufSolver<'_>,
    rep: u32,
    width: u32,
    work: &mut WorkBudget<'_>,
) -> Result<Option<u128>, QueryError> {
    let mut current = rep;
    for _ in 0..source.enodes.len() {
        work.charge(64)?;
        let Some(node) = source.enodes.get(current as usize) else {
            return Err(work.refuse_exhaustion());
        };
        let next = node.next;
        shape::live(source, TermId(current), work)?;
        work.charge(32)?;
        if let TermData::Const(Constant::BitVec {
            value,
            width: actual,
        }) = source.terms.get(TermId(current))
        {
            if *actual == width {
                return literal::magnitude(value, width, work).map(Some);
            }
        }
        current = next;
        if current == rep {
            return Ok(None);
        }
    }
    Err(work.refuse_exhaustion())
}

pub(super) fn value(
    rows: &[Class],
    width: u32,
    rep: u32,
    work: &mut WorkBudget<'_>,
) -> Result<Option<u128>, QueryError> {
    for index in 0..rows.len() {
        work.charge(64)?;
        if (rows[index].width, rows[index].rep) == (width, rep) {
            return Ok(rows[index].value);
        }
    }
    Err(work.refuse_exhaustion())
}

fn used(
    rows: &[Class],
    width: u32,
    candidate: u128,
    work: &mut WorkBudget<'_>,
) -> Result<bool, QueryError> {
    for index in 0..rows.len() {
        work.charge(64)?;
        if rows[index].width == width && rows[index].value == Some(candidate) {
            return Ok(true);
        }
    }
    Ok(false)
}

fn complete(
    source: &EufSolver<'_>,
    rows: &mut [Class],
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    let limit = owned::checked(rows.len().checked_add(1), work)?;
    for index in 0..rows.len() {
        work.charge(64)?;
        if rows[index].value.is_some() {
            continue;
        }
        let row = rows[index];
        let mut candidate = 0u128;
        let mut exhausted = false;
        for _ in 0..limit {
            work.charge(64)?;
            if row.width < 128 && candidate == (1u128 << row.width) {
                exhausted = true;
                break;
            }
            if !used(rows, row.width, candidate, work)? {
                break;
            }
            candidate = candidate
                .checked_add(1)
                .ok_or_else(|| work.refuse_exhaustion())?;
        }
        let selected = if exhausted {
            reuse(source, rows, row, limit, work)?
        } else {
            Some(candidate)
        };
        work.charge(64)?;
        rows[index].value = selected;
    }
    Ok(())
}

fn reuse(
    source: &EufSolver<'_>,
    rows: &[Class],
    row: Class,
    limit: usize,
    work: &mut WorkBudget<'_>,
) -> Result<Option<u128>, QueryError> {
    let mut candidate = 0u128;
    for _ in 0..limit {
        work.charge(64)?;
        if row.width < 128 && candidate == (1u128 << row.width) {
            return Ok(None);
        }
        let mut blocked = false;
        for index in 0..rows.len() {
            work.charge(64)?;
            if rows[index].width == row.width
                && rows[index].value == Some(candidate)
                && disequal(source, row.rep, rows[index].rep, row.width, work)?
            {
                blocked = true;
                break;
            }
        }
        if !blocked {
            return Ok(Some(candidate));
        }
        candidate = candidate
            .checked_add(1)
            .ok_or_else(|| work.refuse_exhaustion())?;
    }
    Err(work.refuse_exhaustion())
}

fn pair(
    source: &EufSolver<'_>,
    a: TermId,
    b: TermId,
    left: u32,
    right: u32,
    width: u32,
    work: &mut WorkBudget<'_>,
) -> Result<bool, QueryError> {
    shape::live(source, a, work)?;
    shape::live(source, b, work)?;
    work.charge(32)?;
    let (Sort::BitVec(first), Sort::BitVec(second)) = (source.terms.sort(a), source.terms.sort(b))
    else {
        return Ok(false);
    };
    if first.width != width || second.width != width {
        return Ok(false);
    }
    let a = shape::representative(source, a, work)?;
    let b = shape::representative(source, b, work)?;
    Ok((a == left && b == right) || (a == right && b == left))
}

fn disequal(
    source: &EufSolver<'_>,
    left: u32,
    right: u32,
    width: u32,
    work: &mut WorkBudget<'_>,
) -> Result<bool, QueryError> {
    work.charge(64)?;
    let _ = owned::scan_table::<(TermId, bool)>(source.assigns.allocation_size(), work)?;
    for (&term, &assigned) in &source.assigns {
        shape::live(source, term, work)?;
        work.charge(64)?;
        let TermData::App(Symbol::Named(name), args) = source.terms.get(term) else {
            continue;
        };
        if !assigned && name.as_ref() == "=" && args.len() == 2 {
            if pair(source, args[0], args[1], left, right, width, work)? {
                return Ok(true);
            }
        } else if assigned && name.as_ref() == "distinct" {
            for i in 0..args.len() {
                for j in (i + 1)..args.len() {
                    work.charge(32)?;
                    if pair(source, args[i], args[j], left, right, width, work)? {
                        return Ok(true);
                    }
                }
            }
        }
    }
    Ok(false)
}
