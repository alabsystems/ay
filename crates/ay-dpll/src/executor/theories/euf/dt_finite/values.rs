// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Value representation and the value-level schemas (1, 2, 5, 6, 9).
//!
//! CANONICAL FORM (critique F1). Every value is canonical:
//! * `Enum`: a one-hot row whose bits are exactly the content atoms
//!   "value = C"; a well-formed enum value has exactly one bit true.
//! * `List`: `D` cells; cell `i` is `(s_i, rows)` with `s_i` = "more than `i`
//!   cons cells" and one guarded one-hot row per cons field (bit = "cell `i`
//!   is present and its field is C"). An ABSENT cell has `s_i` and every row
//!   bit false, a PRESENT cell has exactly one bit per row.
//! * `Record`: the product of its field values (one constructor, so there is
//!   no inactive-constructor field anywhere).
//!
//! Because cell rows are only ever enum rows (the gate admits no other cell
//! field), two canonical values are equal iff their bit vectors agree on the
//! cells they both describe, and no equality is ever taken bitwise between an
//! inactive and an active encoding.

use std::rc::Rc;

use super::cnf::{Cnf, Lit, FALSE, TRUE};
use super::scan::{FieldSort, Scan, SortShape};

/// One cell of a list value.
pub(super) struct Cell {
    pub(super) s: Lit,
    pub(super) rows: Vec<Vec<Lit>>,
}

/// An encoded value.
#[derive(Clone)]
pub(super) enum Val {
    Bool(Lit),
    Enum(Rc<Vec<Lit>>),
    Record(Rc<Vec<Val>>),
    List(Rc<Vec<Rc<Cell>>>),
}

impl Val {
    pub(super) fn lit(&self) -> Option<Lit> {
        match self {
            Val::Bool(l) => Some(*l),
            _ => None,
        }
    }
}

/// Width of an enum sort.
pub(super) fn enum_width(scan: &Scan, sort: u32) -> usize {
    match &scan.sorts[sort as usize].shape {
        SortShape::Enum { ctors } => ctors.len(),
        _ => 0,
    }
}

/// Cell field enum sorts of a list sort.
pub(super) fn cell_fields(scan: &Scan, sort: u32) -> &[u32] {
    match &scan.sorts[sort as usize].shape {
        SortShape::List { cell_fields, .. } => cell_fields,
        _ => &[],
    }
}

/// Schema 2: a guarded one-hot row (`bit -> s`, `s -> exactly-one`).
pub(super) fn guarded_row(cnf: &mut Cnf, width: usize, s: Lit) -> Vec<Lit> {
    if width == 1 {
        return vec![s];
    }
    let row: Vec<Lit> = (0..width).map(|_| cnf.new_var()).collect();
    for &b in &row {
        cnf.add(&[-b, s]);
    }
    cnf.exactly_one(&row, s);
    row
}

/// A fresh well-formed cell whose presence bit implies `prev` (schema 1).
pub(super) fn fresh_cell(cnf: &mut Cnf, scan: &Scan, sort: u32, prev: Lit) -> Rc<Cell> {
    let s = cnf.new_var();
    cnf.add(&[-s, prev]);
    let rows = cell_fields(scan, sort)
        .iter()
        .map(|&e| guarded_row(cnf, enum_width(scan, e), s))
        .collect();
    Rc::new(Cell { s, rows })
}

/// A fresh well-formed value of `sort` (free constant / shared wrong-constructor term).
pub(super) fn fresh(cnf: &mut Cnf, scan: &Scan, d: usize, sort: FieldSort) -> Val {
    let FieldSort::Dt(id) = sort else {
        return Val::Bool(cnf.new_var());
    };
    match &scan.sorts[id as usize].shape {
        SortShape::Enum { ctors } => {
            if ctors.len() == 1 {
                return Val::Enum(Rc::new(vec![TRUE]));
            }
            let row: Vec<Lit> = (0..ctors.len()).map(|_| cnf.new_var()).collect();
            cnf.exactly_one(&row, TRUE);
            Val::Enum(Rc::new(row))
        }
        SortShape::Record { fields, .. } => {
            let fields = fields.clone();
            Val::Record(Rc::new(
                fields.iter().map(|&f| fresh(cnf, scan, d, f)).collect(),
            ))
        }
        SortShape::List { .. } => {
            let mut cells = Vec::with_capacity(d);
            let mut prev = TRUE;
            for _ in 0..d {
                let c = fresh_cell(cnf, scan, id, prev);
                prev = c.s;
                cells.push(c);
            }
            Val::List(Rc::new(cells))
        }
    }
}

/// The constant enum value `ctor` of an enum of `width` constructors.
pub(super) fn enum_const(width: usize, ctor: usize) -> Val {
    Val::Enum(Rc::new(
        (0..width)
            .map(|c| if c == ctor { TRUE } else { FALSE })
            .collect(),
    ))
}

/// The nil constant: every cell absent (schema 3 for the nullary nil).
pub(super) fn nil_value(scan: &Scan, d: usize, sort: u32) -> Val {
    let rows: Vec<Vec<Lit>> = cell_fields(scan, sort)
        .iter()
        .map(|&e| vec![FALSE; enum_width(scan, e)])
        .collect();
    let cell = Rc::new(Cell { s: FALSE, rows });
    Val::List(Rc::new(vec![cell; d]))
}

/// Schema 3: `cons(e, u)`: cell 0 = (TRUE, fields), cell i+1 = cell i of `u`.
pub(super) fn cons_value(fields: Vec<Vec<Lit>>, tail: &Val, d: usize) -> Option<Val> {
    let Val::List(tail_cells) = tail else {
        return None;
    };
    let mut cells = Vec::with_capacity(d);
    cells.push(Rc::new(Cell {
        s: TRUE,
        rows: fields,
    }));
    cells.extend(tail_cells.iter().take(d.saturating_sub(1)).cloned());
    Some(Val::List(Rc::new(cells)))
}

/// Schema 9: the value of `ite(c, a, b)` (bitwise definitional ite).
/// `None` on a shape mismatch (never emits a clause for it).
pub(super) fn mux(cnf: &mut Cnf, c: Lit, a: &Val, b: &Val) -> Option<Val> {
    if c == TRUE {
        return Some(a.clone());
    }
    if c == FALSE {
        return Some(b.clone());
    }
    Some(match (a, b) {
        (Val::Bool(x), Val::Bool(y)) => Val::Bool(cnf.ite(c, *x, *y)),
        (Val::Enum(x), Val::Enum(y)) if x.len() == y.len() => {
            Val::Enum(Rc::new(mux_row(cnf, c, x, y)))
        }
        (Val::Record(x), Val::Record(y)) if x.len() == y.len() => {
            let mut out = Vec::with_capacity(x.len());
            for (p, q) in x.iter().zip(y.iter()) {
                out.push(mux(cnf, c, p, q)?);
            }
            Val::Record(Rc::new(out))
        }
        (Val::List(x), Val::List(y)) if x.len() == y.len() => Val::List(Rc::new(
            x.iter()
                .zip(y.iter())
                .map(|(p, q)| mux_cell(cnf, c, p, q))
                .collect(),
        )),
        _ => return None,
    })
}

pub(super) fn mux_row(cnf: &mut Cnf, c: Lit, x: &[Lit], y: &[Lit]) -> Vec<Lit> {
    x.iter().zip(y).map(|(&p, &q)| cnf.ite(c, p, q)).collect()
}

pub(super) fn mux_cell(cnf: &mut Cnf, c: Lit, p: &Rc<Cell>, q: &Rc<Cell>) -> Rc<Cell> {
    if Rc::ptr_eq(p, q) {
        return p.clone();
    }
    let s = cnf.ite(c, p.s, q.s);
    let rows = p
        .rows
        .iter()
        .zip(&q.rows)
        .map(|(x, y)| mux_row(cnf, c, x, y))
        .collect();
    Rc::new(Cell { s, rows })
}

/// Schema 6: equality of two well-formed enum rows.
fn eq_row(cnf: &mut Cnf, x: &[Lit], y: &[Lit]) -> Lit {
    if let Some(i) = constant_index(x) {
        return y[i];
    }
    if let Some(i) = constant_index(y) {
        return x[i];
    }
    let pairs: Vec<Lit> = x.iter().zip(y).map(|(&p, &q)| cnf.and(&[p, q])).collect();
    cnf.or(&pairs)
}

/// The index of the TRUE bit of a constant one-hot row.
fn constant_index(row: &[Lit]) -> Option<usize> {
    if row.iter().all(|&l| l == TRUE || l == FALSE) {
        row.iter().position(|&l| l == TRUE)
    } else {
        None
    }
}

/// `ce_i`: cells agree (both absent, or both present with equal fields).
fn eq_cell(cnf: &mut Cnf, x: &Rc<Cell>, y: &Rc<Cell>) -> Lit {
    if Rc::ptr_eq(x, y) || (x.s == FALSE && y.s == FALSE) {
        return TRUE;
    }
    let both_absent = cnf.and(&[-x.s, -y.s]);
    let mut present = vec![x.s, y.s];
    for (p, q) in x.rows.iter().zip(&y.rows) {
        // Rows of present cells are well-formed one-hot rows.
        let pairs: Vec<Lit> = p.iter().zip(q).map(|(&a, &b)| cnf.and(&[a, b])).collect();
        present.push(cnf.or(&pairs));
    }
    let both_present = cnf.and(&present);
    cnf.or(&[both_absent, both_present])
}

/// Schema 5: list equality. `e -> ce_i` for every cell, and
/// `(AND ce_i) & !deep -> e`; a deep/deep agreement leaves `e` free. When
/// either side is statically shallow (its last presence bit is FALSE), the
/// two directions coincide and `e` is exactly `AND ce_i`.
fn eq_list(cnf: &mut Cnf, x: &[Rc<Cell>], y: &[Rc<Cell>]) -> Lit {
    let ces: Vec<Lit> = x.iter().zip(y).map(|(p, q)| eq_cell(cnf, p, q)).collect();
    let (Some(lx), Some(ly)) = (x.last(), y.last()) else {
        return TRUE;
    };
    if lx.s == FALSE || ly.s == FALSE {
        return cnf.and(&ces);
    }
    if ces.contains(&FALSE) {
        return FALSE;
    }
    let e = cnf.new_var();
    let mut back = vec![e, lx.s];
    for &ce in &ces {
        cnf.add(&[-e, ce]);
        back.push(-ce);
    }
    cnf.add(&back);
    e
}

/// The equality literal of two values of one sort (`None` on a shape
/// mismatch, which the encoder turns into a decline).
pub(super) fn eq_val(cnf: &mut Cnf, a: &Val, b: &Val) -> Option<Lit> {
    Some(match (a, b) {
        (Val::Bool(x), Val::Bool(y)) => cnf.iff(*x, *y),
        (Val::Enum(x), Val::Enum(y)) if x.len() == y.len() => {
            if Rc::ptr_eq(x, y) {
                return Some(TRUE);
            }
            eq_row(cnf, x, y)
        }
        (Val::Record(x), Val::Record(y)) if x.len() == y.len() => {
            if Rc::ptr_eq(x, y) {
                return Some(TRUE);
            }
            let mut parts = Vec::with_capacity(x.len());
            for (p, q) in x.iter().zip(y.iter()) {
                parts.push(eq_val(cnf, p, q)?);
            }
            cnf.and(&parts)
        }
        (Val::List(x), Val::List(y)) if x.len() == y.len() => {
            if Rc::ptr_eq(x, y) {
                return Some(TRUE);
            }
            eq_list(cnf, x, y)
        }
        _ => return None,
    })
}

/// `guard -> cell p == cell q`, bitwise.
pub(super) fn assert_cell_equal(cnf: &mut Cnf, guard: Lit, p: &Cell, q: &Cell) {
    equal_bits(cnf, guard, &[p.s], &[q.s]);
    for (x, y) in p.rows.iter().zip(&q.rows) {
        equal_bits(cnf, guard, x, y);
    }
}

fn equal_bits(cnf: &mut Cnf, guard: Lit, x: &[Lit], y: &[Lit]) {
    for (&p, &q) in x.iter().zip(y) {
        if p != q {
            cnf.add(&[-guard, -p, q]);
            cnf.add(&[-guard, p, -q]);
        }
    }
}
