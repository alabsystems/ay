// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Term-level encoding: one value per admitted term, children first
//! (schemas 3, 4, 7, 8 and the Lemma 4 forms; value schemas in `values`).

use std::rc::Rc;

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::TermId;

use super::cnf::{Cnf, Lit, FALSE, TRUE};
use super::scan::{FieldSort, Node, Scan, SelKind, SortShape};
use super::values::{
    assert_cell_equal, cell_fields, cons_value, enum_const, eq_val, fresh, fresh_cell, mux,
    mux_cell, mux_row, nil_value, Cell, Val,
};

/// The encoder state for one cell count `d`.
pub(super) struct Encoder<'a> {
    pub(super) scan: &'a Scan,
    pub(super) d: usize,
    pub(super) cnf: Cnf,
    alias: &'a HashMap<TermId, TermId>,
    guarded: &'a HashSet<TermId>,
    /// Value of every admitted term.
    pub(super) vals: HashMap<TermId, Val>,
    /// Value of every alias representative (declared constants).
    consts: HashMap<TermId, Val>,
    /// The shared `rest(nil)` value per list sort.
    pub(super) shared_rest: HashMap<u32, Val>,
    /// The shared `field_j(nil)` value per (list sort, cell field).
    pub(super) shared_field: HashMap<(u32, usize), Val>,
    nils: HashMap<u32, Val>,
    /// Selector values by (argument value identity, sort, field, guarded):
    /// a selector is a function, so two applications to the SAME encoded
    /// value (an alias class, a constant-condition mux) share one value, and
    /// their equality is then `TRUE` by identity (schema 4). Without it two
    /// deep `rest` applications to one value got different beyond-window
    /// cells and their equality stayed free (E13 audit s02).
    sel_memo: HashMap<(usize, u32, Option<usize>, bool), Val>,
    /// Every recursive-selector value, by identity: `(s_0 of its argument,
    /// list sort, guarded)`. When neither argument has a cons cell both
    /// arguments are nil, so two such values of one kind are equal
    /// (functionality, schema 4) even when the window cannot show it — a
    /// deep `rest(nil)` leaves the plain cell equality free (schema 5).
    rest_of: HashMap<usize, (Lit, u32, bool)>,
}

impl<'a> Encoder<'a> {
    pub(super) fn new(
        scan: &'a Scan,
        d: usize,
        max_clauses: usize,
        alias: &'a HashMap<TermId, TermId>,
        guarded: &'a HashSet<TermId>,
    ) -> Self {
        Self {
            scan,
            d,
            cnf: Cnf::new(max_clauses),
            alias,
            guarded,
            vals: HashMap::default(),
            consts: HashMap::default(),
            shared_rest: HashMap::default(),
            shared_field: HashMap::default(),
            nils: HashMap::default(),
            sel_memo: HashMap::default(),
            rest_of: HashMap::default(),
        }
    }

    /// Encode every term and assert every root. `None` declines (shape
    /// mismatch or clause budget exceeded).
    pub(super) fn encode(&mut self) -> Option<()> {
        for (i, &t) in self.scan.order.iter().enumerate() {
            // Values (D cells per list term) allocate outside the clause
            // store, so the footprint is polled per term batch as well.
            if i % 256 == 0 && super::memory::encode_memory_exceeded() {
                self.cnf.set_memory_out();
                return None;
            }
            let v = self.term(t)?;
            self.vals.insert(t, v);
            if self.cnf.overflowed() {
                return None;
            }
        }
        for &r in &self.scan.encode_roots {
            let l = self.vals.get(&r)?.lit()?;
            self.cnf.add(&[l]);
        }
        (!self.cnf.overflowed()).then_some(())
    }

    fn val(&self, t: TermId) -> Option<Val> {
        self.vals.get(&t).cloned()
    }

    fn lit(&self, t: TermId) -> Option<Lit> {
        self.vals.get(&t)?.lit()
    }

    fn lits(&self, ts: &[TermId]) -> Option<Vec<Lit>> {
        ts.iter().map(|&t| self.lit(t)).collect()
    }

    fn term(&mut self, t: TermId) -> Option<Val> {
        let (node, sort) = self.scan.nodes.get(&t)?;
        let sort = *sort;
        Some(match node {
            Node::BoolConst(b) => Val::Bool(if *b { TRUE } else { FALSE }),
            Node::Const => self.constant(t, sort),
            Node::Ctor { ctor, args } => self.ctor(sort, *ctor, args)?,
            Node::Sel { kind, arg } => self.select(t, *kind, *arg)?,
            Node::Tester { ctor, arg } => Val::Bool(self.tester(*ctor, *arg)?),
            Node::Not(a) => Val::Bool(-self.lit(*a)?),
            Node::And(v) => {
                let ls = self.lits(v)?;
                Val::Bool(self.cnf.and(&ls))
            }
            Node::Or(v) => {
                let ls = self.lits(v)?;
                Val::Bool(self.cnf.or(&ls))
            }
            Node::Xor(v) => {
                let ls = self.lits(v)?;
                let mut acc = *ls.first()?;
                for &l in &ls[1..] {
                    acc = -self.cnf.iff(acc, l);
                }
                Val::Bool(acc)
            }
            Node::Implies(v) => {
                let ls = self.lits(v)?;
                let (last, prem) = ls.split_last()?;
                let mut c: Vec<Lit> = prem.iter().map(|&l| -l).collect();
                c.push(*last);
                Val::Bool(self.cnf.or(&c))
            }
            Node::Eq(v) => Val::Bool(self.equality(v)?),
            Node::Distinct(v) => Val::Bool(self.distinct(v)?),
            Node::Ite(c, a, b) => {
                let (c, a, b) = (self.lit(*c)?, self.val(*a)?, self.val(*b)?);
                mux(&mut self.cnf, c, &a, &b)?
            }
        })
    }

    /// Schema 8: declared constants share the value of their alias class.
    fn constant(&mut self, t: TermId, sort: FieldSort) -> Val {
        let rep = self.alias.get(&t).copied().unwrap_or(t);
        if let Some(v) = self.consts.get(&rep) {
            return v.clone();
        }
        let v = fresh(&mut self.cnf, self.scan, self.d, sort);
        self.consts.insert(rep, v.clone());
        v
    }

    fn nil(&mut self, sort: u32) -> Val {
        let (scan, d) = (self.scan, self.d);
        self.nils
            .entry(sort)
            .or_insert_with(|| nil_value(scan, d, sort))
            .clone()
    }

    /// Schema 3 (constructor values).
    fn ctor(&mut self, sort: FieldSort, ctor: usize, args: &[TermId]) -> Option<Val> {
        let FieldSort::Dt(id) = sort else {
            return None;
        };
        match &self.scan.sorts[id as usize].shape {
            SortShape::Enum { ctors } => Some(enum_const(ctors.len(), ctor)),
            SortShape::Record { .. } => {
                let fields = args
                    .iter()
                    .map(|&a| self.val(a))
                    .collect::<Option<Vec<_>>>()?;
                Some(Val::Record(Rc::new(fields)))
            }
            SortShape::List {
                cons_idx, rec_pos, ..
            } => {
                if ctor != *cons_idx {
                    return Some(self.nil(id));
                }
                let rec_pos = *rec_pos;
                let mut rows = Vec::new();
                for (i, &a) in args.iter().enumerate() {
                    if i != rec_pos {
                        match self.vals.get(&a)? {
                            Val::Enum(row) => rows.push(row.to_vec()),
                            _ => return None,
                        }
                    }
                }
                let tail = self.val(*args.get(rec_pos)?)?;
                cons_value(rows, &tail, self.d)
            }
        }
    }

    fn tester(&mut self, ctor: usize, arg: TermId) -> Option<Lit> {
        let FieldSort::Dt(id) = self.scan.sort_of(arg)? else {
            return None;
        };
        match (&self.scan.sorts[id as usize].shape, self.vals.get(&arg)?) {
            (SortShape::Enum { .. }, Val::Enum(row)) => row.get(ctor).copied(),
            (SortShape::Record { .. }, Val::Record(_)) => Some(TRUE),
            (SortShape::List { cons_idx, .. }, Val::List(cells)) => {
                let s0 = cells.first()?.s;
                Some(if ctor == *cons_idx { s0 } else { -s0 })
            }
            _ => None,
        }
    }

    fn equality(&mut self, v: &[TermId]) -> Option<Lit> {
        let first = self.val(*v.first()?)?;
        let mut parts = Vec::with_capacity(v.len());
        for &t in &v[1..] {
            let other = self.val(t)?;
            parts.push(self.eq(&first, &other)?);
        }
        Some(self.cnf.and(&parts))
    }

    fn distinct(&mut self, v: &[TermId]) -> Option<Lit> {
        let vals = v.iter().map(|&t| self.val(t)).collect::<Option<Vec<_>>>()?;
        let mut parts = Vec::new();
        for i in 0..vals.len() {
            for j in (i + 1)..vals.len() {
                parts.push(-self.eq(&vals[i], &vals[j])?);
            }
        }
        Some(self.cnf.and(&parts))
    }

    /// Schema 5 plus functionality (schema 4): two recursive-selector values
    /// of one kind whose arguments are both nil are equal,
    /// `s_0(x) | s_0(y) | e`.
    fn eq(&mut self, a: &Val, b: &Val) -> Option<Lit> {
        let e = eq_val(&mut self.cnf, a, b)?;
        if let (Val::List(x), Val::List(y)) = (a, b) {
            let rest_of =
                |p: &Rc<Vec<Rc<Cell>>>| self.rest_of.get(&(Rc::as_ptr(p) as usize)).copied();
            if let (Some((cx, sx, gx)), Some((cy, sy, gy))) = (rest_of(x), rest_of(y)) {
                if (sx, gx) == (sy, gy) {
                    self.cnf.add(&[cx, cy, e]);
                }
            }
        }
        Some(e)
    }

    /// Schema 3/4 and Lemma 4: selector applications.
    fn select(&mut self, t: TermId, kind: SelKind, arg: TermId) -> Option<Val> {
        let xv = self.val(arg)?;
        let (sort, field) = match kind {
            SelKind::RecordField { pos, .. } => {
                return match xv {
                    Val::Record(fields) => fields.get(pos).cloned(),
                    _ => None,
                };
            }
            SelKind::ListRest { sort } => (sort, None),
            SelKind::ListField { sort, field } => (sort, Some(field)),
        };
        let SortShape::List {
            cons_idx, rec_pos, ..
        } = &self.scan.sorts[sort as usize].shape
        else {
            return None;
        };
        // Syntactic constructor argument: selector-of-constructor (schema 3)
        // or the shared wrong-constructor term (schema 4, nullary nil).
        if let Some(Node::Ctor { ctor, args }) = self.scan.node(arg) {
            if *ctor != *cons_idx {
                return Some(self.shared(sort, field));
            }
            let pos = match field {
                None => *rec_pos,
                Some(j) => cell_arg_pos(j, *rec_pos),
            };
            return self.val(*args.get(pos)?);
        }
        let Val::List(cells) = xv else {
            return None;
        };
        let guarded = self.guarded.contains(&t);
        // `cells` is held by `vals` for the encoder's lifetime, so its
        // address identifies the value.
        let key = (Rc::as_ptr(&cells) as usize, sort, field, guarded);
        if let Some(v) = self.sel_memo.get(&key) {
            return Some(v.clone());
        }
        let v = match (field, guarded) {
            (None, true) => Some(self.rest_guarded(sort, &cells)),
            (None, false) => self.rest_general(sort, &cells),
            (Some(j), true) => Some(self.field_guarded(&cells, j)),
            (Some(j), false) => self.field_general(sort, &cells, j),
        }?;
        if let (None, Val::List(r), Some(c0)) = (field, &v, cells.first()) {
            self.rest_of
                .insert(Rc::as_ptr(r) as usize, (c0.s, sort, guarded));
        }
        self.sel_memo.insert(key, v.clone());
        Some(v)
    }

    /// The one shared value of `rest(nil)` / `field_j(nil)` (schema 4).
    fn shared(&mut self, sort: u32, field: Option<usize>) -> Val {
        let (scan, d) = (self.scan, self.d);
        match field {
            None => {
                if let Some(v) = self.shared_rest.get(&sort) {
                    return v.clone();
                }
                let v = fresh(&mut self.cnf, scan, d, FieldSort::Dt(sort));
                self.shared_rest.insert(sort, v.clone());
                v
            }
            Some(j) => {
                if let Some(v) = self.shared_field.get(&(sort, j)) {
                    return v.clone();
                }
                let e = cell_fields(scan, sort)[j];
                let v = fresh(&mut self.cnf, scan, d, FieldSort::Dt(e));
                self.shared_field.insert((sort, j), v.clone());
                v
            }
        }
    }

    /// Lemma 4, recursive selector: `ite(is-cons x, rest x, nil)` is the
    /// shift of `x` plus one fresh beyond-window cell `L` with
    /// `s(L) -> s_{D-1}(x)` (schema 1 at index D).
    fn rest_guarded(&mut self, sort: u32, x: &[Rc<Cell>]) -> Val {
        let mut cells: Vec<Rc<Cell>> = x.iter().skip(1).cloned().collect();
        let prev = x.last().map_or(FALSE, |c| c.s);
        let last = fresh_cell(&mut self.cnf, self.scan, sort, prev);
        cells.push(last);
        Val::List(Rc::new(cells))
    }

    /// Schema 4, recursive selector: under `s_0(x)` the shift of `x`, else
    /// the shared `rest(nil)`; the last cell is fresh with `s_0(x) & s(L) ->
    /// s_{D-1}(x)` and `!s_0(x) -> L == last cell of rest(nil)`.
    fn rest_general(&mut self, sort: u32, x: &[Rc<Cell>]) -> Option<Val> {
        let Val::List(rn) = self.shared(sort, None) else {
            return None;
        };
        let c = x.first()?.s;
        let d = self.d;
        let mut cells = Vec::with_capacity(d);
        for i in 0..d.saturating_sub(1) {
            cells.push(mux_cell(&mut self.cnf, c, &x[i + 1], &rn[i]));
        }
        let prev = cells.last().map_or(TRUE, |p: &Rc<Cell>| p.s);
        let last = fresh_cell(&mut self.cnf, self.scan, sort, prev);
        self.cnf.add(&[-c, -last.s, x.last()?.s]);
        assert_cell_equal(&mut self.cnf, -c, &last, rn.last()?);
        cells.push(last);
        Some(Val::List(Rc::new(cells)))
    }

    /// Lemma 4, field selector: `ite(is-cons x, f x, C_0)`: cell 0's row with
    /// the first constructor's bit OR-ed with `!s_0(x)` (enum rows only, so
    /// the default is the well-formed nullary `C_0`).
    fn field_guarded(&mut self, x: &[Rc<Cell>], j: usize) -> Val {
        let Some(c0) = x.first() else {
            return Val::Enum(Rc::new(Vec::new()));
        };
        let mut row = c0.rows[j].clone();
        if let Some(b) = row.first_mut() {
            *b = self.cnf.or(&[*b, -c0.s]);
        }
        Val::Enum(Rc::new(row))
    }

    /// Schema 4/9, field selector: `ite(s_0(x), row_j(cell 0), field_j(nil))`.
    fn field_general(&mut self, sort: u32, x: &[Rc<Cell>], j: usize) -> Option<Val> {
        let Val::Enum(fnil) = self.shared(sort, Some(j)) else {
            return None;
        };
        let c0 = x.first()?;
        Some(Val::Enum(Rc::new(mux_row(
            &mut self.cnf,
            c0.s,
            &c0.rows[j],
            &fnil,
        ))))
    }
}

/// Argument position of cell field `j` in the cons constructor.
pub(super) fn cell_arg_pos(j: usize, rec_pos: usize) -> usize {
    if j < rec_pos {
        j
    } else {
        j + 1
    }
}

/// `D_0` (heuristic only): one more than the largest number of distinct
/// ground cons applications reachable from a single assertion root.
pub(super) fn initial_depth(scan: &Scan, max_work: usize) -> usize {
    let mut ground: HashSet<TermId> = HashSet::default();
    for &t in &scan.order {
        if let Some(Node::Ctor { args, .. }) = scan.node(t) {
            if args.iter().all(|a| ground.contains(a)) {
                ground.insert(t);
            }
        }
    }
    let mut best = 0usize;
    let mut work = 0usize;
    for &r in &scan.roots {
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut stack = vec![r];
        let mut n = 0usize;
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            work += 1;
            if work > max_work {
                return best.max(8) + 1;
            }
            let Some(node) = scan.node(t) else { continue };
            let is_cons = matches!(node, Node::Ctor { args, .. } if !args.is_empty())
                && scan.sort_of(t).is_some_and(|s| scan.is_list(s));
            if is_cons && ground.contains(&t) {
                n += 1;
            }
            stack.extend(node.children());
        }
        best = best.max(n);
    }
    best + 1
}
