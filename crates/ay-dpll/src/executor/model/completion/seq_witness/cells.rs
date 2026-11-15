// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cell identification, element binding and fresh elements for
//! [`super::SeqStructure`].

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{Sort, TermId};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{Signed, Zero};

use super::{EvalValue, SeqStructure, Shape, MAX_WITNESS_CELLS};

pub(super) fn find(parent: &mut [usize], mut x: usize) -> usize {
    while parent[x] != x {
        parent[x] = parent[parent[x]];
        x = parent[x];
    }
    x
}

pub(super) fn union(parent: &mut [usize], a: usize, b: usize) {
    let (ra, rb) = (find(parent, a), find(parent, b));
    if ra != rb {
        // The smaller index stays the root, so roots do not depend on the
        // order the equalities were collected in.
        let (keep, drop) = if ra < rb { (ra, rb) } else { (rb, ra) };
        parent[drop] = keep;
    }
}

/// Dense class ids `0..count`, numbered in order of each class's first member.
pub(super) fn dense_classes(parent: &mut [usize]) -> (Vec<usize>, usize) {
    let mut dense: HashMap<usize, usize> = HashMap::default();
    let mut class_of = Vec::with_capacity(parent.len());
    for i in 0..parent.len() {
        let root = find(parent, i);
        let next = dense.len();
        class_of.push(*dense.entry(root).or_insert(next));
    }
    let count = dense.len();
    (class_of, count)
}

/// Element sorts whose values the construction can bind and freshen.
fn supported_element(sort: &Sort) -> bool {
    matches!(sort, Sort::Bool | Sort::Int | Sort::Real | Sort::BitVec(_))
}

fn fits(sort: &Sort, value: &EvalValue) -> bool {
    match (sort, value) {
        (Sort::Bool, EvalValue::Bool(_)) | (Sort::Real, EvalValue::Rational(_)) => true,
        (Sort::Int, EvalValue::Rational(r)) => r.is_integer(),
        (Sort::BitVec(bv), EvalValue::BitVec { width, .. }) => *width == bv.width,
        _ => false,
    }
}

/// Positional cells of the classes whose length is known.
struct Cells {
    base: Vec<Option<usize>>,
    parent: Vec<usize>,
    binds: Vec<(usize, EvalValue)>,
    /// Cells of `(seq.unit e)` terms whose `e` has no value yet: a later
    /// phase decides them, so no class sharing one may be emitted.
    open: Vec<usize>,
    /// A class with a member the construction could not interpret.
    partial: Vec<bool>,
}

impl Cells {
    fn at(&self, class: usize, pos: usize) -> usize {
        // Callers only pass classes with a known length and in-range
        // positions, both of which allocated `base[class]`.
        self.base[class].map_or(0, |b| b + pos)
    }
}

impl SeqStructure<'_> {
    fn element_sort(&self, class_member: usize) -> Option<Sort> {
        self.exec
            .ctx
            .terms
            .sort(self.terms[class_member])
            .seq_element()
            .cloned()
    }

    /// The model value of an element term, only when it fits `sort`.
    fn element_value(&self, e: TermId, sort: &Sort) -> Option<EvalValue> {
        let value = match self.exec.lookup_term_value(self.model, e) {
            EvalValue::Element(token) => self
                .exec
                .parse_model_value_string(&token, &Some(sort.clone())),
            value => value,
        };
        fits(sort, &value).then_some(value)
    }

    pub(super) fn construct(
        &self,
        lengths: &[Option<usize>],
    ) -> Option<HashMap<TermId, Vec<EvalValue>>> {
        let mut total = 0usize;
        let mut base = vec![None; self.class_count];
        for (class, len) in lengths.iter().enumerate() {
            if let Some(n) = len {
                base[class] = Some(total);
                total = total.checked_add(*n).filter(|&t| t <= MAX_WITNESS_CELLS)?;
            }
        }
        let mut cells = Cells {
            base,
            parent: (0..total).collect(),
            binds: Vec::new(),
            open: Vec::new(),
            partial: vec![false; self.class_count],
        };
        for i in 0..self.terms.len() {
            self.place_member(lengths, &mut cells, i)?;
        }
        self.bind_reads(lengths, &mut cells);
        let values = self.cell_values(lengths, &mut cells)?;
        self.emit(lengths, &mut cells, &values)
    }

    /// Identify or bind the cells of term `i`'s class through its shape.
    fn place_member(&self, lengths: &[Option<usize>], cells: &mut Cells, i: usize) -> Option<()> {
        let class = self.class_of[i];
        let Some(len) = lengths[class] else {
            return Some(());
        };
        match &self.shapes[i] {
            Shape::Empty => {}
            Shape::Concat(parts) => {
                let mut offset = 0usize;
                let mut spans = Vec::with_capacity(parts.len());
                for &p in parts {
                    let Some(n) = lengths[self.class_of[p]] else {
                        cells.partial[class] = true;
                        return Some(());
                    };
                    spans.push((self.class_of[p], offset, n));
                    offset = offset.checked_add(n)?;
                }
                if offset != len {
                    return None;
                }
                for (pc, off, n) in spans {
                    for pos in 0..n {
                        let (a, b) = (cells.at(class, off + pos), cells.at(pc, pos));
                        union(&mut cells.parent, a, b);
                    }
                }
            }
            Shape::Extract { src, start, count } => {
                let sc = self.class_of[*src];
                let window =
                    lengths[sc].and_then(|sl| self.extract_window(lengths, *start, *count, sl));
                let Some((off, n)) = window else {
                    cells.partial[class] = true;
                    return Some(());
                };
                if n != len {
                    return None;
                }
                for pos in 0..n {
                    let (a, b) = (cells.at(class, pos), cells.at(sc, off + pos));
                    union(&mut cells.parent, a, b);
                }
            }
            Shape::Unit(e) => {
                let value = self
                    .element_sort(i)
                    .and_then(|sort| self.element_value(*e, &sort));
                if len != 1 {
                    return None;
                }
                match value {
                    Some(v) => cells.binds.push((cells.at(class, 0), v)),
                    None => cells.open.push(cells.at(class, 0)),
                }
            }
            Shape::Opaque => {
                if let Some(elems) = &self.concrete[i] {
                    if elems.len() != len {
                        return None;
                    }
                    for (pos, v) in elems.iter().enumerate() {
                        cells.binds.push((cells.at(class, pos), v.clone()));
                    }
                }
            }
        }
        Some(())
    }

    /// Bind the cell each in-range `(seq.nth s k)` model row reads.
    fn bind_reads(&self, lengths: &[Option<usize>], cells: &mut Cells) {
        for &(read, s, idx) in &self.nth_reads {
            let Some(&si) = self.index.get(&s) else {
                continue;
            };
            let class = self.class_of[si];
            let Some(len) = lengths[class] else { continue };
            let Some(k) = self.int_value(lengths, idx, 0) else {
                continue;
            };
            if k.is_negative() || k >= BigInt::from(len) {
                continue;
            }
            let Some(pos) = num_traits::ToPrimitive::to_usize(&k) else {
                continue;
            };
            let sort = self.element_sort(si);
            if let Some(v) = sort.and_then(|sort| self.element_value(read, &sort)) {
                cells.binds.push((cells.at(class, pos), v));
            }
        }
    }

    /// One value per cell root: its binding, or a fresh element. `None` when
    /// two different values are bound to one cell.
    fn cell_values(
        &self,
        lengths: &[Option<usize>],
        cells: &mut Cells,
    ) -> Option<HashMap<usize, EvalValue>> {
        let mut values: HashMap<usize, EvalValue> = HashMap::default();
        for (cell, value) in std::mem::take(&mut cells.binds) {
            let root = find(&mut cells.parent, cell);
            match values.get(&root) {
                Some(existing) if *existing != value => return None,
                Some(_) => {}
                None => {
                    values.insert(root, value);
                }
            }
        }
        let mut first_member: Vec<Option<usize>> = vec![None; self.class_count];
        for (i, &class) in self.class_of.iter().enumerate() {
            first_member[class].get_or_insert(i);
        }
        let mut fresh = FreshElements::new(&self.max_int_literal, values.values());
        for (class, len) in lengths.iter().enumerate() {
            let (Some(len), Some(member)) = (*len, first_member[class]) else {
                continue;
            };
            let Some(sort) = self.element_sort(member).filter(supported_element) else {
                cells.partial[class] = true;
                continue;
            };
            for pos in 0..len {
                let cell = cells.at(class, pos);
                let root = find(&mut cells.parent, cell);
                if !values.contains_key(&root) {
                    values.insert(root, fresh.next(&sort));
                }
            }
        }
        Some(values)
    }

    /// Values for the non-builtin members of every fully constructed class.
    fn emit(
        &self,
        lengths: &[Option<usize>],
        cells: &mut Cells,
        values: &HashMap<usize, EvalValue>,
    ) -> Option<HashMap<TermId, Vec<EvalValue>>> {
        let open: HashSet<usize> = std::mem::take(&mut cells.open)
            .into_iter()
            .map(|cell| find(&mut cells.parent, cell))
            .collect();
        for (class, len) in lengths.iter().enumerate() {
            for pos in 0..len.unwrap_or(0) {
                let cell = cells.at(class, pos);
                if open.contains(&find(&mut cells.parent, cell)) {
                    cells.partial[class] = true;
                    break;
                }
            }
        }
        let mut out: HashMap<TermId, Vec<EvalValue>> = HashMap::default();
        let mut cloned = 0usize;
        for (i, &t) in self.terms.iter().enumerate() {
            let class = self.class_of[i];
            let (Some(len), false) = (lengths[class], cells.partial[class]) else {
                continue;
            };
            let carrier = self.exec.is_opaque_seq_carrier(t);
            if !carrier {
                continue;
            }
            let mut elems = Vec::with_capacity(len);
            for pos in 0..len {
                let cell = cells.at(class, pos);
                let root = find(&mut cells.parent, cell);
                elems.push(values.get(&root)?.clone());
            }
            cloned = cloned
                .checked_add(len)
                .filter(|&c| c <= MAX_WITNESS_CELLS)?;
            out.insert(t, elems);
        }
        Some(out)
    }
}

/// Pairwise-distinct elements that avoid every bound value and every integer
/// literal of the problem.
struct FreshElements {
    next_int: BigInt,
    used_bv: HashSet<(u32, BigInt)>,
    next_bv: HashMap<u32, BigInt>,
}

impl FreshElements {
    fn new<'v>(max_int_literal: &BigInt, bound: impl Iterator<Item = &'v EvalValue>) -> Self {
        let mut next_int = max_int_literal.clone();
        let mut used_bv = HashSet::default();
        for v in bound {
            match v {
                EvalValue::Rational(r) => {
                    let magnitude = r.abs().ceil().to_integer();
                    if magnitude > next_int {
                        next_int = magnitude;
                    }
                }
                EvalValue::BitVec { value, width } => {
                    used_bv.insert((*width, value.clone()));
                }
                _ => {}
            }
        }
        Self {
            next_int: next_int + 1,
            used_bv,
            next_bv: HashMap::default(),
        }
    }

    fn next(&mut self, sort: &Sort) -> EvalValue {
        match sort {
            Sort::Int | Sort::Real => {
                let v = self.next_int.clone();
                self.next_int += 1;
                EvalValue::Rational(BigRational::from(v))
            }
            Sort::BitVec(bv) => {
                let width = bv.width;
                let modulus = BigInt::from(1) << width;
                let counter = self.next_bv.entry(width).or_insert_with(BigInt::zero);
                // Skip bound values while the domain still has room; past
                // that, repeats are allowed and the gates judge the result.
                let mut steps = 0usize;
                while self.used_bv.contains(&(width, counter.clone() % &modulus))
                    && steps < MAX_WITNESS_CELLS
                {
                    *counter += 1;
                    steps += 1;
                }
                let value = counter.clone() % &modulus;
                *counter += 1;
                self.used_bv.insert((width, value.clone()));
                EvalValue::BitVec { value, width }
            }
            _ => EvalValue::Bool(false),
        }
    }
}
