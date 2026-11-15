// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SAT side (Lemma 3): decode a CNF model into ground datatype values,
//! evaluate the ORIGINAL assertion roots under them with SMT-LIB semantics
//! (selectors total; `sel(nil)` takes one committed value per selector), and
//! export the accepted model for the executor's validation pipeline.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::TermId;

use super::cnf::Lit;
use super::encode::{cell_arg_pos, Encoder};
use super::scan::{FieldSort, Node, Scan, SelKind, SortShape};
use super::values::Val;

/// A hash-consed ground value.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub(super) enum VNode {
    Bool(bool),
    Ctor {
        sort: u32,
        ctor: u32,
        args: Vec<u32>,
    },
}

#[derive(Default, Clone)]
pub(super) struct Values {
    nodes: Vec<VNode>,
    ids: HashMap<VNode, u32>,
}

impl Values {
    pub(super) fn intern(&mut self, n: VNode) -> u32 {
        if let Some(&id) = self.ids.get(&n) {
            return id;
        }
        let id = self.nodes.len() as u32;
        self.nodes.push(n.clone());
        self.ids.insert(n, id);
        id
    }

    pub(super) fn get(&self, id: u32) -> Option<&VNode> {
        self.nodes.get(id as usize)
    }

    fn as_bool(&self, id: u32) -> Option<bool> {
        match self.get(id)? {
            VNode::Bool(b) => Some(*b),
            VNode::Ctor { .. } => None,
        }
    }
}

/// Truth of a DIMACS literal under a 0-indexed SAT model.
pub(super) fn bit(model: &[bool], l: Lit) -> bool {
    let v = l.unsigned_abs() as usize;
    let b = v
        .checked_sub(1)
        .and_then(|i| model.get(i))
        .copied()
        .unwrap_or(false);
    if l > 0 {
        b
    } else {
        !b
    }
}

/// Decoder over one solved encoding.
pub(super) struct Decoder<'e, 'a> {
    pub(super) enc: &'e Encoder<'a>,
    pub(super) model: &'e [bool],
    pub(super) values: Values,
    /// Values fixed by the caller instead of decoded (the test oracle).
    pub(super) fixed_consts: HashMap<TermId, u32>,
    pub(super) fixed_rest: HashMap<u32, u32>,
    pub(super) fixed_field: HashMap<(u32, usize), u32>,
}

impl<'e, 'a> Decoder<'e, 'a> {
    pub(super) fn new(enc: &'e Encoder<'a>, model: &'e [bool]) -> Self {
        Self {
            enc,
            model,
            values: Values::default(),
            fixed_consts: HashMap::default(),
            fixed_rest: HashMap::default(),
            fixed_field: HashMap::default(),
        }
    }

    fn scan(&self) -> &'e Scan {
        self.enc.scan
    }
}

impl Decoder<'_, '_> {
    pub(super) fn nil_of(&mut self, sort: u32) -> Option<u32> {
        let SortShape::List { cons_idx, .. } = self.scan().sorts[sort as usize].shape else {
            return None;
        };
        Some(self.values.intern(VNode::Ctor {
            sort,
            ctor: (1 - cons_idx) as u32,
            args: Vec::new(),
        }))
    }

    fn row_index(&self, row: &[Lit]) -> Option<u32> {
        let mut hits = row.iter().enumerate().filter(|(_, &l)| bit(self.model, l));
        let (i, _) = hits.next()?;
        hits.next().is_none().then_some(i as u32)
    }

    /// Decode an encoded value of `sort`. A deep list (all `D` cells
    /// present) is completed with nil after cell `D-1`.
    pub(super) fn decode(&mut self, v: &Val, sort: FieldSort) -> Option<u32> {
        let FieldSort::Dt(id) = sort else {
            let l = v.lit()?;
            return Some(self.values.intern(VNode::Bool(bit(self.model, l))));
        };
        match (&self.scan().sorts[id as usize].shape, v) {
            (SortShape::Enum { .. }, Val::Enum(row)) => {
                let c = self.row_index(row)?;
                Some(self.enum_value(id, c))
            }
            (SortShape::Record { fields, .. }, Val::Record(vals)) => {
                let fields = fields.clone();
                let mut args = Vec::with_capacity(fields.len());
                for (f, fv) in fields.iter().zip(vals.iter()) {
                    args.push(self.decode(fv, *f)?);
                }
                Some(self.values.intern(VNode::Ctor {
                    sort: id,
                    ctor: 0,
                    args,
                }))
            }
            (
                SortShape::List {
                    cons_idx,
                    rec_pos,
                    cell_fields,
                    ..
                },
                Val::List(cells),
            ) => {
                let (cons_idx, rec_pos, cell_fields) = (*cons_idx, *rec_pos, cell_fields.clone());
                let mut present: Vec<Vec<u32>> = Vec::new();
                for cell in cells.iter() {
                    if !bit(self.model, cell.s) {
                        break;
                    }
                    let mut fs = Vec::with_capacity(cell.rows.len());
                    for (row, &e) in cell.rows.iter().zip(&cell_fields) {
                        let c = self.row_index(row)?;
                        fs.push(self.enum_value(e, c));
                    }
                    present.push(fs);
                }
                let mut acc = self.nil_of(id)?;
                for mut fs in present.into_iter().rev() {
                    fs.insert(rec_pos.min(fs.len()), acc);
                    acc = self.values.intern(VNode::Ctor {
                        sort: id,
                        ctor: cons_idx as u32,
                        args: fs,
                    });
                }
                Some(acc)
            }
            _ => None,
        }
    }

    pub(super) fn enum_value(&mut self, sort: u32, ctor: u32) -> u32 {
        self.values.intern(VNode::Ctor {
            sort,
            ctor,
            args: Vec::new(),
        })
    }

    /// Whether some encoded list value is deep (cell `D-1` present).
    pub(super) fn any_deep(&self) -> bool {
        let deep = |v: &Val| match v {
            Val::List(cells) => cells.last().is_some_and(|c| bit(self.model, c.s)),
            _ => false,
        };
        self.enc.vals.values().any(deep)
            || self.enc.shared_rest.values().any(deep)
            || self.enc.shared_field.values().any(deep)
    }

    /// The committed value of `rest(nil)` for a list sort.
    pub(super) fn rest_nil(&mut self, sort: u32) -> Option<u32> {
        if let Some(&v) = self.fixed_rest.get(&sort) {
            return Some(v);
        }
        match self.enc.shared_rest.get(&sort) {
            Some(v) => {
                let v = v.clone();
                self.decode(&v, FieldSort::Dt(sort))
            }
            None => self.nil_of(sort),
        }
    }

    /// The committed value of `field_j(nil)`.
    pub(super) fn field_nil(&mut self, sort: u32, j: usize) -> Option<u32> {
        let SortShape::List { cell_fields, .. } = &self.scan().sorts[sort as usize].shape else {
            return None;
        };
        let e = *cell_fields.get(j)?;
        if let Some(&v) = self.fixed_field.get(&(sort, j)) {
            return Some(v);
        }
        match self.enc.shared_field.get(&(sort, j)) {
            Some(v) => {
                let v = v.clone();
                self.decode(&v, FieldSort::Dt(e))
            }
            None => Some(self.enum_value(e, 0)),
        }
    }

    /// Evaluate every admitted term under the decoded constants; returns
    /// the per-term values when every root evaluates to `true`.
    pub(super) fn evaluate(&mut self) -> Option<HashMap<TermId, u32>> {
        let mut out: HashMap<TermId, u32> = HashMap::default();
        let order = self.scan().order.clone();
        for t in order {
            let v = self.eval_term(t, &out)?;
            out.insert(t, v);
        }
        let roots = &self.scan().roots;
        let ok = roots
            .iter()
            .all(|r| out.get(r).and_then(|&v| self.values.as_bool(v)) == Some(true));
        ok.then_some(out)
    }

    fn eval_term(&mut self, t: TermId, env: &HashMap<TermId, u32>) -> Option<u32> {
        let (node, sort) = self.scan().nodes.get(&t)?.clone();
        let get = |x: &TermId| env.get(x).copied();
        let bool_of = |s: &Self, x: &TermId| get(x).and_then(|v| s.values.as_bool(v));
        let b = |s: &mut Self, v: bool| Some(s.values.intern(VNode::Bool(v)));
        match node {
            Node::BoolConst(v) => b(self, v),
            Node::Const => {
                if let Some(&v) = self.fixed_consts.get(&t) {
                    return Some(v);
                }
                let v = self.enc.vals.get(&t)?.clone();
                self.decode(&v, sort)
            }
            Node::Ctor { ctor, args } => {
                let FieldSort::Dt(id) = sort else { return None };
                let args = args.iter().map(get).collect::<Option<Vec<_>>>()?;
                Some(self.values.intern(VNode::Ctor {
                    sort: id,
                    ctor: ctor as u32,
                    args,
                }))
            }
            Node::Sel { kind, arg } => self.eval_sel(kind, get(&arg)?),
            Node::Tester { ctor, arg } => {
                let is = matches!(self.values.get(get(&arg)?)?,
                    VNode::Ctor { ctor: c, .. } if *c as usize == ctor);
                b(self, is)
            }
            Node::Not(a) => {
                let v = !bool_of(self, &a)?;
                b(self, v)
            }
            Node::And(v) => {
                let all = v
                    .iter()
                    .map(|x| bool_of(self, x))
                    .collect::<Option<Vec<_>>>()?;
                b(self, all.iter().all(|&x| x))
            }
            Node::Or(v) => {
                let all = v
                    .iter()
                    .map(|x| bool_of(self, x))
                    .collect::<Option<Vec<_>>>()?;
                b(self, all.iter().any(|&x| x))
            }
            Node::Xor(v) => {
                let all = v
                    .iter()
                    .map(|x| bool_of(self, x))
                    .collect::<Option<Vec<_>>>()?;
                b(self, all.iter().fold(false, |acc, &x| acc ^ x))
            }
            Node::Implies(v) => {
                let all = v
                    .iter()
                    .map(|x| bool_of(self, x))
                    .collect::<Option<Vec<_>>>()?;
                let (last, prem) = all.split_last()?;
                b(self, !prem.iter().all(|&x| x) || *last)
            }
            Node::Eq(v) => {
                let ids = v.iter().map(get).collect::<Option<Vec<_>>>()?;
                b(self, ids.iter().all(|&x| x == ids[0]))
            }
            Node::Distinct(v) => {
                let ids = v.iter().map(get).collect::<Option<Vec<_>>>()?;
                let set: HashSet<u32> = ids.iter().copied().collect();
                b(self, set.len() == ids.len())
            }
            Node::Ite(c, x, y) => {
                if bool_of(self, &c)? {
                    get(&x)
                } else {
                    get(&y)
                }
            }
        }
    }

    fn eval_sel(&mut self, kind: SelKind, arg: u32) -> Option<u32> {
        let VNode::Ctor { ctor, args, .. } = self.values.get(arg)?.clone() else {
            return None;
        };
        match kind {
            SelKind::RecordField { pos, .. } => args.get(pos).copied(),
            SelKind::ListRest { sort } | SelKind::ListField { sort, .. } => {
                let SortShape::List {
                    cons_idx, rec_pos, ..
                } = self.scan().sorts[sort as usize].shape
                else {
                    return None;
                };
                let field = match kind {
                    SelKind::ListField { field, .. } => Some(field),
                    _ => None,
                };
                if ctor as usize == cons_idx {
                    let pos = field.map_or(rec_pos, |j| cell_arg_pos(j, rec_pos));
                    return args.get(pos).copied();
                }
                match field {
                    None => self.rest_nil(sort),
                    Some(j) => self.field_nil(sort, j),
                }
            }
        }
    }
}
