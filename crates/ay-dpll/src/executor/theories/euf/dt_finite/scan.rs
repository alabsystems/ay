// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The fragment gate (precondition P1 of the module doc).
//!
//! Sort classes (M1):
//! * `Enum`: a datatype whose constructors are all nullary.
//! * `Record`: a non-recursive datatype with exactly ONE constructor whose
//!   fields are `Bool`, `Enum`, `Record` or `List`.
//! * `List`: exactly two constructors — a cons with exactly one field of the
//!   sort itself and every other field an `Enum`, and one NULLARY nil.
//!
//! Everything else is refused: multi-constructor sorts with fields (sums),
//! several nils or nils with fields, cells with non-enum fields, tree shapes,
//! mutual recursion, parametric instances, and every non-datatype, non-Bool
//! sort. Terms: Boolean connectives, `=`, `distinct`, `ite`, declared
//! nullary constants, constructors, selectors and testers. Declared
//! functions with arguments, quantifiers, `let` and every theory operator are
//! refused.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::{Constant, TermData};
use ay_core::{Sort, TermId};
use ay_frontend::DeclarationKind;

use super::signature::{register_members, shape_of, Signature};
use crate::executor::Executor;

/// Hard cap on the reachable term DAG the gate will classify.
const MAX_TERMS: usize = 4_000_000;

/// Sort of an admitted term or field.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum FieldSort {
    Bool,
    Dt(u32),
}

/// Shape of an admitted datatype sort.
pub(super) enum SortShape {
    Enum {
        ctors: Vec<String>,
    },
    Record {
        ctor: String,
        fields: Vec<FieldSort>,
    },
    List {
        cons: String,
        nil: String,
        /// Declaration index of the cons constructor (the nil is the other).
        cons_idx: usize,
        /// Position of the recursive field among the cons fields.
        rec_pos: usize,
        /// Enum sort of each non-recursive cons field, in declaration order.
        cell_fields: Vec<u32>,
    },
}

pub(super) struct DtSort {
    pub(super) name: String,
    pub(super) shape: SortShape,
    /// The term-store sort object (for minting ground model terms).
    pub(super) sort: Sort,
}

/// What a selector symbol projects.
#[derive(Clone, Copy, Debug)]
pub(super) enum SelKind {
    /// Field `pos` of the record sort `sort`.
    RecordField { sort: u32, pos: usize },
    /// The recursive selector of the list sort `sort`.
    ListRest { sort: u32 },
    /// Cell field `field` (index among the non-recursive cons fields).
    ListField { sort: u32, field: usize },
}

/// Classified node of the admitted term DAG.
#[derive(Clone, Debug)]
pub(super) enum Node {
    BoolConst(bool),
    /// A declared constant (free nullary symbol) of any admitted sort.
    Const,
    /// Constructor `ctor` (index in the sort's declaration) applied to `args`.
    Ctor {
        ctor: usize,
        args: Vec<TermId>,
    },
    Sel {
        kind: SelKind,
        arg: TermId,
    },
    /// `((_ is C) arg)` for constructor index `ctor` of the argument's sort.
    Tester {
        ctor: usize,
        arg: TermId,
    },
    Not(TermId),
    And(Vec<TermId>),
    Or(Vec<TermId>),
    Xor(Vec<TermId>),
    Implies(Vec<TermId>),
    Eq(Vec<TermId>),
    Distinct(Vec<TermId>),
    Ite(TermId, TermId, TermId),
}

impl Node {
    pub(super) fn children(&self) -> Vec<TermId> {
        match self {
            Node::BoolConst(_) | Node::Const => Vec::new(),
            Node::Ctor { args, .. } => args.clone(),
            Node::Sel { arg, .. } | Node::Tester { arg, .. } => vec![*arg],
            Node::Not(a) => vec![*a],
            Node::And(v)
            | Node::Or(v)
            | Node::Xor(v)
            | Node::Implies(v)
            | Node::Eq(v)
            | Node::Distinct(v) => v.clone(),
            Node::Ite(c, a, b) => vec![*c, *a, *b],
        }
    }
}

/// Output of the gate: the admitted signature and the classified term DAG
/// in children-first order.
pub(super) struct Scan {
    pub(super) sorts: Vec<DtSort>,
    pub(super) nodes: HashMap<TermId, (Node, FieldSort)>,
    /// Every reachable term, children before parents.
    pub(super) order: Vec<TermId>,
    pub(super) roots: Vec<TermId>,
    /// The roots that are encoded and asserted: `roots` minus the enum
    /// domain-closure tautologies (see [`Scan::is_domain_closure`]).
    pub(super) encode_roots: Vec<TermId>,
    /// Constructor name -> (sort, declaration index), every admitted sort.
    pub(super) ctor_of: HashMap<String, (u32, usize)>,
    /// Selector name -> what it projects, every admitted sort.
    pub(super) sel_of: HashMap<String, SelKind>,
}

impl Scan {
    pub(super) fn node(&self, t: TermId) -> Option<&Node> {
        self.nodes.get(&t).map(|(n, _)| n)
    }

    pub(super) fn sort_of(&self, t: TermId) -> Option<FieldSort> {
        self.nodes.get(&t).map(|(_, s)| *s)
    }

    /// Whether `t` is `(or (= t0 C_1) ... (= t0 C_k))` naming EVERY
    /// constructor of the enum sort of one term `t0` (either argument order).
    /// Such a root is valid in every datatype model (exhaustiveness), so
    /// dropping it from the encoded conjunction preserves equivalence; the
    /// lane's evaluator still checks it. (Preprocessing adds such domain
    /// closures; asserting them would make guarded selectors unguarded.)
    pub(super) fn is_domain_closure(&self, t: TermId) -> bool {
        let Some(Node::Or(args)) = self.node(t) else {
            return false;
        };
        let mut subject: Option<TermId> = None;
        let mut seen: Vec<usize> = Vec::new();
        for &a in args {
            let Some(Node::Eq(pair)) = self.node(a) else {
                return false;
            };
            let [x, y] = pair.as_slice() else {
                return false;
            };
            let (ctor, other) = match (self.node(*x), self.node(*y)) {
                (Some(Node::Ctor { ctor, args }), _) if args.is_empty() => (*ctor, *y),
                (_, Some(Node::Ctor { ctor, args })) if args.is_empty() => (*ctor, *x),
                _ => return false,
            };
            if *subject.get_or_insert(other) != other {
                return false;
            }
            seen.push(ctor);
        }
        let Some(FieldSort::Dt(s)) = subject.and_then(|x| self.sort_of(x)) else {
            return false;
        };
        let SortShape::Enum { ctors } = &self.sorts[s as usize].shape else {
            return false;
        };
        seen.sort_unstable();
        seen.dedup();
        seen.len() == ctors.len()
    }

    pub(super) fn is_list(&self, s: FieldSort) -> bool {
        match s {
            FieldSort::Dt(i) => matches!(self.sorts[i as usize].shape, SortShape::List { .. }),
            FieldSort::Bool => false,
        }
    }
}

impl Executor {
    /// The fragment gate: `Err(reason)` declines the lane.
    pub(super) fn dt_fd_scan(&self) -> Result<Scan, String> {
        let roots = self.ctx.assertions.clone();
        if roots.is_empty() {
            return Err("no-assertions".to_string());
        }
        let mut sig = Signature::default();
        let mut nodes: HashMap<TermId, (Node, FieldSort)> = HashMap::default();
        let mut order = Vec::new();
        // Iterative post-order DFS: (term, children_done).
        let mut stack: Vec<(TermId, bool)> = roots.iter().rev().map(|&r| (r, false)).collect();
        while let Some((t, done)) = stack.pop() {
            if done {
                order.push(t);
                continue;
            }
            if nodes.contains_key(&t) {
                continue;
            }
            let Some(entry) = self.dt_fd_classify_term(t, &mut sig) else {
                let mut what = format!("term {:?}", self.ctx.terms.get(t));
                what.truncate(160);
                return Err(what);
            };
            let children = entry.0.children();
            nodes.insert(t, entry);
            if nodes.len() > MAX_TERMS {
                return Err("term-budget".to_string());
            }
            stack.push((t, true));
            for c in children.into_iter().rev() {
                if !nodes.contains_key(&c) {
                    stack.push((c, false));
                }
            }
        }
        // Roots must be Boolean; at least one list-sorted term must occur
        // (pure enum/record problems belong to other lanes).
        if roots
            .iter()
            .any(|r| nodes.get(r).map(|e| e.1) != Some(FieldSort::Bool))
        {
            return Err("non-bool-root".to_string());
        }
        let mut scan = Scan {
            sorts: sig.sorts,
            nodes,
            order,
            roots,
            encode_roots: Vec::new(),
            ctor_of: sig.ctor_of,
            sel_of: sig.sel_of,
        };
        scan.encode_roots = scan
            .roots
            .iter()
            .copied()
            .filter(|&r| !scan.is_domain_closure(r))
            .collect();
        if !scan.nodes.values().any(|(_, s)| scan.is_list(*s)) {
            return Err("no-list-sort".to_string());
        }
        Ok(scan)
    }

    /// Classify one term (not its children).
    fn dt_fd_classify_term(&self, t: TermId, sig: &mut Signature) -> Option<(Node, FieldSort)> {
        let sort = self.dt_fd_sort(self.ctx.terms.sort(t), sig)?;
        let node = match self.ctx.terms.get(t) {
            TermData::Const(Constant::Bool(b)) => Node::BoolConst(*b),
            TermData::Var(name, _) => self.dt_fd_leaf(name, sort, true, sig)?,
            TermData::Not(a) => Node::Not(*a),
            TermData::Ite(c, a, b) => Node::Ite(*c, *a, *b),
            TermData::App(sym, args) if args.is_empty() => {
                self.dt_fd_leaf(sym.name(), sort, false, sig)?
            }
            TermData::App(sym, args) => self.dt_fd_app(sym.name(), args, sort, sig)?,
            _ => return None,
        };
        Some((node, sort))
    }

    /// A nullary leaf: a nullary constructor or a declared constant.
    fn dt_fd_leaf(
        &self,
        name: &str,
        sort: FieldSort,
        is_var: bool,
        sig: &mut Signature,
    ) -> Option<Node> {
        let kind = self
            .ctx
            .exact_datatype_member_info(name)
            .map(|i| i.declaration_kind());
        if kind == Some(DeclarationKind::DatatypeConstructor) {
            let (s, ctor) = *sig.ctor_of.get(name)?;
            return (FieldSort::Dt(s) == sort).then_some(Node::Ctor {
                ctor,
                args: Vec::new(),
            });
        }
        if kind.is_some() {
            return None;
        }
        if is_var {
            return Some(Node::Const);
        }
        let declared = self
            .ctx
            .symbol_info_by_identity(name)
            .map(|i| i.declaration_kind());
        (declared == Some(DeclarationKind::Uninterpreted)).then_some(Node::Const)
    }

    /// An application with at least one argument.
    fn dt_fd_app(
        &self,
        name: &str,
        args: &[TermId],
        sort: FieldSort,
        sig: &mut Signature,
    ) -> Option<Node> {
        let v = args.to_vec();
        let bool_result = sort == FieldSort::Bool;
        match name {
            "and" if bool_result => return Some(Node::And(v)),
            "or" if bool_result => return Some(Node::Or(v)),
            "xor" if bool_result => return Some(Node::Xor(v)),
            "=>" if bool_result => return Some(Node::Implies(v)),
            "=" if bool_result && v.len() >= 2 => return Some(Node::Eq(v)),
            "distinct" if bool_result && v.len() >= 2 => return Some(Node::Distinct(v)),
            _ => {}
        }
        let kind = self
            .ctx
            .exact_datatype_member_info(name)
            .map(|i| i.declaration_kind())?;
        // Classify the argument sort first: it registers the member symbols.
        let arg_sort = self.dt_fd_sort(self.ctx.terms.sort(v[0]), sig)?;
        match kind {
            DeclarationKind::DatatypeConstructor => {
                let (s, ctor) = *sig.ctor_of.get(name)?;
                (FieldSort::Dt(s) == sort).then_some(Node::Ctor { ctor, args: v })
            }
            DeclarationKind::DatatypeSelector if v.len() == 1 => {
                let kind = *sig.sel_of.get(name)?;
                let owner = match kind {
                    SelKind::ListRest { sort }
                    | SelKind::ListField { sort, .. }
                    | SelKind::RecordField { sort, .. } => sort,
                };
                (arg_sort == FieldSort::Dt(owner)).then_some(Node::Sel { kind, arg: v[0] })
            }
            DeclarationKind::DatatypeTester if v.len() == 1 && bool_result => {
                let ctor_name = name.strip_prefix("is-")?;
                let (s, ctor) = *sig.ctor_of.get(ctor_name)?;
                (arg_sort == FieldSort::Dt(s)).then_some(Node::Tester { ctor, arg: v[0] })
            }
            _ => None,
        }
    }

    /// Admit a sort: `Bool`, or a datatype of an admitted shape.
    fn dt_fd_sort(&self, sort: &Sort, sig: &mut Signature) -> Option<FieldSort> {
        if *sort == Sort::Bool {
            return Some(FieldSort::Bool);
        }
        let name = self.datatype_sort_name(sort)?;
        self.dt_fd_classify_sort(&name, sort, sig)
            .map(FieldSort::Dt)
    }

    /// Classify one datatype by name (memoized; refusals are memoized too).
    fn dt_fd_classify_sort(&self, name: &str, sort: &Sort, sig: &mut Signature) -> Option<u32> {
        if let Some(cached) = sig.by_name.get(name) {
            return *cached;
        }
        if sig.visiting.iter().any(|n| n == name) {
            return None; // mutual recursion through another sort
        }
        sig.visiting.push(name.to_string());
        let shape = self.dt_fd_shape(name, sig);
        sig.visiting.pop();
        let result = shape.map(|shape| {
            let id = sig.sorts.len() as u32;
            sig.sorts.push(DtSort {
                name: name.to_string(),
                shape,
                sort: sort.clone(),
            });
            id
        });
        sig.by_name.insert(name.to_string(), result);
        if let Some(id) = result {
            register_members(sig, id, self);
        }
        result
    }

    /// The shape of `name`, or `None` when it is outside the fragment.
    fn dt_fd_shape(&self, name: &str, sig: &mut Signature) -> Option<SortShape> {
        if self.ctx.is_parametric_datatype_instance(name) {
            return None;
        }
        let ctors: Vec<String> = self.ctx.datatype_constructors(name)?.to_vec();
        if ctors.is_empty() {
            return None;
        }
        let mut fields: Vec<Vec<(bool, Option<FieldSort>)>> = Vec::new();
        for c in &ctors {
            let info = self
                .ctx
                .constructor_selector_info(c)
                .unwrap_or(&[])
                .to_vec();
            let mut row = Vec::new();
            for (_, s) in &info {
                let recursive = self.datatype_sort_name(s).as_deref() == Some(name);
                let fs = if recursive {
                    None
                } else {
                    Some(self.dt_fd_sort(s, sig)?)
                };
                row.push((recursive, fs));
            }
            fields.push(row);
        }
        shape_of(&ctors, &fields, sig)
    }
}
