// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Export of an evaluator-accepted model to the executor's model pipeline.
//!
//! Every datatype-sorted admitted term is mapped (EUF `term_values`) to an
//! element naming its evaluated ground value, and every such value is also
//! MINTED as a ground constructor term carrying the same element. The
//! pipeline's single-source datatype assignment therefore finds a
//! constructor application in every value class and renders exactly the
//! value the lane evaluated; the always-on validation and the independent
//! gate then re-check the ORIGINAL assertions against it.

use std::collections::BTreeMap;

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::Symbol;
use ay_core::TermId;
use ay_euf::EufModel;

use super::decode::{VNode, Values};
use super::scan::{FieldSort, Node, Scan, SelKind, SortShape};
use crate::executor::model::lane_ground_model::{Ground, GroundSel, GroundSort, LaneGroundModel};
use crate::executor::Executor;

/// A model the lane's own evaluator accepted.
pub(super) struct Accepted {
    pub(super) values: Values,
    /// Value of every admitted term.
    pub(super) env: HashMap<TermId, u32>,
    /// Declared Bool constants and their (1-based) CNF variables.
    pub(super) bool_vars: BTreeMap<TermId, u32>,
    /// The committed `rest(nil)` per list sort and `field_j(nil)` per
    /// (list sort, cell field): with `env` they make the model total.
    pub(super) rest_nil: HashMap<u32, u32>,
    pub(super) field_nil: HashMap<(u32, usize), u32>,
}

/// Element name of a value: enum values are their constructor names (as in
/// the enum SAT lane), every other value a private element.
fn element(scan: &Scan, values: &Values, id: u32) -> Option<String> {
    let VNode::Ctor { sort, ctor, .. } = values.get(id)? else {
        return None;
    };
    match &scan.sorts[*sort as usize].shape {
        SortShape::Enum { ctors } => ctors.get(*ctor as usize).cloned(),
        _ => Some(format!("@dtfd!{id}")),
    }
}

/// Declaration-order constructor names of an admitted sort.
fn ctor_names(exec: &Executor, scan: &Scan, sort: u32) -> Vec<String> {
    match &scan.sorts[sort as usize].shape {
        SortShape::Enum { ctors } => ctors.clone(),
        SortShape::Record { ctor, .. } => vec![ctor.clone()],
        SortShape::List { .. } => exec
            .ctx
            .datatype_constructors(&scan.sorts[sort as usize].name)
            .map(<[String]>::to_vec)
            .unwrap_or_default(),
    }
}

impl Executor {
    /// Mint the ground constructor term of value `id` (memoized).
    fn dt_fd_mint(
        &mut self,
        scan: &Scan,
        values: &Values,
        id: u32,
        memo: &mut HashMap<u32, TermId>,
    ) -> Option<TermId> {
        if let Some(&t) = memo.get(&id) {
            return Some(t);
        }
        let VNode::Ctor { sort, ctor, args } = values.get(id)?.clone() else {
            return None;
        };
        let name = ctor_names(self, scan, sort).get(ctor as usize)?.clone();
        let t = if args.is_empty() {
            self.ctx.exact_datatype_member_info(&name)?.term?
        } else {
            let mut arg_terms = Vec::with_capacity(args.len());
            for a in args {
                match values.get(a)? {
                    VNode::Bool(b) => arg_terms.push(self.ctx.terms.mk_bool(*b)),
                    VNode::Ctor { .. } => arg_terms.push(self.dt_fd_mint(scan, values, a, memo)?),
                }
            }
            let sort_obj = scan.sorts[sort as usize].sort.clone();
            self.ctx
                .terms
                .mk_app(Symbol::named(name.as_str()), arg_terms, sort_obj)
        };
        memo.insert(id, t);
        Some(t)
    }

    /// Build the EUF-shaped export (see module docs) and the exact value
    /// pins of the declared constants and selector applications.
    pub(super) fn dt_fd_export(
        &mut self,
        scan: &Scan,
        acc: &Accepted,
    ) -> Option<(EufModel, Vec<TermId>)> {
        let mut euf = EufModel::default();
        let mut per_sort: HashMap<u32, Vec<u32>> = HashMap::default();
        for (&t, &(_, sort)) in &scan.nodes {
            let FieldSort::Dt(s) = sort else { continue };
            let v = *acc.env.get(&t)?;
            per_sort.entry(s).or_default().push(v);
            euf.term_values.insert(t, element(scan, &acc.values, v)?);
        }
        let mut memo: HashMap<u32, TermId> = HashMap::default();
        let roots: Vec<u32> = per_sort.values().flatten().copied().collect();
        for v in roots {
            // Minting is best effort: a value without a ground term keeps
            // only its element (the pipeline's gates still decide).
            let _ = self.dt_fd_mint(scan, &acc.values, v, &mut memo);
        }
        for (&v, &t) in &memo {
            if let Some(name) = element(scan, &acc.values, v) {
                euf.term_values.entry(t).or_insert(name);
            }
            if let Some(VNode::Ctor { sort, .. }) = acc.values.get(v) {
                per_sort.entry(*sort).or_default().push(v);
            }
        }
        for (s, mut ids) in per_sort {
            ids.sort_unstable();
            ids.dedup();
            let sort = &scan.sorts[s as usize];
            let mut elems: Vec<String> = match &sort.shape {
                SortShape::Enum { ctors } => ctors.clone(),
                _ => ids
                    .iter()
                    .filter_map(|&v| element(scan, &acc.values, v))
                    .collect(),
            };
            elems.sort();
            euf.sort_elements.insert(sort.name.clone(), elems);
        }
        let pins = self.dt_fd_pins(scan, acc, &memo);
        Some((euf, pins))
    }

    /// `(= t v)` for every datatype-sorted declared constant and selector
    /// application `t`, `v` the minted ground term of its value
    /// (#dt-fd-pin-roots). Construction otherwise gives a class that no
    /// collected constructor term forces a guessed default; the lane's
    /// values are exact, and these pins hand them over. A selector
    /// application is pinned too because a wrong-constructor selector's
    /// value is the lane's committed choice, not a function of its argument
    /// that construction could recompute.
    fn dt_fd_pins(
        &mut self,
        scan: &Scan,
        acc: &Accepted,
        memo: &HashMap<u32, TermId>,
    ) -> Vec<TermId> {
        let mut pins = Vec::new();
        for &t in &scan.order {
            let Some((node, FieldSort::Dt(_))) = scan.nodes.get(&t) else {
                continue;
            };
            if !matches!(node, Node::Const | Node::Sel { .. }) {
                continue;
            }
            let Some(&m) = acc.env.get(&t).and_then(|v| memo.get(v)) else {
                continue;
            };
            if m != t {
                pins.push(self.ctx.terms.mk_eq(t, m));
            }
        }
        pins
    }

    /// The confirmed model as one total structure for the value printers
    /// (`model/lane_ground_model.rs`): every valued constant, the committed
    /// wrong-constructor values, and the substitutions preprocessing made, so
    /// a constant it eliminated is valued through its definition.
    pub(super) fn dt_fd_ground_model(
        &self,
        scan: &Scan,
        acc: &Accepted,
    ) -> Option<LaneGroundModel> {
        let ground = |id: u32| ground_of(&acc.values, id, GROUND_DEPTH);
        let sorts = scan
            .sorts
            .iter()
            .enumerate()
            .map(|(i, s)| GroundSort {
                ctors: ctor_names(self, scan, i as u32),
                list: match s.shape {
                    SortShape::List {
                        cons_idx, rec_pos, ..
                    } => Some((cons_idx, rec_pos)),
                    _ => None,
                },
            })
            .collect();
        let sel_of = scan
            .sel_of
            .iter()
            .map(|(name, kind)| {
                let sel = match *kind {
                    SelKind::RecordField { sort, pos } => GroundSel::Record { sort, pos },
                    SelKind::ListRest { sort } => GroundSel::Rest { sort },
                    SelKind::ListField { sort, field } => GroundSel::Field { sort, field },
                };
                (name.clone(), sel)
            })
            .collect();
        let mut consts = HashMap::default();
        for (&t, (node, _)) in &scan.nodes {
            if matches!(node, Node::Const) {
                consts.insert(t, ground(*acc.env.get(&t)?)?);
            }
        }
        let rest_nil = acc
            .rest_nil
            .iter()
            .map(|(&s, &v)| Some((s, ground(v)?)))
            .collect::<Option<_>>()?;
        let field_nil = acc
            .field_nil
            .iter()
            .map(|(&k, &v)| Some((k, ground(v)?)))
            .collect::<Option<_>>()?;
        let substitutions = self
            .recorded_var_substitutions
            .iter()
            .filter(|(from, _)| !consts.contains_key(*from))
            .map(|(&from, &to)| (from, to))
            .collect();
        Some(LaneGroundModel {
            sorts,
            ctor_of: scan.ctor_of.clone(),
            sel_of,
            consts,
            rest_nil,
            field_nil,
            substitutions,
            foreign_wrong_ctor: Default::default(),
        })
    }
}

/// Nesting bound of a lane value converted for the printers.
const GROUND_DEPTH: u32 = 4096;

/// A lane value as a ground tree.
fn ground_of(values: &Values, id: u32, fuel: u32) -> Option<Ground> {
    if fuel == 0 {
        return None;
    }
    Some(match values.get(id)? {
        VNode::Bool(b) => Ground::Bool(*b),
        VNode::Ctor { sort, ctor, args } => Ground::Ctor {
            sort: *sort,
            ctor: *ctor as usize,
            args: args
                .iter()
                .map(|&a| ground_of(values, a, fuel - 1))
                .collect::<Option<Vec<_>>>()?,
        },
    })
}
