// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A published finite-domain lane model as ONE total structure, read by
//! `(get-value)`, `(eval)` and the printed selector tables
//! (#dt-fd-ground-model).
//!
//! An accepted lane model (`theories/euf/dt_finite`) is a genuine datatype
//! model of the lane's admitted signature: every declared constant the query
//! mentions has a ground value, and every selector is a total FUNCTION of its
//! argument's value — the field for the owning constructor, and for a list's
//! nil the one committed value `rest(nil)` / `field_j(nil)` (the lane's
//! decoder evaluates every wrong-constructor application through it). The
//! generic model, however, values terms one TermId at a time. A term the
//! query does not contain — a `(get-value)` tester, a selector over `nil`,
//! an authored subterm that preprocessing dropped, a constant preprocessing
//! substituted away — got either no value (`(error "... not available")`)
//! or a value chosen independently of the lane's, so the printed values were
//! not one model (E13 round-3 findings: `(get-value ((is-nil x)))` errored
//! after a lane `sat`; `(tl x)` and `(tl y)` printed different values with
//! `x = y = nil`).
//!
//! [`LaneGroundModel`] keeps the lane's model after publication, and
//! [`Executor::dt_fd_ground_value`] evaluates any term of the admitted
//! signature over it with the decoder's exact semantics: constants read their
//! lane values (a constant preprocessing eliminated reads the value of its
//! recorded substitution), constructors build, testers compare heads,
//! selectors project or read the committed wrong-constructor value, and `=` /
//! `distinct` compare ground values structurally (ground constructor trees
//! are equal exactly when they are the same value). A constant the lane never
//! valued, and a subterm that mentions nothing the lane values (an
//! arithmetic comparison, a record with an Int field, a sum sort
//! preprocessing dropped), read the other printers' value (`printed.rs`), so
//! a Boolean combination of lane and foreign terms still has a value.
//! Anything else declines, and the term takes the ordinary path unchanged.
//!
//! The structure is output state only: the lane installs it after the model
//! passed the validation pipeline and the independent gate, and it is
//! dropped with the model (`clear_dt_theory_model`, every verdict
//! invalidation). It decides no verdict.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::quote_symbol;
use ay_core::term::{Constant, TermData};
use ay_core::TermId;
use ay_frontend::DeclarationKind;

use super::Model;
use crate::executor::Executor;

mod printed;

/// Nesting bound of one evaluation (terms and substitution chains).
const MAX_DEPTH: u32 = 512;

thread_local! {
    /// Set while a constant the lane never valued is read from the other
    /// printers ([`GroundEval::leaf`]); they must not re-enter the lane model.
    static READING_PRINTED: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// A ground value of the lane signature.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub(in crate::executor) enum Ground {
    Bool(bool),
    /// Constructor `ctor` (declaration index) of sort `sort` (index into
    /// [`LaneGroundModel::sorts`]).
    Ctor {
        sort: u32,
        ctor: usize,
        args: Vec<Ground>,
    },
    /// A value of a datatype outside the lane signature (a sort the query
    /// never uses, e.g. a constructor term only `(get-value)` mentions):
    /// constructor `ctor` (internal name) applied to `args`. Constructor
    /// names are unique, so structural equality is value equality here too.
    Foreign {
        ctor: String,
        args: Vec<Ground>,
    },
    /// A value of a scalar sort (Int, Real, bit-vector, String) outside the
    /// lane signature, as the other printers print it, normalized
    /// ([`normalized`]). Those printers print each such value as one
    /// canonical literal, so text equality is value equality.
    Opaque(String),
}

/// What a selector symbol projects.
#[derive(Clone, Copy, Debug)]
pub(in crate::executor) enum GroundSel {
    /// Argument `pos` of the record constructor of `sort`.
    Record { sort: u32, pos: usize },
    /// The recursive field of the list sort `sort`.
    Rest { sort: u32 },
    /// Cell field `field` (index among the non-recursive cons fields).
    Field { sort: u32, field: usize },
}

/// One admitted sort.
#[derive(Clone, Debug)]
pub(in crate::executor) struct GroundSort {
    /// Constructor names in declaration order.
    pub(in crate::executor) ctors: Vec<String>,
    /// `(cons_idx, rec_pos)` of a list sort.
    pub(in crate::executor) list: Option<(usize, usize)>,
}

/// The published lane model (see the module docs).
#[derive(Clone, Debug, Default)]
pub(in crate::executor) struct LaneGroundModel {
    pub(in crate::executor) sorts: Vec<GroundSort>,
    pub(in crate::executor) ctor_of: HashMap<String, (u32, usize)>,
    pub(in crate::executor) sel_of: HashMap<String, GroundSel>,
    /// Value of every declared constant the lane valued.
    pub(in crate::executor) consts: HashMap<TermId, Ground>,
    /// `rest(nil)` per list sort.
    pub(in crate::executor) rest_nil: HashMap<u32, Ground>,
    /// `field_j(nil)` per (list sort, cell field).
    pub(in crate::executor) field_nil: HashMap<(u32, usize), Ground>,
    /// Constants preprocessing substituted away, with their definitions.
    pub(in crate::executor) substitutions: HashMap<TermId, TermId>,
    /// The value a selector takes on a value of a datatype outside the lane
    /// signature built by another constructor, once read (`printed.rs`):
    /// every later read of the same selector on the same value agrees.
    pub(in crate::executor) foreign_wrong_ctor:
        std::cell::RefCell<HashMap<(String, Ground), Option<Ground>>>,
}

/// Position of cell field `j` among the cons arguments.
fn cell_arg_pos(j: usize, rec_pos: usize) -> usize {
    if j < rec_pos {
        j
    } else {
        j + 1
    }
}

impl Executor {
    /// The printed value of `term` under the published lane model, or `None`
    /// when no lane model is published or `term` is outside what it values.
    /// `printed` is the model the other printers read: a declared constant
    /// the lane never valued (the query does not mention it) takes the value
    /// they print for it.
    pub(in crate::executor) fn dt_fd_ground_value(
        &self,
        printed: &Model,
        term: TermId,
    ) -> Option<String> {
        let lane = self.lane_ground_model.as_deref()?;
        if READING_PRINTED.with(std::cell::Cell::get) {
            // Inside a constant's printed-value read: those printers must
            // not come back here (they may read the constant's selectors).
            return None;
        }
        let mut eval = GroundEval {
            exec: self,
            lane,
            printed,
            memo: HashMap::default(),
        };
        let value = eval.eval(term, MAX_DEPTH)?;
        self.dt_fd_render(lane, &value)
    }

    /// `(selector, rendered nil, rendered value)` for every list selector of
    /// the published lane model: the wrong-constructor values it committed,
    /// which the printed selector tables must carry even where no term of
    /// the store applies the selector to nil.
    pub(in crate::executor) fn dt_fd_ground_wrong_ctor_cases(
        &self,
    ) -> Vec<(String, String, String)> {
        let Some(model) = self.lane_ground_model.as_deref() else {
            return Vec::new();
        };
        let mut cases = Vec::new();
        for (name, &sel) in &model.sel_of {
            let (sort, value) = match sel {
                GroundSel::Rest { sort } => (sort, model.rest_nil.get(&sort)),
                GroundSel::Field { sort, field } => (sort, model.field_nil.get(&(sort, field))),
                GroundSel::Record { .. } => continue,
            };
            let (Some(value), Some((cons_idx, _))) =
                (value, model.sorts.get(sort as usize).and_then(|s| s.list))
            else {
                continue;
            };
            let nil = Ground::Ctor {
                sort,
                ctor: 1 - cons_idx,
                args: Vec::new(),
            };
            if let (Some(arg), Some(value)) = (
                self.dt_fd_render(model, &nil),
                self.dt_fd_render(model, value),
            ) {
                cases.push((name.clone(), arg, value));
            }
        }
        cases.sort();
        cases
    }

    fn dt_fd_render(&self, model: &LaneGroundModel, value: &Ground) -> Option<String> {
        match value {
            Ground::Bool(b) => Some(b.to_string()),
            Ground::Ctor { sort, ctor, args } => {
                let name = model.sorts.get(*sort as usize)?.ctors.get(*ctor)?;
                let head = quote_symbol(self.ctx.output_symbol_name(name));
                if args.is_empty() {
                    return Some(head);
                }
                let parts = args
                    .iter()
                    .map(|a| self.dt_fd_render(model, a))
                    .collect::<Option<Vec<_>>>()?;
                Some(format!("({head} {})", parts.join(" ")))
            }
            Ground::Foreign { ctor, args } => {
                let head = quote_symbol(self.ctx.output_symbol_name(ctor));
                if args.is_empty() {
                    return Some(head);
                }
                let parts = args
                    .iter()
                    .map(|a| self.dt_fd_render(model, a))
                    .collect::<Option<Vec<_>>>()?;
                Some(format!("({head} {})", parts.join(" ")))
            }
            Ground::Opaque(text) => Some(text.clone()),
        }
    }
}

/// One evaluation over the published lane model.
struct GroundEval<'a> {
    exec: &'a Executor,
    lane: &'a LaneGroundModel,
    printed: &'a Model,
    memo: HashMap<TermId, Option<Ground>>,
}

impl GroundEval<'_> {
    fn eval(&mut self, t: TermId, fuel: u32) -> Option<Ground> {
        if let Some(v) = self.memo.get(&t) {
            return v.clone();
        }
        if fuel == 0 {
            return None;
        }
        let v = self
            .eval_inner(t, fuel - 1)
            .or_else(|| self.printed_value(t, fuel - 1));
        self.memo.insert(t, v.clone());
        v
    }

    fn eval_bool(&mut self, t: TermId, fuel: u32) -> Option<bool> {
        match self.eval(t, fuel)? {
            Ground::Bool(b) => Some(b),
            Ground::Ctor { .. } | Ground::Foreign { .. } | Ground::Opaque(_) => None,
        }
    }

    fn eval_inner(&mut self, t: TermId, fuel: u32) -> Option<Ground> {
        let exec = self.exec;
        match exec.ctx.terms.get(t) {
            TermData::Const(Constant::Bool(b)) => Some(Ground::Bool(*b)),
            TermData::Not(a) => Some(Ground::Bool(!self.eval_bool(*a, fuel)?)),
            TermData::Ite(c, a, b) => {
                let branch = if self.eval_bool(*c, fuel)? { *a } else { *b };
                self.eval(branch, fuel)
            }
            TermData::Var(name, _) => self.leaf(t, name, fuel),
            TermData::App(sym, args) if args.is_empty() => self.leaf(t, sym.name(), fuel),
            TermData::App(sym, args) => self.app(t, sym.name(), args, fuel),
            _ => None,
        }
    }

    fn app(&mut self, t: TermId, name: &str, args: &[TermId], fuel: u32) -> Option<Ground> {
        if matches!(name, "and" | "or") {
            // A known absorbing argument decides the connective even when
            // another argument has no value here.
            let absorbing = name == "or";
            let mut unknown = false;
            for &a in args {
                match self.eval_bool(a, fuel) {
                    Some(b) if b == absorbing => return Some(Ground::Bool(absorbing)),
                    Some(_) => {}
                    None => unknown = true,
                }
            }
            return (!unknown).then_some(Ground::Bool(!absorbing));
        }
        if matches!(name, "xor" | "=>") {
            let mut bools = Vec::with_capacity(args.len());
            for &a in args {
                bools.push(self.eval_bool(a, fuel)?);
            }
            let value = match name {
                "xor" => bools.iter().fold(false, |acc, &b| acc ^ b),
                _ => {
                    let (last, premises) = bools.split_last()?;
                    !premises.iter().all(|&b| b) || *last
                }
            };
            return Some(Ground::Bool(value));
        }
        if matches!(name, "=" | "distinct") && args.len() >= 2 {
            let mut vals = Vec::with_capacity(args.len());
            for &a in args {
                vals.push(self.eval(a, fuel)?);
            }
            let value = if name == "=" {
                vals.iter().all(|v| *v == vals[0])
            } else {
                (0..vals.len()).all(|i| (i + 1..vals.len()).all(|j| vals[i] != vals[j]))
            };
            return Some(Ground::Bool(value));
        }
        let kind = self
            .exec
            .ctx
            .exact_datatype_member_info(name)
            .map(|info| info.declaration_kind())?;
        match kind {
            DeclarationKind::DatatypeConstructor => {
                let mut fields = Vec::with_capacity(args.len());
                for &a in args {
                    fields.push(self.eval(a, fuel)?);
                }
                self.constructed(name, fields)
            }
            DeclarationKind::DatatypeSelector if args.len() == 1 => {
                let arg = self.eval(args[0], fuel)?;
                if let Ground::Foreign { ctor, args: fields } = &arg {
                    // Outside the lane signature: the owning constructor's
                    // field, else the one value this selector takes there.
                    let info = self.exec.ctx.constructor_selector_info(ctor)?;
                    return match info.iter().position(|(sel, _)| sel == name) {
                        Some(pos) => fields.get(pos).cloned(),
                        None => self.foreign_wrong_ctor(t, name, &arg),
                    };
                }
                let sel = *self.lane.sel_of.get(name)?;
                select(self.lane, sel, arg)
            }
            DeclarationKind::DatatypeTester if args.len() == 1 => {
                let tested = name.strip_prefix("is-")?;
                match self.eval(args[0], fuel)? {
                    Ground::Ctor {
                        sort: s, ctor: c, ..
                    } => {
                        let &(sort, ctor) = self.lane.ctor_of.get(tested)?;
                        (s == sort).then_some(Ground::Bool(c == ctor))
                    }
                    Ground::Foreign { ctor, .. } => Some(Ground::Bool(ctor == tested)),
                    Ground::Bool(_) | Ground::Opaque(_) => None,
                }
            }
            _ => None,
        }
    }

    /// A nullary leaf: a nullary constructor, a lane-valued constant, a
    /// constant preprocessing substituted away, or a constant the query does
    /// not mention (its printed value).
    fn leaf(&mut self, t: TermId, name: &str, fuel: u32) -> Option<Ground> {
        let kind = self
            .exec
            .ctx
            .exact_datatype_member_info(name)
            .map(|info| info.declaration_kind());
        if kind == Some(DeclarationKind::DatatypeConstructor) {
            return self.constructed(name, Vec::new());
        }
        if kind.is_some() {
            return None;
        }
        if let Some(v) = self.lane.consts.get(&t) {
            return Some(v.clone());
        }
        if let Some(&rhs) = self.lane.substitutions.get(&t) {
            return self.eval(rhs, fuel);
        }
        let printed = self.read_printed(t)?;
        self.parse(&printed)
    }

    /// The value constructor `name` (internal name) builds from `args`.
    fn constructed(&self, name: &str, args: Vec<Ground>) -> Option<Ground> {
        if let Some(&(sort, ctor)) = self.lane.ctor_of.get(name) {
            return Some(Ground::Ctor { sort, ctor, args });
        }
        self.exec.ctx.is_constructor(name)?;
        Some(Ground::Foreign {
            ctor: name.to_string(),
            args,
        })
    }

    /// The internal constructor name a printed head spells: a lane
    /// constructor by its surface name, else a constructor of that name.
    fn ctor_by_surface(&self, surface: &str) -> Option<String> {
        let mut found = None;
        for name in self.lane.ctor_of.keys() {
            if self.exec.ctx.output_symbol_name(name) == surface {
                if found.is_some() {
                    return None;
                }
                found = Some(name.clone());
            }
        }
        found.or_else(|| {
            self.exec
                .ctx
                .is_constructor(surface)
                .is_some()
                .then(|| surface.to_string())
        })
    }
}

/// A selector applied to a ground value: the field, or the committed
/// wrong-constructor value.
fn select(model: &LaneGroundModel, sel: GroundSel, arg: Ground) -> Option<Ground> {
    let Ground::Ctor { sort, ctor, args } = arg else {
        return None;
    };
    match sel {
        GroundSel::Record { sort: owner, pos } => {
            if owner != sort {
                return None;
            }
            args.get(pos).cloned()
        }
        GroundSel::Rest { sort: owner } | GroundSel::Field { sort: owner, .. } => {
            if owner != sort {
                return None;
            }
            let (cons_idx, rec_pos) = model.sorts.get(sort as usize)?.list?;
            let field = match sel {
                GroundSel::Field { field, .. } => Some(field),
                _ => None,
            };
            if ctor == cons_idx {
                let pos = field.map_or(rec_pos, |j| cell_arg_pos(j, rec_pos));
                return args.get(pos).cloned();
            }
            match field {
                None => model.rest_nil.get(&sort).cloned(),
                Some(j) => model.field_nil.get(&(sort, j)).cloned(),
            }
        }
    }
}
