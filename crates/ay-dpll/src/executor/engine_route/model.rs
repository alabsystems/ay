// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The kernel's `sat` answer in the executor's model channels.
//!
//! The kernel's values are read back over the formulas it was checked
//! against, in order (the window the kernel searched first, then the
//! authored window), bottom-up:
//! - leaves and the applications the kernel saw take its values (Boolean
//!   ones the SAT assignment's);
//! - interpreted operators are evaluated exactly;
//! - an application the kernel never saw (one over a term-level `ite` that
//!   the searched window names) takes the value its symbol's table already
//!   holds at the same argument values, and a fresh value when there is
//!   none.
//!
//! Every symbol must come out a function: two applications at one point
//! with two values refuse the model, and the lane decides the check.
//!
//! The executor receives what its lanes produce:
//! - an `EufModel` (when the formulas have uninterpreted content): one
//!   element `@S!k` per class of each uninterpreted sort (`term_values`,
//!   `sort_elements`), and one concrete table per uninterpreted symbol
//!   (`function_tables`, aligned with `function_table_terms`) whose atoms are
//!   spelled the way the executor's evaluator spells model atoms;
//! - an `LraModel` with every non-constant Real term, and an `LiaModel` with
//!   every non-constant Int term.
//!
//! Nothing here decides anything: the executor's model gates evaluate the
//! authored assertions under this model before a `sat` is published.

use ay_cdclt::Engine;
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};
use ay_euf::EufModel;
use ay_lia::LiaModel;
use ay_lra::LraModel;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{Signed, Zero};

use crate::executor_format::format_bigint;

/// A value in the kernel's model.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Val {
    Bool(bool),
    Num(BigRational),
    /// An element of an uninterpreted sort, named by the kernel's value term
    /// (or by the term itself when the kernel never valued it).
    Elem(TermId),
}

/// The kernel's model in the executor's channels.
pub(super) struct ExtractedModel {
    /// `None` when the formulas have no uninterpreted content.
    pub(super) euf: Option<EufModel>,
    pub(super) lra: LraModel,
    pub(super) lia: Option<LiaModel>,
}

/// Read the kernel's model of its last `sat` answer over `roots` (see the
/// module docs). `Err` names why the model cannot be handed over.
pub(super) fn extract(
    engine: &mut Engine,
    terms: &mut TermStore,
    roots: &[TermId],
) -> Result<ExtractedModel, String> {
    let mut reader = Reader {
        engine,
        values: HashMap::default(),
        order: Vec::new(),
        table: HashMap::default(),
        rows: Vec::new(),
    };
    for &root in roots {
        reader.eval(terms, root)?;
    }
    reader.into_model(terms)
}

/// Uninterpreted operator names the kernel treats as interpreted.
const INTERPRETED: [&str; 22] = [
    "=", "distinct", "not", "ite", "and", "or", "xor", "=>", "<=", "<", ">=", ">", "+", "-", "*",
    "/", "div", "mod", "abs", "to_int", "to_real", "is_int",
];

/// Whether `term` is an uninterpreted application (the kernel's registry,
/// `ay-cdclt` `content::is_uf_app`, over the sorts it covers). As there, a
/// user declaration's registered private identity (`__ay_overload_N`) is
/// uninterpreted; any other internal name is not.
fn is_uf_app(terms: &TermStore, term: TermId) -> bool {
    let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
        return false;
    };
    let name: &str = name;
    let internal = name.starts_with('@') || name.starts_with("__ay") || name.starts_with("!ay.");
    !args.is_empty()
        && !INTERPRETED.contains(&name)
        && (!internal || terms.is_declared_function(name))
}

fn numeral(terms: &TermStore, term: TermId) -> Option<BigRational> {
    match terms.get(term) {
        TermData::Const(Constant::Rational(r)) => Some(r.0.clone()),
        TermData::Const(Constant::Int(i)) => Some(BigRational::from_integer(i.clone())),
        TermData::App(sym, args) if sym.name() == "-" && args.len() == 1 => {
            numeral(terms, args[0]).map(|r| -r)
        }
        _ => None,
    }
}

/// A model atom as the executor's evaluator spells it
/// (`Executor::eval_value_to_model_atom`): an integer as a plain numeral
/// (`-7`), a fraction as `(/ n d)`.
fn number_atom(value: &BigRational) -> String {
    if value.is_integer() {
        value.numer().to_string()
    } else {
        format!("(/ {} {})", value.numer(), value.denom())
    }
}

struct Reader<'e> {
    engine: &'e mut Engine,
    values: HashMap<TermId, Val>,
    /// Every valued term, in evaluation order.
    order: Vec<TermId>,
    /// (symbol, argument values) -> value.
    table: HashMap<(String, Vec<Val>), Val>,
    /// The table's rows in the order they were entered, with their source
    /// application.
    rows: Vec<(String, Vec<Val>, TermId)>,
}

impl Reader<'_> {
    /// Post-order with an explicit stack: assertion DAGs can be deep.
    fn eval(&mut self, terms: &mut TermStore, root: TermId) -> Result<(), String> {
        let mut stack = vec![(root, false)];
        while let Some((term, expanded)) = stack.pop() {
            if self.values.contains_key(&term) {
                continue;
            }
            let children = children(terms.get(term));
            if !expanded && !children.is_empty() {
                stack.push((term, true));
                stack.extend(children.into_iter().map(|c| (c, false)));
                continue;
            }
            let value = self.node(terms, term)?;
            self.values.insert(term, value);
            self.order.push(term);
        }
        Ok(())
    }

    fn get(&self, term: TermId) -> Result<&Val, String> {
        self.values
            .get(&term)
            .ok_or_else(|| format!("no value for {term:?}"))
    }

    fn boolean(&self, term: TermId) -> Result<bool, String> {
        match self.get(term)? {
            Val::Bool(b) => Ok(*b),
            _ => Err("a non-Boolean where a Boolean was expected".to_string()),
        }
    }

    fn node(&mut self, terms: &mut TermStore, term: TermId) -> Result<Val, String> {
        match terms.get(term).clone() {
            TermData::Const(Constant::Bool(b)) => Ok(Val::Bool(b)),
            TermData::Const(Constant::Int(i)) => Ok(Val::Num(BigRational::from_integer(i))),
            TermData::Const(Constant::Rational(r)) => Ok(Val::Num(r.0)),
            TermData::Const(other) => Err(format!("constant {other:?}")),
            TermData::Var(..) => self.leaf(terms, term),
            TermData::App(_, args) if args.is_empty() => self.leaf(terms, term),
            TermData::App(sym, args) if is_uf_app(terms, term) => {
                self.application(terms, term, sym.name(), &args)
            }
            TermData::App(sym, args) => self.interpreted(sym.name(), &args),
            TermData::Not(inner) => Ok(Val::Bool(!self.boolean(inner)?)),
            TermData::Ite(c, t, e) => {
                let chosen = if self.boolean(c)? { t } else { e };
                self.get(chosen).cloned()
            }
            other => Err(format!("{other:?}")),
        }
    }

    /// The kernel's value of a term, if it gave one.
    fn kernel_value(&mut self, terms: &mut TermStore, term: TermId) -> Result<Option<Val>, String> {
        Ok(match terms.sort(term).clone() {
            Sort::Bool => self.engine.atom_value(term).map(Val::Bool),
            Sort::Int | Sort::Real => self
                .engine
                .model_value(terms, term)
                .and_then(|v| numeral(terms, v))
                .map(Val::Num),
            Sort::Uninterpreted(_) => self.engine.model_value(terms, term).map(Val::Elem),
            other => return Err(format!("a term of sort {other:?}")),
        })
    }

    /// A free leaf takes one fixed value everywhere (as in the kernel's own
    /// model check): false, 0, or an element of its own.
    fn leaf(&mut self, terms: &mut TermStore, term: TermId) -> Result<Val, String> {
        let value = self.kernel_value(terms, term)?;
        Ok(value.unwrap_or_else(|| fresh(terms.sort(term), term)))
    }

    fn application(
        &mut self,
        terms: &mut TermStore,
        term: TermId,
        name: &str,
        args: &[TermId],
    ) -> Result<Val, String> {
        let key_args = args
            .iter()
            .map(|&a| self.get(a).cloned())
            .collect::<Result<Vec<_>, _>>()?;
        let kernel = self.kernel_value(terms, term)?;
        let key = (name.to_string(), key_args);
        if let Some(value) = self.table.get(&key) {
            if kernel.as_ref().is_some_and(|k| k != value) {
                return Err(format!("`{name}` is not a function in the kernel's model"));
            }
            return Ok(value.clone());
        }
        let value = kernel.unwrap_or_else(|| fresh(terms.sort(term), term));
        self.rows.push((key.0.clone(), key.1.clone(), term));
        self.table.insert(key, value.clone());
        Ok(value)
    }

    fn interpreted(&self, op: &str, args: &[TermId]) -> Result<Val, String> {
        let vals = args
            .iter()
            .map(|&a| self.get(a))
            .collect::<Result<Vec<_>, _>>()?;
        let bools = || {
            vals.iter()
                .map(|v| match v {
                    Val::Bool(b) => Ok(*b),
                    _ => Err(format!("`{op}` over a non-Boolean")),
                })
                .collect::<Result<Vec<bool>, String>>()
        };
        let nums = || {
            vals.iter()
                .map(|v| match v {
                    Val::Num(n) => Ok(n.clone()),
                    _ => Err(format!("`{op}` over a non-number")),
                })
                .collect::<Result<Vec<BigRational>, String>>()
        };
        let value = match op {
            "and" => Val::Bool(bools()?.into_iter().all(|b| b)),
            "or" => Val::Bool(bools()?.into_iter().any(|b| b)),
            "xor" => Val::Bool(bools()?.into_iter().fold(false, |acc, b| acc ^ b)),
            "=>" => {
                let bs = bools()?;
                let (last, init) = bs.split_last().ok_or("empty =>")?;
                Val::Bool(init.iter().any(|b| !b) || *last)
            }
            "=" => Val::Bool(vals.windows(2).all(|w| w[0] == w[1])),
            "distinct" => {
                Val::Bool((0..vals.len()).all(|i| (i + 1..vals.len()).all(|j| vals[i] != vals[j])))
            }
            "<=" | "<" | ">=" | ">" => {
                let ns = nums()?;
                Val::Bool(ns.windows(2).all(|w| match op {
                    "<=" => w[0] <= w[1],
                    "<" => w[0] < w[1],
                    ">=" => w[0] >= w[1],
                    _ => w[0] > w[1],
                }))
            }
            _ => Val::Num(arith(op, nums()?)?),
        };
        Ok(value)
    }

    /// The executor's channels (see the module docs).
    fn into_model(self, terms: &TermStore) -> Result<ExtractedModel, String> {
        let mut euf = EufModel::default();
        let mut names: HashMap<TermId, String> = HashMap::default();
        let mut counters: HashMap<String, usize> = HashMap::default();
        let mut lra = LraModel {
            values: HashMap::default(),
        };
        let mut lia = LiaModel {
            values: HashMap::default(),
        };
        let mut uninterpreted = !self.rows.is_empty();
        for &term in &self.order {
            let atomic = atomic(terms, term);
            match (terms.sort(term), &self.values[&term]) {
                (Sort::Uninterpreted(sort), Val::Elem(elem)) => {
                    uninterpreted = true;
                    let name = names.entry(*elem).or_insert_with(|| {
                        let k = counters.entry(sort.clone()).or_insert(0);
                        let name = format!("@{sort}!{k}");
                        *k += 1;
                        euf.sort_elements
                            .entry(sort.clone())
                            .or_default()
                            .push(name.clone());
                        name
                    });
                    euf.term_values.insert(term, name.clone());
                }
                (Sort::Int, Val::Num(value)) if !is_constant(terms, term) => {
                    if !value.is_integer() {
                        return Err("a fractional value for an Int term".to_string());
                    }
                    let value = value.to_integer();
                    if atomic {
                        euf.int_values.insert(term, value.clone());
                        euf.term_values.insert(term, format_bigint(&value));
                    }
                    lia.values.insert(term, value);
                }
                (Sort::Real, Val::Num(value)) if !is_constant(terms, term) => {
                    if atomic {
                        euf.term_values.insert(term, number_atom(value));
                    }
                    lra.values.insert(term, value.clone());
                }
                (Sort::Bool, Val::Bool(value)) if is_uf_app(terms, term) => {
                    euf.term_values.insert(term, value.to_string());
                }
                _ => {}
            }
        }
        for (name, args, source) in &self.rows {
            let key = (name.clone(), args.clone());
            let TermData::App(_, arg_terms) = terms.get(*source) else {
                return Err("a table row without an application".to_string());
            };
            // A number is the placeholder `@?t` of a term `t` holding it, as
            // the lanes spell their rows: the printer evaluates `t` under the
            // whole model (and spells it as `(get-value)` does), the
            // evaluator resolves it through `term_values`.
            let atom = |value: &Val, holder: TermId, euf: &mut EufModel| match value {
                Val::Bool(b) => Ok(b.to_string()),
                Val::Num(n) => {
                    if matches!(terms.sort(holder), Sort::Int) {
                        euf.term_values
                            .entry(holder)
                            .or_insert_with(|| format_bigint(&n.to_integer()));
                    } else {
                        euf.term_values
                            .entry(holder)
                            .or_insert_with(|| number_atom(n));
                    }
                    Ok(format!("@?{}", holder.0))
                }
                Val::Elem(e) => names
                    .get(e)
                    .cloned()
                    .ok_or_else(|| "an element without a name".to_string()),
            };
            let row_args = args
                .iter()
                .zip(arg_terms)
                .map(|(value, &holder)| atom(value, holder, &mut euf))
                .collect::<Result<Vec<_>, _>>()?;
            let row_value = atom(&self.table[&key], *source, &mut euf)?;
            euf.function_tables
                .entry(name.clone())
                .or_default()
                .push((row_args, row_value));
            euf.function_table_terms
                .entry(name.clone())
                .or_default()
                .push(*source);
        }
        Ok(ExtractedModel {
            euf: uninterpreted.then_some(euf),
            lra,
            lia: (!lia.values.is_empty()).then_some(lia),
        })
    }
}

/// The fixed value of a term the kernel never valued.
fn fresh(sort: &Sort, term: TermId) -> Val {
    match sort {
        Sort::Bool => Val::Bool(false),
        Sort::Int | Sort::Real => Val::Num(BigRational::zero()),
        _ => Val::Elem(term),
    }
}

fn is_constant(terms: &TermStore, term: TermId) -> bool {
    matches!(terms.get(term), TermData::Const(_)) || numeral(terms, term).is_some()
}

/// A term whose value is not computed from its arguments by the
/// executor's evaluator: a leaf, an uninterpreted application, an `ite`.
fn atomic(terms: &TermStore, term: TermId) -> bool {
    match terms.get(term) {
        TermData::Var(..) | TermData::Ite(..) => true,
        TermData::App(_, args) => args.is_empty() || is_uf_app(terms, term),
        _ => false,
    }
}

fn children(data: &TermData) -> Vec<TermId> {
    match data {
        TermData::App(_, args) => args.clone(),
        TermData::Ite(c, t, e) => vec![*c, *t, *e],
        TermData::Not(inner) => vec![*inner],
        _ => Vec::new(),
    }
}

fn arith(op: &str, ns: Vec<BigRational>) -> Result<BigRational, String> {
    let mut it = ns.into_iter();
    let first = it
        .next()
        .ok_or_else(|| format!("`{op}` without arguments"))?;
    match op {
        "+" => Ok(it.fold(first, |acc, n| acc + n)),
        "*" => Ok(it.fold(first, |acc, n| acc * n)),
        "-" => {
            let rest: Vec<BigRational> = it.collect();
            if rest.is_empty() {
                Ok(-first)
            } else {
                Ok(rest.into_iter().fold(first, |acc, n| acc - n))
            }
        }
        "/" => it.try_fold(first, |acc, n| {
            if n.is_zero() {
                Err("division by zero".to_string())
            } else {
                Ok(acc / n)
            }
        }),
        "to_real" => Ok(first),
        "to_int" => Ok(BigRational::from_integer(first.floor().to_integer())),
        "abs" => Ok(first.abs()),
        "div" | "mod" => {
            let divisor = it
                .next()
                .ok_or_else(|| format!("`{op}` needs two arguments"))?;
            int_div_mod(op, &first, &divisor)
        }
        other => Err(format!("operator `{other}`")),
    }
}

/// SMT-LIB integer `div` / `mod`: `a = b·q + r` with `0 ≤ r < |b|`.
fn int_div_mod(op: &str, a: &BigRational, b: &BigRational) -> Result<BigRational, String> {
    if b.is_zero() || !a.is_integer() || !b.is_integer() {
        return Err(format!("`{op}` by zero or on a non-integer"));
    }
    let (a, b): (BigInt, BigInt) = (a.to_integer(), b.to_integer());
    let mut q = &a / &b;
    let mut r = &a - &b * &q;
    if r.is_negative() {
        if b.is_positive() {
            q -= 1;
            r += &b;
        } else {
            q += 1;
            r -= &b;
        }
    }
    Ok(BigRational::from_integer(if op == "div" { q } else { r }))
}

/// Whether the formulas have content the hub serves: an uninterpreted
/// application or a term of an uninterpreted sort. The kernel names
/// term-level `ite`s exactly then; the route names them first, so the
/// applications the kernel values are terms of the window it was given.
pub(super) fn has_hub_content(terms: &TermStore, roots: &[TermId]) -> bool {
    let mut seen: HashSet<TermId> = HashSet::default();
    let mut stack: Vec<TermId> = roots.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if is_uf_app(terms, term) || terms.sort(term).is_uninterpreted() {
            return true;
        }
        stack.extend(children(terms.get(term)));
    }
    false
}
