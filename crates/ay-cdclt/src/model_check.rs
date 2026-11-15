// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! An exact check of a `sat` answer, independent of the search (design P3:
//! the model gate is a final check, never a repair loop).
//!
//! Each formula is evaluated in exact rationals under the engine's model:
//! Boolean structure recursively, comparisons from the plug-ins' values of
//! their arithmetic leaves (never from the atoms' SAT values), and Boolean
//! variables from the SAT model. A leaf the plug-ins never saw is free, so it
//! takes 0 (Boolean: false) consistently everywhere it occurs.
//!
//! Uninterpreted applications take the engine's value for the application
//! (the arithmetic plug-in's, EUF's abstract element, or the predicate's SAT
//! value), and the check verifies that they form a function: two
//! applications of one symbol to equal argument values must have equal
//! values. Terms of an uninterpreted sort are equal iff EUF gave them the
//! same element.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{Constant, Sort, TermData, TermId, TermStore};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{Signed, Zero};

use crate::content::is_uf_app;
use crate::engine::Engine;

/// The verdict of [`Engine::check_model`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModelVerdict {
    /// Every formula evaluates to true.
    Satisfied,
    /// This formula evaluates to false: the answer must not be published.
    Violated(TermId),
    /// A construct the evaluator does not know, named.
    Unchecked(String),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Value {
    Bool(bool),
    Num(BigRational),
    /// An element of an uninterpreted sort, named by a value term.
    Elem(TermId),
}

impl Engine {
    /// Evaluate `formulas` under the last `sat` answer (see the module docs).
    /// `terms` is the store the check ran on.
    ///
    /// When internalization rewrote the assertions (a named term-level
    /// `ite`, an expanded `distinct`), the encoded assertions are evaluated
    /// first: they must hold too, and their applications (over the names)
    /// enter the function tables before the formulas' (over the `ite`s)
    /// look them up, so an application the engine never saw takes the value
    /// of the one it did see at the same argument values.
    pub fn check_model(&mut self, terms: &mut TermStore, formulas: &[TermId]) -> ModelVerdict {
        let internalized = std::mem::take(&mut self.internalized);
        let verdict = self.check_formulas(terms, &[internalized.as_slice(), formulas].concat());
        self.internalized = internalized;
        verdict
    }

    fn check_formulas(&mut self, terms: &mut TermStore, formulas: &[TermId]) -> ModelVerdict {
        let walk = collect(terms, formulas);
        let mut values: HashMap<TermId, Value> = HashMap::default();
        for leaf in walk.arith_leaves {
            let value = self
                .model_value(terms, leaf)
                .and_then(|v| numeral(terms, v))
                .unwrap_or_else(BigRational::zero);
            values.insert(leaf, Value::Num(value));
        }
        for leaf in walk.elem_leaves {
            let value = self.model_value(terms, leaf).unwrap_or(leaf);
            values.insert(leaf, Value::Elem(value));
        }
        let mut apps: HashMap<TermId, Value> = HashMap::default();
        for app in walk.uf_apps {
            let value = match terms.sort(app) {
                Sort::Bool => self.atom_value(app).map(Value::Bool),
                sort if is_arith(sort) => self
                    .model_value(terms, app)
                    .and_then(|v| numeral(terms, v))
                    .map(Value::Num),
                _ => self.model_value(terms, app).map(Value::Elem),
            };
            if let Some(value) = value {
                apps.insert(app, value);
            }
        }
        let mut eval = Evaluator {
            terms: &*terms,
            engine_bool: |term| self.atom_value(term),
            values,
            apps,
            table: HashMap::default(),
            not_a_function: None,
        };
        for &formula in formulas {
            match eval.eval(formula) {
                Ok(Value::Bool(true)) => {}
                Ok(_) => return ModelVerdict::Violated(formula),
                Err(reason) => return ModelVerdict::Unchecked(reason),
            }
        }
        match eval.not_a_function {
            Some(app) => ModelVerdict::Violated(app),
            None => ModelVerdict::Satisfied,
        }
    }
}

fn numeral(terms: &TermStore, term: TermId) -> Option<BigRational> {
    match terms.get(term) {
        TermData::Const(Constant::Rational(r)) => Some(r.0.clone()),
        TermData::Const(Constant::Int(i)) => Some(BigRational::from_integer(i.clone())),
        _ => None,
    }
}

fn is_arith(sort: &Sort) -> bool {
    matches!(sort, Sort::Int | Sort::Real)
}

/// Leaves and applications below the formulas.
struct Walk {
    /// Arithmetic variables and constants-by-declaration.
    arith_leaves: Vec<TermId>,
    /// Constants of uninterpreted sorts.
    elem_leaves: Vec<TermId>,
    /// Uninterpreted applications.
    uf_apps: Vec<TermId>,
}

fn collect(terms: &TermStore, roots: &[TermId]) -> Walk {
    let mut seen: HashMap<TermId, ()> = HashMap::default();
    let mut stack = roots.to_vec();
    let mut walk = Walk {
        arith_leaves: Vec::new(),
        elem_leaves: Vec::new(),
        uf_apps: Vec::new(),
    };
    while let Some(term) = stack.pop() {
        if seen.insert(term, ()).is_some() {
            continue;
        }
        let leaf = match terms.get(term) {
            TermData::Var(..) => true,
            TermData::App(_, args) => args.is_empty(),
            _ => false,
        };
        if leaf {
            match terms.sort(term) {
                sort if is_arith(sort) => walk.arith_leaves.push(term),
                Sort::Uninterpreted(_) => walk.elem_leaves.push(term),
                _ => {}
            }
            continue;
        }
        if is_uf_app(terms, term) {
            walk.uf_apps.push(term);
        }
        match terms.get(term) {
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Ite(c, t, e) => stack.extend([*c, *t, *e]),
            TermData::Not(inner) => stack.push(*inner),
            _ => {}
        }
    }
    walk
}

struct Evaluator<'a, F> {
    terms: &'a TermStore,
    engine_bool: F,
    values: HashMap<TermId, Value>,
    /// The engine's value of each uninterpreted application it knows.
    apps: HashMap<TermId, Value>,
    /// The function tables built so far: (symbol, argument values) -> value.
    table: HashMap<(String, Vec<Value>), Value>,
    /// An application whose engine value contradicts the table.
    not_a_function: Option<TermId>,
}

impl<F: Fn(TermId) -> Option<bool>> Evaluator<'_, F> {
    /// Post-order with an explicit stack: assertion DAGs can be deep.
    fn eval(&mut self, root: TermId) -> Result<Value, String> {
        let mut stack = vec![(root, false)];
        while let Some((term, expanded)) = stack.pop() {
            if self.values.contains_key(&term) {
                continue;
            }
            let children = children(self.terms.get(term));
            if !expanded && !children.is_empty() {
                stack.push((term, true));
                stack.extend(children.into_iter().map(|c| (c, false)));
                continue;
            }
            let value = self.node(term)?;
            self.values.insert(term, value);
        }
        self.values
            .get(&root)
            .cloned()
            .ok_or_else(|| "evaluation produced no value".to_string())
    }

    fn get(&self, term: TermId) -> Result<&Value, String> {
        self.values
            .get(&term)
            .ok_or_else(|| format!("no value for {term:?}"))
    }

    fn boolean(&self, term: TermId) -> Result<bool, String> {
        match self.get(term)? {
            Value::Bool(b) => Ok(*b),
            _ => Err("a non-Boolean where a Boolean was expected".to_string()),
        }
    }

    fn number(&self, term: TermId) -> Result<BigRational, String> {
        match self.get(term)? {
            Value::Num(n) => Ok(n.clone()),
            _ => Err("a non-number where a number was expected".to_string()),
        }
    }

    /// An uninterpreted application: the function table's value for its
    /// argument values, entered from the engine's value on first sight.
    fn application(&mut self, term: TermId, name: &str, args: &[TermId]) -> Result<Value, String> {
        let key_args = args
            .iter()
            .map(|&a| self.get(a).cloned())
            .collect::<Result<Vec<_>, _>>()?;
        let key = (name.to_string(), key_args);
        let engine = self.apps.get(&term).cloned();
        if let Some(value) = self.table.get(&key) {
            if engine.as_ref().is_some_and(|e| e != value) {
                self.not_a_function.get_or_insert(term);
            }
            return Ok(value.clone());
        }
        let value = match engine {
            Some(value) => value,
            None => match self.terms.sort(term) {
                Sort::Bool => Value::Bool(false),
                sort if is_arith(sort) => Value::Num(BigRational::zero()),
                _ => Value::Elem(term),
            },
        };
        self.table.insert(key, value.clone());
        Ok(value)
    }

    fn node(&mut self, term: TermId) -> Result<Value, String> {
        if let TermData::App(sym, args) = self.terms.get(term) {
            if is_uf_app(self.terms, term) {
                return self.application(term, sym.name(), args);
            }
        }
        match self.terms.get(term) {
            TermData::Const(Constant::Bool(b)) => Ok(Value::Bool(*b)),
            TermData::Const(c) => numeral(self.terms, term)
                .map(Value::Num)
                .ok_or_else(|| format!("constant {c:?}")),
            TermData::Var(..) if *self.terms.sort(term) == Sort::Bool => {
                Ok(Value::Bool((self.engine_bool)(term).unwrap_or(false)))
            }
            TermData::Not(inner) => Ok(Value::Bool(!self.boolean(*inner)?)),
            TermData::Ite(c, t, e) => {
                let chosen = if self.boolean(*c)? { *t } else { *e };
                Ok(self.get(chosen)?.clone())
            }
            TermData::App(sym, args) if args.is_empty() => match self.terms.sort(term) {
                Sort::Bool => Ok(Value::Bool((self.engine_bool)(term).unwrap_or(false))),
                _ => Err(format!("constant `{}`", sym.name())),
            },
            TermData::Var(..) => Err("a variable without a value".to_string()),
            TermData::App(sym, args) => self.app(sym.name(), args),
            other => Err(format!("{other:?}")),
        }
    }

    fn app(&self, op: &str, args: &[TermId]) -> Result<Value, String> {
        let bools = || {
            args.iter()
                .map(|&a| self.boolean(a))
                .collect::<Result<Vec<_>, _>>()
        };
        let nums = || {
            args.iter()
                .map(|&a| self.number(a))
                .collect::<Result<Vec<_>, _>>()
        };
        let value = match op {
            "and" => Value::Bool(bools()?.into_iter().all(|b| b)),
            "or" => Value::Bool(bools()?.into_iter().any(|b| b)),
            "xor" => Value::Bool(bools()?.into_iter().fold(false, |acc, b| acc ^ b)),
            "=>" => {
                let bs = bools()?;
                let (last, init) = bs.split_last().ok_or("empty =>")?;
                Value::Bool(init.iter().any(|b| !b) || *last)
            }
            "=" => {
                let vals: Vec<&Value> = args
                    .iter()
                    .map(|&a| self.get(a))
                    .collect::<Result<_, _>>()?;
                Value::Bool(vals.windows(2).all(|w| w[0] == w[1]))
            }
            "distinct" => {
                let vals: Vec<&Value> = args
                    .iter()
                    .map(|&a| self.get(a))
                    .collect::<Result<_, _>>()?;
                let all_distinct =
                    (0..vals.len()).all(|i| (i + 1..vals.len()).all(|j| vals[i] != vals[j]));
                Value::Bool(all_distinct)
            }
            "<=" | "<" | ">=" | ">" => {
                let ns = nums()?;
                let holds = ns.windows(2).all(|w| match op {
                    "<=" => w[0] <= w[1],
                    "<" => w[0] < w[1],
                    ">=" => w[0] >= w[1],
                    _ => w[0] > w[1],
                });
                Value::Bool(holds)
            }
            _ => Value::Num(arith(op, nums()?)?),
        };
        Ok(value)
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
