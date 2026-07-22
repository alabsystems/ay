// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The fresh, pure, total recursive evaluator.
//!
//! `Result<ModelValue, String>` is the internal evaluation type: `Ok(v)` is a
//! computed value and `Err(reason)` means *unevaluable* (which the public API
//! surfaces as [`EvalOutcome::Unevaluable`]). Nothing here panics or unwraps on
//! malformed/under-specified input — every such case returns `Err`.

use std::cell::RefCell;
use std::collections::HashSet;

use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};
use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{Signed, Zero};

use crate::{
    array_select, bitvec, seq, value_eq, ArrayValue, EvalOutcome, ModelValue, ModelView,
    MAX_EVAL_DEPTH,
};

/// One entry of the per-evaluator uninterpreted-function graph: a function
/// name, the VALUES its arguments evaluated to, and the single result value
/// adopted for that argument-value key. See [`Evaluator::eval_uninterpreted_app`].
type UfGraphEntry = (String, Vec<ModelValue>, ModelValue);

/// One entry of the per-evaluator array-`select` graph: the array-expression
/// TERM being read, the index VALUE it was read at, and the single element value
/// adopted for that `(array-term, index-value)` key. See
/// [`Evaluator::eval_select_via_model`].
type SelectGraphEntry = (TermId, ModelValue, ModelValue);

/// Restores the local lambda-binding stack on every exit, including unwinding.
///
/// The evaluator is intentionally reusable across all assertions in one gate
/// pass, so a beta-reduction binding must never leak into a later assertion.
struct LocalBindingGuard<'a> {
    bindings: &'a RefCell<Vec<(TermId, ModelValue)>>,
    restore_len: usize,
}

impl Drop for LocalBindingGuard<'_> {
    fn drop(&mut self) {
        self.bindings.borrow_mut().truncate(self.restore_len);
    }
}

/// A fresh evaluator bound to a term store and a model view.
pub struct Evaluator<'a> {
    terms: &'a TermStore,
    model: &'a dyn ModelView,
    /// Per-evaluator memo of SUCCESSFULLY computed term values
    /// (#gate-eval-memo): `term -> (value, deepest entry depth at which the
    /// evaluation succeeded)`. The assertions the gate re-checks are shared
    /// DAGs (common guard prefixes, let-shared subterms recur across dozens of
    /// assertions), and `eval` is a plain structural recursion, so without a
    /// memo each shared subterm is re-walked once per occurrence.
    ///
    /// EXACT-BEHAVIOR-PRESERVING, argued in two parts:
    ///
    /// 1. VALUE STABILITY. For a fixed model view, re-evaluating a term always
    ///    yields the value of its first evaluation: every node is a pure
    ///    function of its children's values except UF applications and
    ///    unresolved array reads, whose first evaluation ADOPTS a value into
    ///    `uf_graph`/`select_graph` keyed by argument values — entries are
    ///    never removed or overwritten, so a re-walk finds the identical
    ///    adopted value (and adds nothing: the first walk already inserted
    ///    every key along the value path, and the deterministic short-circuit
    ///    order revisits exactly that path). Returning the memoized value is
    ///    therefore bit-identical to a re-walk, including graph side effects.
    ///
    /// 2. DEPTH-BUDGET GUARD. A success memoized at entry depth `d` proves the
    ///    subtree evaluates within `MAX_EVAL_DEPTH` when started at depth `d`,
    ///    hence at any shallower depth too — the memo is only consulted when
    ///    `current depth <= d`, so a memo hit can never return `Ok` where a
    ///    fresh walk would have failed the depth limit (and vice versa).
    ///
    /// `Err` results are NEVER memoized: an `Err` can be depth-dependent
    /// (recursion limit) or cycle-guard-dependent (an in-flight array/datatype
    /// leaf resolution in the view), so it must be recomputed each time —
    /// which also keeps `CannotConfirm` reason strings identical.
    memo: RefCell<ay_core::kani_compat::DetHashMap<TermId, (ModelValue, usize)>>,
    /// Value-keyed interpretation the gate builds for uninterpreted functions
    /// as it evaluates. An uninterpreted function is single-valued, so two
    /// applications whose ARGUMENTS evaluate to equal values must return the
    /// same value; this graph enforces that (first application to reach a given
    /// `(name, arg-values)` key fixes the value for the whole evaluation). It
    /// is what lets the gate catch a model that collapses two congruent
    /// applications' arguments to the same value while pinning them to
    /// different results — the exact QF_UFLIA / array-select wrong-model class.
    uf_graph: RefCell<Vec<UfGraphEntry>>,
    /// Value-keyed interpretation the gate builds for array `select` reads whose
    /// array operand it could not resolve to a concrete `(default, finite-store)`
    /// value (a partial/unreconstructable array leaf). `select` over an array is
    /// a single-valued function of the index, so two reads of the SAME array term
    /// at index values that evaluate equal must denote the same element; this
    /// graph enforces that (first read to reach a given `(array-term,
    /// index-value)` key fixes the element for the whole evaluation). It is the
    /// array analogue of `uf_graph`, and is what lets the gate expose — rather
    /// than honour — an array model that pins two coincident reads to different
    /// values, closing the array-`select` wrong-model class even when the full
    /// array cannot be reconstructed.
    select_graph: RefCell<Vec<SelectGraphEntry>>,
    /// Scoped values for bound variables while beta-reducing a `lambda-array`
    /// read. The most recent binding wins, so nested lambdas and shadowing are
    /// handled naturally. The term-value memo and model-backed application
    /// fallbacks are explicitly bypassed for terms that depend on an active
    /// binding because neither per-TermId cache is indexed by a lambda
    /// environment. Binder-independent terms remain valid model observations
    /// inside an unrelated lambda body.
    local_bindings: RefCell<Vec<(TermId, ModelValue)>>,
}

impl<'a> Evaluator<'a> {
    /// Create an evaluator over `terms`, reading leaf values from `model`.
    #[must_use]
    pub fn new(terms: &'a TermStore, model: &'a dyn ModelView) -> Self {
        Self {
            terms,
            model,
            uf_graph: RefCell::new(Vec::new()),
            select_graph: RefCell::new(Vec::new()),
            local_bindings: RefCell::new(Vec::new()),
            memo: RefCell::new(ay_core::kani_compat::DetHashMap::default()),
        }
    }

    /// Evaluate `term` under the model, surfacing the outcome.
    #[must_use]
    pub fn evaluate(&self, term: TermId) -> EvalOutcome {
        match self.eval(term, 0) {
            Ok(v) => EvalOutcome::Value(v),
            Err(reason) => EvalOutcome::Unevaluable(reason),
        }
    }

    /// Core recursive evaluation. `depth` is the current term's depth; children
    /// are evaluated at `depth + 1`. Exceeding [`MAX_EVAL_DEPTH`] fails closed.
    ///
    /// Memoized over the shared-DAG assertions (see the `memo` field for the
    /// exact-behavior-preservation argument): a hit is taken only when the
    /// stored success depth is at least the current depth, and only `Ok`
    /// results are stored.
    fn eval(&self, term: TermId, depth: usize) -> Result<ModelValue, String> {
        // Constants are cheaper to recompute than to cache (their evaluation
        // is one clone either way). A term depending on an active lambda
        // binding can denote a different value in each beta environment, so a
        // TermId-only memo entry would be an unsound cross-instance reuse.
        if matches!(self.terms.get(term), TermData::Const(_))
            || self.term_depends_on_local_binding(term)
        {
            return self.eval_uncached(term, depth);
        }
        if let Some((v, d)) = self.memo.borrow().get(&term) {
            if depth <= *d {
                return Ok(v.clone());
            }
        }
        let result = self.eval_uncached(term, depth);
        if let Ok(v) = &result {
            let mut memo = self.memo.borrow_mut();
            match memo.get(&term) {
                // Keep the entry with the DEEPEST success depth (the stronger
                // depth-budget guarantee).
                Some((_, d)) if *d >= depth => {}
                _ => {
                    memo.insert(term, (v.clone(), depth));
                }
            }
        }
        result
    }

    /// Uncached body of [`Self::eval`]; recursive calls go back through the
    /// memoized wrapper so shared subterms are computed once.
    fn eval_uncached(&self, term: TermId, depth: usize) -> Result<ModelValue, String> {
        if depth > MAX_EVAL_DEPTH {
            return Err(format!("recursion depth limit {MAX_EVAL_DEPTH} exceeded"));
        }
        match self.terms.get(term) {
            TermData::Const(c) => Self::eval_const(c),
            TermData::Var(name, _) => self
                .local_binding(term)
                .or_else(|| self.model.leaf_value(term))
                // A NULLARY-constructor constant (`zero`, `null`, ... — lowered
                // to a bare `Var` whose name is the constructor) denotes exactly
                // that constructor value in EVERY model; resolve it structurally
                // so an unpinned occurrence inside a constructor tree never
                // makes an otherwise-decidable assertion `Unevaluable`
                // (#mv-gate-reads-printed-dt).
                .or_else(|| {
                    let dt = self.dt_of_sort(&self.terms.sort(term).clone())?;
                    let ctor = dt
                        .constructors
                        .iter()
                        .find(|c| c.name == *name && c.fields.is_empty())?;
                    Some(ModelValue::Datatype {
                        ctor: ctor.name.clone(),
                        args: Vec::new(),
                    })
                })
                .ok_or_else(|| "model does not pin this leaf".to_string()),
            TermData::Not(inner) => Ok(ModelValue::Bool(!self.eval_bool(*inner, depth + 1)?)),
            TermData::Ite(c, t, e) => {
                if self.eval_bool(*c, depth + 1)? {
                    self.eval(*t, depth + 1)
                } else {
                    self.eval(*e, depth + 1)
                }
            }
            TermData::App(sym, args) => match sym {
                Symbol::Named(name) => self.eval_named(term, name, args, depth),
                Symbol::Indexed(name, indices) => {
                    let vals = self.eval_all(args, depth)?;
                    bitvec::eval_indexed(name, indices, &vals)
                }
                _ => Err("unsupported symbol kind".to_string()),
            },
            // A `let` should have been expanded before reaching the gate. An
            // empty binding list is harmless to descend into; a non-empty one
            // binds names we cannot faithfully resolve ⇒ fail closed.
            TermData::Let(bindings, body) => {
                if bindings.is_empty() {
                    self.eval(*body, depth + 1)
                } else {
                    Err("unexpanded let binding".to_string())
                }
            }
            TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => {
                Err("quantifier is not evaluable by the gate".to_string())
            }
            _ => Err("unsupported term kind".to_string()),
        }
    }

    fn eval_bool(&self, term: TermId, depth: usize) -> Result<bool, String> {
        match self.eval(term, depth)? {
            ModelValue::Bool(b) => Ok(b),
            _ => Err("expected a boolean value".to_string()),
        }
    }

    fn eval_all(&self, args: &[TermId], depth: usize) -> Result<Vec<ModelValue>, String> {
        args.iter().map(|&a| self.eval(a, depth + 1)).collect()
    }

    fn eval_const(c: &Constant) -> Result<ModelValue, String> {
        match c {
            Constant::Bool(b) => Ok(ModelValue::Bool(*b)),
            Constant::Int(n) => Ok(ModelValue::Int(n.clone())),
            Constant::Rational(r) => Ok(ModelValue::Real(r.0.clone())),
            Constant::BitVec { value, width } => Ok(ModelValue::bitvec(value.clone(), *width)),
            Constant::String(s) => Ok(ModelValue::Str(s.clone())),
            _ => Err("unsupported constant kind".to_string()),
        }
    }

    // ----- application dispatch -------------------------------------------

    fn eval_named(
        &self,
        term: TermId,
        name: &str,
        args: &[TermId],
        depth: usize,
    ) -> Result<ModelValue, String> {
        match name {
            // Core boolean connectives (short-circuiting where SMT-LIB allows).
            "and" => self.eval_and(args, depth),
            "or" => self.eval_or(args, depth),
            "=>" => self.eval_implies(args, depth),
            "xor" => self.eval_xor(args, depth),
            "not" => {
                let [a] = exactly(args)?;
                Ok(ModelValue::Bool(!self.eval_bool(a, depth + 1)?))
            }
            "ite" | "if" => {
                let [c, t, e] = exactly(args)?;
                if self.eval_bool(c, depth + 1)? {
                    self.eval(t, depth + 1)
                } else {
                    self.eval(e, depth + 1)
                }
            }
            "=" => self.eval_eq(args, depth),
            "distinct" => self.eval_distinct(args, depth),

            // Arithmetic (Int/Real).
            "+" | "-" | "*" | "/" | "div" | "mod" | "abs" | "to_real" | "to_int" | "is_int"
            | "<" | "<=" | ">" | ">=" => self.eval_arith(term, name, args, depth),

            // Arrays.
            "select" | "store" | "const-array" | "lambda-array" | "default" => {
                self.eval_array(term, name, args, depth)
            }

            // Strings (minimal: ++, len, at; `=` handled above generically).
            "str.++" | "str.len" | "str.at" => self.eval_string(name, args, depth),

            _ if is_bv_named(name) => {
                let vals = self.eval_all(args, depth)?;
                bitvec::eval_named(name, &vals)
            }
            _ if name.starts_with("seq.") => {
                let vals = self.eval_all(args, depth)?;
                seq::eval(name, &vals)
            }

            // Datatypes (constructor / selector / tester), else an
            // uninterpreted function: apply the model's value-keyed
            // interpretation (fail closed if it cannot be built).
            _ => match self.eval_datatype(term, name, args, depth) {
                Ok(v) => Ok(v),
                Err(dt_err) => self.eval_uninterpreted_app(term, name, args, depth, dt_err),
            },
        }
    }

    /// Evaluate an uninterpreted-function application `(name arg0 ...)` against
    /// the model, keyed by the argument VALUES (not the argument terms).
    ///
    /// The gate evaluates the arguments itself (independently, with exact
    /// arithmetic), then treats the application as a single-valued function of
    /// those argument values: the FIRST application to reach a given
    /// `(name, arg-values)` key fixes the value for every later application with
    /// the same key. The representative value is the model's committed
    /// per-application value ([`ModelView::uf_app_value`]).
    ///
    /// This is what catches a model that collapses two congruent applications'
    /// arguments to the same value while pinning them to different results
    /// (e.g. `i0 = 0` makes `f(3*i0)` and `f(i0)` both `f(0)`, so a strict
    /// inequality between them cannot hold): both applications resolve through
    /// the same graph entry, so the inequality evaluates to `false` and the
    /// gate refutes the witness. Enforcing single-valuedness by argument VALUE
    /// (rather than trusting the per-application pins, which are exactly what is
    /// inconsistent in the wrong model) is the whole point.
    ///
    /// If the model does not pin the application, the result is `Unevaluable`
    /// (`dt_err` is surfaced) — fail closed, never assumed.
    fn eval_uninterpreted_app(
        &self,
        term: TermId,
        name: &str,
        args: &[TermId],
        depth: usize,
        dt_err: String,
    ) -> Result<ModelValue, String> {
        // Evaluate the arguments ourselves. If any argument is unevaluable, the
        // application is unevaluable (fail closed).
        let arg_vals = self.eval_all(args, depth)?;
        // Consult the value-keyed graph: same function, argument values all
        // equal ⇒ same result.
        {
            let graph = self.uf_graph.borrow();
            for (f, keys, val) in graph.iter() {
                if f == name
                    && keys.len() == arg_vals.len()
                    && keys
                        .iter()
                        .zip(arg_vals.iter())
                        .all(|(a, b)| value_eq(a, b).unwrap_or(false))
                {
                    return Ok(val.clone());
                }
            }
        }
        // A committed value is keyed only by the application TermId. The same
        // body application can be evaluated under several lambda bindings, so
        // consulting that non-contextual pin here could fabricate a value for
        // the wrong beta instance. A previously established value-keyed graph
        // entry above remains sound; only adopting this term's ambient pin is
        // prohibited.
        if self.term_depends_on_local_binding(term) {
            return Err("model-backed context-dependent application is unsupported".to_string());
        }
        // First time this key is seen: adopt the model's committed
        // per-application value as the representative. A model that does not pin
        // the application leaves the gate unable to confirm (fail closed).
        let val = self.model.uf_app_value(term).ok_or(dt_err)?;
        self.uf_graph
            .borrow_mut()
            .push((name.to_string(), arg_vals, val.clone()));
        Ok(val)
    }

    // ----- boolean connectives --------------------------------------------

    fn eval_and(&self, args: &[TermId], depth: usize) -> Result<ModelValue, String> {
        // `and` is false if ANY conjunct is false (even if others are
        // unevaluable); true only if ALL are true.
        let mut pending: Option<String> = None;
        for &a in args {
            match self.eval(a, depth + 1) {
                Ok(ModelValue::Bool(false)) => return Ok(ModelValue::Bool(false)),
                Ok(ModelValue::Bool(true)) => {}
                Ok(_) => return Err("non-boolean argument to and".to_string()),
                Err(e) => pending = Some(e),
            }
        }
        match pending {
            Some(e) => Err(e),
            None => Ok(ModelValue::Bool(true)),
        }
    }

    fn eval_or(&self, args: &[TermId], depth: usize) -> Result<ModelValue, String> {
        // `or` is true if ANY disjunct is true; false only if ALL are false.
        let mut pending: Option<String> = None;
        for &a in args {
            match self.eval(a, depth + 1) {
                Ok(ModelValue::Bool(true)) => return Ok(ModelValue::Bool(true)),
                Ok(ModelValue::Bool(false)) => {}
                Ok(_) => return Err("non-boolean argument to or".to_string()),
                Err(e) => pending = Some(e),
            }
        }
        match pending {
            Some(e) => Err(e),
            None => Ok(ModelValue::Bool(false)),
        }
    }

    fn eval_implies(&self, args: &[TermId], depth: usize) -> Result<ModelValue, String> {
        // (=> a1 ... an) = (or (not a1) ... (not a_{n-1}) a_n).
        if args.len() < 2 {
            return Err("=> needs at least two arguments".to_string());
        }
        let (last, init) = args.split_last().expect("len >= 2");
        let mut pending: Option<String> = None;
        for &a in init {
            match self.eval(a, depth + 1) {
                // A false antecedent makes the implication true.
                Ok(ModelValue::Bool(false)) => return Ok(ModelValue::Bool(true)),
                Ok(ModelValue::Bool(true)) => {}
                Ok(_) => return Err("non-boolean antecedent in =>".to_string()),
                Err(e) => pending = Some(e),
            }
        }
        match self.eval(*last, depth + 1) {
            Ok(ModelValue::Bool(true)) => Ok(ModelValue::Bool(true)),
            Ok(ModelValue::Bool(false)) => match pending {
                Some(e) => Err(e),
                None => Ok(ModelValue::Bool(false)),
            },
            Ok(_) => Err("non-boolean consequent in =>".to_string()),
            Err(e) => Err(e),
        }
    }

    fn eval_xor(&self, args: &[TermId], depth: usize) -> Result<ModelValue, String> {
        let mut acc = false;
        for &a in args {
            acc ^= self.eval_bool(a, depth + 1)?;
        }
        Ok(ModelValue::Bool(acc))
    }

    fn eval_eq(&self, args: &[TermId], depth: usize) -> Result<ModelValue, String> {
        if args.len() < 2 {
            return Err("= needs at least two arguments".to_string());
        }
        // Sound congruence shortcut (closes S1): two applications of the SAME
        // function symbol whose argument VALUES are all equal denote the same
        // value, so the equality holds — even when the function is uninterpreted
        // and cannot itself be evaluated. This lets the gate catch a model that
        // violates congruence, e.g. `(= (f (store a i v)) (f a))` when
        // `store(a,i,v)` and `a` evaluate to the same array. It only ever proves
        // the equality TRUE (equal args ⇒ equal results); it never proves an
        // inequality, so unequal/unevaluable args fall through to value comparison
        // below — preserving the prior behaviour on every other shape.
        if (1..args.len()).all(|k| self.congruent_equal(args[0], args[k], depth)) {
            return Ok(ModelValue::Bool(true));
        }
        let vals = self.eval_all(args, depth)?;
        for v in &vals[1..] {
            if !value_eq(&vals[0], v)? {
                return Ok(ModelValue::Bool(false));
            }
        }
        Ok(ModelValue::Bool(true))
    }

    /// Sound congruence test: are `lhs` and `rhs` provably equal because they are
    /// applications of the SAME named function symbol whose corresponding argument
    /// VALUES are all equal? Returns `true` only when congruence PROVES equality
    /// (also the reflexive `lhs == rhs`); `false` means "cannot conclude via
    /// congruence" (the caller falls back to direct value comparison). It never
    /// concludes inequality, so a `false` here can never turn a real equality into a
    /// wrong `false`. Unevaluable arguments conservatively yield `false`.
    fn congruent_equal(&self, lhs: TermId, rhs: TermId, depth: usize) -> bool {
        if lhs == rhs {
            return true;
        }
        if depth > MAX_EVAL_DEPTH {
            return false;
        }
        match (self.terms.get(lhs), self.terms.get(rhs)) {
            (TermData::App(Symbol::Named(fl), al), TermData::App(Symbol::Named(fr), ar)) => {
                if fl != fr || al.len() != ar.len() || al.is_empty() {
                    return false;
                }
                al.iter().zip(ar.iter()).all(|(&x, &y)| {
                    matches!(
                        (self.eval(x, depth + 1), self.eval(y, depth + 1)),
                        (Ok(vx), Ok(vy)) if value_eq(&vx, &vy).unwrap_or(false)
                    )
                })
            }
            _ => false,
        }
    }

    fn eval_distinct(&self, args: &[TermId], depth: usize) -> Result<ModelValue, String> {
        let vals = self.eval_all(args, depth)?;
        for i in 0..vals.len() {
            for j in (i + 1)..vals.len() {
                if value_eq(&vals[i], &vals[j])? {
                    return Ok(ModelValue::Bool(false));
                }
            }
        }
        Ok(ModelValue::Bool(true))
    }

    // ----- arithmetic ------------------------------------------------------

    fn eval_arith(
        &self,
        term: TermId,
        name: &str,
        args: &[TermId],
        depth: usize,
    ) -> Result<ModelValue, String> {
        let vals = self.eval_all(args, depth)?;
        let sort = self.terms.sort(term);
        match name {
            "+" => {
                let mut acc = BigRational::zero();
                for v in &vals {
                    acc += as_rational(v)?;
                }
                wrap_numeric(acc, sort)
            }
            "*" => {
                let mut acc = BigRational::from(BigInt::from(1));
                for v in &vals {
                    acc *= as_rational(v)?;
                }
                wrap_numeric(acc, sort)
            }
            "-" => {
                if vals.is_empty() {
                    return Err("- needs at least one argument".to_string());
                }
                let mut acc = as_rational(&vals[0])?;
                if vals.len() == 1 {
                    acc = -acc;
                } else {
                    for v in &vals[1..] {
                        acc -= as_rational(v)?;
                    }
                }
                wrap_numeric(acc, sort)
            }
            "/" => {
                if vals.is_empty() {
                    return Err("/ needs at least one argument".to_string());
                }
                let mut acc = as_rational(&vals[0])?;
                for v in &vals[1..] {
                    let d = as_rational(v)?;
                    if d.is_zero() {
                        return Err("real division by zero (under-specified)".to_string());
                    }
                    acc /= d;
                }
                // Result sort of `/` is Real.
                Ok(ModelValue::Real(acc))
            }
            "div" => {
                let (a, b) = (as_integer(&vals[0])?, as_integer(arg_v(&vals, 1)?)?);
                let (q, _) = euclid(&a, &b)
                    .ok_or_else(|| "integer div by zero (under-specified)".to_string())?;
                Ok(ModelValue::Int(q))
            }
            "mod" => {
                let (a, b) = (as_integer(&vals[0])?, as_integer(arg_v(&vals, 1)?)?);
                let (_, r) = euclid(&a, &b)
                    .ok_or_else(|| "integer mod by zero (under-specified)".to_string())?;
                Ok(ModelValue::Int(r))
            }
            "abs" => {
                let r = as_rational(&vals[0])?;
                wrap_numeric(r.abs(), sort)
            }
            "to_real" => Ok(ModelValue::Real(as_rational(&vals[0])?)),
            "to_int" => {
                let r = as_rational(&vals[0])?;
                Ok(ModelValue::Int(r.floor().to_integer()))
            }
            "is_int" => {
                let r = as_rational(&vals[0])?;
                Ok(ModelValue::Bool(r.is_integer()))
            }
            "<" | "<=" | ">" | ">=" => {
                if vals.len() < 2 {
                    return Err("comparison needs at least two arguments".to_string());
                }
                let rats: Vec<BigRational> =
                    vals.iter().map(as_rational).collect::<Result<_, _>>()?;
                let ok = rats.windows(2).all(|w| compare_rat(name, &w[0], &w[1]));
                Ok(ModelValue::Bool(ok))
            }
            _ => Err(format!("unsupported arithmetic operator {name}")),
        }
    }

    // ----- arrays ----------------------------------------------------------

    fn eval_array(
        &self,
        term: TermId,
        name: &str,
        args: &[TermId],
        depth: usize,
    ) -> Result<ModelValue, String> {
        match name {
            "select" => {
                let [a, i] = exactly(args)?;
                let idx = self.eval(i, depth + 1)?;
                // LAZY McCarthy fold over a syntactic store-chain: return the
                // stored value at the matching index WITHOUT reconstructing the
                // base array — so a `select` at a real (pushed) index resolves
                // even when the base is an intermediate/datatype array the model
                // never materializes. Falls through to full resolution otherwise.
                if let Some(v) = self.select_over_store_chain(a, &idx, depth)? {
                    return Ok(v);
                }
                // Full resolution: reconstruct the array to a concrete
                // `(default, finite-store)` value and read it at `idx`. When the
                // array operand cannot be reconstructed (a partial/unpinned array
                // leaf), fall back to the model's committed per-read value keyed
                // for single-valuedness — see `eval_select_via_model`.
                match self.eval_array_value(a, depth + 1) {
                    Ok(arr) => array_select(&arr, &idx),
                    Err(reconstruct_err) => {
                        self.eval_select_via_model(term, a, &idx, reconstruct_err)
                    }
                }
            }
            "store" => {
                let [a, i, v] = exactly(args)?;
                let arr = self.eval_array_value(a, depth + 1)?;
                let idx = self.eval(i, depth + 1)?;
                let val = self.eval(v, depth + 1)?;
                let mut store = arr.store.clone();
                store.push((idx, val));
                Ok(ModelValue::Array(Box::new(ArrayValue {
                    default: arr.default.clone(),
                    store,
                })))
            }
            "const-array" => {
                // `((as const (Array I E)) v)` — a constant array of `v`.
                let [v] = exactly(args)?;
                // Sanity: the result must be an array sort.
                if !matches!(self.terms.sort(term), Sort::Array(_)) {
                    return Err("const-array result is not an array sort".to_string());
                }
                let default = self.eval(v, depth + 1)?;
                Ok(ModelValue::Array(Box::new(ArrayValue {
                    default,
                    store: Vec::new(),
                })))
            }
            "default" => {
                let [array] = exactly(args)?;
                self.eval_array_default(term, array, depth)
            }
            "lambda-array" => {
                let [bound, body] = exactly(args)?;
                let Sort::Array(array_sort) = self.terms.sort(term) else {
                    return Err("lambda-array result is not an array sort".to_string());
                };
                if !matches!(self.terms.get(bound), TermData::Var(_, _))
                    || self.terms.sort(bound) != &array_sort.index_sort
                    || self.terms.sort(body) != &array_sort.element_sort
                {
                    return Err("malformed lambda-array binder or body sort".to_string());
                }

                // A binder-independent body denotes a constant array and has
                // an exact finite representation. This is the only sound way
                // to materialize a lambda as `(default, finite-store)` in the
                // gate. Binder-dependent lambdas are still fully supported by
                // structural `select` beta-reduction below, but cannot in
                // general be represented as a finite ArrayValue.
                if self.term_contains(body, bound) {
                    return Err(
                        "binder-dependent lambda-array has no finite array representation"
                            .to_string(),
                    );
                }
                let default = self.eval(body, depth + 1)?;
                Ok(ModelValue::Array(Box::new(ArrayValue {
                    default,
                    store: Vec::new(),
                })))
            }
            _ => Err(format!("unsupported array operator {name}")),
        }
    }

    fn eval_array_value(&self, term: TermId, depth: usize) -> Result<ArrayValue, String> {
        match self.eval(term, depth)? {
            ModelValue::Array(a) => Ok(*a),
            _ => Err("expected an array value".to_string()),
        }
    }

    /// Evaluate an array else-value without touching irrelevant store writes.
    ///
    /// SMT array semantics gives `default(store(a, i, v)) = default(a)`, so
    /// evaluating `i` or `v` would turn an exact structural result into a
    /// spurious coverage failure when either term is unpinned.
    fn eval_array_default(
        &self,
        term: TermId,
        array: TermId,
        depth: usize,
    ) -> Result<ModelValue, String> {
        let Sort::Array(array_sort) = self.terms.sort(array) else {
            return Err("default operand is not an array sort".to_string());
        };
        if self.terms.sort(term) != &array_sort.element_sort {
            return Err("default result sort does not match array element sort".to_string());
        }

        let mut current = array;
        let mut seen = HashSet::new();
        while seen.insert(current) {
            if depth + seen.len() > MAX_EVAL_DEPTH {
                return Err("array default evaluation depth exceeded".to_string());
            }
            match self.terms.get(current) {
                TermData::App(sym, args) if sym.name() == "store" && args.len() == 3 => {
                    current = args[0];
                }
                TermData::App(sym, args) if sym.name() == "const-array" && args.len() == 1 => {
                    return self.eval(args[0], depth + seen.len());
                }
                _ => return Ok(self.eval_array_value(current, depth + seen.len())?.default),
            }
        }
        Err("cyclic array store chain".to_string())
    }

    /// McCarthy `select` over a SYNTACTIC store-chain:
    /// `select(store(b,j,v), i) = if i==j then v else select(b,i)`, and
    /// `select(const-array d, i) = d`, and
    /// `select(lambda-array(x, body), i) = body[x := i]`. Returns the value
    /// WITHOUT resolving the
    /// base array `b` — so a read at a stored index never needs the base
    /// materialized (essential when `b` is an intermediate/datatype array the
    /// theory model does not reconstruct). `Ok(None)` when the chain bottoms out
    /// in a non-store/non-const-array base (a `Var`) and `i` matched no store
    /// index, so the caller resolves the whole array. SOUND: a store index that
    /// itself fails to evaluate makes the fold indeterminate (`Ok(None)` →
    /// fall through), so a wrong stored value is never returned; and the
    /// outermost (newest) store is matched first, exactly as `store` semantics
    /// require.
    fn select_over_store_chain(
        &self,
        a: TermId,
        idx: &ModelValue,
        depth: usize,
    ) -> Result<Option<ModelValue>, String> {
        if depth > MAX_EVAL_DEPTH {
            return Ok(None);
        }
        match self.terms.get(a) {
            TermData::App(sym, args) if sym.name() == "store" && args.len() == 3 => {
                let j = match self.eval(args[1], depth + 1) {
                    Ok(j) => j,
                    Err(_) => return Ok(None), // indeterminate store index: can't fold
                };
                if value_eq(&j, idx)? {
                    Ok(Some(self.eval(args[2], depth + 1)?))
                } else {
                    self.select_over_store_chain(args[0], idx, depth + 1)
                }
            }
            TermData::App(sym, args) if sym.name() == "const-array" && args.len() == 1 => {
                Ok(Some(self.eval(args[0], depth + 1)?))
            }
            TermData::App(sym, args) if sym.name() == "lambda-array" && args.len() == 2 => {
                let Sort::Array(array_sort) = self.terms.sort(a) else {
                    return Err("lambda-array result is not an array sort".to_string());
                };
                if !matches!(self.terms.get(args[0]), TermData::Var(_, _))
                    || self.terms.sort(args[0]) != &array_sort.index_sort
                    || self.terms.sort(args[1]) != &array_sort.element_sort
                {
                    return Err("malformed lambda-array binder or body sort".to_string());
                }
                Ok(Some(self.eval_with_binding(
                    args[0],
                    idx.clone(),
                    args[1],
                    depth + 1,
                )?))
            }
            _ => {
                // The chain bottomed out at a NON-store, non-const-array base `b`
                // (typically a free array `Var`), and `idx` matched — determinately
                // and unequally — every peeled store index above. By McCarthy,
                // `select(store(b,j,v), i) = select(b, i)` whenever `i != j`, so the
                // value of this read is EXACTLY `select(b, idx)` — INDEPENDENT of the
                // peeled stores' VALUES. Read the base `b` at `idx` DIRECTLY instead
                // of reconstructing the whole store-chain array (the caller's
                // fallback), because that reconstruction eagerly evaluates every
                // stored value, and a stored value can carry an unpinned leaf that is
                // irrelevant to a read that misses that store (e.g. a datatype
                // constructor `(C ... free-array-field ...)` stored under the
                // explicit-constructor array encoding). If `b` itself resolves to a
                // concrete `(default, finite-store)` array, read it; otherwise return
                // `None` so the caller falls through to the model's committed
                // per-read value (fail-closed, never a fabricated value).
                // (#g4-store-chain-base-read)
                match self.eval_array_value(a, depth + 1) {
                    Ok(arr) => Ok(Some(array_select(&arr, idx)?)),
                    Err(_) => Ok(None),
                }
            }
        }
    }

    /// Evaluate `(select array_term _)` at the already-computed index value `idx`
    /// by reading the model's committed per-read value, when the array operand
    /// could NOT be resolved to a concrete `(default, finite-store)` value
    /// (`reconstruct_err` is why). This is the array analogue of
    /// [`Evaluator::eval_uninterpreted_app`].
    ///
    /// `select` over an array is a single-valued function of the index, so two
    /// reads of the SAME array term at index values that evaluate EQUAL denote
    /// the same element (McCarthy functionality). The gate keys reads by
    /// `(array-term, index-value)` and takes the FIRST committed value per key as
    /// the single element there; a later read with the same key resolves through
    /// that same entry. This is what exposes — rather than honours — a model that
    /// pins two coincident reads to different values, and (because the gate
    /// evaluates the indices itself) catches a degenerate array whose reads
    /// contradict an asserted (in)equality. Keying by the array TERM is sound and
    /// never over-refutes: two reads that resolve here to one value are literally
    /// the same array expression at the same index value, which MUST be equal in
    /// any valid model.
    ///
    /// If the model does not pin this read, the result is `Unevaluable`
    /// (`reconstruct_err` is surfaced) — fail closed, never assumed.
    fn eval_select_via_model(
        &self,
        term: TermId,
        array_term: TermId,
        idx: &ModelValue,
        reconstruct_err: String,
    ) -> Result<ModelValue, String> {
        // Consult the value-keyed select graph: same array term, index values
        // equal ⇒ same element. The array key itself must be binder-independent;
        // otherwise the same array TermId can denote a different array in each
        // beta environment.
        if !self.term_depends_on_local_binding(array_term) {
            let graph = self.select_graph.borrow();
            for (at, key_idx, val) in graph.iter() {
                if *at == array_term && value_eq(key_idx, idx).unwrap_or(false) {
                    return Ok(val.clone());
                }
            }
        }
        // As for UF applications, adopting a per-TermId committed read is not
        // sound when this occurrence depends on the active lambda environment.
        if self.term_depends_on_local_binding(term) {
            return Err("model-backed context-dependent array read is unsupported".to_string());
        }
        // First time this `(array-term, index-value)` key is seen: adopt the
        // model's committed per-read value as the representative. A model that
        // does not pin the read leaves the gate unable to confirm (fail closed).
        let val = self.model.array_select_value(term).ok_or(reconstruct_err)?;
        self.select_graph
            .borrow_mut()
            .push((array_term, idx.clone(), val.clone()));
        Ok(val)
    }

    /// Most-recent scoped beta binding for `term`, if any.
    fn local_binding(&self, term: TermId) -> Option<ModelValue> {
        self.local_bindings
            .borrow()
            .iter()
            .rev()
            .find_map(|(bound, value)| (*bound == term).then(|| value.clone()))
    }

    /// Whether `root` syntactically contains any currently bound term.
    ///
    /// Per-TermId model commitments may be reused inside a beta environment
    /// only when this is false. A conservative positive result loses coverage
    /// but cannot admit a value from the wrong lambda instance.
    fn term_depends_on_local_binding(&self, root: TermId) -> bool {
        let bindings = self.local_bindings.borrow();
        if bindings.is_empty() {
            return false;
        }
        let bound: HashSet<TermId> = bindings.iter().map(|(term, _)| *term).collect();
        drop(bindings);

        let mut stack = vec![root];
        let mut seen = HashSet::new();
        while let Some(term) = stack.pop() {
            if bound.contains(&term) {
                return true;
            }
            if seen.insert(term) {
                stack.extend(self.terms.children(term));
            }
        }
        false
    }

    /// Evaluate `body` with one scoped lambda variable value.
    fn eval_with_binding(
        &self,
        bound: TermId,
        value: ModelValue,
        body: TermId,
        depth: usize,
    ) -> Result<ModelValue, String> {
        let restore_len = self.local_bindings.borrow().len();
        self.local_bindings.borrow_mut().push((bound, value));
        let _guard = LocalBindingGuard {
            bindings: &self.local_bindings,
            restore_len,
        };
        self.eval(body, depth)
    }

    /// Whether `needle` occurs syntactically in `root`.
    ///
    /// A negative result proves that a lambda body is binder-independent and
    /// may be materialized as a constant array. A conservative positive result
    /// (for example under a nested binder that reuses the same TermId) merely
    /// loses completeness and therefore remains sound.
    fn term_contains(&self, root: TermId, needle: TermId) -> bool {
        let mut stack = vec![root];
        let mut seen = HashSet::new();
        while let Some(term) = stack.pop() {
            if term == needle {
                return true;
            }
            if seen.insert(term) {
                stack.extend(self.terms.children(term));
            }
        }
        false
    }

    // ----- strings ---------------------------------------------------------

    fn eval_string(&self, name: &str, args: &[TermId], depth: usize) -> Result<ModelValue, String> {
        match name {
            "str.len" => {
                let [s] = exactly(args)?;
                let s = self.eval_str(s, depth + 1)?;
                Ok(ModelValue::Int(BigInt::from(s.chars().count())))
            }
            "str.++" => {
                let mut out = String::new();
                for &a in args {
                    out.push_str(&self.eval_str(a, depth + 1)?);
                }
                Ok(ModelValue::Str(out))
            }
            "str.at" => {
                let [s, i] = exactly(args)?;
                let s = self.eval_str(s, depth + 1)?;
                let idx = as_integer(&self.eval(i, depth + 1)?)?;
                let chars: Vec<char> = s.chars().collect();
                match idx.to_usize_checked().filter(|&k| k < chars.len()) {
                    Some(k) => Ok(ModelValue::Str(chars[k].to_string())),
                    None => Ok(ModelValue::Str(String::new())),
                }
            }
            _ => Err(format!("unsupported string operator {name}")),
        }
    }

    fn eval_str(&self, term: TermId, depth: usize) -> Result<String, String> {
        match self.eval(term, depth)? {
            ModelValue::Str(s) => Ok(s),
            _ => Err("expected a string value".to_string()),
        }
    }

    // ----- datatypes -------------------------------------------------------

    /// Resolve the datatype definition for a sort: directly for
    /// `Sort::Datatype`, or via the model's registry for a datatype abstracted
    /// to `Sort::Uninterpreted(name)` (see [`ModelView::datatype_def`]). Any
    /// other sort is not a datatype.
    fn dt_of_sort(&self, sort: &Sort) -> Option<ay_core::DatatypeSort> {
        match sort {
            Sort::Datatype(dt) => Some(dt.clone()),
            Sort::Uninterpreted(name) => self.model.datatype_def(name),
            _ => None,
        }
    }

    fn eval_datatype(
        &self,
        term: TermId,
        name: &str,
        args: &[TermId],
        depth: usize,
    ) -> Result<ModelValue, String> {
        // (1) Constructor application: the result sort is a datatype that
        //     declares a constructor with this exact name and arity.
        if let Some(dt) = self.dt_of_sort(&self.terms.sort(term).clone()) {
            if let Some(ctor) = dt.constructors.iter().find(|c| c.name == name) {
                if ctor.fields.len() != args.len() {
                    return Err(format!("constructor {name} arity mismatch"));
                }
                let vals = self.eval_all(args, depth)?;
                return Ok(ModelValue::Datatype {
                    ctor: name.to_string(),
                    args: vals,
                });
            }
        }

        // (2) Unary applications over a datatype-sorted argument: tester or
        //     selector. We key entirely off the argument's datatype sort, so a
        //     UF that merely happens to take a datatype argument is not
        //     misread (its name will match neither a recognizer nor a field).
        if args.len() == 1 {
            if let Some(dt) = self.dt_of_sort(&self.terms.sort(args[0]).clone()) {
                // Tester `(_ is C)` → "is-C".
                if let Some(target) = name.strip_prefix("is-") {
                    if dt.constructors.iter().any(|c| c.name == target) {
                        let v = self.eval(args[0], depth + 1)?;
                        return match v {
                            ModelValue::Datatype { ctor, .. } => {
                                Ok(ModelValue::Bool(ctor == target))
                            }
                            _ => Err("tester argument is not a datatype value".to_string()),
                        };
                    }
                }
                // Selector: `name` is a field of some constructor of `dt`.
                if dt
                    .constructors
                    .iter()
                    .any(|c| c.fields.iter().any(|f| f.name == name))
                {
                    match self.eval(args[0], depth + 1) {
                        Ok(v) => return Self::project_selector(&dt, name, v),
                        Err(arg_err) => {
                            return self.eval_selector_via_model(term, name, args[0], arg_err);
                        }
                    }
                }
            }
        }

        Err(format!(
            "uninterpreted / unsupported function application: {name}"
        ))
    }

    /// Resolve a datatype-selector application `(sel arg)` — `sel` a genuine
    /// field selector of `arg`'s datatype — whose ARGUMENT the gate could not
    /// reduce to a concrete datatype value (`arg_err` is why), by reading the
    /// model's committed value for the WHOLE selector application.
    ///
    /// This is the datatype-selector analogue of
    /// [`eval_select_via_model`](Self::eval_select_via_model) /
    /// [`eval_uninterpreted_app`](Self::eval_uninterpreted_app): a datatype
    /// selector projects a scalar (or nested-datatype) field, and under the eager
    /// datatype-in-array lowering the selector-over-array read
    /// `(fld_rhs (select <store-chain> i))` is itself a bit-blasted term with its
    /// own committed model value — the SAME value `get-value` would report — even
    /// when the gate cannot independently rebuild the datatype value flowing into
    /// it (its array operand bottoms out in a free base array the gate does not
    /// reconstruct, or a stored constructor carries an unpinned field the read
    /// never touches). Reading that committed value here closes the completeness
    /// gap the explicit-constructor store encoding opened (#g4-dt-selector-via-model).
    ///
    /// SOUNDNESS. `uf_app_value` returns the model's committed value for THIS
    /// exact application term (via the solver's own model evaluator), never a
    /// fabricated one, and yields `None` when the model does not pin it (⇒ fail
    /// closed to the original `arg_err`). Single-valuedness is enforced exactly as
    /// for uninterpreted-function applications: the value is keyed in `uf_graph`
    /// by the selector name plus the argument's committed representative, so two
    /// selector applications whose arguments the model pins EQUAL resolve to the
    /// SAME gate value — a model that pins them differently is surfaced (the
    /// enclosing (dis)equality then evaluates against one shared value), not
    /// honoured. When the argument has no committed representative the value is
    /// still the single committed value of this one term, so no wrong `Sat` can be
    /// manufactured; and this path only CONFIRMS a value — the constructor-
    /// injectivity-through-array-equality hazard the surrounding gate guards is
    /// decided by the array-equality machinery, which this does not touch.
    fn eval_selector_via_model(
        &self,
        term: TermId,
        name: &str,
        arg: TermId,
        arg_err: String,
    ) -> Result<ModelValue, String> {
        // Unlike structural projection from a concrete constructor, this path
        // reads ambient per-TermId commitments for both the selector and its
        // argument. Neither is indexed by the current beta environment.
        if self.term_depends_on_local_binding(term) {
            return Err("model-backed context-dependent selector is unsupported".to_string());
        }
        // A committed representative for the argument (its selector/uf/array
        // committed value, or a pinned leaf), used only to key single-valuedness.
        let arg_key = self
            .model
            .uf_app_value(arg)
            .or_else(|| self.model.array_select_value(arg))
            .or_else(|| self.model.leaf_value(arg));
        // STRUCTURAL-FIRST (#dt-selector-structural, M1 wrong-SAT root cause):
        // when the argument's own committed value is a datatype value built
        // with the selector's OWN constructor, the selector application is
        // fully determined by SMT-LIB selector semantics — `(sel (C .. a_i ..))
        // = a_i` — and MUST evaluate to that structural projection. The
        // committed per-application value below is consulted ONLY for
        // genuinely under-specified applications (wrong-constructor argument,
        // or no committed argument value at all): honouring a committed
        // per-application value that contradicts the structural projection
        // would let the gate confirm a model that violates
        // `pred(succ(t)) = t`. This branch is a pure function of the
        // argument's committed value, so single-valuedness holds by
        // construction and no `uf_graph` keying is needed.
        if let Some(ModelValue::Datatype { ctor, args: cargs }) = &arg_key {
            if let Some(dt) = self.dt_of_sort(&self.terms.sort(arg).clone()) {
                if let Some(cons) = dt.constructors.iter().find(|c| &c.name == ctor) {
                    if let Some(idx) = cons.fields.iter().position(|f| f.name == name) {
                        if let Some(v) = cargs.get(idx) {
                            return Ok(v.clone());
                        }
                    }
                }
            }
        }
        if let Some(key) = &arg_key {
            let graph = self.uf_graph.borrow();
            for (f, keys, val) in graph.iter() {
                if f == name && keys.len() == 1 && value_eq(&keys[0], key).unwrap_or(false) {
                    return Ok(val.clone());
                }
            }
        }
        let val = self.model.uf_app_value(term).ok_or(arg_err)?;
        if let Some(key) = arg_key {
            self.uf_graph
                .borrow_mut()
                .push((name.to_string(), vec![key], val.clone()));
        }
        Ok(val)
    }

    /// Project selector `sel` out of a datatype value, per the datatype `dt`.
    /// Applying a selector to a value built with a *different* constructor is
    /// under-specified ⇒ unevaluable.
    fn project_selector(
        dt: &ay_core::DatatypeSort,
        sel: &str,
        value: ModelValue,
    ) -> Result<ModelValue, String> {
        let ModelValue::Datatype { ctor, args } = value else {
            return Err("selector argument is not a datatype value".to_string());
        };
        let Some(cons) = dt.constructors.iter().find(|c| c.name == ctor) else {
            return Err("selector: value constructor not found in datatype".to_string());
        };
        match cons.fields.iter().position(|f| f.name == sel) {
            Some(idx) if idx < args.len() => Ok(args[idx].clone()),
            // `sel` is a valid selector of `dt`, but not of THIS value's
            // constructor — under-specified.
            _ => Err(format!(
                "selector {sel} applied to value of constructor {ctor} (under-specified)"
            )),
        }
    }
}

// ===========================================================================
// free helpers
// ===========================================================================

/// Destructure exactly `N` arguments, or fail closed.
fn exactly<const N: usize>(args: &[TermId]) -> Result<[TermId; N], String> {
    <[TermId; N]>::try_from(args).map_err(|_| format!("expected {N} arguments, got {}", args.len()))
}

fn arg_v(vals: &[ModelValue], i: usize) -> Result<&ModelValue, String> {
    vals.get(i).ok_or_else(|| "missing argument".to_string())
}

fn as_rational(v: &ModelValue) -> Result<BigRational, String> {
    match v {
        ModelValue::Int(n) => Ok(BigRational::from(n.clone())),
        ModelValue::Real(r) => Ok(r.clone()),
        _ => Err("expected a numeric (Int/Real) value".to_string()),
    }
}

fn as_integer(v: &ModelValue) -> Result<BigInt, String> {
    match v {
        ModelValue::Int(n) => Ok(n.clone()),
        ModelValue::Real(r) if r.is_integer() => Ok(r.to_integer()),
        _ => Err("expected an integer value".to_string()),
    }
}

/// Wrap an exact rational into the result sort: `Int` requires integrality.
fn wrap_numeric(r: BigRational, sort: &Sort) -> Result<ModelValue, String> {
    match sort {
        Sort::Int => {
            if r.is_integer() {
                Ok(ModelValue::Int(r.to_integer()))
            } else {
                Err("non-integer result in an Int context".to_string())
            }
        }
        Sort::Real => Ok(ModelValue::Real(r)),
        _ => Err("arithmetic result sort is neither Int nor Real".to_string()),
    }
}

/// SMT-LIB Euclidean division/remainder: `a = b*q + r` with `0 <= r < |b|`.
/// Returns `None` when `b == 0` (under-specified).
fn euclid(a: &BigInt, b: &BigInt) -> Option<(BigInt, BigInt)> {
    if b.is_zero() {
        return None;
    }
    let abs_b = b.abs();
    let r = a.mod_floor(&abs_b); // in [0, |b|)
    let q = (a - &r) / b; // exact
    Some((q, r))
}

fn compare_rat(op: &str, a: &BigRational, b: &BigRational) -> bool {
    match op {
        "<" => a < b,
        "<=" => a <= b,
        ">" => a > b,
        ">=" => a >= b,
        _ => false,
    }
}

/// Names of the non-indexed bitvector operators handled by [`bitvec::eval_named`].
fn is_bv_named(name: &str) -> bool {
    matches!(
        name,
        "bvadd"
            | "bvsub"
            | "bvmul"
            | "bvudiv"
            | "bvurem"
            | "bvsdiv"
            | "bvsrem"
            | "bvsmod"
            | "bvand"
            | "bvor"
            | "bvxor"
            | "bvnot"
            | "bvnand"
            | "bvnor"
            | "bvxnor"
            | "bvneg"
            | "bvshl"
            | "bvlshr"
            | "bvashr"
            | "concat"
            | "bvcomp"
            | "bv2nat"
            | "bvult"
            | "bvule"
            | "bvugt"
            | "bvuge"
            | "bvslt"
            | "bvsle"
            | "bvsgt"
            | "bvsge"
    )
}

/// Convenience: a checked `BigInt -> usize`.
trait ToUsizeChecked {
    fn to_usize_checked(&self) -> Option<usize>;
}

impl ToUsizeChecked for BigInt {
    fn to_usize_checked(&self) -> Option<usize> {
        use num_traits::ToPrimitive;
        if self.is_negative() {
            None
        } else {
            self.to_usize()
        }
    }
}
