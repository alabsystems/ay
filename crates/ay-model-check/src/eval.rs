// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The fresh, pure, total recursive evaluator.
//!
//! `Result<ModelValue, String>` is the internal evaluation type: `Ok(v)` is a
//! computed value and `Err(reason)` means *unevaluable* (which the public API
//! surfaces as [`EvalOutcome::Unevaluable`]). Nothing here panics or unwraps on
//! malformed/under-specified input — every such case returns `Err`.

use std::cell::{Cell, RefCell};
use std::collections::HashSet;

use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};
use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{Signed, Zero};

use crate::{
    array_select, bitvec, seq, value_eq, ArrayValue, EvalOutcome, ModelValue, ModelView,
    ProvenUnconstrainedKind, MAX_EVAL_DEPTH,
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

/// Compare two value-key tuples for a congruence-graph lookup.
///
/// `value_eq` is deliberately three-valued: in particular, exact algebraic
/// values from different extensions can be semantically equal even when this
/// checker cannot decide that equality.  A graph lookup may skip an entry only
/// after at least one component is PROVABLY different.  Treating an
/// incomparable component as `false` would permit a second result for a key
/// that may be equal to the first, violating function single-valuedness and
/// potentially confirming a wrong model.
///
/// Keep scanning after an incomparable component because a later
/// `Ok(false)` still proves the tuples distinct.  If no component separates
/// them, the unresolved comparison propagates and the gate fails closed before
/// installing another mapping.
pub(crate) fn congruence_keys_equal(
    stored: &[ModelValue],
    candidate: &[ModelValue],
) -> Result<bool, String> {
    if stored.len() != candidate.len() {
        return Ok(false);
    }

    let mut unresolved = None;
    for (left, right) in stored.iter().zip(candidate) {
        match value_eq(left, right) {
            Ok(true) => {}
            Ok(false) => return Ok(false),
            Err(reason) => {
                if unresolved.is_none() {
                    unresolved = Some(reason);
                }
            }
        }
    }

    match unresolved {
        Some(reason) => Err(format!("cannot decide congruence-key equality: {reason}")),
        None => Ok(true),
    }
}

/// Native evaluator-call depth at which projection dispatch fails closed.
///
/// Projection applications are peeled iteratively, but ordinary terms between
/// projections still recurse through [`Evaluator::eval`]. Keep a conservative
/// backstop below the native-stack exhaustion point seen on libtest's small
/// worker stacks. This does not lower [`MAX_EVAL_DEPTH`] for projection-free
/// evaluation, and consecutive projections consume only the shared logical
/// depth budget because they do not add native evaluator frames.
const MAX_PROJECTION_EVAL_CALL_DEPTH: usize = 128;

/// Restores the local lambda-binding stack on every exit, including unwinding.
///
/// The evaluator is intentionally reusable across all assertions in one gate
/// pass, so a beta-reduction binding must never leak into a later assertion.
struct LocalBindingGuard<'a> {
    bindings: &'a RefCell<Vec<(TermId, ModelValue)>>,
    restore_len: usize,
}

/// Restores the active native evaluator-call count on every exit.
struct EvalCallDepthGuard<'a> {
    active_calls: &'a Cell<usize>,
}

impl Drop for EvalCallDepthGuard<'_> {
    fn drop(&mut self) {
        self.active_calls
            .set(self.active_calls.get().saturating_sub(1));
    }
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
    /// Number of currently active [`Self::eval`] calls. Projection dispatch
    /// uses this only as a native-stack safety backstop; SMT term depth remains
    /// governed by [`MAX_EVAL_DEPTH`].
    active_eval_calls: Cell<usize>,
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
            active_eval_calls: Cell::new(0),
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
    fn eval(&self, mut term: TermId, mut depth: usize) -> Result<ModelValue, String> {
        // This increment is paired one-for-one with `EvalCallDepthGuard::drop`.
        let active_calls = self
            .active_eval_calls
            .get()
            .checked_add(1)
            .ok_or_else(|| "evaluator call depth overflow".to_string())?;
        self.active_eval_calls.set(active_calls);
        let _call_depth_guard = EvalCallDepthGuard {
            active_calls: &self.active_eval_calls,
        };

        // A checked projection is a total symbolic interpretation. Peel it in
        // this SAME evaluator so the selected argument observes the current
        // UF/select graphs, memo, logical depth budget, and lambda bindings.
        // Iteration avoids adding one native Rust frame per projection while
        // retaining one depth edge per beta reduction. Projection lookup must
        // precede the TermId-keyed memo so symbolic definitions cannot be
        // shadowed by a per-application value.
        loop {
            if depth > MAX_EVAL_DEPTH {
                return Err(format!("recursion depth limit {MAX_EVAL_DEPTH} exceeded"));
            }
            let TermData::App(_, args) = self.terms.get(term) else {
                break;
            };
            let Some(projected_argument) = self
                .model
                .projection_argument(term)
                .map_err(|error| error.to_string())?
            else {
                break;
            };
            if active_calls > MAX_PROJECTION_EVAL_CALL_DEPTH {
                return Err(format!(
                    "projection recursion depth limit {MAX_PROJECTION_EVAL_CALL_DEPTH} exceeded"
                ));
            }
            let selected = args.get(projected_argument).copied().ok_or_else(|| {
                format!(
                    "projection selects argument {projected_argument}, but application arity is {}",
                    args.len()
                )
            })?;
            let selected_sort = self.terms.sort(selected);
            let result_sort = self.terms.sort(term);
            if selected_sort != result_sort {
                return Err(format!(
                    "projection selected argument sort {selected_sort:?} does not match result sort {result_sort:?}"
                ));
            }
            term = selected;
            depth += 1;
        }

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
                // NAME and sort the leaf. A bare "does not pin this leaf" gave
                // a `cannot-confirm` no attribution at all, so every
                // completeness investigation had to re-instrument the gate to
                // learn WHICH leaf and carrier the model failed to cover.
                .ok_or_else(|| {
                    format!(
                        "model does not pin this leaf: {name} : {:?}",
                        self.terms.sort(term)
                    )
                }),
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
                    // `(_ NaN eb sb)`, `(_ +zero eb sb)`, … are FP VALUES, not
                    // bitvector operators. Routing every indexed symbol to
                    // `bitvec::eval_indexed` made the gate report "unsupported
                    // indexed bitvector operator NaN" and refuse to confirm the
                    // model, so a correct `sat` was published as `unknown`.
                    if args.is_empty() {
                        if let Some(value) = fp_special_constant(name, indices) {
                            return Ok(value);
                        }
                    }
                    // The ROUNDING conversions take a leading rounding mode,
                    // which is a nullary symbol no model pins — so their first
                    // operand must be resolved syntactically, BEFORE the
                    // blanket `eval_all` below would try to look it up as a
                    // leaf and fail. Each reduces to one correctly rounded
                    // conversion of an exact rational (`crate::fp`).
                    if args.len() == 2 {
                        if let Some(unsigned) = match name.as_str() {
                            "to_fp" => Some(false),
                            "to_fp_unsigned" => Some(true),
                            _ => None,
                        } {
                            let [eb, sb] = <[u32; 2]>::try_from(indices.as_slice())
                                .map_err(|_| "to_fp expects two indices".to_string())?;
                            let rm = self.eval_rounding_mode(args[0], depth)?;
                            let value = self.eval(args[1], depth + 1)?;
                            return crate::fp::to_fp_rounded(unsigned, eb, sb, rm, &value);
                        }
                        if let Some(unsigned) = match name.as_str() {
                            "fp.to_sbv" => Some(false),
                            "fp.to_ubv" => Some(true),
                            _ => None,
                        } {
                            let [width] = <[u32; 1]>::try_from(indices.as_slice())
                                .map_err(|_| "fp.to_sbv/to_ubv expects one index".to_string())?;
                            let rm = self.eval_rounding_mode(args[0], depth)?;
                            let value = self.eval(args[1], depth + 1)?;
                            return crate::fp::to_bv(unsigned, width, rm, &value);
                        }
                    }
                    let vals = self.eval_all(args, depth)?;
                    // `((_ to_fp eb sb) <bv>)` is a BIT REINTERPRET, not a
                    // bitvector operator: it reads an `eb + sb`-wide word as the
                    // IEEE fields of an FP value. No rounding is involved, so
                    // the gate can do it exactly and INDEPENDENTLY — it is pure
                    // bit-splitting, sharing no code with the solver.
                    //
                    // The two-operand ROUNDING forms (`(_ to_fp eb sb) <rm>
                    // <real|bv|fp>` and `to_fp_unsigned`) are handled ABOVE, by
                    // `crate::fp::to_fp_rounded`. They used to decline here on
                    // the grounds that "an independent gate must not confirm a
                    // model using the same rounding routine that produced it,
                    // and an approximate reimplementation could confirm a WRONG
                    // model". The first half is the real constraint and is
                    // honoured — nothing in this crate calls into the solver's
                    // FP code. The second half does not apply, because
                    // `crate::fp` rounds by comparing exact `BigRational`s
                    // against exact half-way points; see that module's header.
                    if name == "to_fp" && vals.len() == 1 {
                        if let Some(value) = fp_from_ieee_bits(indices, &vals[0]) {
                            return Ok(value);
                        }
                    }
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
            //
            // `(/ x 0)`, `(div x 0)` and `(mod x 0)` are UNCONSTRAINED in
            // SMT-LIB — the Ints/Reals theories leave division by zero to an
            // uninterpreted function — so `eval_arith` routes exactly those
            // three sites through [`Self::division_by_zero`], which adopts the
            // model's own choice and then checks the one residue the theory
            // does fix (the result is still a number of the right sort). The
            // adoption is deliberately NOT applied to the whole arithmetic
            // dispatch: a narrower window cannot mistake an unrelated failure
            // for an under-specified one.
            "+" | "-" | "*" | "/" | "div" | "mod" | "abs" | "to_real" | "to_int" | "is_int"
            | "<" | "<=" | ">" | ">=" => self.eval_arith(term, name, args, depth),

            // Floating-point to exact Real.  This deliberately lives outside
            // `eval_arith`: its operand is an IEEE bit-pattern value, not an
            // Int/Real numeric value.  NaN and the infinities have no real
            // value SMT-LIB fixes, so those adopt the model's choice (checked
            // to still be a number) rather than being computed.
            "fp.to_real" => self.eval_fp_to_real(term, args, depth),

            // Floating-point to its IEEE-754 interchange encoding. Pure
            // bit-reinterpretation, so the gate computes it exactly and
            // independently on every value SMT-LIB determines.
            //
            // NaN is the sole exception, and it takes the underspecified path
            // rather than the generic one because adopting the model's value
            // there is only sound WITH A CHECK: the standard frees the sign bit
            // and the payload, it does not free the result from being a NaN
            // encoding at all. `crate::fp::check_ieee_nan_encoding` enforces
            // exactly that residue, so an adopted `#x00000000` — which z3 also
            // refutes — still fails closed instead of confirming a `sat`.
            "fp.to_ieee_bv" => {
                let [arg] = exactly(args)?;
                let operand = self.eval(arg, depth + 1)?;
                match crate::fp::to_ieee_bv(&operand) {
                    Err(reason) if reason == crate::fp::UNDERSPECIFIED => self
                        .adopt_underspecified(term, name, args, depth, reason, |adopted| {
                            crate::fp::check_ieee_nan_encoding(&operand, adopted)
                        }),
                    other => other,
                }
            }

            // The `(fp <sign-bv> <exp-bv> <sig-bv>)` literal: three bitvector
            // fields assembled into a value. Assembling it here rather than
            // adopting the solver's reading of it is the difference between
            // CHECKING an FP assertion and restating one — the literal is the
            // operand of nearly every one of them. The arity guard keeps a
            // user-declared symbol that merely happens to be spelled `fp` on
            // the uninterpreted-application path.
            "fp" if args.len() == 3 => {
                crate::fp::from_field_bitvectors(&self.eval_all(args, depth)?)
            }

            // The rest of the floating-point fragment, computed exactly on
            // `BigInt`/`BigRational` in `crate::fp` — see that module for why
            // an exact reimplementation of IEEE rounding keeps the gate
            // independent.
            //
            // This is a PREFIX arm on purpose. With one match arm per operator,
            // an `fp.` operator nobody had implemented yet fell through to
            // `eval_uninterpreted_app`, which ADOPTS the solver's committed
            // value — silently confirming an interpreted operator the gate
            // never computed. Claiming the whole namespace turns that class of
            // hole into an explicit `Err` and a `CannotConfirm`.
            _ if name.starts_with("fp.") => self.eval_fp(term, name, args, depth),

            // Arrays.
            "select" | "store" | "const-array" | "lambda-array" | "default" => {
                self.eval_array(term, name, args, depth)
            }

            // Strings. Regex structure is interpreted by the separate,
            // proof-checker-parity interval matcher; only String-sorted leaves
            // flow through this evaluator/model view.
            "str.++" | "str.len" | "str.at" | "str.in_re" | "str.in.re" | "str.replace_re"
            | "str.replace_re_all" => self.eval_string(name, args, depth),

            // The rest of the string theory, computed from the operand VALUES.
            // These were reaching the uninterpreted-function path, so the gate
            // adopted the solver's answer for `(str.contains s t)` rather than
            // looking at `s` and `t`.
            _ if crate::strings::handles(name, args.len()) => {
                let vals = self.eval_all(args, depth)?;
                crate::strings::eval(name, &vals)
            }

            // Finite sets, computed from the `(Array T Bool)` membership
            // carrier they are modelled on. Also previously adopted.
            _ if crate::sets::handles(name, args.len()) => {
                let domain = args.first().map_or(crate::sets::DomainSize::Unknown, |&a| {
                    element_domain_size(self.terms.sort(a))
                });
                let vals = self.eval_all(args, depth)?;
                crate::sets::eval(name, &vals, &domain)
            }

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
                Err(dt_err) => {
                    self.eval_uninterpreted_app(term, name, args, depth, dt_err, None, |_| Ok(()))
                }
            },
        }
    }

    /// Adopt the model's committed value for an application whose result
    /// SMT-LIB leaves UNCONSTRAINED on these particular inputs, then CHECK the
    /// residue the standard does constrain.
    ///
    /// SMT-LIB restricts, but does not uniquely determine, `fp.min`/`fp.max` of
    /// `+0` and `-0` and the NaN encoding `fp.to_ieee_bv` returns. On those
    /// inputs the gate may read only a normal, committed application value and
    /// then validates the remaining restriction. Fully unconstrained results
    /// (`fp.to_real` of a non-finite operand and arithmetic division by zero)
    /// use the separate typed [`Self::adopt_proven_unconstrained`] path.
    ///
    /// `residue` is what is left to check once the free part is granted: an
    /// adopted `fp.min` of the two zeros must still be a ZERO of that format,
    /// and an adopted `fp.to_ieee_bv` of NaN must still be a NaN ENCODING.
    /// That is what keeps this path from laundering an evaluator bug into a
    /// confirmed `sat`. A residue failure is an `Err`, i.e. `CannotConfirm` —
    /// fail closed, as everywhere else here.
    fn adopt_underspecified(
        &self,
        term: TermId,
        name: &str,
        args: &[TermId],
        depth: usize,
        reason: String,
        residue: impl Fn(&ModelValue) -> Result<(), String>,
    ) -> Result<ModelValue, String> {
        // `None`, NOT a typed unconstrained reason: this helper exists for
        // results the standard RESTRICTS rather than frees (a NaN keeps a
        // required encoding even though its sign and payload are
        // unspecified), so only the model's own committed value is
        // admissible. The residue is checked before a new graph entry is
        // installed, so an ill-sorted/bogus pin cannot pollute congruent uses.
        self.eval_uninterpreted_app(term, name, args, depth, reason, None, residue)
    }

    /// Adopt a value only after an exact evaluator branch has proved that the
    /// operation is unconstrained on the independently evaluated inputs.
    ///
    /// The ordinary committed value has priority. Only when it is absent may
    /// the model supply a definition-selected value through the typed fallback.
    /// `residue` validates the result sort before the value enters `uf_graph`.
    fn adopt_proven_unconstrained(
        &self,
        term: TermId,
        name: &str,
        args: &[TermId],
        depth: usize,
        kind: ProvenUnconstrainedKind,
        residue: impl Fn(&ModelValue) -> Result<(), String>,
    ) -> Result<ModelValue, String> {
        self.eval_uninterpreted_app(
            term,
            name,
            args,
            depth,
            format!("SMT-LIB leaves {name} unconstrained for these inputs"),
            Some(kind),
            residue,
        )
    }

    /// `(/ a 0)`, `(div a 0)` and `(mod a 0)`: unspecified but TOTAL.
    ///
    /// SMT-LIB constrains integer division and remainder only for a nonzero
    /// divisor. At zero they are arbitrary-but-FIXED functions of their
    /// arguments — every value is a legal interpretation, so there is nothing
    /// to compute, and refusing turned a legitimate `sat` into `unknown`
    /// (`(assert (< 0 (div 1 0)))` is sat in z3).
    ///
    /// So adopt the model's own choice, exactly as `fp.to_real` at NaN does.
    /// The adoption is keyed by the argument VALUES, which is what makes it an
    /// interpretation rather than a wish: `(div 1 0)` gets ONE value across
    /// every occurrence, so a model claiming it is both 0 and 1 is still
    /// refuted. The sort check is the rest of what can be verified — the
    /// theory says nothing else about these values.
    fn division_by_zero(
        &self,
        term: TermId,
        name: &str,
        args: &[TermId],
        depth: usize,
        kind: ProvenUnconstrainedKind,
    ) -> Result<ModelValue, String> {
        let (expected_name, expected_sort, operand_sort) = match kind {
            ProvenUnconstrainedKind::RealDivByZero => ("/", Sort::Real, Sort::Real),
            ProvenUnconstrainedKind::IntDivByZero => ("div", Sort::Int, Sort::Int),
            ProvenUnconstrainedKind::IntModByZero => ("mod", Sort::Int, Sort::Int),
            ProvenUnconstrainedKind::FpToRealNonFinite => {
                return Err(
                    "non-arithmetic unconstrained reason at division-by-zero site".to_string(),
                )
            }
        };
        if name != expected_name
            || self.terms.sort(term) != &expected_sort
            || args.len() != 2
            || args
                .iter()
                .any(|&argument| self.terms.sort(argument) != &operand_sort)
        {
            return Err(format!(
                "typed unconstrained reason does not match `{name}` signature"
            ));
        }
        self.adopt_proven_unconstrained(term, name, args, depth, kind, |adopted| {
            let well_sorted = match kind {
                ProvenUnconstrainedKind::RealDivByZero => {
                    matches!(adopted, ModelValue::Real(_) | ModelValue::Algebraic(_))
                }
                ProvenUnconstrainedKind::IntDivByZero | ProvenUnconstrainedKind::IntModByZero => {
                    matches!(adopted, ModelValue::Int(_))
                }
                ProvenUnconstrainedKind::FpToRealNonFinite => false,
            };
            if well_sorted {
                Ok(())
            } else {
                Err(format!("{name} by zero must still be a number"))
            }
        })
    }

    /// Resolve a `RoundingMode`-sorted operand to one of the five modes.
    ///
    /// A literal (`RNE`, `roundTowardZero`, …) is a nullary symbol that no
    /// model pins, so it is read SYNTACTICALLY; a declared `RoundingMode`
    /// constant is a leaf the model does pin, and arrives as an uninterpreted
    /// token naming its mode. Anything else fails closed.
    fn eval_rounding_mode(
        &self,
        term: TermId,
        depth: usize,
    ) -> Result<crate::fp::RoundingMode, String> {
        let syntactic = match self.terms.get(term) {
            TermData::App(sym, args) if args.is_empty() => {
                crate::fp::RoundingMode::from_name(sym.name())
            }
            TermData::Var(name, _) => crate::fp::RoundingMode::from_name(name),
            _ => None,
        };
        if let Some(rm) = syntactic {
            return Ok(rm);
        }
        match self.eval(term, depth + 1)? {
            ModelValue::Uninterpreted(token) => crate::fp::RoundingMode::from_name(&token)
                .ok_or_else(|| format!("`{token}` does not name a rounding mode")),
            _ => Err("operand is not a rounding mode".to_string()),
        }
    }

    /// The `fp.`-prefixed floating-point operators.
    ///
    /// Split by whether the operator takes a leading rounding mode, because
    /// that decides where the value operands start. Anything not listed falls
    /// through to an `Err` and the gate keeps failing closed on it — which is
    /// the point of routing the whole `fp.` namespace here rather than letting
    /// an unimplemented operator reach the adopt-the-solver's-answer path.
    fn eval_fp(
        &self,
        term: TermId,
        name: &str,
        args: &[TermId],
        depth: usize,
    ) -> Result<ModelValue, String> {
        // Rounding-mode-taking operators: `rm` first, values after.
        if matches!(
            name,
            "fp.add" | "fp.sub" | "fp.mul" | "fp.div" | "fp.fma" | "fp.sqrt" | "fp.roundToIntegral"
        ) {
            let (rm_arg, rest) = args
                .split_first()
                .ok_or_else(|| format!("{name} expects a rounding mode"))?;
            let rm = self.eval_rounding_mode(*rm_arg, depth)?;
            let vals = self.eval_all(rest, depth)?;
            return match name {
                "fp.fma" => crate::fp::fma(rm, &vals),
                "fp.roundToIntegral" | "fp.sqrt" => {
                    let [v] = <&[ModelValue; 1]>::try_from(vals.as_slice())
                        .map_err(|_| format!("{name} expects one argument"))?;
                    if name == "fp.sqrt" {
                        crate::fp::sqrt(rm, v)
                    } else {
                        crate::fp::round_to_integral(rm, v)
                    }
                }
                _ => crate::fp::arith(name, rm, &vals)?
                    .ok_or_else(|| format!("unsupported floating-point operator {name}")),
            };
        }

        let vals = self.eval_all(args, depth)?;
        if let [only] = vals.as_slice() {
            if let Some(verdict) = crate::fp::classify(name, only)? {
                return Ok(ModelValue::Bool(verdict));
            }
            if let Some(value) = crate::fp::unary_sign(name, only)? {
                return Ok(value);
            }
        }
        if let Some(verdict) = crate::fp::compare(name, &vals)? {
            return Ok(ModelValue::Bool(verdict));
        }
        match crate::fp::min_max(name, &vals) {
            Ok(Some(value)) => return Ok(value),
            Ok(None) => {}
            // `fp.min`/`fp.max` of `+0` and `-0`: SMT-LIB allows EITHER zero,
            // so there is nothing to compute and nothing to refuse. Adopt the
            // model's own choice — the treatment `fp.to_real` gets at NaN —
            // and then check that what came back is one of the two answers the
            // standard actually allows, so an adopted value is still a checked
            // one. (`min_max` only reports this for two operands of one
            // format, so `vals[0]` is the format to check against.)
            Err(reason) if reason == crate::fp::UNDERSPECIFIED => {
                let like = vals
                    .first()
                    .cloned()
                    .ok_or_else(|| format!("{name} expects two floating-point arguments"))?;
                return self.adopt_underspecified(term, name, args, depth, reason, |adopted| {
                    if is_zero_of_format(adopted, &like) {
                        Ok(())
                    } else {
                        Err(format!(
                            "{name} of +0 and -0 must be a zero of the operands' format"
                        ))
                    }
                });
            }
            Err(reason) => return Err(reason),
        }
        if name == "fp.rem" {
            return crate::fp::rem(&vals);
        }
        Err(format!("unsupported floating-point operator {name}"))
    }

    /// Evaluate SMT-LIB `fp.to_real` from the model's exact IEEE fields.
    ///
    /// No host float participates in this conversion.  Finite values are
    /// reconstructed as `significand * 2^exponent` using `BigInt` /
    /// `BigRational`; malformed payloads, unsupported field widths, and
    /// impractically large exact shifts are rejected rather than guessed. NaN
    /// and infinity take the separately typed unconstrained-result path after
    /// their exact IEEE encoding has been proved. The shift bound is only a
    /// resource guard: crossing it changes a possible confirmation into
    /// `CannotConfirm`, never the reverse.
    ///
    /// The decoding is kept here, rather than delegated to [`crate::fp`],
    /// because it accepts a WIDER format envelope than the arithmetic there
    /// needs (`fp.to_real` never rounds, so it does not have to bound the
    /// intermediates the way rounding does) — declining a format the gate can
    /// read exactly would be a pure completeness loss.
    fn eval_fp_to_real(
        &self,
        term: TermId,
        args: &[TermId],
        depth: usize,
    ) -> Result<ModelValue, String> {
        let [arg] = exactly(args)?;
        if self.terms.sort(term) != &Sort::Real {
            return Err("fp.to_real result sort is not Real".to_string());
        }
        let Sort::FloatingPoint(expected_exponent_bits, expected_significand_bits) =
            self.terms.sort(arg)
        else {
            return Err("fp.to_real operand sort is not FloatingPoint".to_string());
        };
        let ModelValue::FloatingPoint {
            sign,
            exponent,
            significand,
            exponent_bits,
            significand_bits,
        } = self.eval(arg, depth + 1)?
        else {
            return Err("fp.to_real expects a floating-point value".to_string());
        };
        if exponent_bits != *expected_exponent_bits
            || significand_bits != *expected_significand_bits
        {
            return Err("fp.to_real model payload format disagrees with operand sort".to_string());
        }

        // AY's concrete FP model uses u64 fields.  Keep the independent gate's
        // accepted envelope identical to that representation and validate the
        // raw payload before shifting.
        if !(2..64).contains(&exponent_bits) || !(2..=64).contains(&significand_bits) {
            return Err("unsupported floating-point field width".to_string());
        }
        let stored_bits = significand_bits - 1;
        let max_exponent = (1u64 << exponent_bits) - 1;
        let significand_limit = 1u64 << stored_bits;
        if exponent > max_exponent || significand >= significand_limit {
            return Err("malformed floating-point model payload".to_string());
        }
        if exponent == max_exponent {
            // Unconstrained by SMT-LIB rather than uncomputable: `fp.to_real`
            // of a NaN or an infinity may be ANY real, so this adopts the
            // model's committed choice, or (only if no commitment exists) the
            // definition-selected fallback. Reaching this exact all-ones
            // exponent branch is what mints the typed evidence; malformed
            // fields were rejected above. The only residue is the Real result
            // sort, checked before the value enters the congruence graph.
            return self.adopt_proven_unconstrained(
                term,
                "fp.to_real",
                args,
                depth,
                ProvenUnconstrainedKind::FpToRealNonFinite,
                |adopted| {
                    if matches!(adopted, ModelValue::Real(_) | ModelValue::Algebraic(_)) {
                        Ok(())
                    } else {
                        Err("fp.to_real of NaN or infinity must still be a real".to_string())
                    }
                },
            );
        }

        let bias = (1u64 << (exponent_bits - 1)) - 1;
        let mut exact_significand = BigInt::from(significand);
        if exponent != 0 {
            exact_significand += BigInt::from(1u8) << stored_bits as usize;
        }
        if exact_significand.is_zero() {
            // Both IEEE zeros map to mathematical Real zero.
            return Ok(ModelValue::Real(BigRational::from_integer(BigInt::zero())));
        }

        let effective_exponent = if exponent == 0 {
            1i64 - bias as i64 - i64::from(stored_bits)
        } else {
            exponent as i64 - bias as i64 - i64::from(stored_bits)
        };
        const MAX_EXACT_FP_SHIFT: i64 = 1 << 20;
        if effective_exponent.unsigned_abs() > MAX_EXACT_FP_SHIFT as u64 {
            return Err("fp.to_real exact exponent exceeds resource bound".to_string());
        }

        let magnitude = if effective_exponent >= 0 {
            BigRational::from_integer(exact_significand << effective_exponent as usize)
        } else {
            BigRational::new(
                exact_significand,
                BigInt::from(1u8) << (-effective_exponent) as usize,
            )
        };
        Ok(ModelValue::Real(if sign { -magnitude } else { magnitude }))
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
    ///
    /// `proven_unconstrained` is present only when the exact calling branch has
    /// positively proved one of [`ProvenUnconstrainedKind`]'s input conditions.
    /// It authorizes a fallback to
    /// [`ModelView::proven_unconstrained_app_value`] *only if* the ordinary
    /// committed value is absent. Generic applications and partially
    /// unspecified results pass `None`.
    ///
    /// `residue` validates the value's remaining theory obligations (at least
    /// its result sort) before a fresh graph entry is installed. It is also
    /// rechecked on graph hits, keeping this primitive fail-closed even if a
    /// future caller supplies a stricter residue for the same value key.
    fn eval_uninterpreted_app(
        &self,
        term: TermId,
        name: &str,
        args: &[TermId],
        depth: usize,
        dt_err: String,
        proven_unconstrained: Option<ProvenUnconstrainedKind>,
        residue: impl Fn(&ModelValue) -> Result<(), String>,
    ) -> Result<ModelValue, String> {
        // Evaluate the arguments ourselves. If any argument is unevaluable, the
        // application is unevaluable (fail closed).
        let arg_vals = self.eval_all(args, depth)?;
        // Consult the value-keyed graph: same function, argument values all
        // equal ⇒ same result.
        {
            let graph = self.uf_graph.borrow();
            for (f, keys, val) in graph.iter() {
                if f == name && congruence_keys_equal(keys, &arg_vals)? {
                    residue(val)?;
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
        //
        // Report the MISS, not `dt_err`. `dt_err` is the datatype-dispatch
        // failure that routed us here, and for a plain uninterpreted symbol it
        // reads "uninterpreted / unsupported function application: f" — which
        // states that the EVALUATOR does not support `f`. That is not what
        // happened: the evaluator supports `f` fine (this function is exactly
        // that support), and the real reason is that the MODEL committed no
        // value for this application. The two call for opposite fixes — extend
        // the evaluator vs. complete the model — and the misattribution sends a
        // reader to the wrong one. Keep `dt_err` in the text so the datatype
        // path is still diagnosable when that is genuinely the cause.
        //
        // The argument values are passed through (`uf_app_value_at`) so an
        // implementor whose PUBLISHED model interprets the function totally —
        // a table plus an else branch — can answer AT this argument point, and
        // can RECONCILE a per-application pin against that published body. The
        // value is still keyed into `uf_graph` by these same argument values
        // below, so single-valuedness is enforced identically
        // (#g3-gate-reads-printed-uf).
        let val = if let Some(committed) = self.model.uf_app_value_at(term, &arg_vals) {
            // A normal model commitment always wins. The typed fallback exists
            // solely for otherwise-uncommitted theory applications.
            committed
        } else if let Some(kind) = proven_unconstrained {
            self.model
                .proven_unconstrained_app_value(term, kind)
                .ok_or_else(|| {
                    format!(
                        "model supplies no value for proven-unconstrained \
                         application `{name}` ({kind:?}; {dt_err})"
                    )
                })?
        } else {
            return Err(format!(
                "model commits no value for this application of `{name}` \
                 (gate cannot confirm without one; datatype dispatch also \
                 declined: {dt_err})"
            ));
        };
        // Validate before insertion. In particular, a malicious or malformed
        // fallback cannot seed the value-keyed graph with a wrong-sort value
        // that a congruent sibling would later inherit.
        residue(&val)?;
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
        let operand_sort = self.terms.sort(args[0]);
        if args[1..]
            .iter()
            .any(|&arg| self.terms.sort(arg) != operand_sort)
        {
            return Err("= operands have different sorts".to_string());
        }
        let vals = self.eval_all(args, depth)?;
        for v in &vals[1..] {
            if !self.value_eq_at_sort(&vals[0], v, operand_sort)? {
                return Ok(ModelValue::Bool(false));
            }
        }
        Ok(ModelValue::Bool(true))
    }

    /// Equality with the operand sort still attached.
    ///
    /// Most model values carry enough type information for [`value_eq`]. An
    /// [`ArrayValue`] intentionally does not: it stores only a default and a
    /// finite override list. For arrays, the index sort is necessary to decide
    /// whether differing defaults are reachable. A finite override list can
    /// never cover `Int`, for example, while it can cover all of `Bool`.
    fn value_eq_at_sort(
        &self,
        left: &ModelValue,
        right: &ModelValue,
        sort: &Sort,
    ) -> Result<bool, String> {
        match (sort, left, right) {
            (Sort::Array(array_sort), ModelValue::Array(left), ModelValue::Array(right)) => {
                self.array_eq_at_sort(left, right, array_sort)
            }
            _ => value_eq(left, right),
        }
    }

    /// Extensional equality for typed array values.
    ///
    /// The untyped comparator in `lib.rs` must fail closed when defaults differ,
    /// because it cannot know whether finite stores cover the index domain. This
    /// evaluator owns the original operand sort, so it can make the exact
    /// distinction:
    ///
    /// * on a provably infinite index sort, finitely many stores always leave an
    ///   index where both defaults are read;
    /// * on a known finite carrier, equal reads at every distinct stored key
    ///   decide equality iff those keys cover the complete carrier;
    /// * on an unknown carrier (notably an uninterpreted sort), it retains the
    ///   fail-closed result.
    fn array_eq_at_sort(
        &self,
        left: &ArrayValue,
        right: &ArrayValue,
        sort: &ay_core::ArraySort,
    ) -> Result<bool, String> {
        let defaults_equal =
            self.value_eq_at_sort(&left.default, &right.default, &sort.element_sort)?;

        // A finite override set cannot hide different defaults over an infinite
        // carrier. This proof needs no comparison between the stored keys.
        if !defaults_equal && Self::index_sort_is_definitely_infinite(&sort.index_sort) {
            return Ok(false);
        }

        for (key, _) in left.store.iter().chain(&right.store) {
            let left_value = self.array_select_at_sort(left, key, &sort.index_sort)?;
            let right_value = self.array_select_at_sort(right, key, &sort.index_sort)?;
            if !self.value_eq_at_sort(&left_value, &right_value, &sort.element_sort)? {
                return Ok(false);
            }
        }
        if defaults_equal {
            return Ok(true);
        }

        let keys = self.distinct_array_keys(left, right, &sort.index_sort)?;
        match Self::known_finite_index_cardinality(&sort.index_sort) {
            Some(cardinality) if BigInt::from(keys.len()) >= cardinality => Ok(true),
            Some(_) => Ok(false),
            None => Err(
                "array equality with differing defaults needs index-domain coverage evidence"
                    .to_string(),
            ),
        }
    }

    fn array_select_at_sort(
        &self,
        array: &ArrayValue,
        index: &ModelValue,
        index_sort: &Sort,
    ) -> Result<ModelValue, String> {
        for (stored_index, value) in array.store.iter().rev() {
            if self.value_eq_at_sort(stored_index, index, index_sort)? {
                return Ok(value.clone());
            }
        }
        Ok(array.default.clone())
    }

    fn distinct_array_keys<'b>(
        &self,
        left: &'b ArrayValue,
        right: &'b ArrayValue,
        index_sort: &Sort,
    ) -> Result<Vec<&'b ModelValue>, String> {
        let mut distinct: Vec<&'b ModelValue> = Vec::new();
        for (key, _) in left.store.iter().chain(&right.store) {
            if !Self::model_value_can_index_sort(key, index_sort) {
                return Err("array store key does not inhabit the index sort".to_string());
            }
            let mut duplicate = false;
            for &seen in &distinct {
                if self.value_eq_at_sort(key, seen, index_sort)? {
                    duplicate = true;
                    break;
                }
            }
            if !duplicate {
                distinct.push(key);
            }
        }
        Ok(distinct)
    }

    fn index_sort_is_definitely_infinite(sort: &Sort) -> bool {
        matches!(sort, Sort::Int | Sort::Real | Sort::String | Sort::Seq(_))
    }

    /// Exact cardinality for the finite scalar carriers whose model values the
    /// independent checker can validate without consulting solver state.
    /// `None` means unknown here, not infinite; infinite carriers are handled
    /// separately above.
    fn known_finite_index_cardinality(sort: &Sort) -> Option<BigInt> {
        match sort {
            Sort::Bool => Some(BigInt::from(2u8)),
            Sort::BitVec(bitvec) => Some(BigInt::from(1u8) << bitvec.width as usize),
            Sort::Char => Some(BigInt::from(0x3_0000u32)),
            Sort::FiniteDomain(_, size) => Some(BigInt::from(*size)),
            Sort::Datatype(datatype)
                if datatype
                    .constructors
                    .iter()
                    .all(|constructor| constructor.fields.is_empty()) =>
            {
                Some(BigInt::from(datatype.constructors.len()))
            }
            _ => None,
        }
    }

    fn model_value_can_index_sort(value: &ModelValue, sort: &Sort) -> bool {
        match (value, sort) {
            (ModelValue::Bool(_), Sort::Bool) => true,
            (ModelValue::Int(_), Sort::Int) => true,
            (ModelValue::Real(_) | ModelValue::Algebraic(_), Sort::Real) => true,
            (ModelValue::BitVec { width, value }, Sort::BitVec(bitvec)) => {
                *width == bitvec.width
                    && !value.is_negative()
                    && value < &(BigInt::from(1u8) << bitvec.width as usize)
            }
            (ModelValue::Str(_), Sort::String) => true,
            (ModelValue::Seq(_), Sort::Seq(_)) => true,
            (ModelValue::Int(value), Sort::Char) => {
                !value.is_negative() && value < &BigInt::from(0x3_0000u32)
            }
            (ModelValue::Int(value), Sort::FiniteDomain(_, size)) => {
                !value.is_negative() && value < &BigInt::from(*size)
            }
            (ModelValue::Datatype { ctor, args }, Sort::Datatype(datatype)) => {
                datatype.constructors.iter().any(|constructor| {
                    constructor.name == *ctor && constructor.fields.len() == args.len()
                })
            }
            (ModelValue::Uninterpreted(_), Sort::Uninterpreted(_) | Sort::TypeVar(_)) => true,
            _ => false,
        }
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
                        (Ok(vx), Ok(vy))
                            if self.terms.sort(x) == self.terms.sort(y)
                                && self
                                    .value_eq_at_sort(&vx, &vy, self.terms.sort(x))
                                    .unwrap_or(false)
                    )
                })
            }
            _ => false,
        }
    }

    fn eval_distinct(&self, args: &[TermId], depth: usize) -> Result<ModelValue, String> {
        let Some(&first) = args.first() else {
            return Ok(ModelValue::Bool(true));
        };
        let operand_sort = self.terms.sort(first);
        if args[1..]
            .iter()
            .any(|&arg| self.terms.sort(arg) != operand_sort)
        {
            return Err("distinct operands have different sorts".to_string());
        }
        let vals = self.eval_all(args, depth)?;
        for i in 0..vals.len() {
            for j in (i + 1)..vals.len() {
                if self.value_eq_at_sort(&vals[i], &vals[j], operand_sort)? {
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
            // An ALGEBRAIC operand cannot be folded into a `BigRational` --
            // that is the lossy step that loses `sqrt(2)` -- so the sum/product
            // is carried in the extension instead. Rational operands are lifted
            // into it; a mix of two DIFFERENT extensions declines (resultants),
            // and declining is a coverage gap, never a wrong answer.
            "+" if vals.iter().any(is_algebraic) => fold_algebraic(&vals, AlgebraicFold::Sum),
            "*" if vals.iter().any(is_algebraic) => fold_algebraic(&vals, AlgebraicFold::Product),
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
                let [numerator, denominator] = vals.as_slice() else {
                    return Err("/ expects exactly two canonical operands".to_string());
                };
                let denominator = as_rational(denominator)?;
                if denominator.is_zero() {
                    // SMT-LIB leaves `(/ x 0)` unconstrained — it is an
                    // uninterpreted function on that input, not something
                    // to compute. This exact-zero branch alone mints the
                    // typed reason; adopt the model's choice, checked.
                    return self.division_by_zero(
                        term,
                        name,
                        args,
                        depth,
                        ProvenUnconstrainedKind::RealDivByZero,
                    );
                }
                let numerator = as_rational(numerator)?;
                // Result sort of `/` is Real.
                Ok(ModelValue::Real(numerator / denominator))
            }
            "div" => {
                let [a, b] = vals.as_slice() else {
                    return Err("div expects exactly two operands".to_string());
                };
                let (a, b) = (as_integer(a)?, as_integer(b)?);
                let Some((q, _)) = euclid(&a, &b) else {
                    return self.division_by_zero(
                        term,
                        name,
                        args,
                        depth,
                        ProvenUnconstrainedKind::IntDivByZero,
                    );
                };
                Ok(ModelValue::Int(q))
            }
            "mod" => {
                let [a, b] = vals.as_slice() else {
                    return Err("mod expects exactly two operands".to_string());
                };
                let (a, b) = (as_integer(a)?, as_integer(b)?);
                let Some((_, r)) = euclid(&a, &b) else {
                    return self.division_by_zero(
                        term,
                        name,
                        args,
                        depth,
                        ProvenUnconstrainedKind::IntModByZero,
                    );
                };
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
                // An algebraic operand is ORDERED by refining its isolating
                // interval, not by collapsing it to a rational. `sqrt(2) > 0`
                // is exactly the constraint reduction alone cannot settle --
                // both roots of `x^2 - 2` satisfy the same equalities and
                // differ only in sign.
                if vals.iter().any(is_algebraic) {
                    return compare_with_algebraic(name, &vals).map(ModelValue::Bool);
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

    /// Exact cardinality when it is provably finite and below `cap`.
    ///
    /// This is intentionally the same conservative classification used by the
    /// solver's Z3-compatible array-default pass. `None` means infinite,
    /// recursive/unknown, or at least `cap`; all three take Z3's large-domain
    /// store-default branch.
    fn finite_sort_cardinality_below(
        &self,
        sort: &Sort,
        cap: usize,
        in_progress: &mut Vec<String>,
    ) -> Option<usize> {
        match sort {
            Sort::Bool => (2 < cap).then_some(2),
            Sort::BitVec(bitvec) => {
                if bitvec.width as usize >= cap.trailing_zeros() as usize {
                    None
                } else {
                    Some(1usize << bitvec.width)
                }
            }
            Sort::FiniteDomain(_, size) => {
                let size = usize::try_from(*size).ok()?;
                (size < cap).then_some(size)
            }
            Sort::Array(array) => {
                let index =
                    self.finite_sort_cardinality_below(&array.index_sort, cap, in_progress)?;
                let element =
                    self.finite_sort_cardinality_below(&array.element_sort, cap, in_progress)?;
                let mut total = 1usize;
                for _ in 0..index {
                    total = total.checked_mul(element)?;
                    if total >= cap {
                        return None;
                    }
                }
                Some(total)
            }
            Sort::Datatype(datatype) => self.datatype_cardinality_below(datatype, cap, in_progress),
            Sort::Uninterpreted(name) => {
                let datatype = self.model.datatype_def(name)?;
                self.datatype_cardinality_below(&datatype, cap, in_progress)
            }
            _ => None,
        }
    }

    fn datatype_cardinality_below(
        &self,
        datatype: &ay_core::DatatypeSort,
        cap: usize,
        in_progress: &mut Vec<String>,
    ) -> Option<usize> {
        if datatype.constructors.is_empty() || in_progress.iter().any(|name| name == &datatype.name)
        {
            return None;
        }
        in_progress.push(datatype.name.clone());
        let result = (|| {
            let mut total = 0usize;
            for constructor in &datatype.constructors {
                let mut variants = 1usize;
                for field in &constructor.fields {
                    let count =
                        self.finite_sort_cardinality_below(&field.sort, cap, in_progress)?;
                    variants = variants.checked_mul(count)?;
                    if variants >= cap {
                        return None;
                    }
                }
                total = total.checked_add(variants)?;
                if total >= cap {
                    return None;
                }
            }
            Some(total)
        })();
        in_progress.pop();
        result
    }

    /// Evaluate an array else-value without touching irrelevant store writes.
    ///
    /// Z3 5.0.0 preserves the base default for infinite/large carriers, but a
    /// small finite carrier uses a shared-epsilon select and a unit carrier uses
    /// the stored value. The finite case therefore reads the solver's committed
    /// scalar application value instead of unsoundly peeling the store.
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

        // A binder-dependent lambda has no finite `(else, stores)`
        // representation, but SMT-LIB still exposes `(default lambda)` as an
        // opaque scalar application.  Re-check the model's committed scalar
        // value directly instead of trying (and failing) to reconstruct the
        // whole lambda array.  The value is not invented here: an unpinned
        // default remains unevaluable, and the gate still compares the pin
        // against every authored assertion.
        if let TermData::App(sym, args) = self.terms.get(array) {
            let dependent_lambda = sym.name() == "lambda-array"
                && args.len() == 2
                && self.term_contains(args[1], args[0]);
            let as_array = sym.name().starts_with("as-array[");
            if dependent_lambda || as_array {
                return self
                    .model
                    .uf_app_value(term)
                    .ok_or_else(|| "model does not pin opaque array default".to_string());
            }
        }

        let mut current = array;
        let mut seen = HashSet::new();
        while seen.insert(current) {
            if depth + seen.len() > MAX_EVAL_DEPTH {
                return Err("array default evaluation depth exceeded".to_string());
            }
            match self.terms.get(current) {
                TermData::App(sym, args) if sym.name() == "store" && args.len() == 3 => {
                    let Sort::Array(array_sort) = self.terms.sort(current) else {
                        return Err("store result is not an array sort".to_string());
                    };
                    match self.finite_sort_cardinality_below(
                        &array_sort.index_sort,
                        1 << 14,
                        &mut Vec::new(),
                    ) {
                        Some(1) => return self.eval(args[2], depth + seen.len()),
                        Some(_) => {
                            return self.model.uf_app_value(term).ok_or_else(|| {
                                "model does not pin finite array default".to_string()
                            });
                        }
                        None => current = args[0],
                    }
                }
                TermData::App(sym, args) if sym.name() == "const-array" && args.len() == 1 => {
                    return self.eval(args[0], depth + seen.len());
                }
                _ => {
                    return match self.eval_array_value(current, depth + seen.len()) {
                        Ok(array) => Ok(array.default),
                        // A named/defined array can hide the lambda syntax from
                        // the fast path above. If resolving that alias proves
                        // that its value is a binder-dependent lambda, its
                        // `default` is still the same opaque scalar operation;
                        // use only the model's committed value for this exact
                        // application. Other reconstruction failures remain
                        // fail-closed and never gain this fallback.
                        Err(reason)
                            if reason
                                == "binder-dependent lambda-array has no finite array representation" =>
                        {
                            self.model.uf_app_value(term).ok_or(reason)
                        }
                        Err(reason) => Err(reason),
                    };
                }
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
                if *at == array_term
                    && congruence_keys_equal(
                        std::slice::from_ref(key_idx),
                        std::slice::from_ref(idx),
                    )?
                {
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
            // `str.replace_re` / `str.replace_re_all`.
            //
            // RegLan has no `ModelValue`, so a regex argument cannot be
            // evaluated as a value; like `str.in_re` two arms below, these pass
            // the regex term STRUCTURALLY to this crate's own interval matcher.
            // The SMT-LIB clause (leftmost, then shortest, match) and the one
            // shape that is deliberately left failing closed (a regex accepting
            // the empty word) are documented on [`crate::regex::replace`].
            //
            // This previously accepted only `(str.to_re <non-empty literal>)`
            // and reported `Unevaluable` for every other regex, so the gate
            // refused to confirm any model mentioning one and published a
            // computed `sat` as `unknown`.
            "str.replace_re" | "str.replace_re_all" => {
                let [subject, regex, replacement] = exactly(args)?;
                let subject = self.eval_str(subject, depth + 1)?;
                let replacement = self.eval_str(replacement, depth + 1)?;
                let out = crate::regex::replace(
                    self.terms,
                    name,
                    &subject,
                    regex,
                    &replacement,
                    name == "str.replace_re_all",
                    depth + 1,
                    |term| self.eval_str(term, depth + 2),
                )?;
                Ok(ModelValue::Str(out))
            }
            "str.in_re" | "str.in.re" => {
                let [subject, regex] = exactly(args)?;
                let subject = self.eval_str(subject, depth + 1)?;
                let member =
                    crate::regex::matches(self.terms, &subject, regex, depth + 1, |term| {
                        self.eval_str(term, depth + 2)
                    })?;
                Ok(ModelValue::Bool(member))
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
                if f == name && congruence_keys_equal(keys, std::slice::from_ref(key))? {
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

/// The exact value of an indexed FP special constant, if `name` is one.
///
/// `(_ NaN eb sb)`, `(_ +zero eb sb)`, `(_ -zero eb sb)`, `(_ +oo eb sb)` and
/// `(_ -oo eb sb)` are the SMT-LIB spellings of the FP special values. They are
/// nullary CONSTANTS, but they are `Symbol::Indexed`, and the gate routed every
/// indexed symbol to the bitvector operator table — where they are, correctly,
/// unrecognized. The gate then could not confirm any model mentioning one and
/// degraded the verdict, so `(assert (fp.isNaN (_ NaN 11 53)))` was published
/// as `unknown` even though AY refutes its negation as `unsat`.
///
/// SMT-LIB counts the hidden bit in `sb`, so the stored fraction field is
/// `sb - 1` bits. NaN is a single value in the FP sort (payloads are not
/// observable), so the canonical quiet NaN is an exact representative.
///
/// Returns `None` for any other indexed symbol, which keeps the bitvector path
/// and the gate's fail-closed discipline untouched: an out-of-range width
/// declines here rather than producing a truncated value.
fn fp_special_constant(name: &str, indices: &[u32]) -> Option<ModelValue> {
    let [eb, sb] = <[u32; 2]>::try_from(indices).ok()?;
    // `exponent` and `significand` are `u64`: an all-ones exponent needs
    // `eb <= 64`, and the stored fraction field is `sb - 1` bits wide. A quiet
    // NaN additionally needs a fraction bit to set, hence `sb >= 2`.
    if eb == 0 || eb > 64 || !(2..=65).contains(&sb) {
        return None;
    }
    let all_ones = if eb == 64 { u64::MAX } else { (1u64 << eb) - 1 };
    let (sign, exponent, significand) = match name {
        "+zero" => (false, 0, 0),
        "-zero" => (true, 0, 0),
        "+oo" => (false, all_ones, 0),
        "-oo" => (true, all_ones, 0),
        "NaN" => (false, all_ones, 1u64 << (sb - 2)),
        _ => return None,
    };
    Some(ModelValue::FloatingPoint {
        sign,
        exponent,
        significand,
        exponent_bits: eb,
        significand_bits: sb,
    })
}

/// Reinterpret an `eb + sb`-wide bitvector as the IEEE fields of an FP value.
///
/// This is SMT-LIB `((_ to_fp eb sb) <bv>)`: a pure re-reading of the same
/// bits, with no rounding and no value change. Splitting them out here keeps
/// the gate independent of the solver's FP code.
///
/// Declines (returns `None`) unless the operand is a bitvector of EXACTLY the
/// width the indices call for, and unless both fields fit the `u64` slots of
/// [`ModelValue::FloatingPoint`]. A width mismatch is a malformed term rather
/// than something to coerce, so it falls through and fails closed.
fn fp_from_ieee_bits(indices: &[u32], value: &ModelValue) -> Option<ModelValue> {
    let [eb, sb] = <[u32; 2]>::try_from(indices).ok()?;
    if eb == 0 || eb > 64 || !(2..=65).contains(&sb) {
        return None;
    }
    let ModelValue::BitVec { width, value } = value else {
        return None;
    };
    if *width != eb + sb {
        return None;
    }
    let fraction_bits = sb - 1;
    let exponent_mask = if eb == 64 { u64::MAX } else { (1u64 << eb) - 1 };
    let fraction_mask = if fraction_bits == 64 {
        u64::MAX
    } else {
        (1u64 << fraction_bits) - 1
    };
    // `value` is normalized to `0 <= value < 2^width` by construction, so these
    // shifts stay in range and both fields are guaranteed to fit their masks.
    let sign = ((value >> (eb + sb - 1) as usize) & BigInt::from(1u8)) == BigInt::from(1u8);
    let exponent =
        u64::try_from((value >> fraction_bits as usize) & BigInt::from(exponent_mask)).ok()?;
    let significand = u64::try_from(value & BigInt::from(fraction_mask)).ok()?;
    Some(ModelValue::FloatingPoint {
        sign,
        exponent,
        significand,
        exponent_bits: eb,
        significand_bits: sb,
    })
}

/// Whether `value` is a floating-point ZERO in the same format as `like`.
///
/// The residue [`Evaluator::eval_fp`] checks after adopting the model's choice
/// for `fp.min`/`fp.max` of `+0` and `-0`. SMT-LIB frees WHICH zero comes back;
/// it does not free the result from being a zero of that format at all, so a
/// model answering `1.0` there is still refuted. Deliberately written from the
/// raw fields rather than routed through [`crate::fp`]: the check must hold
/// even for a format that module's arithmetic envelope declines.
fn is_zero_of_format(value: &ModelValue, like: &ModelValue) -> bool {
    let (
        &ModelValue::FloatingPoint {
            exponent,
            significand,
            exponent_bits,
            significand_bits,
            ..
        },
        &ModelValue::FloatingPoint {
            exponent_bits: like_eb,
            significand_bits: like_sb,
            ..
        },
    ) = (value, like)
    else {
        return false;
    };
    exponent == 0 && significand == 0 && exponent_bits == like_eb && significand_bits == like_sb
}

/// How many values the ELEMENT sort of a set carrier has.
///
/// A set is modelled as `(Array T Bool)`, so this is the cardinality of `T`.
/// `crate::sets` needs it to decide whether an index exists that neither
/// operand's store overrides — a fact about the sort, which the VALUE cannot
/// carry.
///
/// Unknown beats a guess: an uninterpreted sort has whatever cardinality the
/// model gives it, and claiming it is infinite would decide `set.subset` on an
/// assumption rather than on the model.
fn element_domain_size(sort: &Sort) -> crate::sets::DomainSize {
    use crate::sets::DomainSize;
    let Sort::Array(array) = sort else {
        return DomainSize::Unknown;
    };
    match &array.index_sort {
        Sort::Bool => DomainSize::Finite(BigInt::from(2u8)),
        Sort::BitVec(bv) => DomainSize::Finite(BigInt::from(1u8) << bv.width as usize),
        // A floating-point sort is finite, but its distinct VALUES are fewer
        // than its bit patterns (all the NaN encodings are one value), so its
        // exact cardinality is not `2^(eb+sb)`. Unknown rather than wrong.
        Sort::FloatingPoint(_, _) => DomainSize::Unknown,
        Sort::Int | Sort::Real | Sort::String => DomainSize::Infinite,
        _ => DomainSize::Unknown,
    }
}

/// Destructure exactly `N` arguments, or fail closed.
fn exactly<const N: usize>(args: &[TermId]) -> Result<[TermId; N], String> {
    <[TermId; N]>::try_from(args).map_err(|_| format!("expected {N} arguments, got {}", args.len()))
}

/// Evaluate a comparison chain where at least one operand is algebraic.
///
/// Each adjacent pair is decided by the SIGN of `a - b`, computed by interval
/// refinement. An undecided sign (the refinement budget ran out, or the pair
/// spans two different extensions) is an error the gate fails closed on --
/// never a `false`, which would be an unearned refutation.
fn compare_with_algebraic(name: &str, vals: &[ModelValue]) -> Result<bool, String> {
    use core::cmp::Ordering;

    let carrier = vals
        .iter()
        .find_map(|v| match v {
            ModelValue::Algebraic(a) => Some(a.as_ref().clone()),
            _ => None,
        })
        .ok_or_else(|| "no algebraic operand".to_string())?;

    let lift = |v: &ModelValue| -> Result<crate::algebraic::Algebraic, String> {
        match v {
            ModelValue::Algebraic(a) => Ok(a.as_ref().clone()),
            other => Ok(carrier.with_rational(as_rational(other)?)),
        }
    };

    for pair in vals.windows(2) {
        let difference = lift(&pair[0])?
            .add(&lift(&pair[1])?.neg())
            .map_err(|e| format!("algebraic comparison declined: {e:?}"))?;
        let ordering = difference
            .sign()
            .map(|s| match s {
                0 => Ordering::Equal,
                n if n < 0 => Ordering::Less,
                _ => Ordering::Greater,
            })
            .ok_or_else(|| "algebraic sign undecided within the refinement budget".to_string())?;
        let holds = match name {
            "<" => ordering == Ordering::Less,
            "<=" => ordering != Ordering::Greater,
            ">" => ordering == Ordering::Greater,
            ">=" => ordering != Ordering::Less,
            _ => return Err(format!("unsupported comparison {name}")),
        };
        if !holds {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Whether a value carries an algebraic number.
fn is_algebraic(v: &ModelValue) -> bool {
    matches!(v, ModelValue::Algebraic(_))
}

/// Which fold `fold_algebraic` performs.
enum AlgebraicFold {
    Sum,
    Product,
}

/// Fold a mixed list of algebraic and rational operands inside one extension.
///
/// Every rational is lifted into the algebraic operand's extension, so exact
/// arithmetic applies throughout. The result collapses back to `Real` when it
/// reduces to a rational -- `sqrt(2) * sqrt(2)` IS 2 -- so downstream
/// comparisons see the simplest exact form.
fn fold_algebraic(vals: &[ModelValue], fold: AlgebraicFold) -> Result<ModelValue, String> {
    let first = vals
        .iter()
        .find_map(|v| match v {
            ModelValue::Algebraic(a) => Some(a.as_ref().clone()),
            _ => None,
        })
        .ok_or_else(|| "no algebraic operand".to_string())?;

    let mut acc = match fold {
        AlgebraicFold::Sum => first.with_rational(BigRational::zero()),
        AlgebraicFold::Product => first.with_rational(BigRational::from(BigInt::from(1))),
    };
    for v in vals {
        let operand = match v {
            ModelValue::Algebraic(a) => a.as_ref().clone(),
            other => first.with_rational(as_rational(other)?),
        };
        acc = match fold {
            AlgebraicFold::Sum => acc.add(&operand),
            AlgebraicFold::Product => acc.mul(&operand),
        }
        .map_err(|e| format!("algebraic arithmetic declined: {e:?}"))?;
    }
    Ok(match acc.as_rational() {
        Some(q) => ModelValue::Real(q),
        None => ModelValue::Algebraic(Box::new(acc)),
    })
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
