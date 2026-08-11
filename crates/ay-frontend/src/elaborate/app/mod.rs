// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;

use crate::command::Term as ParsedTerm;
use ay_core::{Constant, Sort, Symbol, TermData, TermId};

use super::{Context, ElaborateError, Result, SymbolInfo, MAX_FUN_EXPANSION_DEPTH};

mod arithmetic;
mod bitvectors;
mod core;
mod floating_point;
mod map;
mod multiset;
mod sequences;
mod set;
mod strings;

impl Context {
    /// Elaborate a function application
    /// Whether two sorts are DEFINITIVELY structurally incompatible — a
    /// genuine ill-sortedness, not a coercion or under-determination. Returns
    /// `true` ONLY for: distinct datatype/uninterpreted sort NAMES (e.g.
    /// `VecIter_Slice_bv40` vs `Iter_lt_PbLit`), a datatype/uninterpreted sort
    /// against a non-datatype scalar, or distinct BitVec widths. Every other
    /// pair (Int/Real coercions, Array, matching sorts, anything involving a
    /// sort family this check does not model) returns `false`, so the
    /// conservative caller never rejects a legitimately-typed application.
    fn sorts_definitively_incompatible(a: &Sort, b: &Sort) -> bool {
        fn dt_name(s: &Sort) -> Option<&str> {
            match s {
                Sort::Uninterpreted(n) => Some(n.as_str()),
                Sort::Datatype(dt) => Some(dt.name.as_str()),
                _ => None,
            }
        }
        match (dt_name(a), dt_name(b)) {
            // Both name a datatype/uninterpreted sort: incompatible iff the
            // names differ.
            (Some(na), Some(nb)) => na != nb,
            // Exactly one is a datatype/uninterpreted sort and the other is a
            // concrete scalar (BitVec/Bool/Int/Real): a datatype field can never
            // hold such a value — incompatible.
            (Some(_), None) | (None, Some(_)) => matches!(
                if dt_name(a).is_some() { b } else { a },
                Sort::BitVec(_) | Sort::Bool | Sort::Int | Sort::Real
            ),
            // Neither is a datatype/uninterpreted sort: only flag a definitive
            // BitVec width mismatch; leave Int/Real (coercible) and everything
            // else to the existing permissive path.
            (None, None) => match (a, b) {
                (Sort::BitVec(wa), Sort::BitVec(wb)) => wa.width != wb.width,
                _ => false,
            },
        }
    }

    /// Check a declared function's complete domain and insert only the
    /// SMT-LIB Int-to-Real coercion. Generic applications used to trust the
    /// declaration's result sort without checking either arity or operand
    /// sorts, allowing an ill-sorted term such as `f(true)` for `f : Int ->
    /// Bool` to reach `check-sat` and receive a definitive verdict.
    pub(super) fn validate_application_signature(
        &mut self,
        name: &str,
        expected_sorts: &[Sort],
        args: &mut [TermId],
    ) -> Result<()> {
        if expected_sorts.len() != args.len() {
            return Err(ElaborateError::InvalidConstant(format!(
                "{name} requires {} arguments, got {}",
                expected_sorts.len(),
                args.len()
            )));
        }
        for (arg, expected) in args.iter_mut().zip(expected_sorts.iter()) {
            let actual = self.terms.sort(*arg).clone();
            if &actual == expected {
                continue;
            }
            if self.int_real_coercions() && actual == Sort::Int && expected == &Sort::Real {
                *arg = self.coerce_int_to_real(*arg);
                continue;
            }
            return Err(ElaborateError::SortMismatch {
                expected: expected.to_string(),
                actual: actual.to_string(),
            });
        }
        Ok(())
    }

    fn validate_declared_application(
        &mut self,
        name: &str,
        info: &SymbolInfo,
        args: &mut [TermId],
    ) -> Result<()> {
        self.validate_application_signature(name, &info.arg_sorts, args)
    }

    pub(super) fn elaborate_app(
        &mut self,
        name: &str,
        args: &[ParsedTerm],
        env: &HashMap<String, TermId>,
    ) -> Result<TermId> {
        if let Some((params, result_sort, body)) = self.fun_defs.get(name).cloned() {
            if params.len() != args.len() {
                return Err(ElaborateError::InvalidConstant(format!(
                    "{name} requires {} arguments, got {}",
                    params.len(),
                    args.len()
                )));
            }
            // Guard against unbounded recursion in define-fun-rec (#8622)
            if self.fun_expansion_depth >= MAX_FUN_EXPANSION_DEPTH {
                return Err(ElaborateError::RecursionDepthExceeded(
                    MAX_FUN_EXPANSION_DEPTH,
                ));
            }
            self.fun_expansion_depth += 1;
            let mut arg_ids = Vec::with_capacity(args.len());
            for arg in args {
                match self.elaborate_term(arg, env) {
                    Ok(arg) => arg_ids.push(arg),
                    Err(error) => {
                        self.fun_expansion_depth -= 1;
                        return Err(error);
                    }
                }
            }
            let expected_sorts: Vec<Sort> = params.iter().map(|(_, sort)| sort.clone()).collect();
            if let Err(error) =
                self.validate_application_signature(name, &expected_sorts, &mut arg_ids)
            {
                self.fun_expansion_depth -= 1;
                return Err(error);
            }
            // MACRO EXPANSION IS CAPTURE-AVOIDING (SMT-LIB 2.6 §4.2.2): a
            // `define-fun` body's symbols resolve against the signature as it
            // stood AT DEFINITION TIME — its own parameters plus the globals —
            // never against the USE SITE. So the body is elaborated in a FRESH
            // local environment holding only the parameter bindings, exactly
            // the environment `validate_defined_function_body` type-checks it
            // in (declarations.rs).
            //
            // Starting from `env.clone()` (the use-site environment) leaked
            // every enclosing binder — quantifier variables, `let` bindings and
            // `match` pattern variables — into the body, so a body reference to
            // a GLOBAL constant was captured by any same-named binder around the
            // call. That was a wrong-verdict defect in BOTH directions:
            //   (declare-const x Int) (define-fun f () Int x)
            //   (assert (forall ((x Int)) (= f 11)))
            //     is SAT (take the global x = 11); ay answered `unsat`.
            //   … plus (assert (= x 11)) (assert (exists ((x Int)) (not (= f 11))))
            //     is UNSAT; ay answered `sat` with a falsifying model.
            // AY also disagreed with ITSELF: the standard's own expansion of the
            // same script — `(declare-fun f () Int)` + `(assert (= f x))` —
            // answered `sat`.
            let mut new_env = HashMap::default();
            for ((param_name, _), arg_id) in params.iter().zip(arg_ids) {
                new_env.insert(param_name.clone(), arg_id);
            }
            let result = self.elaborate_term(&body, &new_env).and_then(|body_term| {
                let actual = self.terms.sort(body_term).clone();
                if actual == result_sort {
                    Ok(body_term)
                } else if self.int_real_coercions()
                    && actual == Sort::Int
                    && result_sort == Sort::Real
                {
                    Ok(self.coerce_int_to_real(body_term))
                } else {
                    Err(ElaborateError::SortMismatch {
                        expected: result_sort.to_string(),
                        actual: actual.to_string(),
                    })
                }
            });
            self.fun_expansion_depth -= 1;
            return result;
        }

        // Short-circuit `ite` when the condition elaborates to a constant
        // boolean: elaborate ONLY the taken branch. This is load-bearing for
        // `define-fun-rec`: a terminating recursion (e.g. factorial) only
        // terminates during macro expansion if the UNtaken branch — which holds
        // the recursive call — is never elaborated once the guard is decided.
        // Without it, `(ite (= n 0) 1 (* n (fact (- n 1))))` keeps expanding the
        // else-branch even at n=0, exhausting MAX_FUN_EXPANSION_DEPTH. (`mk_ite`
        // already folds a constant condition, but only AFTER both branches are
        // built — too late to stop the runaway recursion.) A non-constant guard
        // falls through to the normal eager elaboration below, so symbolic ITEs
        // are unaffected.
        let builtin_ite_spelling =
            name == "ite" || name == "if" || (self.logic.is_none() && name == "if_then_else");
        if builtin_ite_spelling
            && !self.symbols.contains_key(name)
            && !self.overloaded_symbols.contains_key(name)
            && args.len() == 3
        {
            let cond = self.elaborate_term(&args[0], env)?;
            match self.terms.get(cond) {
                TermData::Const(Constant::Bool(true)) => {
                    return self.elaborate_term(&args[1], env);
                }
                TermData::Const(Constant::Bool(false)) => {
                    return self.elaborate_term(&args[2], env);
                }
                _ => {}
            }
        }

        // A multi-variable lambda may only curry (into the nested lambda-array
        // shape `ho_unfold` consumes) when it is the DIRECT function argument
        // (position 0) of a higher-order sequence combinator. Everywhere else a
        // curried lambda diverges from z3, so it fails closed to `unknown` (see
        // the Lambda arm in `term.rs`). Set the permission only for arg 0 of
        // these ops; the Lambda arm resets it before descending into the body,
        // and every nested `elaborate_app` re-establishes it per position, so
        // it never leaks. (#p1.5-curried-lambda-gate)
        let ho_seq_fn_arg = matches!(
            name,
            "seq.foldl"
                | "seq.fold_left"
                | "seq.foldli"
                | "seq.fold_lefti"
                | "seq.map"
                | "seq.mapi"
        );
        let mut arg_ids: Vec<TermId> = Vec::with_capacity(args.len());
        for (i, a) in args.iter().enumerate() {
            let saved = self.multivar_lambda_curry_allowed;
            self.multivar_lambda_curry_allowed = ho_seq_fn_arg && i == 0;
            let r = self.elaborate_term(a, env);
            self.multivar_lambda_curry_allowed = saved;
            arg_ids.push(r?);
        }

        // A BARE parametric-datatype constructor application (e.g. `(some true)`,
        // `(mk 1 true)`) names no instance sort, so lazy monomorphization is not
        // otherwise triggered. Infer the instance from the argument sorts and
        // register it here so the constructor resolves to it (and gets its
        // injectivity/distinctness axioms). No-op unless `name` is a parametric
        // constructor; never guesses an undetermined (phantom) instance.
        self.ensure_parametric_constructor_instance(name, &arg_ids)?;

        // Resolve a datatype constructor/selector/tester to its INSTANCE-SPECIFIC
        // internal symbol name (mangled, e.g. `osome@Opt!{Bool}`), so the term is
        // name-disjoint per parametric instantiation and the DT theory treats each
        // instance as its own datatype. Surface name is returned unchanged for
        // monomorphic datatypes and non-datatype symbols. Resolved once and reused
        // for both the selector-fold below and the application build.
        let overload = self.resolve_overloaded_symbol(name, &arg_ids)?;
        let app_name: String = self.datatype_internal_name(name, &arg_ids, overload.as_ref());

        // SOUNDNESS (ill-sorted datatype constructor): reject a constructor
        // application whose argument sorts CLEARLY disagree with the declared
        // field sorts. SMT-LIB requires an ill-sorted term to be rejected;
        // accepting it lets a downstream consumer trust a definitive verdict on
        // ill-formed input — a latent false-verify surface (surfaced by a
        // model-checker-consumer codegen bug that applied `Copied_..._mk` (field sort
        // `Iter_lt_PbLit`) to a `VecIter_Slice_bv40` value, which ay solved to a
        // spurious base-UNSAT while z3 rejected the term outright). The check is
        // CONSERVATIVE — it fires only on a DEFINITIVE structural mismatch
        // (distinct datatype/uninterpreted sort names, or distinct BitVec
        // widths), so arithmetic coercions (Int/Real) and every other
        // sort combination keep their existing behavior. Uses the resolved
        // internal name so parametric instances are checked against their own
        // (monomorphized) field sorts.
        if self.is_constructor(name).is_some() {
            if let Some(field_info) = self.constructor_selector_info(&app_name) {
                if field_info.len() == arg_ids.len() {
                    let expected: Vec<Sort> = field_info.iter().map(|(_, s)| s.clone()).collect();
                    for (&arg, field_sort) in arg_ids.iter().zip(expected.iter()) {
                        let arg_sort = self.terms.sort(arg).clone();
                        if Self::sorts_definitively_incompatible(&arg_sort, field_sort) {
                            return Err(ElaborateError::SortMismatch {
                                expected: format!("{field_sort:?}"),
                                actual: format!("{arg_sort:?}"),
                            });
                        }
                    }
                }
            }
        }

        // Algebraic-datatype selector-over-constructor reduction:
        //   sel_i(C(t_0, .., t_n))  ->  t_i
        // When `name` is a selector and its single argument is an application of
        // the constructor that OWNS that selector, return the matching field
        // directly (the SMT-LIB datatype selector axiom). Folding this at
        // elaboration makes datatype construct+select goals DECIDABLE — a
        // selector left as an opaque `App` over a constructor literal otherwise
        // leaves the solver to answer `unknown`. Done before symbol dispatch so
        // it fires for selectors whether they resolve as overloaded or as plain
        // single-datatype symbols.
        //
        // Datatype sorts are `Sort::Uninterpreted(name)` here (the full
        // constructor/field structure is not on the term sort), so the
        // constructor -> ordered-selectors mapping comes from `ctor_selectors`.
        // Soundness: we fold ONLY when the applied constructor owns `name`. A
        // selector applied to a different constructor of a multi-constructor
        // datatype is unspecified in SMT-LIB and produces no `position` match
        // here, so it stays opaque for the existing selector-axiom path.
        if arg_ids.len() == 1 {
            // Datatype tester-over-constructor fold:
            //   is-C(D(t..)) / is-C(<nullary D>)  ->  true iff C == D, false if
            //   C and D are distinct constructors of the SAME datatype.
            // Testers are exhaustive and mutually exclusive over a datatype's
            // constructors, so this is a VALID fold. It is LOAD-BEARING for
            // `define-fun-rec` over datatypes: the recursion's `ite` guard
            // `((_ is nil) l)` must fold to a CONSTANT so the ite short-circuit
            // above elaborates only the taken branch — otherwise the recursive
            // else-branch expands to MAX_FUN_EXPANSION_DEPTH and the call fails
            // closed to `unknown`. `ctor_of_term` recognizes both constructor
            // applications and nullary constructors (which elaborate to Vars,
            // matched TermId-exactly so name shadowing cannot fold unsoundly).
            // `app_name` is the instance-internal resolved name, so parametric
            // instances fold against their own constructors. (#rec-dt-expansion)
            if let Some(tester_ctor) = app_name.strip_prefix("is-") {
                if let Some((tester_dt, _)) = self.is_constructor(tester_ctor) {
                    if let Some(arg_ctor) = self.ctor_of_term(arg_ids[0]) {
                        if let Some((arg_dt, _)) = self.is_constructor(&arg_ctor) {
                            if tester_dt == arg_dt {
                                return Ok(if arg_ctor == tester_ctor {
                                    self.terms.true_term()
                                } else {
                                    self.terms.false_term()
                                });
                            }
                        }
                    }
                }
            }
            let inner = self.terms.get(arg_ids[0]).clone();
            if let TermData::App(Symbol::Named(ctor_name), cargs) = &inner {
                if let Some(sels) = self.ctor_selectors.get(ctor_name) {
                    if let Some(idx) = sels.iter().position(|s| s.as_str() == app_name) {
                        if let Some(&field) = cargs.get(idx) {
                            return Ok(field);
                        }
                    }
                }
            }
            // Selector-over-ite distribution:
            //   sel(ite(c, X, Y))  ->  ite(c, sel(X), sel(Y))
            // applied recursively to constructor leaves so `sel(C(t..)) -> t_i`
            // fires on each branch, yielding a DATATYPE-FREE result. A bounded
            // model checker emits closure-environment SSA selects of exactly this
            // shape — `(cap_i (ite c (Closure_mk ..) (Closure_mk ..)))` — and
            // without this distribution the selector stays an opaque `App` over an
            // `ite`: the solver treats it as a free Tseitin variable, so the
            // captured field is left UNCONSTRAINED (the model defaults it, and the
            // strict datatype-field validator then refutes a precondition that
            // reads the capture — demoting a decidable VC to `unknown`). Only fires
            // when BOTH branches fold to fields, so nothing is left opaque or
            // duplicated unsoundly. (#selector-over-ite)
            if let TermData::Ite(c, x, y) = inner {
                if let (Some(fx), Some(fy)) = (
                    self.try_fold_selector(&app_name, x),
                    self.try_fold_selector(&app_name, y),
                ) {
                    return Ok(self.terms.mk_ite(c, fx, fy));
                }
            }
        }

        // Datatype equality folding (constructor injectivity + distinctness),
        // distributed through `ite`. Rewrites a datatype `=` to a DATATYPE-FREE
        // formula so the combined scalar/UF solver decides it:
        //   C(a..) = C(b..)   ->  (and (= a_i b_i))    [true when 0 fields]
        //   C(a..) = D(b..)   ->  false                (C != D, same datatype)
        //   t = (ite c X Y)   ->  (ite c (= t X) (= t Y))
        // Only datatype-sorted equalities are touched; scalar `=` is untouched.
        // The axiom path (F1/H) only fires for TOP-LEVEL asserted constructor
        // equalities; folding here additionally decides ones nested inside
        // ite/and/or/not — exactly the closure-environment SSA chains a bounded
        // model checker emits (`local = ite(c, C(..), <havoc'd dt var>)`), which
        // otherwise leave the solver `unknown`.
        let builtin_eq_spelling =
            name == "=" || (self.logic.is_none() && matches!(name, "equals" | "equiv" | "iff"));
        if builtin_eq_spelling
            && !self.symbols.contains_key(name)
            && !self.overloaded_symbols.contains_key(name)
            && arg_ids.len() == 2
            && self.is_datatype_sorted(arg_ids[0])
        {
            // z3 4.15.4 parity: a datatype `=` whose operands have DIFFERENT
            // sorts (e.g. `(= dt 5)`, dt vs Int) is a sort error, reported before
            // the datatype fold ever runs. Datatypes are non-coercible, so the
            // rule is exact sort identity: `(= a (ite c X Y))` over the SAME
            // datatype passes (both sides carry that datatype sort), and the
            // recursion in fold_datatype_eq handles the ite distribution.
            if !self.lenient_sort_coercions()
                && self.terms.sort(arg_ids[0]) != self.terms.sort(arg_ids[1])
            {
                return Err(ElaborateError::SortMismatch {
                    expected: self.terms.sort(arg_ids[0]).to_string(),
                    actual: self.terms.sort(arg_ids[1]).to_string(),
                });
            }
            return Ok(self.fold_datatype_eq(arg_ids[0], arg_ids[1]));
        }

        if let Some(info) = overload {
            self.validate_declared_application(name, &info, &mut arg_ids)?;
            if arg_ids.is_empty() {
                if let Some(term) = info.term {
                    return Ok(term);
                }
            }
            return Ok(self
                .terms
                .mk_app(Symbol::named(&app_name), arg_ids, info.sort));
        }

        if let Some(info) = self.symbols.get(name).cloned() {
            self.validate_declared_application(name, &info, &mut arg_ids)?;
            if arg_ids.is_empty() {
                if let Some(term) = info.term {
                    return Ok(term);
                }
            }
            let sort = info.sort;
            let declared_app_name = info.internal_name.unwrap_or_else(|| app_name.clone());
            // A USER-declared `to_real` (deliberately declarable — it is a
            // valid `(_ map f)` target) builds an App byte-identical to the
            // builtin's. Mark the store so the to_real-integrality rewrites
            // in the comparison/equality constructors stand down — they
            // would otherwise fabricate semantics for this free function
            // (a wrong-verdict class). This runs while elaborating the
            // ARGUMENT of any enclosing comparison, i.e. strictly before
            // the constructor that would rewrite it (bottom-up
            // elaboration), so ordering is safe. (#to-real-bridge)
            if name == "to_real" {
                self.terms.mark_to_real_shadowed();
            }
            // A USER-declared `is_int` (also declarable — see
            // EXCLUDED_DECLARABLE_OP_NAMES "map-target") builds an App
            // byte-identical to the builtin's. Mark the store so the
            // `is_int` quantifier eliminator (ay-dpll::qe::isint) stands
            // down — applying integrality (critical-residue) reasoning to
            // this free predicate fabricates its semantics (a confirmed
            // wrong-UNSAT class). Same discipline/ordering as to_real
            // above. (#isint-shadow)
            if name == "is_int" {
                self.terms.mark_is_int_shadowed();
            }
            return Ok(self
                .terms
                .mk_app(Symbol::named(&declared_app_name), arg_ids, sort));
        }

        if let Some(term) = self.try_elaborate_core_app(name, &mut arg_ids)? {
            return Ok(term);
        }
        if let Some(term) = self.try_elaborate_string_or_regex_app(name, &mut arg_ids)? {
            return Ok(term);
        }
        if let Some(term) = self.try_elaborate_sequence_app(name, &mut arg_ids)? {
            return Ok(term);
        }
        if let Some(term) = self.try_elaborate_set_app(name, &arg_ids)? {
            return Ok(term);
        }
        if let Some(term) = self.try_elaborate_multiset_app(name, &arg_ids)? {
            return Ok(term);
        }
        if let Some(term) = self.try_elaborate_map_app(name, &arg_ids)? {
            return Ok(term);
        }
        if let Some(term) = self.try_elaborate_arithmetic_app(name, &mut arg_ids)? {
            return Ok(term);
        }
        if let Some(term) = self.try_elaborate_bitvector_app(name, &arg_ids)? {
            return Ok(term);
        }
        if let Some(term) = self.try_elaborate_floating_point_app(name, &arg_ids)? {
            return Ok(term);
        }

        let result_sort = if let Some(info) = self.symbols.get(name) {
            info.sort.clone()
        } else {
            return Err(ElaborateError::UndefinedSymbol(name.to_string()));
        };
        Ok(self.terms.mk_app(Symbol::named(name), arg_ids, result_sort))
    }

    /// True when `term` has a (non-recursive or recursive) datatype sort — i.e.
    /// its sort is `Sort::Uninterpreted(name)` where `name` is a declared
    /// datatype. Datatypes elaborate to uninterpreted sorts in this frontend.
    fn is_datatype_sorted(&self, term: TermId) -> bool {
        matches!(self.terms.sort(term), Sort::Uninterpreted(s) if self.datatypes.contains_key(s))
    }

    /// Build a datatype tester application `((_ is C) e)` over an already
    /// elaborated scrutinee, given the constructor's INTERNAL name. Mirrors the
    /// `is-<ctor_internal>` named app that [`Self::elaborate_app`] produces for a
    /// surface `(_ is C)`. When the scrutinee is a literal constructor
    /// application the result folds to a Boolean constant (constructor
    /// distinctness), which lets the surrounding `ite` collapse. Used by `match`
    /// desugaring (`elaborate/term.rs`).
    /// The datatype constructor (INTERNAL name) that literally built `t`, if
    /// any: a constructor application `C(a..)`, or a NULLARY constructor —
    /// which elaborates to a named Var, not a 0-ary App (`mk_fresh_named_var`
    /// in `datatypes.rs`), so it is recognized by its exact bound `TermId` via
    /// `nullary_ctor_terms`. The TermId-exact check means a quantifier/let
    /// binder that merely shadows a constructor NAME binds a different term and
    /// can never fold unsoundly. (#rec-dt-expansion)
    pub(super) fn ctor_of_term(&self, t: TermId) -> Option<String> {
        match self.terms.get(t) {
            TermData::App(Symbol::Named(c), _) if self.constructors.contains_key(c) => {
                Some(c.clone())
            }
            TermData::Var(v, _) if self.nullary_ctor_terms.get(v) == Some(&t) => Some(v.clone()),
            _ => None,
        }
    }

    pub(super) fn mk_datatype_tester(&mut self, ctor_internal: &str, scrut: TermId) -> TermId {
        if let Some(applied) = self.ctor_of_term(scrut) {
            return if applied == ctor_internal {
                self.terms.true_term()
            } else {
                self.terms.false_term()
            };
        }
        self.terms.mk_app(
            Symbol::named(format!("is-{ctor_internal}")),
            vec![scrut],
            Sort::Bool,
        )
    }

    /// Build a datatype selector application `(sel e)` over an already elaborated
    /// scrutinee, given the selector's INTERNAL name and field sort. Reuses the
    /// selector-over-constructor / selector-over-ite folding so a `match` on a
    /// literal constructor reduces directly to the stored field. Used by `match`
    /// desugaring (`elaborate/term.rs`).
    pub(super) fn mk_datatype_selector(
        &mut self,
        sel_internal: &str,
        sel_sort: &Sort,
        scrut: TermId,
    ) -> TermId {
        if let Some(folded) = self.try_fold_selector(sel_internal, scrut) {
            return folded;
        }
        self.terms
            .mk_app(Symbol::named(sel_internal), vec![scrut], sel_sort.clone())
    }

    /// Distribute a datatype selector `name` through `ite` down to constructor
    /// leaves: `sel(ite(c, X, Y)) -> ite(c, sel(X), sel(Y))`, folding
    /// `sel(C(t..)) -> t_i` at each leaf. Returns `None` when any leaf is neither
    /// a constructor application owning `name` nor a further `ite`, so the caller
    /// leaves the selector application opaque for the existing axiom path rather
    /// than fabricating a partial distribution. (#selector-over-ite)
    fn try_fold_selector(&mut self, name: &str, arg: TermId) -> Option<TermId> {
        match self.terms.get(arg).clone() {
            TermData::App(Symbol::Named(ctor_name), cargs) => {
                let idx = self
                    .ctor_selectors
                    .get(&ctor_name)?
                    .iter()
                    .position(|s| s.as_str() == name)?;
                cargs.get(idx).copied()
            }
            TermData::Ite(c, x, y) => {
                let fx = self.try_fold_selector(name, x)?;
                let fy = self.try_fold_selector(name, y)?;
                Some(self.terms.mk_ite(c, fx, fy))
            }
            _ => None,
        }
    }

    /// Fold a datatype equality `lhs = rhs` into a datatype-free formula via
    /// constructor injectivity/distinctness, distributing through `ite`. Falls
    /// back to a plain `(= lhs rhs)` when neither operand is a constructor
    /// application or `ite` (e.g. two opaque variables of a recursive datatype),
    /// preserving the existing axiom-based path for those.
    fn fold_datatype_eq(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        let l = self.terms.get(lhs).clone();
        let r = self.terms.get(rhs).clone();
        let l_is_ite = matches!(l, TermData::Ite(..));
        let r_is_ite = matches!(r, TermData::Ite(..));

        // Distribute over a single `ite`. Only when the OTHER side is not itself
        // an `ite`, to avoid an exponential cross-product expansion.
        if l_is_ite && !r_is_ite {
            if let TermData::Ite(c, t, e) = l {
                let tt = self.fold_datatype_eq(t, rhs);
                let ee = self.fold_datatype_eq(e, rhs);
                return self.terms.mk_ite(c, tt, ee);
            }
        }
        if r_is_ite && !l_is_ite {
            if let TermData::Ite(c, t, e) = r {
                let tt = self.fold_datatype_eq(lhs, t);
                let ee = self.fold_datatype_eq(lhs, e);
                return self.terms.mk_ite(c, tt, ee);
            }
        }

        // Constructor vs constructor: injectivity (same ctor) / distinctness.
        if let (TermData::App(Symbol::Named(lc), largs), TermData::App(Symbol::Named(rc), rargs)) =
            (&l, &r)
        {
            let l_dt = self.constructors.get(lc).map(|(dt, _)| dt.clone());
            let r_dt = self.constructors.get(rc).map(|(dt, _)| dt.clone());
            if let (Some(l_dt), Some(r_dt)) = (l_dt, r_dt) {
                if l_dt == r_dt {
                    if lc == rc {
                        if largs.len() == rargs.len() {
                            if largs.is_empty() {
                                return self.terms.true_term();
                            }
                            let largs = largs.clone();
                            let rargs = rargs.clone();
                            let pairs: Vec<TermId> = largs
                                .iter()
                                .zip(rargs.iter())
                                .map(|(&a, &b)| self.fold_field_eq(a, b))
                                .collect();
                            return self.terms.mk_and(pairs);
                        }
                    } else {
                        // Distinct constructors of the same datatype: unsatisfiable.
                        return self.terms.false_term();
                    }
                }
            }
        }

        self.terms.mk_eq(lhs, rhs)
    }

    /// Equality of a single constructor field: recurse into the datatype folder
    /// for datatype-sorted fields (nested products), plain equality otherwise.
    fn fold_field_eq(&mut self, a: TermId, b: TermId) -> TermId {
        if self.is_datatype_sorted(a) {
            self.fold_datatype_eq(a, b)
        } else {
            self.terms.mk_eq(a, b)
        }
    }
}
