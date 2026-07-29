// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use num_bigint::BigInt;
use num_rational::BigRational;

use crate::command::{MatchPattern, ParsedConstant, QualifiedIdentifier, Term as ParsedTerm};
use crate::sexp::{PARSE_STACK_RED_ZONE, PARSE_STACK_SIZE};
use ay_core::{Constant, Sort, Symbol, TermData, TermId};

use super::{Context, ElaborateError, Result};

/// Whether `s` is in z3's arithmetic-coercible set for `=`/`distinct`/`ite`
/// operand mixing: exactly {Bool, Int, Real} (Bool coerces to `(ite b 1 0)`,
/// Int to Real). No other sort coerces — a differing pair outside this set is a
/// sort error in z3 4.15.4.
pub(super) fn arith_coercible(s: &Sort) -> bool {
    matches!(s, Sort::Bool | Sort::Int | Sort::Real)
}

/// Running-join rank for the coercible chain: Real > Int > Bool. Only defined
/// for the coercible sorts; callers guard with [`arith_coercible`] first.
fn arith_rank(s: &Sort) -> u8 {
    match s {
        Sort::Real => 2,
        Sort::Int => 1,
        _ => 0, // Bool
    }
}

/// Kill switch (AY_ELAB_LET_CHAIN=0 restores the legacy per-level clone) for the
/// flattened let-chain elaboration that avoids O(N^2) env cloning on deeply
/// nested let-chains. Cached after first read.
fn elab_let_chain_enabled() -> bool {
    use std::sync::OnceLock;
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var_os("AY_ELAB_LET_CHAIN").is_none_or(|v| v != "0"))
}

/// Collect every symbol/function name referenced anywhere in `root` into `out`.
/// Used by the `let` elaborator to decide which bindings are live (a name not
/// collected here is definitely unused). Over-approximates "used" — it ignores
/// binder shadowing and includes operator/qualified heads — which is sound for
/// the caller: it only ever causes a truly-dead binding to be kept, never a live
/// one to be dropped. Iterative (explicit stack) for deep-term stack safety.
fn collect_term_names(root: &ParsedTerm, out: &mut HashSet<String>) {
    let mut stack: Vec<&ParsedTerm> = vec![root];
    while let Some(t) = stack.pop() {
        match t {
            ParsedTerm::Const(_) => {}
            ParsedTerm::Symbol(n) => {
                out.insert(n.clone());
            }
            ParsedTerm::App(n, args) => {
                out.insert(n.clone());
                stack.extend(args.iter());
            }
            ParsedTerm::IndexedApp(_, _, args) => {
                stack.extend(args.iter());
            }
            ParsedTerm::QualifiedApp(n, _, args) => {
                if let QualifiedIdentifier::Symbol(name) = n {
                    out.insert(name.clone());
                }
                stack.extend(args.iter());
            }
            ParsedTerm::Let(bindings, body) => {
                stack.extend(bindings.iter().map(|(_, v)| v));
                stack.push(body.as_ref());
            }
            ParsedTerm::Forall(_, body)
            | ParsedTerm::Exists(_, body)
            | ParsedTerm::Lambda(_, body) => {
                stack.push(body.as_ref());
            }
            ParsedTerm::Annotated(inner, _) => {
                stack.push(inner.as_ref());
            }
            ParsedTerm::Match(scrutinee, cases) => {
                // Over-approximate liveness: include the scrutinee, every body,
                // and each constructor name. Pattern binders shadow within their
                // body, but over-counting "used" names only ever keeps a dead
                // let-binding (sound), never drops a live one.
                stack.push(scrutinee.as_ref());
                for (pattern, body) in cases {
                    if let MatchPattern::Constructor(ctor, _) = pattern {
                        out.insert(ctor.clone());
                    }
                    stack.push(body);
                }
            }
        }
    }
}

impl Context {
    /// Elaborate a parsed term into the term store.
    /// Uses `stacker::maybe_grow` for stack safety on deeply nested terms (#4602).
    pub(crate) fn elaborate_term(
        &mut self,
        term: &ParsedTerm,
        env: &HashMap<String, TermId>,
    ) -> Result<TermId> {
        stacker::maybe_grow(PARSE_STACK_RED_ZONE, PARSE_STACK_SIZE, || match term {
            ParsedTerm::Const(c) => self.elaborate_constant(c),
            ParsedTerm::Symbol(name) => {
                // Check local environment first (let bindings, quantifier vars)
                if let Some(&id) = env.get(name) {
                    return Ok(id);
                }
                // Check function definitions FIRST (expand nullary define-fun)
                // This must come before the symbols check to properly expand
                // definitions like (define-fun my_eq () Bool (= a b))
                if let Some((params, result_sort, body)) = self.fun_defs.get(name).cloned() {
                    if params.is_empty() {
                        // Expand the body in the DEFINITION-TIME environment,
                        // which for a nullary macro has no local bindings at all
                        // (SMT-LIB 2.6 §4.2.2: the body's symbols resolve against
                        // the signature at definition time, i.e. the globals).
                        // Passing the USE-SITE `env` let every enclosing binder —
                        // quantifier variable, `let` binding, `match` pattern
                        // variable — capture a global the body names; see the
                        // capture-avoidance note in `elaborate_app`.
                        let term = self.elaborate_term(&body, &HashMap::default())?;
                        // SMT-LIB implicit Int->Real coercion for define-fun:
                        // (define-fun x () Real 0) — the numeral `0` elaborates
                        // as Int but the declared sort is Real. Coerce to match.
                        // Without this, downstream mk_eq panics on sort mismatch
                        // and release builds produce false-UNSAT (#6812).
                        let actual = self.terms.sort(term).clone();
                        if actual == result_sort {
                            return Ok(term);
                        }
                        if actual == Sort::Int && result_sort == Sort::Real {
                            return Ok(self.coerce_int_to_real(term));
                        }
                        return Err(ElaborateError::SortMismatch {
                            expected: result_sort.to_string(),
                            actual: actual.to_string(),
                        });
                    }
                }
                // Check global symbols. Bare identifiers can denote only a
                // unique nullary declaration; choosing the last entry of an
                // overloaded name would silently change the user's formula.
                if let Some(info) = self.resolve_bare_declared_symbol(name)? {
                    if let Some(id) = info.term {
                        return Ok(id);
                    }
                    let internal_name = info.internal_name.as_deref().unwrap_or(name);
                    return Ok(self.terms.mk_var(internal_name, info.sort));
                }
                // Handle negative numeric literals: -1, -42, -3.14, etc.
                // In SMT-LIB these should be (- 1), (- 42) but many benchmarks
                // use the shorthand -1, -42 which the lexer parses as symbols
                if let Some(abs_str) = name.strip_prefix('-') {
                    if !abs_str.is_empty() {
                        // Check for negative integer
                        if abs_str.chars().all(|c| c.is_ascii_digit()) {
                            let abs_value: BigInt = abs_str
                                .parse()
                                .map_err(|_| ElaborateError::InvalidConstant(name.clone()))?;
                            let neg_value = -abs_value;
                            return Ok(self.terms.mk_int(neg_value));
                        }
                        // Check for negative decimal (e.g., -3.14)
                        if abs_str.contains('.')
                            && abs_str.chars().all(|c| c.is_ascii_digit() || c == '.')
                            && abs_str.chars().filter(|&c| c == '.').count() == 1
                        {
                            // Parse as rational and negate
                            let parts: Vec<&str> = abs_str.split('.').collect();
                            if parts.len() == 2 {
                                let int_part: BigInt = parts[0]
                                    .parse()
                                    .map_err(|_| ElaborateError::InvalidConstant(name.clone()))?;
                                let frac_str = parts[1];
                                let frac_part: BigInt = frac_str
                                    .parse()
                                    .map_err(|_| ElaborateError::InvalidConstant(name.clone()))?;
                                let denom = BigInt::from(10).pow(frac_str.len() as u32);
                                let numer = int_part * &denom + frac_part;
                                let rational = BigRational::new(-numer, denom);
                                return Ok(self.terms.mk_rational(rational));
                            }
                        }
                    }
                }
                // Regex nullary constants: re.none, re.all, re.allchar
                // SMT-LIB 2.6 Section 3.6.4 defines these as RegLan constants.
                if matches!(name.as_str(), "re.none" | "re.all" | "re.allchar") {
                    return Ok(self.terms.mk_app(Symbol::named(name), vec![], Sort::RegLan));
                }
                // FP rounding mode constants (#4127)
                if matches!(
                    name.as_str(),
                    "RNE"
                        | "RNA"
                        | "RTP"
                        | "RTN"
                        | "RTZ"
                        | "roundNearestTiesToEven"
                        | "roundNearestTiesToAway"
                        | "roundTowardPositive"
                        | "roundTowardNegative"
                        | "roundTowardZero"
                ) {
                    // Store rounding mode as a named app with the RoundingMode
                    // sort (`Sort::Uninterpreted("RoundingMode")` — the same sort
                    // a `(declare-const rm RoundingMode)` falls through to in
                    // sorts.rs). The FP solver still matches on the symbol name,
                    // but the sort must agree with declared RoundingMode consts:
                    // the historical `Sort::Bool` encoding made `(= rm RTP)`
                    // internally ill-sorted, which broke EUF domain reasoning
                    // (wrong `sat` on `(= RTP RTZ)` / RM pigeonholes) and
                    // panicked the ayz3 `rm == RTP()` path on the sort mismatch
                    // (#P0.2 symbolic RoundingMode).
                    let short_name = match name.as_str() {
                        "roundNearestTiesToEven" => "RNE",
                        "roundNearestTiesToAway" => "RNA",
                        "roundTowardPositive" => "RTP",
                        "roundTowardNegative" => "RTN",
                        "roundTowardZero" => "RTZ",
                        other => other,
                    };
                    return Ok(self.terms.mk_app(
                        Symbol::named(short_name),
                        vec![],
                        Sort::Uninterpreted("RoundingMode".to_string()),
                    ));
                }
                Err(ElaborateError::UndefinedSymbol(name.clone()))
            }
            ParsedTerm::App(name, args) => self.elaborate_app(name, args, env),
            ParsedTerm::IndexedApp(name, indices, args) => {
                self.elaborate_indexed_app(name, indices, args, env)
            }
            ParsedTerm::QualifiedApp(name, sort, args) => {
                self.elaborate_qualified_app(name, sort, args, env)
            }
            ParsedTerm::Let(bindings, body) => {
                // `let` BINDS IN PARALLEL (SMT-LIB 2.6 §3.6.1): every binding's
                // value is elaborated in the environment as it stood BEFORE its
                // own level, so a binding CANNOT see its siblings. `let*` must be
                // written as nested `let`s.
                //
                // This used to bind sequentially, which was a wrong-verdict
                // (soundness) defect in the core language — theory-independent and
                // able to flip a verdict in EITHER direction:
                //   (let ((a 0)) (let ((a 1) (b a)) (= b 0)))   is a TAUTOLOGY
                //     (`b` is the OUTER `a`), but bound sequentially `b` became 1
                //     and ay answered `unsat` where z3 answers `sat`.
                //   (let ((a false)) (let ((a true) (b a)) b))  is UNSATISFIABLE,
                //     but ay answered `sat`.
                // It also leaked scope: `(let ((a #b1) (b a)) …)` with nothing
                // named `a` in scope was accepted instead of rejected, which is
                // direct evidence the env was extended before siblings were
                // elaborated. Sibling-referencing multi-binding `let` is what term
                // printers and Tseitin/CSE encoders emit but no random benchmark
                // generator produces, which is why it survived the corpus.
                //
                // Two optimizations are preserved, both now level-aware:
                //  (1) DEAD-BINDING ELIMINATION (#arr_lia561): only elaborate and
                //      intern bindings the body transitively needs. Interning a
                //      dead `(select A i)` lets the lazy array combiner scan it and
                //      drive a spurious UNSAT.
                //  (2) let-CHAIN FLATTEN: clone the env HashMap ONCE for a whole
                //      body-position chain rather than once per level — the
                //      per-level clone was O(N^2) memory on ~8000-deep let-chains
                //      (QF_LRA k-induction) and OOMed during elaboration. The chain
                //      is still walked LEVEL BY LEVEL; only the clone is hoisted.
                //      Collapsing the levels into one ordered list is what made the
                //      flatten unsound, and is exactly what is no longer done.
                // Kill switch AY_ELAB_LET_CHAIN=0 falls back to the per-level clone
                // (identical semantics, one clone per level).
                if elab_let_chain_enabled() {
                    // Collect the body-position chain as LEVELS. Level boundaries
                    // are semantically load-bearing and must not be merged.
                    let mut levels: Vec<&Vec<(String, ParsedTerm)>> = Vec::new();
                    let mut final_body: &ParsedTerm = body;
                    let mut cur_bindings: &Vec<(String, ParsedTerm)> = bindings;
                    loop {
                        levels.push(cur_bindings);
                        match final_body {
                            ParsedTerm::Let(inner_bindings, inner_body) => {
                                cur_bindings = inner_bindings;
                                final_body = &**inner_body;
                            }
                            _ => break,
                        }
                    }
                    // Liveness, innermost level outwards. For a PARALLEL binder the
                    // requirement surviving a level is the free-variable rule
                    //   used_outer = (used \ bound(level)) ∪ names(values of live)
                    // — a sibling reference resolves OUTWARD, so it must keep the
                    // outer binding of that name alive.
                    let mut used: HashSet<String> = HashSet::default();
                    collect_term_names(final_body, &mut used);
                    let mut live: Vec<Vec<bool>> = Vec::with_capacity(levels.len());
                    for level in levels.iter().rev() {
                        let mut flags: Vec<bool> = Vec::with_capacity(level.len());
                        let mut value_names: HashSet<String> = HashSet::default();
                        for (name, value) in level.iter() {
                            let is_live = used.contains(name);
                            flags.push(is_live);
                            if is_live {
                                collect_term_names(value, &mut value_names);
                            }
                        }
                        for (name, _) in level.iter() {
                            used.remove(name);
                        }
                        used.extend(value_names);
                        live.push(flags);
                    }
                    live.reverse();

                    let mut new_env = env.clone();
                    let mut level_values: Vec<(String, TermId)> = Vec::new();
                    for (level, flags) in levels.iter().zip(live.iter()) {
                        // Elaborate EVERY value of this level first, reading only
                        // the pre-level env, and publish them together afterwards.
                        level_values.clear();
                        for ((name, value), &is_live) in level.iter().zip(flags.iter()) {
                            if !is_live {
                                continue; // dead binding: do not elaborate / intern
                            }
                            let value_id = self.elaborate_term(value, &new_env)?;
                            level_values.push((name.clone(), value_id));
                        }
                        for (name, value_id) in level_values.drain(..) {
                            new_env.insert(name, value_id);
                        }
                    }
                    self.elaborate_term(final_body, &new_env)
                } else {
                    // Single level; nested `let`s recurse through elaborate_term.
                    let mut used: HashSet<String> = HashSet::default();
                    collect_term_names(body, &mut used);
                    let mut level_values: Vec<(String, TermId)> = Vec::new();
                    for (name, value) in bindings {
                        if !used.contains(name) {
                            continue; // dead binding: do not elaborate / intern
                        }
                        // `env`, not the extended one: siblings are not in scope.
                        let value_id = self.elaborate_term(value, env)?;
                        level_values.push((name.clone(), value_id));
                    }
                    let mut new_env = env.clone();
                    for (name, value_id) in level_values {
                        new_env.insert(name, value_id);
                    }
                    self.elaborate_term(body, &new_env)
                }
            }
            ParsedTerm::Forall(bindings, body) => {
                // Elaborate quantifier bindings and body
                // Create fresh variables for the bound variables
                let mut new_env = env.clone();
                let mut vars: Vec<(String, Sort)> = Vec::new();
                for (name, sort) in bindings {
                    let sort = self.elaborate_sort(sort)?;
                    let var = self.terms.mk_fresh_var(name, sort.clone());
                    new_env.insert(name.clone(), var);
                    let fresh_name = match self.terms.get(var) {
                        TermData::Var(fresh_name, _) => fresh_name.clone(),
                        other => {
                            return Err(ElaborateError::Unsupported(format!(
                                "quantifier binding is not a Var: {other:?}"
                            )));
                        }
                    };
                    vars.push((fresh_name, sort));
                }
                let (body_id, triggers) =
                    self.elaborate_quantifier_body_with_triggers(body, &new_env)?;
                Ok(self.terms.mk_forall_with_triggers(vars, body_id, triggers))
            }
            ParsedTerm::Exists(bindings, body) => {
                // Elaborate quantifier bindings and body
                let mut new_env = env.clone();
                let mut vars: Vec<(String, Sort)> = Vec::new();
                for (name, sort) in bindings {
                    let sort = self.elaborate_sort(sort)?;
                    let var = self.terms.mk_fresh_var(name, sort.clone());
                    new_env.insert(name.clone(), var);
                    let fresh_name = match self.terms.get(var) {
                        TermData::Var(fresh_name, _) => fresh_name.clone(),
                        other => {
                            return Err(ElaborateError::Unsupported(format!(
                                "quantifier binding is not a Var: {other:?}"
                            )));
                        }
                    };
                    vars.push((fresh_name, sort));
                }
                let (body_id, triggers) =
                    self.elaborate_quantifier_body_with_triggers(body, &new_env)?;
                Ok(self.terms.mk_exists_with_triggers(vars, body_id, triggers))
            }
            ParsedTerm::Lambda(bindings, body) => {
                // Elaborate lambda array: (lambda ((x Int)) body)
                // Creates a lambda-array term where select performs beta reduction.
                //
                // A single-variable lambda elaborates to a plain lambda-array
                // `(Array S R)` and is sound in every position (select is a
                // sound beta-reduction, and single-var lambda (dis)equality
                // fails closed to `unknown`).
                //
                // A MULTI-variable lambda `(lambda ((v1 S1) ... (vn Sn)) body)`
                // is elaborated as a CURRIED nest of single-variable
                // lambda-arrays:
                //   lambda-array(v1, lambda-array(v2, ... lambda-array(vn, body)))
                // with sort `(Array S1 (Array S2 ... (Array Sn R)))`. This is
                // exactly the curried function-as-array convention the
                // higher-order sequence combinators expect — `seq.foldl f`
                // wants `(Array A (Array E A))` and `seq.mapi f` wants
                // `(Array Int (Array E R))` (see `ay-dpll seq/ho_unfold.rs`),
                // so a natural 2-arg fold lambda unfolds and DECIDES there.
                //
                // BUT that curried encoding is NOT z3-equivalent in any other
                // position: z3 treats an n-ary lambda as an n-ary function, not
                // a curried array. Left visible elsewhere it wrong-decides —
                // a false `sat` on an equality between two 2-var lambda-arrays
                // (they are opaque, freely-equatable arrays to AY), and a
                // spurious `unsat` on a direct `(select (select f i) j)` chain
                // that z3 rejects as ill-sorted. So multi-var currying is only
                // permitted when this lambda is the direct function argument of
                // a higher-order sequence combinator (the flag set by
                // `elaborate_app`, consumed here); otherwise we fail closed to
                // `unknown`, exactly as the pre-P1.5 code did. Fail-closing is
                // always sound (§0). (#p1.5-curried-lambda-gate)
                if bindings.is_empty() {
                    return Err(ElaborateError::Unsupported(
                        "lambda requires at least one bound variable".to_string(),
                    ));
                }
                if bindings.len() > 1 && !self.multivar_lambda_curry_allowed {
                    return Err(ElaborateError::Unsupported(
                        "lambda arrays with multiple bound variables are only \
                         supported as the function argument of a higher-order \
                         sequence combinator (seq.foldl/seq.foldli/seq.map/seq.mapi)"
                            .to_string(),
                    ));
                }
                let mut new_env = env.clone();
                let mut vars: Vec<TermId> = Vec::with_capacity(bindings.len());
                for (name, parsed_sort) in bindings {
                    let sort = self.elaborate_sort(parsed_sort)?;
                    let var = self.terms.mk_fresh_var(name, sort);
                    new_env.insert(name.clone(), var);
                    vars.push(var);
                }
                // The fn-arg permission applies ONLY to this direct lambda.
                // Descending into the body leaves the fn-arg position, so a
                // nested multi-var lambda (e.g. inside the fold body) must fail
                // closed like any other non-combinator context.
                let saved = self.multivar_lambda_curry_allowed;
                self.multivar_lambda_curry_allowed = false;
                let body_result = self.elaborate_term(body, &new_env);
                self.multivar_lambda_curry_allowed = saved;
                let mut result = body_result?;
                for var in vars.into_iter().rev() {
                    result = self.terms.mk_lambda_array(var, result);
                }
                Ok(result)
            }
            ParsedTerm::Annotated(inner, annotations) => {
                // Elaborate the inner term
                let term_id = self.elaborate_term(inner, env)?;

                self.process_term_annotations(term_id, annotations);

                Ok(term_id)
            }
            ParsedTerm::Match(scrutinee, cases) => self.elaborate_match(scrutinee, cases, env),
        })
    }

    /// Desugar an SMT-LIB 2.6 `(match e ((p1 b1) (p2 b2) ...))` into nested
    /// `ite` guarded by datatype testers, with each constructor-pattern field
    /// binder bound to the corresponding selector applied to `e`:
    ///
    /// ```text
    /// (match e ((C x..) b) ... (default d))
    ///   ->  (ite (is-C e) b[x := sel(e)] (ite ... d))
    /// ```
    ///
    /// SOUNDNESS: every sub-case is desugared with the datatype's real
    /// tester/selector machinery (so it is decided exactly like a hand-written
    /// `ite`), or the whole match is rejected with an [`ElaborateError`] — never
    /// guessed. A non-exhaustive match with no default binder is rejected so the
    /// CLI fails closed to `unknown` rather than fabricating an else branch.
    fn elaborate_match(
        &mut self,
        scrutinee: &ParsedTerm,
        cases: &[(MatchPattern, ParsedTerm)],
        env: &HashMap<String, TermId>,
    ) -> Result<TermId> {
        if cases.is_empty() {
            return Err(ElaborateError::Unsupported(
                "match expression has no cases".to_string(),
            ));
        }

        let scrut = self.elaborate_term(scrutinee, env)?;
        let scrut_sort = self.terms.sort(scrut).clone();
        let Sort::Uninterpreted(dt_name) = &scrut_sort else {
            return Err(ElaborateError::Unsupported(format!(
                "match scrutinee must have a datatype sort, got {scrut_sort}"
            )));
        };
        let dt_name = dt_name.clone();
        let ctor_internals = self.datatypes.get(&dt_name).cloned().ok_or_else(|| {
            ElaborateError::Unsupported(format!(
                "match scrutinee sort '{dt_name}' is not a datatype"
            ))
        })?;

        // (guard, body): guard `None` is a catch-all (variable/wildcard binder).
        let mut branches: Vec<(Option<TermId>, TermId)> = Vec::with_capacity(cases.len());
        let mut covered: HashSet<String> = HashSet::default();
        let mut has_default = false;

        for (pattern, body) in cases {
            if has_default {
                // A catch-all already decides every scrutinee value; SMT-LIB
                // forbids later cases, and ignoring them is sound.
                break;
            }
            match pattern {
                MatchPattern::Symbol(symbol) if symbol != "_" => {
                    if let Some(ctor_internal) =
                        self.datatype_ctor_internal(&ctor_internals, symbol)
                    {
                        // Bare symbol naming a constructor: a nullary-constructor
                        // pattern. A constructor that carries fields cannot appear
                        // bare (it needs field binders).
                        let selectors = self
                            .ctor_selector_info
                            .get(&ctor_internal)
                            .cloned()
                            .unwrap_or_default();
                        if !selectors.is_empty() {
                            return Err(ElaborateError::Unsupported(format!(
                                "constructor '{symbol}' in match pattern needs {} field binder(s)",
                                selectors.len()
                            )));
                        }
                        let guard = self.mk_datatype_tester(&ctor_internal, scrut);
                        covered.insert(ctor_internal);
                        // Guard short-circuit over a literal-constructor
                        // scrutinee: a FALSE tester makes this case dead — skip
                        // its body entirely (load-bearing for recursive match
                        // bodies, mirroring the elaborate_app ite short-circuit);
                        // a TRUE tester decides the match here, so the body is
                        // the catch-all and later cases are dead. A symbolic
                        // guard keeps today's behavior. (#rec-dt-expansion)
                        match self.terms.get(guard) {
                            TermData::Const(Constant::Bool(false)) => {}
                            TermData::Const(Constant::Bool(true)) => {
                                let body_id = self.elaborate_term(body, env)?;
                                has_default = true;
                                branches.push((None, body_id));
                            }
                            _ => {
                                let body_id = self.elaborate_term(body, env)?;
                                branches.push((Some(guard), body_id));
                            }
                        }
                    } else {
                        // A symbol that is not a constructor: a variable binder
                        // for the whole scrutinee (the default case).
                        let mut new_env = env.clone();
                        new_env.insert(symbol.clone(), scrut);
                        let body_id = self.elaborate_term(body, &new_env)?;
                        has_default = true;
                        branches.push((None, body_id));
                    }
                }
                MatchPattern::Symbol(_) => {
                    // `_` wildcard: default case, binds nothing.
                    let body_id = self.elaborate_term(body, env)?;
                    has_default = true;
                    branches.push((None, body_id));
                }
                MatchPattern::Constructor(ctor, vars) => {
                    let ctor_internal = self
                        .datatype_ctor_internal(&ctor_internals, ctor)
                        .ok_or_else(|| {
                            ElaborateError::Unsupported(format!(
                                "'{ctor}' is not a constructor of datatype '{dt_name}' in a match pattern"
                            ))
                        })?;
                    let selectors = self
                        .ctor_selector_info
                        .get(&ctor_internal)
                        .cloned()
                        .unwrap_or_default();
                    if selectors.len() != vars.len() {
                        return Err(ElaborateError::Unsupported(format!(
                            "constructor '{ctor}' in match pattern expects {} field(s), got {}",
                            selectors.len(),
                            vars.len()
                        )));
                    }
                    let guard = self.mk_datatype_tester(&ctor_internal, scrut);
                    covered.insert(ctor_internal);
                    // Same guard short-circuit as the nullary arm: skip dead
                    // cases (FALSE guard) without elaborating their bodies —
                    // load-bearing for match-based recursion over datatypes —
                    // and treat a TRUE guard as the deciding catch-all.
                    // (#rec-dt-expansion)
                    if matches!(
                        self.terms.get(guard),
                        TermData::Const(Constant::Bool(false))
                    ) {
                        continue;
                    }
                    let mut new_env = env.clone();
                    for (var, (sel_internal, sel_sort)) in vars.iter().zip(selectors.iter()) {
                        if var == "_" {
                            continue; // unbound field wildcard
                        }
                        let field = self.mk_datatype_selector(sel_internal, sel_sort, scrut);
                        new_env.insert(var.clone(), field);
                    }
                    if matches!(self.terms.get(guard), TermData::Const(Constant::Bool(true))) {
                        let body_id = self.elaborate_term(body, &new_env)?;
                        has_default = true;
                        branches.push((None, body_id));
                    } else {
                        let body_id = self.elaborate_term(body, &new_env)?;
                        branches.push((Some(guard), body_id));
                    }
                }
            }
        }

        // Exhaustiveness: a default binder, or every constructor covered. Without
        // it, treating the last case as the else would fabricate a value for an
        // uncovered constructor — unsound — so reject and fail closed.
        if !has_default && !ctor_internals.iter().all(|ci| covered.contains(ci)) {
            return Err(ElaborateError::Unsupported(format!(
                "non-exhaustive match on datatype '{dt_name}' (missing default or constructor case)"
            )));
        }

        // Fold into nested ite, last case as the else (its guard, if any, is
        // implied by exhaustiveness once the earlier guards are excluded).
        let mut acc: Option<TermId> = None;
        for (guard, body) in branches.into_iter().rev() {
            acc = Some(match (guard, acc) {
                (None, _) => body,       // catch-all default
                (Some(_), None) => body, // last case = else
                (Some(g), Some(prev)) => self.terms.mk_ite(g, body, prev),
            });
        }
        // All cases folded away as dead (every guard constant-folded to false).
        // Semantically unreachable for a well-sorted exhaustive match, but fail
        // closed instead of panicking. (#rec-dt-expansion)
        acc.ok_or_else(|| {
            ElaborateError::Unsupported("match expression reduced to no live cases".to_string())
        })
    }

    /// Resolve a surface constructor name to its instance-specific INTERNAL name
    /// among a datatype's constructors. For a monomorphic datatype the internal
    /// name equals the surface name; for a parametric instance it is the mangled
    /// member name (e.g. `cns@L!{Int}`), recovered via the internal->surface map.
    fn datatype_ctor_internal(&self, ctor_internals: &[String], surface: &str) -> Option<String> {
        ctor_internals
            .iter()
            .find(|ci| self.dt_surface_name(ci).unwrap_or(ci.as_str()) == surface)
            .cloned()
    }

    pub(super) fn process_term_annotations(
        &mut self,
        term_id: TermId,
        annotations: &[(String, crate::sexp::SExpr)],
    ) {
        // Track :named for get-assignment and get-unsat-core.
        for (keyword, value) in annotations {
            if keyword != ":named" {
                continue;
            }

            if let crate::sexp::SExpr::Symbol(name) = value {
                self.named_terms.insert(name.clone(), term_id);
                // Track in current scope for proper cleanup on pop.
                if let Some(scope) = self.scopes.last_mut() {
                    scope.named_terms.push(name.clone());
                }
            }
        }
    }

    fn elaborate_quantifier_body_with_triggers(
        &mut self,
        body: &ParsedTerm,
        env: &HashMap<String, TermId>,
    ) -> Result<(TermId, Vec<Vec<TermId>>)> {
        let ParsedTerm::Annotated(inner, annotations) = body else {
            return Ok((self.elaborate_term(body, env)?, Vec::new()));
        };

        let triggers = self.elaborate_user_triggers_from_annotations(annotations, env)?;
        let body_id = self.elaborate_term(inner, env)?;
        self.process_term_annotations(body_id, annotations);
        Ok((body_id, triggers))
    }

    fn elaborate_user_triggers_from_annotations(
        &mut self,
        annotations: &[(String, crate::sexp::SExpr)],
        env: &HashMap<String, TermId>,
    ) -> Result<Vec<Vec<TermId>>> {
        let mut triggers = Vec::new();

        for (keyword, value) in annotations {
            if keyword != ":pattern" {
                continue;
            }

            let crate::sexp::SExpr::List(terms) = value else {
                return Err(ElaborateError::Unsupported(format!(
                    ":pattern expects a list of terms, got {value}"
                )));
            };

            if terms.is_empty() {
                return Err(ElaborateError::Unsupported(
                    ":pattern multi-pattern must be non-empty".to_string(),
                ));
            }

            let mut multi_trigger = Vec::with_capacity(terms.len());
            for term_sexp in terms {
                let term = ParsedTerm::from_sexp(term_sexp).map_err(|e| {
                    ElaborateError::Unsupported(format!("invalid :pattern term: {e}"))
                })?;
                multi_trigger.push(self.elaborate_term(&term, env)?);
            }
            triggers.push(multi_trigger);
        }

        Ok(triggers)
    }

    /// Elaborate a constant
    fn elaborate_constant(&mut self, constant: &ParsedConstant) -> Result<TermId> {
        match constant {
            ParsedConstant::True => Ok(self.terms.true_term()),
            ParsedConstant::False => Ok(self.terms.false_term()),
            ParsedConstant::Numeral(s) => {
                let value: BigInt = s
                    .parse()
                    .map_err(|_| ElaborateError::InvalidConstant(s.clone()))?;
                Ok(self.terms.mk_int(value))
            }
            ParsedConstant::Decimal(s) => {
                // Parse as rational
                let parts: Vec<&str> = s.split('.').collect();
                if parts.len() == 2 {
                    let int_part: BigInt = parts[0]
                        .parse()
                        .map_err(|_| ElaborateError::InvalidConstant(s.clone()))?;
                    let frac_str = parts[1];
                    let frac_part: BigInt = frac_str
                        .parse()
                        .map_err(|_| ElaborateError::InvalidConstant(s.clone()))?;
                    let denom = BigInt::from(10).pow(frac_str.len() as u32);
                    let numer = int_part * &denom + frac_part;
                    let rational = BigRational::new(numer, denom);
                    Ok(self.terms.mk_rational(rational))
                } else {
                    let value: BigInt = s
                        .parse()
                        .map_err(|_| ElaborateError::InvalidConstant(s.clone()))?;
                    Ok(self.terms.mk_rational(BigRational::from(value)))
                }
            }
            ParsedConstant::Hexadecimal(s) => {
                // #xABCD -> bitvector
                let hex = s.trim_start_matches("#x");
                let width = hex
                    .len()
                    .checked_mul(4)
                    .and_then(|width| u32::try_from(width).ok())
                    .ok_or_else(|| ElaborateError::InvalidConstant(s.clone()))?;
                Self::checked_bitvector_sort(width)?;
                let value = BigInt::parse_bytes(hex.as_bytes(), 16)
                    .ok_or_else(|| ElaborateError::InvalidConstant(s.clone()))?;
                Ok(self.terms.mk_bitvec(value, width))
            }
            ParsedConstant::Binary(s) => {
                // #b1010 -> bitvector
                let bin = s.trim_start_matches("#b");
                let width = u32::try_from(bin.len())
                    .map_err(|_| ElaborateError::InvalidConstant(s.clone()))?;
                Self::checked_bitvector_sort(width)?;
                let value = BigInt::parse_bytes(bin.as_bytes(), 2)
                    .ok_or_else(|| ElaborateError::InvalidConstant(s.clone()))?;
                Ok(self.terms.mk_bitvec(value, width))
            }
            ParsedConstant::String(s) => Ok(self.terms.mk_string(s.clone())),
        }
    }

    pub(super) fn promote_int_consts_to_real(&mut self, args: &mut [TermId]) -> Result<()> {
        for arg in args {
            if *self.terms.sort(*arg) != Sort::Int {
                continue;
            }
            // SMT-LIB implicit Int->Real coercion: coerce_int_to_real
            // constant-folds Int literals to Rational, rebuilds ITE with
            // coerced branches, and wraps other Int terms in to_real
            // (needed for mixed Int/Real logics like QF_LIRA).
            *arg = self.coerce_int_to_real(*arg);
        }
        Ok(())
    }

    /// Coerce an Int-sorted term to Real. Constants are converted directly.
    /// ITE terms are rebuilt with coerced branches. Other terms are wrapped
    /// in `to_real`.
    pub(super) fn coerce_int_to_real(&mut self, term: TermId) -> TermId {
        match self.terms.get(term).clone() {
            TermData::Const(Constant::Int(n)) => self.terms.mk_rational(BigRational::from(n)),
            TermData::Ite(cond, then_br, else_br) => {
                let then_real = self.coerce_int_to_real(then_br);
                let else_real = self.coerce_int_to_real(else_br);
                self.terms.mk_ite(cond, then_real, else_real)
            }
            _ => self.terms.mk_to_real(term),
        }
    }

    pub(super) fn maybe_promote_numeric_args(&mut self, args: &mut [TermId]) -> Result<()> {
        // #7126: BV-to-Int abstraction can produce Bool and BV args in numeric
        // context. Coerce non-numeric args to Int before other promotions.
        //
        // Skip promotion when all args share the same non-promotable sort
        // (e.g., all String). In that case the operator (like `=`) handles
        // same-sort args natively — no coercion needed. Without this guard,
        // String-sorted equality operands are coerced to Int(0), making
        // `(= str.++(x,y) "abc")` trivially true (#7464).
        //
        // Promotion IS needed when:
        // - Args include Bool, BitVec, or mixed sorts (BV-to-Int abstraction)
        // - Any arg is already numeric (mixed Int/Real with non-numeric)
        let has_non_numeric = args
            .iter()
            .any(|&id| !matches!(self.terms.sort(id), Sort::Int | Sort::Real));
        if has_non_numeric {
            // Check if ALL non-numeric args are the same non-promotable sort.
            // Sorts like String, Seq, Array, Datatype, Uninterpreted, Bool
            // should not be promoted when all args share the same sort — the
            // operator works natively. BitVec always needs promotion since it
            // has a natural numeric interpretation.
            //
            // Bool is non-promotable here (#8481): when all args are Bool
            // (e.g., `(= a b)` where a, b are Bool), the equality operator
            // handles Bool natively. Promoting Bool to (ite b 1 0) would
            // change the operand sort from Bool to Int, breaking downstream
            // simplifications like `(not (ite c a b))` which expect Bool.
            let all_same_non_promotable = args.iter().all(|&id| {
                let sort = self.terms.sort(id);
                matches!(
                    sort,
                    Sort::Bool
                        | Sort::String
                        | Sort::RegLan
                        | Sort::Seq(_)
                        | Sort::Array(_)
                        | Sort::Datatype(_)
                        | Sort::Uninterpreted(_)
                        | Sort::FloatingPoint(_, _)
                        | Sort::BitVec(_)
                )
            });
            if all_same_non_promotable {
                // All args are non-promotable sorts (e.g., all String).
                // No promotion needed — skip the coercion entirely.
            } else {
                for arg in args.iter_mut() {
                    match self.terms.sort(*arg).clone() {
                        Sort::Int | Sort::Real => {} // already numeric
                        Sort::Bool => {
                            let one = self.terms.mk_int(BigInt::from(1));
                            let zero = self.terms.mk_int(BigInt::from(0));
                            *arg = self.terms.mk_ite(*arg, one, zero);
                        }
                        Sort::BitVec(_) => {
                            *arg = self.terms.mk_bv2nat(*arg);
                        }
                        _ => {
                            // Unsupported sort in arithmetic — coerce to 0.
                            *arg = self.terms.mk_int(BigInt::from(0));
                        }
                    }
                }
            }
        }

        let has_real = args.iter().any(|&id| *self.terms.sort(id) == Sort::Real);
        let has_int = args.iter().any(|&id| *self.terms.sort(id) == Sort::Int);
        if has_real && has_int {
            // SMT-LIB numerals are usable in both Int and Real contexts. If we see a mix
            // of Int/Real in a numeric operator, treat Int constants as Real constants.
            self.promote_int_consts_to_real(args)?;
        }
        Ok(())
    }

    /// Verify that a chain of `=`/`distinct` operands is well-sorted the way
    /// z3 4.15.4 does. The coercible set is EXACTLY {Bool, Int, Real}: z3 mixes
    /// those freely (Bool as `(ite b 1 0)`, Int as Real), tracking a running
    /// join (rank Real > Int > Bool). Any other sort must appear IDENTICALLY at
    /// every operand — two `(Seq Int)`, two same-width BitVec, two of the same
    /// datatype/uninterpreted/FP/array sort are accepted (z3 accepts them); a
    /// differing pair not both in {Bool, Int, Real} is a sort error. The
    /// equal-sort identity rule is what keeps every non-{Bool,Int,Real} theory
    /// from being over-rejected. On the first incompatible adjacent step this
    /// reports `SortMismatch { expected: <running join>, actual: <next> }`,
    /// which the CLI renders as z3's `Sorts E and A are incompatible`.
    pub(super) fn check_chain_sorts(&self, arg_ids: &[TermId]) -> Result<()> {
        let Some((first, rest)) = arg_ids.split_first() else {
            return Ok(());
        };
        let mut acc = self.terms.sort(*first).clone();
        for &next in rest {
            let ns = self.terms.sort(next);
            if *ns == acc {
                // Identity: a matching sort is always well-sorted, INCLUDING
                // non-coercible sorts (Seq, Array, datatype, uninterpreted,
                // same-width BitVec, FloatingPoint, String, ...).
                continue;
            }
            if arith_coercible(&acc) && arith_coercible(ns) {
                // Running join over the {Bool, Int, Real} chain (Real > Int > Bool).
                if arith_rank(ns) > arith_rank(&acc) {
                    acc = ns.clone();
                }
            } else {
                return Err(ElaborateError::SortMismatch {
                    expected: acc.to_string(),
                    actual: ns.to_string(),
                });
            }
        }
        Ok(())
    }

    /// Coerce BV width mismatches in equality/distinct args (#5115).
    /// Competition benchmarks (MCMPC family) use `(= #x1 ((_ extract N N) x))`
    /// where `#x1` is BitVec(4) and extract produces BitVec(1). SMT-LIB strictly
    /// requires same-sort `=` args and z3 REJECTS these as ill-sorted — VERIFIED
    /// 2026-07-16: z3 errors on the exact `(= #x1 ((_ extract 0 0) x))` case
    /// (`Sorts (_ BitVec 4) and (_ BitVec 1) are incompatible`). This is a
    /// DELIBERATE AY leniency (NOT z3 parity): zero-extend the narrower operand
    /// to match the wider one, so the MCMPC family — which intends the
    /// zero-extension — is solved rather than rejected. Under a future
    /// `--z3-mode` elaboration-strictness gate this coercion should be disabled
    /// to match z3 exactly (see the burndown's silent-acceptance row).
    pub(super) fn maybe_coerce_bv_widths(&mut self, args: &mut [TermId]) {
        if args.len() != 2 {
            return;
        }
        let w0 = match self.terms.sort(args[0]) {
            Sort::BitVec(bv) => bv.width,
            _ => return,
        };
        let w1 = match self.terms.sort(args[1]) {
            Sort::BitVec(bv) => bv.width,
            _ => return,
        };
        if w0 == w1 {
            return;
        }
        if w0 < w1 {
            args[0] = self.terms.mk_bvzero_extend(w1 - w0, args[0]);
        } else {
            args[1] = self.terms.mk_bvzero_extend(w0 - w1, args[1]);
        }
    }

    pub(super) fn expect_exact_arity(
        &self,
        name: &str,
        args: &[TermId],
        expected: usize,
    ) -> Result<()> {
        if args.len() == expected {
            Ok(())
        } else {
            Err(ElaborateError::InvalidConstant(format!(
                "{name} requires {expected} arguments"
            )))
        }
    }

    pub(super) fn expect_min_arity(&self, name: &str, args: &[TermId], min: usize) -> Result<()> {
        if args.len() >= min {
            Ok(())
        } else {
            Err(ElaborateError::InvalidConstant(format!(
                "{name} requires at least {min} arguments"
            )))
        }
    }

    pub(super) fn expect_arg_sort(&self, arg: TermId, expected: &Sort) -> Result<()> {
        let actual = self.terms.sort(arg).clone();
        if &actual == expected {
            Ok(())
        } else {
            Err(ElaborateError::SortMismatch {
                expected: expected.to_string(),
                actual: actual.to_string(),
            })
        }
    }

    pub(super) fn expect_all_args_sort(&self, args: &[TermId], expected: &Sort) -> Result<()> {
        for &arg in args {
            self.expect_arg_sort(arg, expected)?;
        }
        Ok(())
    }
}
