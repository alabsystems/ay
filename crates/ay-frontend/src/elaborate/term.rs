// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use num_bigint::BigInt;
use num_rational::BigRational;

use crate::command::{
    MatchPattern, ParsedConstant, ParsedSort, QualifiedIdentifier, Term as ParsedTerm,
};
use crate::sexp::{SExpr, PARSE_STACK_RED_ZONE, PARSE_STACK_SIZE};
use ay_core::{Constant, Sort, Symbol, TermData, TermId};

use super::sorts::{FAM_REGLAN, FAM_RM};
use super::{Context, ElaborateError, MacroCallSite, MacroExpansionWatermark, Result};

struct ElaboratedQuantifierAttributes {
    triggers: Vec<Vec<TermId>>,
    no_patterns: Vec<TermId>,
    weight: u32,
    qid: Option<String>,
    skolem_id: Option<String>,
}

impl Default for ElaboratedQuantifierAttributes {
    fn default() -> Self {
        Self {
            triggers: Vec::new(),
            no_patterns: Vec::new(),
            weight: 1,
            qid: None,
            skolem_id: None,
        }
    }
}

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

/// Production policy for the flattened let-chain elaboration that avoids
/// O(N^2) environment cloning on deeply nested let-chains.
///
/// B24 retired the legacy per-level-clone A/B path, so the optimized,
/// semantics-equivalent chain elaboration is always enabled.
fn elab_let_chain_enabled() -> bool {
    true
}

/// Collect every symbol/function name referenced anywhere in `root` into `out`.
/// Used by the `let` elaborator to decide which bindings are live (a name not
/// collected here is definitely unused). Over-approximates "used" — it ignores
/// binder shadowing and includes operator/qualified heads — which is sound for
/// the caller: it only ever causes a truly-dead binding to be kept, never a live
/// one to be dropped. Iterative (explicit stack) for deep-term stack safety.
pub(super) fn collect_term_names(root: &ParsedTerm, out: &mut HashSet<String>) {
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
            ParsedTerm::Annotated(inner, attributes) => {
                // A `:pattern` or `:no-pattern` term is elaborated in the
                // scope of the term it annotates, so a `let` name used only
                // there is live.
                for (keyword, value) in attributes {
                    if matches!(keyword.as_str(), ":pattern" | ":no-pattern") {
                        collect_sexpr_symbols(value, out);
                    }
                }
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

/// Collect every symbol in an attribute value, which may hold terms.
fn collect_sexpr_symbols(root: &SExpr, out: &mut HashSet<String>) {
    let mut stack: Vec<&SExpr> = vec![root];
    while let Some(value) = stack.pop() {
        match value {
            SExpr::Symbol(name) => {
                out.insert(name.clone());
            }
            SExpr::List(items) => stack.extend(items.iter()),
            _ => {}
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
        let shared = self.shared_surface_lookup(term, env.is_empty())?;
        if let super::shared_surface::Lookup::Hit(term) = shared {
            return Ok(term);
        }
        let result = self.elaborate_term_uncached(term, env);
        if let (super::shared_surface::Lookup::Miss(index), Ok(term)) = (shared, &result) {
            self.shared_surface_record(index, *term)?;
        }
        result
    }

    fn elaborate_term_uncached(
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
                // A label accepted earlier in the assertion being elaborated.
                if let Some(body) = self.pending_label_body(name) {
                    return self.elaborate_term(&body, &HashMap::default());
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
                        //
                        // The body therefore depends on nothing but the
                        // definition, so the same use-site memo the applied
                        // case uses (`elaborate/macro_memo.rs`) elaborates a
                        // chain of nullary definitions once instead of once per
                        // path through it.
                        let entry_depth = self.fun_expansion_depth;
                        let memo_key = (MacroCallSite::BareSymbol, name.clone(), Vec::new());
                        if let Some(memoized) =
                            self.memoized_macro_expansion(&memo_key, entry_depth)
                        {
                            return Ok(memoized);
                        }
                        let watermark = MacroExpansionWatermark::open(self, entry_depth, &body);
                        let expanded =
                            self.elaborate_term(&body, &HashMap::default())
                                .and_then(|term| {
                                    // SMT-LIB implicit Int->Real coercion for
                                    // define-fun: (define-fun x () Real 0) —
                                    // the numeral `0` elaborates as Int but the
                                    // declared sort is Real. Coerce to match.
                                    // Without this, downstream mk_eq panics on
                                    // sort mismatch and release builds produce
                                    // false-UNSAT (#6812).
                                    let actual = self.terms.sort(term).clone();
                                    if actual == result_sort {
                                        Ok(term)
                                    } else if self.int_real_coercions()
                                        && actual == Sort::Int
                                        && result_sort == Sort::Real
                                    {
                                        Ok(self.coerce_int_to_real(term))
                                    } else {
                                        Err(ElaborateError::SortMismatch {
                                            expected: result_sort.to_string(),
                                            actual: actual.to_string(),
                                        })
                                    }
                                });
                        watermark.close(self, memo_key, expanded.as_ref().ok().copied());
                        return expanded;
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
                // A bare `-1` / `-3.14` never reaches here: the S-expression
                // parser reads the UNQUOTED shorthand as the signed numeral it
                // spells, as z3 and cvc5 do (`sexp::negative_numeric_literal`).
                // A symbol named `-1` is only ever the QUOTED `|-1|`, and an
                // undeclared one is an unknown constant, as in z3.
                // Regex nullary constants: re.none, re.all, re.allchar
                // SMT-LIB 2.6 Section 3.6.4 defines these as RegLan constants.
                if matches!(name.as_str(), "re.none" | "re.all" | "re.allchar") {
                    self.require_logic_builtin_family(name, FAM_REGLAN)?;
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
                    self.require_logic_builtin_family(name, FAM_RM)?;
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
                if let Some(literal) = name.strip_prefix("#f") {
                    if let Some((value, modulus)) = literal.split_once('m') {
                        let field = modulus
                            .parse()
                            .ok()
                            .and_then(ay_core::FiniteFieldSort::new)
                            .ok_or_else(|| {
                                ElaborateError::InvalidConstant("unsupported prime field".into())
                            })?;
                        if !matches!(self.logic(), None | Some("ALL" | "QF_FF")) {
                            return Err(ElaborateError::InvalidConstant(
                                "finite-field literal outside field logic".into(),
                            ));
                        }
                        let n: BigInt = value
                            .parse()
                            .map_err(|_| ElaborateError::InvalidConstant(name.clone()))?;
                        let p = BigInt::from(field.modulus());
                        use num_traits::ToPrimitive;
                        let residue = ((n % &p + &p) % &p)
                            .to_u32()
                            .ok_or_else(|| ElaborateError::InvalidConstant(name.clone()))?;
                        return Ok(self.terms.mk_finite_field(residue, field));
                    }
                }
                Err(ElaborateError::UndefinedSymbol(name.clone()))
            }
            // A `let`, quantifier, `match` or parameter variable shadows every
            // function of its name, so `(g 1)` applies the variable: z3 reads
            // it as `select` on an array variable and rejects it otherwise.
            // Neither is modeled; resolving the global `g` would give the term
            // another meaning.
            ParsedTerm::App(name, args) if !args.is_empty() && env.contains_key(name) => {
                Err(ElaborateError::Unsupported(format!(
                    "the bound variable '{name}' is applied to arguments"
                )))
            }
            // The same shadowing under a sort ascription: z3 reads `(as k S)`
            // as the variable `k` and `((as g S) 1)` as `g` applied. The
            // ascription is resolved against the declarations here, so either
            // would mean the global.
            ParsedTerm::QualifiedApp(QualifiedIdentifier::Symbol(name), _, _)
                if env.contains_key(name) =>
            {
                Err(ElaborateError::Unsupported(format!(
                    "the bound variable '{name}' is qualified with `as`"
                )))
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
                // The legacy per-level clone remains below as a local reference
                // implementation; B24 retired its runtime A/B switch.
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
                    // Dead bindings in scope, by sort. z3 reads their values,
                    // and a dead value may name an earlier dead binding.
                    let mut dead_scope: HashMap<String, Sort> = HashMap::default();
                    let mut level_dead: Vec<(String, Sort)> = Vec::new();
                    for (level, flags) in levels.iter().zip(live.iter()) {
                        // Elaborate EVERY value of this level first, reading only
                        // the pre-level env, and publish them together afterwards.
                        level_values.clear();
                        level_dead.clear();
                        for ((name, value), &is_live) in level.iter().zip(flags.iter()) {
                            if !is_live {
                                // Dead binding: not elaborated or interned,
                                // but z3 reads it (`skipped_subterms`).
                                if let Some(sort) =
                                    self.check_skipped_subterm(value, &new_env, &dead_scope)?
                                {
                                    level_dead.push((name.clone(), sort));
                                }
                                continue;
                            }
                            let value_id = self.elaborate_term(value, &new_env)?;
                            level_values.push((name.clone(), value_id));
                        }
                        for (name, value_id) in level_values.drain(..) {
                            dead_scope.remove(&name);
                            new_env.insert(name, value_id);
                        }
                        for (name, sort) in level_dead.drain(..) {
                            dead_scope.insert(name, sort);
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
                            // Dead binding: not elaborated or interned, but z3
                            // reads it (`skipped_subterms`).
                            self.check_skipped_subterm(value, env, &HashMap::default())?;
                            continue;
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
                self.check_z3_quantifier_binders(bindings)?;
                // Elaborate quantifier bindings and body
                // Create fresh variables for the bound variables
                let mut new_env = env.clone();
                let mut vars: Vec<(String, Sort)> = Vec::new();
                let mut binder_ids: Vec<TermId> = Vec::with_capacity(bindings.len());
                for (name, sort) in bindings {
                    let sort = self.elaborate_sort(sort)?;
                    let var = self.terms.mk_fresh_var(name, sort.clone());
                    new_env.insert(name.clone(), var);
                    binder_ids.push(var);
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
                let (body_id, mut attributes) = self.with_label_binders(&binder_ids, |ctx| {
                    ctx.elaborate_quantifier_body_with_attributes(body, &new_env)
                })?;
                self.require_boolean_quantifier_body(body_id)?;
                let quantifier = self.terms.mk_forall_with_triggers(
                    vars,
                    body_id,
                    std::mem::take(&mut attributes.triggers),
                );
                if let Some(shared) =
                    self.share_alpha_equivalent_quantifier(quantifier, &attributes)
                {
                    return Ok(shared);
                }
                self.attach_quantifier_attributes(quantifier, attributes);
                Ok(quantifier)
            }
            ParsedTerm::Exists(bindings, body) => {
                self.check_z3_quantifier_binders(bindings)?;
                // Elaborate quantifier bindings and body
                let mut new_env = env.clone();
                let mut vars: Vec<(String, Sort)> = Vec::new();
                let mut binder_ids: Vec<TermId> = Vec::with_capacity(bindings.len());
                for (name, sort) in bindings {
                    let sort = self.elaborate_sort(sort)?;
                    let var = self.terms.mk_fresh_var(name, sort.clone());
                    new_env.insert(name.clone(), var);
                    binder_ids.push(var);
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
                let (body_id, mut attributes) = self.with_label_binders(&binder_ids, |ctx| {
                    ctx.elaborate_quantifier_body_with_attributes(body, &new_env)
                })?;
                self.require_boolean_quantifier_body(body_id)?;
                let quantifier = self.terms.mk_exists_with_triggers(
                    vars,
                    body_id,
                    std::mem::take(&mut attributes.triggers),
                );
                if let Some(shared) =
                    self.share_alpha_equivalent_quantifier(quantifier, &attributes)
                {
                    return Ok(shared);
                }
                self.attach_quantifier_attributes(quantifier, attributes);
                Ok(quantifier)
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
                let body_result =
                    self.with_label_binders(&vars, |ctx| ctx.elaborate_term(body, &new_env));
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

                self.process_term_annotations(term, inner, term_id, annotations, env)?;

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
        // Sorts of the case bodies passed over, which z3 still reads.
        let mut skipped_sorts: Vec<Sort> = Vec::new();

        for (pattern, body) in cases {
            if has_default {
                // A catch-all already decides every scrutinee value, so a
                // later case is never taken. z3 still reads it: its pattern
                // is checked here and its body where it stands.
                let binders: HashMap<String, Sort> = self
                    .match_case_binders(&ctor_internals, &dt_name, &scrut_sort, pattern)?
                    .into_iter()
                    .collect();
                skipped_sorts.extend(self.check_skipped_subterm(body, env, &binders)?);
                continue;
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
                            TermData::Const(Constant::Bool(false)) => {
                                skipped_sorts.extend(self.check_skipped_subterm(
                                    body,
                                    env,
                                    &HashMap::default(),
                                )?);
                            }
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
                        let binders: HashMap<String, Sort> = vars
                            .iter()
                            .zip(selectors.iter())
                            .filter(|(var, _)| var.as_str() != "_")
                            .map(|(var, (_, sort))| (var.clone(), sort.clone()))
                            .collect();
                        skipped_sorts.extend(self.check_skipped_subterm(body, env, &binders)?);
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

        // Every case body, taken or passed over, must have one sort, as z3
        // checks. A differing sort is left unsupported rather than joined:
        // z3 rejects most pairs and joins an Int and a Real, and an `ite`
        // over bodies of different sorts has no reading here.
        if let Some(&(_, first_body)) = branches.first() {
            let taken_sort = self.terms.sort(first_body).clone();
            let differing = branches
                .iter()
                .map(|&(_, body)| self.terms.sort(body))
                .chain(skipped_sorts.iter())
                .find(|sort| **sort != taken_sort);
            if let Some(sort) = differing {
                return Err(ElaborateError::Unsupported(format!(
                    "match cases have bodies of sorts {taken_sort} and {sort}"
                )));
            }
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
    pub(super) fn datatype_ctor_internal(
        &self,
        ctor_internals: &[String],
        surface: &str,
    ) -> Option<String> {
        ctor_internals
            .iter()
            .find(|ci| self.dt_surface_name(ci).unwrap_or(ci.as_str()) == surface)
            .cloned()
    }

    pub(super) fn process_term_annotations(
        &mut self,
        node: &ParsedTerm,
        inner: &ParsedTerm,
        term_id: TermId,
        annotations: &[(String, SExpr)],
        env: &HashMap<String, TermId>,
    ) -> Result<()> {
        for (index, (keyword, value)) in annotations.iter().enumerate() {
            if keyword == ":named" {
                self.record_label(node, index, inner, term_id, value, env)?;
            } else if matches!(keyword.as_str(), ":lblpos" | ":lblneg") {
                self.validate_label_annotation(term_id, keyword, value)?;
            } else if matches!(
                keyword.as_str(),
                ":weight" | ":no-pattern" | ":qid" | ":skolemid" | ":pattern"
            ) {
                return Err(ElaborateError::Unsupported(format!(
                    "quantifier attribute {keyword} is not directly in the scope of a quantifier"
                )));
            }
        }
        Ok(())
    }

    fn validate_label_annotation(
        &self,
        term_id: TermId,
        keyword: &str,
        value: &SExpr,
    ) -> Result<()> {
        if !matches!(value, SExpr::Symbol(_)) {
            return Err(ElaborateError::Unsupported(format!(
                "{keyword} expects a symbol"
            )));
        }
        if self.terms.sort(term_id) != &Sort::Bool {
            return Err(ElaborateError::Unsupported(format!(
                "{keyword} expects a Boolean expression"
            )));
        }
        Ok(())
    }

    pub(super) fn record_named_term(&mut self, term_id: TermId, value: &SExpr) {
        if let SExpr::Symbol(name) = value {
            self.named_terms.insert(name.clone(), term_id);
            // Track in current scope for proper cleanup on pop.
            if let Some(scope) = self.scopes.last_mut() {
                scope.named_terms.push(name.clone());
            }
        }
    }

    fn elaborate_quantifier_body_with_attributes(
        &mut self,
        body: &ParsedTerm,
        env: &HashMap<String, TermId>,
    ) -> Result<(TermId, ElaboratedQuantifierAttributes)> {
        let ParsedTerm::Annotated(inner, annotations) = body else {
            return Ok((
                self.elaborate_term(body, env)?,
                ElaboratedQuantifierAttributes::default(),
            ));
        };

        let mut attributes = ElaboratedQuantifierAttributes {
            triggers: self.elaborate_user_triggers_from_annotations(annotations, env)?,
            ..ElaboratedQuantifierAttributes::default()
        };

        for (keyword, value) in annotations {
            match keyword.as_str() {
                ":no-pattern" => {
                    let term = ParsedTerm::from_sexp(value).map_err(|error| {
                        ElaborateError::Unsupported(format!("invalid :no-pattern term: {error}"))
                    })?;
                    attributes
                        .no_patterns
                        .push(self.elaborate_term(&term, env)?);
                }
                ":weight" => {
                    let SExpr::Numeral(value) = value else {
                        return Err(ElaborateError::Unsupported(
                            ":weight expects an unsigned integer".to_string(),
                        ));
                    };
                    attributes.weight = value.parse::<u32>().map_err(|_| {
                        ElaborateError::Unsupported(
                            ":weight must fit in an unsigned 32-bit integer".to_string(),
                        )
                    })?;
                }
                ":qid" => {
                    let SExpr::Symbol(value) = value else {
                        return Err(ElaborateError::Unsupported(
                            ":qid expects a symbol".to_string(),
                        ));
                    };
                    attributes.qid = Some(value.clone());
                }
                ":skolemid" => {
                    let SExpr::Symbol(value) = value else {
                        return Err(ElaborateError::Unsupported(
                            ":skolemid expects a symbol".to_string(),
                        ));
                    };
                    attributes.skolem_id = Some(value.clone());
                }
                ":pattern" | ":named" | ":lblpos" | ":lblneg" => {}
                _ => {}
            }
        }

        if !attributes.triggers.is_empty() && !attributes.no_patterns.is_empty() {
            return Err(ElaborateError::Unsupported(
                "simultaneous :pattern and :no-pattern attributes are not supported by Z3"
                    .to_string(),
            ));
        }

        let body_id = self.elaborate_term(inner, env)?;
        for (index, (keyword, value)) in annotations.iter().enumerate() {
            if keyword == ":named" {
                self.record_label(body, index, inner, body_id, value, env)?;
            } else if matches!(keyword.as_str(), ":lblpos" | ":lblneg") {
                self.validate_label_annotation(body_id, keyword, value)?;
            }
        }
        Ok((body_id, attributes))
    }

    /// Reject a quantifier whose body is not Boolean, after its body and
    /// attributes are read, as every z3 does ("quantifier body must be a
    /// Boolean expression"). The term store has no reading for such a
    /// quantifier.
    fn require_boolean_quantifier_body(&self, body: TermId) -> Result<()> {
        let sort = self.terms.sort(body);
        if *sort == Sort::Bool {
            return Ok(());
        }
        Err(ElaborateError::IllSorted(format!(
            "quantifier body must be a Boolean expression, got {sort}"
        )))
    }

    /// Under [`Context::set_z3_mode`], reject a quantifier with no bound
    /// variable before its body is read, as every z3 does. Elsewhere the
    /// quantifier reads as its body.
    fn check_z3_quantifier_binders(&self, bindings: &[(String, ParsedSort)]) -> Result<()> {
        if self.z3_mode && bindings.is_empty() {
            return Err(ElaborateError::IllSorted(
                "invalid quantifier, list of sorted variables is empty".to_string(),
            ));
        }
        Ok(())
    }

    /// Under [`Context::set_z3_mode`], reject a `:pattern` term that is a
    /// variable or a quantifier, as every z3 does. A `let` name counts as a
    /// variable here, so this may reject a pattern z3 accepts, never the
    /// reverse.
    fn check_z3_pattern_term(
        &self,
        term: &ParsedTerm,
        env: &HashMap<String, TermId>,
    ) -> Result<()> {
        let rejected = match term {
            ParsedTerm::Symbol(name) => env.contains_key(name),
            ParsedTerm::Forall(..) | ParsedTerm::Exists(..) | ParsedTerm::Lambda(..) => true,
            _ => false,
        };
        if self.z3_mode && rejected {
            return Err(ElaborateError::IllSorted(
                "patterns cannot be variables or quantifiers".to_string(),
            ));
        }
        Ok(())
    }

    fn attach_quantifier_attributes(
        &mut self,
        quantifier: TermId,
        attributes: ElaboratedQuantifierAttributes,
    ) {
        self.terms
            .set_quantifier_weight(quantifier, attributes.weight);
        self.terms
            .set_quantifier_no_patterns(quantifier, attributes.no_patterns);
        if let Some(qid) = attributes.qid {
            self.terms.set_quantifier_id(quantifier, qid);
        }
        if let Some(skolem_id) = attributes.skolem_id {
            self.terms.set_skolem_id(quantifier, skolem_id);
        }
    }

    fn elaborate_user_triggers_from_annotations(
        &mut self,
        annotations: &[(String, SExpr)],
        env: &HashMap<String, TermId>,
    ) -> Result<Vec<Vec<TermId>>> {
        let mut triggers = Vec::new();

        for (keyword, value) in annotations {
            if keyword != ":pattern" {
                continue;
            }

            let SExpr::List(terms) = value else {
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
                self.check_z3_pattern_term(&term, env)?;
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
                if self.numeral_as_real() {
                    Ok(self.terms.mk_rational(BigRational::from(value)))
                } else {
                    Ok(self.terms.mk_int(value))
                }
            }
            ParsedConstant::Decimal(s) => {
                // Parse as rational. The sign of an unquoted `-2.5` belongs to
                // the whole value: reading `-2` and `5` apart and adding them
                // would make it -1.5.
                let (negative, magnitude) = s
                    .strip_prefix('-')
                    .map_or((false, s.as_str()), |magnitude| (true, magnitude));
                let parts: Vec<&str> = magnitude.split('.').collect();
                if parts.len() == 2 {
                    let digits = |part: &str| {
                        if part.is_empty() || !part.bytes().all(|byte| byte.is_ascii_digit()) {
                            return Err(ElaborateError::InvalidConstant(s.clone()));
                        }
                        part.parse::<BigInt>()
                            .map_err(|_| ElaborateError::InvalidConstant(s.clone()))
                    };
                    let int_part = digits(parts[0])?;
                    let frac_str = parts[1];
                    let frac_part = digits(frac_str)?;
                    let denom = BigInt::from(10).pow(frac_str.len() as u32);
                    let numer = int_part * &denom + frac_part;
                    let numer = if negative { -numer } else { numer };
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

    /// Apply Z3's arithmetic-only Bool-to-Int coercion before the shared
    /// Int/Real promotion pass.
    ///
    /// [`Self::maybe_promote_numeric_args`] is also used by polymorphic core
    /// operators such as `=` and `distinct`. Those operators must preserve a
    /// homogeneous Bool argument list as Bool (#8481), while arithmetic
    /// applications in Z3 5.0.0 interpret each Bool as `(ite b 1 0)`. Keeping
    /// that distinction at the call site prevents arithmetic's coercion rule
    /// from changing the sort of ordinary Boolean equality.
    pub(super) fn maybe_promote_arithmetic_args(&mut self, args: &mut [TermId]) -> Result<()> {
        self.check_arithmetic_operand_sorts(args)?;
        for arg in args.iter_mut() {
            if self.terms.sort(*arg) != &Sort::Bool {
                continue;
            }
            if !self.int_real_coercions() || !self.logic_allows_bool_to_int_coercion() {
                return Err(ElaborateError::SortMismatch {
                    expected: "Int or Real".to_string(),
                    actual: Sort::Bool.to_string(),
                });
            }
            let one = self.terms.mk_int(BigInt::from(1));
            let zero = self.terms.mk_int(BigInt::from(0));
            *arg = self.terms.mk_ite(*arg, one, zero);
        }
        self.maybe_promote_numeric_args(args)
    }

    /// Arithmetic operands z3 accepts: Int, Real and Bool (read as
    /// `(ite b 1 0)`), in z3 4.12.5 and z3 5 alike. Under
    /// [`Context::set_z3_mode`] any other operand is z3's sort error.
    /// Elsewhere a bit-vector operand beside a number is read as its `bv2nat`
    /// value (`maybe_promote_numeric_args`), which the CHC engine's
    /// bit-vector-to-Int abstraction relies on, and an authored assertion's
    /// labels after it are not taken to be z3's. Any other operand, and
    /// operands none of which is a number or a Bool (which nothing would
    /// promote, leaving an arithmetic term over bit-vectors), are a sort
    /// error in every mode.
    pub(super) fn check_arithmetic_operand_sorts(&mut self, args: &[TermId]) -> Result<()> {
        let is_numeric = |sort: &Sort| matches!(sort, Sort::Bool | Sort::Int | Sort::Real);
        let Some(other) = args
            .iter()
            .map(|&arg| self.terms.sort(arg))
            .find(|sort| !is_numeric(sort))
        else {
            return Ok(());
        };
        let promoted = matches!(other, Sort::BitVec(_))
            && args.iter().all(|&arg| {
                let sort = self.terms.sort(arg);
                is_numeric(sort) || matches!(sort, Sort::BitVec(_))
            })
            && args.iter().any(|&arg| is_numeric(self.terms.sort(arg)));
        if self.z3_mode || !promoted {
            return Err(ElaborateError::SortMismatch {
                expected: "Int or Real".to_string(),
                actual: other.to_string(),
            });
        }
        self.note_construct_z3_may_reject();
        Ok(())
    }

    pub(super) fn maybe_promote_numeric_args(&mut self, args: &mut [TermId]) -> Result<()> {
        if !self.int_real_coercions() {
            if let Some(first) = args.first() {
                let expected = self.terms.sort(*first).clone();
                if let Some(actual) = args
                    .iter()
                    .skip(1)
                    .map(|arg| self.terms.sort(*arg))
                    .find(|actual| *actual != &expected)
                {
                    return Err(ElaborateError::SortMismatch {
                        expected: expected.to_string(),
                        actual: actual.to_string(),
                    });
                }
            }
            return Ok(());
        }

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
    pub(super) fn check_chain_sorts(&mut self, arg_ids: &[TermId]) -> Result<()> {
        let Some((first, rest)) = arg_ids.split_first() else {
            return Ok(());
        };
        let mut acc = self.terms.sort(*first).clone();
        for &next in rest {
            let ns = self.terms.sort(next).clone();
            let ns = &ns;
            if *ns == acc {
                // Identity: a matching sort is always well-sorted, INCLUDING
                // non-coercible sorts (Seq, Array, datatype, uninterpreted,
                // same-width BitVec, FloatingPoint, String, ...).
                continue;
            }
            if self.int_real_coercions()
                && arith_coercible(&acc)
                && arith_coercible(ns)
                && !self.z3_rejects_bool_beside_number(&acc, ns)
            {
                self.note_bool_beside_number(&acc, ns);
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

    /// Under [`Context::set_z3_mode`], whether `=`, `distinct` or `ite` must
    /// reject a Bool beside an Int or a Real, as z3 4.12.5 does ("Sorts Bool
    /// and Int are incompatible"). z3 5 coerces the Bool; rejecting is the
    /// reading that drops an assertion, never adds one, against either.
    pub(super) fn z3_rejects_bool_beside_number(&self, left: &Sort, right: &Sort) -> bool {
        self.z3_mode && (*left == Sort::Bool) != (*right == Sort::Bool)
    }

    /// A Bool accepted beside a number in `=`, `distinct` or `ite` (outside
    /// z3 mode) is read differently by z3 4.12.5 and z3 5.
    pub(super) fn note_bool_beside_number(&mut self, left: &Sort, right: &Sort) {
        if (*left == Sort::Bool) != (*right == Sort::Bool) {
            self.note_construct_z3_may_reject();
        }
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

/// Binder count beyond which a quantifier is not offered for alpha sharing.
const MAX_ALPHA_SHARE_BINDERS: usize = 8;
/// Candidates compared per index key.
const MAX_ALPHA_SHARE_CANDIDATES: usize = 8;
/// Quantifiers indexed per index key.
const MAX_ALPHA_SHARE_INDEXED: usize = 256;
/// Node visits one alpha-equivalence comparison may spend.
const MAX_ALPHA_SHARE_WORK: usize = 200_000;
/// Depth beyond which the alpha-invariant shape hash stops descending.
const MAX_ALPHA_SHAPE_DEPTH: u32 = 4;
/// Children per node the alpha-invariant shape hash descends into.
const MAX_ALPHA_SHAPE_FANOUT: usize = 8;
/// Argument count beyond which a commutative application is not multiset-matched.
const MAX_ALPHA_COMMUTATIVE_ARITY: usize = 8;

/// The symbols the TERM STORE itself canonicalizes by ascending `TermId`:
/// `mk_eq` and `mk_xor` swap their two operands, `mk_and`/`mk_or` sort theirs,
/// and `mk_mul`/`mk_add` sort factors and summands. Ordering under these
/// carries NO meaning — the store only imposes it to hash-cons commutative
/// spellings together — and every one of them is genuinely commutative.
///
/// This is why it matters here. A bound variable's `TermId` depends on WHEN
/// the binder was minted, so the same formula elaborated twice can sort
/// `(= x c)` one way and `(= c x)` the other. That is not an alpha-variance
/// the structural walk can see in child order, so [`alpha_equivalent_under`]
/// matches these arguments as a MULTISET and [`alpha_shape_hash`] combines
/// their hashes order-independently.
///
/// Membership is a SOUNDNESS obligation: permuting the arguments of a
/// non-commutative symbol would equate `(- a b)` with `(- b a)`. Only add a
/// symbol here after checking the store canonicalizes its argument order.
const ID_SORTED_COMMUTATIVE_SYMBOLS: &[&str] = &["=", "and", "or", "xor", "*", "+"];

fn is_id_sorted_commutative(symbol: &Symbol) -> bool {
    matches!(symbol, Symbol::Named(_)) && ID_SORTED_COMMUTATIVE_SYMBOLS.contains(&symbol.name())
}

/// Hash a term's structure with every VARIABLE IDENTITY erased.
///
/// Alpha-equivalent terms have identical structure, identical constants and
/// symbols, and matching sorts at every node — they differ only in which names
/// the binders minted, and (for the symbols in
/// [`ID_SORTED_COMMUTATIVE_SYMBOLS`]) in the resulting argument order. Erasing
/// variable identity and combining those arguments commutatively therefore
/// makes this hash EQUAL for any two alpha-equivalent terms, which is what
/// makes it a sound bucket key for [`Context::alpha_share_key`]: a share can
/// never be missed because the two sides landed in different buckets.
///
/// It is deliberately coarse in the other direction — `(P x)` and `(P y)` for
/// two distinct FREE variables collide, as do two terms that first differ below
/// [`MAX_ALPHA_SHAPE_DEPTH`] — because `alpha_equivalent_under` re-derives the
/// real equivalence before anything is shared. A collision costs one
/// comparison.
///
/// The walk is bounded by DEPTH and FANOUT rather than by a running node
/// budget, so where it stops is a property of the shape alone: two
/// alpha-equivalent terms are always truncated at the same places, and the
/// walk visits at most `MAX_ALPHA_SHAPE_FANOUT ^ MAX_ALPHA_SHAPE_DEPTH` nodes.
fn alpha_shape_hash(terms: &ay_core::TermStore, root: TermId) -> u64 {
    alpha_shape_of(terms, root, MAX_ALPHA_SHAPE_DEPTH)
}

fn alpha_shape_of(terms: &ay_core::TermStore, id: TermId, depth: u32) -> u64 {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    // Below the depth limit every subterm contributes the same marker.
    if depth == 0 {
        return 0x9E37_79B9_7F4A_7C15;
    }
    let mut hasher = DefaultHasher::new();
    terms.sort(id).hash(&mut hasher);
    let mut ordered_children = DefaultHasher::new();
    let mut ordered_child_count = 0usize;
    let mut hash_ordered_child = |child| {
        ordered_child_count += 1;
        alpha_shape_of(terms, child, depth - 1).hash(&mut ordered_children);
    };
    let mut children_commutative: u64 = 0;
    match terms.get(id) {
        TermData::Const(constant) => {
            0u8.hash(&mut hasher);
            constant.hash(&mut hasher);
        }
        // Identity erased: this is the whole point of the hash.
        TermData::Var(_, _) => 1u8.hash(&mut hasher),
        TermData::App(symbol, args) => {
            2u8.hash(&mut hasher);
            symbol.hash(&mut hasher);
            args.len().hash(&mut hasher);
            let considered = args.iter().take(MAX_ALPHA_SHAPE_FANOUT);
            if is_id_sorted_commutative(symbol) {
                for &arg in considered {
                    // `wrapping_add` is commutative, so the store's TermId
                    // ordering cannot change this sum.
                    children_commutative =
                        children_commutative.wrapping_add(alpha_shape_of(terms, arg, depth - 1));
                }
            } else {
                for &arg in considered {
                    hash_ordered_child(arg);
                }
            }
        }
        TermData::Not(inner) => {
            3u8.hash(&mut hasher);
            hash_ordered_child(*inner);
        }
        TermData::Ite(condition, then_branch, else_branch) => {
            4u8.hash(&mut hasher);
            for branch in [*condition, *then_branch, *else_branch] {
                hash_ordered_child(branch);
            }
        }
        TermData::Forall(vars, body, triggers) | TermData::Exists(vars, body, triggers) => {
            if matches!(terms.get(id), TermData::Forall(..)) {
                5u8.hash(&mut hasher);
            } else {
                6u8.hash(&mut hasher);
            }
            for (_, sort) in vars {
                sort.hash(&mut hasher);
            }
            hash_ordered_child(*body);
            triggers.len().hash(&mut hasher);
            for multi in triggers.iter().take(MAX_ALPHA_SHAPE_FANOUT) {
                multi.len().hash(&mut hasher);
                for &trigger in multi.iter().take(MAX_ALPHA_SHAPE_FANOUT) {
                    hash_ordered_child(trigger);
                }
            }
        }
        // `Let` is refused by `alpha_equivalent_under`, and any variant added
        // later must fall here rather than silently hash as something else.
        other => {
            7u8.hash(&mut hasher);
            std::mem::discriminant(other).hash(&mut hasher);
        }
    }
    ordered_child_count.hash(&mut hasher);
    ordered_children.finish().hash(&mut hasher);
    children_commutative.hash(&mut hasher);
    hasher.finish()
}

/// Structural alpha-equivalence of `left` and `right` under the binder
/// correspondence `forward` (left name -> right name) and its inverse.
///
/// Deliberately has NO `a == b` fast path: `(exists ((x1 Int)) (P x1))` and
/// `(exists ((x2 Int)) (P x1))` share the interned body `(P x1)`, and they are
/// NOT alpha-equivalent — the first occurrence of `x1` is bound and the second
/// free. Every leaf is therefore judged against the correspondence.
///
/// Fail-closed: `Let` is refused outright (its bindings are a second binder
/// form this walk does not model), and an exhausted work budget answers
/// `false`.
fn alpha_equivalent_under(
    terms: &ay_core::TermStore,
    left: TermId,
    right: TermId,
    forward: &mut HashMap<String, String>,
    backward: &mut HashMap<String, String>,
    work: &mut usize,
) -> bool {
    if *work == 0 {
        return false;
    }
    *work -= 1;
    if terms.sort(left) != terms.sort(right) {
        return false;
    }
    match (terms.get(left), terms.get(right)) {
        (TermData::Const(a), TermData::Const(b)) => a == b,
        (TermData::Var(a, _), TermData::Var(b, _)) => match (forward.get(a), backward.get(b)) {
            (Some(mapped), Some(back)) => mapped == b && back == a,
            (None, None) => a == b,
            _ => false,
        },
        (TermData::App(sa, aa), TermData::App(sb, ab)) => {
            if sa != sb || aa.len() != ab.len() {
                return false;
            }
            let commutative = is_id_sorted_commutative(sa);
            let (aa, ab) = (aa.clone(), ab.clone());
            if aa
                .iter()
                .zip(ab.iter())
                .all(|(&x, &y)| alpha_equivalent_under(terms, x, y, forward, backward, work))
            {
                return true;
            }
            // In-order matching failed. For a symbol the store canonicalizes by
            // ascending `TermId` the order carries no meaning, and a bound
            // variable's id depends on WHEN its binder was minted — so the same
            // formula really can come out as `(= x c)` here and `(= c x)`
            // there. Match the arguments as a multiset instead.
            //
            // Greedy, and deliberately so: a comparison never leaves the binder
            // correspondence altered (the quantifier arm restores it on every
            // exit), so the pairing order cannot change any answer, and the
            // worst case of a greedy miss is one share not taken.
            if !commutative || aa.len() > MAX_ALPHA_COMMUTATIVE_ARITY {
                return false;
            }
            let mut taken = vec![false; ab.len()];
            for &left in &aa {
                let mut matched = false;
                for (index, &right) in ab.iter().enumerate() {
                    if taken[index] {
                        continue;
                    }
                    if alpha_equivalent_under(terms, left, right, forward, backward, work) {
                        taken[index] = true;
                        matched = true;
                        break;
                    }
                }
                if !matched {
                    return false;
                }
            }
            true
        }
        (TermData::Not(a), TermData::Not(b)) => {
            let (a, b) = (*a, *b);
            alpha_equivalent_under(terms, a, b, forward, backward, work)
        }
        (TermData::Ite(ca, ta, ea), TermData::Ite(cb, tb, eb)) => {
            let (ca, ta, ea, cb, tb, eb) = (*ca, *ta, *ea, *cb, *tb, *eb);
            alpha_equivalent_under(terms, ca, cb, forward, backward, work)
                && alpha_equivalent_under(terms, ta, tb, forward, backward, work)
                && alpha_equivalent_under(terms, ea, eb, forward, backward, work)
        }
        (TermData::Forall(va, ba, ta), TermData::Forall(vb, bb, tb))
        | (TermData::Exists(va, ba, ta), TermData::Exists(vb, bb, tb)) => {
            if va.len() != vb.len() || ta.len() != tb.len() {
                return false;
            }
            if ta.iter().zip(tb.iter()).any(|(a, b)| a.len() != b.len()) {
                return false;
            }
            let (va, vb) = (va.clone(), vb.clone());
            let (ba, bb) = (*ba, *bb);
            // Triggers are INTERNED into `TermData`, not attached to the id, so
            // they are part of the formula's identity here and are compared
            // under the very same binder correspondence as the body. Their
            // order is significant: a reordering answers `false`, which only
            // costs a share.
            let (ta, tb) = (ta.clone(), tb.clone());
            if va.iter().zip(vb.iter()).any(|(a, b)| a.1 != b.1) {
                return false;
            }
            let saved: Vec<(String, String, Option<String>, Option<String>)> = va
                .iter()
                .zip(vb.iter())
                .map(|(a, b)| {
                    (
                        a.0.clone(),
                        b.0.clone(),
                        forward.insert(a.0.clone(), b.0.clone()),
                        backward.insert(b.0.clone(), a.0.clone()),
                    )
                })
                .collect();
            let mut equal = alpha_equivalent_under(terms, ba, bb, forward, backward, work);
            if equal {
                'triggers: for (multi_a, multi_b) in ta.iter().zip(tb.iter()) {
                    for (&left_trigger, &right_trigger) in multi_a.iter().zip(multi_b.iter()) {
                        if !alpha_equivalent_under(
                            terms,
                            left_trigger,
                            right_trigger,
                            forward,
                            backward,
                            work,
                        ) {
                            equal = false;
                            break 'triggers;
                        }
                    }
                }
            }
            for (left_name, right_name, old_forward, old_backward) in saved.into_iter().rev() {
                match old_forward {
                    Some(previous) => {
                        forward.insert(left_name, previous);
                    }
                    None => {
                        forward.remove(&left_name);
                    }
                }
                match old_backward {
                    Some(previous) => {
                        backward.insert(right_name, previous);
                    }
                    None => {
                        backward.remove(&right_name);
                    }
                }
            }
            equal
        }
        _ => false,
    }
}

impl Context {
    /// Reuse an already-elaborated alpha-equivalent quantifier for `quantifier`,
    /// or index it for later occurrences (#alpha-quantifier-sharing).
    ///
    /// WHY THIS EXISTS. Elaborating a quantifier mints a globally unique name
    /// for each binder, so
    ///
    /// ```smt2
    /// (assert (and G (exists ((v Int)) phi)))
    /// (assert (not   (exists ((v Int)) phi)))
    /// ```
    ///
    /// produces two DIFFERENT existential terms — `v_3` and `v_6` — and the
    /// one-resolution-step refutation is invisible to everything downstream:
    /// the quantifier proxy abstraction mints two unrelated proxies, the
    /// authored `and`-conjunct closure holds no complementary pair, and the
    /// artifact firewall has nothing to translate. MEASURED on LIA
    /// `UltimateAutomizer recHanoi03 …_557` and `…_874`, whose whole gap this
    /// is.
    ///
    /// SOUNDNESS. Alpha-equivalent formulas ARE the same formula, so returning
    /// the earlier term is an identity, not a rewrite. The index is only a
    /// hint: `alpha_equivalent_under` re-derives the equivalence structurally
    /// against the live store at this exact moment, so a stale, rolled-back or
    /// foreign candidate can only fail and leave `quantifier` as built. No
    /// capture is possible either — alpha-equivalence requires the FREE parts
    /// to be identical terms, and the reused binder names are the globally
    /// unique ones the earlier occurrence minted.
    ///
    /// Deliberately narrow on the INCOMING side: a `:qid`, `:skolem-id`,
    /// `:no-pattern` or non-default `:weight` on the quantifier being
    /// elaborated disqualifies sharing outright, because those attributes are
    /// attached to the TermId rather than interned into it and sharing skips
    /// `attach_quantifier_attributes` — reusing an earlier term would DROP
    /// them. The candidate side is deliberately NOT screened: a candidate can
    /// acquire metadata at any later moment (the native API attaches `:qid`
    /// and the no-MBQI mark after building the term), so screening here would
    /// be a half-guarantee that merely made a natively built binder
    /// unrecoverable from its own retained source. Inheriting a candidate's
    /// hints is sound in any case — they restrict instantiation, which can
    /// only lose proofs, never produce a wrong `unsat`.
    ///
    /// Triggers, by contrast, ARE interned into `TermData`, so they are part of
    /// the formula's identity and are compared structurally under the binder
    /// correspondence like the body.
    /// Kill switch: `--no-alpha-quantifier-sharing`.
    fn share_alpha_equivalent_quantifier(
        &mut self,
        quantifier: TermId,
        attributes: &ElaboratedQuantifierAttributes,
    ) -> Option<TermId> {
        if ay_core::misc_cli_flags().no_alpha_quantifier_sharing {
            return None;
        }
        if !attributes.no_patterns.is_empty()
            || attributes.weight != ElaboratedQuantifierAttributes::default().weight
            || attributes.qid.is_some()
            || attributes.skolem_id.is_some()
        {
            return None;
        }
        let key = self.alpha_share_key(quantifier)?;
        let candidates: Vec<TermId> = self
            .alpha_quantifier_index
            .get(&key)
            .map(|bucket| {
                bucket
                    .iter()
                    .rev()
                    .take(MAX_ALPHA_SHARE_CANDIDATES)
                    .copied()
                    .collect()
            })
            .unwrap_or_default();
        for candidate in candidates {
            if candidate == quantifier {
                // Already interned to the same term: nothing to share, and the
                // caller's attributes still have to be attached.
                return None;
            }
            // LIVENESS FIRST, and it is not paranoia: `TermStore::get` indexes
            // without a bounds check, and a speculative rollback SHRINKS the
            // store, so an indexed id from before a rollback would PANIC inside
            // the comparison rather than fail it. `entry_stamp` is the
            // bounds-checked accessor. Slot REUSE needs no separate guard: the
            // structural comparison below re-derives the equivalence against
            // whatever the slot holds now, so a recycled id simply does not
            // match. Measured: without this the quantifier finite-table tests
            // abort with "index out of bounds: the len is 7 but the index is 8".
            if self.terms.entry_stamp(candidate).is_none() {
                continue;
            }
            let mut work = MAX_ALPHA_SHARE_WORK;
            let mut forward = HashMap::default();
            let mut backward = HashMap::default();
            if alpha_equivalent_under(
                &self.terms,
                candidate,
                quantifier,
                &mut forward,
                &mut backward,
                &mut work,
            ) {
                return Some(candidate);
            }
        }
        let bucket = self.alpha_quantifier_index.entry(key).or_default();
        if bucket.len() < MAX_ALPHA_SHARE_INDEXED {
            bucket.push(quantifier);
        }
        None
    }

    /// Offer a quantifier built OUTSIDE the surface elaborator — through the
    /// native `Solver` term API — to the same alpha-equivalence sharing index.
    ///
    /// WHY THIS EXISTS. `mk_fresh_var` mints a globally unique binder name for
    /// every quantifier occurrence, so a quantifier term is NOT canonical under
    /// alpha-renaming the way every ground term is canonical under
    /// hash-consing: re-elaborating a faithful SMT-LIB spelling of an existing
    /// binder builds an alpha-VARIANT with a different `TermId`.
    /// `share_alpha_equivalent_quantifier` is what restores that canonicity,
    /// but its index used to be populated only by the elaborator, so a natively
    /// built binder was invisible to it. `Solver::try_assert_term_with_source`
    /// then compared a natively built quantifier against a freshly elaborated
    /// one and refused every binder-carrying assertion — which aborted the
    /// whole solve under `:produce-proofs`.
    ///
    /// Registering here makes the native term the candidate the elaborator
    /// finds, so the re-elaboration lands on the very term the caller built.
    /// The identity check at the call site is untouched: it still demands one
    /// `TermId`, and that identity is now reached by an alpha-equivalence
    /// `alpha_equivalent_under` re-derives structurally against the live store.
    ///
    /// Indexing ONLY — this never returns a different term to the native
    /// builder, so no existing `TermId` changes hands.
    #[doc(hidden)]
    pub fn index_quantifier_for_alpha_sharing(&mut self, quantifier: TermId) {
        if ay_core::misc_cli_flags().no_alpha_quantifier_sharing {
            return;
        }
        let Some(key) = self.alpha_share_key(quantifier) else {
            return;
        };
        let bucket = self.alpha_quantifier_index.entry(key).or_default();
        if bucket.contains(&quantifier) {
            return;
        }
        if bucket.len() < MAX_ALPHA_SHARE_INDEXED {
            bucket.push(quantifier);
        }
    }

    /// Sharing-index key for `quantifier`, or `None` when it is not a
    /// shareable quantifier (not a binder at all, nullary, or wider than
    /// [`MAX_ALPHA_SHARE_BINDERS`]).
    ///
    /// Alpha-equivalent quantifiers always produce the SAME key — the binder
    /// sorts are compared by `alpha_equivalent_under` anyway and
    /// [`alpha_shape_hash`] erases variable identity — so bucketing can never
    /// hide a share.
    fn alpha_share_key(&self, quantifier: TermId) -> Option<(bool, Vec<Sort>, u64)> {
        let (is_forall, sorts): (bool, Vec<Sort>) = match self.terms.get(quantifier) {
            TermData::Forall(vars, _, _) => {
                (true, vars.iter().map(|(_, sort)| sort.clone()).collect())
            }
            TermData::Exists(vars, _, _) => {
                (false, vars.iter().map(|(_, sort)| sort.clone()).collect())
            }
            _ => return None,
        };
        if sorts.is_empty() || sorts.len() > MAX_ALPHA_SHARE_BINDERS {
            return None;
        }
        let shape = alpha_shape_hash(&self.terms, quantifier);
        Some((is_forall, sorts, shape))
    }
}
