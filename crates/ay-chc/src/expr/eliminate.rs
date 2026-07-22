// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Expression elimination transformations (ITE, mod/div, mixed-sort, array simplification).

use std::sync::Arc;

use ay_core::kani_compat::DetHashMap as FxHashMap;

use super::{
    maybe_grow_expr_stack, ChcExpr, ChcOp, ChcSort, ChcVar, ExprDepthGuard,
    MAX_EXPR_RECURSION_DEPTH, MAX_PREPROCESSING_NODES,
};

/// Memoization table for `simplify_array_ops`, keyed by `Arc` pointer identity.
///
/// Same contract as `SimplifyMemo` in `simplify.rs` (#7060): while the
/// top-level call holds the input alive, `Arc::as_ptr` is a stable, unique
/// key per shared subtree, so each shared `Arc` is rewritten at most once
/// per call instead of once per DAG path (item 4c: the polynomial-DAG BMC
/// encoder calls this on every conjunct of Array-of-BV clauses whose store
/// chains share large subtrees).
type ArrayOpsMemo = FxHashMap<*const ChcExpr, Arc<ChcExpr>>;

/// Shared state for expression elimination transformations (ITE, mod/div).
///
/// Both `eliminate_ite` and `eliminate_mod` need: a fresh-variable counter,
/// a list of collected definitional constraints, and a node budget (#2774).
struct EliminationState {
    /// Counter for generating unique variable names
    counter: u32,
    /// Collected definitional constraints
    constraints: Vec<ChcExpr>,
    /// Node traversal budget (#2774). Returns original expression when exhausted.
    budget: usize,
}

impl EliminationState {
    fn new() -> Self {
        Self {
            counter: 0,
            constraints: Vec::new(),
            budget: MAX_PREPROCESSING_NODES,
        }
    }

    /// Decrement budget by one. Returns false if budget is exhausted.
    fn tick(&mut self) -> bool {
        if self.budget == 0 {
            return false;
        }
        self.budget -= 1;
        true
    }

    fn fresh_var(&mut self, prefix: &str, sort: ChcSort) -> ChcVar {
        let name = format!("{}_{}", prefix, self.counter);
        self.counter += 1;
        ChcVar::new(name, sort)
    }
}

impl ChcExpr {
    pub(crate) fn positive_int_constant_expr_value(expr: &Self) -> Option<u128> {
        match expr {
            Self::Int(n) if *n > 0 => Some(*n as u128),
            Self::Op(ChcOp::Add, args) if !args.is_empty() => {
                args.iter().try_fold(0u128, |acc, arg| {
                    acc.checked_add(Self::positive_int_constant_expr_value(arg.as_ref())?)
                })
            }
            Self::Op(ChcOp::Mul, args) if !args.is_empty() => {
                args.iter().try_fold(1u128, |acc, arg| {
                    acc.checked_mul(Self::positive_int_constant_expr_value(arg.as_ref())?)
                })
            }
            _ => None,
        }
    }

    fn positive_int_constant_expr(expr: &Self) -> Option<Self> {
        let value = Self::positive_int_constant_expr_value(expr)?;
        if value == 0 {
            return None;
        }
        Some(expr.simplify_constants())
    }

    fn is_int_euclidean_dividend(expr: &Self) -> bool {
        match expr {
            Self::Int(_) => true,
            Self::Var(var) => var.sort == ChcSort::Int,
            Self::FuncApp(_, sort, _) => *sort == ChcSort::Int,
            Self::Op(ChcOp::Neg, args) if args.len() == 1 => {
                Self::is_int_euclidean_dividend(args[0].as_ref())
            }
            Self::Op(ChcOp::Add | ChcOp::Sub | ChcOp::Mul | ChcOp::Div | ChcOp::Mod, args) => args
                .iter()
                .all(|arg| Self::is_int_euclidean_dividend(arg.as_ref())),
            Self::Op(ChcOp::Ite, args) if args.len() == 3 => {
                Self::is_int_euclidean_dividend(args[1].as_ref())
                    && Self::is_int_euclidean_dividend(args[2].as_ref())
            }
            // #A3: Int-valued array reads are legitimate Euclidean dividends.
            // AUFLIA clauses use shapes like `(mod (select a i) k)`; without
            // this case the mod/div survives elimination and the ay-dpll
            // executor rejects the query with "(unsupported arithmetic)".
            Self::Op(ChcOp::Select, args) if args.len() == 2 => expr.sort() == ChcSort::Int,
            _ => false,
        }
    }

    /// Eliminate arithmetic ite expressions by introducing auxiliary variables and constraints.
    ///
    /// The CHC SMT backend ultimately relies on the LIA solver, which only supports linear
    /// integer/real arithmetic terms. Arithmetic-valued ite terms (e.g. `(ite c 1 0)`) create
    /// non-linear theory atoms like `(= x (ite ...))`, which can force the backend to return
    /// `unknown`. This pass rewrites arithmetic ite expressions into a fresh variable `v` with:
    /// - (=> c (= v t))
    /// - (=> (not c) (= v e))
    ///
    /// Boolean-valued ite expressions are left intact.
    /// If the expression tree exceeds 1M nodes, returns `self` unchanged (#2774).
    pub(crate) fn eliminate_ite(&self) -> Self {
        let mut state = EliminationState::new();
        let Some(transformed) = self.eliminate_ite_recursive(&mut state) else {
            return self.clone();
        };

        if state.constraints.is_empty() {
            transformed
        } else {
            let mut all_conjuncts = state.constraints;
            all_conjuncts.push(transformed);
            Self::and_vec(all_conjuncts)
        }
    }

    /// Eliminate mod expressions by introducing auxiliary variables and constraints.
    ///
    /// For each `(mod x k)` where k is a constant:
    /// - Introduces a fresh quotient variable q
    /// - Rewrites `(mod x k)` to `(x - k*q)` with constraints:
    ///   `0 <= (x - k*q)` and `(x - k*q) < |k|`
    ///
    /// For each `(div x k)` where k is a constant:
    /// - Introduces a fresh quotient variable q
    /// - Adds the same bounded-remainder constraints as for mod elimination
    /// - Replaces the div term with q
    ///
    /// For k = 0, follows SMT-LIB total semantics:
    /// - (mod x 0) = x
    /// - (div x 0) = 0
    ///
    /// Returns the transformed expression with all definitional constraints ANDed.
    /// If the expression tree exceeds 1M nodes, returns `self` unchanged (#2774).
    pub(crate) fn eliminate_mod(&self) -> Self {
        let mut state = EliminationState::new();
        let Some(transformed) = self.eliminate_mod_recursive(&mut state) else {
            return self.clone();
        };

        if state.constraints.is_empty() {
            transformed
        } else {
            // AND all constraints together with the transformed expression
            let mut all_conjuncts = state.constraints;
            all_conjuncts.push(transformed);
            Self::and_vec(all_conjuncts)
        }
    }

    /// Euclidean decomposition for mod/div elimination.
    ///
    /// Given `x` and non-zero divisor `k`, creates fresh variables `q` (quotient)
    /// and `r` (remainder) and adds constraints:
    ///   x = k * q + r, r >= 0, r < |k|
    ///
    /// Using named remainder/quotient variables (instead of inlining `x - k*q`)
    /// prevents expression tree duplication that causes conversion budget
    /// exhaustion in TPA's exponential composition.
    ///
    /// Returns `(quotient_var, remainder_var)`. Caller picks which to use:
    /// mod returns the remainder, div returns the quotient.
    fn euclidean_decompose(
        state: &mut EliminationState,
        x: Self,
        divisor: Self,
        abs_divisor: Self,
        prefix: &str,
    ) -> (ChcVar, ChcVar) {
        let q = state.fresh_var(&format!("_{prefix}_q"), ChcSort::Int);
        let r = state.fresh_var(&format!("_{prefix}_r"), ChcSort::Int);

        let q_expr = Self::Var(q.clone());
        let r_expr = Self::Var(r.clone());

        // x = k * q + r
        let k_times_q = Self::mul(divisor, q_expr);
        state
            .constraints
            .push(Self::eq(x, Self::add(k_times_q, r_expr.clone())));
        // r >= 0
        state
            .constraints
            .push(Self::ge(r_expr.clone(), Self::Int(0)));
        // r < |k|
        state.constraints.push(Self::lt(r_expr, abs_divisor));

        (q, r)
    }

    /// Recursive helper for ite elimination.
    /// Returns `None` if the node budget is exhausted (#2774).
    fn eliminate_ite_recursive(&self, state: &mut EliminationState) -> Option<Self> {
        maybe_grow_expr_stack(|| {
            ExprDepthGuard::check()?;
            if !state.tick() {
                return None;
            }
            Some(match self {
                Self::Bool(_) | Self::Int(_) | Self::Real(_, _) | Self::Var(_) => self.clone(),

                Self::Op(ChcOp::Ite, args) if args.len() == 3 => {
                    let cond = args[0]
                        .eliminate_ite_recursive(state)
                        .unwrap_or_else(|| args[0].as_ref().clone());
                    let then_ = args[1]
                        .eliminate_ite_recursive(state)
                        .unwrap_or_else(|| args[1].as_ref().clone());
                    let else_ = args[2]
                        .eliminate_ite_recursive(state)
                        .unwrap_or_else(|| args[2].as_ref().clone());

                    let then_sort = then_.sort();
                    let else_sort = else_.sort();
                    if then_sort == else_sort && matches!(then_sort, ChcSort::Int | ChcSort::Real) {
                        let v = state.fresh_var("_ite", then_sort);
                        let v_expr = Self::Var(v);

                        let eq_then = Self::eq(v_expr.clone(), then_);
                        let eq_else = Self::eq(v_expr.clone(), else_);

                        state.constraints.push(Self::implies(cond.clone(), eq_then));
                        state
                            .constraints
                            .push(Self::implies(Self::not(cond), eq_else));

                        return Some(v_expr);
                    }

                    // Skip rebuild when children are unchanged (#3665)
                    if args[0].as_ref() == &cond
                        && args[1].as_ref() == &then_
                        && args[2].as_ref() == &else_
                    {
                        self.clone()
                    } else {
                        Self::ite(cond, then_, else_)
                    }
                }

                _ => self.map_children_with(|child| {
                    child
                        .eliminate_ite_recursive(state)
                        .unwrap_or_else(|| child.clone())
                }),
            })
        })
    }

    /// Recursive helper for mod elimination.
    /// Returns `None` if the node budget is exhausted (#2774).
    fn eliminate_mod_recursive(&self, state: &mut EliminationState) -> Option<Self> {
        maybe_grow_expr_stack(|| {
            ExprDepthGuard::check()?;
            if !state.tick() {
                return None;
            }
            Some(match self {
                Self::Op(ChcOp::Mod, args)
                    if args.len() == 2 && Self::is_int_euclidean_dividend(args[0].as_ref()) =>
                {
                    match args[1].as_ref() {
                        Self::Int(k) if *k != i128::MIN => {
                            if *k == 0 {
                                // SMT-LIB total semantics: (mod x 0) = x
                                return args[0].eliminate_mod_recursive(state);
                            }
                            let x = args[0]
                                .eliminate_mod_recursive(state)
                                .unwrap_or_else(|| args[0].as_ref().clone());
                            let (_, r) = Self::euclidean_decompose(
                                state,
                                x,
                                Self::Int(*k),
                                Self::Int(k.saturating_abs()),
                                "mod",
                            );
                            Self::Var(r)
                        }
                        divisor => {
                            // W1-1B: preserve a wide constant product-tree modulus
                            // `mod(x, 2^w)` for w>=63 (value > i64::MAX) so the BigInt
                            // executor folds and solves it exactly. Euclidean-decomposing
                            // such a modulus blows 2^64 into a div/mod UF whose coefficient
                            // overflows i64/Rational64 and stalls to Unknown; the preserved
                            // wide mod is a sound pure relaxation (it removes, never adds,
                            // constraints, so any UNSAT it yields stays UNSAT). Small
                            // (<= i64::MAX) constant moduli keep decomposing exactly as
                            // before, so width < 63 and all mod-elim / #7006 tests are
                            // untouched.
                            // i128-lockstep: the preserve boundary moves from i64::MAX
                            // to i128::MAX — decomposition coefficients up to i128 are
                            // now exactly representable (ChcExpr::Int is i128-wide and
                            // the Farkas lane is checked-i128), so folds/eliminations
                            // inside i128 are exact; only beyond-i128 stays preserved
                            // for the BigInt executor (same soundness argument).
                            if Self::positive_int_constant_expr_value(divisor)
                                .is_some_and(|v| v > i128::MAX as u128)
                            {
                                let x = args[0]
                                    .eliminate_mod_recursive(state)
                                    .unwrap_or_else(|| args[0].as_ref().clone());
                                Self::Op(ChcOp::Mod, vec![Arc::new(x), args[1].clone()])
                            } else if let Some(divisor) = Self::positive_int_constant_expr(divisor)
                            {
                                let x = args[0]
                                    .eliminate_mod_recursive(state)
                                    .unwrap_or_else(|| args[0].as_ref().clone());
                                let (_, r) = Self::euclidean_decompose(
                                    state,
                                    x,
                                    divisor.clone(),
                                    divisor,
                                    "mod",
                                );
                                Self::Var(r)
                            } else {
                                self.map_children_with(|child| {
                                    child
                                        .eliminate_mod_recursive(state)
                                        .unwrap_or_else(|| child.clone())
                                })
                            }
                        }
                    }
                }

                Self::Op(ChcOp::Div, args)
                    if args.len() == 2 && Self::is_int_euclidean_dividend(args[0].as_ref()) =>
                {
                    match args[1].as_ref() {
                        Self::Int(k) if *k != i128::MIN => {
                            if *k == 0 {
                                // SMT-LIB total semantics: (div x 0) = 0
                                return Some(Self::Int(0));
                            }
                            let x = args[0]
                                .eliminate_mod_recursive(state)
                                .unwrap_or_else(|| args[0].as_ref().clone());
                            let (q, _) = Self::euclidean_decompose(
                                state,
                                x,
                                Self::Int(*k),
                                Self::Int(k.saturating_abs()),
                                "div",
                            );
                            Self::Var(q)
                        }
                        divisor => {
                            // W1-1B: preserve a wide constant product-tree divisor
                            // `div(x, 2^w)` for w>=63 (value > i64::MAX) so the BigInt
                            // executor folds and solves it exactly (see the Mod arm above
                            // for the soundness argument — a preserved div is likewise a
                            // pure relaxation). Small constant divisors decompose exactly
                            // as before.
                            // i128-lockstep: the preserve boundary moves from i64::MAX
                            // to i128::MAX — decomposition coefficients up to i128 are
                            // now exactly representable (ChcExpr::Int is i128-wide and
                            // the Farkas lane is checked-i128), so folds/eliminations
                            // inside i128 are exact; only beyond-i128 stays preserved
                            // for the BigInt executor (same soundness argument).
                            if Self::positive_int_constant_expr_value(divisor)
                                .is_some_and(|v| v > i128::MAX as u128)
                            {
                                let x = args[0]
                                    .eliminate_mod_recursive(state)
                                    .unwrap_or_else(|| args[0].as_ref().clone());
                                Self::Op(ChcOp::Div, vec![Arc::new(x), args[1].clone()])
                            } else if let Some(divisor) = Self::positive_int_constant_expr(divisor)
                            {
                                let x = args[0]
                                    .eliminate_mod_recursive(state)
                                    .unwrap_or_else(|| args[0].as_ref().clone());
                                let (q, _) = Self::euclidean_decompose(
                                    state,
                                    x,
                                    divisor.clone(),
                                    divisor,
                                    "div",
                                );
                                Self::Var(q)
                            } else {
                                self.map_children_with(|child| {
                                    child
                                        .eliminate_mod_recursive(state)
                                        .unwrap_or_else(|| child.clone())
                                })
                            }
                        }
                    }
                }

                _ => self.map_children_with(|child| {
                    child
                        .eliminate_mod_recursive(state)
                        .unwrap_or_else(|| child.clone())
                }),
            })
        })
    }

    /// Rewrite mixed-sort equalities `(= Int_expr Bool_expr)` into
    /// `(= Int_expr (ite Bool_expr 1 0))`.
    ///
    /// CHC benchmarks (e.g., id_o20) contain patterns like `(= D (= E 0))` where D has sort
    /// Int and `(= E 0)` has sort Bool. When sent to the LRA solver as a theory atom, the
    /// Bool sub-expression marks the atom as unsupported, causing Unknown results (#6167).
    ///
    /// This pass lifts the Bool-to-Int coercion to an ITE, which `eliminate_ite` then handles
    /// by introducing a fresh Int variable with definitional constraints. This is the same
    /// pattern used by FlatZinc `bool2int` (#5925).
    ///
    /// If the expression tree exceeds 1M nodes, returns `self` unchanged.
    pub(crate) fn eliminate_mixed_sort_eq(&self) -> Self {
        use std::cell::Cell;

        const MAX_NODES: usize = MAX_PREPROCESSING_NODES;
        let budget = Cell::new(MAX_NODES);

        fn rewrite_inner(expr: &ChcExpr, budget: &Cell<usize>, depth: usize) -> Option<ChcExpr> {
            maybe_grow_expr_stack(|| {
                if depth >= MAX_EXPR_RECURSION_DEPTH {
                    return None;
                }
                let remaining = budget.get();
                if remaining == 0 {
                    return None;
                }
                budget.set(remaining - 1);

                Some(match expr {
                    ChcExpr::Bool(_)
                    | ChcExpr::Int(_)
                    | ChcExpr::Real(_, _)
                    | ChcExpr::BitVec(_, _)
                    | ChcExpr::Var(_) => expr.clone(),

                    ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                        let a = rewrite_inner(&args[0], budget, depth + 1)
                            .unwrap_or_else(|| args[0].as_ref().clone());
                        let b = rewrite_inner(&args[1], budget, depth + 1)
                            .unwrap_or_else(|| args[1].as_ref().clone());

                        let sa = a.sort();
                        let sb = b.sort();

                        if sa == ChcSort::Bool && matches!(sb, ChcSort::Int | ChcSort::Real) {
                            // (= Bool_expr Int_expr) → (= (ite Bool_expr 1 0) Int_expr)
                            let coerced = if sb == ChcSort::Real {
                                ChcExpr::ite(a, ChcExpr::Real(1, 1), ChcExpr::Real(0, 1))
                            } else {
                                ChcExpr::ite(a, ChcExpr::Int(1), ChcExpr::Int(0))
                            };
                            ChcExpr::eq(coerced, b)
                        } else if sb == ChcSort::Bool && matches!(sa, ChcSort::Int | ChcSort::Real)
                        {
                            // (= Int_expr Bool_expr) → (= Int_expr (ite Bool_expr 1 0))
                            let coerced = if sa == ChcSort::Real {
                                ChcExpr::ite(b, ChcExpr::Real(1, 1), ChcExpr::Real(0, 1))
                            } else {
                                ChcExpr::ite(b, ChcExpr::Int(1), ChcExpr::Int(0))
                            };
                            ChcExpr::eq(a, coerced)
                        } else {
                            // Skip rebuild when children are unchanged (#3665)
                            if args[0].as_ref() == &a && args[1].as_ref() == &b {
                                expr.clone()
                            } else {
                                ChcExpr::eq(a, b)
                            }
                        }
                    }

                    _ => expr.map_children_with(|child| {
                        rewrite_inner(child, budget, depth + 1).unwrap_or_else(|| child.clone())
                    }),
                })
            })
        }

        rewrite_inner(self, &budget, 0).unwrap_or_else(|| self.clone())
    }

    /// Simplify array operations using McCarthy's read-over-write axioms.
    ///
    /// Applies these rewrite rules bottom-up:
    ///
    /// 1. **ROW1 (same index):** `select(store(a, i, v), j)` → `v` when `i == j`
    ///    syntactically.
    /// 2. **ROW2 (different index):** `select(store(a, i, v), j)` → `select(a, j)`
    ///    when `i ≠ j` is provable from distinct constants.
    /// 3. **Const-array select:** `select(ConstArray(val), _)` → `val`.
    ///
    /// ROW1 recurses on nested stores: `select(store(store(a, 0, x), 1, y), 0)`
    /// first applies ROW2 (outer: idx=1, sel=0, different) yielding
    /// `select(store(a, 0, x), 0)`, then ROW1 (same index) yielding `x`.
    ///
    /// This eliminates select-store chains that would otherwise require the SMT
    /// solver's eager array axiom generation, which creates massive term expansion
    /// for BV-indexed arrays (#6047).
    ///
    /// If the expression tree exceeds 1M nodes, returns `self` unchanged.
    pub(crate) fn simplify_array_ops(&self) -> Self {
        use std::cell::Cell;

        const MAX_NODES: usize = MAX_PREPROCESSING_NODES;
        let budget = Cell::new(MAX_NODES);
        let mut memo: ArrayOpsMemo = ArrayOpsMemo::default();

        /// Simplify a child `Arc` subtree, memoizing on pointer identity so
        /// each shared `Arc` subtree is rewritten at most once per top-level
        /// call — the exact pattern of `simplify_constants::simplify_arg`.
        ///
        /// SOUNDNESS: within one top-level `simplify_array_ops` call every
        /// input subtree stays alive (reachable from the borrowed `self`), so
        /// `Arc::as_ptr` is a stable, unique key for that subtree. A cached
        /// result is, by construction, a valid (semantically equal) rewrite of
        /// that subtree. The budget/depth-exhaustion `None` case is never
        /// cached, so an earlier/shallower path that reaches the same subtree
        /// with budget to spare can still simplify it.
        fn simplify_arg(
            a: &Arc<ChcExpr>,
            budget: &Cell<usize>,
            depth: usize,
            memo: &mut ArrayOpsMemo,
        ) -> Arc<ChcExpr> {
            let key = Arc::as_ptr(a);
            if let Some(cached) = memo.get(&key) {
                return Arc::clone(cached);
            }
            match simplify_inner(a.as_ref(), budget, depth, memo) {
                Some(simplified) => {
                    let result = Arc::new(simplified);
                    memo.insert(key, Arc::clone(&result));
                    result
                }
                // Budget/depth exhausted: keep the original subtree (sound,
                // and preserves sharing) without caching.
                None => Arc::clone(a),
            }
        }

        fn simplify_inner(
            expr: &ChcExpr,
            budget: &Cell<usize>,
            depth: usize,
            memo: &mut ArrayOpsMemo,
        ) -> Option<ChcExpr> {
            maybe_grow_expr_stack(|| {
                if depth >= MAX_EXPR_RECURSION_DEPTH {
                    return None;
                }
                let remaining = budget.get();
                if remaining == 0 {
                    return None;
                }
                budget.set(remaining - 1);

                Some(match expr {
                    ChcExpr::Bool(_)
                    | ChcExpr::Int(_)
                    | ChcExpr::Real(_, _)
                    | ChcExpr::BitVec(_, _)
                    | ChcExpr::Var(_) => expr.clone(),

                    // select(arr, idx) — try to reduce after simplifying children.
                    ChcExpr::Op(ChcOp::Select, args) if args.len() == 2 => {
                        let arr = simplify_arg(&args[0], budget, depth + 1, memo);
                        let idx = simplify_arg(&args[1], budget, depth + 1, memo);
                        reduce_select(expr, arr.as_ref(), idx.as_ref(), args)
                    }

                    // Explicit arms (rather than the `map_children_with`
                    // fallback) so child `Arc`s go through the pointer-identity
                    // memo — mirrors `simplify_constants` (#7060).
                    ChcExpr::Op(op, args) => {
                        let simplified_args: Vec<Arc<ChcExpr>> = args
                            .iter()
                            .map(|arg| simplify_arg(arg, budget, depth + 1, memo))
                            .collect();
                        // Skip rebuild when children are unchanged (#3665).
                        let args_changed = !args
                            .iter()
                            .zip(simplified_args.iter())
                            .all(|(old, new)| old.as_ref() == new.as_ref());
                        if args_changed {
                            ChcExpr::Op(*op, simplified_args)
                        } else {
                            expr.clone()
                        }
                    }
                    ChcExpr::FuncApp(name, sort, args) => {
                        let simplified_args: Vec<Arc<ChcExpr>> = args
                            .iter()
                            .map(|arg| simplify_arg(arg, budget, depth + 1, memo))
                            .collect();
                        let args_changed = !args
                            .iter()
                            .zip(simplified_args.iter())
                            .all(|(old, new)| old.as_ref() == new.as_ref());
                        if args_changed {
                            ChcExpr::FuncApp(name.clone(), sort.clone(), simplified_args)
                        } else {
                            expr.clone()
                        }
                    }
                    ChcExpr::PredicateApp(name, id, args) => {
                        let simplified_args: Vec<Arc<ChcExpr>> = args
                            .iter()
                            .map(|arg| simplify_arg(arg, budget, depth + 1, memo))
                            .collect();
                        let args_changed = !args
                            .iter()
                            .zip(simplified_args.iter())
                            .all(|(old, new)| old.as_ref() == new.as_ref());
                        if args_changed {
                            ChcExpr::PredicateApp(name.clone(), *id, simplified_args)
                        } else {
                            expr.clone()
                        }
                    }
                    ChcExpr::ConstArray(key_sort, val) => {
                        let new_val = simplify_arg(val, budget, depth + 1, memo);
                        if val.as_ref() == new_val.as_ref() {
                            expr.clone()
                        } else {
                            ChcExpr::ConstArray(key_sort.clone(), new_val)
                        }
                    }

                    // Leaf markers with no array-relevant children.
                    _ => expr.clone(),
                })
            })
        }

        /// Reduce `select(arr, idx)` using ROW axioms.
        ///
        /// Recurses on nested stores: checks the outermost store first,
        /// then peels it off (ROW2) or returns the stored value (ROW1).
        /// Accepts the original expression and args to skip rebuild when
        /// children are unchanged (#3665).
        fn reduce_select(
            orig_expr: &ChcExpr,
            arr: &ChcExpr,
            idx: &ChcExpr,
            orig_args: &[Arc<ChcExpr>],
        ) -> ChcExpr {
            maybe_grow_expr_stack(|| match arr {
                // select(store(base, store_idx, val), idx)
                ChcExpr::Op(ChcOp::Store, args) if args.len() == 3 => {
                    let base = &args[0];
                    let store_idx = &args[1];
                    let val = &args[2];

                    if store_idx.as_ref() == idx {
                        // ROW1: same index → return stored value.
                        val.as_ref().clone()
                    } else if are_distinct_constants(store_idx, idx) {
                        // ROW2: provably different indices → look through store.
                        // This always produces a genuinely different expression.
                        reduce_select(orig_expr, base, idx, orig_args)
                    } else {
                        // Indices are symbolic and not provably equal/different.
                        // Skip rebuild when children are unchanged (#3665).
                        if orig_args[0].as_ref() == arr && orig_args[1].as_ref() == idx {
                            orig_expr.clone()
                        } else {
                            ChcExpr::select(arr.clone(), idx.clone())
                        }
                    }
                }
                // select(ConstArray(val), _) → val
                ChcExpr::ConstArray(_, val) => val.as_ref().clone(),
                // No reduction possible.
                _ => {
                    // Skip rebuild when children are unchanged (#3665)
                    if orig_args[0].as_ref() == arr && orig_args[1].as_ref() == idx {
                        orig_expr.clone()
                    } else {
                        ChcExpr::select(arr.clone(), idx.clone())
                    }
                }
            })
        }

        /// Check if two constant expressions are provably distinct.
        ///
        /// Returns true when both are ground values of the same sort with
        /// different values: Int literals, BitVec literals, or Bool literals.
        fn are_distinct_constants(a: &Arc<ChcExpr>, b: &ChcExpr) -> bool {
            match (a.as_ref(), b) {
                (ChcExpr::Int(x), ChcExpr::Int(y)) => x != y,
                (ChcExpr::BitVec(x, xw), ChcExpr::BitVec(y, yw)) => xw == yw && x != y,
                (ChcExpr::Bool(x), ChcExpr::Bool(y)) => x != y,
                _ => false,
            }
        }

        simplify_inner(self, &budget, 0, &mut memo).unwrap_or_else(|| self.clone())
    }

    /// Eagerly unfold `select(store(...))` into ITE chains using the McCarthy
    /// read-over-write axiom, even when indices are symbolic.
    ///
    /// Unlike `simplify_array_ops`, which only fires ROW on syntactically-equal
    /// or provably-distinct constant indices, this routine also expands the
    /// symbolic case:
    ///
    ///   `select(store(a, i, v), j)` → `ite((= i j), v, select(a, j))`
    ///
    /// and recursively unfolds the resulting `select(a, j)` if `a` is itself a
    /// store. Matches Z3's `array_rewriter::expand_select_store` (see
    /// `reference/z3/src/ast/rewriter/array_rewriter.cpp:354-381`) and ay's
    /// term-level equivalent at `crates/ay-core/src/term/expand_select_store.rs`.
    ///
    /// This is used to eagerly discharge array theory reasoning in
    /// self-inductiveness SMT queries (#8660 Phase 2), where the ay-dpll array
    /// theory cannot close queries of the form
    ///
    ///   `frame ∧ lemma(body) ∧ transition ∧ ¬lemma(head)`
    ///
    /// when `transition` produces `head = store(body, i, v)` and `lemma`
    /// references `select(head, k)` with a concrete `k` and symbolic `i`. The
    /// ITE expansion reduces the query to pure LIA+UF (modulo the branch
    /// guards), letting the PDR ITE case-splitter discharge each branch.
    ///
    /// ## Budget
    ///
    /// Each symbolic expansion consumes from `symbolic_budget` (default 8).
    /// Concrete ROW1/ROW2 reductions are free. When the budget is exhausted,
    /// remaining selects stay as-is (sound: no precision loss beyond what the
    /// array theory would produce on its own).
    pub(crate) fn expand_select_store_symbolic(&self) -> Self {
        use std::cell::Cell;

        const MAX_NODES: usize = MAX_PREPROCESSING_NODES;
        /// Number of symbolic `select(store(...))` expansions allowed per call.
        /// Each expansion produces an ITE with a fresh `select(a, j)` else-branch
        /// that may itself be a `select(store(...))`. Bounded to avoid O(2^N)
        /// ITE blowup on deep store chains; the ITE case-splitter caps at depth
        /// 3 anyway so larger budgets buy no additional discharge power.
        const SYMBOLIC_BUDGET: usize = 8;

        let node_budget = Cell::new(MAX_NODES);
        let symbolic_budget = Cell::new(SYMBOLIC_BUDGET);

        fn rewrite(
            expr: &ChcExpr,
            node_budget: &Cell<usize>,
            symbolic_budget: &Cell<usize>,
            depth: usize,
        ) -> Option<ChcExpr> {
            maybe_grow_expr_stack(|| {
                if depth >= MAX_EXPR_RECURSION_DEPTH {
                    return None;
                }
                let remaining = node_budget.get();
                if remaining == 0 {
                    return None;
                }
                node_budget.set(remaining - 1);

                Some(match expr {
                    ChcExpr::Bool(_)
                    | ChcExpr::Int(_)
                    | ChcExpr::Real(_, _)
                    | ChcExpr::BitVec(_, _)
                    | ChcExpr::Var(_) => expr.clone(),

                    ChcExpr::Op(ChcOp::Select, args) if args.len() == 2 => {
                        let arr = rewrite(&args[0], node_budget, symbolic_budget, depth + 1)
                            .unwrap_or_else(|| args[0].as_ref().clone());
                        let idx = rewrite(&args[1], node_budget, symbolic_budget, depth + 1)
                            .unwrap_or_else(|| args[1].as_ref().clone());
                        expand_select(&arr, &idx, node_budget, symbolic_budget, depth)
                    }

                    _ => expr.map_children_with(|child| {
                        rewrite(child, node_budget, symbolic_budget, depth + 1)
                            .unwrap_or_else(|| child.clone())
                    }),
                })
            })
        }

        /// Unfold `select(arr, idx)` using ROW.
        ///
        /// - ROW1: `select(store(a, i, v), i)` → `v` (syntactic equality)
        /// - ROW2: `select(store(a, i, v), j)` → `select(a, j)` when `i ≠ j`
        ///   is provable from distinct constants
        /// - Symbolic: `select(store(a, i, v), j)` →
        ///   `ite((= i j), v, select(a, j))` (consumes one unit of budget)
        ///
        /// The else-branch `select(a, j)` is recursively unfolded if `a` is
        /// itself a store.
        fn expand_select(
            arr: &ChcExpr,
            idx: &ChcExpr,
            node_budget: &Cell<usize>,
            symbolic_budget: &Cell<usize>,
            depth: usize,
        ) -> ChcExpr {
            maybe_grow_expr_stack(|| {
                if depth >= MAX_EXPR_RECURSION_DEPTH {
                    return ChcExpr::select(arr.clone(), idx.clone());
                }
                match arr {
                    ChcExpr::Op(ChcOp::Store, args) if args.len() == 3 => {
                        let base = args[0].as_ref();
                        let store_idx = args[1].as_ref();
                        let val = args[2].as_ref();

                        if store_idx == idx {
                            // ROW1: same index → stored value.
                            return val.clone();
                        }
                        if are_distinct_constants_val(store_idx, idx) {
                            // ROW2: provably different → look through store,
                            // recursing in case `base` is also a store.
                            return expand_select(
                                base,
                                idx,
                                node_budget,
                                symbolic_budget,
                                depth + 1,
                            );
                        }

                        // Symbolic case: emit ITE if budget permits.
                        let budget = symbolic_budget.get();
                        if budget == 0 {
                            return ChcExpr::select(arr.clone(), idx.clone());
                        }
                        symbolic_budget.set(budget - 1);

                        let else_branch =
                            expand_select(base, idx, node_budget, symbolic_budget, depth + 1);
                        ChcExpr::ite(
                            ChcExpr::eq(store_idx.clone(), idx.clone()),
                            val.clone(),
                            else_branch,
                        )
                    }
                    ChcExpr::ConstArray(_, val) => val.as_ref().clone(),
                    _ => ChcExpr::select(arr.clone(), idx.clone()),
                }
            })
        }

        fn are_distinct_constants_val(a: &ChcExpr, b: &ChcExpr) -> bool {
            match (a, b) {
                (ChcExpr::Int(x), ChcExpr::Int(y)) => x != y,
                (ChcExpr::BitVec(x, xw), ChcExpr::BitVec(y, yw)) => xw == yw && x != y,
                (ChcExpr::Bool(x), ChcExpr::Bool(y)) => x != y,
                _ => false,
            }
        }

        rewrite(self, &node_budget, &symbolic_budget, 0).unwrap_or_else(|| self.clone())
    }
}
