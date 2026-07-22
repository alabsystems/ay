// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Ground-table read concretization (model-checker-consumer parity item 4, Stage 1).
//!
//! Read-only lookup-table CHC encodings (e.g. model-checker-consumer's `obj_size :
//! Array(BV32->BV32)` metadata table: 146 selects, 0 stores, every read a
//! positive ground pin `(= (select obj_size #xNN) #xVV)`) thread the table
//! array through every relation hop even though its entire observable content
//! is a finite, conflict-free pin map. The array argument then blocks every
//! array-free proof lane (#9227 empty-model rejection, scalar acyclic
//! exhaustion, BV-native collapse).
//!
//! This pass performs a GLOBAL analysis proving the problem only ever reads
//! such tables at ground constant indices with ground constant results, at
//! positive polarity, and then replaces every pin atom with `true`. The
//! table arrays become dead in every constraint; predicate signatures are
//! untouched, so the existing trailing [`super::DeadParamEliminator`] slices
//! the dead array argument positions.
//!
//! # Soundness (single-table instantiation argument)
//!
//! Let `M` be any total array agreeing with a lane's (conflict-free) pin map.
//!
//! - **Safe transfer** (transformed Safe => original Safe, same model): each
//!   pin atom is replaced by `true` at POSITIVE polarity only, so every
//!   original clause constraint implies its rewritten form; a predicate
//!   interpretation validating the rewritten clause validates the original.
//! - **Unsafe transfer** (transformed Unsafe => original Unsafe): closure
//!   guarantees a lane array occurs ONLY inside its pin atoms, so
//!   instantiating the lane variable with `M` in any transformed derivation
//!   makes every pin atom true and yields a syntactically valid original
//!   derivation. (Promotion still replays on the ORIGINAL clauses
//!   fail-closed; this argument is why the replay succeeds.)
//!
//! The NEGATIVE-POLARITY BAIL IS LOAD-BEARING: replacing a pin under
//! negation with `true` would *weaken* the original constraint, so a
//! transformed-Safe verdict would no longer transfer (see
//! `hazard_orig` fixture: `(not (= (select A 1) 5))` reachable under the
//! pinned `A[1]=5` would flip Safe to spurious Unsafe). `ite` conditions
//! carry both polarities and bail likewise.
//!
//! Any failed check bails the WHOLE pass to identity — the transform never
//! partially rewrites.
//!
//! Kill switch: `AY_CHC_DISABLE_GROUND_TABLE_CONCRETIZATION=1`.

use crate::expr::{maybe_grow_expr_stack, MAX_EXPR_RECURSION_DEPTH};
use crate::{ChcExpr, ChcOp, ChcProblem, ChcSort, ClauseHead, PredicateId};
use ay_core::kani_compat::DetHashMap as FxHashMap;

use super::{
    IdentityBackTranslator, MemoryBackTranslator, TransformMemoryReport, TransformObligation,
    TransformationResult, Transformer,
};

/// Kill switch: `AY_CHC_DISABLE_GROUND_TABLE_CONCRETIZATION=1` (or any value
/// other than `0`) disables the pass. Default: enabled.
pub(crate) fn ground_table_concretization_enabled() -> bool {
    std::env::var("AY_CHC_DISABLE_GROUND_TABLE_CONCRETIZATION")
        .map(|v| v == "0")
        .unwrap_or(true)
}

/// Ground-table read concretization (see module docs).
pub(crate) struct GroundTableReadConcretizer {
    verbose: bool,
}

impl Default for GroundTableReadConcretizer {
    fn default() -> Self {
        Self::new()
    }
}

impl GroundTableReadConcretizer {
    pub(crate) fn new() -> Self {
        Self { verbose: false }
    }

    pub(crate) fn with_verbose(mut self, verbose: bool) -> Self {
        self.verbose = verbose;
        self
    }

    /// Apply the pass. Returns `None` (identity) when nothing changed.
    ///
    /// Two phases, each independently equivalence-preserving:
    /// 1. Clause-local array ALIAS elimination: `(= v w)` over array vars
    ///    where `v` is clause-local is substituted (`v := w`, chain-resolved)
    ///    and the equality dropped — the same local existential projection
    ///    `LocalVarEliminator` performs, restricted to array-var aliases.
    ///    The ClauseInliner's composed clauses carry hundreds of freshened
    ///    `table__inline_N = table` bridges that otherwise keep every array
    ///    argument position LIVE for DeadParamEliminator and defeat the pin
    ///    analysis below.
    /// 2. Ground-pin concretization (global analysis; see module docs).
    pub(crate) fn apply(&self, problem: &ChcProblem) -> Option<ChcProblem> {
        let dealiased = eliminate_clause_local_array_aliases(problem);
        let (alias_count, base) = match &dealiased {
            Some((count, cleaned)) => (*count, cleaned),
            None => (0, problem),
        };
        let concretized = self.concretize_pins(base);
        if self.verbose && alias_count > 0 {
            safe_eprintln!(
                "CHC: ground-table concretization: {} array alias equalities unified",
                alias_count
            );
        }
        match concretized {
            Some(rewritten) => Some(rewritten),
            None => dealiased.map(|(_, cleaned)| cleaned),
        }
    }

    /// Phase 2: ground-pin concretization (see module docs). `None` when the
    /// global analysis bails or no pin exists.
    fn concretize_pins(&self, problem: &ChcProblem) -> Option<ChcProblem> {
        let analysis = analyze(problem)?;
        if analysis.pin_count == 0 {
            return None;
        }
        let mut new_problem = problem.clone();
        for clause in new_problem.clauses_mut() {
            if let Some(constraint) = clause.body.constraint.take() {
                let rewritten = replace_pin_atoms(&constraint, 0).simplify_constants();
                clause.body.constraint = match rewritten {
                    ChcExpr::Bool(true) => None,
                    other => Some(other),
                };
            }
        }
        if self.verbose {
            safe_eprintln!(
                "CHC: ground-table concretization: {} table lanes, {} pins replaced",
                analysis.lane_count,
                analysis.pin_count
            );
        }
        Some(new_problem)
    }
}

impl Transformer for GroundTableReadConcretizer {
    fn transform(self: Box<Self>, problem: ChcProblem) -> TransformationResult {
        if !ground_table_concretization_enabled() || !problem.has_array_sorts() {
            return TransformationResult {
                problem,
                back_translator: Box::new(IdentityBackTranslator),
            };
        }
        match self.apply(&problem) {
            Some(new_problem) => TransformationResult {
                problem: new_problem,
                back_translator: Box::new(
                    MemoryBackTranslator::new(
                        // Signatures untouched, witnesses pass through; Safe
                        // answers still validate and Unsafe witnesses still
                        // replay against the ORIGINAL clauses fail-closed
                        // (mirrors ArrayStoreForwarder). The pin rewrite itself
                        // is equisat by the single-table instantiation argument
                        // (module docs), which is why the obligation name is on
                        // the `is_equisat_grade` allowlist.
                        TransformMemoryReport::with_original_validation_obligations(
                            "ground_table_read_concretization",
                            [
                                TransformObligation::named("ground-table-read-concretization"),
                                TransformObligation::named("original-validation-on-safe"),
                                TransformObligation::named("original-replay-on-unsafe"),
                            ],
                        ),
                    )
                    .with_ground_input("ground-table-read-concretization", &problem),
                ),
            },
            None => TransformationResult {
                problem,
                back_translator: Box::new(IdentityBackTranslator),
            },
        }
    }
}

// ---------------------------------------------------------------------------
// Phase 1: top-level array alias unification (solved-form elimination)
// ---------------------------------------------------------------------------

/// Unify array variables equated by top-level body conjuncts.
///
/// For each clause, top-level conjuncts `(= v w)` with BOTH sides bare
/// array-sorted variables connect an alias class. Every non-representative
/// member is substituted by the class representative (lexicographically
/// smallest name, deterministic) THROUGHOUT the clause — constraint,
/// body predicate arguments, and head arguments — and equalities that
/// become `(= x x)` are dropped.
///
/// Soundness (solved-form variable elimination, exact): for the
/// universally quantified clause `∀ vars. (preds ∧ v = w ∧ R) ⇒ H`, the
/// body forces `v = w`, so the clause is equivalent to
/// `∀ vars \ {v}. (preds ∧ R)[v := w] ⇒ H[v := w]` — the same rewrite
/// `LocalVarEliminator` performs for clause-local variables, extended to
/// argument positions (which stay bare variables, so signatures and lane
/// discipline are preserved). The ClauseInliner's composed clauses carry
/// hundreds of freshened `table__inline_N = table` bridges — many used as
/// fresh argument variables — that otherwise keep every array argument
/// position LIVE for DeadParamEliminator and defeat the pin analysis.
///
/// Returns `None` when no clause changed; otherwise `(aliases, problem)`.
fn eliminate_clause_local_array_aliases(problem: &ChcProblem) -> Option<(usize, ChcProblem)> {
    let mut new_problem = problem.clone();
    let mut total_aliases = 0usize;
    for clause in new_problem.clauses_mut() {
        let Some(constraint) = clause.body.constraint.as_ref() else {
            continue;
        };
        let conjuncts = constraint.collect_conjuncts_nontrivial();
        if conjuncts.is_empty() {
            continue;
        }

        // Union alias classes over the top-level var-var array equalities.
        let mut uf = UnionFind::new();
        let mut nodes: FxHashMap<crate::ChcVar, usize> = FxHashMap::default();
        let mut any_alias_eq = false;
        for conj in &conjuncts {
            let Some((a, b)) = as_array_var_eq(conj) else {
                continue;
            };
            any_alias_eq = true;
            let na = *nodes.entry(a.clone()).or_insert_with(|| uf.make());
            let nb = *nodes.entry(b.clone()).or_insert_with(|| uf.make());
            uf.union(na, nb);
        }
        if !any_alias_eq {
            continue;
        }

        // Deterministic representative: the lexicographically-first member.
        let mut class_members: FxHashMap<usize, Vec<&crate::ChcVar>> = FxHashMap::default();
        for (var, &node) in &nodes {
            class_members.entry(uf.find(node)).or_default().push(var);
        }
        let mut subst_owned: Vec<(crate::ChcVar, ChcExpr)> = Vec::new();
        for members in class_members.values() {
            let rep = members
                .iter()
                .min_by(|a, b| a.name.cmp(&b.name))
                .expect("non-empty class");
            for member in members {
                if *member != *rep {
                    subst_owned.push(((*member).clone(), ChcExpr::var((*rep).clone())));
                }
            }
        }
        if subst_owned.is_empty() {
            continue;
        }
        let subst_refs: FxHashMap<&crate::ChcVar, &ChcExpr> =
            subst_owned.iter().map(|(var, expr)| (var, expr)).collect();

        // Substitute the WHOLE clause; drop equalities that TRIVIALIZED.
        let mut kept: Vec<ChcExpr> = Vec::with_capacity(conjuncts.len());
        let mut dropped = 0usize;
        for conj in &conjuncts {
            let rewritten = conj.substitute_map(&subst_refs);
            if let Some((a, b)) = as_array_var_eq(&rewritten) {
                if a == b {
                    dropped += 1;
                    continue;
                }
            }
            kept.push(rewritten);
        }
        if dropped == 0 {
            continue;
        }
        for (_, args) in &mut clause.body.predicates {
            for arg in args.iter_mut() {
                *arg = arg.substitute_map(&subst_refs);
            }
        }
        if let ClauseHead::Predicate(_, args) = &mut clause.head {
            for arg in args.iter_mut() {
                *arg = arg.substitute_map(&subst_refs);
            }
        }
        total_aliases += dropped;
        let new_constraint = ChcExpr::and_all(kept).simplify_constants();
        clause.body.constraint = Some(new_constraint).filter(|c| !matches!(c, ChcExpr::Bool(true)));
    }

    (total_aliases > 0).then_some((total_aliases, new_problem))
}

/// `(= v w)` with both sides bare array-sorted variables.
fn as_array_var_eq(expr: &ChcExpr) -> Option<(&crate::ChcVar, &crate::ChcVar)> {
    let ChcExpr::Op(ChcOp::Eq, args) = expr else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let (ChcExpr::Var(a), ChcExpr::Var(b)) = (args[0].as_ref(), args[1].as_ref()) else {
        return None;
    };
    (matches!(a.sort, ChcSort::Array(_, _)) && matches!(b.sort, ChcSort::Array(_, _)))
        .then_some((a, b))
}

// ---------------------------------------------------------------------------
// Global analysis
// ---------------------------------------------------------------------------

/// Formula polarity for the pin walk.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Polarity {
    Positive,
    Negative,
    Both,
}

impl Polarity {
    fn flip(self) -> Self {
        match self {
            Polarity::Positive => Polarity::Negative,
            Polarity::Negative => Polarity::Positive,
            Polarity::Both => Polarity::Both,
        }
    }
}

/// Union-find node key: a predicate argument position or a clause-scoped
/// array variable. Variables are scoped per clause (CHC variables are
/// clause-local), so unconnected same-named vars in different clauses form
/// independent lanes.
#[derive(Clone, PartialEq, Eq, Hash)]
enum LaneKey {
    Position(PredicateId, usize),
    Var(usize, String),
}

/// Minimal union-find over dense indices.
struct UnionFind {
    parent: Vec<usize>,
}

impl UnionFind {
    fn new() -> Self {
        Self { parent: Vec::new() }
    }

    fn make(&mut self) -> usize {
        let id = self.parent.len();
        self.parent.push(id);
        id
    }

    fn find(&mut self, mut x: usize) -> usize {
        while self.parent[x] != x {
            self.parent[x] = self.parent[self.parent[x]];
            x = self.parent[x];
        }
        x
    }

    fn union(&mut self, a: usize, b: usize) {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra != rb {
            self.parent[ra] = rb;
        }
    }
}

struct Analysis {
    lane_count: usize,
    pin_count: usize,
}

struct Analyzer {
    uf: UnionFind,
    keys: FxHashMap<LaneKey, usize>,
    /// Recorded pins: (lane node, index constant, value constant).
    pins: Vec<(usize, ChcExpr, ChcExpr)>,
}

impl Analyzer {
    fn node(&mut self, key: LaneKey) -> usize {
        if let Some(&id) = self.keys.get(&key) {
            return id;
        }
        let id = self.uf.make();
        self.keys.insert(key, id);
        id
    }
}

/// Run the whole-problem analysis. `None` = bail (identity).
fn analyze(problem: &ChcProblem) -> Option<Analysis> {
    let mut analyzer = Analyzer {
        uf: UnionFind::new(),
        keys: FxHashMap::default(),
        pins: Vec::new(),
    };

    for (clause_idx, clause) in problem.clauses().iter().enumerate() {
        // (a) Predicate-app args: array positions must be BARE Vars (union
        // them with their positions); other positions must be array-free and
        // select-free.
        let mut apps: Vec<(PredicateId, &[ChcExpr])> = clause
            .body
            .predicates
            .iter()
            .map(|(pid, args)| (*pid, args.as_slice()))
            .collect();
        if let ClauseHead::Predicate(pid, args) = &clause.head {
            apps.push((*pid, args.as_slice()));
        }
        for (pid, args) in apps {
            for (arg_idx, arg) in args.iter().enumerate() {
                let position_is_array = matches!(arg, ChcExpr::Var(v) if matches!(v.sort, ChcSort::Array(_, _)))
                    || expr_sort_is_array(arg);
                if position_is_array {
                    let ChcExpr::Var(v) = arg else {
                        return None; // non-Var array argument
                    };
                    if !matches!(v.sort, ChcSort::Array(_, _)) {
                        return None;
                    }
                    let pos = analyzer.node(LaneKey::Position(pid, arg_idx));
                    let var = analyzer.node(LaneKey::Var(clause_idx, v.name.clone()));
                    analyzer.uf.union(pos, var);
                } else if !term_is_table_free(arg, 0) {
                    return None;
                }
            }
        }

        // (b)+(c) Constraint: polarity walk validating closure and pin shape.
        if let Some(constraint) = clause.body.constraint.as_ref() {
            if !analyzer.scan_formula(constraint, Polarity::Positive, clause_idx, 0) {
                return None;
            }
        }
    }

    // (d) Pin map per lane; conflicting values -> bail (equal duplicates OK).
    let mut pin_map: FxHashMap<(usize, ChcExpr), ChcExpr> = FxHashMap::default();
    let mut lanes: FxHashMap<usize, ()> = FxHashMap::default();
    let pins = std::mem::take(&mut analyzer.pins);
    for (node, index, value) in pins {
        let lane = analyzer.uf.find(node);
        lanes.insert(lane, ());
        match pin_map.get(&(lane, index.clone())) {
            Some(existing) if *existing != value => return None,
            Some(_) => {}
            None => {
                pin_map.insert((lane, index), value);
            }
        }
    }

    Some(Analysis {
        lane_count: lanes.len(),
        pin_count: pin_map.len(),
    })
}

impl Analyzer {
    /// Polarity walk over a formula position. Returns `false` to bail.
    fn scan_formula(
        &mut self,
        expr: &ChcExpr,
        polarity: Polarity,
        clause_idx: usize,
        depth: usize,
    ) -> bool {
        if depth >= MAX_EXPR_RECURSION_DEPTH {
            return false; // conservative bail
        }
        maybe_grow_expr_stack(|| match expr {
            ChcExpr::Op(ChcOp::And, args) | ChcExpr::Op(ChcOp::Or, args) => args
                .iter()
                .all(|a| self.scan_formula(a, polarity, clause_idx, depth + 1)),
            ChcExpr::Op(ChcOp::Not, args) => args
                .iter()
                .all(|a| self.scan_formula(a, polarity.flip(), clause_idx, depth + 1)),
            ChcExpr::Op(ChcOp::Implies, args) if !args.is_empty() => {
                let (last, hyps) = args.split_last().expect("non-empty");
                hyps.iter()
                    .all(|a| self.scan_formula(a, polarity.flip(), clause_idx, depth + 1))
                    && self.scan_formula(last, polarity, clause_idx, depth + 1)
            }
            ChcExpr::Op(ChcOp::Iff, args) => args
                .iter()
                .all(|a| self.scan_formula(a, Polarity::Both, clause_idx, depth + 1)),
            ChcExpr::Op(ChcOp::Ite, args) if args.len() == 3 => {
                // Bool-formula ite: condition occurs under both polarities.
                self.scan_formula(&args[0], Polarity::Both, clause_idx, depth + 1)
                    && self.scan_formula(&args[1], polarity, clause_idx, depth + 1)
                    && self.scan_formula(&args[2], polarity, clause_idx, depth + 1)
            }
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                match extract_pin(&args[0], &args[1]) {
                    Some((var_name, index, value)) => {
                        // (c) pin polarity: POSITIVE only. A pin-shaped atom
                        // at negative/both polarity bails the whole pass.
                        if polarity != Polarity::Positive {
                            return false;
                        }
                        let node = self.node(LaneKey::Var(clause_idx, var_name));
                        self.pins.push((node, index, value));
                        true
                    }
                    // Non-pin equality: both sides must be table-free
                    // (bails on array equality, non-ground selects, etc.).
                    None => args.iter().all(|a| term_is_table_free(a, depth + 1)),
                }
            }
            // Bool-sorted equality chains >2, Ne, comparisons, predicate/
            // function atoms, constants, variables: plain term positions —
            // no array-sorted subterm and no select may appear.
            _ => term_is_table_free(expr, depth),
        })
    }
}

/// Pin shape: `(= (select VAR CONST) CONST)` in either orientation, where
/// VAR is a bare array-sorted variable and both constants are ground scalar
/// literals. Returns `(var_name, index, value)`.
fn extract_pin(a: &ChcExpr, b: &ChcExpr) -> Option<(String, ChcExpr, ChcExpr)> {
    for (sel_side, val_side) in [(a, b), (b, a)] {
        if let ChcExpr::Op(ChcOp::Select, sel_args) = sel_side {
            if sel_args.len() != 2 {
                continue;
            }
            let ChcExpr::Var(v) = sel_args[0].as_ref() else {
                continue;
            };
            if !matches!(v.sort, ChcSort::Array(_, _)) {
                continue;
            }
            if !is_ground_scalar_constant(sel_args[1].as_ref())
                || !is_ground_scalar_constant(val_side)
            {
                continue;
            }
            return Some((
                v.name.clone(),
                sel_args[1].as_ref().clone(),
                val_side.clone(),
            ));
        }
    }
    None
}

fn is_ground_scalar_constant(expr: &ChcExpr) -> bool {
    matches!(
        expr,
        ChcExpr::Bool(_) | ChcExpr::Int(_) | ChcExpr::Real(_, _) | ChcExpr::BitVec(_, _)
    )
}

/// Whether an expression is array-sorted at its root (conservative: only the
/// shapes the analysis must reject; bare Vars are checked by sort).
fn expr_sort_is_array(expr: &ChcExpr) -> bool {
    match expr {
        ChcExpr::Var(v) => matches!(v.sort, ChcSort::Array(_, _)),
        ChcExpr::Op(ChcOp::Store, _) | ChcExpr::ConstArray(_, _) | ChcExpr::ConstArrayMarker(_) => {
            true
        }
        ChcExpr::FuncApp(_, sort, _) => matches!(sort, ChcSort::Array(_, _)),
        _ => false,
    }
}

/// Term-position closure check (rule (b)): NO array-sorted subterm and NO
/// select may appear — a select outside a validated pin position violates
/// rule (c), and any store/const-array/array-var occurrence violates the
/// read-only table discipline. Depth cap bails conservatively (`false`).
fn term_is_table_free(expr: &ChcExpr, depth: usize) -> bool {
    if depth >= MAX_EXPR_RECURSION_DEPTH {
        return false;
    }
    maybe_grow_expr_stack(|| match expr {
        ChcExpr::Bool(_) | ChcExpr::Int(_) | ChcExpr::Real(_, _) | ChcExpr::BitVec(_, _) => true,
        ChcExpr::Var(v) => !matches!(v.sort, ChcSort::Array(_, _)),
        ChcExpr::ConstArray(_, _) | ChcExpr::ConstArrayMarker(_) => false,
        ChcExpr::IsTesterMarker(_) => true,
        ChcExpr::Op(ChcOp::Select, _) | ChcExpr::Op(ChcOp::Store, _) => false,
        ChcExpr::FuncApp(_, sort, args) => {
            !matches!(sort, ChcSort::Array(_, _))
                && args.iter().all(|a| term_is_table_free(a, depth + 1))
        }
        ChcExpr::Op(_, args) | ChcExpr::PredicateApp(_, _, args) => {
            args.iter().all(|a| term_is_table_free(a, depth + 1))
        }
    })
}

// ---------------------------------------------------------------------------
// Rewrite
// ---------------------------------------------------------------------------

/// Replace every validated pin atom with `true`. The analysis already proved
/// every pin-shaped equality in the problem occurs at positive polarity (any
/// other occurrence bailed), so shape-matching here replaces exactly the
/// recorded pin set.
fn replace_pin_atoms(expr: &ChcExpr, depth: usize) -> ChcExpr {
    if depth >= MAX_EXPR_RECURSION_DEPTH {
        return expr.clone();
    }
    maybe_grow_expr_stack(|| match expr {
        ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
            if extract_pin(&args[0], &args[1]).is_some() {
                ChcExpr::Bool(true)
            } else {
                expr.clone()
            }
        }
        ChcExpr::Op(
            op @ (ChcOp::And | ChcOp::Or | ChcOp::Not | ChcOp::Implies | ChcOp::Ite),
            args,
        ) => ChcExpr::Op(
            op.clone(),
            args.iter()
                .map(|a| std::sync::Arc::new(replace_pin_atoms(a, depth + 1)))
                .collect(),
        ),
        _ => expr.clone(),
    })
}

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
#[path = "ground_table_read_concretization_tests.rs"]
mod tests;
