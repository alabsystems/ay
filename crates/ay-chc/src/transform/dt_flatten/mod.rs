// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Datatype flattening transformation for CHC problems (#8288).
//!
//! Converts DT-sorted predicate arguments into scalar parameters by flattening
//! constructor fields. This enables PDR and other engines that only handle
//! scalar (Bool/Int/Real/BV) state to reason about struct/enum-sorted predicates.
//!
//! # Single-constructor (struct-like) DTs
//!
//! A predicate `P(s: Pair{fst:Int, snd:Int})` becomes `P(s_fst: Int, s_snd: Int)`.
//! Constructor applications become their field values. Selectors become direct
//! references to the corresponding field variable. Testers become `true`.
//!
//! # Multi-constructor (enum-like) DTs — PER-VARIANT COLUMNS (item 4 Stage 4)
//!
//! A predicate `P(x: Option{None, Some(val:Int)})` becomes
//! `P(x_disc, x_v1_val)`: one discriminant column followed by the
//! concatenation of EVERY variant's recursively-flattened fields. Each column
//! is owned by exactly one variant; columns of inactive variants are
//! unconstrained free values, which models the SMT-LIB free-accessor
//! semantics of selectors applied to the wrong constructor exactly (a
//! selector read on a variable always reads that variable's own column, so
//! all reads of the same accessor on the same variable agree).
//!
//! The discriminant column is `(_ BitVec 8)` when the problem carries BV
//! sorts (keeps the flattened problem inside the BV-native lane) and `Int`
//! otherwise.
//!
//! Rewrites:
//! - constructor app `C_k(args)` -> `disc = k` plus variant `k`'s columns;
//!   inactive variants' columns are filled with default constants (they are
//!   only ever compared under false discriminant guards);
//! - tester `is-C_k(x)` -> `x_disc = k`;
//! - selector on the matching variant -> that variant's column;
//! - selector on a PROVABLY-mismatched constructor application -> a
//!   deterministic uninterpreted function of the flattened value
//!   (`dtflat!wva!<dt>!<sel>`), never a fresh-per-occurrence variable:
//!   accessor congruence must be preserved (all reads of the same accessor
//!   on the same value must agree);
//! - DT equality -> discriminant equality plus per-variant DISC-GUARDED
//!   field equalities (recursive schema; inactive columns are never
//!   compared);
//! - DT ITE -> column-wise ITE.
//!
//! # Nested DTs
//!
//! Nested DTs are flattened recursively. A DT field that is itself a DT is
//! expanded into its own scalar fields (including its own discriminant for
//! multi-constructor nested DTs) in the parent's expansion.
//!
//! # Soundness
//!
//! The encoding is exact for variables, testers, matching-variant selectors,
//! equality, and ITE. Two deliberate approximation points remain and are
//! tracked as [`ApproxEvents`]:
//! - wrong-variant accessor reads on constructor applications become
//!   unconstrained-but-congruent EUF values (over-approximation);
//! - constructor applications fill inactive-variant columns with default
//!   constants (observable only through ITE-mixed column reads).
//! Whenever any such event fires (or recursive-DT depth truncation is
//! possible), the back-translator reports the
//! [`DT_FLATTEN_APPROX_OBLIGATION`] obligation so downstream acceptance
//! paths that would otherwise trust TRANSFORMED evidence (e.g. the
//! CheckedQueryOnlyDischarge Safe promotion) fail closed. Safe models are
//! always validated against the ORIGINAL clauses; Unsafe witnesses always
//! replay against the ORIGINAL clauses
//! (`with_incomplete_unsafe_backtranslation`).

use std::cell::Cell;
use std::sync::Arc;

use ay_core::kani_compat::DetHashMap as FxHashMap;

use crate::{
    ChcDtConstructor, ChcDtSelector, ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, ClauseBody,
    ClauseHead, HornClause, InvariantModel, PredicateId, PredicateInterpretation,
};

use super::{
    BackTranslator, IdentityBackTranslator, InvalidityWitness, TransformMemoryReport,
    TransformObligation, TransformationResult, Transformer, ValidityWitness,
};

/// Obligation name reported when the flattening made ANY approximation
/// (wrong-variant EUF reads, default-filled inactive constructor columns, or
/// possible recursive-depth truncation). Acceptance paths that trust
/// transformed evidence for Safe must reject chains carrying this obligation.
pub(crate) const DT_FLATTEN_APPROX_OBLIGATION: &str = "datatype-flatten-approximation";

// ── Discriminant kind ──────────────────────────────────────────────────────

/// Sort used for multi-constructor discriminant columns.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DiscKind {
    /// Integer discriminants (problems without BV sorts).
    Int,
    /// `(_ BitVec 8)` discriminants (keeps BV problems in the BV-native lane).
    Bv8,
}

impl DiscKind {
    fn for_problem(problem: &ChcProblem) -> Self {
        if problem.has_bv_sorts() {
            Self::Bv8
        } else {
            Self::Int
        }
    }

    fn sort(self) -> ChcSort {
        match self {
            Self::Int => ChcSort::Int,
            Self::Bv8 => ChcSort::BitVec(8),
        }
    }

    fn constant(self, k: usize) -> ChcExpr {
        match self {
            Self::Int => ChcExpr::Int(k as i128),
            Self::Bv8 => ChcExpr::BitVec(k as u128, 8),
        }
    }

    fn capacity(self) -> usize {
        match self {
            Self::Int => usize::MAX,
            Self::Bv8 => 256,
        }
    }
}

/// Extract a literal discriminant value from an expression of the disc sort.
fn disc_literal(expr: &ChcExpr, disc: DiscKind) -> Option<usize> {
    match (disc, expr) {
        (DiscKind::Int, ChcExpr::Int(v)) if *v >= 0 => Some(*v as usize),
        (DiscKind::Bv8, ChcExpr::BitVec(v, 8)) => Some(*v as usize),
        _ => None,
    }
}

// ── Approximation tracking ─────────────────────────────────────────────────

/// Approximation events observed while flattening a problem.
#[derive(Debug, Clone, Copy, Default)]
struct ApproxEvents {
    /// Recursive-DT depth truncation is possible for some flattened sort.
    truncated_recursion: bool,
    /// Multi-ctor constructor applications flattened with default-filled
    /// inactive-variant columns.
    ctor_app_default_columns: usize,
    /// Wrong-variant accessor reads turned into congruent EUF applications.
    wrong_variant_reads: usize,
}

impl ApproxEvents {
    fn any(&self) -> bool {
        self.truncated_recursion
            || self.ctor_app_default_columns > 0
            || self.wrong_variant_reads > 0
    }
}

/// Per-clause rewrite context: the clause's DT variable expansion plus the
/// problem-wide discriminant kind and approximation event sink.
struct FlattenCx<'a> {
    vars: &'a VarExpansion,
    disc: DiscKind,
    events: &'a Cell<ApproxEvents>,
    /// Per-clause wrong-variant-accessor variables, deduplicated by
    /// (selector key, subject expression): every read of the same accessor
    /// on the same subject WITHIN a clause maps to the SAME free variable
    /// (accessor congruence inside the clause — never fresh-per-occurrence).
    /// Across clauses the values are independently quantified, which is an
    /// over-approximation covered by the wva approximation event. Plain
    /// variables (not EUF applications) keep the flattened problem inside
    /// the executor's native BV fragment.
    wva_vars: &'a std::cell::RefCell<FxHashMap<(String, ChcExpr), ChcVar>>,
    /// Clause ordinal, kept in the generated wva variable names so distinct
    /// clauses never alias through identically-named implicit clause vars.
    clause_idx: usize,
}

impl FlattenCx<'_> {
    fn record_ctor_app_defaults(&self) {
        let mut e = self.events.get();
        e.ctor_app_default_columns += 1;
        self.events.set(e);
    }

    fn record_wva(&self) {
        let mut e = self.events.get();
        e.wrong_variant_reads += 1;
        self.events.set(e);
    }

    /// Deduplicated per-clause free variable for a wrong-variant accessor
    /// read (`selector_key` on `subject`).
    fn wva_var(&self, selector_key: String, subject: &ChcExpr, sort: ChcSort) -> ChcExpr {
        let mut cache = self.wva_vars.borrow_mut();
        let next_idx = cache.len();
        let var = cache
            .entry((selector_key, subject.clone()))
            .or_insert_with(|| {
                ChcVar::new(format!("dtflat_wva_c{}_{next_idx}", self.clause_idx), sort)
            })
            .clone();
        ChcExpr::Var(var)
    }
}

// ── Flattening metadata ────────────────────────────────────────────────────

/// Information about how one DT predicate argument was flattened.
#[allow(clippy::rc_buffer)]
#[derive(Debug, Clone)]
struct DtArgFlatInfo {
    /// Original predicate argument index.
    original_arg: usize,
    /// Original predicate argument sort.
    original_sort: ChcSort,
    /// Original constructors.
    constructors: Arc<Vec<ChcDtConstructor>>,
    /// Whether this DT has a single constructor (struct-like).
    single_ctor: bool,
    /// Synthetic original variable used when rebuilding invariant formulas.
    original_var: ChcVar,
    /// Flattened component bindings, in transformed argument order.
    components: Vec<DtFlatComponentBinding>,
}

/// One scalar component emitted for a flattened datatype argument.
#[derive(Debug, Clone)]
struct DtFlatComponentBinding {
    flat_offset: usize,
    sort: ChcSort,
    replacement: ChcExpr,
    obligation: DtRefinementObligation,
}

/// Obligation retained for validation/refinement after datatype flattening.
///
/// These records make the scalar-to-DT relationship explicit enough for a
/// failed original validation to identify the selector/tester fact that was
/// approximated instead of accepting a stale flattened SAFE model.
#[derive(Debug, Clone, PartialEq, Eq)]
enum DtRefinementObligation {
    Unit,
    SelectorPath(Vec<String>),
    Discriminant,
    GuardedPayload {
        constructors: Vec<String>,
        field_offset: usize,
    },
}

/// Per-predicate mapping from original DT arg index to flattened info.
struct DtFlatMap {
    /// Per-predicate: original argument sorts before flattening.
    pred_original_sorts: FxHashMap<PredicateId, Vec<ChcSort>>,
    /// Per-predicate: for each original arg, whether it was a DT that got flattened.
    pred_arg_flattened: FxHashMap<PredicateId, Vec<bool>>,
    /// Per-predicate: for each original DT arg, the flattening/backtranslation plan.
    pred_arg_dt_info: FxHashMap<PredicateId, Vec<Option<DtArgFlatInfo>>>,
    /// Discriminant kind used for every multi-constructor DT in this problem.
    disc: DiscKind,
    /// Approximation events observed during flattening.
    events: ApproxEvents,
}

impl DtFlatMap {
    fn new(disc: DiscKind) -> Self {
        Self {
            pred_original_sorts: FxHashMap::default(),
            pred_arg_flattened: FxHashMap::default(),
            pred_arg_dt_info: FxHashMap::default(),
            disc,
            events: ApproxEvents::default(),
        }
    }
}

const RECURSIVE_DT_PREFIX_EXPERIMENT_DEPTH: usize = 2;
const RECURSIVE_DT_LEGACY_SAFE_DEPTH: usize = 3;

// ── Public transformer ─────────────────────────────────────────────────────

/// DT flattening transformer (#8288).
///
/// No-op for problems without DT-sorted predicate arguments.
pub(crate) struct DtFlattener {
    verbose: bool,
}

impl DtFlattener {
    pub(crate) fn new() -> Self {
        Self { verbose: false }
    }

    pub(crate) fn with_verbose(mut self, verbose: bool) -> Self {
        self.verbose = verbose;
        self
    }
}

impl Transformer for DtFlattener {
    fn transform(self: Box<Self>, problem: ChcProblem) -> TransformationResult {
        if !problem.has_datatype_sorts() {
            return TransformationResult {
                problem,
                back_translator: Box::new(IdentityBackTranslator),
            };
        }
        let disc = DiscKind::for_problem(&problem);
        if let Some(sort) = first_unsupported_flattened_sort(&problem, disc) {
            if self.verbose {
                tracing::debug!(
                    sort = ?sort,
                    "DtFlatten: unsupported datatype field layout; leaving problem unchanged"
                );
            }
            return TransformationResult {
                problem,
                back_translator: Box::new(IdentityBackTranslator),
            };
        }
        if datatype_defs_exceed_disc_capacity(&problem, disc) {
            return TransformationResult {
                problem,
                back_translator: Box::new(IdentityBackTranslator),
            };
        }

        let mut map = DtFlatMap::new(disc);
        let transformed = flatten_problem(&problem, &mut map, self.verbose);
        TransformationResult {
            problem: transformed,
            back_translator: Box::new(DtFlatBackTranslator {
                map,
                input_problem: crate::ground_derivation::ground_backtranslation_enabled()
                    .then(|| std::sync::Arc::new(problem)),
            }),
        }
    }
}

fn datatype_defs_exceed_disc_capacity(problem: &ChcProblem, disc: DiscKind) -> bool {
    problem
        .datatype_defs()
        .iter()
        .any(|(_, ctors)| ctors.len() > disc.capacity())
}

// ── Sort flattening ────────────────────────────────────────────────────────

/// Recursively flatten a DT sort into scalar sorts.
///
/// For a single-constructor DT, returns the constructor's field sorts
/// (recursively flattened). For a multi-constructor DT, returns
/// `[disc_sort, variant0_fields..., variant1_fields..., ...]`: the
/// discriminant column followed by every variant's recursively-flattened
/// fields (per-variant columns; no union slots).
fn flatten_sort(sort: &ChcSort, disc: DiscKind) -> Vec<ChcSort> {
    flatten_sort_with_depth(sort, recursive_dt_flatten_depth(), disc)
}

fn recursive_dt_flatten_depth() -> usize {
    // Default preserves the legacy shallow recursive encoding used by existing
    // adaptive routes. The scalar-prefix mode is experimental and opt-in until
    // ADT-LIA target evidence plus original-problem validation justifies
    // promotion.
    if ay_core::misc_cli_flags().chc_dt_recursive_prefix {
        RECURSIVE_DT_PREFIX_EXPERIMENT_DEPTH
    } else {
        RECURSIVE_DT_LEGACY_SAFE_DEPTH
    }
}

fn flatten_sort_with_depth(sort: &ChcSort, max_depth: usize, disc: DiscKind) -> Vec<ChcSort> {
    flatten_sort_with_stack(sort, &mut Vec::new(), max_depth, disc)
}

fn flatten_sort_with_stack(
    sort: &ChcSort,
    dt_stack: &mut Vec<String>,
    max_depth: usize,
    disc: DiscKind,
) -> Vec<ChcSort> {
    match sort {
        ChcSort::Datatype { name, constructors } => {
            if dt_stack.iter().filter(|seen| *seen == name).count() >= max_depth {
                return Vec::new();
            }
            dt_stack.push(name.clone());
            let result = if constructors.len() == 1 {
                flatten_single_ctor_sort(constructors, dt_stack, max_depth, disc)
            } else {
                flatten_multi_ctor_sort(constructors, dt_stack, max_depth, disc)
            };
            dt_stack.pop();
            result
        }
        ChcSort::Uninterpreted(name)
            if dt_stack.iter().filter(|seen| *seen == name).count() >= max_depth =>
        {
            Vec::new()
        }
        _ => vec![sort.clone()],
    }
}

#[allow(clippy::rc_buffer)]
fn flatten_single_ctor_sort(
    constructors: &Arc<Vec<ChcDtConstructor>>,
    dt_stack: &mut Vec<String>,
    max_depth: usize,
    disc: DiscKind,
) -> Vec<ChcSort> {
    let ctor = &constructors[0];
    let mut result = Vec::new();
    for sel in &ctor.selectors {
        result.extend(flatten_sort_with_stack(
            &sel.sort, dt_stack, max_depth, disc,
        ));
    }
    if result.is_empty() {
        result.push(ChcSort::Bool);
    }
    result
}

#[allow(clippy::rc_buffer)]
fn flatten_multi_ctor_sort(
    constructors: &Arc<Vec<ChcDtConstructor>>,
    dt_stack: &mut Vec<String>,
    max_depth: usize,
    disc: DiscKind,
) -> Vec<ChcSort> {
    let mut result = vec![disc.sort()];
    for ctor in constructors.iter() {
        for sel in &ctor.selectors {
            result.extend(flatten_sort_with_stack(
                &sel.sort, dt_stack, max_depth, disc,
            ));
        }
    }
    result
}

fn flatten_sort_under(parent_sort: &ChcSort, sort: &ChcSort, disc: DiscKind) -> Vec<ChcSort> {
    let mut dt_stack = datatype_stack_for_sort(parent_sort);
    flatten_sort_with_stack(sort, &mut dt_stack, recursive_dt_flatten_depth(), disc)
}

fn datatype_stack_for_sort(sort: &ChcSort) -> Vec<String> {
    match sort {
        ChcSort::Datatype { name, .. } => vec![name.clone()],
        _ => Vec::new(),
    }
}

fn first_unsupported_flattened_sort(problem: &ChcProblem, disc: DiscKind) -> Option<ChcSort> {
    problem
        .predicates()
        .iter()
        .flat_map(|pred| pred.arg_sorts.iter())
        .find(|sort| {
            matches!(sort, ChcSort::Datatype { .. }) && !dt_flatten_sort_supported(sort, disc)
        })
        .cloned()
}

fn dt_flatten_sort_supported(sort: &ChcSort, disc: DiscKind) -> bool {
    dt_flatten_sort_supported_with_stack(sort, &mut Vec::new(), recursive_dt_flatten_depth(), disc)
}

fn dt_flatten_sort_supported_with_stack(
    sort: &ChcSort,
    dt_stack: &mut Vec<String>,
    max_depth: usize,
    disc: DiscKind,
) -> bool {
    match sort {
        ChcSort::Datatype { name, constructors } => {
            if dt_stack.iter().filter(|seen| *seen == name).count() >= max_depth {
                return true;
            }
            dt_stack.push(name.clone());
            let supported = if constructors.len() == 1 {
                constructors[0].selectors.iter().all(|selector| {
                    dt_flatten_sort_supported_with_stack(&selector.sort, dt_stack, max_depth, disc)
                })
            } else {
                multi_ctor_layout_supported(constructors, dt_stack, max_depth, disc)
            };
            dt_stack.pop();
            supported
        }
        ChcSort::Array(_, _) => true,
        ChcSort::Bool
        | ChcSort::Int
        | ChcSort::Real
        | ChcSort::BitVec(_)
        | ChcSort::Uninterpreted(_) => true,
    }
}

/// Per-variant-columns support: every variant's every field must be
/// recursively supported, and the constructor count must fit the
/// discriminant sort. Non-defaultable column sorts (opaque recursive
/// backedges) keep the legacy `Int 0` filler in inactive constructor
/// columns; the disc-guarded equality schema never compares those columns.
#[allow(clippy::rc_buffer)]
fn multi_ctor_layout_supported(
    constructors: &Arc<Vec<ChcDtConstructor>>,
    dt_stack: &mut Vec<String>,
    max_depth: usize,
    disc: DiscKind,
) -> bool {
    if constructors.len() > disc.capacity() {
        return false;
    }
    constructors.iter().all(|ctor| {
        ctor.selectors.iter().all(|selector| {
            dt_flatten_sort_supported_with_stack(&selector.sort, dt_stack, max_depth, disc)
        })
    })
}

/// Whether flattening `sort` would hit the recursive-DT depth cap anywhere
/// (i.e. the flat encoding TRUNCATES the value and equality on the truncated
/// tail is not represented).
fn sort_flatten_hits_cap(sort: &ChcSort, dt_stack: &mut Vec<String>, max_depth: usize) -> bool {
    match sort {
        ChcSort::Datatype { name, constructors } => {
            if dt_stack.iter().filter(|seen| *seen == name).count() >= max_depth {
                return true;
            }
            dt_stack.push(name.clone());
            let hit = constructors.iter().any(|ctor| {
                ctor.selectors
                    .iter()
                    .any(|sel| sort_flatten_hits_cap(&sel.sort, dt_stack, max_depth))
            });
            dt_stack.pop();
            hit
        }
        ChcSort::Uninterpreted(name) => {
            dt_stack.iter().filter(|seen| *seen == name).count() >= max_depth
        }
        _ => false,
    }
}

/// Build the explicit flattening/backtranslation plan for a DT argument.
fn make_flat_info(original_arg: usize, sort: &ChcSort, disc: DiscKind) -> Option<DtArgFlatInfo> {
    match sort {
        ChcSort::Datatype { constructors, .. } => {
            let single_ctor = constructors.len() == 1;
            let original_var = ChcVar::new(format!("x{original_arg}"), sort.clone());
            let components =
                flat_component_bindings_for_sort(sort, &ChcExpr::var(original_var.clone()), disc)?;
            Some(DtArgFlatInfo {
                original_arg,
                original_sort: sort.clone(),
                constructors: constructors.clone(),
                single_ctor,
                original_var,
                components,
            })
        }
        _ => None,
    }
}

// ── Problem flattening ─────────────────────────────────────────────────────

fn flatten_problem(problem: &ChcProblem, map: &mut DtFlatMap, verbose: bool) -> ChcProblem {
    let disc = map.disc;
    let mut result = ChcProblem::new();

    // Copy datatype definitions to the new problem (needed by downstream).
    for (name, ctors) in problem.datatype_defs() {
        result.add_datatype_def(name.clone(), ctors.clone());
    }

    // Truncation pre-scan: if any flattened sort (predicate args or declared
    // datatype defs) hits the recursive depth cap, equality on the truncated
    // tail is unrepresented -> approximation-grade chain.
    let max_depth = recursive_dt_flatten_depth();
    let truncated = problem
        .predicates()
        .iter()
        .flat_map(|pred| pred.arg_sorts.iter())
        .any(|sort| sort_flatten_hits_cap(sort, &mut Vec::new(), max_depth))
        || problem.datatype_defs().iter().any(|(name, ctors)| {
            let constructors: Vec<ChcDtConstructor> = ctors
                .iter()
                .map(|(ctor_name, selectors)| ChcDtConstructor {
                    name: ctor_name.clone(),
                    selectors: selectors
                        .iter()
                        .map(|(sel_name, sel_sort)| ChcDtSelector {
                            name: sel_name.clone(),
                            sort: sel_sort.clone(),
                        })
                        .collect(),
                })
                .collect();
            let sort = ChcSort::Datatype {
                name: name.clone(),
                constructors: Arc::new(constructors),
            };
            sort_flatten_hits_cap(&sort, &mut Vec::new(), max_depth)
        });
    let events = Cell::new(ApproxEvents {
        truncated_recursion: truncated,
        ..ApproxEvents::default()
    });

    // Phase 1: Flatten predicate signatures.
    for pred in problem.predicates() {
        map.pred_original_sorts
            .insert(pred.id, pred.arg_sorts.clone());
        let mut new_sorts = Vec::new();
        let mut arg_flattened = Vec::new();
        let mut arg_dt_info = Vec::new();

        for (arg_idx, sort) in pred.arg_sorts.iter().enumerate() {
            if matches!(sort, ChcSort::Datatype { .. }) {
                let flat_sorts = flatten_sort(sort, disc);
                new_sorts.extend(flat_sorts);
                arg_flattened.push(true);
                arg_dt_info.push(make_flat_info(arg_idx, sort, disc));
            } else {
                new_sorts.push(sort.clone());
                arg_flattened.push(false);
                arg_dt_info.push(None);
            }
        }

        map.pred_arg_flattened.insert(pred.id, arg_flattened);
        map.pred_arg_dt_info.insert(pred.id, arg_dt_info);
        result.declare_predicate(&pred.name, new_sorts);
    }

    if verbose {
        for (i, pred) in result.predicates().iter().enumerate() {
            let orig = &problem.predicates()[i];
            if pred.arity() != orig.arity() {
                tracing::info!(
                    predicate = %pred.name,
                    orig_arity = orig.arity(),
                    new_arity = pred.arity(),
                    "DtFlatten: expanded predicate"
                );
            }
        }
    }

    // Phase 2: Transform each clause.
    for (clause_idx, clause) in problem.clauses().iter().enumerate() {
        let new_clause = flatten_clause(clause, problem, disc, &events, clause_idx);
        result.add_clause(new_clause);
    }

    map.events = events.get();
    result
}

// ── Variable expansion ─────────────────────────────────────────────────────

/// For a DT variable, generate the list of flattened field variable names
/// and sorts.
///
/// Single-constructor: `p: Pair{fst,snd}` -> `[("p_fst", Int), ("p_snd", Int)]`.
/// Multi-constructor (per-variant columns):
/// `x: Option{None, Some(val:Int)}` -> `[("x_disc", disc), ("x_v1_val", Int)]`.
fn expand_dt_var(var_name: &str, sort: &ChcSort, disc: DiscKind) -> Vec<(String, ChcSort)> {
    expand_dt_var_with_depth(var_name, sort, recursive_dt_flatten_depth(), disc)
}

fn expand_dt_var_with_depth(
    var_name: &str,
    sort: &ChcSort,
    max_depth: usize,
    disc: DiscKind,
) -> Vec<(String, ChcSort)> {
    expand_dt_var_with_stack(var_name, sort, &mut Vec::new(), max_depth, disc)
}

fn expand_dt_var_with_stack(
    var_name: &str,
    sort: &ChcSort,
    dt_stack: &mut Vec<String>,
    max_depth: usize,
    disc: DiscKind,
) -> Vec<(String, ChcSort)> {
    match sort {
        ChcSort::Datatype { name, constructors } => {
            if dt_stack.iter().filter(|seen| *seen == name).count() >= max_depth {
                return Vec::new();
            }
            dt_stack.push(name.clone());
            let result = if constructors.len() == 1 {
                let ctor = &constructors[0];
                let mut result = Vec::new();
                if ctor.selectors.is_empty() {
                    // Unit struct: single dummy Bool
                    result.push((format!("{var_name}_unit"), ChcSort::Bool));
                } else {
                    for sel in &ctor.selectors {
                        expand_selector_columns(
                            &format!("{var_name}_{}", sel.name),
                            &sel.sort,
                            dt_stack,
                            max_depth,
                            disc,
                            &mut result,
                        );
                    }
                }
                result
            } else {
                // Multi-constructor: discriminant + per-variant columns.
                let mut result = vec![(format!("{var_name}_disc"), disc.sort())];
                for (k, ctor) in constructors.iter().enumerate() {
                    for sel in &ctor.selectors {
                        expand_selector_columns(
                            &format!("{var_name}_v{k}_{}", sel.name),
                            &sel.sort,
                            dt_stack,
                            max_depth,
                            disc,
                            &mut result,
                        );
                    }
                }
                result
            };
            dt_stack.pop();
            result
        }
        ChcSort::Uninterpreted(name)
            if dt_stack.iter().filter(|seen| *seen == name).count() >= max_depth =>
        {
            Vec::new()
        }
        _ => vec![(var_name.to_string(), sort.clone())],
    }
}

fn expand_selector_columns(
    child_name: &str,
    sel_sort: &ChcSort,
    dt_stack: &mut Vec<String>,
    max_depth: usize,
    disc: DiscKind,
    out: &mut Vec<(String, ChcSort)>,
) {
    match sel_sort {
        ChcSort::Datatype { .. } => {
            out.extend(expand_dt_var_with_stack(
                child_name, sel_sort, dt_stack, max_depth, disc,
            ));
        }
        ChcSort::Uninterpreted(name)
            if dt_stack.iter().filter(|seen| *seen == name).count() >= max_depth => {}
        _ => out.push((child_name.to_string(), sel_sort.clone())),
    }
}

// ── Context for DT var tracking during clause rewriting ────────────────────

/// Maps a DT variable name to its flattened field variables.
type VarExpansion = FxHashMap<String, Vec<ChcVar>>;

/// Build a VarExpansion from a list of (original_arg_expr, original_sort) pairs,
/// considering only Var arguments that are DT-sorted.
fn build_var_expansion(args: &[ChcExpr], sorts: &[ChcSort], disc: DiscKind) -> VarExpansion {
    let mut expansion = VarExpansion::default();
    for (arg, sort) in args.iter().zip(sorts.iter()) {
        if let (ChcExpr::Var(v), ChcSort::Datatype { .. }) = (arg, sort) {
            if !expansion.contains_key(&v.name) {
                let field_vars: Vec<ChcVar> = expand_dt_var(&v.name, sort, disc)
                    .into_iter()
                    .map(|(name, s)| ChcVar::new(name, s))
                    .collect();
                expansion.insert(v.name.clone(), field_vars);
            }
        }
    }
    expansion
}

// ── Clause rewriting ───────────────────────────────────────────────────────

fn flatten_clause(
    clause: &HornClause,
    orig_problem: &ChcProblem,
    disc: DiscKind,
    events: &Cell<ApproxEvents>,
    clause_idx: usize,
) -> HornClause {
    // Collect all DT variables used in this clause (from predicate args).
    let mut var_expansion = VarExpansion::default();
    let mut domain_constraints = Vec::new();

    for (pid, args) in &clause.body.predicates {
        let orig_sorts = &orig_problem.predicates()[pid.index()].arg_sorts;
        let exp = build_var_expansion(args, orig_sorts, disc);
        for (k, v) in exp {
            var_expansion.entry(k).or_insert(v);
        }
    }
    if let ClauseHead::Predicate(pid, args) = &clause.head {
        let orig_sorts = &orig_problem.predicates()[pid.index()].arg_sorts;
        let exp = build_var_expansion(args, orig_sorts, disc);
        for (k, v) in exp {
            var_expansion.entry(k).or_insert(v);
        }
    }

    // Also scan the constraint for DT variables that appear only in selectors/testers.
    if let Some(constraint) = &clause.body.constraint {
        collect_dt_vars_from_expr(constraint, &mut var_expansion, disc);
    }

    let wva_vars = std::cell::RefCell::new(FxHashMap::default());
    let cx = FlattenCx {
        vars: &var_expansion,
        disc,
        events,
        wva_vars: &wva_vars,
        clause_idx,
    };

    // Transform body predicates: expand DT args.
    let body_preds: Vec<(PredicateId, Vec<ChcExpr>)> = clause
        .body
        .predicates
        .iter()
        .map(|(pid, args)| {
            let orig_sorts = &orig_problem.predicates()[pid.index()].arg_sorts;
            let expanded = expand_pred_args(args, orig_sorts, &cx);
            domain_constraints.extend(predicate_arg_domain_constraints(
                &expanded, orig_sorts, disc,
            ));
            (*pid, expanded)
        })
        .collect();

    // Transform body constraint.
    let rewritten_body_constraint = clause
        .body
        .constraint
        .as_ref()
        .map(|c| rewrite_expr(c, &cx));

    // Transform head.
    let head = match &clause.head {
        ClauseHead::Predicate(pid, args) => {
            let orig_sorts = &orig_problem.predicates()[pid.index()].arg_sorts;
            let expanded = expand_pred_args(args, orig_sorts, &cx);
            domain_constraints.extend(predicate_arg_domain_constraints(
                &expanded, orig_sorts, disc,
            ));
            ClauseHead::Predicate(*pid, expanded)
        }
        ClauseHead::False => ClauseHead::False,
    };

    let body_constraint = conjoin_domain_constraints(rewritten_body_constraint, domain_constraints);
    let body = ClauseBody::new(body_preds, body_constraint);
    HornClause::new(body, head)
}

/// Scan an expression for DT-sorted variables used in selectors/testers/equality
/// and add them to the var expansion if not already present.
fn collect_dt_vars_from_expr(expr: &ChcExpr, expansion: &mut VarExpansion, disc: DiscKind) {
    crate::expr::maybe_grow_expr_stack(|| match expr {
        ChcExpr::Var(v)
            if matches!(v.sort, ChcSort::Datatype { .. }) && !expansion.contains_key(&v.name) =>
        {
            let field_vars: Vec<ChcVar> = expand_dt_var(&v.name, &v.sort, disc)
                .into_iter()
                .map(|(name, s)| ChcVar::new(name, s))
                .collect();
            expansion.insert(v.name.clone(), field_vars);
        }
        ChcExpr::Op(_, args) => {
            for a in args {
                collect_dt_vars_from_expr(a, expansion, disc);
            }
        }
        ChcExpr::FuncApp(_, _, args) => {
            for a in args {
                collect_dt_vars_from_expr(a, expansion, disc);
            }
        }
        ChcExpr::PredicateApp(_, _, args) => {
            for a in args {
                collect_dt_vars_from_expr(a, expansion, disc);
            }
        }
        _ => {}
    });
}

/// Expand predicate arguments: DT args become their flattened field expressions.
fn expand_pred_args(
    args: &[ChcExpr],
    original_sorts: &[ChcSort],
    cx: &FlattenCx<'_>,
) -> Vec<ChcExpr> {
    let mut expanded = Vec::new();
    for (arg, sort) in args.iter().zip(original_sorts.iter()) {
        if matches!(sort, ChcSort::Datatype { .. }) {
            let flat = flatten_dt_expr(arg, sort, cx);
            expanded.extend(flat);
        } else {
            expanded.push(rewrite_expr(arg, cx));
        }
    }
    expanded
}

/// Exact constructor-domain constraints for flattened datatype predicate args.
///
/// A multi-constructor DT is encoded with a discriminant column. The source
/// value can only use real constructor indexes, and nested recursive
/// discriminants are real only when their parent constructor field is active.
/// These constraints keep the scalarized CHC in that image without
/// constraining inactive payload columns whose selector values are
/// underspecified by SMT-LIB datatypes.
fn predicate_arg_domain_constraints(
    expanded_args: &[ChcExpr],
    original_sorts: &[ChcSort],
    disc: DiscKind,
) -> Vec<ChcExpr> {
    let mut constraints = Vec::new();
    let mut flat_idx = 0;

    for sort in original_sorts {
        if matches!(sort, ChcSort::Datatype { .. }) {
            let flat_len = flatten_sort(sort, disc).len();
            if flat_idx + flat_len <= expanded_args.len() {
                collect_dt_domain_constraints(
                    sort,
                    &expanded_args[flat_idx..flat_idx + flat_len],
                    None,
                    &mut constraints,
                    disc,
                );
            }
            flat_idx += flat_len;
        } else {
            flat_idx += 1;
        }
    }

    constraints
}

fn collect_dt_domain_constraints(
    sort: &ChcSort,
    flat_exprs: &[ChcExpr],
    guard: Option<ChcExpr>,
    out: &mut Vec<ChcExpr>,
    disc: DiscKind,
) {
    let ChcSort::Datatype { constructors, .. } = sort else {
        return;
    };

    if constructors.len() == 1 {
        let ctor = &constructors[0];
        let mut field_idx = 0;
        for sel in &ctor.selectors {
            let flat_len = flatten_sort_under(sort, &sel.sort, disc).len();
            if flat_len == 0 {
                continue;
            }
            if matches!(sel.sort, ChcSort::Datatype { .. })
                && field_idx + flat_len <= flat_exprs.len()
            {
                collect_dt_domain_constraints(
                    &sel.sort,
                    &flat_exprs[field_idx..field_idx + flat_len],
                    guard.clone(),
                    out,
                    disc,
                );
            }
            field_idx += flat_len;
        }
        return;
    }

    let Some(disc_expr) = flat_exprs.first().cloned() else {
        return;
    };
    out.push(guard_constraint(
        discriminant_domain(disc_expr.clone(), constructors.len(), disc),
        &guard,
    ));

    let mut field_idx = 1;
    for (ctor_idx, ctor) in constructors.iter().enumerate() {
        let ctor_guard = ChcExpr::eq(disc_expr.clone(), disc.constant(ctor_idx));
        let nested_guard = match &guard {
            Some(parent) => ChcExpr::and(parent.clone(), ctor_guard),
            None => ctor_guard,
        };
        for sel in &ctor.selectors {
            let flat_len = flatten_sort_under(sort, &sel.sort, disc).len();
            if flat_len == 0 {
                continue;
            }
            if matches!(sel.sort, ChcSort::Datatype { .. })
                && field_idx + flat_len <= flat_exprs.len()
            {
                collect_dt_domain_constraints(
                    &sel.sort,
                    &flat_exprs[field_idx..field_idx + flat_len],
                    Some(nested_guard.clone()),
                    out,
                    disc,
                );
            }
            field_idx += flat_len;
        }
    }
}

fn discriminant_domain(disc_expr: ChcExpr, constructor_count: usize, disc: DiscKind) -> ChcExpr {
    debug_assert!(constructor_count > 1);
    match disc {
        DiscKind::Int => ChcExpr::and_all([
            ChcExpr::ge(disc_expr.clone(), ChcExpr::Int(0)),
            ChcExpr::le(
                disc_expr,
                ChcExpr::Int(constructor_count.saturating_sub(1) as i128),
            ),
        ]),
        DiscKind::Bv8 => ChcExpr::Op(
            ChcOp::BvULe,
            vec![
                Arc::new(disc_expr),
                Arc::new(ChcExpr::BitVec(
                    constructor_count.saturating_sub(1) as u128,
                    8,
                )),
            ],
        ),
    }
}

fn guard_constraint(constraint: ChcExpr, guard: &Option<ChcExpr>) -> ChcExpr {
    match guard {
        Some(guard) => ChcExpr::implies(guard.clone(), constraint),
        None => constraint,
    }
}

fn conjoin_domain_constraints(
    rewritten_body_constraint: Option<ChcExpr>,
    domain_constraints: Vec<ChcExpr>,
) -> Option<ChcExpr> {
    if domain_constraints.is_empty() {
        return rewritten_body_constraint;
    }

    let constraints = rewritten_body_constraint
        .into_iter()
        .chain(domain_constraints)
        .collect::<Vec<_>>();
    Some(ChcExpr::and_all(constraints))
}

// ── Selector column lookup ─────────────────────────────────────────────────

/// Locate a selector's flattened column block within its owning DT's layout.
///
/// Returns `(ctor_idx, absolute_column_start, flat_len)`. For
/// single-constructor DTs columns start at 0; for multi-constructor DTs
/// column 0 is the discriminant and each variant owns its own column block.
fn selector_column(
    parent_sort: &ChcSort,
    sel_name: &str,
    disc: DiscKind,
) -> Option<(usize, usize, usize)> {
    let ChcSort::Datatype { constructors, .. } = parent_sort else {
        return None;
    };
    let mut col = if constructors.len() > 1 { 1 } else { 0 };
    for (ctor_idx, ctor) in constructors.iter().enumerate() {
        for sel in &ctor.selectors {
            let len = flatten_sort_under(parent_sort, &sel.sort, disc).len();
            if sel.name == sel_name {
                return Some((ctor_idx, col, len));
            }
            col += len;
        }
    }
    None
}

/// One naming step for nested selector chains: the name-suffix piece for a
/// selector under `current_sort` plus the selector's sort.
fn selector_step(current_sort: &ChcSort, sel_name: &str) -> Option<(String, ChcSort)> {
    let ChcSort::Datatype { constructors, .. } = current_sort else {
        return None;
    };
    let multi = constructors.len() > 1;
    for (k, ctor) in constructors.iter().enumerate() {
        for sel in &ctor.selectors {
            if sel.name == sel_name {
                let piece = if multi {
                    format!("_v{k}_{}", sel.name)
                } else {
                    format!("_{}", sel.name)
                };
                return Some((piece, sel.sort.clone()));
            }
        }
    }
    None
}

// ── DT expression flattening ───────────────────────────────────────────────

/// Flatten a DT-sorted expression into its scalar components.
///
/// - Variable: expand to field variables
/// - Constructor application: disc constant + variant columns (inactive
///   variants default-filled)
/// - ITE: distribute across branches column-wise
/// - Other: fall back to selector extraction
fn flatten_dt_expr(expr: &ChcExpr, sort: &ChcSort, cx: &FlattenCx<'_>) -> Vec<ChcExpr> {
    let ChcSort::Datatype { constructors, .. } = sort else {
        return vec![rewrite_expr(expr, cx)];
    };

    match expr {
        ChcExpr::Var(v) => {
            if let Some(field_vars) = cx.vars.get(&v.name) {
                field_vars
                    .iter()
                    .map(|fv| ChcExpr::Var(fv.clone()))
                    .collect()
            } else {
                // Fallback: use selectors
                selector_extraction(expr, sort, cx)
            }
        }
        ChcExpr::FuncApp(name, ChcSort::Datatype { .. }, args) => {
            if let Some(components) = resolve_nested_dt_components(expr, sort, cx) {
                return components;
            }

            // This is a constructor application.
            // Find which constructor this is.
            if let Some((ctor_idx, ctor)) = constructors
                .iter()
                .enumerate()
                .find(|(_, c)| c.name == *name)
            {
                if constructors.len() == 1 {
                    // Single-ctor: just return the flattened field values
                    let mut result = Vec::new();
                    for (sel_i, sel) in ctor.selectors.iter().enumerate() {
                        if let Some(field_expr) = args.get(sel_i) {
                            if matches!(sel.sort, ChcSort::Datatype { .. }) {
                                result.extend(flatten_dt_expr(field_expr, &sel.sort, cx));
                            } else {
                                result.push(rewrite_expr(field_expr, cx));
                            }
                        }
                    }
                    if result.is_empty() {
                        result.push(ChcExpr::Bool(true)); // unit struct
                    }
                    result
                } else {
                    // Multi-ctor per-variant columns: disc constant + active
                    // variant's field values; inactive variants' columns are
                    // default-filled (only ever compared under false
                    // discriminant guards).
                    let mut result = vec![cx.disc.constant(ctor_idx)];
                    let mut pushed_defaults = false;
                    for (j, cj) in constructors.iter().enumerate() {
                        if j == ctor_idx {
                            for (sel_i, sel) in cj.selectors.iter().enumerate() {
                                let expected = flatten_sort_under(sort, &sel.sort, cx.disc).len();
                                if expected == 0 {
                                    continue;
                                }
                                let mut cols = Vec::with_capacity(expected);
                                if let Some(field_expr) = args.get(sel_i) {
                                    if matches!(sel.sort, ChcSort::Datatype { .. }) {
                                        let nested = flatten_dt_expr(field_expr, &sel.sort, cx);
                                        cols.extend(nested.into_iter().take(expected));
                                    } else {
                                        cols.push(rewrite_expr(field_expr, cx));
                                    }
                                }
                                // Pad (recursive-depth truncation mismatch or
                                // missing arg) with sort-correct defaults.
                                let flat_sorts = flatten_sort_under(sort, &sel.sort, cx.disc);
                                while cols.len() < expected {
                                    cols.push(
                                        flat_sorts
                                            .get(cols.len())
                                            .and_then(default_expr_for_sort)
                                            .unwrap_or(ChcExpr::Int(0)),
                                    );
                                }
                                result.extend(cols);
                            }
                        } else {
                            for sel in &cj.selectors {
                                for s in flatten_sort_under(sort, &sel.sort, cx.disc) {
                                    result
                                        .push(default_expr_for_sort(&s).unwrap_or(ChcExpr::Int(0)));
                                    pushed_defaults = true;
                                }
                            }
                        }
                    }
                    if pushed_defaults {
                        cx.record_ctor_app_defaults();
                    }
                    result
                }
            } else {
                // DT-returning SELECTOR application on an arbitrary DT
                // subject (constructor application, ITE of constructor
                // applications, ...): resolve through the subject's
                // flattened components — the selector's owning column block
                // distributes over ITE branches. A PROVABLY-mismatched read
                // (subject discriminant is a literal of another variant)
                // becomes deterministic congruent EUF applications per
                // column, never the default-filled block and never
                // fresh-per-occurrence variables.
                if let Some(components) =
                    resolve_selector_on_dt_subject_components(name, args, sort, cx)
                {
                    return components;
                }
                // Unknown constructor: fall back to selector extraction
                selector_extraction(expr, sort, cx)
            }
        }
        ChcExpr::Op(ChcOp::Ite, args) if args.len() == 3 => {
            // ITE over DT: distribute column-wise
            let cond = rewrite_expr(&args[0], cx);
            let then_flat = flatten_dt_expr(&args[1], sort, cx);
            let else_flat = flatten_dt_expr(&args[2], sort, cx);
            if then_flat.len() == else_flat.len() {
                then_flat
                    .into_iter()
                    .zip(else_flat)
                    .map(|(t, e)| {
                        if t == e {
                            t
                        } else {
                            ChcExpr::Op(
                                ChcOp::Ite,
                                vec![Arc::new(cond.clone()), Arc::new(t), Arc::new(e)],
                            )
                        }
                    })
                    .collect()
            } else {
                // Mismatched lengths: fall back
                selector_extraction(expr, sort, cx)
            }
        }
        _ => selector_extraction(expr, sort, cx),
    }
}

/// Resolve a DT-returning selector application over an arbitrary DT subject
/// into its flattened column-block components (see the call site in
/// [`flatten_dt_expr`] for the semantics).
fn resolve_selector_on_dt_subject_components(
    sel_name: &str,
    args: &[Arc<ChcExpr>],
    sel_ret_sort: &ChcSort,
    cx: &FlattenCx<'_>,
) -> Option<Vec<ChcExpr>> {
    if args.len() != 1 {
        return None;
    }
    let subject = args[0].as_ref();
    let subject_sort = subject.sort();
    let ChcSort::Datatype {
        name: dt_name,
        constructors,
    } = &subject_sort
    else {
        return None;
    };
    let (ctor_idx, abs_col, flat_len) = selector_column(&subject_sort, sel_name, cx.disc)?;
    if flat_len == 0 {
        return None;
    }
    let expected_subject = flatten_sort(&subject_sort, cx.disc).len();
    let subject_comps = flatten_dt_expr(subject, &subject_sort, cx);
    if subject_comps.len() != expected_subject || abs_col + flat_len > subject_comps.len() {
        return None;
    }
    let provably_mismatched = constructors.len() > 1
        && disc_literal(&subject_comps[0], cx.disc).is_some_and(|k| k != ctor_idx);
    if provably_mismatched {
        // Wrong-variant accessor: free value per column, deduplicated per
        // (selector, subject) within the clause (congruent inside the
        // clause, never fresh-per-occurrence).
        let col_sorts = flatten_sort_under(&subject_sort, sel_ret_sort, cx.disc);
        if col_sorts.len() != flat_len {
            return None;
        }
        cx.record_wva();
        return Some(
            col_sorts
                .into_iter()
                .enumerate()
                .map(|(i, col_sort)| {
                    cx.wva_var(format!("{dt_name}!{sel_name}!{i}"), subject, col_sort)
                })
                .collect(),
        );
    }
    Some(subject_comps[abs_col..abs_col + flat_len].to_vec())
}

fn resolve_nested_dt_components(
    expr: &ChcExpr,
    expected_sort: &ChcSort,
    cx: &FlattenCx<'_>,
) -> Option<Vec<ChcExpr>> {
    let mut chain: Vec<&str> = Vec::new();
    let mut cursor = expr;

    let base_var = loop {
        match cursor {
            ChcExpr::Var(v) => {
                cx.vars.get(&v.name)?;
                break v;
            }
            ChcExpr::FuncApp(name, ret_sort, args)
                if args.len() == 1 && matches!(ret_sort, ChcSort::Datatype { .. }) =>
            {
                chain.push(name.as_str());
                cursor = args[0].as_ref();
            }
            _ => return None,
        }
    };

    if chain.is_empty() {
        return None;
    }
    chain.reverse();

    let mut current_sort = base_var.sort.clone();
    let mut prefix = base_var.name.clone();
    for selector_name in &chain {
        let (piece, next_sort) = selector_step(&current_sort, selector_name)?;
        prefix.push_str(&piece);
        current_sort = next_sort;
    }

    if &current_sort != expected_sort {
        return None;
    }

    let field_vars = cx.vars.get(&base_var.name)?;
    let expected_components = expand_dt_var(&prefix, expected_sort, cx.disc);
    if expected_components.is_empty() {
        return None;
    }

    expected_components
        .into_iter()
        .map(|(name, sort)| {
            field_vars
                .iter()
                .find(|field_var| field_var.name == name && field_var.sort == sort)
                .cloned()
                .map(ChcExpr::Var)
        })
        .collect()
}

/// Fall back: extract scalar fields from a DT expression using selectors.
///
/// Semantically exact: the emitted components are the ORIGINAL selector
/// applications (wrong-variant reads are the theory's free accessor values,
/// which is precisely the per-variant column semantics). The output keeps DT
/// sub-expressions, so this path never yields a DT-free problem by itself.
fn selector_extraction(expr: &ChcExpr, sort: &ChcSort, cx: &FlattenCx<'_>) -> Vec<ChcExpr> {
    let ChcSort::Datatype { constructors, .. } = sort else {
        return vec![rewrite_expr(expr, cx)];
    };
    let rewritten = rewrite_expr(expr, cx);

    if constructors.len() == 1 {
        let ctor = &constructors[0];
        let mut result = Vec::new();
        if ctor.selectors.is_empty() {
            result.push(ChcExpr::Bool(true));
        } else {
            for sel in &ctor.selectors {
                if matches!(sel.sort, ChcSort::Datatype { .. }) {
                    let sel_expr = ChcExpr::FuncApp(
                        sel.name.clone(),
                        sel.sort.clone(),
                        vec![Arc::new(rewritten.clone())],
                    );
                    result.extend(selector_extraction(&sel_expr, &sel.sort, cx));
                } else {
                    result.push(ChcExpr::FuncApp(
                        sel.name.clone(),
                        sel.sort.clone(),
                        vec![Arc::new(rewritten.clone())],
                    ));
                }
            }
        }
        result
    } else {
        // Multi-ctor per-variant columns: disc via tester ITE chain, then one
        // column block per variant (selector applications; wrong-variant
        // reads are the free accessor values).
        let mut result = vec![tester_discriminant_chain(&rewritten, constructors, cx.disc)];
        for ctor in constructors.iter() {
            for sel in &ctor.selectors {
                let expected = flatten_sort_under(sort, &sel.sort, cx.disc).len();
                if expected == 0 {
                    continue;
                }
                let raw_selector = ChcExpr::FuncApp(
                    sel.name.clone(),
                    sel.sort.clone(),
                    vec![Arc::new(rewritten.clone())],
                );
                if matches!(sel.sort, ChcSort::Datatype { .. }) {
                    let mut nested = selector_extraction(&raw_selector, &sel.sort, cx);
                    nested.truncate(expected);
                    let flat_sorts = flatten_sort_under(sort, &sel.sort, cx.disc);
                    while nested.len() < expected {
                        nested.push(
                            flat_sorts
                                .get(nested.len())
                                .and_then(default_expr_for_sort)
                                .unwrap_or(ChcExpr::Int(0)),
                        );
                    }
                    result.extend(nested);
                } else {
                    result.push(raw_selector);
                }
            }
        }
        result
    }
}

/// Discriminant of an opaque DT expression: ITE chain over testers, yielding
/// discriminant constants of the configured kind.
fn tester_discriminant_chain(
    value: &ChcExpr,
    constructors: &[ChcDtConstructor],
    disc: DiscKind,
) -> ChcExpr {
    let mut disc_expr = disc.constant(0);
    for (i, ctor) in constructors.iter().enumerate().rev() {
        if i == 0 {
            continue;
        }
        let tester = tester_expr(value, &ctor.name);
        disc_expr = ChcExpr::ite(tester, disc.constant(i), disc_expr);
    }
    disc_expr
}

// ── Nested selector/tester resolution (#8419) ──────────────────────────────

/// Try to resolve a nested selector chain (e.g., `ok_val(tag(s))`) into the
/// corresponding flattened field variable (#8419).
fn resolve_nested_selector(
    outer_sel_name: &str,
    inner_expr: &ChcExpr,
    cx: &FlattenCx<'_>,
) -> Option<ChcExpr> {
    // Collect the selector chain from outside-in.
    // E.g., ok_val(tag(s)) -> chain = ["ok_val", "tag"], base_var = "s"
    let mut chain: Vec<&str> = vec![outer_sel_name];
    let mut cursor = inner_expr;

    loop {
        match cursor {
            ChcExpr::Var(v) => {
                let field_vars = cx.vars.get(&v.name)?;
                // Reverse chain so it's innermost-first: ["tag", "ok_val"]
                chain.reverse();
                let mut prefix = v.name.clone();
                let mut current_sort = v.sort.clone();
                for sel_name in &chain {
                    let (piece, next_sort) = selector_step(&current_sort, sel_name)?;
                    prefix.push_str(&piece);
                    current_sort = next_sort;
                }
                // For scalar (non-DT) end result, look for exact match.
                if !matches!(current_sort, ChcSort::Datatype { .. }) {
                    for fv in field_vars {
                        if fv.name == prefix {
                            return Some(ChcExpr::Var(fv.clone()));
                        }
                    }
                    return None;
                }
                // For DT end result (intermediate selector returning DT),
                // we can't resolve to a single var.
                return None;
            }
            ChcExpr::FuncApp(name, ret_sort, args)
                if args.len() == 1 && matches!(ret_sort, ChcSort::Datatype { .. }) =>
            {
                // Another DT-returning selector in the chain.
                chain.push(name.as_str());
                cursor = args[0].as_ref();
            }
            _ => return None,
        }
    }
}

/// Try to resolve a nested tester on a selector chain (#8419).
///
/// Handles patterns like `is-ok(tag(s))` where `tag` returns a nested DT
/// and `s` is in the var expansion. Returns a discriminant equality check
/// using the nested DT's discriminant variable.
fn resolve_nested_tester(
    ctor_name: &str,
    inner_expr: &ChcExpr,
    cx: &FlattenCx<'_>,
) -> Option<ChcExpr> {
    // Walk selector chain to find base variable and collect path.
    let mut chain: Vec<&str> = Vec::new();
    let mut cursor = inner_expr;

    let base_var = loop {
        match cursor {
            ChcExpr::Var(v) => {
                cx.vars.get(&v.name)?;
                break v;
            }
            ChcExpr::FuncApp(name, ret_sort, args)
                if args.len() == 1 && matches!(ret_sort, ChcSort::Datatype { .. }) =>
            {
                chain.push(name.as_str());
                cursor = args[0].as_ref();
            }
            _ => return None,
        }
    };

    // chain is in outside-in order; reverse so it's innermost-first.
    chain.reverse();

    // Walk the DT sort tree to find the nested DT sort at the end of the chain.
    let mut current_sort = base_var.sort.clone();
    let mut prefix = base_var.name.clone();
    for sel_name in &chain {
        let (piece, next_sort) = selector_step(&current_sort, sel_name)?;
        prefix.push_str(&piece);
        current_sort = next_sort;
    }

    // current_sort should be the DT that the tester applies to.
    let ChcSort::Datatype { constructors, .. } = &current_sort else {
        return None;
    };

    if constructors.len() == 1 {
        // Single-ctor: tester is always true when the ctor matches.
        return constructors
            .iter()
            .any(|c| c.name == ctor_name)
            .then_some(ChcExpr::Bool(true));
    }

    // Find the constructor index.
    let (ctor_idx, _) = constructors
        .iter()
        .enumerate()
        .find(|(_, c)| c.name == ctor_name)?;

    // Find the disc variable: it should be named `{prefix}_disc`.
    let disc_name = format!("{prefix}_disc");
    let field_vars = cx.vars.get(&base_var.name)?;
    let disc_var = field_vars.iter().find(|fv| fv.name == disc_name)?;

    Some(ChcExpr::eq(
        ChcExpr::Var(disc_var.clone()),
        cx.disc.constant(ctor_idx),
    ))
}

// ── Recursive disc-guarded DT equality (per-variant schema) ────────────────

/// Equality of two flattened DT component slices under the per-variant
/// layout: discriminant equality plus per-variant DISC-GUARDED field
/// equalities (recursive). Inactive-variant columns are never compared.
fn dt_slice_eq(sort: &ChcSort, lhs: &[ChcExpr], rhs: &[ChcExpr], disc: DiscKind) -> ChcExpr {
    dt_slice_eq_with_stack(
        sort,
        lhs,
        rhs,
        &mut Vec::new(),
        recursive_dt_flatten_depth(),
        disc,
    )
}

fn dt_slice_eq_with_stack(
    sort: &ChcSort,
    lhs: &[ChcExpr],
    rhs: &[ChcExpr],
    dt_stack: &mut Vec<String>,
    max_depth: usize,
    disc: DiscKind,
) -> ChcExpr {
    match sort {
        ChcSort::Datatype { name, constructors } => {
            if dt_stack.iter().filter(|seen| *seen == name).count() >= max_depth {
                // Truncated tail: no columns to compare (approximation-grade,
                // tracked by the truncation pre-scan).
                return ChcExpr::Bool(true);
            }
            dt_stack.push(name.clone());
            let result = if constructors.len() == 1 {
                single_ctor_slice_eq(sort, constructors, lhs, rhs, dt_stack, max_depth, disc)
            } else {
                multi_ctor_slice_eq(sort, constructors, lhs, rhs, dt_stack, max_depth, disc)
            };
            dt_stack.pop();
            result
        }
        _ => {
            // Scalar leaf: single column.
            match (lhs.first(), rhs.first()) {
                (Some(l), Some(r)) => ChcExpr::eq(l.clone(), r.clone()),
                _ => ChcExpr::Bool(true),
            }
        }
    }
}

#[allow(clippy::too_many_arguments, clippy::rc_buffer)]
fn single_ctor_slice_eq(
    parent_sort: &ChcSort,
    constructors: &Arc<Vec<ChcDtConstructor>>,
    lhs: &[ChcExpr],
    rhs: &[ChcExpr],
    dt_stack: &mut Vec<String>,
    max_depth: usize,
    disc: DiscKind,
) -> ChcExpr {
    let ctor = &constructors[0];
    if ctor.selectors.is_empty() {
        // Unit struct: values are always equal; the dummy Bool column carries
        // no information.
        return ChcExpr::Bool(true);
    }
    let mut parts = Vec::new();
    let mut idx = 0;
    for sel in &ctor.selectors {
        let len = flatten_sort_with_stack(&sel.sort, dt_stack, max_depth, disc).len();
        if len == 0 {
            continue;
        }
        if idx + len > lhs.len() || idx + len > rhs.len() {
            break;
        }
        let sub = dt_slice_eq_with_stack(
            &sel.sort,
            &lhs[idx..idx + len],
            &rhs[idx..idx + len],
            dt_stack,
            max_depth,
            disc,
        );
        if !matches!(sub, ChcExpr::Bool(true)) {
            parts.push(sub);
        }
        idx += len;
    }
    let _ = parent_sort;
    ChcExpr::and_all(parts)
}

#[allow(clippy::too_many_arguments, clippy::rc_buffer)]
fn multi_ctor_slice_eq(
    parent_sort: &ChcSort,
    constructors: &Arc<Vec<ChcDtConstructor>>,
    lhs: &[ChcExpr],
    rhs: &[ChcExpr],
    dt_stack: &mut Vec<String>,
    max_depth: usize,
    disc: DiscKind,
) -> ChcExpr {
    let (Some(l_disc), Some(r_disc)) = (lhs.first(), rhs.first()) else {
        return ChcExpr::Bool(true);
    };
    let l_lit = disc_literal(l_disc, disc);
    let r_lit = disc_literal(r_disc, disc);

    // Per-variant field equality bodies, computed over matching column blocks.
    let variant_body = |k: usize, dt_stack: &mut Vec<String>| -> ChcExpr {
        let mut idx = 1;
        // Skip preceding variants' blocks.
        for ctor in constructors.iter().take(k) {
            for sel in &ctor.selectors {
                idx += flatten_sort_with_stack(&sel.sort, dt_stack, max_depth, disc).len();
            }
        }
        let mut parts = Vec::new();
        for sel in &constructors[k].selectors {
            let len = flatten_sort_with_stack(&sel.sort, dt_stack, max_depth, disc).len();
            if len == 0 {
                continue;
            }
            if idx + len > lhs.len() || idx + len > rhs.len() {
                break;
            }
            let sub = dt_slice_eq_with_stack(
                &sel.sort,
                &lhs[idx..idx + len],
                &rhs[idx..idx + len],
                dt_stack,
                max_depth,
                disc,
            );
            if !matches!(sub, ChcExpr::Bool(true)) {
                parts.push(sub);
            }
            idx += len;
        }
        ChcExpr::and_all(parts)
    };

    let _ = parent_sort;
    match (l_lit, r_lit) {
        (Some(lk), Some(rk)) => {
            if lk != rk {
                return ChcExpr::Bool(false);
            }
            if lk >= constructors.len() {
                return ChcExpr::eq(l_disc.clone(), r_disc.clone());
            }
            variant_body(lk, dt_stack)
        }
        (Some(k), None) | (None, Some(k)) => {
            let other = if l_lit.is_some() { r_disc } else { l_disc };
            let mut parts = vec![ChcExpr::eq(other.clone(), disc.constant(k))];
            if k < constructors.len() {
                let body = variant_body(k, dt_stack);
                if !matches!(body, ChcExpr::Bool(true)) {
                    parts.push(body);
                }
            }
            ChcExpr::and_all(parts)
        }
        (None, None) => {
            let mut parts = vec![ChcExpr::eq(l_disc.clone(), r_disc.clone())];
            for k in 0..constructors.len() {
                let body = variant_body(k, dt_stack);
                if !matches!(body, ChcExpr::Bool(true)) {
                    parts.push(ChcExpr::implies(
                        ChcExpr::eq(l_disc.clone(), disc.constant(k)),
                        body,
                    ));
                }
            }
            ChcExpr::and_all(parts)
        }
    }
}

// ── Scalar expression rewriting ────────────────────────────────────────────

/// Rewrite a scalar expression, replacing DT operations with their scalar
/// equivalents.
fn rewrite_expr(expr: &ChcExpr, cx: &FlattenCx<'_>) -> ChcExpr {
    crate::expr::maybe_grow_expr_stack(|| match expr {
        // Tester on a DT expression: replace with discriminant check.
        // MUST be checked before the selector arm because testers also
        // match FuncApp(_, Bool, [_]) with !matches!(Bool, Datatype).
        ChcExpr::FuncApp(name, ChcSort::Bool, args)
            if args.len() == 1 && name.starts_with("is-") =>
        {
            let ctor_name = &name[3..]; // strip "is-"
            if let ChcExpr::Var(v) = args[0].as_ref() {
                if let Some(field_vars) = cx.vars.get(&v.name) {
                    if let ChcSort::Datatype { constructors, .. } = &v.sort {
                        if constructors.len() == 1 {
                            // Single-ctor: tester is always true
                            if constructors.iter().any(|c| c.name == ctor_name) {
                                return ChcExpr::Bool(true);
                            }
                        }
                        // Multi-ctor: disc == ctor_idx
                        if let Some((ctor_idx, _)) = constructors
                            .iter()
                            .enumerate()
                            .find(|(_, c)| c.name == ctor_name)
                        {
                            if !field_vars.is_empty() {
                                let disc_var = &field_vars[0]; // first is discriminant
                                return ChcExpr::eq(
                                    ChcExpr::Var(disc_var.clone()),
                                    cx.disc.constant(ctor_idx),
                                );
                            }
                        }
                    }
                }
            }
            // Tester on a constructor application: fold to a constant.
            if let ChcExpr::FuncApp(subj_name, ChcSort::Datatype { constructors, .. }, _) =
                args[0].as_ref()
            {
                if constructors.iter().any(|c| c.name == *subj_name)
                    && constructors.iter().any(|c| c.name == ctor_name)
                {
                    return ChcExpr::Bool(*subj_name == ctor_name);
                }
            }
            // Nested tester on a DT selector chain (#8419).
            if let Some(resolved) = resolve_nested_tester(ctor_name, args[0].as_ref(), cx) {
                return resolved;
            }
            // General subject (ITE of constructor applications, etc.):
            // resolve through the flattened components — the discriminant
            // column is component 0 and is always exact (constructor
            // applications pin it to a constant; ITE distributes it).
            let subject_sort = args[0].sort();
            if let ChcSort::Datatype { constructors, .. } = &subject_sort {
                if let Some((ctor_idx, _)) = constructors
                    .iter()
                    .enumerate()
                    .find(|(_, c)| c.name == ctor_name)
                {
                    if constructors.len() == 1 {
                        return ChcExpr::Bool(true);
                    }
                    let expected = flatten_sort(&subject_sort, cx.disc).len();
                    let comps = flatten_dt_expr(args[0].as_ref(), &subject_sort, cx);
                    if comps.len() == expected {
                        if let Some(disc_comp) = comps.into_iter().next() {
                            return ChcExpr::eq(disc_comp, cx.disc.constant(ctor_idx));
                        }
                    }
                }
            }
            // Not a resolvable tester: rewrite args
            let new_args: Vec<Arc<ChcExpr>> =
                args.iter().map(|a| Arc::new(rewrite_expr(a, cx))).collect();
            ChcExpr::FuncApp(name.clone(), ChcSort::Bool, new_args)
        }

        // Selector on a DT expression: replace with the owning column.
        ChcExpr::FuncApp(sel_name, ret_sort, args)
            if args.len() == 1 && !matches!(ret_sort, ChcSort::Datatype { .. }) =>
        {
            // Check if the argument is a DT variable
            if let ChcExpr::Var(v) = args[0].as_ref() {
                if let Some(field_vars) = cx.vars.get(&v.name) {
                    if matches!(v.sort, ChcSort::Datatype { .. }) {
                        if let Some((_, abs_col, flat_len)) =
                            selector_column(&v.sort, sel_name, cx.disc)
                        {
                            if flat_len == 1 && abs_col < field_vars.len() {
                                return ChcExpr::Var(field_vars[abs_col].clone());
                            }
                        }
                    }
                }
            }
            // Nested selector chain on a DT variable (#8419).
            if let Some(resolved) = resolve_nested_selector(sel_name, args[0].as_ref(), cx) {
                return resolved;
            }
            // Selector on a constructor application: dig into the matching
            // variant's payload, or route a PROVABLY-mismatched read through
            // a deterministic congruent EUF application (never a
            // fresh-per-occurrence variable).
            if let ChcExpr::FuncApp(
                ctor_name,
                ChcSort::Datatype {
                    name: dt_name,
                    constructors,
                },
                ctor_args,
            ) = args[0].as_ref()
            {
                if let Some(ctor) = constructors.iter().find(|c| c.name == *ctor_name) {
                    for (i, sel) in ctor.selectors.iter().enumerate() {
                        if sel.name == *sel_name {
                            if let Some(field_arg) = ctor_args.get(i) {
                                return rewrite_expr(field_arg, cx);
                            }
                        }
                    }
                    // Wrong-variant accessor on a constructed value: SMT
                    // free-accessor semantics. A per-clause free variable
                    // deduplicated by (selector, subject) keeps accessor
                    // congruence inside the clause (all reads of the same
                    // accessor on the same subject agree) while staying
                    // unconstrained — and keeps the flattened problem in
                    // the executor's native BV fragment (no EUF apps).
                    let selector_of_other_variant = constructors.iter().any(|c| {
                        c.name != *ctor_name && c.selectors.iter().any(|s| s.name == *sel_name)
                    });
                    if selector_of_other_variant {
                        cx.record_wva();
                        return cx.wva_var(
                            format!("{dt_name}!{sel_name}"),
                            args[0].as_ref(),
                            ret_sort.clone(),
                        );
                    }
                }
            }
            // General subject (ITE of constructor applications, etc.):
            // resolve through the flattened components — the selector's
            // owning column distributes over ITE branches. Reads that land
            // on a default-filled inactive constructor column are covered by
            // the ctor-app approximation event (recorded when that ctor app
            // was flattened), which fail-closes transformed-evidence Safe
            // acceptance; the Unsafe direction always replays on the
            // original clauses.
            {
                let subject_sort = args[0].sort();
                if matches!(subject_sort, ChcSort::Datatype { .. }) {
                    if let Some((_, abs_col, flat_len)) =
                        selector_column(&subject_sort, sel_name, cx.disc)
                    {
                        if flat_len == 1 {
                            let expected = flatten_sort(&subject_sort, cx.disc).len();
                            let comps = flatten_dt_expr(args[0].as_ref(), &subject_sort, cx);
                            if comps.len() == expected && abs_col < comps.len() {
                                return comps
                                    .into_iter()
                                    .nth(abs_col)
                                    .unwrap_or_else(|| ChcExpr::Bool(false));
                            }
                        }
                    }
                }
            }
            // Fallback: rewrite args
            let new_args: Vec<Arc<ChcExpr>> =
                args.iter().map(|a| Arc::new(rewrite_expr(a, cx))).collect();
            ChcExpr::FuncApp(sel_name.clone(), ret_sort.clone(), new_args)
        }

        // Equality of DT expressions: recursive disc-guarded schema.
        ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
            let lhs_sort = args[0].sort();
            if matches!(lhs_sort, ChcSort::Datatype { .. }) {
                let expected = flatten_sort(&lhs_sort, cx.disc).len();
                let lhs_flat = flatten_dt_expr(&args[0], &lhs_sort, cx);
                let rhs_flat = flatten_dt_expr(&args[1], &lhs_sort, cx);
                if lhs_flat.len() == rhs_flat.len() && lhs_flat.len() == expected && expected > 0 {
                    return dt_slice_eq(&lhs_sort, &lhs_flat, &rhs_flat, cx.disc);
                }
            }
            // Non-DT equality or component mismatch: rewrite args
            ChcExpr::Op(
                ChcOp::Eq,
                args.iter().map(|a| Arc::new(rewrite_expr(a, cx))).collect(),
            )
        }

        // Inequality of DT expressions: negation of the guarded schema.
        ChcExpr::Op(ChcOp::Ne, args) if args.len() == 2 => {
            let lhs_sort = args[0].sort();
            if matches!(lhs_sort, ChcSort::Datatype { .. }) {
                let expected = flatten_sort(&lhs_sort, cx.disc).len();
                let lhs_flat = flatten_dt_expr(&args[0], &lhs_sort, cx);
                let rhs_flat = flatten_dt_expr(&args[1], &lhs_sort, cx);
                if lhs_flat.len() == rhs_flat.len() && lhs_flat.len() == expected && expected > 0 {
                    return ChcExpr::not(dt_slice_eq(&lhs_sort, &lhs_flat, &rhs_flat, cx.disc));
                }
            }
            ChcExpr::Op(
                ChcOp::Ne,
                args.iter().map(|a| Arc::new(rewrite_expr(a, cx))).collect(),
            )
        }

        // General recursive case
        ChcExpr::Op(op, args) => {
            let new_args: Vec<Arc<ChcExpr>> =
                args.iter().map(|a| Arc::new(rewrite_expr(a, cx))).collect();
            ChcExpr::Op(*op, new_args)
        }
        ChcExpr::PredicateApp(name, id, args) => {
            // Predicate apps in constraints shouldn't normally have DT args
            // (those are handled by expand_pred_args), but rewrite sub-exprs.
            let new_args: Vec<Arc<ChcExpr>> =
                args.iter().map(|a| Arc::new(rewrite_expr(a, cx))).collect();
            ChcExpr::PredicateApp(name.clone(), *id, new_args)
        }
        ChcExpr::FuncApp(name, sort, args) => {
            let new_args: Vec<Arc<ChcExpr>> =
                args.iter().map(|a| Arc::new(rewrite_expr(a, cx))).collect();
            ChcExpr::FuncApp(name.clone(), sort.clone(), new_args)
        }
        ChcExpr::ConstArray(sort, val) => {
            ChcExpr::ConstArray(sort.clone(), Arc::new(rewrite_expr(val, cx)))
        }
        // Atoms: pass through unchanged
        _ => expr.clone(),
    })
}

fn default_expr_for_sort(sort: &ChcSort) -> Option<ChcExpr> {
    match sort {
        ChcSort::Bool => Some(ChcExpr::Bool(false)),
        ChcSort::Int => Some(ChcExpr::Int(0)),
        ChcSort::Real => Some(ChcExpr::Real(0, 1)),
        ChcSort::BitVec(width) => Some(ChcExpr::BitVec(0, *width)),
        ChcSort::Array(key, value) => {
            let value = default_expr_for_sort(value)?;
            Some(ChcExpr::ConstArray(key.as_ref().clone(), Arc::new(value)))
        }
        ChcSort::Datatype { .. } => None,
        ChcSort::Uninterpreted(_) => None,
    }
}

// ── Back-translation ───────────────────────────────────────────────────────

struct DtFlatBackTranslator {
    map: DtFlatMap,
    /// INPUT (unflattened) problem, retained for ground back-translation only.
    ///
    /// Flattening keeps every clause and its order, so a ground derivation maps
    /// across index-for-index. The datatype VALUES are not read out of the flat
    /// columns: they are recovered by ground propagation over the original
    /// clause's own constructor/selector equalities, which is exact when those
    /// equalities determine them and a rejection when they do not.
    input_problem: Option<std::sync::Arc<ChcProblem>>,
}

impl BackTranslator for DtFlatBackTranslator {
    fn translate_ground_derivation(
        &self,
        derivation: &crate::ground_derivation::GroundDerivation,
    ) -> Option<crate::ground_derivation::GroundDerivation> {
        // NOTE ON APPROXIMATION EVENTS. Flattening reports wrong-variant
        // accessor reads, default-filled inactive constructor columns and
        // recursion truncation, and those DO make the flat problem an
        // over-approximation — which is exactly why
        // `unsafe_backtranslation_complete` is false and why the transformed
        // witness may never be trusted.
        //
        // They are NOT a reason to refuse the ground attempt. Nothing about the
        // flat problem is being believed here: the candidate derivation is
        // rebuilt over the ORIGINAL datatype clauses and then DECIDED by
        // evaluation against them. If an approximated column made the
        // transformed counterexample spurious, the reconstructed datatype
        // values will not satisfy the original constructor/selector equalities
        // and validation rejects it. Refusing to try would only lose real
        // counterexamples; it cannot make a fabricated one safe, because
        // validation — not provenance — is the trust anchor.
        if self.map.events.any() {
            crate::ground_derivation::log_ground_translation_detail(format_args!(
                "dt-flattener: approximation events present (wrong-variant reads {}, \
                 default-filled columns {}, truncated recursion {}); attempting the ground \
                 reconstruction anyway — the original-clause validator decides",
                self.map.events.wrong_variant_reads,
                self.map.events.ctor_app_default_columns,
                self.map.events.truncated_recursion
            ));
        }
        let input_problem = self.input_problem.clone()?;
        let candidates = (0..input_problem.clauses().len())
            .map(|index| vec![index])
            .collect();
        let disc = self.map.disc;
        crate::ground_derivation::clause_map::ClauseMapGroundTranslator::new(
            "dt-flattener",
            input_problem,
            candidates,
        )
        .with_seeder(Box::new(move |clause, flat_env, env| {
            seed_dt_values_from_columns(clause, flat_env, env, disc);
        }))
        .translate(derivation)
    }

    fn ground_translation_name(&self) -> &'static str {
        "dt-flattener"
    }

    fn translate_validity(&self, witness: ValidityWitness) -> ValidityWitness {
        reconstruct_dt_invariant(&witness, &self.map)
    }

    fn translate_invalidity(&self, witness: InvalidityWitness) -> InvalidityWitness {
        reconstruct_dt_counterexample(witness, &self.map)
    }

    fn transform_memory(&self) -> TransformMemoryReport {
        let flattened_args = self.map.flattened_arg_count();
        let component_obligations = self.map.component_obligation_count();
        let (single_ctor_args, multi_ctor_args) = self.map.constructor_shape_counts();

        let mut obligations = vec![
            TransformObligation::named("datatype-model-reconstruction"),
            TransformObligation::named("datatype-counterexample-reconstruction"),
            TransformObligation::named("datatype-selector-refinement-obligations"),
            TransformObligation::named("original-validation-on-safe"),
            TransformObligation::named("original-replay-on-unsafe"),
        ];
        if self.map.events.any() {
            obligations.push(TransformObligation::named(DT_FLATTEN_APPROX_OBLIGATION));
        }

        TransformMemoryReport::with_original_validation_obligations("dt_flatten", obligations)
            .with_fact(
                "datatype_flattening_maps",
                self.map.pred_original_sorts.len().to_string(),
            )
            .with_fact("datatype_flattened_args", flattened_args.to_string())
            .with_fact(
                "datatype_component_obligations",
                component_obligations.to_string(),
            )
            .with_fact("datatype_single_ctor_args", single_ctor_args.to_string())
            .with_fact("datatype_multi_ctor_args", multi_ctor_args.to_string())
            .with_fact(
                "datatype_ctor_app_default_columns",
                self.map.events.ctor_app_default_columns.to_string(),
            )
            .with_fact(
                "datatype_wrong_variant_reads",
                self.map.events.wrong_variant_reads.to_string(),
            )
            .with_fact(
                "datatype_truncated_recursion",
                self.map.events.truncated_recursion.to_string(),
            )
            .with_incomplete_unsafe_backtranslation()
    }
}

impl DtFlatMap {
    fn flattened_arg_count(&self) -> usize {
        self.pred_arg_flattened
            .values()
            .map(|args| args.iter().filter(|flattened| **flattened).count())
            .sum()
    }

    fn component_obligation_count(&self) -> usize {
        self.pred_arg_dt_info
            .values()
            .flat_map(|infos| infos.iter())
            .filter_map(Option::as_ref)
            .map(|info| info.components.len())
            .sum()
    }

    fn constructor_shape_counts(&self) -> (usize, usize) {
        self.pred_arg_dt_info
            .values()
            .flat_map(|infos| infos.iter())
            .filter_map(Option::as_ref)
            .fold((0, 0), |(single, multi), info| {
                if info.single_ctor {
                    (single + 1, multi)
                } else {
                    (single, multi + 1)
                }
            })
    }
}

#[cfg(test)]
#[derive(Debug, Clone)]
#[allow(dead_code)]
struct FlattenedSelectorBinding {
    replacement: ChcExpr,
}

/// Reconstruct DT-sorted invariant model from flattened model.
fn reconstruct_dt_invariant(inv: &InvariantModel, map: &DtFlatMap) -> InvariantModel {
    let mut result = InvariantModel::new();
    for (pid, interp) in inv.iter() {
        let Some(orig_sorts) = map.pred_original_sorts.get(pid) else {
            result.set(*pid, interp.clone());
            continue;
        };

        match reconstruct_dt_interpretation(*pid, interp, orig_sorts, map) {
            Some(translated) => result.set(*pid, translated),
            None => {
                // Fail closed: unsupported flattening shapes must not let a SAFE
                // model validate with stale flattened free variables.
                result.set(
                    *pid,
                    PredicateInterpretation::new(Vec::new(), ChcExpr::Bool(false)),
                );
            }
        }
    }
    result
}

fn reconstruct_dt_interpretation(
    pid: PredicateId,
    interp: &PredicateInterpretation,
    orig_sorts: &[ChcSort],
    map: &DtFlatMap,
) -> Option<PredicateInterpretation> {
    let flattened = map.pred_arg_flattened.get(&pid)?;
    let arg_infos = map.pred_arg_dt_info.get(&pid)?;
    if flattened.len() != orig_sorts.len() {
        return None;
    }

    let mut new_vars = Vec::with_capacity(orig_sorts.len());
    let mut substitutions = Vec::new();
    let mut flat_idx = 0;

    for (arg_idx, sort) in orig_sorts.iter().enumerate() {
        let was_flattened = flattened.get(arg_idx).copied().unwrap_or(false);

        if was_flattened {
            let info = arg_infos.get(arg_idx)?.as_ref()?;
            if info.original_arg != arg_idx
                || info.original_sort != *sort
                || info.components.len() != flatten_sort(sort, map.disc).len()
                || info.single_ctor
                    != matches!(sort, ChcSort::Datatype { constructors, .. } if constructors.len() == 1)
                || !dt_arg_info_matches_sort(info, sort, map.disc)
            {
                return None;
            }
            for (component_idx, binding) in info.components.iter().enumerate() {
                let transformed_var = interp.vars.get(flat_idx)?;
                if transformed_var.sort != binding.sort
                    || transformed_var.sort != binding.replacement.sort()
                    || binding.flat_offset != component_idx
                {
                    return None;
                }
                substitutions.push((transformed_var.clone(), binding.replacement.clone()));
                flat_idx += 1;
            }
            new_vars.push(info.original_var.clone());
        } else {
            let transformed_var = interp.vars.get(flat_idx)?;
            if transformed_var.sort != *sort {
                return None;
            }
            new_vars.push(transformed_var.clone());
            flat_idx += 1;
        }
    }

    if flat_idx != interp.vars.len() {
        return None;
    }

    Some(PredicateInterpretation::new(
        new_vars,
        interp.formula.substitute(&substitutions),
    ))
}

fn dt_arg_info_matches_sort(info: &DtArgFlatInfo, sort: &ChcSort, disc: DiscKind) -> bool {
    let ChcSort::Datatype { constructors, .. } = sort else {
        return false;
    };
    if info.constructors.as_ref() != constructors.as_ref() {
        return false;
    }
    info.components
        .iter()
        .all(|component| component_obligation_sort_compatible(component, disc))
}

fn component_obligation_sort_compatible(
    component: &DtFlatComponentBinding,
    disc: DiscKind,
) -> bool {
    match &component.obligation {
        DtRefinementObligation::Unit => component.sort == ChcSort::Bool,
        DtRefinementObligation::Discriminant => {
            component.sort == disc.sort() && component.sort == component.replacement.sort()
        }
        DtRefinementObligation::SelectorPath(_) | DtRefinementObligation::GuardedPayload { .. } => {
            component.sort == component.replacement.sort()
        }
    }
}

fn flat_component_bindings_for_sort(
    sort: &ChcSort,
    value: &ChcExpr,
    disc: DiscKind,
) -> Option<Vec<DtFlatComponentBinding>> {
    let replacements = flattened_component_exprs_for_sort(sort, value.clone(), disc)?;
    let obligations = refinement_obligations_for_sort(sort, disc)?;
    if replacements.len() != obligations.len() {
        return None;
    }

    Some(
        replacements
            .into_iter()
            .zip(obligations)
            .enumerate()
            .map(
                |(flat_offset, (replacement, obligation))| DtFlatComponentBinding {
                    flat_offset,
                    sort: replacement.sort(),
                    replacement,
                    obligation,
                },
            )
            .collect(),
    )
}

#[cfg(test)]
fn flattened_selector_bindings_for_sort(
    sort: &ChcSort,
    original_var: &ChcVar,
    disc: DiscKind,
) -> Option<Vec<FlattenedSelectorBinding>> {
    let components =
        flat_component_bindings_for_sort(sort, &ChcExpr::var(original_var.clone()), disc)?;
    Some(
        components
            .into_iter()
            .map(|component| FlattenedSelectorBinding {
                replacement: component.replacement,
            })
            .collect(),
    )
}

fn refinement_obligations_for_sort(
    sort: &ChcSort,
    disc: DiscKind,
) -> Option<Vec<DtRefinementObligation>> {
    refinement_obligations_with_stack(
        sort,
        &mut Vec::new(),
        recursive_dt_flatten_depth(),
        &mut Vec::new(),
        disc,
    )
}

fn refinement_obligations_with_stack(
    sort: &ChcSort,
    dt_stack: &mut Vec<String>,
    max_depth: usize,
    selector_path: &mut Vec<String>,
    disc: DiscKind,
) -> Option<Vec<DtRefinementObligation>> {
    match sort {
        ChcSort::Datatype { name, constructors } => {
            if dt_stack.iter().filter(|seen| *seen == name).count() >= max_depth {
                return Some(Vec::new());
            }
            dt_stack.push(name.clone());
            let result = if constructors.len() == 1 {
                let ctor = &constructors[0];
                if ctor.selectors.is_empty() {
                    vec![DtRefinementObligation::Unit]
                } else {
                    let mut result = Vec::new();
                    for selector in &ctor.selectors {
                        selector_path.push(selector.name.clone());
                        result.extend(refinement_obligations_with_stack(
                            &selector.sort,
                            dt_stack,
                            max_depth,
                            selector_path,
                            disc,
                        )?);
                        selector_path.pop();
                    }
                    if result.is_empty() {
                        result.push(DtRefinementObligation::Unit);
                    }
                    result
                }
            } else {
                // Per-variant columns: discriminant, then each variant's
                // fields. Direct scalar leaves are GuardedPayload records
                // owned by exactly one constructor; nested DT fields recurse
                // into their own obligation blocks.
                let mut result = vec![DtRefinementObligation::Discriminant];
                for ctor in constructors.iter() {
                    for selector in &ctor.selectors {
                        if matches!(selector.sort, ChcSort::Datatype { .. }) {
                            selector_path.push(selector.name.clone());
                            result.extend(refinement_obligations_with_stack(
                                &selector.sort,
                                dt_stack,
                                max_depth,
                                selector_path,
                                disc,
                            )?);
                            selector_path.pop();
                        } else {
                            let flat_len =
                                flatten_sort_with_stack(&selector.sort, dt_stack, max_depth, disc)
                                    .len();
                            for _ in 0..flat_len {
                                let field_offset = result.len();
                                result.push(DtRefinementObligation::GuardedPayload {
                                    constructors: vec![ctor.name.clone()],
                                    field_offset,
                                });
                            }
                        }
                    }
                }
                result
            };
            dt_stack.pop();
            Some(result)
        }
        ChcSort::Uninterpreted(name)
            if dt_stack.iter().filter(|seen| *seen == name).count() >= max_depth =>
        {
            Some(Vec::new())
        }
        _ => Some(vec![DtRefinementObligation::SelectorPath(
            selector_path.clone(),
        )]),
    }
}

fn flattened_component_exprs_for_sort(
    sort: &ChcSort,
    value: ChcExpr,
    disc: DiscKind,
) -> Option<Vec<ChcExpr>> {
    flattened_component_exprs_with_stack(
        sort,
        value,
        &mut Vec::new(),
        recursive_dt_flatten_depth(),
        disc,
    )
}

fn flattened_component_exprs_with_stack(
    sort: &ChcSort,
    value: ChcExpr,
    dt_stack: &mut Vec<String>,
    max_depth: usize,
    disc: DiscKind,
) -> Option<Vec<ChcExpr>> {
    match sort {
        ChcSort::Datatype { name, constructors } => {
            if dt_stack.iter().filter(|seen| *seen == name).count() >= max_depth {
                return Some(Vec::new());
            }

            dt_stack.push(name.clone());
            let result = if constructors.len() == 1 {
                flattened_single_ctor_components(constructors, value, dt_stack, max_depth, disc)
            } else {
                flattened_multi_ctor_components(constructors, value, dt_stack, max_depth, disc)
            };
            dt_stack.pop();
            result
        }
        ChcSort::Uninterpreted(name)
            if dt_stack.iter().filter(|seen| *seen == name).count() >= max_depth =>
        {
            Some(Vec::new())
        }
        _ => Some(vec![value]),
    }
}

#[allow(clippy::rc_buffer)]
fn flattened_single_ctor_components(
    constructors: &Arc<Vec<ChcDtConstructor>>,
    value: ChcExpr,
    dt_stack: &mut Vec<String>,
    max_depth: usize,
    disc: DiscKind,
) -> Option<Vec<ChcExpr>> {
    let ctor = &constructors[0];
    if ctor.selectors.is_empty() {
        return Some(vec![ChcExpr::Bool(true)]);
    }

    let mut result = Vec::new();
    for selector in &ctor.selectors {
        let selected = selector_app(&value, selector);
        result.extend(flattened_component_exprs_with_stack(
            &selector.sort,
            selected,
            dt_stack,
            max_depth,
            disc,
        )?);
    }
    if result.is_empty() {
        result.push(ChcExpr::Bool(true));
    }
    Some(result)
}

/// Per-variant columns: the discriminant (tester ITE chain) followed by every
/// variant's selector applications. Wrong-variant selector applications are
/// exactly the theory's free accessor values — the column semantics.
#[allow(clippy::rc_buffer)]
fn flattened_multi_ctor_components(
    constructors: &Arc<Vec<ChcDtConstructor>>,
    value: ChcExpr,
    dt_stack: &mut Vec<String>,
    max_depth: usize,
    disc: DiscKind,
) -> Option<Vec<ChcExpr>> {
    let mut result = vec![discriminant_expr(&value, constructors, disc)];
    for ctor in constructors.iter() {
        for selector in &ctor.selectors {
            let selected = selector_app(&value, selector);
            result.extend(flattened_component_exprs_with_stack(
                &selector.sort,
                selected,
                dt_stack,
                max_depth,
                disc,
            )?);
        }
    }
    Some(result)
}

fn discriminant_expr(
    value: &ChcExpr,
    constructors: &[ChcDtConstructor],
    disc: DiscKind,
) -> ChcExpr {
    let mut disc_expr = disc.constant(0);
    for (idx, ctor) in constructors.iter().enumerate().rev() {
        if idx == 0 {
            continue;
        }
        disc_expr = ChcExpr::ite(
            tester_expr(value, &ctor.name),
            disc.constant(idx),
            disc_expr,
        );
    }
    disc_expr
}

fn selector_app(value: &ChcExpr, selector: &ChcDtSelector) -> ChcExpr {
    ChcExpr::FuncApp(
        selector.name.clone(),
        selector.sort.clone(),
        vec![Arc::new(value.clone())],
    )
}

fn tester_expr(value: &ChcExpr, ctor_name: &str) -> ChcExpr {
    ChcExpr::FuncApp(
        format!("is-{ctor_name}"),
        ChcSort::Bool,
        vec![Arc::new(value.clone())],
    )
}

/// Reconstruct DT counterexample from flattened counterexample.
fn reconstruct_dt_counterexample(mut cex: InvalidityWitness, map: &DtFlatMap) -> InvalidityWitness {
    for step in &mut cex.steps {
        let Some(orig_sorts) = map.pred_original_sorts.get(&step.predicate) else {
            continue;
        };
        let flattened = map.pred_arg_flattened.get(&step.predicate);

        let mut new_assignments = FxHashMap::default();
        let mut flat_idx = 0;
        for (arg_idx, sort) in orig_sorts.iter().enumerate() {
            let was_flattened = flattened
                .and_then(|f| f.get(arg_idx))
                .copied()
                .unwrap_or(false);

            if was_flattened {
                let n_flat = flatten_sort(sort, map.disc).len();
                // Copy flattened assignments with original-style names
                for i in 0..n_flat {
                    let flat_name = format!("x{}", flat_idx + i);
                    if let Some(&val) = step.assignments.get(&flat_name) {
                        new_assignments.insert(flat_name, val);
                    }
                }
                flat_idx += n_flat;
            } else {
                let name = format!("x{flat_idx}");
                if let Some(&val) = step.assignments.get(&name) {
                    new_assignments.insert(name, val);
                }
                flat_idx += 1;
            }
        }
        step.assignments = new_assignments;
    }
    cex
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
mod tests;

// ── Ground back-translation: datatype values from flat columns ─────────────

/// Rebuild datatype-sorted clause variables from their flattened columns.
///
/// Flattening replaces a datatype variable `v` of a multi-constructor sort by a
/// discriminant column `v_disc` plus, for every constructor `k` and selector
/// `sel`, a column `v_v{k}_{sel}` (recursively); a single-constructor sort uses
/// `v_{sel}` directly, or `v_unit` when it has no fields. That naming is a pure
/// function of the variable name and sort, so the value is recovered by reading
/// the discriminant, choosing the constructor, and assembling the active
/// variant's fields — no per-clause map has to be retained.
///
/// This writes into `env` WITHOUT overwriting existing bindings, and everything
/// it writes is subsequently checked by ground validation against the original
/// datatype clause. Columns belonging to inactive variants are ignored by
/// construction (only the discriminant-selected variant is read), which is why
/// default-filled inactive columns cannot leak into the reconstructed value.
fn seed_dt_values_from_columns(
    clause: &HornClause,
    flat_env: &ay_core::kani_compat::DetHashMap<String, crate::smt::SmtValue>,
    env: &mut ay_core::kani_compat::DetHashMap<String, crate::smt::SmtValue>,
    disc: DiscKind,
) {
    let mut vars = clause.body.vars();
    for var in clause.head.vars() {
        if !vars.contains(&var) {
            vars.push(var);
        }
    }
    for var in vars {
        if env.contains_key(&var.name) {
            continue;
        }
        if !matches!(var.sort, ChcSort::Datatype { .. }) {
            continue;
        }
        if let Some(value) = dt_value_from_columns(
            &var.name,
            &var.sort,
            flat_env,
            disc,
            recursive_dt_flatten_depth(),
        ) {
            env.insert(var.name.clone(), value);
        }
    }
}

/// Read one datatype value out of the flat columns rooted at `prefix`.
fn dt_value_from_columns(
    prefix: &str,
    sort: &ChcSort,
    flat_env: &ay_core::kani_compat::DetHashMap<String, crate::smt::SmtValue>,
    disc: DiscKind,
    fuel: usize,
) -> Option<crate::smt::SmtValue> {
    use crate::smt::SmtValue;
    match sort {
        ChcSort::Datatype { constructors, .. } => {
            if fuel == 0 {
                return None;
            }
            let (ctor, field_prefix): (&ChcDtConstructor, Box<dyn Fn(&str) -> String>) =
                if constructors.len() == 1 {
                    let ctor = constructors.first()?;
                    let base = prefix.to_string();
                    (ctor, Box::new(move |sel: &str| format!("{base}_{sel}")))
                } else {
                    // Multi-constructor: the discriminant column selects the
                    // live variant; only that variant's columns are read.
                    let disc_value = flat_env.get(&format!("{prefix}_disc"))?;
                    let index = match (disc, disc_value) {
                        (DiscKind::Int, SmtValue::Int(value)) => usize::try_from(*value).ok()?,
                        (DiscKind::Bv8, SmtValue::BitVec(value, 8)) => {
                            usize::try_from(*value).ok()?
                        }
                        _ => return None,
                    };
                    let ctor = constructors.get(index)?;
                    let base = prefix.to_string();
                    (
                        ctor,
                        Box::new(move |sel: &str| format!("{base}_v{index}_{sel}")),
                    )
                };
            if ctor.selectors.is_empty() {
                return Some(SmtValue::Datatype(ctor.name.clone(), Vec::new()));
            }
            let mut fields = Vec::with_capacity(ctor.selectors.len());
            for sel in &ctor.selectors {
                let name = field_prefix(&sel.name);
                fields.push(dt_value_from_columns(
                    &name,
                    &sel.sort,
                    flat_env,
                    disc,
                    fuel - 1,
                )?);
            }
            Some(SmtValue::Datatype(ctor.name.clone(), fields))
        }
        _ => flat_env.get(prefix).cloned(),
    }
}
