// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Term representation for AY
//!
//! Terms are represented as a hash-consed DAG for efficient sharing.
//! The `TermStore` manages term creation and ensures structural sharing
//! through hash-consing.

use crate::kani_compat::KaniHashMap;
use crate::sort::Sort;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, ToPrimitive, Zero};
use serde::{Deserialize, Serialize};
use std::fmt;
use std::hash::{BuildHasher, Hash, Hasher};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

mod arith_div_cmp;
mod arithmetic;
mod arithmetic_sub_mul;
mod array;
mod bitvector;
mod boolean;
mod boolean_eq;
mod builders;
mod cardinality;
mod compact;
mod expand_select_store;
mod ite_lifting;
mod preprocess;
mod subst;

pub use compact::{RemapTable, Remappable};
#[allow(clippy::panic)]
#[cfg(test)]
mod tests;

/// Global counter tracking approximate bytes allocated across ALL TermStore instances.
///
/// Each portfolio engine has its own TermStore. This atomic provides cross-engine
/// visibility into aggregate memory consumption, enabling the portfolio coordinator
/// or engine cancellation checks to detect OOM conditions before they crash the process.
///
/// The count includes `size_of::<TermEntry>()` per interned term plus estimated
/// heap allocations within `TermData` variants: `Vec<TermId>` children in `App`,
/// `String` capacity in constants/variables, quantifier variable/trigger lists,
/// let-binding lists, BigInt digit heap for `Int`/`BitVec`/`Rational` constants,
/// hash_cons bucket `Vec<TermId>` growth, and `names` HashMap entry overhead
/// (#8600). The BigInt heap estimate uses `bits()` to count limbs, which
/// slightly underestimates due to Vec capacity rounding, but is close enough
/// for OOM detection.
static GLOBAL_TERM_BYTES: AtomicUsize = AtomicUsize::new(0);

/// Global counter for the number of active portfolio engines.
///
/// Set by the portfolio coordinator before spawning engines. Used to compute
/// per-engine memory budgets: `global_term_memory_limit / max(1, engine_count)`.
/// This prevents a single engine from consuming the entire budget, leaving
/// nothing for fallback engines (#8600 item 5).
static GLOBAL_ENGINE_COUNT: AtomicUsize = AtomicUsize::new(1);

/// Default memory limit for aggregate TermStore allocation: unlimited.
///
/// Set to `usize::MAX` so that ay uses all available system resources by
/// default. The caller controls limits via `ay_sys::set_process_memory_limit()`
/// (CLI `-memory:<MB>` or `AY_MEMORY_LIMIT` env var). The term-byte counter
/// still tracks allocation for observability, but will never trigger early
/// exit on its own.
///
/// When multiple engines are active, `per_engine_budget()` divides this by
/// `engine_count`. With `usize::MAX`, each engine's budget is also effectively
/// unlimited, which is correct: the process-level RSS check handles OOM.
const DEFAULT_TERM_MEMORY_LIMIT: usize = usize::MAX;

/// Configurable aggregate TermStore allocation limit.
///
/// Defaults to [`DEFAULT_TERM_MEMORY_LIMIT`] and is intentionally separate from
/// the global term-byte counter so tests and embedding callers can exercise the
/// term-memory guard without restoring the old hard-coded 4GB cap.
static GLOBAL_TERM_MEMORY_LIMIT: AtomicUsize = AtomicUsize::new(DEFAULT_TERM_MEMORY_LIMIT);

/// Delta in `instance_term_bytes` that triggers a recomputation of the cached
/// `true_memory_bytes()`. Set to 64 KiB: fine-grained enough to catch memory
/// growth before OOM, but coarse enough to avoid O(hash_cons.len()) scans on
/// every DPLL(T) iteration (#8600).
const TRUE_MEMORY_RECOMPUTE_DELTA: usize = 64 * 1024;

/// A term identifier (index into the term store)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
#[must_use = "TermId must be used (discarding it usually indicates a bug)"]
pub struct TermId(pub u32);

impl TermId {
    /// Sentinel value used by the LRA simplex solver for bounds that have no
    /// SAT-level atom reason (e.g., Gomory/HNF cuts, model-seed probing).
    /// Must never collide with a real interned term ID.
    pub const SENTINEL: Self = Self(u32::MAX);

    /// Create a new TermId
    pub fn new(id: u32) -> Self {
        Self(id)
    }

    /// Returns true if this is the sentinel (no real atom reason).
    pub fn is_sentinel(self) -> bool {
        self.0 == u32::MAX
    }

    /// Get the raw index
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

impl fmt::Display for TermId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "t{}", self.0)
    }
}

/// Internal term representation with pre-computed hash
#[derive(Debug, Clone)]
struct TermEntry {
    term: TermData,
    sort: Sort,
}

/// The actual term data
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum TermData {
    /// A constant value
    Const(Constant),
    /// A variable with name and unique ID
    Var(String, u32),
    /// Function application: function symbol + arguments
    App(Symbol, Vec<TermId>),
    /// Let binding (after expansion this should not appear)
    Let(Vec<(String, TermId)>, TermId),
    /// Negation (special case for efficient handling)
    Not(TermId),
    /// If-then-else
    Ite(TermId, TermId, TermId),
    /// Universal quantifier: forall ((x1 S1) (x2 S2) ...) body
    ///
    /// Triggers are multi-patterns:
    /// - Outer Vec = alternative trigger sets (disjunction)
    /// - Inner Vec = multi-trigger patterns (conjunction; currently flattened by E-matching)
    Forall(Vec<(String, Sort)>, TermId, Vec<Vec<TermId>>),
    /// Existential quantifier: exists ((x1 S1) (x2 S2) ...) body
    ///
    /// Triggers are multi-patterns:
    /// - Outer Vec = alternative trigger sets (disjunction)
    /// - Inner Vec = multi-trigger patterns (conjunction; currently flattened by E-matching)
    Exists(Vec<(String, Sort)>, TermId, Vec<Vec<TermId>>),
}

impl Hash for TermData {
    fn hash<H: Hasher>(&self, state: &mut H) {
        std::mem::discriminant(self).hash(state);
        match self {
            Self::Const(c) => c.hash(state),
            Self::Var(name, id) => {
                name.hash(state);
                id.hash(state);
            }
            Self::App(sym, args) => {
                sym.hash(state);
                args.hash(state);
            }
            Self::Let(bindings, body) => {
                bindings.hash(state);
                body.hash(state);
            }
            Self::Not(t) => t.hash(state),
            Self::Ite(c, t, e) => {
                c.hash(state);
                t.hash(state);
                e.hash(state);
            }
            Self::Forall(vars, body, triggers) | Self::Exists(vars, body, triggers) => {
                for (name, sort) in vars {
                    name.hash(state);
                    sort.hash(state);
                }
                body.hash(state);
                triggers.hash(state);
            }
        }
    }
}

/// Function/predicate symbol
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum Symbol {
    /// Named function (user-defined or built-in)
    Named(String),
    /// Indexed function like (_ extract 7 4)
    Indexed(String, Vec<u32>),
}

impl Symbol {
    /// Create a named symbol
    pub fn named(name: impl Into<String>) -> Self {
        Self::Named(name.into())
    }

    /// Create an indexed symbol
    pub fn indexed(name: impl Into<String>, indices: Vec<u32>) -> Self {
        Self::Indexed(name.into(), indices)
    }

    /// Get the name of the symbol
    pub fn name(&self) -> &str {
        match self {
            Self::Named(n) | Self::Indexed(n, _) => n,
        }
    }
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Named(n) => write!(f, "{n}"),
            Self::Indexed(n, indices) => {
                write!(f, "(_ {n}")?;
                for idx in indices {
                    write!(f, " {idx}")?;
                }
                write!(f, ")")
            }
        }
    }
}

/// Constant values
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum Constant {
    /// Boolean constant
    Bool(bool),
    /// Integer constant (arbitrary precision)
    Int(BigInt),
    /// Rational constant
    Rational(RationalWrapper),
    /// Bitvector constant with value and width
    BitVec {
        /// The numeric value of the bitvector
        value: BigInt,
        /// The bit width of the bitvector
        width: u32,
    },
    /// String constant
    String(String),
}

/// Wrapper for BigRational to implement Eq and Hash
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RationalWrapper(pub BigRational);

impl PartialEq for RationalWrapper {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl Eq for RationalWrapper {}

impl Hash for RationalWrapper {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Hash the normalized form
        self.0.numer().hash(state);
        self.0.denom().hash(state);
    }
}

impl From<BigRational> for RationalWrapper {
    fn from(r: BigRational) -> Self {
        Self(r)
    }
}

/// Hash-consing term store
///
/// All terms are stored uniquely. Creating a term that already exists
/// returns the existing TermId.
// Trust: `Clone` lets an independent UNSAT re-discharge build a FRESH `Executor`
// over a copy of an existing store (preserving the original parser-built term
// structure, which the thin `Solver`+`Translator` re-build does not — the latter
// defeats `solve_lia` on deep nested-ite obligations). The store is plain data;
// cloning also mints a distinct rollback identity so an opaque speculative
// checkpoint can never be transplanted between the two otherwise-identical
// stores.
#[derive(Clone)]
pub struct TermStore {
    /// All terms, indexed by TermId
    terms: Vec<TermEntry>,
    /// Hash-cons map: hash -> list of term IDs with that hash
    hash_cons: KaniHashMap<u64, Vec<TermId>>,
    /// Memoization for `mk_not`: arg TermId -> negated result. `mk_not` performs
    /// recursive De Morgan / ITE-negation push-down, which without memoization
    /// re-processes shared (let-bound) subterms — an O(DAG-unfolded-to-tree)
    /// blow-up on large heavily-shared formulas (e.g. a state-machine VC with
    /// 100k+ `let` shares). Sound: `mk_not` is a pure deterministic function of
    /// its arg. TermIds below a sealed speculative rollback checkpoint remain
    /// stable, and rollback prunes every cache entry that mentions a discarded
    /// ID before that suffix can be reused. (#mk-not-memo)
    not_cache: KaniHashMap<TermId, TermId>,
    /// Variable counter for generating unique IDs
    var_counter: u32,
    /// Named constants/variables: name -> (TermId, Sort)
    names: KaniHashMap<String, (TermId, Sort)>,
    /// Pre-allocated common terms
    true_term: Option<TermId>,
    false_term: Option<TermId>,
    /// A user declaration has SHADOWED the builtin `to_real` symbol (it is
    /// deliberately declarable as a `(_ map f)` target). When set, the
    /// to_real-integrality rewrites in the comparison/equality constructors are
    /// disabled — a user's uninterpreted `to_real` is byte-identical to the
    /// builtin App in the store, and rewriting it would fabricate semantics for
    /// a free function (a wrong-verdict class). Sticky across pop: deliberately
    /// conservative, fail-closed. (#to-real-bridge)
    to_real_shadowed: bool,
    /// A user declaration has SHADOWED the builtin `is_int` symbol (it is
    /// deliberately declarable — `is_int` is a legal `(_ map f)` target and
    /// carries the `"map-target"` tag in `EXCLUDED_DECLARABLE_OP_NAMES`). When
    /// set, the `is_int` quantifier eliminator (`ay-dpll::qe::isint`) stands
    /// down: a user's uninterpreted `is_int` builds an App byte-identical to the
    /// builtin's, and applying integrality (critical-residue) reasoning to a
    /// free predicate fabricates its semantics — a confirmed wrong-UNSAT class
    /// (`(declare-fun is_int (Real) Bool)` + `(forall ((x Real)) (is_int x))`
    /// decided `unsat` where z3 exhibits the model `is_int ≡ λx.true`). Sticky
    /// across pop: deliberately conservative, fail-closed. Mirrors
    /// `to_real_shadowed`. (#isint-shadow)
    is_int_shadowed: bool,
    /// Per-instance term memory counter (bytes). Not shared across instances.
    /// Tracks approximate allocation for THIS TermStore only, enabling
    /// per-solver memory budgets without cross-instance interference (#6563).
    instance_term_bytes: usize,
    /// Accumulated heap bytes from `TermData` contents only (Vec children,
    /// String capacity, BigInt limbs). Tracked separately from container
    /// overhead so that `true_memory_bytes()` can compute an accurate total
    /// without double-counting (#8600).
    heap_data_bytes: usize,
    /// Total capacity (in bytes) of all bucket vectors in `hash_cons`.
    /// Tracked incrementally to avoid O(hash_cons.len()) scans (#8600).
    bucket_capacity_bytes: usize,
    /// Cached result of the last `true_memory_bytes()` computation.
    /// Recomputed when `instance_term_bytes` changes by more than
    /// `TRUE_MEMORY_RECOMPUTE_DELTA` since the last cache update.
    /// Uses `Cell` for interior mutability so `instance_memory_exceeded()`
    /// can remain `&self` — callers pass `&TermStore` in read-only contexts
    /// (e.g., DPLL check_sat preflight).
    true_memory_cache: std::cell::Cell<usize>,
    /// `instance_term_bytes` value at last `true_memory_cache` computation.
    true_memory_cache_at: std::cell::Cell<usize>,
    /// `Forall` term IDs marked "E-matching only" (no MBQI/CEGQI synthesis).
    /// A quantifier needing Verus/trigger-only semantics (e.g. the Hilbert-
    /// `choose` witness axiom, which must fire only from an established ground
    /// witness — never be synthesis-instantiated against a transparent
    /// predicate's model) marks its term here; the quantifier loop then excludes
    /// it from MBQI and CEGQI and fails closed to `Unknown`, like a
    /// non-conjunctive-position `forall`. CONSERVATIVE (skipping instantiation
    /// can only lose proofs, never a wrong-UNSAT); stable across push/pop (the
    /// ordinary push/pop is append-only; the isolated speculative rollback
    /// lane prunes this set together with its discarded term suffix).
    no_mbqi: crate::kani_compat::KaniHashSet<TermId>,
    /// Names of Skolem symbols minted by existential Skolemization — both the
    /// Skolem *constants* (`mk_fresh_var("sk!x", ..)`) and the Skolem *function*
    /// symbols (`mk_internal_symbol("sk_x")` → `__ay_sk_x!N`). Registered at the
    /// single creation site (`skolemize_quantifier_body`); names are globally
    /// fresh (uniquified counters), so membership is EXACT provenance: a symbol
    /// is in this set iff it was created by Skolemization. Consumed by the
    /// quantified-CE-lemma de-Skolemizer (`rebuild_quantified_ce_lemma`), which
    /// must recover the pre-Skolemization body exactly or fail closed. The set
    /// is append-only for the TermStore lifetime (push/pop and repeated
    /// `process_quantifiers` runs only ever ADD freshly-named symbols).
    skolem_symbols: crate::kani_compat::KaniHashSet<String>,
    /// TermStore length at the start of the FIRST quantifier-instantiation pass
    /// (`process_quantifiers`), i.e. the count of ORIGINAL problem terms before
    /// any MBQI/CEGQI model-value witness is synthesized. Set ONCE (outside the
    /// isolated speculative rollback lane every later `mk_*` gets a
    /// strictly-greater id), so
    /// `is_synthesized(id)` reliably distinguishes a solve-invented witness
    /// (e.g. `f2(-1,0)` built from an LIA model value) from a genuine
    /// program-level one (e.g. an asserted `f2(7,8)`). Immune to the
    /// generation-bump "re-materialization" problem (a hash-consed id never
    /// changes). Consumed ONLY by the `no_mbqi` (Hilbert-`choose`) E-match guard,
    /// where restricting candidates can only lose proofs, never wrong-UNSAT.
    synthesis_watermark: Option<usize>,
    /// Optional `:qid` (quantifier identifier) attached to a `Forall`/`Exists`
    /// term, keyed by `TermId`. A side-map (mirroring `no_mbqi`) so the metadata
    /// attaches WITHOUT changing the quantifier variant — no touch to the many
    /// `TermData::Forall`/`Exists` match sites. Pure instantiation-hint metadata:
    /// storing/returning it can never change any sat/unsat verdict. Set from the
    /// FFI `Z3_mk_quantifier_ex`/`_const_ex` qid symbol (and the SMT-LIB `:qid`
    /// annotation); read back by `Z3_get_quantifier_id`.
    quantifier_id: KaniHashMap<TermId, String>,
    /// Optional `:skolemid` attached to a `Forall`/`Exists` term, keyed by
    /// `TermId`. Same mechanism/semantics as [`Self::quantifier_id`]; read back
    /// by `Z3_get_quantifier_skolem_id`.
    skolem_id: KaniHashMap<TermId, String>,
    /// Per-store identity for affine speculative rollback checkpoints.
    /// `RollbackIdentity::clone` deliberately mints a fresh identity, so a
    /// checkpoint from a cloned store cannot truncate this store.
    rollback_identity: RollbackIdentity,
    /// Invalidates every older checkpoint after one rollback is consumed.
    rollback_generation: u64,
}

/// Clone behavior for a store's rollback identity: a cloned `TermStore` owns
/// an independent term universe even when its initial contents are identical.
#[derive(Debug)]
struct RollbackIdentity(Arc<()>);

impl RollbackIdentity {
    fn new() -> Self {
        Self(Arc::new(()))
    }
}

impl Clone for RollbackIdentity {
    fn clone(&self) -> Self {
        Self::new()
    }
}

/// Opaque, affine checkpoint for discarding one speculative term suffix.
///
/// Only [`TermStore::rollback_checkpoint`] can construct this value. It is
/// intentionally not `Clone`: rollback consumes it, and the store generation
/// rejects older or out-of-order checkpoints. Callers must still satisfy the
/// semantic contract documented on [`TermStore::rollback_to`] by dropping all
/// external references to terms in the discarded suffix.
#[derive(Debug)]
pub struct TermStoreRollbackCheckpoint {
    identity: Arc<()>,
    generation: u64,
    len: usize,
}

impl Drop for TermStore {
    fn drop(&mut self) {
        // Decrement the global counter by this instance's tracked allocation.
        // Without this, GLOBAL_TERM_BYTES only ever grows — after a portfolio
        // solve where 12 engines each build a TermStore, the counter retains
        // all dead allocations. Across multiple test runs in the same process
        // (or sequential CHC solves), the counter climbs monotonically, causing
        // global_memory_exceeded() to false-trigger and eventually contributing
        // to OOM by preventing engines from exiting cleanly.
        //
        // Use a CAS loop for saturating subtraction: if reset_global_term_bytes()
        // zeroed the counter while a TermStore from the previous solve was still
        // alive (e.g., on a reaper thread), a plain fetch_sub would underflow to
        // usize::MAX and immediately trip global_memory_exceeded().
        let sub = self.instance_term_bytes;
        if sub == 0 {
            return;
        }
        let mut current = GLOBAL_TERM_BYTES.load(Ordering::Relaxed);
        loop {
            let new_val = current.saturating_sub(sub);
            match GLOBAL_TERM_BYTES.compare_exchange_weak(
                current,
                new_val,
                Ordering::Relaxed,
                Ordering::Relaxed,
            ) {
                Ok(_) => break,
                Err(actual) => current = actual,
            }
        }
    }
}

impl Default for TermStore {
    fn default() -> Self {
        Self::new()
    }
}

/// SMT-LIB Euclidean remainder: always non-negative, satisfying 0 <= r < |b|.
///
/// Rust's `%` truncates toward zero, which can give negative remainders.
/// This function adjusts the result to match SMT-LIB semantics where
/// `a = b * (div a b) + (mod a b)` and `(mod a b) >= 0`.
pub(super) fn smt_euclid_rem(a: &BigInt, b: &BigInt) -> BigInt {
    let r = a % b;
    if r.is_negative() {
        r + b.abs()
    } else {
        r
    }
}

impl TermStore {
    /// Create a new empty term store
    pub fn new() -> Self {
        let mut store = Self {
            terms: Vec::new(),
            hash_cons: KaniHashMap::default(),
            not_cache: KaniHashMap::default(),
            var_counter: 0,
            names: KaniHashMap::default(),
            true_term: None,
            false_term: None,
            to_real_shadowed: false,
            is_int_shadowed: false,
            instance_term_bytes: 0,
            heap_data_bytes: 0,
            bucket_capacity_bytes: 0,
            true_memory_cache: std::cell::Cell::new(0),
            true_memory_cache_at: std::cell::Cell::new(0),
            no_mbqi: crate::kani_compat::KaniHashSet::default(),
            skolem_symbols: crate::kani_compat::KaniHashSet::default(),
            synthesis_watermark: None,
            quantifier_id: KaniHashMap::default(),
            skolem_id: KaniHashMap::default(),
            rollback_identity: RollbackIdentity::new(),
            rollback_generation: 0,
        };
        // Pre-create true and false
        store.true_term = Some(store.mk_bool(true));
        store.false_term = Some(store.mk_bool(false));
        store
    }

    /// Kani-only constructor: creates an empty TermStore without pre-creating
    /// true/false terms. Avoids the `mk_bool()` → `hash_cons.insert()` path
    /// that triggers deep BTree symbolic exploration in CBMC (#6612).
    ///
    /// Only suitable for Kani proofs that test pointer/structural properties
    /// without dereferencing term data.
    #[cfg(kani)]
    pub fn new_kani_minimal() -> Self {
        Self {
            terms: Vec::new(),
            hash_cons: KaniHashMap::default(),
            not_cache: KaniHashMap::default(),
            var_counter: 0,
            names: KaniHashMap::default(),
            true_term: None,
            false_term: None,
            to_real_shadowed: false,
            is_int_shadowed: false,
            instance_term_bytes: 0,
            heap_data_bytes: 0,
            bucket_capacity_bytes: 0,
            true_memory_cache: std::cell::Cell::new(0),
            true_memory_cache_at: std::cell::Cell::new(0),
            no_mbqi: crate::kani_compat::KaniHashSet::default(),
            skolem_symbols: crate::kani_compat::KaniHashSet::default(),
            synthesis_watermark: None,
            quantifier_id: KaniHashMap::default(),
            skolem_id: KaniHashMap::default(),
            rollback_identity: RollbackIdentity::new(),
            rollback_generation: 0,
        }
    }

    /// Mark a `Forall` term as "E-matching only" — excluded from MBQI/CEGQI
    /// synthesis instantiation. See the `no_mbqi` field docs. No-op unless `id`
    /// is a `Forall` term.
    pub fn mark_no_mbqi(&mut self, id: TermId) {
        if matches!(self.get(id), TermData::Forall(..)) {
            self.no_mbqi.insert(id);
        }
    }

    /// Whether `id` was marked "E-matching only" via [`Self::mark_no_mbqi`].
    #[must_use]
    pub fn is_no_mbqi(&self, id: TermId) -> bool {
        self.no_mbqi.contains(&id)
    }

    /// Attach a `:qid` (quantifier identifier) to a `Forall`/`Exists` term.
    /// No-op unless `id` is a quantifier term (metadata only — never affects the
    /// asserted formula's semantics). See the `quantifier_id` field docs.
    pub fn set_quantifier_id(&mut self, id: TermId, qid: String) {
        if matches!(self.get(id), TermData::Forall(..) | TermData::Exists(..)) {
            self.quantifier_id.insert(id, qid);
        }
    }

    /// The `:qid` attached to `id` via [`Self::set_quantifier_id`], if any.
    #[must_use]
    pub fn quantifier_id(&self, id: TermId) -> Option<&str> {
        self.quantifier_id.get(&id).map(String::as_str)
    }

    /// Attach a `:skolemid` to a `Forall`/`Exists` term. No-op unless `id` is a
    /// quantifier term (metadata only). See the `skolem_id` field docs.
    pub fn set_skolem_id(&mut self, id: TermId, skid: String) {
        if matches!(self.get(id), TermData::Forall(..) | TermData::Exists(..)) {
            self.skolem_id.insert(id, skid);
        }
    }

    /// The `:skolemid` attached to `id` via [`Self::set_skolem_id`], if any.
    #[must_use]
    pub fn skolem_id(&self, id: TermId) -> Option<&str> {
        self.skolem_id.get(&id).map(String::as_str)
    }

    /// Register a Skolemization-minted symbol name (constant or function). See
    /// the `skolem_symbols` field docs: call ONLY from the Skolem creation site
    /// so membership remains exact provenance.
    pub fn mark_skolem_symbol(&mut self, name: impl Into<String>) {
        self.skolem_symbols.insert(name.into());
    }

    /// Whether `name` was minted by Skolemization ([`Self::mark_skolem_symbol`]).
    #[must_use]
    pub fn is_skolem_symbol(&self, name: &str) -> bool {
        self.skolem_symbols.contains(name)
    }

    /// Whether `name` is already interned as a variable/declared-constant in the
    /// name table (i.e. [`Self::mk_var`] with this name would return an EXISTING
    /// node rather than mint a fresh one).
    ///
    /// Read-only. Used by fresh-symbol minting (e.g. the `reduce-args` tactic's
    /// per-constant specialization names `f!k`) to advance past any name that
    /// would otherwise alias a user-declared symbol — including a declared but
    /// otherwise unused constant that never appears in the goal DAG.
    #[must_use]
    pub fn has_var_name(&self, name: &str) -> bool {
        self.names.contains_key(name)
    }

    /// Record the current term count as the ORIGINAL-problem watermark, ONCE.
    /// Idempotent: a second call is a no-op, so it is safe to call at the top of
    /// every quantifier-instantiation pass — the FIRST call (before any MBQI/CEGQI
    /// model-value synthesis) fixes the boundary. See the `synthesis_watermark`
    /// field docs.
    pub fn set_synthesis_watermark(&mut self) {
        if self.synthesis_watermark.is_none() {
            self.synthesis_watermark = Some(self.terms.len());
        }
    }

    /// Whether `id` was created AFTER the synthesis watermark, i.e. is a
    /// solve-invented term rather than an original problem term. Returns `false`
    /// (fail-OPEN) until the watermark is set, so it never changes behavior
    /// outside the quantifier path. See the `synthesis_watermark` field docs.
    #[must_use]
    pub fn is_synthesized(&self, id: TermId) -> bool {
        self.synthesis_watermark
            .is_some_and(|w| (id.0 as usize) >= w)
    }

    /// Get the number of terms in the store
    pub fn len(&self) -> usize {
        self.terms.len()
    }

    /// Check if the store is empty
    pub fn is_empty(&self) -> bool {
        self.terms.is_empty()
    }

    /// Capture the current suffix boundary for one later speculative rollback.
    ///
    /// The returned checkpoint is bound to this exact store instance and its
    /// current rollback generation. It cannot be constructed or cloned by a
    /// caller.
    #[must_use]
    pub fn rollback_checkpoint(&self) -> TermStoreRollbackCheckpoint {
        TermStoreRollbackCheckpoint {
            identity: Arc::clone(&self.rollback_identity.0),
            generation: self.rollback_generation,
            len: self.terms.len(),
        }
    }

    /// Roll the store back to `checkpoint`, discarding every term created
    /// since it was captured (#dt-lazy-isolation).
    ///
    /// CONTRACT: the caller must guarantee that NO `TermId >= checkpoint.len` is
    /// retained anywhere — not in assertions, models, caches, proof
    /// trackers, or theory state. The intended use is a speculative solver
    /// lane that materialized scratch terms and then fully unwound (the lazy
    /// DT lane's fallback): after restoring its entry snapshots, the store
    /// itself is the last place the lane's scratch material survives, and a
    /// later lane's whole-store scans must not observe it.
    ///
    /// The memory counters (`instance_term_bytes`, `heap_data_bytes`) are
    /// deliberately NOT decremented: they feed budget checks (conservative
    /// overcount is safe) and the `Drop` decrement of the global counter,
    /// which must mirror everything this instance ever added.
    ///
    /// Panics before mutation if the checkpoint belongs to another (including
    /// cloned) store, is stale/out of order, predates the preallocated Boolean
    /// floor, or lies beyond the current store. These checks turn public API
    /// misuse into a fail-fast error instead of silent TermId aliasing.
    pub fn rollback_to(&mut self, checkpoint: TermStoreRollbackCheckpoint) {
        assert!(
            Arc::ptr_eq(&self.rollback_identity.0, &checkpoint.identity),
            "term rollback checkpoint belongs to a different store"
        );
        assert_eq!(
            checkpoint.generation, self.rollback_generation,
            "term rollback checkpoint is stale or out of order"
        );
        let boolean_floor = match (self.true_term, self.false_term) {
            (Some(true_term), Some(false_term)) => {
                true_term.index().max(false_term.index()).saturating_add(1)
            }
            (None, None) => 0,
            _ => panic!("term store has a partial preallocated Boolean floor"),
        };
        assert!(
            checkpoint.len >= boolean_floor,
            "term rollback checkpoint predates the preallocated Boolean floor"
        );
        assert!(
            checkpoint.len <= self.terms.len(),
            "term rollback checkpoint lies beyond the current store"
        );
        self.rollback_generation = self
            .rollback_generation
            .checked_add(1)
            .expect("term rollback generation exhausted");
        let len = checkpoint.len;
        let keep = |id: &TermId| (id.0 as usize) < len;
        self.terms.truncate(len);
        for bucket in self.hash_cons.values_mut() {
            bucket.retain(|id| keep(id));
        }
        self.hash_cons.retain(|_, bucket| !bucket.is_empty());
        self.not_cache.retain(|k, v| keep(k) && keep(v));
        self.names.retain(|_, (id, _)| keep(id));
        self.no_mbqi.retain(keep);
        self.quantifier_id.retain(|k, _| keep(k));
        self.skolem_id.retain(|k, _| keep(k));
        if self.synthesis_watermark.is_some_and(|w| w > len) {
            self.synthesis_watermark = Some(len);
        }
    }

    /// Iterator over all TermIds in this store.
    pub fn term_ids(&self) -> impl Iterator<Item = TermId> {
        (0..self.terms.len() as u32).map(TermId)
    }

    /// Check if the process-wide RSS limit has been exceeded, or if the global
    /// TermStore allocation counter exceeds the configured term-memory limit.
    ///
    /// With the default `DEFAULT_TERM_MEMORY_LIMIT = usize::MAX`, the term-byte
    /// comparison is always false. The effective memory guard is
    /// `ay_sys::process_memory_exceeded()`, which checks RSS against the
    /// caller-set process memory limit (CLI `-memory:<MB>` / `AY_MEMORY_LIMIT`).
    ///
    /// The check uses `Relaxed` ordering — the exact byte count doesn't need to be
    /// precise, we just need to detect when we're in the danger zone.
    pub fn global_memory_exceeded() -> bool {
        GLOBAL_TERM_BYTES.load(Ordering::Relaxed) > GLOBAL_TERM_MEMORY_LIMIT.load(Ordering::Relaxed)
            || ay_sys::process_memory_exceeded()
    }

    /// Get the current global term memory usage in bytes (approximate).
    pub fn global_term_bytes() -> usize {
        GLOBAL_TERM_BYTES.load(Ordering::Relaxed)
    }

    /// Reset the global term memory counter.
    ///
    /// Call this at the start of a new portfolio solve to avoid accumulating
    /// counts from previous solves. Safe to call from any thread — the counter
    /// is atomic.
    pub fn reset_global_term_bytes() {
        GLOBAL_TERM_BYTES.store(0, Ordering::Relaxed);
    }

    /// Set the number of active portfolio engines for per-engine budgeting.
    ///
    /// Call this from the portfolio coordinator before spawning engines.
    /// The per-engine budget is `global_term_memory_limit / max(1, count)`.
    /// Defaults to 1 if never called (single-engine mode).
    pub fn set_engine_count(count: usize) {
        GLOBAL_ENGINE_COUNT.store(count.max(1), Ordering::Relaxed);
    }

    /// Get the per-engine memory budget in bytes.
    ///
    /// Returns `global_term_memory_limit / engine_count`. Each engine should
    /// check `instance_memory_exceeded(per_engine_budget())` to ensure no
    /// single engine hogs the entire global allocation.
    pub fn per_engine_budget() -> usize {
        let count = GLOBAL_ENGINE_COUNT.load(Ordering::Relaxed).max(1);
        GLOBAL_TERM_MEMORY_LIMIT.load(Ordering::Relaxed) / count
    }

    /// Configure the global TermStore allocation limit.
    ///
    /// This controls the TermStore allocation guard used by
    /// `global_memory_exceeded()` and `per_engine_budget()`. The default remains
    /// `DEFAULT_TERM_MEMORY_LIMIT`, which is unlimited (`usize::MAX`).
    pub fn set_global_term_memory_limit(bytes: usize) {
        GLOBAL_TERM_MEMORY_LIMIT.store(bytes, Ordering::Relaxed);
    }

    /// Test-only helper to restore the default global TermStore allocation limit.
    #[doc(hidden)]
    pub fn reset_global_term_memory_limit_for_testing() {
        GLOBAL_TERM_MEMORY_LIMIT.store(DEFAULT_TERM_MEMORY_LIMIT, Ordering::Relaxed);
    }

    /// Test-only helper to force the global term-byte counter.
    ///
    /// This is used by CHC regression tests to exercise memory-budget exit paths
    /// without allocating gigabytes of terms.
    #[doc(hidden)]
    pub fn force_global_term_bytes_for_testing(bytes: usize) {
        GLOBAL_TERM_BYTES.store(bytes, Ordering::Relaxed);
    }

    /// Test-only helper to force `global_memory_exceeded()` to return true.
    ///
    /// Sets the process-level RSS limit to 1 byte so that
    /// `ay_sys::process_memory_exceeded()` fires. Call
    /// `reset_process_memory_limit_for_testing()` to undo.
    #[doc(hidden)]
    pub fn force_process_memory_exceeded_for_testing() {
        // Thread-local force (not the process-global RSS limit) so a test running
        // in parallel with others cannot make their concurrent solves abort.
        ay_sys::force_process_memory_exceeded_for_testing(true);
    }

    /// Test-only helper to reset the process-level RSS limit (undo force).
    #[doc(hidden)]
    pub fn reset_process_memory_limit_for_testing() {
        ay_sys::force_process_memory_exceeded_for_testing(false);
        ay_sys::set_process_memory_limit(0);
    }

    /// Per-instance term memory usage in bytes (approximate).
    ///
    /// Unlike `global_term_bytes()`, this counts only terms interned by THIS
    /// `TermStore` instance. Use this for per-solver memory budgets that must
    /// not interfere with other concurrent solver instances (#6563).
    pub fn instance_term_bytes(&self) -> usize {
        self.instance_term_bytes
    }

    /// Accurate memory footprint of THIS `TermStore` instance (bytes).
    ///
    /// Unlike `instance_term_bytes()`, which incrementally tracks per-element
    /// allocations and can undercount by up to 2x (missing Vec spare capacity,
    /// HashMap table overhead, and BTreeMap node overhead), this method
    /// queries actual container capacities to compute a more precise estimate.
    ///
    /// Components:
    /// 1. `terms` Vec: `capacity * size_of::<TermEntry>()` (includes spare slots)
    /// 2. `hash_cons` map table: `allocation_size()` on hashbrown, or estimated
    ///    node overhead on BTreeMap (Kani mode)
    /// 3. `hash_cons` bucket Vecs: sum of `capacity * size_of::<TermId>()`
    /// 4. `names` map table: `allocation_size()` or BTreeMap node estimate
    /// 5. `heap_data_bytes`: accumulated TermData heap (String, Vec, BigInt)
    ///    plus names HashMap string key heap — tracked incrementally since
    ///    querying individual term heap sizes would require a full scan.
    ///
    /// This is O(hash_cons.len()) due to the bucket capacity scan, so use it
    /// for periodic budget checks (e.g., once per conflict) rather than on
    /// every propagation.
    pub fn true_memory_bytes(&self) -> usize {
        use std::mem::size_of;

        // 1. terms Vec heap allocation
        let terms_heap = self.terms.capacity() * size_of::<TermEntry>();

        // 2. hash_cons map table overhead
        #[cfg(not(kani))]
        let hash_cons_table = self.hash_cons.allocation_size();
        #[cfg(kani)]
        let hash_cons_table = {
            // BTreeMap: estimate ~64 bytes per node (key + value + 2 pointers + metadata)
            self.hash_cons.len() * 64
        };

        // 3. hash_cons bucket Vec heap: each bucket is a Vec<TermId>
        let hash_cons_buckets = self.bucket_capacity_bytes;

        // 4. names map table overhead
        #[cfg(not(kani))]
        let names_table = self.names.allocation_size();
        #[cfg(kani)]
        let names_table = self.names.len() * 64;

        // 5. heap_data_bytes: accumulated TermData heap + names key strings
        terms_heap + hash_cons_table + hash_cons_buckets + names_table + self.heap_data_bytes
    }

    /// Check if THIS instance has exceeded a given memory budget.
    ///
    /// Uses a cached `true_memory_bytes()` for accurate capacity-based
    /// accounting (#8600). The cache is refreshed when `instance_term_bytes`
    /// grows by more than `TRUE_MEMORY_RECOMPUTE_DELTA` (64 KiB) since the
    /// last computation, balancing accuracy against the O(hash_cons.len())
    /// scan cost in the DPLL(T) hot loop.
    ///
    /// The previous implementation used `instance_term_bytes` directly,
    /// which undercounted by missing Vec spare capacity and HashMap table
    /// overhead, allowing actual RSS to reach 2-3x the reported value
    /// before the limit triggered.
    pub fn instance_memory_exceeded(&self, limit: usize) -> bool {
        let cached_at = self.true_memory_cache_at.get();
        let delta = self.instance_term_bytes.saturating_sub(cached_at);
        if delta >= TRUE_MEMORY_RECOMPUTE_DELTA || self.true_memory_cache.get() == 0 {
            let fresh = self.true_memory_bytes();
            self.true_memory_cache.set(fresh);
            self.true_memory_cache_at.set(self.instance_term_bytes);
            fresh > limit
        } else {
            self.true_memory_cache.get() > limit
        }
    }

    /// Get the TermId for true
    pub fn true_term(&self) -> TermId {
        self.true_term
            .expect("TermStore: true_term accessed before initialization")
    }

    /// Get the TermId for false
    pub fn false_term(&self) -> TermId {
        self.false_term
            .expect("TermStore: false_term accessed before initialization")
    }

    /// Record that a USER declaration shadows the builtin `to_real` symbol
    /// (declarable as a `(_ map f)` target). Disables the to_real-integrality
    /// rewrites in comparison/equality constructors — rewriting a user's
    /// uninterpreted `to_real` would fabricate semantics for a free function.
    /// Sticky (never cleared, even on pop): conservative, fail-closed.
    /// (#to-real-bridge)
    pub fn mark_to_real_shadowed(&mut self) {
        self.to_real_shadowed = true;
    }

    /// Whether the builtin `to_real` has been shadowed by a user declaration.
    pub fn to_real_is_shadowed(&self) -> bool {
        self.to_real_shadowed
    }

    /// Record that a USER declaration shadows the builtin `is_int` symbol
    /// (declarable as a `(_ map f)` target). Makes the `is_int` quantifier
    /// eliminator stand down — applying integrality (critical-residue)
    /// reasoning to a user's uninterpreted `is_int` would fabricate semantics
    /// for a free predicate (a confirmed wrong-UNSAT class). Sticky (never
    /// cleared, even on pop): conservative, fail-closed. (#isint-shadow)
    pub fn mark_is_int_shadowed(&mut self) {
        self.is_int_shadowed = true;
    }

    /// Whether the builtin `is_int` has been shadowed by a user declaration.
    pub fn is_int_is_shadowed(&self) -> bool {
        self.is_int_shadowed
    }

    /// Get the term data for a TermId
    pub fn get(&self, id: TermId) -> &TermData {
        &self.terms[id.index()].term
    }

    /// Get the sort of a term
    pub fn sort(&self, id: TermId) -> &Sort {
        &self.terms[id.index()].sort
    }

    /// The current variable counter (number of unique variable ids minted).
    #[must_use]
    pub fn var_counter(&self) -> u32 {
        self.var_counter
    }

    /// Snapshot every interned term as an ordered `(TermData, Sort)` list where
    /// position `i` corresponds to `TermId(i)`. This is the checker-only payload
    /// needed to re-validate a proof offline: [`check_proof_strict`] reads terms
    /// purely by index (`get`/`sort`) and never re-interns, so the hash-cons map,
    /// the name table, and the byte counters need not round-trip.
    #[must_use]
    pub fn entries_snapshot(&self) -> Vec<(TermData, Sort)> {
        self.terms
            .iter()
            .map(|e| (e.term.clone(), e.sort.clone()))
            .collect()
    }

    /// Rebuild a CHECKER-ONLY term store from a positional `(TermData, Sort)`
    /// snapshot (see [`entries_snapshot`]). `TermId(i)` resolves to `entries[i]`,
    /// preserving every id embedded in a serialized proof. The hash-cons interner
    /// and the name table are left EMPTY: this store supports `get`/`sort`/
    /// `true_term`/`false_term` — everything [`check_proof_strict`] needs — but
    /// MUST NOT mint or look up terms (`mk_*`/`find_interned` would
    /// mis-deduplicate against the empty interner). `instance_term_bytes` is left
    /// at 0 so the `Drop` global-accounting path is a no-op for this transient
    /// store.
    #[must_use]
    pub fn from_entries(
        entries: Vec<(TermData, Sort)>,
        true_term: Option<TermId>,
        false_term: Option<TermId>,
        var_counter: u32,
    ) -> Self {
        let terms = entries
            .into_iter()
            .map(|(term, sort)| TermEntry { term, sort })
            .collect();
        Self {
            terms,
            hash_cons: KaniHashMap::default(),
            var_counter,
            names: KaniHashMap::default(),
            true_term,
            false_term,
            to_real_shadowed: false,
            is_int_shadowed: false,
            instance_term_bytes: 0,
            heap_data_bytes: 0,
            bucket_capacity_bytes: 0,
            true_memory_cache: std::cell::Cell::new(0),
            true_memory_cache_at: std::cell::Cell::new(0),
            // Empty: this checker-only store never interns, so the not-memo cache
            // stays empty (the strict checker only reads terms by index).
            not_cache: KaniHashMap::default(),
            no_mbqi: crate::kani_compat::KaniHashSet::default(),
            skolem_symbols: crate::kani_compat::KaniHashSet::default(),
            synthesis_watermark: None,
            quantifier_id: KaniHashMap::default(),
            skolem_id: KaniHashMap::default(),
            rollback_identity: RollbackIdentity::new(),
            rollback_generation: 0,
        }
    }

    /// Compute hash for term data
    pub(super) fn compute_hash(term: &TermData) -> u64 {
        foldhash::fast::FixedState::default().hash_one(term)
    }

    /// Look up an existing term without creating a new interned entry.
    pub fn find_interned(&self, term: &TermData) -> Option<TermId> {
        let hash = Self::compute_hash(term);
        let ids = self.hash_cons.get(&hash)?;
        ids.iter()
            .copied()
            .find(|&id| &self.terms[id.index()].term == term)
    }

    /// Look up an existing function application `App(sym, args)` without
    /// creating a new interned entry. Returns `Some(id)` if the exact term
    /// exists in the store, `None` otherwise.
    pub fn find_app(&self, sym: &Symbol, args: &[TermId]) -> Option<TermId> {
        let hash = self.compute_app_hash(sym, args);
        let ids = self.hash_cons.get(&hash)?;
        ids.iter().copied().find(|&id| {
            if let TermData::App(s, a) = self.get(id) {
                s == sym && a == args
            } else {
                false
            }
        })
    }

    /// Look up an existing function application `App(Symbol::Named(name), args)`
    /// without creating a new interned entry or allocating a `Symbol`.
    pub fn find_app_named(&self, name: &str, args: &[TermId]) -> Option<TermId> {
        let hash = self.compute_app_hash_named(name, args);
        let ids = self.hash_cons.get(&hash)?;
        ids.iter().copied().find(|&id| {
            if let TermData::App(Symbol::Named(s), a) = self.get(id) {
                s == name && a == args
            } else {
                false
            }
        })
    }

    fn compute_app_hash(&self, sym: &Symbol, args: &[TermId]) -> u64 {
        let mut state = foldhash::fast::FixedState::default().build_hasher();
        std::mem::discriminant(&TermData::App(Symbol::named(""), vec![])).hash(&mut state);
        sym.hash(&mut state);
        args.hash(&mut state);
        state.finish()
    }

    fn compute_app_hash_named(&self, name: &str, args: &[TermId]) -> u64 {
        let mut state = foldhash::fast::FixedState::default().build_hasher();
        std::mem::discriminant(&TermData::App(Symbol::named(""), vec![])).hash(&mut state);
        std::mem::discriminant(&Symbol::Named(String::new())).hash(&mut state);
        name.hash(&mut state);
        args.hash(&mut state);
        state.finish()
    }

    /// Look up an existing universal quantifier.
    pub fn find_forall(
        &self,
        vars: &[(String, Sort)],
        body: TermId,
        triggers: &[Vec<TermId>],
    ) -> Option<TermId> {
        let hash = self.compute_quantifier_hash(true, vars, body, triggers);
        let ids = self.hash_cons.get(&hash)?;
        ids.iter().copied().find(|&id| {
            if let TermData::Forall(v, b, t) = self.get(id) {
                v == vars && *b == body && t == triggers
            } else {
                false
            }
        })
    }

    /// Look up an existing existential quantifier.
    pub fn find_exists(
        &self,
        vars: &[(String, Sort)],
        body: TermId,
        triggers: &[Vec<TermId>],
    ) -> Option<TermId> {
        let hash = self.compute_quantifier_hash(false, vars, body, triggers);
        let ids = self.hash_cons.get(&hash)?;
        ids.iter().copied().find(|&id| {
            if let TermData::Exists(v, b, t) = self.get(id) {
                v == vars && *b == body && t == triggers
            } else {
                false
            }
        })
    }

    fn compute_quantifier_hash(
        &self,
        is_forall: bool,
        vars: &[(String, Sort)],
        body: TermId,
        triggers: &[Vec<TermId>],
    ) -> u64 {
        let mut state = foldhash::fast::FixedState::default().build_hasher();
        if is_forall {
            std::mem::discriminant(&TermData::Forall(vec![], body, vec![])).hash(&mut state);
        } else {
            std::mem::discriminant(&TermData::Exists(vec![], body, vec![])).hash(&mut state);
        }
        for (name, sort) in vars {
            name.hash(&mut state);
            sort.hash(&mut state);
        }
        body.hash(&mut state);
        triggers.hash(&mut state);
        state.finish()
    }

    /// Look up an existing let binding.
    pub fn find_let(&self, bindings: &[(String, TermId)], body: TermId) -> Option<TermId> {
        let hash = self.compute_let_hash(bindings, body);
        let ids = self.hash_cons.get(&hash)?;
        ids.iter().copied().find(|&id| {
            if let TermData::Let(b, bd) = self.get(id) {
                b == bindings && *bd == body
            } else {
                false
            }
        })
    }

    fn compute_let_hash(&self, bindings: &[(String, TermId)], body: TermId) -> u64 {
        let mut state = foldhash::fast::FixedState::default().build_hasher();
        std::mem::discriminant(&TermData::Let(vec![], body)).hash(&mut state);
        bindings.hash(&mut state);
        body.hash(&mut state);
        state.finish()
    }

    /// Look up an existing equality term without triggering `mk_eq`
    /// simplification or allocating a fresh node.
    pub fn find_eq(&self, lhs: TermId, rhs: TermId) -> Option<TermId> {
        if lhs == rhs {
            return Some(
                self.true_term
                    .expect("TermStore: true_term accessed before initialization"),
            );
        }
        let args = if lhs < rhs { [lhs, rhs] } else { [rhs, lhs] };
        self.find_app_named("=", &args)
    }
}
