// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Term representation for AY
//!
//! Terms are represented as a hash-consed DAG for efficient sharing.
//! The `TermStore` manages term creation and ensures structural sharing
//! through hash-consing.

use crate::kani_compat::{KaniHashMap, KaniHashSet};
use crate::sort::Sort;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, ToPrimitive, Zero};
use std::fmt;
use std::hash::{BuildHasher, Hash, Hasher};
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
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
mod memory;
mod preprocess;
mod subst;
mod value;

pub use compact::{RemapTable, Remappable};
pub use value::{Constant, RationalWrapper, SkolemChoice, Symbol, TermData, TermId};
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

/// Process-wide source of non-reused term-entry identities.
///
/// A `TermId` is only a slot index and speculative rollback can later reuse a
/// discarded suffix slot.  Native API handles therefore authenticate both the
/// slot and this birth stamp.  Keeping the source outside `TermStore` is
/// deliberate: cloning and later restoring a speculative store snapshot cannot
/// rewind it and accidentally resurrect a stale handle.
static NEXT_TERM_ENTRY_STAMP: AtomicU64 = AtomicU64::new(1);

/// Opaque birth identity of one exact entry in a [`TermStore`].
///
/// The stamp is copied when a store is cloned, so prefix entries retain their
/// logical identity across an exact rollback snapshot. Freshly interned entries
/// always receive a process-wide non-reused stamp, including when their numeric
/// [`TermId`] slot was previously occupied by a discarded speculative term.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TermEntryStamp(u64);

#[allow(clippy::panic, deprecated)]
fn fresh_term_entry_stamp() -> TermEntryStamp {
    // `fetch_update`, not `try_update`: identical semantics (the closure-CAS
    // loop returning the previous value), but stable since 1.45 — `try_update`
    // is its unstable rename (#135894) and holds every downstream consumer
    // (model-checker-consumer pins nightly-2025-12-03, which lacks it) to a newer toolchain
    // for no behavioral gain.
    let stamp = NEXT_TERM_ENTRY_STAMP
        .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |current| {
            current.checked_add(1)
        })
        .unwrap_or_else(|_| panic!("term entry identity space exhausted"));
    TermEntryStamp(stamp)
}

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

/// Cap on `TermStore::strict_bv_semantics_ok`. Past it the store stops
/// memoizing completed strict BV validations and the checker re-runs them, so
/// the bound costs time, never correctness.
const MAX_STRICT_BV_SEMANTICS_MEMO: usize = 4096;

/// Internal term representation with pre-computed hash
#[derive(Debug, Clone)]
struct TermEntry {
    term: TermData,
    sort: Sort,
    stamp: TermEntryStamp,
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
    /// Monotone modification counter over the CHECKER-VISIBLE metadata
    /// families of this store — the TermStore state the strict proof checker
    /// (`ay-proof`) reads BESIDES the immutable term entries/sorts: the
    /// `to_real_shadowed` and `is_int_shadowed` latches and the
    /// `skolem_symbols` / `skolem_choice` registries. Those families mutate
    /// through their registration mutators WITHOUT appending a term or
    /// advancing the structural generation, so [`Self::snapshot_stamp`]
    /// equality alone does NOT prove them unchanged; any consumer replaying
    /// checker-derived conclusions (the strict-walk memo,
    /// `ay-dpll` #strict-walk-memo) must additionally compare
    /// [`Self::checker_visible_metadata_generation`].
    ///
    /// CONTRACT (kept by construction, pinned by the memo's adversarial
    /// tests): every mutation of these four families either bumps this
    /// counter ([`Self::mark_to_real_shadowed`],
    /// [`Self::mark_is_int_shadowed`], [`Self::mark_skolem_symbol`],
    /// [`Self::register_skolem_choice`] — including a `skolem_choice`
    /// OVERWRITE, which changes the table at unchanged size) or retires the
    /// snapshot stamp ([`Self::rollback_to`] pruning, `mark_and_compact`
    /// remapping — both advance the structural generation — and `Clone`,
    /// which mints a fresh identity). Bumps happen only on an ACTUAL state
    /// change, so a re-record of an identical value costs no consumer a
    /// false invalidation; the counter never decreases.
    /// (#checker-visible-metadata-generation)
    checker_visible_metadata_generation: u64,
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
    no_mbqi: KaniHashSet<TermId>,
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
    skolem_symbols: KaniHashSet<String>,
    /// Hilbert-choice provenance of a Skolem CONSTANT, keyed by its witness
    /// `TermId`. See [`SkolemChoice`]. Recorded at the single creation site
    /// (`skolemize_quantifier_body`) so the value is what the substitution
    /// actually used, not a name-derived reconstruction. Consumed ONLY by the
    /// Alethe printer, which DEFINES `sk!x` as the `choice` term it denotes.
    /// A `(declare-fun ...)` is not an option: an Alethe proof document admits
    /// no declaration command at all, so a witness with no entry here makes the
    /// exporter DECLINE. Never read by the solver, so a missing or stale entry
    /// can only cost a printable proof, never change a verdict.
    skolem_choice: KaniHashMap<TermId, SkolemChoice>,
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
    /// SMT-LIB/Z3 quantifier priority (`:weight`), keyed by quantifier term.
    /// Missing entries have Z3's parser default weight `1`. The E-matching cost
    /// gate consumes this value as `weight + generation`; keeping it in a side
    /// map preserves the existing public `TermData` shape while making the
    /// annotation operational instead of silently discarding it.
    quantifier_weight: KaniHashMap<TermId, u32>,
    /// Negative auto-trigger candidates from SMT-LIB `:no-pattern`
    /// annotations, keyed by quantifier term. These are heuristic metadata (not
    /// logical children) and are filtered only from automatic pattern
    /// inference, matching Z3's `pattern_inference_cfg::add_candidate` rule.
    quantifier_no_patterns: KaniHashMap<TermId, Vec<TermId>>,
    /// Per-store identity for affine speculative rollback checkpoints.
    /// `RollbackIdentity::clone` deliberately mints a fresh identity, so a
    /// checkpoint from a cloned store cannot truncate this store.
    rollback_identity: RollbackIdentity,
    /// Invalidates every older checkpoint and structural snapshot after a
    /// rollback or compaction can make a previously used length alias a new
    /// term universe.
    rollback_generation: u64,
    /// Clauses whose strict `bv_bitblast` SEMANTIC decision procedure has
    /// already run to completion — and PASSED — against this store.
    ///
    /// A memo of work already done, never a substitute for it. An entry is
    /// written only by the strict checker, only after the full decision
    /// procedure (exhaustive bounded evaluation, or the bounded bit-blast +
    /// LRAT proof producer and its replay) ACCEPTED that exact clause, and it
    /// is read only to skip repeating that identical decision. Failures are
    /// deliberately never recorded: the proof-producing checker is
    /// deadline-bounded, so a failure is a fact about one attempt, not about
    /// the clause.
    ///
    /// Keyed by `TermId`, hence cleared by every operation that can change what
    /// a `TermId` means — `rollback_to` and `mark_and_compact` are the only two
    /// (every other mutation of `self.terms` appends), and both clear it.
    /// `Clone` and `from_entries` start empty.
    strict_bv_semantics_ok: std::cell::RefCell<KaniHashSet<Vec<TermId>>>,
}

impl Clone for TermStore {
    fn clone(&self) -> Self {
        let cloned = Self {
            terms: self.terms.clone(),
            hash_cons: self.hash_cons.clone(),
            not_cache: self.not_cache.clone(),
            var_counter: self.var_counter,
            names: self.names.clone(),
            true_term: self.true_term,
            false_term: self.false_term,
            to_real_shadowed: self.to_real_shadowed,
            is_int_shadowed: self.is_int_shadowed,
            checker_visible_metadata_generation: self.checker_visible_metadata_generation,
            // These are conservative allocation ledgers, not a fresh capacity
            // census. A cloned Vec/HashMap may reserve less than its source,
            // so copying can overcount, but never undercounts the source's
            // tracked history and remains exactly balanced with this clone's
            // later Drop.
            instance_term_bytes: self.instance_term_bytes,
            heap_data_bytes: self.heap_data_bytes,
            bucket_capacity_bytes: self.bucket_capacity_bytes,
            // Container clones are free to choose different capacities, so the
            // source store's capacity-based cache is not valid for this copy.
            true_memory_cache: std::cell::Cell::new(0),
            true_memory_cache_at: std::cell::Cell::new(0),
            no_mbqi: self.no_mbqi.clone(),
            skolem_symbols: self.skolem_symbols.clone(),
            skolem_choice: self.skolem_choice.clone(),
            synthesis_watermark: self.synthesis_watermark,
            quantifier_id: self.quantifier_id.clone(),
            skolem_id: self.skolem_id.clone(),
            quantifier_weight: self.quantifier_weight.clone(),
            quantifier_no_patterns: self.quantifier_no_patterns.clone(),
            rollback_identity: self.rollback_identity.clone(),
            rollback_generation: self.rollback_generation,
            // A memo of completed checker work, not store content. Starting a
            // clone empty is always correct: it only costs a re-validation.
            strict_bv_semantics_ok: std::cell::RefCell::new(KaniHashSet::default()),
        };

        // A cloned store owns a second physical allocation and its Drop
        // subtracts this exact per-instance counter. Credit the process-wide
        // aggregate only after every field clone succeeded, keeping clone/drop
        // accounting balanced even if an allocation above panics.
        GLOBAL_TERM_BYTES.fetch_add(cloned.instance_term_bytes, Ordering::Relaxed);
        cloned
    }
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

/// Opaque identity of one exact structural [`TermStore`] snapshot.
///
/// This is intended for read-only derived indexes.  It compares equal only
/// while the same physical store has the same structural generation and
/// length: cloning/replacing a store mints a fresh identity, appending changes
/// the length, and rollback or compaction advances the generation. Existing
/// term entries are immutable, so equality is sufficient evidence that a
/// structural index over `0..len` still describes this store exactly.
#[derive(Clone)]
pub struct TermStoreSnapshotStamp {
    identity: Arc<()>,
    generation: u64,
    len: usize,
}

impl PartialEq for TermStoreSnapshotStamp {
    fn eq(&self, other: &Self) -> bool {
        self.generation == other.generation
            && self.len == other.len
            && Arc::ptr_eq(&self.identity, &other.identity)
    }
}

impl Eq for TermStoreSnapshotStamp {}

impl TermStoreSnapshotStamp {
    /// Whether this snapshot remains an immutable prefix of `store` after only
    /// append-only growth.
    ///
    /// Unlike equality, this deliberately permits `store` to contain terms
    /// appended after the snapshot. It still requires the same physical term
    /// universe and structural generation, so cloning/replacing the store,
    /// rolling back any suffix, or compacting it retires the stamp. Since term
    /// entries are immutable, those conditions plus `store.len() >= self.len`
    /// guarantee that every `TermId` below the captured boundary still names
    /// the same entry.
    #[must_use]
    pub fn is_append_only_prefix_of(&self, store: &TermStore) -> bool {
        self.generation == store.rollback_generation
            && self.len <= store.terms.len()
            && Arc::ptr_eq(&self.identity, &store.rollback_identity.0)
    }
}

impl fmt::Debug for TermStoreSnapshotStamp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TermStoreSnapshotStamp")
            .field("identity", &"<opaque>")
            .field("generation", &self.generation)
            .field("len", &self.len)
            .finish()
    }
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
            checker_visible_metadata_generation: 0,
            instance_term_bytes: 0,
            heap_data_bytes: 0,
            bucket_capacity_bytes: 0,
            true_memory_cache: std::cell::Cell::new(0),
            true_memory_cache_at: std::cell::Cell::new(0),
            no_mbqi: KaniHashSet::default(),
            skolem_symbols: KaniHashSet::default(),
            skolem_choice: KaniHashMap::default(),
            synthesis_watermark: None,
            quantifier_id: KaniHashMap::default(),
            skolem_id: KaniHashMap::default(),
            quantifier_weight: KaniHashMap::default(),
            quantifier_no_patterns: KaniHashMap::default(),
            rollback_identity: RollbackIdentity::new(),
            rollback_generation: 0,
            strict_bv_semantics_ok: std::cell::RefCell::new(KaniHashSet::default()),
        };
        // Pre-create true and false
        store.true_term = Some(store.mk_bool(true));
        let false_term = store.mk_bool(false);
        // `PREALLOCATED_FALSE` lets store-free callers (proof-shape recognizers
        // that receive only a `Proof`) name the `false` constant. Check the
        // alignment here — once per store, one integer compare — so the constant
        // cannot silently drift from the constructor that establishes it.
        assert_eq!(
            false_term,
            Self::PREALLOCATED_FALSE,
            "TermStore::new must intern `false` at its documented position"
        );
        store.false_term = Some(false_term);
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
            checker_visible_metadata_generation: 0,
            instance_term_bytes: 0,
            heap_data_bytes: 0,
            bucket_capacity_bytes: 0,
            true_memory_cache: std::cell::Cell::new(0),
            true_memory_cache_at: std::cell::Cell::new(0),
            no_mbqi: KaniHashSet::default(),
            skolem_symbols: KaniHashSet::default(),
            skolem_choice: KaniHashMap::default(),
            synthesis_watermark: None,
            quantifier_id: KaniHashMap::default(),
            skolem_id: KaniHashMap::default(),
            quantifier_weight: KaniHashMap::default(),
            quantifier_no_patterns: KaniHashMap::default(),
            rollback_identity: RollbackIdentity::new(),
            rollback_generation: 0,
            strict_bv_semantics_ok: std::cell::RefCell::new(KaniHashSet::default()),
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

    /// Attach the SMT-LIB/Z3 `:weight` priority to a quantifier.
    pub fn set_quantifier_weight(&mut self, id: TermId, weight: u32) {
        if matches!(self.get(id), TermData::Forall(..) | TermData::Exists(..)) {
            self.quantifier_weight.insert(id, weight);
        }
    }

    /// Return a quantifier's SMT-LIB/Z3 priority, defaulting to `1`.
    #[must_use]
    pub fn quantifier_weight(&self, id: TermId) -> u32 {
        self.quantifier_weight.get(&id).copied().unwrap_or(1)
    }

    /// Return an explicitly attached priority, distinguishing parser-default
    /// `:weight 1` from quantifiers created by APIs that use the solver config.
    #[must_use]
    pub fn explicit_quantifier_weight(&self, id: TermId) -> Option<u32> {
        self.quantifier_weight.get(&id).copied()
    }

    /// Attach exact `:no-pattern` terms to a quantifier.
    pub fn set_quantifier_no_patterns(&mut self, id: TermId, no_patterns: Vec<TermId>) {
        if matches!(self.get(id), TermData::Forall(..) | TermData::Exists(..)) {
            if no_patterns.is_empty() {
                self.quantifier_no_patterns.remove(&id);
            } else {
                self.quantifier_no_patterns.insert(id, no_patterns);
            }
        }
    }

    /// Return the exact `:no-pattern` terms attached to a quantifier.
    pub fn quantifier_no_patterns(&self, id: TermId) -> &[TermId] {
        self.quantifier_no_patterns
            .get(&id)
            .map_or(&[], Vec::as_slice)
    }

    /// Copy metadata when a logically equivalent quantifier is rebuilt.
    /// IDs, weights, and no-patterns mirror the source. `no_mbqi` is monotone
    /// across hash-consed rewrites: either origin's restriction survives.
    pub fn copy_quantifier_metadata(&mut self, source: TermId, target: TermId) {
        let target_is_forall = matches!(self.get(target), TermData::Forall(..));
        if !target_is_forall && !matches!(self.get(target), TermData::Exists(..)) {
            return;
        }

        // Snapshot first: source and target may be the same interned term.
        let no_mbqi =
            target_is_forall && (self.no_mbqi.contains(&source) || self.no_mbqi.contains(&target));
        let qid = self.quantifier_id.get(&source).cloned();
        let skid = self.skolem_id.get(&source).cloned();
        let weight = self.quantifier_weight.get(&source).copied();
        let no_patterns = self.quantifier_no_patterns(source).to_vec();

        // Mirror ordinary metadata exactly. `no_mbqi` is the exception: a
        // rebuilt term can hash-cons onto a distinct marked quantifier, so its
        // restrictive instantiation policy is merged rather than cleared.
        if no_mbqi {
            self.no_mbqi.insert(target);
        } else {
            self.no_mbqi.remove(&target);
        }

        match qid {
            Some(qid) => {
                self.quantifier_id.insert(target, qid);
            }
            None => {
                self.quantifier_id.remove(&target);
            }
        }
        match skid {
            Some(skid) => {
                self.skolem_id.insert(target, skid);
            }
            None => {
                self.skolem_id.remove(&target);
            }
        }
        match weight {
            Some(weight) => {
                self.quantifier_weight.insert(target, weight);
            }
            None => {
                self.quantifier_weight.remove(&target);
            }
        }
        if no_patterns.is_empty() {
            self.quantifier_no_patterns.remove(&target);
        } else {
            self.quantifier_no_patterns.insert(target, no_patterns);
        }
    }

    /// Register an authenticated Skolem symbol name (constant or function). See
    /// the `skolem_symbols` field docs: call only from the Skolem creation site,
    /// or while restoring an offline certificate after independently checking
    /// its exact substitution, freshness, uniqueness, and dependency provenance,
    /// so membership remains exact authority rather than a name heuristic.
    pub fn mark_skolem_symbol(&mut self, name: impl Into<String>) {
        if self.skolem_symbols.insert(name.into()) {
            // A NEW registration changes what the strict checker's
            // `is_skolem_symbol` authority answers without touching the term
            // arena; see #checker-visible-metadata-generation.
            self.bump_checker_visible_metadata_generation();
        }
    }

    /// Whether `name` was minted by Skolemization ([`Self::mark_skolem_symbol`]).
    #[must_use]
    pub fn is_skolem_symbol(&self, name: &str) -> bool {
        self.skolem_symbols.contains(name)
    }

    /// Record the Hilbert-choice term a Skolem CONSTANT denotes (see
    /// [`SkolemChoice`]). Call only from the Skolem creation site, with the
    /// binder/body the substitution actually used. No-op unless `witness` is a
    /// `Var` — a Skolem FUNCTION application has no single choice term and must
    /// stay unregistered so the printer fails closed.
    pub fn register_skolem_choice(&mut self, witness: TermId, choice: SkolemChoice) {
        if matches!(self.get(witness), TermData::Var(..)) {
            // Both a FIRST registration and an OVERWRITE change what the
            // strict checker's `skolem_choice` authority answers — and an
            // overwrite leaves the table SIZE unchanged, so nothing but this
            // bump makes the change observable to a stamp-keyed consumer;
            // see #checker-visible-metadata-generation. Bump only on an
            // actual value change so a re-registration of the identical
            // choice costs no consumer a false invalidation.
            if self.skolem_choice.get(&witness) != Some(&choice) {
                self.bump_checker_visible_metadata_generation();
            }
            self.skolem_choice.insert(witness, choice);
        }
    }

    /// The Hilbert-choice provenance of `witness`, if it was registered by
    /// [`Self::register_skolem_choice`].
    #[must_use]
    pub fn skolem_choice(&self, witness: TermId) -> Option<&SkolemChoice> {
        self.skolem_choice.get(&witness)
    }

    /// Every registered Skolem-constant choice, in ascending witness `TermId`
    /// order — i.e. mint order, so a witness precedes every witness whose body
    /// can mention it.
    pub fn skolem_choices(&self) -> impl Iterator<Item = (TermId, &SkolemChoice)> {
        let mut entries: Vec<(TermId, &SkolemChoice)> = self
            .skolem_choice
            .iter()
            .map(|(id, choice)| (*id, choice))
            .collect();
        entries.sort_by_key(|(id, _)| *id);
        entries.into_iter()
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

    /// Capture the identity of the current immutable structural snapshot.
    ///
    /// Read-only caches may reuse data only while this stamp remains equal.
    /// Any append, rollback, compaction, clone, or wholesale store replacement
    /// makes a previously captured stamp compare unequal.
    #[must_use]
    pub fn snapshot_stamp(&self) -> TermStoreSnapshotStamp {
        TermStoreSnapshotStamp {
            identity: Arc::clone(&self.rollback_identity.0),
            generation: self.rollback_generation,
            len: self.terms.len(),
        }
    }

    /// Current value of the checker-visible-metadata modification counter —
    /// see the `checker_visible_metadata_generation` field docs
    /// (#checker-visible-metadata-generation) for the exact families it
    /// covers and the mutation contract. A consumer replaying strict-checker
    /// conclusions must require BOTH an equal [`Self::snapshot_stamp`] (term
    /// arena) and an equal value here (checker-read metadata): neither
    /// authority implies the other.
    #[must_use]
    pub fn checker_visible_metadata_generation(&self) -> u64 {
        self.checker_visible_metadata_generation
    }

    /// Record one actual state change of a checker-visible metadata family.
    fn bump_checker_visible_metadata_generation(&mut self) {
        self.checker_visible_metadata_generation = self
            .checker_visible_metadata_generation
            .checked_add(1)
            .expect("checker-visible metadata generation exhausted");
    }

    /// Retire every structural snapshot and affine rollback checkpoint minted
    /// before a destructive arena rewrite.
    pub(super) fn advance_structural_generation(&mut self) {
        self.rollback_generation = self
            .rollback_generation
            .checked_add(1)
            .expect("term store structural generation exhausted");
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
        self.advance_structural_generation();
        let len = checkpoint.len;
        let keep = |id: &TermId| (id.0 as usize) < len;
        self.terms.truncate(len);
        // Every memoized checker verdict is keyed by `TermId`; the suffix this
        // truncation reclaims can be re-minted as entirely different terms, so
        // the memo must not survive it.
        self.strict_bv_semantics_ok.get_mut().clear();
        for bucket in self.hash_cons.values_mut() {
            bucket.retain(|id| keep(id));
        }
        self.hash_cons.retain(|_, bucket| !bucket.is_empty());
        self.not_cache.retain(|k, v| keep(k) && keep(v));
        self.names.retain(|_, (id, _)| keep(id));
        self.no_mbqi.retain(keep);
        self.quantifier_id.retain(|k, _| keep(k));
        self.skolem_id.retain(|k, _| keep(k));
        self.quantifier_weight.retain(|k, _| keep(k));
        self.quantifier_no_patterns
            .retain(|k, patterns| keep(k) && patterns.iter().all(&keep));
        // Drop a witness whose OWN id or whose choice body was truncated away:
        // rendering it would spell a term this store no longer holds.
        self.skolem_choice
            .retain(|k, choice| keep(k) && keep(&choice.body));
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

    /// Whether `clause` is recorded as having PASSED the strict `bv_bitblast`
    /// semantic decision procedure against this store.
    ///
    /// `true` means that procedure has already run TO COMPLETION on this exact
    /// clause in this exact store and accepted it; see
    /// `strict_bv_semantics_ok`. There is deliberately no way to record — or to
    /// observe — a failure, so this can never be used to skip a check that has
    /// not actually passed.
    #[must_use]
    pub fn strict_bv_semantics_validated(&self, clause: &[TermId]) -> bool {
        self.strict_bv_semantics_ok.borrow().contains(clause)
    }

    /// Record that the strict `bv_bitblast` semantic decision procedure ran to
    /// completion on `clause` and ACCEPTED it.
    ///
    /// Callers must only call this immediately after such a success.
    pub fn record_strict_bv_semantics_validated(&self, clause: &[TermId]) {
        let mut memo = self.strict_bv_semantics_ok.borrow_mut();
        // Bounded so an untrusted proof cannot grow the memo without limit.
        // Once full we simply stop memoizing and re-validate, as before.
        if memo.len() >= MAX_STRICT_BV_SEMANTICS_MEMO {
            return;
        }
        memo.insert(clause.to_vec());
    }

    /// Interning position of the preallocated `false` constant.
    ///
    /// [`TermStore::new`] interns `true` and then `false` into an empty store
    /// before any other term, so `false` occupies the same `TermId` in every
    /// store the solver builds — cloning preserves ids, and
    /// [`TermStore::rollback_to`] refuses to truncate below that Boolean floor.
    /// The constructor asserts the alignment, so this constant cannot drift
    /// away from [`Self::false_term`].
    ///
    /// This exists for the few callers that must recognize the `false` constant
    /// with NO store in hand — specifically the store-free proof-shape
    /// recognizers, which take only a `Proof`. Anything holding a store must
    /// use [`Self::false_term`].
    pub const PREALLOCATED_FALSE: TermId = TermId(1);

    /// Record that a USER declaration shadows the builtin `to_real` symbol
    /// (declarable as a `(_ map f)` target). Disables the to_real-integrality
    /// rewrites in comparison/equality constructors — rewriting a user's
    /// uninterpreted `to_real` would fabricate semantics for a free function.
    /// Sticky (never cleared, even on pop): conservative, fail-closed.
    /// (#to-real-bridge)
    pub fn mark_to_real_shadowed(&mut self) {
        if !self.to_real_shadowed {
            // The latch flip changes what the strict checker's ground
            // evaluator accepts without touching the term arena; see
            // #checker-visible-metadata-generation.
            self.bump_checker_visible_metadata_generation();
        }
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
        if !self.is_int_shadowed {
            // Same observability argument as `mark_to_real_shadowed`; see
            // #checker-visible-metadata-generation.
            self.bump_checker_visible_metadata_generation();
        }
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

    /// Return the opaque birth stamp for a live term slot.
    ///
    /// Unlike [`Self::get`] and [`Self::sort`], this lookup is bounds checked so
    /// an untrusted native handle can be authenticated before any indexing.
    #[must_use]
    pub fn entry_stamp(&self, id: TermId) -> Option<TermEntryStamp> {
        self.terms.get(id.index()).map(|entry| entry.stamp)
    }

    /// The current variable counter (number of unique variable ids minted).
    #[must_use]
    pub fn var_counter(&self) -> u32 {
        self.var_counter
    }

    /// Snapshot every interned term as an ordered `(TermData, Sort)` list where
    /// position `i` corresponds to `TermId(i)`. This is the checker-only payload
    /// needed to re-validate a proof offline: `check_proof_strict` reads terms
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
    /// snapshot (see `entries_snapshot`). `TermId(i)` resolves to `entries[i]`,
    /// preserving every id embedded in a serialized proof. The hash-cons interner
    /// and the name table are left EMPTY: this store supports `get`/`sort`/
    /// `true_term`/`false_term` — everything `check_proof_strict` needs — but
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
            .map(|(term, sort)| TermEntry {
                term,
                sort,
                stamp: fresh_term_entry_stamp(),
            })
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
            checker_visible_metadata_generation: 0,
            instance_term_bytes: 0,
            heap_data_bytes: 0,
            bucket_capacity_bytes: 0,
            true_memory_cache: std::cell::Cell::new(0),
            true_memory_cache_at: std::cell::Cell::new(0),
            // Empty: this checker-only store never interns, so the not-memo cache
            // stays empty (the strict checker only reads terms by index).
            not_cache: KaniHashMap::default(),
            no_mbqi: KaniHashSet::default(),
            skolem_symbols: KaniHashSet::default(),
            skolem_choice: KaniHashMap::default(),
            synthesis_watermark: None,
            quantifier_id: KaniHashMap::default(),
            skolem_id: KaniHashMap::default(),
            quantifier_weight: KaniHashMap::default(),
            quantifier_no_patterns: KaniHashMap::default(),
            rollback_identity: RollbackIdentity::new(),
            rollback_generation: 0,
            strict_bv_semantics_ok: std::cell::RefCell::new(KaniHashSet::default()),
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
