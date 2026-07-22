// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Data types for the EUF theory solver.
//!
//! Contains union-find, E-node, congruence table, and model types.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermId;
use num_bigint::BigInt;

/// Model for uninterpreted sorts - maps sort names to element enumerations
pub type SortModel = HashMap<String, Vec<String>>;

/// Function table entry: maps argument values to result value
pub type FunctionTable = Vec<(Vec<String>, String)>;

/// Model for uninterpreted functions
#[derive(Debug, Clone, Default)]
pub struct EufModel {
    /// Element representatives for each uninterpreted sort
    /// Maps sort name -> list of distinct element names
    pub sort_elements: SortModel,
    /// Maps term IDs to their model element name
    pub term_values: HashMap<TermId, String>,
    /// Function interpretations as finite tables
    /// Maps function name -> list of (arg_values, result_value) entries
    pub function_tables: HashMap<String, FunctionTable>,
    /// Source application for each aligned function-table row.
    ///
    /// Model combination may change arithmetic argument values after EUF table
    /// extraction.  Keeping the originating application makes it possible to
    /// repair or reject newly-colliding rows for every result sort without
    /// encoding provenance into user-visible model atoms.
    pub function_table_terms: HashMap<String, Vec<TermId>>,
    /// Functions whose rows became semantically inconsistent after
    /// cross-theory model merging and could not be repaired exactly.
    /// Consumers must fail closed instead of falling back to per-TermId values,
    /// which would model one mathematical function as several functions.
    pub function_table_conflicts: HashSet<String>,
    /// Function application values for Int/Real/BV-returning UF applications.
    /// Maps function application term ID -> constant term ID that equals it.
    /// This enables get-value to return the actual value for `(f x)` when
    /// we have `(= (f x) 100)` in assertions.
    pub func_app_const_terms: HashMap<TermId, TermId>,
    /// Distinct integer values for Int-sorted terms managed by EUF.
    /// Each equivalence class gets a unique integer so that disequalities
    /// are respected when no LIA/LRA model is available (#3172).
    pub int_values: HashMap<TermId, BigInt>,
    /// Int-sorted terms whose value above is a FABRICATED per-class fresh
    /// integer (no concrete constant in the class) rather than a committed
    /// one (#uflia-arith-arg-key). The model evaluator deprioritizes these:
    /// congruence resolution against committed (LIA-merged / assertion-pinned)
    /// values wins over a fabricated read, which only remains as the final
    /// fallback for terms constrained by nothing but EUF disequalities.
    pub speculative_int_terms: ay_core::kani_compat::DetHashSet<TermId>,
}

// ============================================================================
// Incremental E-Graph Data Structures
// ============================================================================

/// E-node: A term in the E-graph with equivalence class tracking and parent pointers.
///
/// Each ENode maintains:
/// - `root`: The representative of its equivalence class
/// - `next`: Circular linked list of class members (for iteration)
/// - `parents`: Function applications that use this term as an argument
/// - `class_size`: Number of members in the class (only valid at root)
///
/// Reference: Z3's `euf_enode.h`
#[derive(Clone, Debug)]
pub(crate) struct ENode {
    /// Representative of the equivalence class
    pub(crate) root: u32,
    /// Next node in circular list of equivalence class members
    pub(crate) next: u32,
    /// Size of equivalence class (only meaningful at root)
    pub(crate) class_size: u32,
    /// Parent function applications using this term as an argument.
    /// When we merge two classes, we must update the congruence table
    /// for all parent applications.
    pub(crate) parents: Vec<u32>,
    /// Proof-forest parent: the node this was merged into. None = tree root.
    /// Reference: Z3's euf_enode.h m_target
    pub(crate) proof_target: Option<u32>,
    /// Reason for the proof edge to proof_target.
    /// Reference: Z3's euf_enode.h m_justification
    pub(crate) proof_justification: Option<EqualityReason>,
}

impl ENode {
    /// Create a new ENode for a term
    pub(crate) fn new(id: u32) -> Self {
        Self {
            root: id,
            next: id, // Self-loop for singleton class
            class_size: 1,
            parents: Vec::new(),
            proof_target: None,
            proof_justification: None,
        }
    }
}

/// Compact congruence signature — zero heap allocation (#5575).
///
/// Uses a u128 hash of (func_hash, arg_representatives) as the table key.
/// This avoids Vec<u32> allocation per signature, which was the main
/// allocation hotspot in the incremental E-graph merge path.
///
/// Collision safety: `insert()` returns matches purely by signature.
/// Callers MUST verify actual congruence (same func_hash + pairwise-equal
/// arg representatives) before trusting a match. See #6153.
pub(crate) type Signature = u128;

/// Compute a compact signature hash from function hash and argument representatives.
/// No heap allocation — uses bit mixing to combine func_hash with arg reps.
#[inline]
fn compute_signature(func_hash: u64, args: &[u32], enodes: &[ENode]) -> Signature {
    let mut h = u128::from(func_hash);
    // Mix in argument count to differentiate f(a) from f(a, b)
    h = h.wrapping_mul(0x9E3779B97F4A7C15_u128) ^ (args.len() as u128);
    for &arg in args {
        // Follow root pointers to get representative
        let mut curr = arg;
        while enodes[curr as usize].root != curr {
            curr = enodes[curr as usize].root;
        }
        // Mix representative into hash
        h = h.wrapping_mul(0x517CC1B727220A95_u128) ^ u128::from(curr);
    }
    h
}

/// Like `compute_signature`, but under a merge SIMULATION: each argument's
/// live representative is remapped through `map` (live rep -> simulated
/// canonical rep) as if the simulated merges had already happened. Used by
/// the eager negative-congruence lookahead (#cong-neg-prop) to ask "what
/// would this application's signature be in the simulated world?" without
/// mutating the E-graph. The one-step case is `|r| if r == from { to } else
/// { r }`; the cascade case maps every rep in a merged group to the group's
/// canonical rep.
#[inline]
fn compute_signature_mapped(
    func_hash: u64,
    args: &[u32],
    enodes: &[ENode],
    map: impl Fn(u32) -> u32,
) -> Signature {
    let mut h = u128::from(func_hash);
    h = h.wrapping_mul(0x9E3779B97F4A7C15_u128) ^ (args.len() as u128);
    for &arg in args {
        let mut curr = arg;
        while enodes[curr as usize].root != curr {
            curr = enodes[curr as usize].root;
        }
        curr = map(curr);
        h = h.wrapping_mul(0x517CC1B727220A95_u128) ^ u128::from(curr);
    }
    h
}

/// Persistent congruence table for incremental closure.
///
/// Maps compact signature hashes to their canonical representative term.
/// Uses u128 signatures to avoid Vec allocation in the hot merge path.
///
/// Reference: Z3's `euf_etable.h`
#[derive(Clone, Debug, Default)]
pub(crate) struct CongruenceTable {
    /// Maps signature hash -> canonical term ID
    table: HashMap<Signature, u32>,
}

impl CongruenceTable {
    /// Create a new empty congruence table
    pub(crate) fn new() -> Self {
        Self {
            table: HashMap::default(),
        }
    }

    /// Build a compact signature for a function application.
    /// Zero heap allocation — uses u128 hash (#5575).
    pub(crate) fn make_signature(func_hash: u64, args: &[u32], enodes: &[ENode]) -> Signature {
        compute_signature(func_hash, args, enodes)
    }

    /// Build a signature under a simulated remapping of live representatives
    /// (#cong-neg-prop). See `compute_signature_mapped`.
    pub(crate) fn make_signature_mapped(
        func_hash: u64,
        args: &[u32],
        enodes: &[ENode],
        map: impl Fn(u32) -> u32,
    ) -> Signature {
        compute_signature_mapped(func_hash, args, enodes, map)
    }

    /// Look up the canonical term currently registered for a signature.
    /// Callers MUST verify actual congruence before trusting a match (#6153).
    pub(crate) fn get(&self, sig: &Signature) -> Option<u32> {
        self.table.get(sig).copied()
    }

    /// Insert a term into the table.
    ///
    /// Returns `Some(other)` if a congruent term already exists, `None` otherwise.
    pub(crate) fn insert(&mut self, term: u32, sig: Signature) -> Option<u32> {
        if let Some(&existing) = self.table.get(&sig) {
            if existing != term {
                return Some(existing);
            }
            // Already in table with same term, no action needed
            None
        } else {
            self.table.insert(sig, term);
            None
        }
    }

    /// Remove a term from the table by its signature.
    pub(crate) fn remove(&mut self, sig: &Signature) {
        self.table.remove(sig);
    }

    /// Raw restore of a signature->term mapping, overwriting any current
    /// occupant (#euf-inc-cong-undo). Used only by pop()'s `CongSet` undo
    /// replay to re-establish the exact pre-merge entry; unlike `insert` it
    /// does not check for or report congruence collisions.
    pub(crate) fn set(&mut self, sig: Signature, term: u32) {
        self.table.insert(sig, term);
    }

    /// Clear all entries
    pub(crate) fn clear(&mut self) {
        self.table.clear();
    }

    /// The set of signatures currently registered (#euf-inc-cong-undo debug
    /// cross-check). Used only in debug builds to assert the incremental
    /// pop-restore preserved the exact congruence key set.
    #[cfg(debug_assertions)]
    pub(crate) fn signature_set(&self) -> std::collections::BTreeSet<Signature> {
        self.table.keys().copied().collect()
    }

    /// Number of entries in the table (for testing)
    #[cfg(test)]
    pub(crate) fn table_len(&self) -> usize {
        self.table.len()
    }

    /// Whether the table is empty (for testing)
    #[cfg(test)]
    pub(crate) fn table_is_empty(&self) -> bool {
        self.table.is_empty()
    }
}

/// Undo record for incremental push/pop support.
///
/// When we push a scope, we save the undo stack length.
/// When we pop, we replay undo records in reverse order.
#[derive(Clone, Debug)]
pub(crate) enum UndoRecord {
    /// Restore a node's root pointer
    SetRoot {
        node: u32,
        old_root: u32,
        old_next: u32,
    },
    /// Restore root's class size
    SetClassSize { node: u32, old_size: u32 },
    /// Remove a parent from a node's parent list
    RemoveParent { node: u32 },
    /// Remove an equality edge added during incremental_merge (#3734)
    RemoveEqualityEdge(u32, u32),
    /// Undo a proof-forest merge: clear node's proof target and reverse the
    /// old root's justification chain to restore pre-merge proof tree.
    /// Port of Z3's unmerge_justification (euf_enode.cpp).
    UnmergeProofForest { node: u32, old_root: u32 },
    /// Remove a shared equality reason added during assert_shared_equality (#4840).
    /// Enables scope-aware cleanup instead of blanket clear, preventing
    /// proof-forest explain() from finding dangling Shared reason references.
    RemoveSharedEqualityReason(u32, u32),
    /// Remove a shared disequality added during assert_shared_disequality (#8469).
    /// Enables scope-aware cleanup on pop().
    RemoveSharedDisequality(u32, u32),
    /// Restore a congruence-table entry that `incremental_merge` removed
    /// (#euf-inc-cong-undo). Replaying this on pop re-establishes the exact
    /// signature->term mapping that existed before the merge, so the full
    /// O(func_apps) `cong_table` rebuild in pop() can be skipped. Sound: the
    /// canonical term stored for a signature is verified argument-by-argument
    /// at every consumption site, and the restored table's KEY SET (the set of
    /// distinct live signatures under the restored roots) is identical to what
    /// a from-scratch rebuild produces.
    CongSet { sig: Signature, term: u32 },
    /// Remove a congruence-table entry that `incremental_merge` newly inserted
    /// (#euf-inc-cong-undo). See `CongSet`.
    CongRemove { sig: Signature },
    /// Restore a disequality-pair-index entry that `incremental_merge` (rep
    /// rekey) or a merged-pair collapse removed (#euf-inc-diseq-undo).
    /// Replaying this on pop re-establishes the exact
    /// `(min_rep,max_rep) -> (a, b, eq_term)` mapping present before the merge,
    /// so the O(|assigns|) `diseq_pair_index` rebuild in pop() can be skipped.
    /// Sound: the restored index's KEY SET (the set of live disequal rep-pairs
    /// under the restored roots) is identical to a from-scratch rebuild's; only
    /// the canonical witness stored for a multiply-witnessed pair may differ,
    /// and that witness is re-validated against the live e-graph at every
    /// consumption site (`emit_diseq_propagations` orientation check,
    /// `check_disequality_conflicts` staleness gate).
    DiseqSet {
        key: (u32, u32),
        entry: (TermId, TermId, TermId),
    },
    /// Remove a disequality-pair-index entry that `incremental_merge` (rekey)
    /// newly created (#euf-inc-diseq-undo). The rekeyed disequality is restored
    /// under its pre-merge key by the paired `DiseqSet`, so this is a pure
    /// removal. See `DiseqSet`.
    DiseqRemove { key: (u32, u32) },
    /// Undo a `sync_diseq_index` insertion that moved a disequality from the
    /// pending queue into the index (#euf-inc-diseq-undo). Unlike `DiseqRemove`
    /// (a merge rekey), the diseq's ONLY home is this index entry, so undoing it
    /// must also put it BACK on `pending_neg_eqs` — but ONLY if the disequality
    /// assignment itself survived the pop (a deferred sync: the diseq was
    /// asserted at a shallower scope than it was indexed, e.g. its terms entered
    /// the e-graph late). If the assignment was retracted by this same pop, the
    /// diseq is simply gone and no re-queue happens. The re-queue makes the
    /// completeness guard in pop() observe a non-empty pending set and fall back
    /// to the sound from-scratch rebuild for that pop.
    DiseqUnsync {
        key: (u32, u32),
        entry: (TermId, TermId, TermId),
    },
}

// ============================================================================
// Original Union-Find (kept for compatibility during transition)
// ============================================================================

/// Union-Find structure for equivalence classes
pub(crate) struct UnionFind {
    pub(crate) parent: Vec<u32>,
    pub(crate) rank: Vec<u32>,
}

impl UnionFind {
    /// Create a new union-find with n elements
    #[must_use]
    #[allow(clippy::cast_possible_truncation)] // n is bounded by term count which fits in u32
    pub(crate) fn new(n: usize) -> Self {
        Self {
            parent: (0..n as u32).collect(),
            rank: vec![0; n],
        }
    }

    pub(crate) fn reset(&mut self) {
        for (idx, p) in self.parent.iter_mut().enumerate() {
            *p = idx as u32;
        }
        self.rank.fill(0);
    }

    pub(crate) fn ensure_size(&mut self, n: usize) {
        if n <= self.parent.len() {
            return;
        }
        let start = self.parent.len() as u32;
        self.parent
            .extend(start..start + (n - self.parent.len()) as u32);
        self.rank.resize(n, 0);
    }

    /// Find the representative of an element (with path compression)
    pub(crate) fn find(&mut self, x: u32) -> u32 {
        if self.parent[x as usize] != x {
            self.parent[x as usize] = self.find(self.parent[x as usize]);
        }
        self.parent[x as usize]
    }

    /// Union two elements
    #[cfg_attr(not(kani), allow(dead_code))]
    pub(crate) fn union(&mut self, x: u32, y: u32) {
        let rx = self.find(x);
        let ry = self.find(y);
        if rx != ry {
            match self.rank[rx as usize].cmp(&self.rank[ry as usize]) {
                std::cmp::Ordering::Less => {
                    self.parent[rx as usize] = ry;
                }
                std::cmp::Ordering::Greater => {
                    self.parent[ry as usize] = rx;
                }
                std::cmp::Ordering::Equal => {
                    self.parent[ry as usize] = rx;
                    self.rank[rx as usize] += 1;
                }
            }
        }
    }
}

/// Reason for an edge in the equality graph
#[derive(Clone, Debug)]
pub(crate) enum EqualityReason {
    /// Direct equality assertion: the TermId of the (= a b) term
    Direct(TermId),
    /// Congruence: f(a1,...,an) = f(b1,...,bn) because ai = bi for all i
    Congruence {
        /// The two congruent terms (for future proof generation)
        _term1: TermId,
        _term2: TermId,
        /// Pairs of arguments that must be equal
        arg_pairs: Vec<(TermId, TermId)>,
    },
    /// Shared equality from Nelson-Oppen theory combination.
    /// The actual reason literals are stored in `EufSolver::shared_equality_reasons`.
    Shared,
    /// Bool-value merge: two terms share the same Boolean truth value.
    /// The edge between `term` and its canonical representative exists because
    /// both were assigned the stored `value`. (#4610)
    BoolValue {
        /// The term merged with the canonical representative
        term: TermId,
        /// The truth value assigned to both
        value: bool,
    },
    /// ITE axiom: `ite(c, t, e) = t` when `c = true`, or `ite(c, t, e) = e` when `c = false`.
    /// The condition term is stored so explain() can produce the reason. (#5081)
    Ite {
        /// The condition term that was assigned
        condition: TermId,
        /// The truth value of the condition
        value: bool,
    },
}

/// Result of the negative-congruence merge-lookahead simulation
/// (#cong-neg-prop): asserting the candidate equality would — through the
/// recorded cascade of congruence merges — make applications `hit.0` and
/// `hit.1` congruent while their (simulated) classes carry the asserted
/// disequality `diseq`. This records STRUCTURE only (which apps became
/// congruent, in application order); the propagation REASON is rebuilt from
/// the live proof forest at emit time, never cached, so it cannot go stale.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CongNegCascade {
    /// Cascade merges applied beyond the hypothesis, in application order:
    /// each pair `(p, q)` is an application pair that is congruent in the
    /// simulated world of the hypothesis merge plus all EARLIER entries
    /// (congruence is monotone under merges, so later worlds keep it).
    /// Empty for a depth-1 (legacy one-step) hit.
    pub(crate) merges: Vec<(u32, u32)>,
    /// Final congruent application pair whose simulated classes carry the
    /// disequality. Congruent in the world of the hypothesis + all `merges`.
    pub(crate) hit: (u32, u32),
    /// The asserted disequality witness: `(a, b, atom)` with `atom` the
    /// `(= a b)` term currently asserted FALSE.
    pub(crate) diseq: (TermId, TermId, TermId),
}

/// Reusable scratch for the cascade lookahead (#cong-neg-prop): one instance
/// lives on the solver and is taken/restored per `cong_diseq_lookahead` call,
/// so the hot miss path (the overwhelmingly common outcome) allocates
/// nothing. The overlay is a tiny linear-assoc map (live rep -> simulated
/// group id) — bounded by 2x the merge-application cap, so linear scans beat
/// hashing.
#[derive(Default)]
pub(crate) struct CongNegScratch {
    /// (live rep, simulated group id) pairs; absent rep = singleton class.
    pub(crate) overlay: Vec<(u32, u32)>,
    /// Canonical live rep per simulated group id (index).
    pub(crate) canon: Vec<u32>,
    /// Pending simulated merges: (term_a, term_b, level).
    pub(crate) queue: std::collections::VecDeque<(u32, u32, u32)>,
    /// Simulated signature -> app for re-hashed apps. NOT rebuilt between
    /// rounds: stale entries are harmless because every probe hit is verified
    /// argument-by-argument before use.
    pub(crate) local_sigs: HashMap<Signature, u32>,
    /// Every app re-hashed so far (budget accounting; dedup by `contains`).
    pub(crate) rehashed: Vec<u32>,
    /// Apps to re-hash in the current round.
    pub(crate) round: Vec<u32>,
    /// Generation-stamped membership mirror of `round` (indexed by term id):
    /// `round_stamp[p] == round_gen` iff `p` is in the current round. Makes the
    /// per-parent dedup O(1) instead of a linear `round.contains` — pure
    /// speedup; the ordered `round` Vec still drives iteration order.
    pub(crate) round_stamp: Vec<u32>,
    pub(crate) round_gen: u32,
    /// Generation-stamped membership mirror of `rehashed` (indexed by term id):
    /// `rehashed_stamp[p] == rehashed_gen` iff `p` is already re-hashed in this
    /// lookahead. Replaces the linear `rehashed.contains`; `rehashed` order is
    /// irrelevant (only membership + len matter), so this is behaviour-exact.
    pub(crate) rehashed_stamp: Vec<u32>,
    pub(crate) rehashed_gen: u32,
    /// Key-list buffers for the diseq probe / from-member collection.
    pub(crate) keys_a: Vec<u32>,
    pub(crate) keys_b: Vec<u32>,
}

/// Cached metadata for a function application term
pub(crate) struct FuncAppMeta {
    pub(crate) term_id: u32,
    /// Pre-computed hash of (symbol, result_sort) for fast signature lookup
    pub(crate) func_hash: u64,
    /// Argument term ids (not representatives - those change)
    pub(crate) args: Vec<u32>,
}

/// Reason why two terms should be merged (for worklist processing)
#[derive(Clone, Debug)]
pub(crate) struct MergeReason {
    /// First term
    pub(crate) a: u32,
    /// Second term
    pub(crate) b: u32,
    /// Why they are equal
    pub(crate) reason: EqualityReason,
}
