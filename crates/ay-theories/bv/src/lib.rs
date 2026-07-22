// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

//! AY BV - Bitvector theory solver
//!
//! Implements eager bit-blasting for bitvectors. Each bitvector variable is
//! mapped to a vector of boolean variables (one per bit), and bitvector
//! operations are translated to boolean circuits.

#![warn(missing_docs)]
#![warn(clippy::all)]

// Import safe_eprintln! from ay-core (non-panicking eprintln replacement)
#[macro_use]
extern crate ay_core;

mod arithmetic;
mod arithmetic_ops;
mod assertions;
pub mod batch;
mod bitblast_bool;
mod comparisons;
mod delayed;
mod delayed_solver;
mod division;
mod gates;
mod shifts;
mod state;
mod theory_impl;
mod validation;

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, OnceLock};

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, Symbol, TermData, TermId, TermStore};
use ay_core::{CnfClause, CnfLit, Sort, TheoryPropagation, TheoryResult, TheorySolver};

pub use batch::{
    BvClauseBatch, BvFreshVarRange, BvGateTemplate, BvGateTemplateKind, BvStampedGate,
    BvTemplateBatch,
};
pub use delayed::{DelayedBvOp, DelayedBvState};
pub use validation::{
    evaluate_bv_assertion, evaluate_bv_expr, validate_bv_assertions, BvValidationError,
};

/// Red zone size for `stacker::maybe_grow` in BV bitblasting.
const BV_STACK_RED_ZONE: usize = if cfg!(debug_assertions) {
    128 * 1024
} else {
    32 * 1024
};

/// Stack segment size allocated by stacker for BV bitblast recursion.
const BV_STACK_SIZE: usize = 2 * 1024 * 1024;

/// Cached `AY_DEBUG_BOOL_ITE` env var (checked once per process).
/// Also enabled by `AY_DEBUG_THEORY=1` umbrella.
fn debug_bool_ite() -> bool {
    static CACHED: OnceLock<bool> = OnceLock::new();
    *CACHED.get_or_init(|| ay_core::debug_channel_active(ay_core::DebugChannel::BoolIte))
}

/// A vector of boolean literals representing a bitvector
/// LSB is at index 0
pub type BvBits = Vec<CnfLit>;

/// Gate cache type: maps normalized `(min(a,b), max(a,b))` key to output literal.
pub type GateCache = HashMap<(CnfLit, CnfLit), CnfLit>;

/// Reverse map from an AND gate output literal to its normalized input literals.
pub type AndChildren = HashMap<CnfLit, (CnfLit, CnfLit)>;

/// Reverse map from a primitive XOR gate output literal to its input literals.
///
/// Companion to [`AndChildren`] for the other clause-emitting binary primitive.
/// Populated only when gate-provenance capture is enabled (see
/// `BvSolver::enable_gate_provenance`); empty on the default solve path so
/// production bit-blasting pays no memory cost. Together with [`AndChildren`] and
/// [`MuxChildren`] this gives every fresh-variable Tseitin gate a (kind, inputs)
/// reverse mapping — the data a zero-trust bit-blast proof export
/// (`ay-proof::bv_blast_export`) needs to attach per-gate provenance to each CNF
/// clause. OR/XNOR/adder/comparator circuits are *composed* from these three
/// primitives, so they need no separate record.
pub type XorChildren = HashMap<CnfLit, (CnfLit, CnfLit)>;

/// Reverse map from a primitive MUX gate output literal to its `(sel, then, else)`
/// input literals. Non-commutative, so the tuple order is significant. Populated
/// only under gate-provenance capture (see [`XorChildren`]).
pub type MuxChildren = HashMap<CnfLit, (CnfLit, CnfLit, CnfLit)>;

/// Model extracted from BV solver with variable assignments
#[derive(Debug, Clone)]
pub struct BvModel {
    /// Variable assignments: term_id -> bitvector value (as BigInt)
    pub values: HashMap<TermId, num_bigint::BigInt>,
    /// Term to bit mappings (for debugging)
    pub term_to_bits: HashMap<TermId, BvBits>,
    /// Bool-sorted variable overrides from preprocessing substitution recovery.
    /// When a Bool variable is substituted with a BV predicate (e.g., `p -> (bvult x #x42)`),
    /// the evaluated Bool result is stored here for model validation (#5524).
    pub bool_overrides: HashMap<TermId, bool>,
}

/// Bitvector theory solver using eager bit-blasting
pub struct BvSolver<'a> {
    /// Reference to the term store
    terms: &'a TermStore,
    /// Mapping from BV term IDs to their bit representations
    term_to_bits: HashMap<TermId, BvBits>,
    /// Mapping from BV predicate term IDs to their bitblasted CNF variable
    /// This is used to connect Tseitin variables to BV bitblast results (#858)
    predicate_to_var: HashMap<TermId, CnfLit>,
    /// Mapping from Bool term IDs to their CNF variable.
    ///
    /// Used for bit-blasting Boolean conditions inside BV terms (e.g., `ite`).
    bool_to_var: HashMap<TermId, CnfLit>,
    /// Generated CNF clauses
    clauses: Vec<CnfClause>,
    /// Next fresh variable (1-indexed for DIMACS compatibility)
    next_var: u32,
    /// Trail of assertions for backtracking
    trail: Vec<TermId>,
    /// Stack of trail sizes for push/pop
    trail_stack: Vec<usize>,
    /// Asserted literals and their values
    asserted: HashMap<TermId, bool>,
    /// Bool terms that are conditions for BV-sorted ITE expressions.
    ///
    /// These are the ONLY Bool terms that should be linked via Tseitin
    /// equivalences. Linking all Bool terms is unsound because assertion-level
    /// structure (from `process_assertion`) creates incorrect equivalences
    /// that allow spurious SAT models. See #1696.
    bv_ite_conditions: HashSet<TermId>,
    /// Literals known to be false (constrained by unit clause `-lit`).
    /// Used for leading-zero optimization in multiplication. (#1720)
    known_false: HashSet<CnfLit>,
    /// Cached false literal: reused across all calls to `fresh_false()`.
    /// Avoids allocating a new variable and unit clause for every zero bit,
    /// which was a major source of variable bloat in QF_ABV benchmarks.
    cached_false_lit: Option<CnfLit>,
    /// Cache for AND gates: (min(a,b), max(a,b)) -> output literal
    /// Used for structural hashing to avoid duplicate gates. (#1774)
    and_cache: HashMap<(CnfLit, CnfLit), CnfLit>,
    /// Reverse map for AND gates used by the two-level AIG rewriter (#8809).
    and_children: AndChildren,
    /// Reverse map for primitive XOR gates. Populated only when
    /// `capture_gate_provenance` is set; see [`XorChildren`].
    xor_children: XorChildren,
    /// Reverse map for primitive MUX gates. Populated only when
    /// `capture_gate_provenance` is set; see [`MuxChildren`].
    mux_children: MuxChildren,
    /// When set, primitive XOR/MUX gate emitters record their output→inputs
    /// reverse mapping (into [`Self::xor_children`] / [`Self::mux_children`]) so a
    /// zero-trust bit-blast proof export can recover per-gate provenance. Off by
    /// default: the production solve path skips the inserts entirely, so big
    /// QF_BV/QF_ABV problems carry no extra per-gate memory. (AND provenance is
    /// always captured for the AIG rewriter and so is unaffected by this flag.)
    capture_gate_provenance: bool,
    /// Cache for OR gates: (min(a,b), max(a,b)) -> output literal
    /// Used for structural hashing to avoid duplicate gates. (#1774)
    or_cache: HashMap<(CnfLit, CnfLit), CnfLit>,
    /// Cache for XOR gates: (min(a,b), max(a,b)) -> output literal
    /// Used for structural hashing to avoid duplicate gates. (#1774)
    xor_cache: HashMap<(CnfLit, CnfLit), CnfLit>,
    /// Cache for MUX gates: (sel, then_lit, else_lit) -> output literal.
    /// Used for structural hashing to avoid duplicate MUX gates in nested ITE
    /// expressions. MUX is not commutative so the key is not normalized. (#8143)
    mux_cache: HashMap<(CnfLit, CnfLit, CnfLit), CnfLit>,
    /// Cache for unsigned division/remainder circuits (#4873).
    /// When both `bvudiv(x,y)` and `bvurem(x,y)` appear, they share one
    /// `bitblast_udiv_urem` circuit instead of building two independent ones.
    unsigned_div_cache: HashMap<(TermId, TermId), (BvBits, BvBits)>,
    /// Cache for signed division/remainder intermediates (#4873).
    /// Shares abs-value computation and unsigned division circuit between
    /// `bvsdiv(x,y)` and `bvsrem(x,y)`.  Stores (abs_q, abs_r, sign_a, sign_b).
    signed_div_cache: HashMap<(TermId, TermId), (BvBits, BvBits, CnfLit, CnfLit)>,
    /// Delayed operations: terms whose circuits are not yet built (#7015).
    /// Maps each delayed term to its operation name and argument TermIds.
    /// Fresh bits are allocated but unconstrained; the relationship between
    /// inputs and output is enforced lazily via `check_delayed_operations()`.
    delayed_ops: Vec<DelayedBvOp>,
    /// Whether delayed internalization is enabled for this BvSolver instance.
    delay_enabled: bool,
    /// External interrupt flag for cooperative cancellation (#8609).
    ///
    /// When set, the BV solver periodically checks this flag during long-running
    /// operations (bitblasting, circuit building) and returns early if interrupted.
    /// This allows `set_timeout()` and `interrupt()` to take effect during BV
    /// theory solving, rather than only after BV returns.
    interrupt: Option<Arc<AtomicBool>>,
    /// Terms that must be eagerly internalized even when `delay_enabled` is true (#8142).
    ///
    /// In combined theories (QF_ABV, QF_UFBV), BV terms that appear as array
    /// select/store indices or UF arguments must be eagerly bit-blasted so that
    /// array/EUF axioms reason over constrained bits. Without this, delayed
    /// mul/div/rem operations produce unconstrained index bits, causing false-UNSAT.
    eager_terms: HashSet<TermId>,
    // Per-theory runtime statistics (#4706)
    check_count: u64,
    conflict_count: u64,
    propagation_count: u64,
}

impl<'a> BvSolver<'a> {
    /// Create a new BV solver
    #[must_use]
    pub fn new(terms: &'a TermStore) -> Self {
        BvSolver {
            terms,
            term_to_bits: HashMap::default(),
            predicate_to_var: HashMap::default(),
            bool_to_var: HashMap::default(),
            clauses: Vec::new(),
            next_var: 1,
            trail: Vec::new(),
            trail_stack: Vec::new(),
            asserted: HashMap::default(),
            bv_ite_conditions: HashSet::default(),
            known_false: HashSet::default(),
            cached_false_lit: None,
            and_cache: HashMap::default(),
            and_children: HashMap::default(),
            xor_children: HashMap::default(),
            mux_children: HashMap::default(),
            capture_gate_provenance: false,
            or_cache: HashMap::default(),
            xor_cache: HashMap::default(),
            mux_cache: HashMap::default(),
            unsigned_div_cache: HashMap::default(),
            signed_div_cache: HashMap::default(),
            delayed_ops: Vec::new(),
            delay_enabled: false,
            interrupt: None,
            eager_terms: HashSet::default(),
            check_count: 0,
            conflict_count: 0,
            propagation_count: 0,
        }
    }

    /// Allocate a fresh CNF variable
    fn fresh_var(&mut self) -> CnfLit {
        let var = self.next_var as CnfLit;
        self.next_var += 1;
        var
    }

    /// Allocate a deterministic contiguous range of fresh CNF variables.
    ///
    /// This is the BV-side foundation for batch bit-blast emitters: future
    /// external code generation kernels can reserve output variables up front and stamp
    /// clauses against a stable range without changing SAT runtime semantics.
    pub fn batch_fresh_vars(&mut self, count: usize) -> BvFreshVarRange {
        let count_u32 = u32::try_from(count).expect("BV fresh-var batch count exceeds u32");
        let first = self.next_var;
        let next = first
            .checked_add(count_u32)
            .expect("BV fresh-var batch overflow");
        assert!(
            next <= i32::MAX as u32 + 1,
            "BV fresh-var batch exceeds CnfLit positive range"
        );
        self.next_var = next;
        BvFreshVarRange::new(first as CnfLit, count_u32)
    }

    /// Add a clause.
    ///
    /// This is the current single-clause emission sink for eager BV
    /// bit-blasting. Gate helpers in `gates.rs` call this after allocating
    /// outputs; `BvClauseBatch` can extract the resulting deterministic CNF
    /// without enabling native compilation.
    fn add_clause(&mut self, clause: CnfClause) {
        self.clauses.push(clause);
    }

    /// Allocate a fresh CNF variable constrained to false.
    /// The literal is tracked in `known_false` for optimization. (#1720)
    /// Cached: all zero bits share a single variable to avoid CNF bloat.
    fn fresh_false(&mut self) -> CnfLit {
        if let Some(lit) = self.cached_false_lit {
            return lit;
        }
        let var = self.fresh_var();
        self.add_clause(CnfClause::unit(-var));
        self.known_false.insert(var);
        self.cached_false_lit = Some(var);
        var
    }

    /// Check if a literal is known to be false (i.e., constrained to false)
    fn is_known_false(&self, lit: CnfLit) -> bool {
        lit > 0 && self.known_false.contains(&lit)
    }

    /// Check if a literal is known to be true (i.e., constrained to true)
    fn is_known_true(&self, lit: CnfLit) -> bool {
        lit < 0 && self.known_false.contains(&-lit)
    }

    /// Check if a literal is a known constant (either true or false)
    fn is_known_const(&self, lit: CnfLit) -> bool {
        self.is_known_true(lit) || self.is_known_false(lit)
    }

    /// Try to extract a constant usize value from a bit vector whose bits
    /// are all known constants. Returns `None` if any bit is non-constant
    /// or the value exceeds `usize::MAX`.
    ///
    /// Used by bitblaster shift/multiply shortcuts (#8111) to detect constant
    /// operands and bypass barrel-shifter/multiplier circuits.
    fn try_bits_to_usize(&self, bits: &BvBits) -> Option<usize> {
        let mut value: usize = 0;
        for (i, &lit) in bits.iter().enumerate() {
            if self.is_known_true(lit) {
                // Guard against overflow for very wide bitvectors
                if i >= usize::BITS as usize {
                    return None;
                }
                value |= 1usize << i;
            } else if !self.is_known_false(lit) {
                return None; // non-constant bit
            }
        }
        Some(value)
    }

    /// Check if exactly one bit is set (power of 2) in a constant bit vector.
    /// Returns the position of the set bit, or None if not a power of 2
    /// or if any bit is non-constant.
    ///
    /// Used by bitblaster mul shortcut (#8111) to detect power-of-2 multipliers
    /// and replace the multiplier circuit with simple wiring.
    fn try_bits_power_of_2(&self, bits: &BvBits) -> Option<usize> {
        let mut set_pos = None;
        for (i, &lit) in bits.iter().enumerate() {
            if self.is_known_true(lit) {
                if set_pos.is_some() {
                    return None; // more than one bit set
                }
                set_pos = Some(i);
            } else if !self.is_known_false(lit) {
                return None; // non-constant bit
            }
        }
        set_pos
    }

    /// Create a fresh literal constrained to true.
    ///
    /// Returns a negative literal -v where v is in known_false, so
    /// is_known_true(-v) returns true.
    fn fresh_true(&mut self) -> CnfLit {
        let v = self.fresh_var();
        // Add v to known_false, then return -v
        // is_known_true(-v) = -v < 0 && known_false.contains(&-(-v)) = known_false.contains(&v)
        self.known_false.insert(v);
        // Add unit clause asserting v is false (which means -v is true)
        self.add_clause(CnfClause::unit(-v));
        -v
    }

    /// Get or create bit representation for a BV term.
    /// Uses `stacker::maybe_grow` for stack safety on deeply nested terms (#4602).
    fn get_bits(&mut self, term: TermId) -> BvBits {
        stacker::maybe_grow(BV_STACK_RED_ZONE, BV_STACK_SIZE, || {
            if let Some(bits) = self.term_to_bits.get(&term) {
                return bits.clone();
            }

            let bits = self.bitblast(term);
            self.term_to_bits.insert(term, bits.clone());
            bits
        })
    }

    /// Bit-blast a bitvector term
    fn bitblast(&mut self, term: TermId) -> BvBits {
        let data = self.terms.get(term).clone();

        match data {
            TermData::Const(Constant::BitVec { ref value, width }) => {
                // Constant: create bits from value.
                // Zero bits use `fresh_false` to track in `known_false` for multiplication
                // optimization (#1720).
                let mut bits = Vec::with_capacity(width as usize);
                for i in 0..width {
                    let bit_set =
                        (value >> i) & num_bigint::BigInt::from(1) != num_bigint::BigInt::from(0);
                    let lit = if bit_set {
                        // Use the canonical true representation recognized by
                        // `is_known_true`, matching `const_bits`. Previously
                        // positive unit literals here looked variable to every
                        // constant-propagation and multiplier shortcut.
                        -self.fresh_false()
                    } else {
                        self.fresh_false()
                    };
                    bits.push(lit);
                }
                bits
            }
            TermData::Var(ref _name, _) => {
                // Variable: allocate fresh boolean variables
                let width = match self.terms.sort(term) {
                    Sort::BitVec(bv) => bv.width,
                    _ => return Vec::new(),
                };
                self.batch_fresh_vars(width as usize).to_vec()
            }
            TermData::Ite(cond, then_term, else_term) => {
                let Sort::BitVec(_) = self.terms.sort(term) else {
                    return Vec::new();
                };
                self.bitblast_ite_flattened(cond, then_term, else_term)
            }
            TermData::App(ref sym, ref args) => self.bitblast_app(term, sym, args),
            _ => {
                // Unknown term type - allocate fresh bits
                if let Sort::BitVec(bv) = self.terms.sort(term) {
                    self.batch_fresh_vars(bv.width as usize).to_vec()
                } else {
                    Vec::new()
                }
            }
        }
    }

    /// Return fresh unconstrained bits for the given term's sort width.
    /// Used as fallback when bitblasting encounters width mismatches (#5595).
    fn fresh_bits_for_term(&mut self, term: TermId) -> BvBits {
        if let Sort::BitVec(bv) = self.terms.sort(term) {
            self.batch_fresh_vars(bv.width as usize).to_vec()
        } else {
            Vec::new()
        }
    }

    /// Get bits for a binary BV operation, returning None if operands have
    /// mismatched widths (0 bits from non-BV sub-terms). (#5595)
    fn get_binary_bits(&mut self, a: TermId, b: TermId) -> Option<(BvBits, BvBits)> {
        let a_bits = self.get_bits(a);
        let b_bits = self.get_bits(b);
        if a_bits.is_empty() || b_bits.is_empty() || a_bits.len() != b_bits.len() {
            None
        } else {
            Some((a_bits, b_bits))
        }
    }
}

#[allow(clippy::panic)]
#[cfg(test)]
mod tests;

#[cfg(kani)]
mod verification;
