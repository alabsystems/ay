// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Incremental state accessors for `BvSolver`.
//!
//! These methods handle saving and restoring BV solver state across
//! incremental solving sessions (push/pop). They are mechanical
//! getter/setter pairs with no algorithmic content.

use super::*;

impl BvSolver<'_> {
    /// Get the generated CNF clauses
    pub fn clauses(&self) -> &[CnfClause] {
        &self.clauses
    }

    /// Take ownership of the generated CNF clauses
    pub fn take_clauses(&mut self) -> Vec<CnfClause> {
        std::mem::take(&mut self.clauses)
    }

    /// Extract generated clauses into the deterministic flat BV batch contract.
    ///
    /// This does not change solver state and does not compile or install native
    /// code. It is intended as the BV-side handoff for future external code generation
    /// clause emitters.
    pub fn clause_batch(&self) -> BvClauseBatch {
        BvClauseBatch::from_clauses(self.num_vars(), &self.clauses)
    }

    /// Get the number of variables used
    pub fn num_vars(&self) -> u32 {
        self.next_var - 1
    }

    /// Cheap O(1) estimate of how many persistent-cache entries this solver's
    /// current state would capture: the same collections `ay-chc`'s
    /// `PersistentBvCache::total_entries()` counts, measured live. Used by the
    /// caller's DYNAMIC bit-blast budget guard to abort a single query's blast
    /// the moment it would overflow the cache cap, instead of predicting the
    /// cost from term shapes up front (which over- or under-counts by up to
    /// 5x depending on sharing structure).
    pub fn minted_entries_estimate(&self) -> usize {
        let (unsigned_div, signed_div) = (&self.unsigned_div_cache, &self.signed_div_cache);
        self.clauses.len()
            + self.term_to_bits.len()
            + self.predicate_to_var.len()
            + self.bool_to_var.len()
            + self.bv_ite_conditions.len()
            + self.and_cache.len()
            + self.and_children.len()
            + self.or_cache.len()
            + self.xor_cache.len()
            + self.mux_cache.len()
            + unsigned_div.len()
            + signed_div.len()
    }

    /// Get the bit representation for a term, if it has been bit-blasted
    ///
    /// Returns None if the term has not been processed by the bit-blaster
    pub fn get_term_bits(&self, term: TermId) -> Option<&[CnfLit]> {
        self.term_to_bits.get(&term).map(Vec::as_slice)
    }

    /// Ensure a bitvector term has a bit-level representation.
    ///
    /// Returns the cached/generated bit literals for `term`, or `None` when
    /// `term` is not bitvector-sorted.
    pub fn ensure_term_bits(&mut self, term: TermId) -> Option<Vec<CnfLit>> {
        if !matches!(self.terms.sort(term), Sort::BitVec(_)) {
            return None;
        }
        Some(self.get_bits(term))
    }

    /// Ensure a Bool-sorted term has a single-literal representation.
    ///
    /// Returns the cached/generated CNF literal for `term` (recorded in
    /// `bool_to_var`), or `None` when `term` is not Bool-sorted. Used by the
    /// combined-theory congruence generators to encode equality between
    /// Bool-sorted UF arguments as a 1-bit XOR (Bool args have no BV bits, so
    /// `ensure_term_bits` cannot represent them).
    pub fn ensure_bool_literal(&mut self, term: TermId) -> Option<CnfLit> {
        if !matches!(self.terms.sort(term), Sort::Bool) {
            return None;
        }
        Some(self.bitblast_bool(term))
    }

    /// Get an iterator over all bit-blasted terms and their bit representations
    pub fn iter_term_bits(&self) -> impl Iterator<Item = (TermId, &[CnfLit])> {
        self.term_to_bits
            .iter()
            .map(|(&id, bits)| (id, bits.as_slice()))
    }

    /// Get a reference to all term-to-bits mappings
    ///
    /// Used for preserving BV state across incremental solving sessions.
    pub fn term_to_bits(&self) -> &HashMap<TermId, BvBits> {
        &self.term_to_bits
    }

    /// Get a reference to all predicate-to-var mappings
    ///
    /// Maps BV predicate term IDs (equalities, comparisons) to their bitblasted
    /// CNF variables. Used to connect Tseitin variables to BV results (#858).
    pub fn predicate_to_var(&self) -> &HashMap<TermId, CnfLit> {
        &self.predicate_to_var
    }

    /// Get a reference to all Bool-to-var mappings used by the BV bitblaster.
    ///
    /// These literals represent Boolean terms that appear *inside* BV terms
    /// (e.g., as conditions of BV `ite`).
    pub fn bool_to_var(&self) -> &HashMap<TermId, CnfLit> {
        &self.bool_to_var
    }

    /// Set the bit representation for a term
    ///
    /// Used for restoring BV state in incremental solving.
    pub fn set_term_bits(&mut self, term: TermId, bits: BvBits) {
        self.term_to_bits.insert(term, bits);
    }

    /// Set the next variable counter
    ///
    /// Used for restoring BV state in incremental solving.
    pub fn set_next_var(&mut self, next_var: u32) {
        self.next_var = next_var;
    }

    /// Set the full term-to-bits mapping (bulk restore for delayed circuit building).
    pub fn set_term_to_bits(&mut self, map: HashMap<TermId, BvBits>) {
        self.term_to_bits = map;
    }

    /// Set the delayed operations list (for Phase 2 circuit building).
    pub fn set_delayed_ops(&mut self, ops: Vec<DelayedBvOp>) {
        self.delayed_ops = ops;
    }

    /// Restore the predicate-to-variable cache
    ///
    /// Used for restoring BV state in incremental solving (#1452).
    /// This ensures that re-bitblasting predicates returns the same CNF variables
    /// that were used in previous check-sats.
    pub fn set_predicate_to_var(&mut self, map: HashMap<TermId, CnfLit>) {
        self.predicate_to_var = map;
    }

    /// Restore the Bool-to-variable cache.
    ///
    /// Used for restoring BV state in incremental solving. This ensures that
    /// Boolean terms inside BV expressions (e.g., BV `ite` conditions) map to a
    /// stable SAT variable across check-sat calls.
    pub fn set_bool_to_var(&mut self, map: HashMap<TermId, CnfLit>) {
        self.bool_to_var = map;
    }

    /// Get the set of Bool terms that are conditions for BV-sorted ITE expressions.
    ///
    /// Only these terms should be linked via Tseitin equivalences during BV encoding.
    /// Linking other Bool terms (from assertion-level structure) is unsound. See #1696.
    pub fn bv_ite_conditions(&self) -> &HashSet<TermId> {
        &self.bv_ite_conditions
    }

    /// Restore the BV ITE conditions set.
    ///
    /// Used for restoring BV state in incremental solving.
    pub fn set_bv_ite_conditions(&mut self, conditions: HashSet<TermId>) {
        self.bv_ite_conditions = conditions;
    }

    /// Get gate caches for incremental state preservation (#5877).
    ///
    /// Returns (and_cache, or_cache, xor_cache) so the caller can persist them
    /// across `BvSolver` rebuilds. Without this, re-bitblasting shared
    /// sub-expressions creates redundant gate variables that over-constrain
    /// the SAT solver.
    pub fn gate_caches(&self) -> (&GateCache, &GateCache, &GateCache) {
        (&self.and_cache, &self.or_cache, &self.xor_cache)
    }

    /// Get the AND child provenance map for incremental state preservation (#8809).
    pub fn and_children(&self) -> &AndChildren {
        &self.and_children
    }

    /// Enable gate-provenance capture: subsequent primitive XOR/MUX gates record
    /// their output→inputs reverse mapping (queryable via [`Self::xor_children`] /
    /// [`Self::mux_children`]). Off by default so the production solve path carries
    /// no extra per-gate memory. Enable before bit-blasting when a zero-trust proof
    /// export needs to recover each fresh gate's (kind, inputs). AND provenance is
    /// always recorded (for the AIG rewriter) and so is independent of this flag.
    pub fn enable_gate_provenance(&mut self) {
        self.capture_gate_provenance = true;
    }

    /// Get the primitive-XOR child provenance map (output literal → input pair).
    /// Empty unless [`Self::enable_gate_provenance`] was called before blasting.
    pub fn xor_children(&self) -> &XorChildren {
        &self.xor_children
    }

    /// Get the primitive-MUX child provenance map (output literal → `(sel, then,
    /// else)`). Empty unless [`Self::enable_gate_provenance`] was called.
    pub fn mux_children(&self) -> &MuxChildren {
        &self.mux_children
    }

    /// Get the MUX gate cache for incremental state preservation (#8143).
    ///
    /// Returns the MUX cache mapping (sel, then, else) -> output literal.
    pub fn mux_cache(&self) -> &HashMap<(CnfLit, CnfLit, CnfLit), CnfLit> {
        &self.mux_cache
    }

    /// Restore gate caches from a previous incremental session (#5877).
    pub fn set_gate_caches(
        &mut self,
        and_cache: GateCache,
        or_cache: GateCache,
        xor_cache: GateCache,
    ) {
        self.and_cache = and_cache;
        self.or_cache = or_cache;
        self.xor_cache = xor_cache;
    }

    /// Restore AND child provenance from a previous incremental session (#8809).
    pub fn set_and_children(&mut self, and_children: AndChildren) {
        self.and_children = and_children;
    }

    /// Restore the MUX gate cache from a previous incremental session (#8143).
    pub fn set_mux_cache(&mut self, cache: HashMap<(CnfLit, CnfLit, CnfLit), CnfLit>) {
        self.mux_cache = cache;
    }

    /// Get division caches for incremental state preservation (#5877).
    ///
    /// Returns (unsigned_div_cache, signed_div_cache) for persisting across rebuilds.
    #[allow(clippy::type_complexity)]
    pub fn div_caches(
        &self,
    ) -> (
        &HashMap<(TermId, TermId), (BvBits, BvBits)>,
        &HashMap<(TermId, TermId), (BvBits, BvBits, CnfLit, CnfLit)>,
    ) {
        (&self.unsigned_div_cache, &self.signed_div_cache)
    }

    /// Restore division caches from a previous incremental session (#5877).
    #[allow(clippy::type_complexity)]
    pub fn set_div_caches(
        &mut self,
        unsigned: HashMap<(TermId, TermId), (BvBits, BvBits)>,
        signed: HashMap<(TermId, TermId), (BvBits, BvBits, CnfLit, CnfLit)>,
    ) {
        self.unsigned_div_cache = unsigned;
        self.signed_div_cache = signed;
    }

    /// Check if a bit literal has a known constant value.
    ///
    /// Returns `Some(true)` if the bit is known-true, `Some(false)` if known-false,
    /// `None` if the value is not determined at encoding time.
    /// Used by array axiom generation to skip axioms for provably-distinct indices.
    pub fn bit_constant_value(&self, lit: CnfLit) -> Option<bool> {
        if self.is_known_false(lit) {
            Some(false)
        } else if self.is_known_true(lit) {
            Some(true)
        } else {
            None
        }
    }

    /// Check if two bit vectors represent provably distinct constants.
    ///
    /// Returns true when both bit vectors are fully constant (all bits have
    /// known values) and differ in at least one bit position. This enables
    /// skipping functional consistency axioms for array index pairs that can
    /// never be equal, avoiding O(N^2) axiom explosion on benchmarks with
    /// many constant-indexed selects.
    pub fn are_bits_distinct_constants(&self, bits_a: &[CnfLit], bits_b: &[CnfLit]) -> bool {
        if bits_a.len() != bits_b.len() || bits_a.is_empty() {
            return false;
        }
        let mut all_const = true;
        let mut any_differ = false;
        for (&a, &b) in bits_a.iter().zip(bits_b.iter()) {
            let va = self.bit_constant_value(a);
            let vb = self.bit_constant_value(b);
            match (va, vb) {
                (Some(ca), Some(cb)) => {
                    if ca != cb {
                        any_differ = true;
                    }
                }
                _ => {
                    all_const = false;
                    break;
                }
            }
        }
        all_const && any_differ
    }

    /// Set an external interrupt flag for cooperative cancellation (#8609).
    ///
    /// When set, the BV solver checks this flag periodically during long-running
    /// operations (bitblasting, delayed circuit building) and returns early if
    /// the flag is set to `true`. This allows `set_timeout()` and `interrupt()`
    /// to take effect during BV theory solving.
    pub fn set_interrupt(&mut self, flag: Arc<AtomicBool>) {
        self.interrupt = Some(flag);
    }

    /// Check whether the external interrupt flag has been set (#8609).
    ///
    /// Returns `true` if the interrupt flag exists and is set to `true`.
    /// Used for cooperative cancellation in hot loops.
    pub fn is_interrupted(&self) -> bool {
        self.interrupt
            .as_ref()
            .is_some_and(|flag| flag.load(Ordering::Relaxed))
    }

    /// Count the number of bit positions where both literals are known-equal
    /// constants. Used to optimize diff variable generation — positions where
    /// both indices have the same known bit value don't need XOR diff variables.
    pub fn count_known_equal_bits(&self, bits_a: &[CnfLit], bits_b: &[CnfLit]) -> usize {
        bits_a
            .iter()
            .zip(bits_b.iter())
            .filter(|(&a, &b)| {
                matches!(
                    (self.bit_constant_value(a), self.bit_constant_value(b)),
                    (Some(va), Some(vb)) if va == vb
                )
            })
            .count()
    }
}
