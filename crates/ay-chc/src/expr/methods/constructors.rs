// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! ChcExpr constructors, sort computation, and structural hashing.

use std::collections::VecDeque;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use ay_core::kani_compat::DetHashSet as FxHashSet;
use rustc_hash::FxHasher;

// Fast-core P1: wrap child expressions via the interning helper (interns leaves
// when --chc-intern is enabled; plain Arc::new otherwise / for interior nodes).
use crate::expr::intern::arc as mk_arc;

use super::{extract_int_constant, ChcExpr, ChcOp, ChcSort, ChcVar, PredicateId};

mod sort;

/// Conjuncts processed between two `should_stop` polls in
/// [`ChcExpr::and_all_checked`].
///
/// A power of two well above the cost of one `Instant::now()` (tens of ns) so
/// the poll is noise, yet small enough that a tripped deadline is observed
/// within a few hundred microseconds of hash-consing.
const AND_ALL_POLL_STRIDE: u32 = 512;

impl ChcExpr {
    // Convenience constructors

    pub fn bool_const(b: bool) -> Self {
        Self::Bool(b)
    }

    /// Build an integer constant.
    ///
    /// i128-lockstep: accepts anything losslessly convertible to `i128`
    /// (`i8`..`i128`, `u8`..`u64`) so pre-widening `int(x_i64)` call sites
    /// keep compiling unchanged.
    pub fn int(n: impl Into<i128>) -> Self {
        Self::Int(n.into())
    }

    /// Build an exact bit-vector literal from an arbitrary-precision value.
    ///
    /// Values are reduced modulo `2^width`, matching SMT-LIB's `(_ bvN W)`
    /// literal semantics. Widths through 128 use the compact leaf node; wider
    /// literals are represented as a most-significant-first tree of at most
    /// 128-bit `concat` chunks. This keeps [`ChcExpr`] source-compatible while
    /// giving typed frontends a lossless path for Rust SIMD and pointer-model
    /// values wider than `u128`.
    ///
    /// # Errors
    ///
    /// Returns [`crate::ChcError::InvalidBitVectorWidth`] unless `width` is in
    /// `1..=`[`crate::MAX_BITVECTOR_WIDTH`]. SMT-LIB does not permit width zero,
    /// and the upper bound prevents an untrusted typed input from allocating a
    /// `width / 128`-node literal tree without limit.
    pub fn bitvec_from_biguint(value: &num_bigint::BigUint, width: u32) -> crate::ChcResult<Self> {
        use num_traits::{One, ToPrimitive};

        if width == 0 || width > crate::MAX_BITVECTOR_WIDTH {
            return Err(crate::ChcError::InvalidBitVectorWidth {
                width,
                max: crate::MAX_BITVECTOR_WIDTH,
            });
        }

        // Discard high limbs before extracting chunks. Besides implementing
        // the modulo-2^width literal semantics, this bounds all subsequent
        // work by `width`: callers may otherwise pass a BigUint whose storage
        // is arbitrarily larger than the declared (and capped) BV width.
        let width_mask = (num_bigint::BigUint::one() << width) - 1_u8;
        let reduced = value & &width_mask;

        let mut chunks = Vec::new();
        let mut remaining = width;
        while remaining != 0 {
            let chunk_width = if remaining % 128 == 0 {
                128
            } else {
                remaining % 128
            };
            let offset = remaining - chunk_width;
            let mask = (num_bigint::BigUint::one() << chunk_width) - 1_u8;
            let chunk = ((&reduced >> offset) & mask).to_u128().ok_or_else(|| {
                crate::ChcError::Internal(
                    "masked bit-vector literal chunk did not fit in u128".to_owned(),
                )
            })?;
            chunks.push(Self::BitVec(chunk, chunk_width));
            remaining = offset;
        }

        let mut chunks = chunks.into_iter();
        let first = chunks
            .next()
            .ok_or(crate::ChcError::InvalidBitVectorWidth {
                width,
                max: crate::MAX_BITVECTOR_WIDTH,
            })?;
        Ok(chunks.fold(first, |high, low| {
            Self::Op(ChcOp::BvConcat, vec![mk_arc(high), mk_arc(low)])
        }))
    }

    /// Parse and build an exact unsigned bit-vector literal.
    ///
    /// This is the dependency-light entry point for typed frontends whose IR
    /// stores constants as strings. `radix` must be in `2..=36`; `digits` must
    /// be an unsigned numeral without a prefix or sign. The parsed value uses
    /// the same modulo-`2^width` semantics as [`Self::bitvec_from_biguint`].
    ///
    /// # Errors
    ///
    /// Returns a typed parse error for an invalid radix/numeral and propagates
    /// [`crate::ChcError::InvalidBitVectorWidth`] for a width outside the
    /// supported range.
    pub fn bitvec_from_str_radix(digits: &str, radix: u32, width: u32) -> crate::ChcResult<Self> {
        // Check before parsing the numeral so an invalid-width request cannot
        // amplify work through an arbitrarily large BigUint allocation.
        if width == 0 || width > crate::MAX_BITVECTOR_WIDTH {
            return Err(crate::ChcError::InvalidBitVectorWidth {
                width,
                max: crate::MAX_BITVECTOR_WIDTH,
            });
        }
        if !(2..=36).contains(&radix) {
            return Err(crate::ChcError::Parse(format!(
                "invalid bit-vector literal radix {radix}; expected 2..=36"
            )));
        }
        let value =
            num_bigint::BigUint::parse_bytes(digits.as_bytes(), radix).ok_or_else(|| {
                crate::ChcError::Parse(format!("invalid base-{radix} bit-vector literal"))
            })?;
        Self::bitvec_from_biguint(&value, width)
    }

    /// Encode a `BigInt` value as a `ChcExpr` (exact for every input).
    ///
    /// Values that fit the widened `Int(i128)` become a plain constant; only
    /// beyond-i128 magnitudes fall back to the sign-aware Horner base-10^9
    /// encoding (`(+ (* (+ (* c0 10^9) c1) 10^9) c2)...`), which the BigInt
    /// LIA lane and [`crate::expr::evaluate::evaluate_expr`]'s exact BigInt
    /// comparison fallback both fold losslessly. Shared by the parser
    /// (beyond-i128 source literals) and term→expr back-conversion
    /// (solver-side big constants re-enter the symbolic lane instead of
    /// aborting extraction).
    pub fn from_bigint(n: num_bigint::BigInt) -> Self {
        use num_traits::{Signed, ToPrimitive};
        if let Some(small) = n.to_i128() {
            return Self::Int(small);
        }

        if n.is_negative() {
            Self::neg(Self::from_bigint_positive(&(-n)))
        } else {
            Self::from_bigint_positive(&n)
        }
    }

    /// Horner base-10^9 encoding of a positive beyond-i128 `BigInt`.
    fn from_bigint_positive(n: &num_bigint::BigInt) -> Self {
        const CHUNK_DIGITS: usize = 9;
        const BASE: i64 = 1_000_000_000;

        let decimal = n.to_str_radix(10);
        let first_len = match decimal.len() % CHUNK_DIGITS {
            0 => CHUNK_DIGITS,
            len => len,
        };

        let mut chunks = Vec::new();
        chunks.push(
            decimal[..first_len]
                .parse::<i64>()
                .expect("first decimal chunk has at most 9 digits"),
        );
        let mut offset = first_len;
        while offset < decimal.len() {
            chunks.push(
                decimal[offset..offset + CHUNK_DIGITS]
                    .parse::<i64>()
                    .expect("decimal chunk has exactly 9 digits"),
            );
            offset += CHUNK_DIGITS;
        }

        let mut iter = chunks.into_iter();
        let first = Self::int(iter.next().expect("positive BigInt has digits"));
        iter.fold(first, |acc, chunk| {
            Self::add(Self::mul(acc, Self::int(BASE)), Self::int(chunk))
        })
    }

    /// Extract an integer constant, handling `Neg(Int(n))` → `-n`.
    ///
    /// Returns `Some(n)` for `Int(n)` or `Neg(Int(n))`, `None` otherwise.
    pub fn as_i128(&self) -> Option<i128> {
        extract_int_constant(self)
    }

    /// Extract an integer constant that fits in `i64`.
    ///
    /// i128-lockstep: fail-closed narrowing — returns `None` (never truncates)
    /// when the constant is outside `i64` range. Callers that can handle the
    /// full width should use [`Self::as_i128`].
    pub fn as_i64(&self) -> Option<i64> {
        extract_int_constant(self).and_then(|n| i64::try_from(n).ok())
    }

    pub fn var(v: ChcVar) -> Self {
        Self::Var(v)
    }

    /// Create a predicate application
    pub fn predicate_app(name: impl Into<String>, id: PredicateId, args: Vec<Self>) -> Self {
        Self::PredicateApp(name.into(), id, args.into_iter().map(mk_arc).collect())
    }

    pub fn not(e: Self) -> Self {
        // Double negation elimination: NOT(NOT(x)) = x
        if let Self::Op(ChcOp::Not, args) = &e {
            if args.len() == 1 {
                return (*args[0]).clone();
            }
        }
        Self::Op(ChcOp::Not, vec![mk_arc(e)])
    }

    pub fn and(a: Self, b: Self) -> Self {
        // Canonicalize to n-ary form to avoid deep left-associated trees from repeated
        // binary chaining (which can trigger stack overflows on large formulas).
        Self::and_all([a, b])
    }

    pub fn or(a: Self, b: Self) -> Self {
        // Same canonicalization as `and`: flatten nested OR chains.
        Self::or_all([a, b])
    }

    /// Build an n-ary disjunction.
    ///
    /// Returns `false` when `args` is empty.
    pub fn or_vec(args: Vec<Self>) -> Self {
        match args.len() {
            0 => Self::Bool(false),
            1 => args.into_iter().next().expect("len==1"),
            _ => Self::Op(ChcOp::Or, args.into_iter().map(mk_arc).collect()),
        }
    }

    /// Build an n-ary conjunction.
    ///
    /// Returns `true` when `args` is empty.
    pub fn and_vec(args: Vec<Self>) -> Self {
        match args.len() {
            0 => Self::Bool(true),
            1 => args.into_iter().next().expect("len==1"),
            _ => Self::Op(ChcOp::And, args.into_iter().map(mk_arc).collect()),
        }
    }

    /// Build an n-ary conjunction from an iterator with constant folding.
    ///
    /// - Returns `true` for empty input
    /// - Skips `true` literals
    /// - Short-circuits on `false` literals
    /// - Recursively flattens nested `And` operations
    ///
    /// This is the canonical version used throughout CHC solving.
    pub fn and_all(conjuncts: impl IntoIterator<Item = Self>) -> Self {
        Self::and_all_checked(conjuncts, || false)
            .expect("and_all_checked never stops when the predicate is always false")
    }

    /// [`Self::and_all`], interruptible on a caller-supplied stop predicate.
    ///
    /// The flattening loop below is the hot spot when a synthesis stage builds
    /// one very large conjunction: every conjunct is deep-hashed into `seen`,
    /// so the loop can run for seconds while the *outer* iteration count stays
    /// at one. A caller under a deadline therefore cannot bound this work by
    /// polling between calls — it has to poll inside.
    ///
    /// `should_stop` is consulted every [`AND_ALL_POLL_STRIDE`] conjuncts, which
    /// keeps the clock read off the per-conjunct path while bounding overshoot
    /// to one stride's worth of hash-consing. Returning `None` means the stop
    /// predicate tripped: the partial conjunction is DISCARDED rather than
    /// returned, so no caller can mistake a truncated (weaker) formula for the
    /// conjunction it asked for.
    pub(crate) fn and_all_checked<F: FnMut() -> bool>(
        conjuncts: impl IntoIterator<Item = Self>,
        mut should_stop: F,
    ) -> Option<Self> {
        let mut out: Vec<Arc<Self>> = Vec::new();
        let mut seen: FxHashSet<Arc<Self>> = FxHashSet::default();
        let mut pending: VecDeque<Self> = conjuncts.into_iter().collect();
        let mut since_poll: u32 = 0;

        while let Some(expr) = pending.pop_front() {
            since_poll += 1;
            if since_poll >= AND_ALL_POLL_STRIDE {
                since_poll = 0;
                if should_stop() {
                    return None;
                }
            }
            match expr {
                Self::Bool(true) => {}
                Self::Bool(false) => return Some(Self::Bool(false)),
                Self::Op(ChcOp::And, ref args) => {
                    // Maintain left-to-right order while flattening deeply nested And trees.
                    for arg in args.iter().rev() {
                        pending.push_front(arg.as_ref().clone());
                    }
                }
                other => {
                    // Exact duplicate conjuncts are idempotent. Compiler-
                    // generated CHCs often repeat identical array bounds many
                    // times after inlining; retaining one copy avoids sending
                    // a much larger but equivalent formula to every engine.
                    let arc = mk_arc(other);
                    if seen.insert(arc.clone()) {
                        out.push(arc);
                    }
                }
            }
        }

        Some(match out.len() {
            0 => Self::Bool(true),
            1 => (*out.pop().expect("len==1")).clone(),
            _ => Self::Op(ChcOp::And, out),
        })
    }

    /// Build an n-ary disjunction from an iterator with constant folding.
    ///
    /// - Returns `false` for empty input
    /// - Skips `false` literals
    /// - Short-circuits on `true` literals
    /// - Recursively flattens nested `Or` operations
    ///
    /// This is the canonical version used throughout CHC solving.
    pub fn or_all(disjuncts: impl IntoIterator<Item = Self>) -> Self {
        let mut out: Vec<Arc<Self>> = Vec::new();
        let mut seen: FxHashSet<Arc<Self>> = FxHashSet::default();
        let mut pending: VecDeque<Self> = disjuncts.into_iter().collect();

        while let Some(expr) = pending.pop_front() {
            match expr {
                Self::Bool(false) => {}
                Self::Bool(true) => return Self::Bool(true),
                Self::Op(ChcOp::Or, ref args) => {
                    // Maintain left-to-right order while flattening deeply nested Or trees.
                    for arg in args.iter().rev() {
                        pending.push_front(arg.as_ref().clone());
                    }
                }
                other => {
                    // #5877: Deduplicate repeated disjuncts. Interpolation
                    // produces massive Or expressions with identical repeated
                    // literals (e.g., `(<= x -1)` appearing 11 times).
                    //
                    // #9076 soundness: dedup by EXACT identity, not by hash
                    // alone. The previous `FxHashSet<u64>` of the disjunct's
                    // hash silently DROPPED a structurally-distinct disjunct on
                    // any 64-bit hash collision — weakening the Or, a latent
                    // unsound (unsat->sat) path. `FxHashSet<Arc<Self>>` hashes
                    // for bucketing then confirms with structural Eq, so a
                    // collision can never drop a distinct literal. The Arc clone
                    // is a refcount bump.
                    let arc = mk_arc(other);
                    if seen.insert(arc.clone()) {
                        out.push(arc);
                    }
                }
            }
        }

        match out.len() {
            0 => Self::Bool(false),
            1 => (*out.pop().expect("len==1")).clone(),
            _ => Self::Op(ChcOp::Or, out),
        }
    }

    pub fn implies(a: Self, b: Self) -> Self {
        Self::Op(ChcOp::Implies, vec![mk_arc(a), mk_arc(b)])
    }

    pub fn add(a: Self, b: Self) -> Self {
        Self::Op(ChcOp::Add, vec![mk_arc(a), mk_arc(b)])
    }

    pub fn sub(a: Self, b: Self) -> Self {
        Self::Op(ChcOp::Sub, vec![mk_arc(a), mk_arc(b)])
    }

    pub fn mul(a: Self, b: Self) -> Self {
        Self::Op(ChcOp::Mul, vec![mk_arc(a), mk_arc(b)])
    }

    pub fn mod_op(a: Self, b: Self) -> Self {
        Self::Op(ChcOp::Mod, vec![mk_arc(a), mk_arc(b)])
    }

    pub fn bv_ule(a: Self, b: Self) -> Self {
        Self::Op(ChcOp::BvULe, vec![mk_arc(a), mk_arc(b)])
    }

    pub fn bv_sle(a: Self, b: Self) -> Self {
        Self::Op(ChcOp::BvSLe, vec![mk_arc(a), mk_arc(b)])
    }

    pub fn bv_urem(a: Self, b: Self) -> Self {
        Self::Op(ChcOp::BvURem, vec![mk_arc(a), mk_arc(b)])
    }

    pub fn neg(e: Self) -> Self {
        // Constant folding: Neg(Int(n)) → Int(-n)
        if let Self::Int(n) = e {
            if let Some(neg) = n.checked_neg() {
                return Self::Int(neg);
            }
            // i64::MIN: -i64::MIN overflows, keep as Op(Neg, [Int(i64::MIN)])
        }
        // Double negation elimination: Neg(Neg(x)) → x
        if let Self::Op(ChcOp::Neg, ref args) = e {
            if args.len() == 1 {
                return (*args[0]).clone();
            }
        }
        Self::Op(ChcOp::Neg, vec![mk_arc(e)])
    }

    pub fn eq(a: Self, b: Self) -> Self {
        Self::Op(ChcOp::Eq, vec![mk_arc(a), mk_arc(b)])
    }

    pub fn ne(a: Self, b: Self) -> Self {
        Self::Op(ChcOp::Ne, vec![mk_arc(a), mk_arc(b)])
    }

    pub fn lt(a: Self, b: Self) -> Self {
        Self::Op(ChcOp::Lt, vec![mk_arc(a), mk_arc(b)])
    }

    pub fn le(a: Self, b: Self) -> Self {
        Self::Op(ChcOp::Le, vec![mk_arc(a), mk_arc(b)])
    }

    pub fn gt(a: Self, b: Self) -> Self {
        Self::Op(ChcOp::Gt, vec![mk_arc(a), mk_arc(b)])
    }

    pub fn ge(a: Self, b: Self) -> Self {
        Self::Op(ChcOp::Ge, vec![mk_arc(a), mk_arc(b)])
    }

    pub fn ite(cond: Self, then_: Self, else_: Self) -> Self {
        Self::Op(ChcOp::Ite, vec![mk_arc(cond), mk_arc(then_), mk_arc(else_)])
    }

    /// Array select: select(arr, idx)
    pub fn select(arr: Self, idx: Self) -> Self {
        Self::Op(ChcOp::Select, vec![mk_arc(arr), mk_arc(idx)])
    }

    /// Array store: store(arr, idx, val)
    pub fn store(arr: Self, idx: Self, val: Self) -> Self {
        Self::Op(ChcOp::Store, vec![mk_arc(arr), mk_arc(idx), mk_arc(val)])
    }

    /// Constant array: all elements have the given value.
    /// `key_sort` is the index sort from `(as const (Array KeySort ValSort))`.
    pub fn const_array(key_sort: ChcSort, val: Self) -> Self {
        Self::ConstArray(key_sort, mk_arc(val))
    }

    /// Compute a structural hash of the expression using FxHasher.
    /// Uses the derived `Hash` impl which recursively hashes the entire tree.
    /// Useful for deduplication in sets/maps without allocating a `to_string()`.
    pub fn structural_hash(&self) -> u64 {
        let mut hasher = FxHasher::default();
        self.hash(&mut hasher);
        hasher.finish()
    }
}
