// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Term creation (builder) methods for [`TermStore`].
//!
//! Extracted from `mod.rs` — contains `intern`, all `mk_*` constructors,
//! and `is_quantifier`.

use std::mem::size_of;
use std::sync::atomic::Ordering;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::One;

use crate::sort::Sort;

use super::{
    fresh_term_entry_stamp, Constant, Symbol, TermData, TermEntry, TermId, TermStore,
    GLOBAL_TERM_BYTES,
};

impl TermStore {
    /// Internal: find or create a term
    pub(super) fn intern(&mut self, term: TermData, sort: Sort) -> TermId {
        let hash = Self::compute_hash(&term);

        // Check if we already have this term.
        //
        // Hash-consing MUST be SORT-AWARE (#6734): two terms with identical
        // `TermData` but different sorts are DISTINCT values and must never be
        // merged into one `TermId`. This matters for sort-polymorphic nullary
        // constructors whose element sort is carried only in `sort`, not in the
        // `TermData` — e.g. `(as seq.empty (Seq Bool))` and
        // `(as seq.empty (Seq Int))` both intern as `App("seq.empty", [])`.
        // Merging them aliases a `Seq(Bool)` and a `Seq(Int)` value to one id,
        // which later drives an ill-typed `mk_eq` (sort-mismatch panic in debug,
        // a degenerate/false equality → wrong UNSAT in release). Keying the
        // bucket-equality test on `(TermData, Sort)` keeps every `TermId`
        // single-sorted. The hash stays keyed on `TermData` alone so the
        // sort-blind `find_*` lookup APIs remain consistent; the only effect is
        // that a same-`TermData`/different-`sort` term falls through to a fresh
        // entry in the same bucket instead of aliasing.
        if let Some(ids) = self.hash_cons.get(&hash) {
            for &id in ids {
                if self.terms[id.index()].term == term && self.terms[id.index()].sort == sort {
                    return id;
                }
            }
        }

        // Track approximate memory usage across all TermStore instances (#2769).
        // size_of::<TermEntry>() captures the inline struct size. We also count
        // heap allocations within TermData: Vec<TermId> children, String constants,
        // quantifier variable lists, trigger lists, and let-binding lists (#8600).
        // The names HashMap entry overhead is tracked separately in mk_var/
        // mk_fresh_named_var.
        let heap_bytes = Self::heap_size(&term);
        let entry_size = size_of::<TermEntry>() + heap_bytes;
        GLOBAL_TERM_BYTES.fetch_add(entry_size, Ordering::Relaxed);
        self.instance_term_bytes += entry_size;
        self.heap_data_bytes += heap_bytes;

        // Create new term
        let id = TermId(self.terms.len() as u32);
        self.terms.push(TermEntry {
            term,
            sort,
            stamp: fresh_term_entry_stamp(),
        });

        // Track hash_cons bucket Vec capacity overhead (#8600 item 4).
        // When the bucket Vec grows, it allocates new heap memory. We
        // measure capacity before and after the push to capture this.
        let bucket = self.hash_cons.entry(hash).or_default();
        let cap_before = bucket.capacity();
        bucket.push(id);
        let cap_after = bucket.capacity();
        if cap_after > cap_before {
            let bucket_growth = (cap_after - cap_before) * size_of::<TermId>();
            GLOBAL_TERM_BYTES.fetch_add(bucket_growth, Ordering::Relaxed);
            self.instance_term_bytes += bucket_growth;
            self.bucket_capacity_bytes += bucket_growth;
        }

        id
    }

    /// Estimate the heap bytes owned by a `TermData` value.
    ///
    /// This accounts for `Vec` capacity (elements * element size), `String`
    /// capacity, and `BigInt`/`BigRational` digit heap storage. The BigInt
    /// estimate uses `bits()` to compute the minimum number of 64-bit limbs,
    /// which slightly underestimates due to Vec capacity rounding but is close
    /// enough for OOM prevention.
    pub(super) fn heap_size(term: &TermData) -> usize {
        match term {
            TermData::Const(c) => match c {
                Constant::String(s) => s.capacity(),
                Constant::Bool(_) => 0,
                // BigInt stores digits in a heap-allocated Vec<u64>.
                // We estimate the heap as ceil(bit_length / 64) * 8 bytes,
                // falling back to 3 * size_of::<u64>() for small values
                // (BigInt always allocates at least one limb).
                Constant::Int(n) => Self::bigint_heap_estimate(n),
                Constant::Rational(r) => {
                    Self::bigint_heap_estimate(r.0.numer())
                        + Self::bigint_heap_estimate(r.0.denom())
                }
                Constant::BitVec { value, width } => {
                    // The BigInt stores ceil(width/64) limbs on the heap.
                    let limbs = (*width as usize).div_ceil(64);
                    let estimated = limbs.max(1) * size_of::<u64>();
                    // Also count the BigInt's own heap from its magnitude.
                    estimated.max(Self::bigint_heap_estimate(value))
                }
            },
            TermData::Var(name, _) => name.capacity(),
            TermData::App(sym, args) => {
                let sym_heap = match sym {
                    Symbol::Named(n) => n.capacity(),
                    Symbol::Indexed(n, indices) => {
                        n.capacity() + indices.capacity() * size_of::<u32>()
                    }
                };
                sym_heap + args.capacity() * size_of::<TermId>()
            }
            TermData::Let(bindings, _) => {
                let per_binding = size_of::<(String, TermId)>();
                let vec_heap = bindings.capacity() * per_binding;
                let string_heap: usize = bindings.iter().map(|(s, _)| s.capacity()).sum();
                vec_heap + string_heap
            }
            TermData::Not(_) | TermData::Ite(_, _, _) => 0,
            TermData::Forall(vars, _, triggers) | TermData::Exists(vars, _, triggers) => {
                let per_var = size_of::<(String, Sort)>();
                let vars_heap = vars.capacity() * per_var;
                let var_string_heap: usize = vars.iter().map(|(s, _)| s.capacity()).sum();
                let triggers_outer = triggers.capacity() * size_of::<Vec<TermId>>();
                let triggers_inner: usize = triggers
                    .iter()
                    .map(|t| t.capacity() * size_of::<TermId>())
                    .sum();
                vars_heap + var_string_heap + triggers_outer + triggers_inner
            }
        }
    }

    /// Estimate the heap bytes used by a `BigInt` value.
    ///
    /// `num-bigint`'s `BigInt` stores its magnitude in a `BigUint` which uses
    /// a `Vec<u64>` (on 64-bit platforms) or `Vec<u32>` (on 32-bit). The inline
    /// portion is captured by `size_of::<TermEntry>()` already; this estimates
    /// the heap-allocated digit buffer. We use `bits()` to determine the
    /// minimum number of 64-bit limbs needed, with a floor of 1 limb (24 bytes
    /// Vec overhead for an empty BigInt is still heap).
    fn bigint_heap_estimate(n: &BigInt) -> usize {
        let bit_len = n.bits() as usize;
        let limbs = bit_len.div_ceil(64).max(1);
        limbs * size_of::<u64>()
    }

    /// Create a boolean constant
    pub fn mk_bool(&mut self, value: bool) -> TermId {
        self.intern(TermData::Const(Constant::Bool(value)), Sort::Bool)
    }

    /// Create an integer constant
    pub fn mk_int(&mut self, value: BigInt) -> TermId {
        self.intern(TermData::Const(Constant::Int(value)), Sort::Int)
    }

    /// Create a rational constant
    pub fn mk_rational(&mut self, value: BigRational) -> TermId {
        self.intern(
            TermData::Const(Constant::Rational(value.into())),
            Sort::Real,
        )
    }

    /// Create a bitvector constant
    ///
    /// The value is normalized to the canonical unsigned representation
    /// (0 to 2^width - 1) so that `mk_bitvec(-128, 8)` and `mk_bitvec(128, 8)`
    /// produce the same interned constant (both represent 0x80).
    pub fn mk_bitvec(&mut self, value: BigInt, width: u32) -> TermId {
        // Normalize to unsigned representation: value mod 2^width
        // This ensures -128 and 128 both become 128 for 8-bit bitvectors.
        let modulus = BigInt::one() << width;
        let normalized = ((value % &modulus) + &modulus) % &modulus;
        self.intern(
            TermData::Const(Constant::BitVec {
                value: normalized,
                width,
            }),
            Sort::bitvec(width),
        )
    }

    /// Create a string constant
    pub fn mk_string(&mut self, value: String) -> TermId {
        self.intern(TermData::Const(Constant::String(value)), Sort::String)
    }

    /// The interned variable with this exact name, if one exists.
    ///
    /// Read-only counterpart to [`Self::mk_var`], which requires `&mut self`
    /// and would CREATE the variable when absent. Callers that must not mint a
    /// new binder — the model evaluator resolving a solver-internal name it did
    /// not author — need the lookup without the side effect.
    ///
    /// Returns the most recently interned binding for the name. Creating a
    /// fresh same-name binding replaces this lookup entry while the older term
    /// remains valid by its [`TermId`].
    #[must_use]
    pub fn find_var(&self, name: &str) -> Option<TermId> {
        self.names.get(name).map(|(id, _)| *id)
    }

    /// Create or get a variable with the given name and sort.
    ///
    /// Variables are reused only when both their name and sort match. If the
    /// same name was previously interned at another sort, this creates a
    /// distinct term rather than returning a mis-sorted variable.
    pub fn mk_var(&mut self, name: impl Into<String>, sort: Sort) -> TermId {
        let name = name.into();

        // Reuse the cached variable ONLY when the SORT also matches.
        //
        // This used to destructure `&(id, _)`, discarding the requested sort and
        // handing back a term of the WRONG SORT whenever a name was reused at a
        // different sort — even though the map has always stored the sort right
        // there. `define-fun` formals are bound through here, so a file whose
        // second definition reuses a parameter name at another sort got a
        // mis-sorted binder, its body failed to type-check, the command was
        // dropped, the problem was tainted, and AY emitted `(error ...)` with no
        // verdict at all.
        //
        // Measured 2026-07-26 on the full SMT-LIB corpus: that single line
        // accounted for 402 of the 637 z3-decided files across the 25 divisions
        // AY scored 0% on (428 corpus-wide) — not a theory gap, a name collision.
        //
        // Sort-aware interning is already the invariant one function down
        // (`intern`, #6734): two terms with identical `TermData` but different
        // sorts are DISTINCT values and must never be merged. This restores it
        // for named variables.
        if let Some((id, cached_sort)) = self.names.get(&name) {
            if *cached_sort == sort {
                return *id;
            }
            // Same visible name, different sort: a genuinely distinct binder.
            // That is exactly the redeclaration case `mk_fresh_named_var` exists
            // for — fresh internal identity, unchanged user-facing name.
            return self.mk_fresh_named_var(name, sort);
        }

        let var_id = self.var_counter;
        self.var_counter += 1;

        let id = self.intern(TermData::Var(name.clone(), var_id), sort.clone());
        // Track names HashMap entry heap: the String key is heap-allocated (#8600).
        // The value (TermId, Sort) is inline in the map entry; we count the key's
        // string capacity as additional heap.
        let name_heap = name.capacity() + size_of::<(TermId, Sort)>();
        GLOBAL_TERM_BYTES.fetch_add(name_heap, Ordering::Relaxed);
        self.instance_term_bytes += name_heap;
        self.heap_data_bytes += name_heap;
        self.names.insert(name, (id, sort));
        id
    }

    /// Create a fresh variable while preserving the visible symbol name.
    ///
    /// SMT-LIB allows a symbol name to be declared again after the declaring
    /// scope has been popped. Those redeclarations must get a fresh internal
    /// identity even though the user-facing name is unchanged; otherwise
    /// incremental solvers can accidentally alias stale scoped state to the
    /// new declaration.
    pub fn mk_fresh_named_var(&mut self, name: impl Into<String>, sort: Sort) -> TermId {
        let name = name.into();
        let var_id = self.var_counter;
        self.var_counter += 1;

        let id = self.intern(TermData::Var(name.clone(), var_id), sort.clone());
        // Track names HashMap entry heap (#8600).
        let name_heap = name.capacity() + size_of::<(TermId, Sort)>();
        GLOBAL_TERM_BYTES.fetch_add(name_heap, Ordering::Relaxed);
        self.instance_term_bytes += name_heap;
        self.heap_data_bytes += name_heap;
        self.names.insert(name, (id, sort));
        id
    }

    /// Create a fresh variable (guaranteed unique)
    pub fn mk_fresh_var(&mut self, prefix: &str, sort: Sort) -> TermId {
        loop {
            let var_id = self.var_counter;
            self.var_counter += 1;

            let name = format!("{prefix}_{var_id}");
            if self.names.contains_key(name.as_str()) {
                continue;
            }

            return self.intern(TermData::Var(name, var_id), sort);
        }
    }

    /// Create an internal symbol name guaranteed not to collide with user symbols.
    ///
    /// Uses format: `__ay_<purpose>!<id>` where id is monotonically increasing.
    /// The `!` separator follows Z3's fresh symbol convention.
    ///
    /// # Arguments
    /// * `purpose` - Descriptive tag (e.g., "dt_depth", "mbc")
    ///
    /// # Returns
    /// A unique symbol name that will never collide with user declarations
    /// (since user symbols starting with `__ay_` are rejected by the frontend).
    #[must_use]
    pub fn mk_internal_symbol(&mut self, purpose: &str) -> String {
        let id = self.var_counter;
        self.var_counter += 1;
        format!("__ay_{purpose}!{id}")
    }

    /// Create a function application
    pub fn mk_app(&mut self, func: Symbol, args: impl AsRef<[TermId]>, sort: Sort) -> TermId {
        let args = args.as_ref();
        // Do NOT short-circuit through the sort-blind `find_app`: for a
        // sort-polymorphic nullary constructor (e.g. `seq.empty`) the same
        // `(func, args)` can exist at a different sort, and `find_app` would
        // alias to that wrong-sorted entry (#6734). Delegate to `intern`, which
        // performs the sort-aware bucket scan and returns the existing term only
        // when BOTH `TermData` and `sort` match, otherwise mints a fresh,
        // correctly-sorted entry.
        self.intern(TermData::App(func, args.to_vec()), sort)
    }

    /// Distribute a datatype selector `sel_name` through `ite` down to constructor
    /// leaves, folding `(sel_i (C a..)) -> a_i` at each leaf. Returns `None` when a
    /// leaf is neither a constructor application of `arg`'s datatype owning a field
    /// named `sel_name` nor a further `ite`, leaving the selector opaque (so the
    /// caller falls back to the existing axiom path rather than fabricating a
    /// partial distribution).
    ///
    /// This is the term-construction dual of the frontend's elaboration-time
    /// `try_fold_selector`, exposed to post-elaboration passes (notably variable
    /// substitution): when an SSA datatype reconstruction — e.g. a `Parser`/`Vec`
    /// post-state defined `(= local_N (ite c (Parser_mk ..) ..))` — is substituted
    /// into a field read, this collapses `(fld_x (ite c (Parser_mk ..) ..))` to the
    /// concrete field value instead of leaving an opaque selector over a giant
    /// ite-tree (which never reduces and bloats the formula). SOUND by the datatype
    /// selector axiom; it keys off `arg`'s own datatype sort, so a non-selector UF
    /// is never misidentified.
    pub fn try_fold_datatype_selector(&mut self, sel_name: &str, arg: TermId) -> Option<TermId> {
        match self.get(arg).clone() {
            TermData::App(Symbol::Named(ctor_name), cargs) => {
                let Sort::Datatype(dt) = self.sort(arg).clone() else {
                    return None;
                };
                let ctor = dt.constructors.iter().find(|c| c.name == ctor_name)?;
                let idx = ctor.fields.iter().position(|f| f.name == sel_name)?;
                cargs.get(idx).copied()
            }
            TermData::Ite(cond, then_br, else_br) => {
                let folded_then = self.try_fold_datatype_selector(sel_name, then_br)?;
                let folded_else = self.try_fold_datatype_selector(sel_name, else_br)?;
                Some(self.mk_ite(cond, folded_then, folded_else))
            }
            _ => None,
        }
    }

    /// Create a universal quantifier: forall ((x1 S1) ...) body
    pub fn mk_forall(&mut self, vars: Vec<(String, Sort)>, body: TermId) -> TermId {
        self.mk_forall_with_triggers(vars, body, Vec::new())
    }

    /// Create a universal quantifier with explicit user triggers.
    pub fn mk_forall_with_triggers(
        &mut self,
        vars: Vec<(String, Sort)>,
        body: TermId,
        triggers: Vec<Vec<TermId>>,
    ) -> TermId {
        debug_assert!(
            self.sort(body) == &Sort::Bool,
            "BUG: mk_forall body must be Bool, got {:?}",
            self.sort(body)
        );
        self.intern(TermData::Forall(vars, body, triggers), Sort::Bool)
    }

    /// Create an existential quantifier: exists ((x1 S1) ...) body
    pub fn mk_exists(&mut self, vars: Vec<(String, Sort)>, body: TermId) -> TermId {
        self.mk_exists_with_triggers(vars, body, Vec::new())
    }

    /// Create an existential quantifier with explicit user triggers.
    pub fn mk_exists_with_triggers(
        &mut self,
        vars: Vec<(String, Sort)>,
        body: TermId,
        triggers: Vec<Vec<TermId>>,
    ) -> TermId {
        debug_assert!(
            self.sort(body) == &Sort::Bool,
            "BUG: mk_exists body must be Bool, got {:?}",
            self.sort(body)
        );
        self.intern(TermData::Exists(vars, body, triggers), Sort::Bool)
    }

    /// Create a let binding: (let ((x1 t1) ...) body)
    ///
    /// The sort of a let expression is the sort of its body.
    pub fn mk_let(&mut self, bindings: Vec<(String, TermId)>, body: TermId) -> TermId {
        let body_sort = self.sort(body).clone();
        self.intern(TermData::Let(bindings, body), body_sort)
    }

    /// Check if a term is a quantifier
    pub fn is_quantifier(&self, term: TermId) -> bool {
        matches!(
            self.get(term),
            TermData::Forall(_, _, _) | TermData::Exists(_, _, _)
        )
    }
}
