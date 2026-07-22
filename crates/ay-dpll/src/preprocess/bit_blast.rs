// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `bit-blast` preprocessing pass: QF_BV goal → pure-Boolean (SAT-level) goal.
//!
//! Rewrites a bit-vector goal into an **equisatisfiable** goal built only from
//! Boolean atoms (`and`/`or`/`not`/`xor`/`=`-over-Bool/`ite`-over-Bool) — Z3's
//! `bit-blast` tactic. Each `n`-bit BV variable becomes `n` fresh Boolean
//! bit-variables (LSB at index 0), each BV constant becomes its literal bit
//! pattern, and each BV operator is replaced by its Boolean *circuit*. The
//! resulting goal contains no bit-vector terms for the supported fragment.
//!
//! # What is bit-blasted
//!
//! The word-level circuits mirror AY's own internal SAT-level bit-blaster
//! (`ay_theories::bv`), so they are the same, already-validated circuits — only
//! the output medium differs (Boolean `TermId`s here vs CNF literals there):
//!
//! * bitwise: `bvand`, `bvor`, `bvxor`, `bvnot`, `bvnand`, `bvnor`, `bvxnor`
//! * arithmetic: `bvadd`, `bvsub`, `bvneg`, `bvmul` (ripple-carry / shift-add)
//! * shifts: `bvshl`, `bvlshr`, `bvashr` (barrel shifter)
//! * structural: `concat`, `extract`, `zero_extend`, `sign_extend`, `repeat`,
//!   and BV-sorted `ite`
//! * predicates (produce a Boolean literal): `=`, `distinct`, `bvult`, `bvule`,
//!   `bvugt`, `bvuge`, `bvslt`, `bvsle`, `bvsgt`, `bvsge`
//! * the Boolean skeleton around them: `and`, `or`, `not`, `xor`, `=>`,
//!   `=`-over-Bool (iff), `distinct`-over-Bool, and `ite`-over-Bool.
//!
//! # All-or-nothing (honest: blast, no-op, or FAIL — never a fabricated blast)
//!
//! [`BitBlast::classify_goal`] decides, before anything is rewritten, which of
//! three honest outcomes applies (so the tactic never returns a silent
//! successful identity for a goal it did not actually blast):
//!
//! * The whole goal is inside the supported fragment ([`BitBlast::is_blastable`])
//!   AND mentions bit-vector content → [`BitBlast::apply`] rewrites it to an
//!   equisatisfiable pure-Boolean goal.
//! * The goal has no bit-vector content at all → a genuine no-op identity (z3's
//!   `bit-blast` is likewise the identity on a non-BV goal — verified vs z3).
//! * The goal mentions bit-vector content but contains a construct outside the
//!   supported fragment (a division/remainder op `bvudiv`/`bvurem`/`bvsdiv`/
//!   `bvsrem`/`bvsmod`, a `bv2nat`/`int2bv`, an uninterpreted function or array
//!   over BV, …) → the tactic layer HONESTLY FAILS (a `tactic failed: … not
//!   supported by bit-blast` error). It never emits a partial or fabricated
//!   blast, and never returns the input relabeled as "blasted".
//!
//! The `apply` pass itself is still all-or-nothing (it re-checks the fragment and
//! makes no change unless the whole goal is blastable), so even reached directly
//! it can only blast-in-full or no-op — never fabricate.
//!
//! # Soundness (HARD requirement)
//!
//! Bit-blasting is **equisatisfiable**: a model of the BV goal induces (bit by
//! bit) a model of the Boolean goal and vice versa, because every operator's
//! circuit computes exactly the SMT-LIB semantics of that operator. The only
//! new variables are the per-bit Booleans standing for the BV variables' bits,
//! which are functionally in one-to-one correspondence with the BV variables'
//! values. Consequently `check-sat` on the blasted goal agrees with `check-sat`
//! on the original for every QF_BV instance.

use super::PreprocessingPass;
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};

/// Rewrite every assertion of a supported QF_BV goal into an equisatisfiable
/// pure-Boolean goal (see the module docs).
pub(crate) struct BitBlast {
    /// Memo: a BV-sorted term → its bit terms, LSB at index 0. A BV *variable*
    /// is memoized here so all its occurrences share the same fresh Boolean
    /// bits (essential for correctness — the same word must blast to the same
    /// bits everywhere).
    bits: HashMap<TermId, Vec<TermId>>,
    /// Memo: a Boolean-sorted term → its blasted Boolean term.
    blasted: HashMap<TermId, TermId>,
    /// Memo for [`Self::contains_bv`].
    has_bv: HashMap<TermId, bool>,
    /// Memo for [`Self::is_blastable`].
    supported: HashMap<TermId, bool>,
    /// Whether any assertion changed during the current `apply`.
    progress: bool,
}

impl BitBlast {
    pub(crate) fn new() -> Self {
        Self {
            bits: HashMap::default(),
            blasted: HashMap::default(),
            has_bv: HashMap::default(),
            supported: HashMap::default(),
            progress: false,
        }
    }
}

impl Default for BitBlast {
    fn default() -> Self {
        Self::new()
    }
}

impl PreprocessingPass for BitBlast {
    fn apply(&mut self, terms: &mut TermStore, assertions: &mut Vec<TermId>) -> bool {
        self.progress = false;

        // All-or-nothing: only rewrite if the WHOLE goal is inside the supported
        // fragment AND actually contains some bit-vector content. Otherwise this
        // is an honest no-op (never a partial or fabricated blast).
        let mut any_bv = false;
        for &a in assertions.iter() {
            if !self.is_blastable(terms, a) {
                return false;
            }
            if self.contains_bv(terms, a) {
                any_bv = true;
            }
        }
        if !any_bv {
            return false;
        }

        for a in assertions.iter_mut() {
            let out = self.blast_bool(terms, *a);
            if out != *a {
                self.progress = true;
            }
            *a = out;
        }
        self.progress
    }

    fn reset(&mut self) {
        self.bits.clear();
        self.blasted.clear();
        self.has_bv.clear();
        self.supported.clear();
        self.progress = false;
    }
}

#[cfg(test)]
impl BitBlast {
    /// The memoized Boolean bits (LSB first) a previous `apply` produced for the
    /// BV-sorted term `id`. Test-only introspection so the exhaustive
    /// equisatisfiability check can bind a variable's blasted bits.
    pub(crate) fn bits_for_test(&self, id: TermId) -> Vec<TermId> {
        self.bits
            .get(&id)
            .cloned()
            .expect("term was not blasted by this pass")
    }
}

/// The bit width of a BV-sorted term.
fn bv_width(terms: &TermStore, id: TermId) -> u32 {
    match terms.sort(id) {
        Sort::BitVec(bvs) => bvs.width,
        other => unreachable!("bv_width on non-BitVec sort {other:?}"),
    }
}

fn is_bv(sort: &Sort) -> bool {
    matches!(sort, Sort::BitVec(_))
}

impl BitBlast {
    // ---------------------------------------------------------------------
    // Fragment analysis
    // ---------------------------------------------------------------------

    /// Classify the goal for the tactic layer (see `Tactic::BitBlast`).
    ///
    /// This is the HONESTY GATE that decides between blasting, a legitimate
    /// identity, and an honest failure — so `(apply bit-blast)` never returns a
    /// silent successful identity for a goal it did not actually blast:
    ///
    /// - `Ok(true)`  — the whole goal is inside the supported fragment AND
    ///   mentions bit-vector content, so [`apply`](PreprocessingPass::apply)
    ///   rewrites it to an equisatisfiable pure-Boolean goal.
    /// - `Ok(false)` — the goal is BV-free; z3's `bit-blast` is a genuine no-op
    ///   identity on a non-bit-vector goal (verified vs z3 4.15.4), so the tactic
    ///   echoes it unchanged.
    /// - `Err(detail)` — the goal mentions bit-vector content but also contains a
    ///   construct outside the supported fragment (`detail` names the first such
    ///   construct, e.g. `"operator bvudiv"`); the tactic must HONESTLY FAIL
    ///   rather than fabricate or silently identity-return a blast.
    pub(crate) fn classify_goal(
        &mut self,
        terms: &TermStore,
        assertions: &[TermId],
    ) -> Result<bool, String> {
        let mut any_bv = false;
        for &a in assertions {
            if self.contains_bv(terms, a) {
                any_bv = true;
            }
        }
        if !any_bv {
            // No bit-vector content: z3's bit-blast is the identity (a no-op).
            return Ok(false);
        }
        // The goal HAS bit-vector content, so it must be FULLY blastable; a
        // bit-vector construct we cannot blast is an honest failure — never a
        // partial blast, and never a silent identity claiming to have blasted.
        for &a in assertions {
            if let Some(detail) = self.first_unsupported(terms, a) {
                return Err(detail);
            }
        }
        Ok(true)
    }

    /// If `term` (or any subterm) lies outside the supported bit-blasting
    /// fragment, return a short description of the FIRST offending construct (a
    /// deterministic pre-order walk); otherwise `None`. Mirrors [`is_blastable`]
    /// but yields the diagnostic used in the honest-failure message.
    ///
    /// [`is_blastable`]: Self::is_blastable
    fn first_unsupported(&mut self, terms: &TermStore, term: TermId) -> Option<String> {
        if self.is_blastable(terms, term) {
            return None;
        }
        match terms.get(term).clone() {
            TermData::Not(inner) => self
                .first_unsupported(terms, inner)
                .or_else(|| Some("operator not".to_string())),
            TermData::Ite(c, t, e) => self
                .first_unsupported(terms, c)
                .or_else(|| self.first_unsupported(terms, t))
                .or_else(|| self.first_unsupported(terms, e))
                .or_else(|| Some(format!("ite of sort {}", terms.sort(term)))),
            TermData::App(sym, args) => {
                if !Self::is_supported_op(sym.name()) {
                    return Some(format!("operator {}", sym.name()));
                }
                args.iter()
                    .find_map(|&a| self.first_unsupported(terms, a))
                    .or_else(|| Some(format!("operator {}", sym.name())))
            }
            TermData::Var(name, _) => Some(format!("variable {name} of sort {}", terms.sort(term))),
            TermData::Const(_) => Some(format!("constant of sort {}", terms.sort(term))),
            TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => Some("quantifier".to_string()),
            TermData::Let(_, _) => Some("let-binding".to_string()),
            _ => Some("unsupported construct".to_string()),
        }
    }

    /// Whether `name` is an operator the blaster has a circuit for (independently
    /// of whether its operands are themselves blastable — that is checked by
    /// recursion). Kept in sync with [`is_blastable_app`](Self::is_blastable_app).
    fn is_supported_op(name: &str) -> bool {
        matches!(
            name,
            "=" | "distinct"
                | "bvand"
                | "bvor"
                | "bvxor"
                | "bvnot"
                | "bvnand"
                | "bvnor"
                | "bvxnor"
                | "bvadd"
                | "bvsub"
                | "bvneg"
                | "bvmul"
                | "concat"
                | "bvshl"
                | "bvlshr"
                | "bvashr"
                | "bvult"
                | "bvule"
                | "bvugt"
                | "bvuge"
                | "bvslt"
                | "bvsle"
                | "bvsgt"
                | "bvsge"
                | "extract"
                | "zero_extend"
                | "sign_extend"
                | "repeat"
                | "rotate_left"
                | "rotate_right"
                | "bvcomp"
                | "and"
                | "or"
                | "xor"
                | "=>"
                | "implies"
        )
    }

    /// Whether `term` (and every subterm) lies inside the supported bit-blasting
    /// fragment. This is the honesty gate: if it returns `false` for any
    /// assertion, the pass leaves the whole goal untouched.
    fn is_blastable(&mut self, terms: &TermStore, term: TermId) -> bool {
        if let Some(&b) = self.supported.get(&term) {
            return b;
        }
        // Guard against cycles / re-entrancy in the DAG walk.
        self.supported.insert(term, false);
        let result = self.is_blastable_inner(terms, term);
        self.supported.insert(term, result);
        result
    }

    fn is_blastable_inner(&mut self, terms: &TermStore, term: TermId) -> bool {
        match terms.get(term).clone() {
            TermData::Const(Constant::Bool(_)) | TermData::Const(Constant::BitVec { .. }) => true,
            // Int/Real/String constants are not part of the BV fragment.
            TermData::Const(_) => false,
            // A leaf is supported iff it is Boolean- or BitVec-sorted (an Int,
            // array, datatype, … variable cannot be bit-blasted).
            TermData::Var(_, _) => {
                matches!(terms.sort(term), Sort::Bool) || is_bv(terms.sort(term))
            }
            TermData::Not(inner) => self.is_blastable(terms, inner),
            TermData::Ite(c, t, e) => {
                let s = terms.sort(term).clone();
                (matches!(s, Sort::Bool) || is_bv(&s))
                    && self.is_blastable(terms, c)
                    && self.is_blastable(terms, t)
                    && self.is_blastable(terms, e)
            }
            TermData::App(sym, args) => self.is_blastable_app(terms, sym.name(), &args),
            // Quantifiers and residual lets are outside the QF_BV fragment.
            TermData::Forall(_, _, _) | TermData::Exists(_, _, _) | TermData::Let(_, _) => false,
            _ => false,
        }
    }

    fn is_blastable_app(&mut self, terms: &TermStore, name: &str, args: &[TermId]) -> bool {
        // Structural / equality predicates need a sort check on their operands.
        match name {
            "=" | "distinct" => {
                if args.is_empty() {
                    return false;
                }
                let s0 = terms.sort(args[0]).clone();
                // Only Boolean and BitVec operands can be bit-blasted; anything
                // else (Int equality, array equality, …) is out of fragment.
                if !(matches!(s0, Sort::Bool) || is_bv(&s0)) {
                    return false;
                }
            }
            // BV-producing and BV-predicate operators: operands are BV by
            // construction; still require each to be blastable. `rotate_left`/
            // `rotate_right` carry a CONSTANT amount (an SMT-LIB index), so they
            // are a fixed bit permutation; `bvcomp` is a 1-bit equality reducer.
            "bvand" | "bvor" | "bvxor" | "bvnot" | "bvnand" | "bvnor" | "bvxnor" | "bvadd"
            | "bvsub" | "bvneg" | "bvmul" | "concat" | "bvshl" | "bvlshr" | "bvashr" | "bvult"
            | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" | "bvsgt" | "bvsge" | "extract"
            | "zero_extend" | "sign_extend" | "repeat" | "rotate_left" | "rotate_right"
            | "bvcomp" => {}
            // Boolean skeleton connectives (operands are Boolean).
            "and" | "or" | "xor" | "=>" | "implies" => {}
            // Everything else (uninterpreted functions over BV, division/rem
            // bvudiv/bvurem/bvsdiv/bvsrem/bvsmod, bv2nat/int2bv, …) is outside the
            // supported fragment; the tactic layer HONESTLY FAILS on it.
            _ => return false,
        }
        args.iter().all(|&a| self.is_blastable(terms, a))
    }

    /// Whether `term` mentions any bit-vector subterm (used to leave already
    /// pure-Boolean subformulas byte-for-byte unchanged).
    fn contains_bv(&mut self, terms: &TermStore, term: TermId) -> bool {
        if let Some(&b) = self.has_bv.get(&term) {
            return b;
        }
        self.has_bv.insert(term, false);
        let result = if is_bv(terms.sort(term)) {
            true
        } else {
            self.contains_bv_children(terms, term)
        };
        self.has_bv.insert(term, result);
        result
    }

    fn contains_bv_children(&mut self, terms: &TermStore, term: TermId) -> bool {
        match terms.get(term).clone() {
            TermData::Not(inner) => self.contains_bv(terms, inner),
            TermData::Ite(c, t, e) => {
                self.contains_bv(terms, c)
                    || self.contains_bv(terms, t)
                    || self.contains_bv(terms, e)
            }
            TermData::App(_, args) => args.iter().any(|&a| self.contains_bv(terms, a)),
            _ => false,
        }
    }

    // ---------------------------------------------------------------------
    // Boolean-side blasting
    // ---------------------------------------------------------------------

    /// Blast a Boolean-sorted term into a Boolean term with no BV subterms.
    fn blast_bool(&mut self, terms: &mut TermStore, term: TermId) -> TermId {
        // A subformula with no BV content is already pure Boolean: keep it
        // verbatim (this also covers Boolean variables and constants).
        if !self.contains_bv(terms, term) {
            return term;
        }
        if let Some(&t) = self.blasted.get(&term) {
            return t;
        }
        let result = match terms.get(term).clone() {
            TermData::Not(inner) => {
                let b = self.blast_bool(terms, inner);
                terms.mk_not(b)
            }
            TermData::Ite(c, t, e) => {
                // Boolean-sorted ite: a connective. (A BV-sorted ite is handled
                // in `bits`, never here.)
                let cb = self.blast_bool(terms, c);
                let tb = self.blast_bool(terms, t);
                let eb = self.blast_bool(terms, e);
                terms.mk_ite(cb, tb, eb)
            }
            TermData::App(sym, args) => self.blast_bool_app(terms, sym, &args),
            // Boolean var/const are handled by the `contains_bv` short-circuit
            // above; any other shape is carried through unchanged (sound: it has
            // BV content only if a child does, and children are blasted lazily).
            _ => term,
        };
        self.blasted.insert(term, result);
        result
    }

    fn blast_bool_app(&mut self, terms: &mut TermStore, sym: Symbol, args: &[TermId]) -> TermId {
        match sym.name() {
            "and" => {
                let sub: Vec<TermId> = args.iter().map(|&a| self.blast_bool(terms, a)).collect();
                terms.mk_and(sub)
            }
            "or" => {
                let sub: Vec<TermId> = args.iter().map(|&a| self.blast_bool(terms, a)).collect();
                terms.mk_or(sub)
            }
            "xor" => {
                let sub: Vec<TermId> = args.iter().map(|&a| self.blast_bool(terms, a)).collect();
                let mut it = sub.into_iter();
                let first = it.next().unwrap_or_else(|| terms.mk_bool(false));
                it.fold(first, |acc, b| terms.mk_xor(acc, b))
            }
            "=>" | "implies" => {
                // Right-associative: (=> a b c) = (=> a (=> b c)).
                let sub: Vec<TermId> = args.iter().map(|&a| self.blast_bool(terms, a)).collect();
                let mut it = sub.into_iter().rev();
                let last = it.next().unwrap_or_else(|| terms.mk_bool(true));
                it.fold(last, |acc, a| terms.mk_implies(a, acc))
            }
            "=" => self.blast_eq(terms, args),
            "distinct" => self.blast_distinct(terms, args),
            "bvult" => {
                let a = self.bits(terms, args[0]);
                let b = self.bits(terms, args[1]);
                self.bit_ult(terms, &a, &b)
            }
            "bvule" => {
                let a = self.bits(terms, args[0]);
                let b = self.bits(terms, args[1]);
                let lt = self.bit_ult(terms, &b, &a);
                terms.mk_not(lt)
            }
            "bvugt" => {
                let a = self.bits(terms, args[0]);
                let b = self.bits(terms, args[1]);
                self.bit_ult(terms, &b, &a)
            }
            "bvuge" => {
                let a = self.bits(terms, args[0]);
                let b = self.bits(terms, args[1]);
                let lt = self.bit_ult(terms, &a, &b);
                terms.mk_not(lt)
            }
            "bvslt" => {
                let a = self.bits(terms, args[0]);
                let b = self.bits(terms, args[1]);
                self.bit_slt(terms, &a, &b)
            }
            "bvsle" => {
                let a = self.bits(terms, args[0]);
                let b = self.bits(terms, args[1]);
                let lt = self.bit_slt(terms, &b, &a);
                terms.mk_not(lt)
            }
            "bvsgt" => {
                let a = self.bits(terms, args[0]);
                let b = self.bits(terms, args[1]);
                self.bit_slt(terms, &b, &a)
            }
            "bvsge" => {
                let a = self.bits(terms, args[0]);
                let b = self.bits(terms, args[1]);
                let lt = self.bit_slt(terms, &a, &b);
                terms.mk_not(lt)
            }
            // `is_blastable` guarantees no other Boolean-producing App reaches
            // here; carry it through unchanged as a defensive fallback.
            _ => {
                let sub: Vec<TermId> = args.iter().map(|&a| self.blast_bool(terms, a)).collect();
                terms.mk_app(sym, sub, Sort::Bool)
            }
        }
    }

    /// Blast an `=` over Boolean or BitVec operands ("all equal to the first").
    fn blast_eq(&mut self, terms: &mut TermStore, args: &[TermId]) -> TermId {
        if args.len() < 2 {
            return terms.mk_bool(true);
        }
        let mut conjuncts = Vec::with_capacity(args.len() - 1);
        if is_bv(terms.sort(args[0])) {
            let first = self.bits(terms, args[0]);
            for &other in &args[1..] {
                let ob = self.bits(terms, other);
                let eq = self.bits_eq(terms, &first, &ob);
                conjuncts.push(eq);
            }
        } else {
            // Boolean iff: treat as a 1-bit equality (xnor).
            let first = self.blast_bool(terms, args[0]);
            for &other in &args[1..] {
                let ob = self.blast_bool(terms, other);
                let eq = self.xnor(terms, first, ob);
                conjuncts.push(eq);
            }
        }
        terms.mk_and(conjuncts)
    }

    /// Blast a `distinct` over Boolean or BitVec operands (pairwise `!=`).
    fn blast_distinct(&mut self, terms: &mut TermStore, args: &[TermId]) -> TermId {
        if args.len() < 2 {
            return terms.mk_bool(true);
        }
        let bv = is_bv(terms.sort(args[0]));
        // Pre-blast each operand once.
        let operand_bits: Vec<Vec<TermId>> = if bv {
            args.iter().map(|&a| self.bits(terms, a)).collect()
        } else {
            args.iter()
                .map(|&a| vec![self.blast_bool(terms, a)])
                .collect()
        };
        let mut conjuncts = Vec::new();
        for i in 0..operand_bits.len() {
            for j in (i + 1)..operand_bits.len() {
                let eq = self.bits_eq(terms, &operand_bits[i], &operand_bits[j]);
                let ne = terms.mk_not(eq);
                conjuncts.push(ne);
            }
        }
        terms.mk_and(conjuncts)
    }

    // ---------------------------------------------------------------------
    // Word-level (BV) blasting: term → Vec<bit>, LSB at index 0
    // ---------------------------------------------------------------------

    /// Blast a BV-sorted term into its Boolean bit vector (LSB at index 0),
    /// memoized so a shared word (in particular a variable) blasts once.
    fn bits(&mut self, terms: &mut TermStore, term: TermId) -> Vec<TermId> {
        if let Some(b) = self.bits.get(&term) {
            return b.clone();
        }
        let result = self.bits_inner(terms, term);
        debug_assert_eq!(
            result.len() as u32,
            bv_width(terms, term),
            "bit-blast produced the wrong number of bits"
        );
        self.bits.insert(term, result.clone());
        result
    }

    fn bits_inner(&mut self, terms: &mut TermStore, term: TermId) -> Vec<TermId> {
        match terms.get(term).clone() {
            TermData::Const(Constant::BitVec { value, width }) => (0..width)
                .map(|i| terms.mk_bool(value.bit(u64::from(i))))
                .collect(),
            TermData::Var(name, _) => {
                let n = bv_width(terms, term);
                let prefix = format!("{name}!bit");
                (0..n)
                    .map(|_| terms.mk_fresh_var(&prefix, Sort::Bool))
                    .collect()
            }
            TermData::Ite(c, t, e) => {
                let sel = self.blast_bool(terms, c);
                let tb = self.bits(terms, t);
                let eb = self.bits(terms, e);
                tb.iter()
                    .zip(eb.iter())
                    .map(|(&ti, &ei)| self.mux(terms, ti, ei, sel))
                    .collect()
            }
            TermData::App(sym, args) => self.bits_app(terms, &sym, &args),
            other => unreachable!("bit-blast reached a non-BV word term: {other:?}"),
        }
    }

    fn bits_app(&mut self, terms: &mut TermStore, sym: &Symbol, args: &[TermId]) -> Vec<TermId> {
        match sym {
            Symbol::Named(name) => self.bits_named(terms, name, args),
            Symbol::Indexed(name, indices) => self.bits_indexed(terms, name, indices, args),
            // `Symbol` is `#[non_exhaustive]`; `is_blastable` only admits the two
            // shapes above, so any other kind is unreachable here.
            _ => unreachable!("bit-blast reached a non-Named/Indexed symbol"),
        }
    }

    fn bits_named(&mut self, terms: &mut TermStore, name: &str, args: &[TermId]) -> Vec<TermId> {
        match name {
            "bvand" => self.fold_bitwise(terms, args, |ts, x, y| ts.mk_and(vec![x, y])),
            "bvor" => self.fold_bitwise(terms, args, |ts, x, y| ts.mk_or(vec![x, y])),
            "bvxor" => self.fold_bitwise(terms, args, |ts, x, y| ts.mk_xor(x, y)),
            "bvnot" => {
                let a = self.bits(terms, args[0]);
                a.into_iter().map(|bit| terms.mk_not(bit)).collect()
            }
            "bvnand" => {
                let a = self.fold_bitwise(terms, args, |ts, x, y| ts.mk_and(vec![x, y]));
                a.into_iter().map(|bit| terms.mk_not(bit)).collect()
            }
            "bvnor" => {
                let a = self.fold_bitwise(terms, args, |ts, x, y| ts.mk_or(vec![x, y]));
                a.into_iter().map(|bit| terms.mk_not(bit)).collect()
            }
            "bvxnor" => {
                let a = self.fold_bitwise(terms, args, |ts, x, y| ts.mk_xor(x, y));
                a.into_iter().map(|bit| terms.mk_not(bit)).collect()
            }
            "bvadd" => self.fold_words(terms, args, |s, ts, x, y| s.add(ts, x, y)),
            "bvsub" => self.fold_words(terms, args, |s, ts, x, y| s.sub(ts, x, y)),
            "bvmul" => self.fold_words(terms, args, |s, ts, x, y| s.mul(ts, x, y)),
            "bvneg" => {
                let a = self.bits(terms, args[0]);
                self.neg(terms, &a)
            }
            "concat" => {
                // (concat a b c): a most significant, c least. LSB-first result
                // is c ++ b ++ a — walk operands in reverse, appending bits.
                let mut out = Vec::new();
                for &arg in args.iter().rev() {
                    let b = self.bits(terms, arg);
                    out.extend(b);
                }
                out
            }
            "bvshl" => {
                let a = self.bits(terms, args[0]);
                let b = self.bits(terms, args[1]);
                self.shl(terms, &a, &b)
            }
            "bvlshr" => {
                let a = self.bits(terms, args[0]);
                let b = self.bits(terms, args[1]);
                self.lshr(terms, &a, &b)
            }
            "bvashr" => {
                let a = self.bits(terms, args[0]);
                let b = self.bits(terms, args[1]);
                self.ashr(terms, &a, &b)
            }
            "bvcomp" => {
                // 1-bit result: `1` iff a == b — the AND of the per-bit XNORs.
                // (SMT-LIB `bvcomp` is binary and returns `(_ BitVec 1)`.)
                let a = self.bits(terms, args[0]);
                let b = self.bits(terms, args[1]);
                let eq = self.bits_eq(terms, &a, &b);
                vec![eq]
            }
            other => unreachable!("bit-blast reached unsupported BV op {other}"),
        }
    }

    fn bits_indexed(
        &mut self,
        terms: &mut TermStore,
        name: &str,
        indices: &[u32],
        args: &[TermId],
    ) -> Vec<TermId> {
        let a = self.bits(terms, args[0]);
        match name {
            "extract" => {
                // (_ extract high low): inclusive slice of the LSB-first bits.
                let high = indices[0] as usize;
                let low = indices[1] as usize;
                a[low..=high].to_vec()
            }
            "zero_extend" => {
                let k = indices[0] as usize;
                let mut out = a;
                let zero = terms.mk_bool(false);
                out.extend(std::iter::repeat_n(zero, k));
                out
            }
            "sign_extend" => {
                let k = indices[0] as usize;
                let sign = *a.last().expect("sign_extend of a zero-width bv");
                let mut out = a;
                out.extend(std::iter::repeat_n(sign, k));
                out
            }
            "repeat" => {
                let k = indices[0] as usize;
                let mut out = Vec::with_capacity(a.len() * k);
                for _ in 0..k {
                    out.extend(a.iter().copied());
                }
                out
            }
            "rotate_left" => {
                // (_ rotate_left k): rotate the VALUE left by k. On LSB-first
                // bits that is result[i] = a[(i + n - (k mod n)) mod n] (the top
                // bit wraps to the bottom). Cross-checked vs z3 4.15.4.
                let n = a.len();
                if n == 0 {
                    return a;
                }
                let k = (indices[0] as usize) % n;
                (0..n).map(|i| a[(i + n - k) % n]).collect()
            }
            "rotate_right" => {
                // (_ rotate_right k): rotate the VALUE right by k. On LSB-first
                // bits that is result[i] = a[(i + k) mod n]. Cross-checked vs z3.
                let n = a.len();
                if n == 0 {
                    return a;
                }
                let k = (indices[0] as usize) % n;
                (0..n).map(|i| a[(i + k) % n]).collect()
            }
            other => unreachable!("bit-blast reached unsupported indexed BV op {other}"),
        }
    }

    // ---------------------------------------------------------------------
    // Circuit primitives (mirror `ay_theories::bv`)
    // ---------------------------------------------------------------------

    fn xnor(&mut self, terms: &mut TermStore, a: TermId, b: TermId) -> TermId {
        let x = terms.mk_xor(a, b);
        terms.mk_not(x)
    }

    /// Multiplexer: `if sel then a else b`, as `(sel ∧ a) ∨ (¬sel ∧ b)`.
    fn mux(&mut self, terms: &mut TermStore, a: TermId, b: TermId, sel: TermId) -> TermId {
        let nsel = terms.mk_not(sel);
        let sa = terms.mk_and(vec![sel, a]);
        let nb = terms.mk_and(vec![nsel, b]);
        terms.mk_or(vec![sa, nb])
    }

    /// `a = b` over equal-length bit vectors: conjunction of per-bit XNOR.
    fn bits_eq(&mut self, terms: &mut TermStore, a: &[TermId], b: &[TermId]) -> TermId {
        debug_assert_eq!(a.len(), b.len());
        let mut eqs = Vec::with_capacity(a.len());
        for (&ai, &bi) in a.iter().zip(b.iter()) {
            let e = self.xnor(terms, ai, bi);
            eqs.push(e);
        }
        terms.mk_and(eqs)
    }

    /// Unsigned less-than `a < b` (ripple from LSB to MSB), matching
    /// `BvSolver::bitblast_ult`.
    fn bit_ult(&mut self, terms: &mut TermStore, a: &[TermId], b: &[TermId]) -> TermId {
        debug_assert_eq!(a.len(), b.len());
        let mut lt = terms.mk_bool(false);
        for i in 0..a.len() {
            let not_ai = terms.mk_not(a[i]);
            let a_lt_b = terms.mk_and(vec![not_ai, b[i]]);
            let eq = self.xnor(terms, a[i], b[i]);
            let eq_and_lt = terms.mk_and(vec![eq, lt]);
            lt = terms.mk_or(vec![a_lt_b, eq_and_lt]);
        }
        lt
    }

    /// Signed less-than `a <_s b`, matching `BvSolver::bitblast_slt`.
    fn bit_slt(&mut self, terms: &mut TermStore, a: &[TermId], b: &[TermId]) -> TermId {
        debug_assert_eq!(a.len(), b.len());
        let n = a.len();
        if n == 0 {
            return terms.mk_bool(false);
        }
        let sign_a = a[n - 1];
        let sign_b = b[n - 1];
        // a negative and b non-negative ⇒ a < b
        let not_sign_b = terms.mk_not(sign_b);
        let a_neg_b_pos = terms.mk_and(vec![sign_a, not_sign_b]);
        // same sign ⇒ compare magnitudes with unsigned <
        let signs_eq = self.xnor(terms, sign_a, sign_b);
        let ult = self.bit_ult(terms, a, b);
        let same_sign_lt = terms.mk_and(vec![signs_eq, ult]);
        terms.mk_or(vec![a_neg_b_pos, same_sign_lt])
    }

    /// A full adder: returns `(sum, carry_out)` for `a + b + cin`.
    fn full_adder(
        &mut self,
        terms: &mut TermStore,
        a: TermId,
        b: TermId,
        cin: TermId,
    ) -> (TermId, TermId) {
        let s1 = terms.mk_xor(a, b);
        let c1 = terms.mk_and(vec![a, b]);
        let sum = terms.mk_xor(s1, cin);
        let c2 = terms.mk_and(vec![s1, cin]);
        let carry = terms.mk_or(vec![c1, c2]);
        (sum, carry)
    }

    /// Ripple-carry `a + b + cin` (mod 2^n); the final carry is discarded.
    fn add_with_carry(
        &mut self,
        terms: &mut TermStore,
        a: &[TermId],
        b: &[TermId],
        cin: TermId,
    ) -> Vec<TermId> {
        debug_assert_eq!(a.len(), b.len());
        let mut carry = cin;
        let mut out = Vec::with_capacity(a.len());
        for i in 0..a.len() {
            let (s, c) = self.full_adder(terms, a[i], b[i], carry);
            out.push(s);
            carry = c;
        }
        out
    }

    fn add(&mut self, terms: &mut TermStore, a: &[TermId], b: &[TermId]) -> Vec<TermId> {
        let cin = terms.mk_bool(false);
        self.add_with_carry(terms, a, b, cin)
    }

    /// `a - b = a + ~b + 1`.
    fn sub(&mut self, terms: &mut TermStore, a: &[TermId], b: &[TermId]) -> Vec<TermId> {
        let not_b: Vec<TermId> = b.iter().map(|&x| terms.mk_not(x)).collect();
        let cin = terms.mk_bool(true);
        self.add_with_carry(terms, a, &not_b, cin)
    }

    /// `-a = ~a + 1`.
    fn neg(&mut self, terms: &mut TermStore, a: &[TermId]) -> Vec<TermId> {
        let not_a: Vec<TermId> = a.iter().map(|&x| terms.mk_not(x)).collect();
        let zero: Vec<TermId> = (0..a.len()).map(|_| terms.mk_bool(false)).collect();
        let cin = terms.mk_bool(true);
        self.add_with_carry(terms, &not_a, &zero, cin)
    }

    /// Shift `a` left by a *constant* amount, filling with zero (LSB-first).
    fn shift_left_const(&mut self, terms: &mut TermStore, a: &[TermId], amt: usize) -> Vec<TermId> {
        let n = a.len();
        let amt = amt.min(n);
        let mut out = Vec::with_capacity(n);
        let zero = terms.mk_bool(false);
        for _ in 0..amt {
            out.push(zero);
        }
        out.extend(a.iter().take(n - amt).copied());
        out
    }

    /// Shift-add multiplier (low `n` bits), matching `bitblast_mul_shift_add`.
    fn mul(&mut self, terms: &mut TermStore, a: &[TermId], b: &[TermId]) -> Vec<TermId> {
        // The circuit is asymmetric even though multiplication is not: bits of
        // the selector word control both masking and whether an addition is
        // needed. Put the cheaper word on that side so raw bvmul terms cannot
        // suffer an order-dependent circuit blow-up.
        let (a, b) = if Self::mul_selector_score(terms, a) < Self::mul_selector_score(terms, b) {
            (b, a)
        } else {
            (a, b)
        };
        let n = a.len();
        if n == 0 {
            return Vec::new();
        }
        let mut result: Vec<TermId> = (0..n).map(|_| terms.mk_bool(false)).collect();
        for (i, &bi) in b.iter().enumerate().take(n) {
            let shifted = self.shift_left_const(terms, a, i);
            let masked: Vec<TermId> = shifted
                .into_iter()
                .map(|s| terms.mk_and(vec![s, bi]))
                .collect();
            result = self.add(terms, &result, &masked);
        }
        result
    }

    /// Cost key for the selector side of shift-and-add multiplication.
    fn mul_selector_score(terms: &TermStore, bits: &[TermId]) -> (usize, usize) {
        let mut non_false = 0;
        let mut unknown = 0;
        for &bit in bits {
            match terms.get(bit) {
                TermData::Const(Constant::Bool(false)) => {}
                TermData::Const(Constant::Bool(true)) => non_false += 1,
                _ => {
                    non_false += 1;
                    unknown += 1;
                }
            }
        }
        (non_false, unknown)
    }

    /// `ceil(log2(n))` for `n ≥ 1` (the number of shift-amount bits a barrel
    /// shifter needs), matching the internal blaster.
    fn log2_ceil(n: usize) -> usize {
        if n.is_power_of_two() {
            n.trailing_zeros() as usize
        } else {
            (usize::BITS - n.leading_zeros()) as usize
        }
    }

    /// Per-bit multiplexer over two words.
    fn bitwise_mux(
        &mut self,
        terms: &mut TermStore,
        x: &[TermId],
        y: &[TermId],
        sel: TermId,
    ) -> Vec<TermId> {
        x.iter()
            .zip(y.iter())
            .map(|(&xi, &yi)| self.mux(terms, xi, yi, sel))
            .collect()
    }

    /// Barrel left shift by a variable amount, matching `BvSolver::bitblast_shl`.
    fn shl(&mut self, terms: &mut TermStore, a: &[TermId], b: &[TermId]) -> Vec<TermId> {
        let n = a.len();
        if n == 0 {
            return Vec::new();
        }
        let mut current = a.to_vec();
        let log2_n = Self::log2_ceil(n);
        for (i, &bi) in b.iter().enumerate().take(log2_n) {
            let shift_amt = 1usize << i;
            if shift_amt >= n {
                break;
            }
            let shifted = self.shift_left_const(terms, &current, shift_amt);
            current = self.bitwise_mux(terms, &shifted, &current, bi);
        }
        self.shift_overflow_to_zero(terms, current, b, log2_n)
    }

    /// If any shift-amount bit at or above `log2_n` is set, the shift is ≥ n and
    /// the (logical) result is all-zero. Shared by shl/lshr.
    fn shift_overflow_to_zero(
        &mut self,
        terms: &mut TermStore,
        current: Vec<TermId>,
        b: &[TermId],
        log2_n: usize,
    ) -> Vec<TermId> {
        let high_bits: Vec<TermId> = b.iter().skip(log2_n).copied().collect();
        if high_bits.is_empty() {
            return current;
        }
        let overflow = terms.mk_or(high_bits);
        let zero: Vec<TermId> = (0..current.len()).map(|_| terms.mk_bool(false)).collect();
        self.bitwise_mux(terms, &zero, &current, overflow)
    }

    /// Shift `a` right by a *constant* amount, filling the high bits with `fill`.
    fn shift_right_const_fill(&mut self, a: &[TermId], amt: usize, fill: TermId) -> Vec<TermId> {
        let n = a.len();
        let amt = amt.min(n);
        let mut out: Vec<TermId> = a.iter().skip(amt).copied().collect();
        out.extend(std::iter::repeat_n(fill, amt));
        out
    }

    /// Barrel logical right shift, matching `BvSolver::bitblast_lshr`.
    fn lshr(&mut self, terms: &mut TermStore, a: &[TermId], b: &[TermId]) -> Vec<TermId> {
        let n = a.len();
        if n == 0 {
            return Vec::new();
        }
        let zero = terms.mk_bool(false);
        let mut current = a.to_vec();
        let log2_n = Self::log2_ceil(n);
        for (i, &bi) in b.iter().enumerate().take(log2_n) {
            let shift_amt = 1usize << i;
            if shift_amt >= n {
                break;
            }
            let shifted = self.shift_right_const_fill(&current, shift_amt, zero);
            current = self.bitwise_mux(terms, &shifted, &current, bi);
        }
        self.shift_overflow_to_zero(terms, current, b, log2_n)
    }

    /// Barrel arithmetic right shift, matching `BvSolver::bitblast_ashr`.
    fn ashr(&mut self, terms: &mut TermStore, a: &[TermId], b: &[TermId]) -> Vec<TermId> {
        let n = a.len();
        if n == 0 {
            return Vec::new();
        }
        let sign = a[n - 1];
        let mut current = a.to_vec();
        let log2_n = Self::log2_ceil(n);
        for (i, &bi) in b.iter().enumerate().take(log2_n) {
            let shift_amt = 1usize << i;
            if shift_amt >= n {
                break;
            }
            let shifted = self.shift_right_const_fill(&current, shift_amt, sign);
            current = self.bitwise_mux(terms, &shifted, &current, bi);
        }
        // Overflow (shift ≥ n): every bit becomes the sign bit.
        let high_bits: Vec<TermId> = b.iter().skip(log2_n).copied().collect();
        if high_bits.is_empty() {
            return current;
        }
        let overflow = terms.mk_or(high_bits);
        let all_sign: Vec<TermId> = vec![sign; n];
        self.bitwise_mux(terms, &all_sign, &current, overflow)
    }

    // ---------------------------------------------------------------------
    // Small folding helpers
    // ---------------------------------------------------------------------

    /// Fold a per-bit binary gate over `n`-ary operands (bitwise ops).
    fn fold_bitwise(
        &mut self,
        terms: &mut TermStore,
        args: &[TermId],
        gate: impl Fn(&mut TermStore, TermId, TermId) -> TermId + Copy,
    ) -> Vec<TermId> {
        let mut acc = self.bits(terms, args[0]);
        for &arg in &args[1..] {
            let b = self.bits(terms, arg);
            acc = acc
                .iter()
                .zip(b.iter())
                .map(|(&x, &y)| gate(terms, x, y))
                .collect();
        }
        acc
    }

    /// Fold a word-level circuit over `n`-ary operands (arithmetic ops).
    fn fold_words(
        &mut self,
        terms: &mut TermStore,
        args: &[TermId],
        op: impl Fn(&mut BitBlast, &mut TermStore, &[TermId], &[TermId]) -> Vec<TermId> + Copy,
    ) -> Vec<TermId> {
        let mut acc = self.bits(terms, args[0]);
        for &arg in &args[1..] {
            let b = self.bits(terms, arg);
            acc = op(self, terms, &acc, &b);
        }
        acc
    }
}

#[cfg(test)]
#[path = "bit_blast_tests.rs"]
mod tests;
