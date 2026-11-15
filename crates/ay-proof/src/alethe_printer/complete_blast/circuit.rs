// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The Boolean gate DAG that mirrors the pinned checker's bit-blasting
//! circuits TERM FOR TERM.
//!
//! Every `bitblast_*` rule in carcara re-computes the circuit it expects and
//! compares it to the printed conclusion with `assert_eq`, so a gate built
//! here is accepted only if it is spelled exactly as
//! `carcara/src/checker/rules/bitvectors.rs` builds it — including the
//! constant `false` operands and the doubled negations that the checker does
//! NOT fold away. That is why a reference carries a PRINTED negation count
//! rather than a Boolean polarity: `(not (not x))` and `x` are the same
//! literal to carcara's resolution layer (`remove_all_negations_with_polarity`)
//! and DIFFERENT terms to its rule layer, and this type has to be right for
//! both at once.

use super::super::dialect::{self, AletheDialect, CleanOnlySpelling};
use ay_core::kani_compat::DetHashMap;
use std::fmt::Write as _;

/// Largest printed negation nesting a reference may carry. The circuits below
/// never need more than two; anything deeper is refused rather than printed.
const MAX_NOTS: u8 = 3;

/// Widest operand the word circuits below will build: the lowering's own
/// bit-vector width bound, so every per-bit allocation here is bounded.
const MAX_CIRCUIT_BITS: usize = super::MAX_WIDTH as usize;

/// A signed reference to a gate: the gate itself plus the number of `not`
/// wrappers that must be PRINTED around it.
///
/// `nots` is a print count, not a polarity: the checker's rule layer compares
/// terms syntactically, so a circuit position the checker spells
/// `(not (not x))` must be printed that way even though the SAT layer treats
/// it as the positive literal `x`.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(super) struct SRef {
    pub(super) gate: u32,
    pub(super) nots: u8,
}

mod divide;
pub(super) use divide::Divider;

impl SRef {
    pub(super) const fn pos(gate: u32) -> Self {
        Self { gate, nots: 0 }
    }

    /// Wrap one more printed `not`. Returns `None` past [`MAX_NOTS`] so a
    /// pathological nesting fails closed instead of printing a term the
    /// circuit replication was never measured against.
    pub(super) const fn not(self) -> Option<Self> {
        if self.nots >= MAX_NOTS {
            return None;
        }
        Some(Self {
            gate: self.gate,
            nots: self.nots + 1,
        })
    }

    /// Whether the SAT literal for this reference is negative.
    pub(super) const fn negative(self) -> bool {
        self.nots % 2 == 1
    }
}

/// One node of the gate DAG.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub(super) enum GateKind {
    /// A free Boolean variable printed with this exact spelling (a
    /// `((_ @bit_of i) t)` projection, or a Boolean problem variable).
    Atom(String),
    /// A Boolean constant, printed `true` / `false`.
    Const(bool),
    /// `(and ...)`, at least two arguments.
    And(Vec<SRef>),
    /// `(or ...)`, at least two arguments.
    Or(Vec<SRef>),
    /// `(xor a b)`.
    Xor(SRef, SRef),
    /// `(=> a b)`, retained verbatim for the checker's implication rules.
    Implies(SRef, SRef),
    /// `(= a b)` between two Boolean terms.
    Iff(SRef, SRef),
    /// `(ite c a b)` between two Boolean terms.
    Ite(SRef, SRef, SRef),
    /// A theory atom whose printed body is supplied verbatim (a bit-vector
    /// equality or `bvult`). Its Tseitin clauses come from the bit-blast
    /// equivalence step, never from Boolean structure.
    Theory(String),
}

/// A hash-consed gate DAG plus the proof-local names its nodes print under.
pub(super) struct Circuit {
    prefix: String,
    kinds: Vec<GateKind>,
    interned: DetHashMap<GateKind, u32>,
}

impl Circuit {
    pub(super) fn new(prefix: String) -> Self {
        Self {
            prefix,
            kinds: Vec::new(),
            interned: DetHashMap::default(),
        }
    }

    pub(super) fn len(&self) -> usize {
        self.kinds.len()
    }

    pub(super) fn kind(&self, gate: u32) -> &GateKind {
        &self.kinds[gate as usize]
    }

    fn intern(&mut self, kind: GateKind) -> u32 {
        if let Some(existing) = self.interned.get(&kind) {
            return *existing;
        }
        let id = self.kinds.len() as u32;
        self.kinds.push(kind.clone());
        self.interned.insert(kind, id);
        id
    }

    pub(super) fn atom(&mut self, text: String) -> SRef {
        SRef::pos(self.intern(GateKind::Atom(text)))
    }

    pub(super) fn constant(&mut self, value: bool) -> SRef {
        SRef::pos(self.intern(GateKind::Const(value)))
    }

    pub(super) fn and(&mut self, args: Vec<SRef>) -> SRef {
        debug_assert!(args.len() >= 2);
        SRef::pos(self.intern(GateKind::And(args)))
    }

    pub(super) fn or(&mut self, args: Vec<SRef>) -> SRef {
        debug_assert!(args.len() >= 2);
        SRef::pos(self.intern(GateKind::Or(args)))
    }

    pub(super) fn xor(&mut self, a: SRef, b: SRef) -> SRef {
        SRef::pos(self.intern(GateKind::Xor(a, b)))
    }

    pub(super) fn implies(&mut self, a: SRef, b: SRef) -> SRef {
        SRef::pos(self.intern(GateKind::Implies(a, b)))
    }

    pub(super) fn iff(&mut self, a: SRef, b: SRef) -> SRef {
        SRef::pos(self.intern(GateKind::Iff(a, b)))
    }

    pub(super) fn ite(&mut self, c: SRef, a: SRef, b: SRef) -> SRef {
        SRef::pos(self.intern(GateKind::Ite(c, a, b)))
    }

    pub(super) fn theory(&mut self, body: String) -> SRef {
        SRef::pos(self.intern(GateKind::Theory(body)))
    }

    /// The spelling a gate is referenced by. Atoms and constants print
    /// themselves; every structural gate prints its proof-local name, which
    /// the checker inlines back to the body before any rule runs.
    pub(super) fn reference(&self, gate: u32) -> String {
        match &self.kinds[gate as usize] {
            GateKind::Atom(text) => text.clone(),
            GateKind::Const(true) => "true".to_string(),
            GateKind::Const(false) => "false".to_string(),
            _ => format!("{}g{gate}", self.prefix),
        }
    }

    /// The printed form of a signed reference, negation wrappers included.
    pub(super) fn text(&self, r: SRef) -> String {
        let mut out = self.reference(r.gate);
        for _ in 0..r.nots {
            out = format!("(not {out})");
        }
        out
    }

    /// The `define-fun` body for a structural gate, or `None` for a gate that
    /// prints itself.
    pub(super) fn definition(&self, gate: u32) -> Option<String> {
        let mut body = String::new();
        match &self.kinds[gate as usize] {
            GateKind::Atom(_) | GateKind::Const(_) => return None,
            GateKind::And(args) => {
                body.push_str("(and");
                for a in args {
                    let _ = write!(body, " {}", self.text(*a));
                }
                body.push(')');
            }
            GateKind::Or(args) => {
                body.push_str("(or");
                for a in args {
                    let _ = write!(body, " {}", self.text(*a));
                }
                body.push(')');
            }
            GateKind::Xor(a, b) => {
                let _ = write!(body, "(xor {} {})", self.text(*a), self.text(*b));
            }
            GateKind::Implies(a, b) => {
                let _ = write!(body, "(=> {} {})", self.text(*a), self.text(*b));
            }
            GateKind::Iff(a, b) => {
                let _ = write!(body, "(= {} {})", self.text(*a), self.text(*b));
            }
            GateKind::Ite(c, a, b) => {
                let _ = write!(
                    body,
                    "(ite {} {} {})",
                    self.text(*c),
                    self.text(*a),
                    self.text(*b)
                );
            }
            GateKind::Theory(text) => body.push_str(text),
        }
        Some(body)
    }

    // ---------------------------------------------------------------- circuits

    /// carcara `ripple_carry_adder` with no incoming carry: `carries[0]` is
    /// `false`, `carry_i` is
    /// `(or (and x_{i-1} y_{i-1}) (and (xor x_{i-1} y_{i-1}) carry_{i-1}))`
    /// and `res_i` is `(xor (xor x_i y_i) carry_i)`.
    ///
    /// Returns `None` when `y` is narrower than `x` or the width exceeds
    /// [`MAX_CIRCUIT_BITS`].
    pub(super) fn ripple_carry_adder(&mut self, x: &[SRef], y: &[SRef]) -> Option<Vec<SRef>> {
        let size = x.len();
        if size > MAX_CIRCUIT_BITS || y.len() < size {
            return None;
        }
        let mut carry = self.constant(false);
        let mut carries = Vec::with_capacity(size);
        carries.push(carry);
        for (xi, yi) in x.iter().zip(y).take(size.saturating_sub(1)) {
            let generate = self.and(vec![*xi, *yi]);
            let propagate = self.xor(*xi, *yi);
            let carried = self.and(vec![propagate, carry]);
            carry = self.or(vec![generate, carried]);
            carries.push(carry);
        }
        let mut out = Vec::with_capacity(size);
        for ((xi, yi), carry_i) in x.iter().zip(y).zip(&carries) {
            let half = self.xor(*xi, *yi);
            out.push(self.xor(half, *carry_i));
        }
        Some(out)
    }

    /// carcara `bitblast_ult`: `(and (not x_0) y_0)` extended by
    /// `(or (and (= x_i y_i) prev) (and (not x_i) y_i))`.
    pub(super) fn unsigned_less_than(&mut self, x: &[SRef], y: &[SRef]) -> Option<SRef> {
        let size = x.len();
        if size == 0 || y.len() != size {
            return None;
        }
        let (x0, y0) = (x.first()?, y.first()?);
        let not_x0 = x0.not()?;
        let mut res = self.and(vec![not_x0, *y0]);
        for (xi, yi) in x.iter().zip(y).skip(1) {
            let same = self.iff(*xi, *yi);
            let keep = self.and(vec![same, res]);
            let not_xi = xi.not()?;
            let strict = self.and(vec![not_xi, *yi]);
            res = self.or(vec![keep, strict]);
        }
        Some(res)
    }

    /// carcara `bitblast_slt`: [`Self::unsigned_less_than`] over every bit
    /// below the sign, then `(or (and (= x_s y_s) prev) (and x_s (not y_s)))`
    /// at the sign bit `s`; at width one it is `(and x_0 (not y_0))`.
    pub(super) fn signed_less_than(&mut self, x: &[SRef], y: &[SRef]) -> Option<SRef> {
        let size = x.len();
        if size == 0 || y.len() != size {
            return None;
        }
        let (sign_x, sign_y) = (*x.last()?, *y.last()?);
        let not_sign_y = sign_y.not()?;
        if size == 1 {
            return Some(self.and(vec![sign_x, not_sign_y]));
        }
        let (x0, y0) = (x.first()?, y.first()?);
        let not_x0 = x0.not()?;
        let mut res = self.and(vec![not_x0, *y0]);
        for (xi, yi) in x.iter().zip(y).take(size - 1).skip(1) {
            let same = self.iff(*xi, *yi);
            let keep = self.and(vec![same, res]);
            let not_xi = xi.not()?;
            let strict = self.and(vec![not_xi, *yi]);
            res = self.or(vec![keep, strict]);
        }
        let same = self.iff(sign_x, sign_y);
        let keep = self.and(vec![same, res]);
        let strict = self.and(vec![sign_x, not_sign_y]);
        Some(self.or(vec![keep, strict]))
    }

    /// carcara `bitblast_neg`: two's complement as `(bvnot x) + 1`, spelled
    /// with the same `false` operands the checker builds.
    pub(super) fn negate_bits(&mut self, x: &[SRef]) -> Option<Vec<SRef>> {
        let size = x.len();
        if size > MAX_CIRCUIT_BITS {
            return None;
        }
        let false_ref = self.constant(false);
        let mut carry = self.constant(true);
        let mut carries = Vec::with_capacity(size);
        carries.push(carry);
        for prev in x.iter().take(size.saturating_sub(1)) {
            let not_prev = prev.not()?;
            let generate = self.and(vec![not_prev, false_ref]);
            let propagate = self.xor(not_prev, false_ref);
            let carried = self.and(vec![propagate, carry]);
            carry = self.or(vec![generate, carried]);
            carries.push(carry);
        }
        let mut out = Vec::with_capacity(size);
        for (xi, carry_i) in x.iter().zip(&carries) {
            let not_xi = xi.not()?;
            let half = self.xor(not_xi, false_ref);
            out.push(self.xor(half, *carry_i));
        }
        Some(out)
    }

    /// carcara `shift_add_multiplier`.
    ///
    /// Returns `None` when `y` is narrower than `x` or the width exceeds
    /// [`MAX_CIRCUIT_BITS`].
    pub(super) fn multiplier(&mut self, x: &[SRef], y: &[SRef]) -> Option<Vec<SRef>> {
        let size = x.len();
        if size > MAX_CIRCUIT_BITS || y.len() < size {
            return None;
        }
        let false_ref = self.constant(false);
        let mut shift: Vec<Vec<SRef>> = Vec::with_capacity(size);
        for (j, yj) in y.iter().take(size).enumerate() {
            let mut row = Vec::with_capacity(size);
            for i in 0..size {
                // `j <= i` exactly when `i - j` does not underflow.
                match i.checked_sub(j) {
                    Some(offset) => {
                        let xi = *x.get(offset)?;
                        row.push(self.and(vec![*yj, xi]));
                    }
                    None => row.push(false_ref),
                }
            }
            shift.push(row);
        }

        let mut res: Vec<Vec<SRef>> = Vec::with_capacity(size);
        res.push(shift.first().cloned().unwrap_or_default());

        for (j, shift_j) in shift.iter().enumerate().skip(1) {
            // `res[j - 1]`: exactly `j` rows have been pushed so far.
            let prev = res.last()?;
            let mut carry_row = Vec::with_capacity(size);
            carry_row.push(false_ref);
            for i in 1..size {
                let value = if j < i {
                    let before = i.checked_sub(1)?;
                    let prev_carry = *carry_row.last()?;
                    let res_bit = *prev.get(before)?;
                    let shift_bit = *shift_j.get(before)?;
                    let generate = self.and(vec![res_bit, shift_bit]);
                    let propagate = self.xor(res_bit, shift_bit);
                    let carried = self.and(vec![propagate, prev_carry]);
                    self.or(vec![generate, carried])
                } else {
                    false_ref
                };
                carry_row.push(value);
            }

            let mut row = Vec::with_capacity(size);
            for i in 0..size {
                let value = if i == 0 {
                    *shift.first()?.first()?
                } else if j > i {
                    *res.get(i)?.get(i)?
                } else {
                    let half = self.xor(*prev.get(i)?, *shift_j.get(i)?);
                    self.xor(half, *carry_row.get(i)?)
                };
                row.push(value);
            }
            res.push(row);
        }
        res.last().cloned()
    }

    /// carcara `bitblast_shift_op` for `bvshl` / `bvlshr` / `bvashr`.
    /// `size_bits` must be the checker's OWN spelling of the width constant's
    /// bits. The rule builds `(bvult y size)` from a freshly constructed
    /// bit-vector TERM, so `get_term_bits` projects `((_ @bit_of i) size)`
    /// from it — folding those projections to `true`/`false` here produces a
    /// different term and the rule rejects the step.
    pub(super) fn shift(
        &mut self,
        op: ShiftOp,
        x: &[SRef],
        y: &[SRef],
        size_bits: &[SRef],
    ) -> Option<Vec<SRef>> {
        let size = x.len();
        if size == 0 || y.len() != size || size_bits.len() != size {
            return None;
        }
        let y_ult_size = self.unsigned_less_than(y, size_bits)?;

        let sign_bit = *x.last()?;
        let mut res = x.to_vec();
        let k = size.ilog2() as usize + usize::from(!size.is_power_of_two());

        for (s, ys) in y.iter().copied().enumerate().take(k) {
            let previous = res.clone();
            let thresh = 1usize.checked_shl(u32::try_from(s).ok()?)?;
            for (i, slot) in res.iter_mut().enumerate() {
                let current = *previous.get(i)?;
                // `previous` holds exactly `size` bits, so the lookup ahead is
                // absent exactly when `i + thresh >= size`, and the lookup
                // behind exactly when `i < thresh`.
                let ahead = i.checked_add(thresh).and_then(|a| previous.get(a));
                *slot = match op {
                    ShiftOp::Shl => match i.checked_sub(thresh) {
                        None => {
                            let zero = self.constant(false);
                            self.ite(ys, zero, current)
                        }
                        Some(behind) => self.ite(ys, *previous.get(behind)?, current),
                    },
                    ShiftOp::LShr => match ahead {
                        None => {
                            let zero = self.constant(false);
                            self.ite(ys, zero, current)
                        }
                        Some(ahead) => {
                            let not_ys = ys.not()?;
                            self.ite(not_ys, current, *ahead)
                        }
                    },
                    ShiftOp::AShr => match ahead {
                        None => self.ite(ys, sign_bit, current),
                        Some(ahead) => {
                            let not_ys = ys.not()?;
                            self.ite(not_ys, current, *ahead)
                        }
                    },
                };
            }
        }

        // A shift by at least the width fills with zero for `bvshl`/`bvlshr`.
        // For `bvashr` the two checkers disagree (`super::super::dialect`):
        // Clean's Carcara (`third-party/carcara`, DOWNSTREAM fix 2) builds
        // `(ite y_ult_size bit sign)`, as SMT-LIB requires, and upstream
        // Carcara 9a352ee builds `(ite y_ult_size bit false)`. They denote the
        // same function only inside `arithmetic_shift_is_admissible`, which is
        // therefore the soundness precondition of the pinned spelling: the
        // pinned checker would accept a false zero-filled conclusion outside it.
        let fill = match op {
            ShiftOp::AShr if dialect::current() == AletheDialect::Clean => {
                if sign_bit.nots != 0 || self.kind(sign_bit.gate) != &GateKind::Const(false) {
                    dialect::note_clean_only(CleanOnlySpelling::SignFilledAshrOvershift);
                }
                sign_bit
            }
            ShiftOp::AShr | ShiftOp::Shl | ShiftOp::LShr => self.constant(false),
        };
        for bit in &mut res {
            *bit = self.ite(y_ult_size, *bit, fill);
        }
        Some(res)
    }
}

/// Which shift the checker's shared barrel-shifter builder is spelling.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum ShiftOp {
    Shl,
    LShr,
    AShr,
}
