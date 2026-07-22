// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Structured, replayable bit-blast proof export for the external-codegen slice fragment.
//!
//! # What this module is (C1 producer, design §9 verified-codegen loop)
//!
//! This is the **producer** half of the verified-codegen loop. It emits, for the
//! narrow QF_BV fragment the external-codegen slice needs, a fully structured bit-blast
//! refutation that a **separate, later-built consumer** (`proof-replay-consumer`) can replay
//! into a kernel `Expr` proof of type `(...) -> False` with **zero opaque `trust`
//! steps**.
//!
//! Today the rest of `ay-proof` exports a whole bit-blast as one opaque
//! `:rule trust` Alethe step (see `lib.rs::try_export_alethe`; only `LraFarkas` /
//! `LiaGeneric` are independently verifiable). [`BvBlastProof`] closes that gap for
//! the slice fragment: **every** step it emits is either a *definitional bit-lemma*
//! (a full-adder / full-subtractor relation, an XNOR equality definition) or a
//! *resolution step with named premises*. There is no `trust` variant in this
//! format — it is structurally impossible to emit one.
//!
//! # ════════════════════════════════════════════════════════════════════════
//! # No injected congruence axiom — `L_i = R_i` holds by variable identity
//! # ════════════════════════════════════════════════════════════════════════
//!
//! An earlier version of this producer bit-blasted the two syntactically-identical
//! sides to **separate** output vars `L_i`, `R_i` and then *asserted* `L_i = R_i`
//! via injected "bit-agreement" clauses `(¬L_i ∨ R_i)`, `(L_i ∨ ¬R_i)` carrying a
//! `BitAgreement` provenance tag. Those clauses were **not** derived by resolution
//! from the gate CNF — they were starting axioms whose soundness rested on a
//! congruence argument written only in a doc comment, and `validate()` accepted
//! them on the strength of two in-range lemma indices. That was a smaller-but-still-
//! opaque trust step (a "trust the per-bit congruence" axiom in clause clothing),
//! and it was the load-bearing leaf of the whole refutation.
//!
//! This producer removes that axiom at the root. The bit-blaster uses a **gate
//! cache** keyed on `(kind, ins)`: because the two sides apply identical gates to
//! identical input vars, every gate the right side would allocate is found already
//! cached from the left side, so **both sides share the same output variable**
//! `L_i ≡ R_i` by construction. `L_i = R_i` therefore holds by *variable identity*,
//! not by any clause, and the format no longer has a `BitAgreement` provenance at
//! all. The per-bit equality unit `e_i` is now derived **purely by resolution from
//! the `XnorEq` Tseitin CNF** of `e_i ⇔ ¬(L_i ⊕ L_i)` (which, with both inputs the
//! same var, are the genuine gate clauses `(e_i ∨ ¬L_i)` and `(e_i ∨ L_i)` —
//! emitted and *re-derived by `validate()` from the gate semantics*), so the
//! refutation bottoms out entirely in checked gate clauses plus the disequality.
//!
//! Trade-off, stated honestly: the two sides no longer carry *distinct* per-bit
//! lemmas; they share one. That is the correct lowering of a syntactically-identical
//! obligation and removes the only opaque step. The proof is genuinely zero-trust
//! replayable: a consumer rebuilds every output var by its (single) defining lemma
//! and replays a resolution chain whose every leaf it has itself re-checked against
//! the gate's truth table.
//!
//! # Scope (the slice fragment)
//!
//! ```text
//!   UNSAT( not( bvop(a, b) == bvop(a, b) ) )      where bvop ∈ {bvadd, bvsub, bvxor,
//!                                                  bvand, bvor, bvshl, bvlshr, bvashr},
//!                                                  1 <= width <= MAX_WIDTH (64),
//!                                                  a and b free width-bit vars
//! ```
//!
//! This is the shape of obligations like `proof_isub_i32`:
//! `not(bvsub(a,b) == bvsub(a,b))` is UNSAT because the two sides are syntactically
//! identical. The negation `not(bvadd(a,b) == bvadd(b,a))` — note `b,a` — is **SAT**
//! (commutativity is *true*, so its negation is satisfiable... actually `bvadd(a,b)
//! == bvadd(b,a)` is valid, so `not(...)` is UNSAT; the genuinely-SAT companion used
//! in tests is `not(bvsub(a,b) == bvsub(b,a))`). For any SAT / non-identical
//! obligation, [`export_bv_blast_proof`] returns
//! [`BvBlastExportError::NoRefutation`] rather than fabricating a proof.
//!
//! Width is parametric over [`1..=MAX_WIDTH`](MAX_WIDTH) (the historical slice width
//! [`SLICE_WIDTH`], `32`, remains the [`SliceObligation::identical`] default;
//! [`SliceObligation::identical_at`] picks any supported width). Different
//! operands, other ops, and non-equality predicates remain out of scope here and
//! are rejected with a typed error — the solver-backed paths
//! ([`crate::bv_blast_solver::export_bv_blast_proof_solved`] for operand-swapped
//! commutativity obligations, [`crate::bv_blast_solver::export_bv_blast_proof_expr`]
//! for arbitrary expression-tree equalities) cover those shapes.
//!
//! # ════════════════════════════════════════════════════════════════════════
//! # THE CONTRACT (what the separate proof consumer builds against)
//! # ════════════════════════════════════════════════════════════════════════
//!
//! A [`BvBlastProof`] is a self-contained, serde-serializable object. A zero-trust
//! consumer reconstructs a kernel proof of `False` from the assumption
//! `not(lhs == rhs)` by the following replay procedure, and the producer guarantees
//! every clause/lemma below is present and internally consistent
//! ([`BvBlastProof::validate`] checks this).
//!
//! ## 1. Variables ([`BvBlastProof::vars`], a [`VarTable`])
//!
//! Every Boolean variable referenced anywhere in the proof is a `u32` index
//! ("var id"). The [`VarTable`] gives each var id a [`VarRole`] explaining what
//! Boolean fact it denotes:
//!   - `InputA { bit }` / `InputB { bit }` — bit `bit` of free operand `a` / `b`.
//!   - `Out { bit }` — bit `bit` of the bit-blasted result. Because the two sides are
//!     syntactically identical the bit-blaster shares gates, so this single var is
//!     both `L_bit` and `R_bit` (`L_bit ≡ R_bit` by identity).
//!   - `BitEq { bit }` — the Tseitin variable for `lhs_bit <=> rhs_bit`.
//!   - `Aux { .. }` — an internal carry / intermediate gate output.
//!
//! The reconstructor maps each var id to a kernel `Expr : Bool`. Input vars map to
//! the corresponding extracted bit of the kernel `a` / `b`; all other vars are
//! *defined* by the lemmas in §2, so the reconstructor introduces them by `let` /
//! definitional equality and never has to trust them.
//!
//! ## 2. Bit lemmas ([`BvBlastProof::bit_lemmas`], `[BitLemma]`)
//!
//! Each [`BitLemma`] is a **definitional** relation: it states that an output var
//! equals a Boolean function of already-defined vars. The [`BitLemmaKind`] names the
//! exact gate so the reconstructor can emit the matching kernel-level definitional
//! equality:
//!   - `Xor3` — full-adder sum `a ⊕ b ⊕ cin` (also the MSB sum, carry-out discarded).
//!   - `FullAdderCarry` — `carry = (a∧b) ∨ (cin∧(a⊕b)) = MAJ(a,b,cin)`. Used for
//!     `bvadd` and (over `~b`, `cin`) `bvsub`.
//!   - `Not` — `out = ¬in` (the `~b` of two's-complement subtraction).
//!   - `ConstTrue` / `ConstFalse` — the injected subtraction carry-in `= 1`.
//!   - `XnorEq` — `out = ¬(lhs_bit ⊕ rhs_bit)`, i.e. `out <=> (lhs_bit == rhs_bit)`.
//!     These define the `BitEq` vars.
//!
//! A lemma's `out` var, together with its `kind` and ordered `ins`, is enough to
//! *derive* `out`'s truth value as a function of the inputs — no clause is trusted;
//! the consumer re-derives it.
//!
//! ## 3. Blasted clauses ([`BvBlastProof::clauses`], `[Clause]`)
//!
//! The CNF of the obligation, every clause carrying [`ClauseProvenance`]:
//!   - `BitLemmaCnf { lemma }` — a Tseitin clause that is one implication of bit
//!     lemma index `lemma`. Sound because it is entailed by that lemma's defining
//!     relation; the consumer discharges it from the lemma, not by trust.
//!     **[`BvBlastProof::validate`] re-derives the gate's full Tseitin clause set
//!     from the cited lemma's `kind`/`out`/`ins` and asserts the clause is one of
//!     them** — the provenance tag is *checked against gate semantics*, not trusted.
//!   - `Disequality` — the single clause `(¬BitEq_0 ∨ … ∨ ¬BitEq_{n-1})` coming from
//!     `not(lhs == rhs)`: at least one bit differs.
//!
//! Each clause has a stable `id` (its index) used as a resolution premise name.
//!
//! ## 4. SAT refutation ([`BvBlastProof::refutation`], a [`Refutation`])
//!
//! A list of [`ResolutionStep`]s. Each step has an `id`, a derived `clause`, a
//! `rule` ([`ResRule::Resolution`] only — **never** trust), and named `premises`
//! (ids of earlier clauses or steps) plus the `pivot` variable resolved on. The
//! chain is checkable: applying resolution to the premises on the pivot yields
//! exactly the step's clause, and the final step's clause is **empty** (the empty
//! clause = `False`). [`BvBlastProof::validate`] re-runs every resolution and
//! confirms the last derived clause is empty. A consumer that trusts nothing simply
//! replays the same chain at the kernel level.
//!
//! ## Soundness summary for the consumer
//!
//! The producer asserts nothing the consumer must believe blindly:
//!   * input vars ↦ kernel bit-extracts (definitional),
//!   * every non-input var is introduced by a bit lemma (definitional equality),
//!   * every clause is either a bit-lemma Tseitin implication (re-derived from the
//!     gate truth table by `validate()`, entailed by §2) or the one disequality
//!     clause (entailed by the assumption `not(lhs==rhs)`),
//!   * the resolution chain (§4) is locally checkable and ends in `False`.
//!
//! Therefore replaying the object yields `(not(lhs==rhs)) -> False` with no trust.
//!
//! # Honesty note on provenance of the refutation
//!
//! The resolution chain in §4 is **constructed directly by this producer** for the
//! identical-operand slice, not lifted out of the CDCL SAT engine's DRAT/LRAT
//! chain: that case is a fully determined one-resolution-per-bit shortcut, so
//! constructing it is sound, deterministic, and minimal. The historical reason
//! this was the *only* option — `ay-sat` exposing its refutation solely as a
//! file-emission LRAT byte stream — no longer holds:
//! [`ay_sat::prove_unsat_resolution_dag`] surfaces the solver's own refutation as
//! an in-memory resolution/RUP DAG, and the solver-backed producers in
//! [`crate::bv_blast_solver`] (operand-swap and expression-tree paths) already
//! carry that genuinely CDCL-derived chain through this same [`BvBlastProof`]
//! format (route (b) of the verified-codegen loop; the route-b CNF entry point
//! consumed by external-codegen is `ay-sat`'s feature-gated `prove_cnf_unsat_dimacs`).

use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;

/// The historical (and default) slice-fragment width. Kept as the
/// [`SliceObligation::identical`] default; the producer itself accepts any
/// width in [`1..=MAX_WIDTH`](MAX_WIDTH).
pub const SLICE_WIDTH: u32 = 32;

/// Largest width [`export_bv_blast_proof`] accepts. Matches the solver-backed
/// paths' [`crate::bv_blast_solver::SOLVED_MAX_WIDTH`]: bounded so the var-id
/// space stays comfortably within the `u32` ids the [`BvBlastProof`] format
/// uses (a width-64 barrel shifter allocates ~1.7k gate vars).
pub const MAX_WIDTH: u32 = 64;

/// The bit-vector operation of a slice obligation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum BvOp {
    /// `bvadd` — two's-complement ripple-carry addition.
    Add,
    /// `bvsub` — two's-complement subtraction `a + ~b + 1`.
    Sub,
    /// `bvxor` — bitwise exclusive-or (per-bit `out_i = a_i ⊕ b_i`, no carry).
    Xor,
    /// `bvand` — bitwise and (per-bit `out_i = a_i ∧ b_i`, no carry).
    And,
    /// `bvor` — bitwise or (per-bit `out_i = a_i ∨ b_i`, no carry).
    Or,
    /// `bvshl` — logical shift left by a variable amount (barrel shifter).
    Shl,
    /// `bvlshr` — logical shift right by a variable amount (barrel shifter).
    Lshr,
    /// `bvashr` — arithmetic shift right by a variable amount (barrel shifter).
    Ashr,
}

impl BvOp {
    /// SMT-LIB symbol name.
    #[must_use]
    pub const fn smt_name(self) -> &'static str {
        match self {
            Self::Add => "bvadd",
            Self::Sub => "bvsub",
            Self::Xor => "bvxor",
            Self::And => "bvand",
            Self::Or => "bvor",
            Self::Shl => "bvshl",
            Self::Lshr => "bvlshr",
            Self::Ashr => "bvashr",
        }
    }
}

/// A slice-fragment proof obligation: `UNSAT( not( bvop(a,b) == bvop(c,d) ) )`.
///
/// The operands are named by index into a notional pair of free `width`-bit
/// variables `a` (index 0) and `b` (index 1). The producer only proves the case
/// where the left and right applications are *syntactically identical*
/// (`lhs_args == rhs_args`); other cases are SAT or out of scope and yield
/// [`BvBlastExportError`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SliceObligation {
    /// Bit width ([`1..=MAX_WIDTH`](MAX_WIDTH)).
    pub width: u32,
    /// The bit-vector operation applied on both sides.
    pub op: BvOp,
    /// Operand indices for the left-hand application, e.g. `[0, 1]` for `op(a, b)`.
    pub lhs_args: [OperandRef; 2],
    /// Operand indices for the right-hand application.
    pub rhs_args: [OperandRef; 2],
}

/// Reference to one of the two free operands.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum OperandRef {
    /// Free 32-bit variable `a`.
    A,
    /// Free 32-bit variable `b`.
    B,
}

impl OperandRef {
    const fn name(self) -> &'static str {
        match self {
            Self::A => "a",
            Self::B => "b",
        }
    }
}

impl SliceObligation {
    /// Construct the canonical `not(op(a,b) == op(a,b))` obligation at the
    /// default width [`SLICE_WIDTH`].
    #[must_use]
    pub const fn identical(op: BvOp) -> Self {
        Self::identical_at(op, SLICE_WIDTH)
    }

    /// Construct the `not(op(a,b) == op(a,b))` obligation at an explicit
    /// `width` (validated against [`1..=MAX_WIDTH`](MAX_WIDTH) by
    /// [`export_bv_blast_proof`]).
    #[must_use]
    pub const fn identical_at(op: BvOp, width: u32) -> Self {
        Self {
            width,
            op,
            lhs_args: [OperandRef::A, OperandRef::B],
            rhs_args: [OperandRef::A, OperandRef::B],
        }
    }

    /// True iff the two applications are syntactically identical (the only shape
    /// that is UNSAT and thus refutable by this producer).
    #[must_use]
    pub fn is_identical(&self) -> bool {
        self.lhs_args == self.rhs_args
    }

    /// Render the asserted (negated) formula in SMT-LIB syntax for documentation.
    #[must_use]
    pub fn render_smt(&self) -> String {
        let op = self.op.smt_name();
        format!(
            "(not (= ({op} {} {}) ({op} {} {})))",
            self.lhs_args[0].name(),
            self.lhs_args[1].name(),
            self.rhs_args[0].name(),
            self.rhs_args[1].name(),
        )
    }
}

/// The semantic role of a Boolean variable referenced in a [`BvBlastProof`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum VarRole {
    /// Bit `bit` of free operand `a`.
    InputA {
        /// Bit position (LSB = 0).
        bit: u32,
    },
    /// Bit `bit` of free operand `b`.
    InputB {
        /// Bit position (LSB = 0).
        bit: u32,
    },
    /// Bit `bit` of the bit-blasted result.
    ///
    /// Because the slice fragment's two sides are syntactically identical and the
    /// bit-blaster shares gates via a cache, the left and right output bits are the
    /// **same** variable; this single role denotes both `L_bit` and `R_bit`.
    Out {
        /// Bit position (LSB = 0).
        bit: u32,
    },
    /// Tseitin variable for `lhs_bit <=> rhs_bit` at bit `bit`.
    BitEq {
        /// Bit position (LSB = 0).
        bit: u32,
    },
    /// An internal carry / intermediate gate output.
    Aux {
        /// Bit position the auxiliary is associated with.
        bit: u32,
    },
    /// The adder carry-in: constant `true` for `bvsub`
    /// (two's complement `a + ~b + 1`), constant `false` for `bvadd`.
    CarryIn,
    /// A `~b` bit produced by subtraction's one's-complement.
    NotB {
        /// Bit position (LSB = 0).
        bit: u32,
    },
    /// Bit `bit` of the **left** side's bit-blasted result, used by the
    /// solver-backed non-identical path where the two sides do not share gates.
    LhsOut {
        /// Bit position (LSB = 0).
        bit: u32,
    },
    /// Bit `bit` of the **right** side's bit-blasted result (non-identical path).
    RhsOut {
        /// Bit position (LSB = 0).
        bit: u32,
    },
    /// Internal carry/intermediate of the **left** side (non-identical path).
    LhsAux {
        /// Bit position the auxiliary is associated with.
        bit: u32,
    },
    /// Internal carry/intermediate of the **right** side (non-identical path).
    RhsAux {
        /// Bit position the auxiliary is associated with.
        bit: u32,
    },
    /// The carry-in of the **right** side adder (non-identical path).
    RhsCarryIn,
    /// A `~b` bit of the **right** side's subtraction (non-identical path).
    RhsNotB {
        /// Bit position (LSB = 0).
        bit: u32,
    },
    /// Bit `bit` of a general named free input leaf `leaf`, used by the
    /// expression-tree path ([`crate::bv_blast_solver::export_bv_blast_proof_expr`]).
    /// Unlike [`VarRole::InputA`]/[`VarRole::InputB`] (which name a notional pair
    /// `a`/`b`), this names one of arbitrarily many BV leaves by a stable index so
    /// the same leaf referenced on both sides shares the same input vars.
    InputLeaf {
        /// Stable index of the named leaf (assigned in first-seen order).
        leaf: u32,
        /// Bit position (LSB = 0).
        bit: u32,
    },
}

/// Maps each Boolean variable id used in the proof to its semantic [`VarRole`].
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct VarTable {
    /// `roles[i]` is the role of variable id `i`. Dense, 0-based.
    pub roles: Vec<VarRole>,
}

impl VarTable {
    pub(crate) fn alloc(&mut self, role: VarRole) -> u32 {
        let id = self.roles.len() as u32;
        self.roles.push(role);
        id
    }

    /// Number of variables.
    #[must_use]
    pub fn len(&self) -> usize {
        self.roles.len()
    }

    /// True when no variables are registered.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.roles.is_empty()
    }
}

/// The gate denoted by a [`BitLemma`] — names the exact definitional relation the
/// reconstructor must reproduce at the kernel level.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum BitLemmaKind {
    /// `out = in0 ⊕ in1` (XOR of two inputs).
    Xor2,
    /// `out = in0 ∧ in1` (AND of two inputs).
    And2,
    /// `out = in0 ∨ in1` (OR of two inputs).
    Or2,
    /// `out = in0 ⊕ in1 ⊕ in2` (sum of a full adder / MSB xor3).
    Xor3,
    /// `out = (in0 ∧ in1) ∨ (in2 ∧ (in0 ⊕ in1))` (carry of a full adder).
    FullAdderCarry,
    /// `out = ¬in0`.
    Not,
    /// `out = true` (injected constant; no inputs).
    ConstTrue,
    /// `out = false` (no inputs).
    ConstFalse,
    /// `out = ¬(in0 ⊕ in1)` — bit-equality (XNOR), defines a `BitEq` var.
    XnorEq,
}

impl BitLemmaKind {
    /// Expected number of input variables for this gate.
    #[must_use]
    pub const fn arity(self) -> usize {
        match self {
            Self::ConstTrue | Self::ConstFalse => 0,
            Self::Not => 1,
            Self::Xor2 | Self::And2 | Self::Or2 | Self::XnorEq => 2,
            Self::Xor3 | Self::FullAdderCarry => 3,
        }
    }
}

/// A definitional bit-blasting lemma: `out` equals `kind(ins...)`.
///
/// This is the *only* kind of "axiom" in the proof, and it is not trusted: it is a
/// definition the consumer re-introduces as a kernel definitional equality.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BitLemma {
    /// Stable id (index into [`BvBlastProof::bit_lemmas`]).
    pub id: u32,
    /// The gate relation.
    pub kind: BitLemmaKind,
    /// Defined output variable id.
    pub out: u32,
    /// Ordered input variable ids (length must equal `kind.arity()`).
    pub ins: Vec<u32>,
}

/// A Boolean literal: `(var, negated)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct Lit {
    /// Variable id.
    pub var: u32,
    /// True if the literal is the negation of `var`.
    pub neg: bool,
}

impl Lit {
    /// Positive literal `var`.
    #[must_use]
    pub const fn pos(var: u32) -> Self {
        Self { var, neg: false }
    }
    /// Negative literal `¬var`.
    #[must_use]
    pub const fn neg(var: u32) -> Self {
        Self { var, neg: true }
    }
    /// The complementary literal.
    #[must_use]
    pub const fn negated(self) -> Self {
        Self {
            var: self.var,
            neg: !self.neg,
        }
    }
}

/// Why a CNF clause is sound (its derivation source).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ClauseProvenance {
    /// One Tseitin implication of bit lemma `lemma`; entailed by that lemma.
    ///
    /// [`BvBlastProof::validate`] re-derives the gate's full Tseitin clause set from
    /// the cited lemma and asserts this clause is one of them, so the tag is checked
    /// against gate semantics rather than trusted.
    BitLemmaCnf {
        /// Index into [`BvBlastProof::bit_lemmas`].
        lemma: u32,
    },
    /// The single disequality clause from `not(lhs == rhs)`.
    Disequality,
}

/// A CNF clause with provenance.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Clause {
    /// Stable id (index into [`BvBlastProof::clauses`]), usable as a resolution premise.
    pub id: u32,
    /// The clause literals (a disjunction).
    pub lits: Vec<Lit>,
    /// Why this clause is sound.
    pub provenance: ClauseProvenance,
}

/// The inference rule of a [`ResolutionStep`]. There is intentionally **no** trust
/// variant: this enum cannot encode an opaque step.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ResRule {
    /// Binary resolution on the recorded pivot variable.
    Resolution,
}

/// One resolution step in the SAT refutation.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ResolutionStep {
    /// Stable id; resolution-step ids are namespaced after clause ids
    /// (`id >= clauses.len()`), so a premise id unambiguously names a clause or step.
    pub id: u32,
    /// The derived clause.
    pub clause: Vec<Lit>,
    /// Always [`ResRule::Resolution`].
    pub rule: ResRule,
    /// Ids of the two premises (clauses or earlier steps).
    pub premises: [u32; 2],
    /// The variable resolved upon.
    pub pivot: u32,
}

/// The SAT refutation: a resolution chain ending in the empty clause.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Refutation {
    /// Ordered resolution steps; the last step's clause is empty.
    pub steps: Vec<ResolutionStep>,
}

/// A complete, zero-trust, replayable bit-blast refutation for a slice obligation.
///
/// See the module-level docs for the full contract. Use [`BvBlastProof::validate`]
/// to confirm well-formedness (every clause has a derivation, the resolution chain
/// is locally sound and ends in the empty clause, no opaque step exists).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BvBlastProof {
    /// Format version (bump on breaking changes to the contract).
    pub format_version: u32,
    /// The obligation this proof refutes.
    pub obligation: SliceObligation,
    /// SMT-LIB rendering of the asserted (negated) formula, for human/debug use.
    pub asserted_smt: String,
    /// Variable table (var id -> role).
    pub vars: VarTable,
    /// Definitional bit lemmas.
    pub bit_lemmas: Vec<BitLemma>,
    /// CNF clauses with provenance.
    pub clauses: Vec<Clause>,
    /// The resolution refutation.
    pub refutation: Refutation,
}

/// Current [`BvBlastProof::format_version`].
pub const FORMAT_VERSION: u32 = 1;

/// Errors from [`export_bv_blast_proof`].
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum BvBlastExportError {
    /// The obligation width is zero or exceeds the supported range.
    #[error("unsupported width {got}: slice fragment supports 1..={max}")]
    UnsupportedWidth {
        /// Width seen.
        got: u32,
        /// Maximum supported width ([`MAX_WIDTH`]).
        max: u32,
    },
    /// The obligation is SAT (or otherwise not refutable by this producer): the
    /// left and right applications differ, so `not(lhs == rhs)` has a model. No
    /// proof is fabricated.
    #[error("no refutation: obligation is SAT or non-identical ({reason})")]
    NoRefutation {
        /// Human-readable reason.
        reason: String,
    },
}

/// Errors from [`BvBlastProof::validate`].
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum BvBlastValidateError {
    /// A variable id referenced somewhere is not in the [`VarTable`].
    #[error("variable id {0} out of range")]
    UndefinedVar(u32),
    /// A bit lemma's input arity does not match its kind.
    #[error("bit lemma {id} (kind {kind:?}) expects {expected} inputs, got {got}")]
    BadLemmaArity {
        /// Lemma id.
        id: u32,
        /// Lemma kind.
        kind: BitLemmaKind,
        /// Expected arity.
        expected: usize,
        /// Actual arity.
        got: usize,
    },
    /// A clause cites a bit lemma index that does not exist.
    #[error("clause {clause} cites missing bit lemma {lemma}")]
    MissingLemma {
        /// Clause id.
        clause: u32,
        /// Cited lemma index.
        lemma: u32,
    },
    /// A `BitLemmaCnf` clause's literals are not one of the Tseitin clauses entailed
    /// by the cited lemma's gate over its declared `out`/`ins` variables. This is the
    /// leaf-clause semantic check: provenance is verified against gate truth, not
    /// accepted as a label.
    #[error(
        "clause {clause}: literals are not a Tseitin clause of cited lemma {lemma} \
         (kind {kind:?}); provenance does not match gate semantics"
    )]
    ClauseNotEntailed {
        /// Clause id.
        clause: u32,
        /// Cited lemma index.
        lemma: u32,
        /// The cited lemma's gate kind.
        kind: BitLemmaKind,
    },
    /// A clause id is not equal to its position (ids must be dense / canonical).
    #[error("clause at index {index} has non-canonical id {id}")]
    NonCanonicalClauseId {
        /// Position.
        index: usize,
        /// Recorded id.
        id: u32,
    },
    /// A resolution step references a premise id that names nothing.
    #[error("step {step} references unknown premise {premise}")]
    UnknownPremise {
        /// Step id.
        step: u32,
        /// Bad premise id.
        premise: u32,
    },
    /// Applying resolution to a step's premises did not yield its recorded clause.
    #[error("step {step}: resolution result does not match recorded clause")]
    ResolutionMismatch {
        /// Step id.
        step: u32,
    },
    /// The refutation does not end in the empty clause.
    #[error("refutation does not end in the empty clause (last clause has {0} literals)")]
    NotEmptyClause(usize),
    /// The refutation has no steps at all.
    #[error("refutation is empty")]
    EmptyRefutation,
}

impl BvBlastProof {
    /// Validate well-formedness against the contract.
    ///
    /// Checks: all referenced var ids exist; every bit lemma has correct arity;
    /// every clause has a real provenance (an existing bit lemma, or the
    /// disequality); clause ids are canonical; every resolution step's premises
    /// exist and the recorded clause is exactly the resolvent of its premises on
    /// the pivot; and the final derived clause is empty. No step may be opaque
    /// (the [`ResRule`] enum cannot express one).
    ///
    /// # Errors
    /// Returns the first [`BvBlastValidateError`] encountered.
    pub fn validate(&self) -> Result<(), BvBlastValidateError> {
        let nvars = self.vars.len() as u32;
        let check_var = |v: u32| -> Result<(), BvBlastValidateError> {
            if v < nvars {
                Ok(())
            } else {
                Err(BvBlastValidateError::UndefinedVar(v))
            }
        };

        // 1. Bit lemmas: arity + var references.
        for lem in &self.bit_lemmas {
            let expected = lem.kind.arity();
            if lem.ins.len() != expected {
                return Err(BvBlastValidateError::BadLemmaArity {
                    id: lem.id,
                    kind: lem.kind,
                    expected,
                    got: lem.ins.len(),
                });
            }
            check_var(lem.out)?;
            for &i in &lem.ins {
                check_var(i)?;
            }
        }

        // 2. Clauses: canonical ids, provenance resolves, var references.
        for (idx, cl) in self.clauses.iter().enumerate() {
            if cl.id as usize != idx {
                return Err(BvBlastValidateError::NonCanonicalClauseId {
                    index: idx,
                    id: cl.id,
                });
            }
            for lit in &cl.lits {
                check_var(lit.var)?;
            }
            match cl.provenance {
                ClauseProvenance::BitLemmaCnf { lemma } => {
                    let Some(lem) = self.bit_lemmas.get(lemma as usize) else {
                        return Err(BvBlastValidateError::MissingLemma {
                            clause: cl.id,
                            lemma,
                        });
                    };
                    // Leaf-clause semantic check: the clause must be one of the
                    // Tseitin clauses entailed by this gate over its own out/ins.
                    // This re-derives gate semantics from scratch — the provenance
                    // tag is verified, not believed. A clause with arbitrary literals
                    // that merely cites an in-range lemma is rejected here.
                    let generated = tseitin_clauses(lem.kind, lem.out, &lem.ins);
                    if !generated.iter().any(|g| clause_set_eq(g, &cl.lits)) {
                        return Err(BvBlastValidateError::ClauseNotEntailed {
                            clause: cl.id,
                            lemma,
                            kind: lem.kind,
                        });
                    }
                }
                ClauseProvenance::Disequality => {}
            }
        }

        // 3. Resolution chain. Premise id space: [0, clauses.len()) are clauses,
        //    [clauses.len(), ...) are steps in order.
        let nclauses = self.clauses.len() as u32;
        if self.refutation.steps.is_empty() {
            return Err(BvBlastValidateError::EmptyRefutation);
        }
        let lookup = |id: u32, upto_step: usize| -> Option<Vec<Lit>> {
            if id < nclauses {
                return Some(self.clauses[id as usize].lits.clone());
            }
            let step_idx = (id - nclauses) as usize;
            if step_idx < upto_step {
                Some(self.refutation.steps[step_idx].clause.clone())
            } else {
                None
            }
        };

        for (i, step) in self.refutation.steps.iter().enumerate() {
            for &p in &step.premises {
                if lookup(p, i).is_none() {
                    return Err(BvBlastValidateError::UnknownPremise {
                        step: step.id,
                        premise: p,
                    });
                }
            }
            check_var(step.pivot)?;
            let a = lookup(step.premises[0], i).expect("checked above");
            let b = lookup(step.premises[1], i).expect("checked above");
            let got = resolve(&a, &b, step.pivot);
            match got {
                Some(resolvent) if clause_set_eq(&resolvent, &step.clause) => {}
                _ => return Err(BvBlastValidateError::ResolutionMismatch { step: step.id }),
            }
        }

        let last = self
            .refutation
            .steps
            .last()
            .expect("non-empty checked above");
        if !last.clause.is_empty() {
            return Err(BvBlastValidateError::NotEmptyClause(last.clause.len()));
        }
        Ok(())
    }
}

/// Resolve clauses `a` and `b` on `pivot`. Requires `pivot` appear positively in
/// one and negatively in the other; returns the resolvent (deduplicated), or `None`
/// if the pivot is not a clean resolution pivot or the result is tautological.
fn resolve(a: &[Lit], b: &[Lit], pivot: u32) -> Option<Vec<Lit>> {
    let a_has_pos = a.contains(&Lit::pos(pivot));
    let a_has_neg = a.contains(&Lit::neg(pivot));
    let b_has_pos = b.contains(&Lit::pos(pivot));
    let b_has_neg = b.contains(&Lit::neg(pivot));

    // Exactly one polarity of the pivot in each, opposite across the two clauses.
    let valid = (a_has_pos && b_has_neg && !a_has_neg && !b_has_pos)
        || (a_has_neg && b_has_pos && !a_has_pos && !b_has_neg);
    if !valid {
        return None;
    }

    let mut out: Vec<Lit> = Vec::new();
    let mut seen: BTreeSet<Lit> = BTreeSet::new();
    for &l in a.iter().chain(b.iter()) {
        if l.var == pivot {
            continue;
        }
        // Tautology check: pivot-free complementary literals make a useless resolvent.
        if seen.contains(&l.negated()) {
            return None;
        }
        if seen.insert(l) {
            out.push(l);
        }
    }
    Some(out)
}

/// Order-insensitive, duplicate-insensitive clause equality.
fn clause_set_eq(a: &[Lit], b: &[Lit]) -> bool {
    let sa: BTreeSet<Lit> = a.iter().copied().collect();
    let sb: BTreeSet<Lit> = b.iter().copied().collect();
    sa == sb
}

/// Build a structured bit-blast refutation for a slice obligation.
///
/// # Behavior
///
/// * Width must be in [`1..=MAX_WIDTH`](MAX_WIDTH). Otherwise
///   [`BvBlastExportError::UnsupportedWidth`].
/// * The obligation must be *identical-operand* (`lhs_args == rhs_args`). Only then
///   is `not(lhs == rhs)` UNSAT. For any non-identical obligation (e.g.
///   `not(bvsub(a,b) == bvsub(b,a))`, which is SAT) this returns
///   [`BvBlastExportError::NoRefutation`] — **no bogus proof is produced**.
///
/// # Why the refutation is built here, not surfaced from `ay-sat`
///
/// For the identical-operand slice the refutation is short and fully determined
/// by the bit-blast structure (one gate-clause resolution per bit, then peel the
/// disequality), so this producer builds it constructively: deterministic,
/// minimal, and independent of solver search order. Obligations whose refutation
/// genuinely needs CDCL search take the solver-backed paths in
/// [`crate::bv_blast_solver`], which lift the engine's own chain through
/// [`ay_sat::prove_unsat_resolution_dag`] into this same [`BvBlastProof`] format
/// (see the module-level honesty note).
///
/// # Errors
/// See [`BvBlastExportError`].
pub fn export_bv_blast_proof(
    obligation: SliceObligation,
) -> Result<BvBlastProof, BvBlastExportError> {
    if obligation.width == 0 || obligation.width > MAX_WIDTH {
        return Err(BvBlastExportError::UnsupportedWidth {
            got: obligation.width,
            max: MAX_WIDTH,
        });
    }
    if !obligation.is_identical() {
        return Err(BvBlastExportError::NoRefutation {
            reason: format!(
                "left/right applications differ: {} vs {} — not(lhs==rhs) is satisfiable",
                fmt_args(&obligation.lhs_args),
                fmt_args(&obligation.rhs_args),
            ),
        });
    }

    let n = obligation.width;
    let mut vars = VarTable::default();
    let mut bit_lemmas: Vec<BitLemma> = Vec::new();
    let mut clauses: Vec<Clause> = Vec::new();

    // --- Input bits a[0..n], b[0..n] (free) ---
    let a_bits: Vec<u32> = (0..n)
        .map(|bit| vars.alloc(VarRole::InputA { bit }))
        .collect();
    let b_bits: Vec<u32> = (0..n)
        .map(|bit| vars.alloc(VarRole::InputB { bit }))
        .collect();

    // --- Bit-blast the (single, shared) result. --------------------------------
    // The two sides are syntactically identical, so a gate cache keyed on
    // `(kind, ins)` fuses every gate: the right side's gates are all found already
    // built from the left side, and both sides reference the SAME output variable
    // `L_i ≡ R_i`. `L_i = R_i` therefore holds by variable identity — there is no
    // congruence axiom and no `BitAgreement` clause. (See the module header.)
    let mut cache = GateCache::default();
    let out = blast_side(
        obligation.op,
        &a_bits,
        &b_bits,
        &mut vars,
        &mut bit_lemmas,
        &mut clauses,
        &mut cache,
    );

    // --- Per-bit equality vars E_i = (L_i <=> R_i) via XnorEq lemmas + Tseitin CNF. ---
    // Because `L_i ≡ R_i` is one variable `l`, the XnorEq gate is `e ⇔ ¬(l ⊕ l)`,
    // whose Tseitin CNF (generated and re-validated from the gate truth table) is
    // exactly the two non-tautological clauses `(e ∨ ¬l)` and `(e ∨ l)`. From those
    // two the unit `e_i` follows by a single resolution on `l` — no agreement axiom.
    let mut eq_vars: Vec<u32> = Vec::with_capacity(n as usize);
    // Per bit: the ids of the two XnorEq gate clauses `[(e∨¬l), (e∨l)]`.
    let mut xnor_clauses: Vec<[u32; 2]> = Vec::with_capacity(n as usize);
    for (bit, &l) in out.iter().enumerate() {
        let e = vars.alloc(VarRole::BitEq { bit: bit as u32 });
        eq_vars.push(e);
        let lemma_id = bit_lemmas.len() as u32;
        let ins = vec![l, l];
        bit_lemmas.push(BitLemma {
            id: lemma_id,
            kind: BitLemmaKind::XnorEq,
            out: e,
            ins: ins.clone(),
        });
        // Emit the gate's Tseitin CNF straight from the shared generator: with both
        // inputs the same var this yields the two units below (tautologies dropped).
        let emitted = push_gate_cnf(&mut clauses, BitLemmaKind::XnorEq, e, &ins, lemma_id);
        debug_assert_eq!(
            emitted.len(),
            2,
            "XnorEq(l,l) has 2 non-tautological clauses"
        );
        let id_e_nl = find_clause_id(&clauses, &[Lit::pos(e), Lit::neg(l)])
            .expect("XnorEq(l,l) clause (e∨¬l) must exist");
        let id_e_l = find_clause_id(&clauses, &[Lit::pos(e), Lit::pos(l)])
            .expect("XnorEq(l,l) clause (e∨l) must exist");
        xnor_clauses.push([id_e_nl, id_e_l]);
    }

    // --- The disequality clause from not(lhs == rhs): at least one bit differs. ---
    //   not( AND_i e_i )  ==  (¬e_0 ∨ ¬e_1 ∨ ... ∨ ¬e_{n-1})
    let diseq_id = clauses.len() as u32;
    clauses.push(Clause {
        id: diseq_id,
        lits: eq_vars.iter().map(|&e| Lit::neg(e)).collect(),
        provenance: ClauseProvenance::Disequality,
    });

    // --- Resolution refutation. -------------------------------------------------
    // For each bit i, derive the unit `e_i` by resolving the two XnorEq gate clauses
    // on the shared output var `l`:
    //   e_i = res( (e ∨ ¬l), (e ∨ l), pivot = l )
    // Then resolve every `e_i` unit into the disequality clause to reach the empty
    // clause. Every step is binary resolution with named premises; no trust, and
    // every premise bottoms out in a gate Tseitin clause or the disequality clause.
    let nclauses = clauses.len() as u32;
    let mut steps: Vec<ResolutionStep> = Vec::new();
    let mut next_step_id = nclauses;
    let mut unit_eq_step_ids: Vec<u32> = Vec::with_capacity(n as usize);

    for (bit, &l) in out.iter().enumerate() {
        let e = eq_vars[bit];
        // e_i = res( (e ∨ ¬l), (e ∨ l), l ) = (e)
        let unit = next_step_id;
        next_step_id += 1;
        steps.push(ResolutionStep {
            id: unit,
            clause: vec![Lit::pos(e)],
            rule: ResRule::Resolution,
            premises: xnor_clauses[bit],
            pivot: l,
        });
        unit_eq_step_ids.push(unit);
    }

    // Resolve each unit e_i against the disequality clause, peeling off one ¬e_i
    // at a time until the empty clause remains.
    let mut current = diseq_id; // start from the disequality clause id
    for (k, &unit_step) in unit_eq_step_ids.iter().enumerate() {
        let e = eq_vars[k];
        // remaining literals after removing e_0..e_k
        let remaining: Vec<Lit> = eq_vars[(k + 1)..].iter().map(|&ev| Lit::neg(ev)).collect();
        let step_id = next_step_id;
        next_step_id += 1;
        steps.push(ResolutionStep {
            id: step_id,
            clause: remaining,
            rule: ResRule::Resolution,
            premises: [current, unit_step],
            pivot: e,
        });
        current = step_id;
    }

    let refutation = Refutation { steps };

    let proof = BvBlastProof {
        format_version: FORMAT_VERSION,
        obligation,
        asserted_smt: obligation.render_smt(),
        vars,
        bit_lemmas,
        clauses,
        refutation,
    };
    Ok(proof)
}

fn fmt_args(args: &[OperandRef; 2]) -> String {
    format!("[{}, {}]", args[0].name(), args[1].name())
}

pub(crate) fn find_clause_id(clauses: &[Clause], lits: &[Lit]) -> Option<u32> {
    clauses
        .iter()
        .find(|c| clause_set_eq(&c.lits, lits))
        .map(|c| c.id)
}

/// Caches built gates by `(kind, ins)` so syntactically-identical gates (e.g. the
/// "two" sides of an identical-operand obligation) **share** one output variable and
/// one defining lemma. This is what makes `L_i ≡ R_i` true by variable identity and
/// removes any need for an injected congruence/agreement axiom.
#[derive(Default)]
pub(crate) struct GateCache {
    entries: std::collections::HashMap<(BitLemmaKind, Vec<u32>), u32>,
}

impl GateCache {
    pub(crate) fn get(&self, kind: BitLemmaKind, ins: &[u32]) -> Option<u32> {
        self.entries.get(&(kind, ins.to_vec())).copied()
    }
    pub(crate) fn put(&mut self, kind: BitLemmaKind, ins: Vec<u32>, out: u32) {
        self.entries.insert((kind, ins), out);
    }
}

/// Build (or reuse) a gate `out = kind(ins...)`: allocate the output var with `role`,
/// record the [`BitLemma`], and emit its Tseitin CNF via the shared generator. If an
/// identical gate is already cached, returns the existing output var and emits
/// nothing new.
#[allow(clippy::too_many_arguments)]
pub(crate) fn build_gate(
    kind: BitLemmaKind,
    ins: Vec<u32>,
    role: VarRole,
    vars: &mut VarTable,
    bit_lemmas: &mut Vec<BitLemma>,
    clauses: &mut Vec<Clause>,
    cache: &mut GateCache,
) -> u32 {
    if let Some(out) = cache.get(kind, &ins) {
        return out;
    }
    let out = vars.alloc(role);
    let lemma_id = bit_lemmas.len() as u32;
    bit_lemmas.push(BitLemma {
        id: lemma_id,
        kind,
        out,
        ins: ins.clone(),
    });
    push_gate_cnf(clauses, kind, out, &ins, lemma_id);
    cache.put(kind, ins, out);
    out
}

/// Bit-blast `bvadd` / `bvsub` over the shared input bits, allocating output /
/// auxiliary variables and recording the corresponding bit lemmas. Returns the `n`
/// output variable ids (LSB first).
///
/// This mirrors `ay-bv`'s `bitblast_add` / `bitblast_sub` (full adder per bit, xor3
/// at the MSB; subtraction = `a + ~b + 1`). Gates are built through [`GateCache`], so
/// the identical-operand obligation's two sides reference the same output vars.
fn blast_side(
    op: BvOp,
    a_bits: &[u32],
    b_bits: &[u32],
    vars: &mut VarTable,
    bit_lemmas: &mut Vec<BitLemma>,
    clauses: &mut Vec<Clause>,
    cache: &mut GateCache,
) -> Vec<u32> {
    let n = a_bits.len();

    // Variable-amount shifts use a barrel shifter (own gate topology).
    if matches!(op, BvOp::Shl | BvOp::Lshr | BvOp::Ashr) {
        return blast_shift(op, a_bits, b_bits, vars, bit_lemmas, clauses, cache);
    }

    // Bitwise XOR / AND / OR: per-bit single 2-input gate, NO carry chain (different
    // gate-fidelity than the ripple-carry adder). `op(a,b)` and `op(b,a)` use the
    // same `GateCache`, so the identical-operand obligation collapses cleanly.
    let bitwise_gate = match op {
        BvOp::Xor => Some(BitLemmaKind::Xor2),
        BvOp::And => Some(BitLemmaKind::And2),
        BvOp::Or => Some(BitLemmaKind::Or2),
        // Add/Sub fall through to the ripple-carry adder; shifts handled above.
        BvOp::Add | BvOp::Sub | BvOp::Shl | BvOp::Lshr | BvOp::Ashr => None,
    };
    if let Some(gate) = bitwise_gate {
        return (0..n)
            .map(|bit| {
                build_gate(
                    gate,
                    vec![a_bits[bit], b_bits[bit]],
                    VarRole::Out { bit: bit as u32 },
                    vars,
                    bit_lemmas,
                    clauses,
                    cache,
                )
            })
            .collect();
    }

    // For subtraction: operand2 = ~b, carry-in = 1.  For addition: operand2 = b,
    // carry-in = 0 (modelled uniformly with a ConstFalse cin for lemma clarity).
    let (op2_bits, cin): (Vec<u32>, u32) = if matches!(op, BvOp::Sub) {
        let notb: Vec<u32> = b_bits
            .iter()
            .enumerate()
            .map(|(bit, &b)| {
                build_gate(
                    BitLemmaKind::Not,
                    vec![b],
                    VarRole::NotB { bit: bit as u32 },
                    vars,
                    bit_lemmas,
                    clauses,
                    cache,
                )
            })
            .collect();
        let t = build_gate(
            BitLemmaKind::ConstTrue,
            vec![],
            VarRole::CarryIn,
            vars,
            bit_lemmas,
            clauses,
            cache,
        );
        (notb, t)
    } else {
        let f = build_gate(
            BitLemmaKind::ConstFalse,
            vec![],
            VarRole::CarryIn,
            vars,
            bit_lemmas,
            clauses,
            cache,
        );
        (b_bits.to_vec(), f)
    };

    let mut out = Vec::with_capacity(n);
    let mut carry = cin;
    for bit in 0..n {
        let a = a_bits[bit];
        let b2 = op2_bits[bit];
        // sum = a ⊕ b2 ⊕ carry (Xor3); carry-out only needed for non-MSB bits.
        let o = build_gate(
            BitLemmaKind::Xor3,
            vec![a, b2, carry],
            VarRole::Out { bit: bit as u32 },
            vars,
            bit_lemmas,
            clauses,
            cache,
        );

        if bit != n - 1 {
            // new carry = (a∧b2) ∨ (carry ∧ (a⊕b2)) = MAJ(a, b2, carry).
            carry = build_gate(
                BitLemmaKind::FullAdderCarry,
                vec![a, b2, carry],
                VarRole::Aux { bit: bit as u32 },
                vars,
                bit_lemmas,
                clauses,
                cache,
            );
        }
        out.push(o);
    }
    out
}

/// Rewire `bits` shifted by the constant `amt` (no gates — pure variable
/// selection). Vacated positions take `zero` (shl/lshr) or `sign` (ashr).
fn shift_const_rewire(op: BvOp, bits: &[u32], amt: usize, zero: u32, sign: u32) -> Vec<u32> {
    let n = bits.len();
    (0..n)
        .map(|j| match op {
            // out[j] = (j >= amt) ? bits[j-amt] : 0
            BvOp::Shl => {
                if j >= amt {
                    bits[j - amt]
                } else {
                    zero
                }
            }
            // out[j] = (j+amt < n) ? bits[j+amt] : 0
            BvOp::Lshr => {
                if j + amt < n {
                    bits[j + amt]
                } else {
                    zero
                }
            }
            // out[j] = (j+amt < n) ? bits[j+amt] : sign
            BvOp::Ashr => {
                if j + amt < n {
                    bits[j + amt]
                } else {
                    sign
                }
            }
            _ => unreachable!("shift_const_rewire is only used for shift ops"),
        })
        .collect()
}

/// `out = sel ? on_true : on_false`, built as `(sel ∧ on_true) ∨ (¬sel ∧ on_false)`
/// from existing `And2`/`Or2`/`Not` gates. The final `Or2` carries `role`.
#[allow(clippy::too_many_arguments)]
fn mux_bit(
    sel: u32,
    on_true: u32,
    on_false: u32,
    bit: usize,
    role: VarRole,
    vars: &mut VarTable,
    bit_lemmas: &mut Vec<BitLemma>,
    clauses: &mut Vec<Clause>,
    cache: &mut GateCache,
) -> u32 {
    let aux = VarRole::Aux { bit: bit as u32 };
    let nsel = build_gate(
        BitLemmaKind::Not,
        vec![sel],
        aux,
        vars,
        bit_lemmas,
        clauses,
        cache,
    );
    let t1 = build_gate(
        BitLemmaKind::And2,
        vec![sel, on_true],
        aux,
        vars,
        bit_lemmas,
        clauses,
        cache,
    );
    let t2 = build_gate(
        BitLemmaKind::And2,
        vec![nsel, on_false],
        aux,
        vars,
        bit_lemmas,
        clauses,
        cache,
    );
    build_gate(
        BitLemmaKind::Or2,
        vec![t1, t2],
        role,
        vars,
        bit_lemmas,
        clauses,
        cache,
    )
}

/// OR-reduce `bits` (non-empty) into a single var via a chain of `Or2` gates.
fn or_reduce(
    bits: &[u32],
    vars: &mut VarTable,
    bit_lemmas: &mut Vec<BitLemma>,
    clauses: &mut Vec<Clause>,
    cache: &mut GateCache,
) -> u32 {
    let mut acc = bits[0];
    for &b in &bits[1..] {
        acc = build_gate(
            BitLemmaKind::Or2,
            vec![acc, b],
            VarRole::Aux { bit: 0 },
            vars,
            bit_lemmas,
            clauses,
            cache,
        );
    }
    acc
}

/// Bit-blast a variable-amount shift (`bvshl`/`bvlshr`/`bvashr`) as a barrel
/// shifter: `ceil(log2(n))` conditional constant-shift layers selected by the low
/// bits of the shift amount, then an overflow mux that saturates when the amount is
/// `>= n` (0 for shl/lshr, the replicated sign bit for ashr). Every gate reuses an
/// existing [`BitLemmaKind`], so the producer CNF and the validator agree by
/// construction. `a_bits` is the value, `b_bits` the shift amount (LSB-first).
pub(crate) fn blast_shift(
    op: BvOp,
    a_bits: &[u32],
    b_bits: &[u32],
    vars: &mut VarTable,
    bit_lemmas: &mut Vec<BitLemma>,
    clauses: &mut Vec<Clause>,
    cache: &mut GateCache,
) -> Vec<u32> {
    let n = a_bits.len();
    let zero = build_gate(
        BitLemmaKind::ConstFalse,
        vec![],
        VarRole::CarryIn,
        vars,
        bit_lemmas,
        clauses,
        cache,
    );
    let sign = a_bits[n - 1];
    // Value shifted into every position on a full over-shift (amount >= n).
    let saturate_fill = if matches!(op, BvOp::Ashr) { sign } else { zero };

    // ceil(log2(n)) control bits cover every in-range shift amount 0..n-1.
    let log2_n = (u32::BITS - (n as u32 - 1).leading_zeros()) as usize;
    let mut current: Vec<u32> = a_bits.to_vec();
    for (i, &ctrl_bit) in b_bits.iter().enumerate().take(log2_n) {
        let amt = 1usize << i;
        let shifted = shift_const_rewire(op, &current, amt, zero, sign);
        current = (0..n)
            .map(|bit| {
                mux_bit(
                    ctrl_bit,
                    shifted[bit],
                    current[bit],
                    bit,
                    VarRole::Aux { bit: bit as u32 },
                    vars,
                    bit_lemmas,
                    clauses,
                    cache,
                )
            })
            .collect();
    }

    // Over-shift: if any shift-amount bit at position >= log2_n is set, the amount
    // is >= 2^log2_n >= n and the result saturates. Amounts in [n, 2^log2_n) (which
    // exist only for non-power-of-two widths) carry no high bit, but the layered
    // constant rewires already saturate them: each layer's `shift_const_rewire`
    // fills vacated positions with `zero`/`sign`, so a composed shift of >= n
    // positions leaves only fill bits. The final mux outputs are the result bits.
    let high = &b_bits[log2_n.min(n)..];
    debug_assert!(
        !high.is_empty(),
        "ceil(log2({n})) < {n} for all n >= 1, so over-shift bits always exist"
    );
    let overflow = or_reduce(high, vars, bit_lemmas, clauses, cache);
    (0..n)
        .map(|bit| {
            mux_bit(
                overflow,
                saturate_fill,
                current[bit],
                bit,
                VarRole::Out { bit: bit as u32 },
                vars,
                bit_lemmas,
                clauses,
                cache,
            )
        })
        .collect()
}

/// Evaluate a gate's output truth value given the truth values of its (positionally
/// matched) input vars. Returns `None` only on an arity mismatch.
///
/// This is the **single source of gate semantics**: both the producer's CNF emission
/// ([`push_gate_cnf`]) and the validator's leaf-clause check ([`tseitin_clauses`])
/// derive their clauses from this function, so a clause can never disagree with the
/// gate the validator believes it encodes.
fn gate_eval(kind: BitLemmaKind, ins: &[bool]) -> Option<bool> {
    if ins.len() != kind.arity() {
        return None;
    }
    Some(match kind {
        BitLemmaKind::Xor2 => ins[0] ^ ins[1],
        BitLemmaKind::And2 => ins[0] && ins[1],
        BitLemmaKind::Or2 => ins[0] || ins[1],
        BitLemmaKind::Xor3 => ins[0] ^ ins[1] ^ ins[2],
        // carry = (a∧b) ∨ (c∧(a⊕b)) = majority(a,b,c).
        BitLemmaKind::FullAdderCarry => (ins[0] && ins[1]) || (ins[2] && (ins[0] ^ ins[1])),
        BitLemmaKind::Not => !ins[0],
        BitLemmaKind::ConstTrue => true,
        BitLemmaKind::ConstFalse => false,
        // out <=> (l == r), i.e. ¬(l ⊕ r).
        BitLemmaKind::XnorEq => !(ins[0] ^ ins[1]),
    })
}

/// The full Tseitin clause set entailed by `out = kind(ins...)`, over the **distinct**
/// variables among `{out} ∪ ins`. For every assignment to those variables that
/// violates `out == gate_eval(ins)`, emit the clause that forbids exactly that
/// assignment. Tautological clauses (which arise when an input var is repeated, e.g.
/// `XnorEq(l, l)`) and duplicate clauses are dropped.
///
/// Used by the producer to emit CNF and by [`BvBlastProof::validate`] to re-derive
/// the gate's clauses and check each `BitLemmaCnf` clause is one of them. Because the
/// two paths share this function and [`gate_eval`], "the clause matches its provenance
/// tag" is genuinely checked against gate semantics, not asserted.
fn tseitin_clauses(kind: BitLemmaKind, out: u32, ins: &[u32]) -> Vec<Vec<Lit>> {
    // Distinct vars (stable order: out first, then ins in order), so a repeated input
    // var contributes only one assignment column.
    let mut order: Vec<u32> = Vec::with_capacity(ins.len() + 1);
    for &v in std::iter::once(&out).chain(ins.iter()) {
        if !order.contains(&v) {
            order.push(v);
        }
    }
    let k = order.len();
    let mut result: Vec<Vec<Lit>> = Vec::new();
    let mut seen: BTreeSet<BTreeSet<Lit>> = BTreeSet::new();
    for mask in 0u32..(1u32 << k) {
        // Truth value of each distinct var under this assignment.
        let val = |v: u32| -> bool {
            let idx = order.iter().position(|&x| x == v).expect("v in order");
            mask & (1 << idx) != 0
        };
        let out_v = val(out);
        let in_vals: Vec<bool> = ins.iter().map(|&v| val(v)).collect();
        let expected = gate_eval(kind, &in_vals).expect("arity checked by caller");
        if out_v == expected {
            continue; // satisfying row — no clause needed
        }
        // Forbid this violating assignment: the clause is its negation, one literal
        // per distinct var (so a repeated input naturally collapses → may be a unit).
        let mut lits: Vec<Lit> = Vec::with_capacity(k);
        let mut tautology = false;
        let mut litset: BTreeSet<Lit> = BTreeSet::new();
        for &v in &order {
            let lit = lit_for(v, !val(v));
            if litset.contains(&lit.negated()) {
                tautology = true;
                break;
            }
            if litset.insert(lit) {
                lits.push(lit);
            }
        }
        if tautology {
            continue;
        }
        let canon: BTreeSet<Lit> = lits.iter().copied().collect();
        if seen.insert(canon) {
            result.push(lits);
        }
    }
    result
}

/// Emit the gate's Tseitin CNF into `clauses` (with `BitLemmaCnf` provenance) and
/// return the ids of the emitted clauses. Delegates clause computation to
/// [`tseitin_clauses`] so producer and validator never diverge.
pub(crate) fn push_gate_cnf(
    clauses: &mut Vec<Clause>,
    kind: BitLemmaKind,
    out: u32,
    ins: &[u32],
    lemma: u32,
) -> Vec<u32> {
    tseitin_clauses(kind, out, ins)
        .into_iter()
        .map(|lits| {
            let id = clauses.len() as u32;
            clauses.push(Clause {
                id,
                lits,
                provenance: ClauseProvenance::BitLemmaCnf { lemma },
            });
            id
        })
        .collect()
}

fn lit_for(var: u32, positive: bool) -> Lit {
    if positive {
        Lit::pos(var)
    } else {
        Lit::neg(var)
    }
}

#[cfg(test)]
#[path = "bv_blast_export_tests.rs"]
mod tests;
