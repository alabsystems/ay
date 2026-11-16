// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A COMPLETE, hole-free Alethe refutation for a bit-vector theory lemma.
//!
//! Every other bit-blast lowering in this printer recognizes one exact clause
//! shape. This one does not: it takes an arbitrary QF_BV theory lemma
//! `(cl (not A))`, bit-blasts `A` the way the pinned checker itself does, and
//! transports AY's own SAT refutation over the resulting Boolean atoms. The
//! result contains no `hole`, no `trust`, and no rule the checker does not
//! implement — or it is not emitted at all.
//!
//! ## The four layers
//!
//! 1. **Word to bit.** One `bitblast_*` step per bit-vector node, bottom-up.
//!    Each node is first re-spelled with `cong` so its operands are `@bbterm`
//!    lists (the checker's `get_term_bits` short-circuits an existing
//!    `@bbterm`, which is the only way a compound operand's already-derived
//!    bits reach the rule), then the `bitblast_*` rule is applied, then `trans`
//!    stitches the two together.
//! 2. **Atom to Boolean.** A bit-vector equality becomes a conjunction of bit
//!    equivalences through `bitblast_equal`; `bvult` becomes its comparator
//!    through `bitblast_ult`. `equiv1`/`equiv2` turn each equivalence into the
//!    two clauses the SAT layer needs.
//! 3. **Tseitin.** Every structural gate's defining clauses are DERIVED with
//!    the ordinary Boolean tautology rules (`and_pos`, `or_neg`, `xor_pos1`,
//!    `equiv_neg2`, `ite_pos1`, …) rather than assumed. A gate is named by a
//!    proof-local `define-fun`, which the checker inlines before any rule runs,
//!    so naming shrinks the document without weakening a single check.
//! 4. **Transport.** AY re-runs its own SAT engine on exactly that clause set
//!    and transports the refutation as a chain of BINARY resolutions — one
//!    pivot per printed step, which is the inference the checker replays.
//!    Every transported clause carries the extra literal `(not A)`, so the
//!    chain ends at `(cl (not A))` instead of `(cl)`: the assumption is
//!    carried, never used as a premise.
//!
//! Before any of it is disclosed, the printed document is replayed from its
//! own TEXT ([`selfcheck`]). A document AY cannot replay is not printed, so
//! the disclosure `unproved_steps=0` can never be stronger than the document
//! it describes.
//!
//! ## Two operators with no rule of their own
//!
//! * `bvsub` and a power-of-two `bvmul` are RE-SPELLED, never assumed: one
//!   `poly_simp` step proves `(= (bvsub a b) (bvadd a (bvneg b)))` (the pinned
//!   checker normalizes bit-vector polynomials modulo `2^w`), and the
//!   doubling chain for `x * 2^k` is proved the same way. A multiplication
//!   that is not a power of two still goes through `bitblast_mult`.
//! * A bit-vector `ite` has NO bit-blasting rule in the pinned checker, and
//!   `bitblast_var` on it would throw its semantics away. Instead `ite_intro`
//!   derives `(= true (and true (ite c (= t a) (= t b))))` — a shape the
//!   checker validates structurally — and `ite1`/`ite2` turn it into the two
//!   guarded equalities, which `bitblast_equal` then reduces to bit-level
//!   clauses. The `ite`'s own bits stay free variables constrained by exactly
//!   those clauses.
//!
//! ## Fail closed
//!
//! Every unsupported operator, over-wide word, over-budget document, and —
//! decisively — a SATISFIABLE bit-blasting returns `None`, which leaves the
//! ordinary honest `hole` in place. A wrong theorem can therefore never be
//! dressed as an accepted proof: the refutation has to exist before anything
//! is printed.

mod ask;
mod case_split;
mod circuit;
mod clause;
mod constant_product;
mod consumer_work;
#[cfg(test)]
#[path = "complete_blast/corpus.rs"]
mod corpus;
mod division;
mod ground;
mod ite;
#[cfg(test)]
#[path = "complete_blast/judged_tests.rs"]
mod judged_tests;
mod lane;
mod lazy;
mod normalize;
mod offset;
#[cfg(test)]
#[path = "complete_blast/offset_tests.rs"]
mod offset_tests;
mod opaque_array_read;
mod order;
mod resolvent;
mod rup_replay;
#[path = "complete_blast/selfcheck.rs"]
mod selfcheck;
#[cfg(test)]
#[path = "complete_blast/shift_semantics_tests.rs"]
mod shift_semantics_tests;
mod surface;
#[cfg(test)]
mod surface_tests;
mod sweep;
#[cfg(test)]
#[path = "complete_blast/tests.rs"]
mod tests;
mod transport;
mod traversal;
mod zero_extend;

use super::{AlethePrinter, CheckableRule};
use ay_core::kani_compat::{DetHashMap, DetHashSet};
use ay_core::{Constant, ProofId, Sort, Symbol, TermData, TermId};
use circuit::{Circuit, SRef, ShiftOp};

pub use ask::CompleteBlastAsk;

/// Widest bit-vector node this lowering will blast.
///
/// Every bit is its own gate reference, so width alone costs nothing but
/// gates; what a width can break is integer arithmetic on bit POSITIONS or
/// VALUES. Audited 2026-09-30 when this rose from 128 (a external-codegen gate row
/// compares two 192-bit `concat`s of 64-bit words): literals are read bit by bit from
/// their `BigInt`; `constant_product` refuses literals over its own 128 bits;
/// the doubling chain and `arithmetic_shift_is_admissible` build `2^k` with
/// `checked_shl` and refuse past `u128`; `lazy.rs` leaves divisions over 128
/// bits exact and reads model values with `checked_shl`; and the one
/// unchecked shift, `size_constant_bits`, now shifts the width in its own
/// `u32` through `checked_shr`. Re-audited for 1024-bit source words:
/// derived-order integer weights use `BigInt`, while the optional numeric
/// `u128` optimizations keep their checked declines. Gate, term, replay,
/// document, and multiplication-chain budgets do not grow with this bound.
const MAX_WIDTH: u32 = 1_024;
/// Largest source term DAG (distinct nodes) this lowering will walk.
const MAX_TERM_NODES: usize = 8_192;
/// Largest Boolean gate DAG.
const MAX_GATES: usize = 4_000_000;
/// Largest planned input clause set.
const MAX_PLANNED_CLAUSES: usize = 8_000_000;
/// Largest replayed refutation (derived clauses).
const MAX_DERIVED_CLAUSES: usize = 2_000_000;
/// Largest transported chain (printed binary resolution steps).
const MAX_CHAIN_STEPS: u64 = 16_000_000;
/// Largest document emitted without counting the consumer's work.
///
/// This is a CONSUMER budget, not a memory budget, and it is measured rather
/// than chosen: against the pinned checker (clean @ acdc24598, carcara
/// d62d45c) certificates of 11.4, 51.3, 52.1, 61.2, 84.8, 89.2 and 92.5 MB
/// were reported `fully verified`, while 111, 140 and 181 MB were refused
/// outright with `invalid or over-budget zero-extension normalization` —
/// the downstream proof consumer's own normalizer budget, which no proof of this shape can clear.
/// Emitting a document the consumer cannot check is strictly worse than the
/// honest `hole` it replaces, so a document that would cross this line is not
/// emitted at all.
///
/// RE-MEASURED after the pivot-carrying transport (same checker). The earlier
/// 96 MiB line was calibrated on the LOAD family, and the STORE family clears
/// the normalizer at a lower figure: `str.ui.gpr.w1` verified at 75,244,514
/// bytes, while `str.ui.fpr.w4`, `str.ui.fpr.w2`/`str.ui.gpr.w2` and
/// `str.ui.gpr.w4` were refused with that same message at 83,725,293,
/// 85,561,380 and 90,660,574 bytes. The budget is work over zero-extension
/// terms rather than bytes, so no byte figure separates the two families
/// exactly; this one sits inside the measured gap, keeping every certificate
/// that is currently accepted (largest 75,244,514) and refusing the four that
/// the consumer rejects. A refusal leaves the honest `hole`, which is strictly
/// better than a document that reaches the consumer and fails.
///
/// Past this line a document is sized in the consumer's own unit instead
/// ([`consumer_accepts`]): the bytes-per-unit ratio is a property of the
/// family and of the transport, and `drup` steps (`resolvent.rs`) print their
/// premises, which the normalizer does not charge, without the pivots, which
/// it does. Measured 2026-09-30 on external-codegen's 64-bit division rows with the
/// `drup` transport: 88,380,648 and 90,589,115 bytes at 3,099,994 and
/// 3,218,056 normalizer units, both `fully verified` by clean `5390f432b8`.
const MAX_TEXT_BYTES: usize = 76 * 1024 * 1024;
/// Largest document emitted at all, whatever its work: a memory bound on the
/// text this printer holds, above every document measured to verify.
pub(super) const MAX_COUNTED_TEXT_BYTES: usize = 128 * 1024 * 1024;
/// The consumer normalizer's budget for a whole certificate (clean
/// `carcara_verify/zero_extend.rs`, `MAX_WORK` 4,000,000; which Cleans charge
/// it is in `consumer_work`), less a margin for
/// the problem's premises and the proof's other steps, which it charges too.
/// Measured: documents of 4,609,600 to 4,943,582 units were refused `over-budget`
/// and those of 2,875,378 to 3,218,056 verified.
const MAX_CONSUMER_WORK: usize = 3_800_000;

/// Whether the consumer's normalizer takes `document`: within the measured
/// byte line, or within the counted bound and the consumer's budget by its
/// own count (`consumer_work.rs`).
fn consumer_accepts(document: &str) -> bool {
    document.len() <= MAX_TEXT_BYTES
        || (document.len() <= MAX_COUNTED_TEXT_BYTES
            && consumer_work::normalizer_work(document)
                .is_some_and(|work| work <= MAX_CONSUMER_WORK))
}
/// Largest `x * 2^k` doubling chain re-spelled through `poly_simp`.
/// Retain the earlier 256-bit envelope's chain cap independently of source
/// width. Each doubling is a one-monomial `poly_simp` step; the checked
/// numeric carrier may decline earlier (see `build_multiplication`).
const MAX_MUL_DOUBLINGS: u32 = 255;
/// Longest term spelling still printed inline rather than behind a name.
const INLINE_REFERENCE_BYTES: usize = 24;

/// A bit-vector node that has been reduced to an explicit bit list.
struct Word {
    /// How this word prints wherever it occurs (its own short spelling, or
    /// the proof-local name defined for it).
    reference: String,
    width: u32,
    /// Bits, least significant first.
    bits: Vec<SRef>,
    /// Step whose conclusion is `(= reference (@bbterm bits…))`.
    step: String,
}

/// How an input clause of the transported CNF reaches the document.
enum ClauseEmit {
    /// Printed by [`Blaster::emit_planned_clause`] when the refutation uses it.
    Rule {
        rule: CheckableRule,
        args: Option<String>,
        premises: Vec<String>,
    },
    /// Already printed as part of the bit-blasting machinery under this id.
    Existing(String),
    /// The assumed root. It is never a premise: the transported chain carries
    /// `(not A)` in every clause instead, which is the same assumption.
    Root,
}

impl ClauseEmit {
    fn rule(rule: &str, args: Option<String>, premises: Vec<String>) -> Option<Self> {
        Some(Self::Rule {
            rule: CheckableRule::new(rule)?,
            args,
            premises,
        })
    }

    fn bare(rule: &str) -> Option<Self> {
        Self::rule(rule, None, Vec::new())
    }
}

/// One clause handed to the SAT engine, with the derivation that licenses it.
struct PlannedClause {
    lits: Vec<SRef>,
    emit: ClauseEmit,
}

/// The bit-vector operation a word node stands for, after re-spelling.
enum WordOp {
    /// A free bit-vector term: its bits are `((_ @bit_of i) t)` projections.
    Leaf,
    /// A bit-vector literal.
    Const(Vec<bool>),
    And(Vec<usize>),
    Or(Vec<usize>),
    Xor(Vec<usize>),
    Not(usize),
    Add(Vec<usize>),
    Mul(Vec<usize>),
    Neg(usize),
    Concat(Vec<usize>),
    Extract {
        low: u32,
        arg: usize,
    },
    SignExtend {
        by: u32,
        arg: usize,
    },
    /// Spelled `((_ zero_extend k) x)`, related to its definition `(concat
    /// zero x)` by one `refl` identity (`zero_extend_identity`).
    ZeroExtend {
        zero: usize,
        arg: usize,
    },
    Shift {
        op: ShiftOp,
        x: usize,
        y: usize,
    },
    /// `bvudiv` (`remainder == false`) or `bvurem`: a checker's long-division
    /// circuit (`division`).
    Div {
        x: usize,
        y: usize,
        remainder: bool,
    },
}

struct Blaster<'a, 'p> {
    printer: &'p AlethePrinter<'a>,
    /// The namespace of this document's step names: the lemma id, or a
    /// case's anchor (`case_split.rs`).
    id: String,
    prefix: String,
    circuit: Circuit,
    words: Vec<Word>,
    word_of: DetHashMap<TermId, usize>,
    bool_of: DetHashMap<TermId, SRef>,
    /// Every `define-fun` this document introduces, in CREATION order.
    ///
    /// Words and gates reference each other in both directions — a
    /// bit-vector `ite` word names its condition gate, and a bit atom names
    /// the word it projects — so neither table can be emitted as a block.
    /// Creation order IS dependency order (nothing is built before its
    /// operands), so appending both kinds to one buffer as they are minted is
    /// the only ordering the checker's parser accepts.
    definitions: String,
    /// Gates already flushed into `definitions`.
    flushed_gates: u32,
    /// Bit-blasting, theory-equivalence and `ite`-semantics steps.
    steps: String,
    /// Width-constant bit projections the barrel shifter needs, per width.
    size_constants: DetHashMap<u32, Vec<SRef>>,
    planned: Vec<PlannedClause>,
    next_id: u32,
    text_used: usize,
    /// Source nodes built so far, over EVERY root of this document, so
    /// [`MAX_TERM_NODES`] bounds a multi-root blast as a whole.
    walked: usize,
    /// Array-variable source leaves used only by opaque BV reads. They count
    /// against the same source-node envelope across every prepared root.
    opaque_array_variables: DetHashSet<TermId>,
    /// The words that are bit-vector LITERALS, not merely constant-valued.
    literal_words: DetHashSet<usize>,
    /// Every bit-vector `ite` word, as the sweep models it (`ite.rs`).
    guarded_ites: Vec<sweep::GuardedIte>,
    /// Divisions left as free words (`lazy.rs`).
    opaque_divisions: DetHashSet<TermId>,
    /// The case this document assumes, and the words bound by it, each to
    /// its literal and the step `(= v K)` (`case_split.rs`).
    case: Option<case_split::Case>,
    case_words: DetHashMap<usize, (TermId, String)>,
    /// Each bit-vector `ite` word's bits and its planned guarded equalities.
    ite_definitions: Vec<crate::sat_sweep::split::Definition>,
    /// Each bit-vector `ite` word's else-branch word (`ite.rs`).
    ite_else: DetHashMap<usize, usize>,
    /// One `(bvsub x y)` word per pair of offset words, and one blasted
    /// `(= d k)` gate per difference and constant (`offset.rs`).
    differences: DetHashMap<(TermId, TermId), usize>,
    offset_targets: DetHashMap<(TermId, TermId, String), (SRef, String, String)>,
    /// The equalities the roots reach: only a reading that pays is bridged.
    offset_shares: ay_core::BvOffsetShares,
    /// Gates whose structural clauses are planned.
    structured_gates: u32,
    /// Set by a transport that its document's size refused.
    refused_by_size: std::cell::Cell<bool>,
    /// The sweep refuted this plan and only its document's size refused it,
    /// which settles the plan (`transport/size_refusal.rs`).
    swept_refused_by_size: bool,
}

impl AlethePrinter<'_> {
    /// Emit a complete, hole-free refutation of a QF_BV theory lemma, or
    /// `None` to leave the ordinary honest `hole` in place.
    pub(super) fn format_bv_complete_blast_refutation(
        &self,
        id: ProofId,
        clause: &[TermId],
    ) -> Option<String> {
        self.check_emission_progress(0).ok()?;
        // `--debug-cert` names the phase that declined, so a census of the
        // lemmas this lowering leaves as holes reads the reason off the trace.
        let decline = |phase: &str| {
            if ay_core::misc_cli_flags().debug_cert {
                ay_core::safe_eprintln!(
                    "c !! complete-blast declined at {id}: {phase} (clause of {} literal(s))",
                    clause.len()
                );
            }
        };
        if let Some(reason) = self.complete_blast_unasked() {
            decline(reason);
            return None;
        }
        let [literal] = clause else {
            decline("not a unit clause");
            return None;
        };
        // `(cl (not A))` refutes `A`; a positive `(cl P)` refutes the
        // gate-level negation of `P`. Either way the root clause is carried
        // as a literal, and the chain lands on exactly the lemma's literal.
        let (root, negated) = match self.terms.get(*literal) {
            TermData::Not(root) => (*root, false),
            _ => (*literal, true),
        };
        if self.terms.sort(root) != &Sort::Bool {
            decline("the root is not Boolean");
            return None;
        }
        let prefix = self.fresh_complete_blast_prefix(id)?;
        if self.complete_blast_surface_agrees(*literal).is_none() {
            decline("the printed surface disagrees");
            return None;
        }
        let orient = |_: &mut Blaster<'_, '_>, prepared: &[SRef]| {
            let [prepared] = prepared else { return None };
            if negated {
                prepared.not()
            } else {
                Some(*prepared)
            }
        };
        let final_clause = self.format_clause(clause);
        // A root with an `ite` condition `(= v K)` is refuted by cases on it
        // first, as the strict checker validates it (`case_split.rs`); the
        // whole root is the fallback.
        let document = Blaster::case_split_document(
            self,
            id,
            &prefix,
            root,
            &orient,
            &final_clause,
        )
        .or_else(|| {
            self.check_emission_progress(0).ok()?;
            let whole = &[root];
            Blaster::lemma_document(self, id, &prefix, whole, &orient, &final_clause, None, None)
        });
        let Some(document) = document else {
            decline("prepare or finish (a node, a bound, SAT, transport, size or replay)");
            return None;
        };
        if self.work_budget_exhausted() {
            decline("the printer's work budget");
            return None;
        }
        Some(document)
    }

    /// A proof-local name prefix that collides with nothing in the problem,
    /// the overrides, or this document's other definitions.
    fn fresh_complete_blast_prefix(&self, id: ProofId) -> Option<String> {
        for nonce in 0_u64..64 {
            let prefix = format!("@ay_cbb_{id}_{nonce}_");
            if !self.proof_definition_name_collision(&prefix) {
                return Some(prefix);
            }
        }
        None
    }
}

impl<'a, 'p> Blaster<'a, 'p> {
    fn new(printer: &'p AlethePrinter<'a>, id: ProofId, prefix: String) -> Self {
        Self {
            printer,
            id: id.to_string(),
            circuit: Circuit::new(prefix.clone()),
            prefix,
            words: Vec::new(),
            word_of: DetHashMap::default(),
            bool_of: DetHashMap::default(),
            definitions: String::new(),
            flushed_gates: 0,
            steps: String::new(),
            size_constants: DetHashMap::default(),
            planned: Vec::new(),
            next_id: 0,
            text_used: 0,
            walked: 0,
            opaque_array_variables: DetHashSet::default(),
            literal_words: DetHashSet::default(),
            guarded_ites: Vec::new(),
            opaque_divisions: DetHashSet::default(),
            case: None,
            case_words: DetHashMap::default(),
            ite_definitions: Vec::new(),
            ite_else: DetHashMap::default(),
            differences: DetHashMap::default(),
            offset_targets: DetHashMap::default(),
            offset_shares: ay_core::BvOffsetShares::default(),
            structured_gates: 0,
            refused_by_size: std::cell::Cell::new(false),
            swept_refused_by_size: false,
        }
    }

    fn step_name(&mut self, tag: &str) -> String {
        let name = format!("{}.cbb{}{}", self.id, self.next_id, tag);
        self.next_id += 1;
        name
    }

    fn charge(&mut self, bytes: usize) -> Option<()> {
        self.printer.check_emission_progress(0).ok()?;
        self.text_used = self.text_used.checked_add(bytes)?;
        (self.text_used <= MAX_COUNTED_TEXT_BYTES).then_some(())?;
        self.printer.check_emission_progress(0).ok()
    }

    fn push_step(&mut self, text: &str) -> Option<()> {
        self.charge(text.len() + 1)?;
        self.steps.push_str(text);
        self.steps.push('\n');
        Some(())
    }

    fn bbterm(&self, bits: &[SRef]) -> String {
        let mut out = String::from("(@bbterm");
        for bit in bits {
            out.push(' ');
            out.push_str(&self.circuit.text(*bit));
        }
        out.push(')');
        out
    }

    fn clause_text(&self, lits: &[SRef]) -> String {
        if lits.is_empty() {
            return "(cl)".to_string();
        }
        let mut out = String::from("(cl");
        for lit in lits {
            out.push(' ');
            out.push_str(&self.circuit.text(*lit));
        }
        out.push(')');
        out
    }
}

// ------------------------------------------------------------------- words

impl Blaster<'_, '_> {
    fn word_ref(&self, index: usize) -> String {
        self.words[index].reference.clone()
    }

    fn word_of_term(&self, term: TermId) -> Option<usize> {
        self.word_of.get(&term).copied()
    }

    fn build_word(&mut self, term: TermId, width: u32) -> Option<usize> {
        let data = self.printer.terms.get(term).clone();
        match data {
            TermData::Const(Constant::BitVec { value, width: w }) => {
                if w != width || value.sign() == num_bigint::Sign::Minus {
                    return None;
                }
                let bits = (0..u64::from(width)).map(|i| value.bit(i)).collect();
                let body = self.printer.format_term(term);
                self.new_word(body, width, WordOp::Const(bits))
            }
            TermData::Var(..) => {
                if let Some(bound) = self.case_bound_word(term, width) {
                    return bound;
                }
                let body = self.printer.format_term(term);
                self.new_word(body, width, WordOp::Leaf)
            }
            TermData::Ite(cond, then_branch, else_branch) => {
                self.build_bitvector_ite(cond, then_branch, else_branch, width)
            }
            TermData::App(symbol, args) => {
                if self.opaque_divisions.contains(&term) {
                    let body = self.printer.format_term(term);
                    return self.new_word(body, width, WordOp::Leaf);
                }
                if let Some(word) = self.build_word_app(&symbol, &args, width) {
                    return Some(word);
                }
                // An operator this lowering does not interpret (`bvsdiv`,
                // `bvsrem`, a rotation, ..) is an OPAQUE word: `bitblast_var`
                // holds for ANY bit-vector term, so its bits are free
                // `@bit_of` projections, shared by every occurrence of the
                // same term. Sound for a refutation — the SAT layer must refute
                // every interpretation of those bits — and a lemma that needs
                // the operator's meaning stays SATISFIABLE and is declined.
                let body = self.printer.format_term(term);
                self.new_word(body, width, WordOp::Leaf)
            }
            _ => None,
        }
    }

    fn build_word_app(&mut self, symbol: &Symbol, args: &[TermId], width: u32) -> Option<usize> {
        let operands: Option<Vec<usize>> = args.iter().map(|a| self.word_of_term(*a)).collect();
        let operands = operands?;
        match symbol {
            Symbol::Named(name) => match name.as_ref() {
                "bvand" if operands.len() >= 2 => self.nary(operands, width, "bvand", WordOp::And),
                "bvor" if operands.len() >= 2 => self.nary(operands, width, "bvor", WordOp::Or),
                "bvxor" if operands.len() >= 2 => self.nary(operands, width, "bvxor", WordOp::Xor),
                "bvadd" if operands.len() >= 2 => self.nary(operands, width, "bvadd", WordOp::Add),
                "bvmul" if operands.len() >= 2 => self.build_multiplication(&operands, width),
                "bvsub" if operands.len() >= 2 => self.build_subtraction(&operands, width),
                "concat" if operands.len() >= 2 => {
                    self.nary(operands, width, "concat", WordOp::Concat)
                }
                "bvnot" if operands.len() == 1 => {
                    let body = self.application("bvnot", &operands);
                    self.new_word(body, width, WordOp::Not(operands[0]))
                }
                "bvneg" if operands.len() == 1 => {
                    let body = self.application("bvneg", &operands);
                    self.new_word(body, width, WordOp::Neg(operands[0]))
                }
                "bvudiv" | "bvurem" if operands.len() == 2 => {
                    let body = self.application(name.as_ref(), &operands);
                    self.new_word(
                        body,
                        width,
                        WordOp::Div {
                            x: operands[0],
                            y: operands[1],
                            remainder: name.as_ref() == "bvurem",
                        },
                    )
                }
                "bvshl" | "bvlshr" | "bvashr" if operands.len() == 2 => {
                    let op = match name.as_ref() {
                        "bvshl" => ShiftOp::Shl,
                        "bvlshr" => ShiftOp::LShr,
                        _ => ShiftOp::AShr,
                    };
                    let operands = self.with_ground_shift_amount(op, operands, args, width);
                    let body = self.application(name.as_ref(), &operands);
                    self.new_word(
                        body,
                        width,
                        WordOp::Shift {
                            op,
                            x: operands[0],
                            y: operands[1],
                        },
                    )
                }
                _ => None,
            },
            Symbol::Indexed(name, indices) => match (name.as_ref(), indices.as_slice()) {
                ("extract", [high, low]) if operands.len() == 1 => {
                    if high < low || high - low + 1 != width {
                        return None;
                    }
                    let body = format!("((_ extract {high} {low}) {})", self.word_ref(operands[0]));
                    self.new_word(
                        body,
                        width,
                        WordOp::Extract {
                            low: *low,
                            arg: operands[0],
                        },
                    )
                }
                ("sign_extend", [by]) if operands.len() == 1 && *by > 0 => {
                    let body = format!("((_ sign_extend {by}) {})", self.word_ref(operands[0]));
                    self.new_word(
                        body,
                        width,
                        WordOp::SignExtend {
                            by: *by,
                            arg: operands[0],
                        },
                    )
                }
                ("zero_extend", [0]) if operands.len() == 1 => {
                    self.zero_extend_zero_word(operands[0], width)
                }
                ("zero_extend", [by]) if operands.len() == 1 && *by > 0 => {
                    let zero = self.zero_constant(*by)?;
                    let body = format!("((_ zero_extend {by}) {})", self.word_ref(operands[0]));
                    self.new_word(
                        body,
                        width,
                        WordOp::ZeroExtend {
                            zero,
                            arg: operands[0],
                        },
                    )
                }
                _ => None,
            },
            _ => None,
        }
    }

    fn nary(
        &mut self,
        operands: Vec<usize>,
        width: u32,
        head: &str,
        make: impl FnOnce(Vec<usize>) -> WordOp,
    ) -> Option<usize> {
        let body = self.application(head, &operands);
        self.new_word(body, width, make(operands))
    }

    fn application(&self, head: &str, operands: &[usize]) -> String {
        let mut out = format!("({head}");
        for operand in operands {
            out.push(' ');
            out.push_str(&self.words[*operand].reference);
        }
        out.push(')');
        out
    }

    /// A `#b0…0` literal of the given width, as its own word node.
    fn zero_constant(&mut self, width: u32) -> Option<usize> {
        let body = format!("#b{}", "0".repeat(width as usize));
        let bits = vec![false; width as usize];
        self.new_word(body, width, WordOp::Const(bits))
    }

    /// `(bvsub a b …)` has no bit-blasting rule. Re-spell it as
    /// `(bvadd a (bvneg b) …)` — an identity the pinned checker's
    /// bit-vector polynomial normalizer discharges directly — and blast that.
    fn build_subtraction(&mut self, operands: &[usize], width: u32) -> Option<usize> {
        let mut addends = vec![operands[0]];
        for operand in &operands[1..] {
            let body = self.application("bvneg", &[*operand]);
            addends.push(self.new_word(body, width, WordOp::Neg(*operand))?);
        }
        let sum_body = self.application("bvadd", &addends);
        let sum = self.new_word(sum_body, width, WordOp::Add(addends))?;
        let body = self.application("bvsub", operands);
        self.rewritten_word(body, width, sum)
    }

    /// A multiplication by `2^k` is re-spelled as a doubling chain, again
    /// through the checker's polynomial normalizer: `bitblast_mult` spells a
    /// full `w^2` shift-and-add array even when one operand is a constant,
    /// and `k` ripple-carry adders are far smaller. Everything else goes
    /// through `bitblast_mult` unchanged.
    ///
    /// Each running product is NAMED BY ITS OWN POLYNOMIAL, `(bvmul 2^i x)`,
    /// and its bits are proved equal to the sum `w_{i-1} + w_{i-1}` by one
    /// `poly_simp` step per doubling. The checker inlines `w_{i-1}` as that
    /// one-monomial product, so every step costs it a constant amount of
    /// work. Naming the product by the chain instead — `(bvadd w w)` over
    /// `(bvadd v v)` … — made the single final `poly_simp` expand `2^k` leaves
    /// (the checker's polynomial walk has no cache), which is what capped this
    /// at 16 doublings and left `x * 2^32` at 64 bits (external-codegen's
    /// `Sub_Lsl_Shift_I64 k=32`, 2026-09-28) as a hole.
    fn build_multiplication(&mut self, operands: &[usize], width: u32) -> Option<usize> {
        if let Some(word) = self.case_product(operands, width) {
            return Some(word);
        }
        if operands.len() == 2 {
            for (constant, other) in [(0_usize, 1_usize), (1, 0)] {
                if let Some(doublings) = self.power_of_two_exponent(operands[constant]) {
                    if doublings <= MAX_MUL_DOUBLINGS && doublings < width {
                        let x = operands[other];
                        if doublings == 0 {
                            // `(bvmul 1 x)` is `x`: one `poly_simp` step.
                            let body = self.application("bvmul", operands);
                            return self.rewritten_word(body, width, x);
                        }
                        let mut current = x;
                        for step in 1..=doublings {
                            let body = self.application("bvadd", &[current, current]);
                            let sum =
                                self.new_word(body, width, WordOp::Add(vec![current, current]))?;
                            let product = if step == doublings {
                                self.application("bvmul", operands)
                            } else {
                                format!(
                                    "(bvmul (_ bv{} {width}) {})",
                                    1_u128.checked_shl(step)?,
                                    self.word_ref(x)
                                )
                            };
                            current = self.rewritten_word(product, width, sum)?;
                        }
                        return Some(current);
                    }
                }
            }
        }
        if let Some(word) = self.constant_product(operands, width) {
            return Some(word);
        }
        let body = self.application("bvmul", operands);
        self.new_word(body, width, WordOp::Mul(operands.to_vec()))
    }

    /// `Some(k)` when this word is the literal `2^k` — a LITERAL: the checker's
    /// polynomial normalizer reads `((_ extract 31 0) (_ bv8589934594 64))` as
    /// an atom, not as 2, and refused the doubling chain printed over it.
    fn power_of_two_exponent(&self, word: usize) -> Option<u32> {
        if !self.literal_words.contains(&word) {
            return None;
        }
        let bits = &self.words[word].bits;
        let mut exponent = None;
        for (index, bit) in bits.iter().enumerate() {
            match self.circuit.kind(bit.gate) {
                circuit::GateKind::Const(value) => {
                    let value = *value != bit.negative();
                    if value {
                        if exponent.is_some() {
                            return None;
                        }
                        exponent = Some(index as u32);
                    }
                }
                _ => return None,
            }
        }
        exponent
    }

    /// Bind a word whose bits come from an equal, re-spelled word, with the
    /// re-spelling discharged by `poly_simp` rather than assumed.
    fn rewritten_word(&mut self, body: String, width: u32, target: usize) -> Option<usize> {
        let reference = self.bind_word_reference(body, width)?;
        let rewrite = self.step_name(".pr");
        let step = self.step_name("");
        let target_reference = self.word_ref(target);
        let target_step = self.words[target].step.clone();
        let bits = self.words[target].bits.clone();
        let bbterm = self.bbterm(&bits);
        self.push_step(&format!(
            "(step {rewrite} (cl (= {reference} {target_reference})) :rule poly_simp)"
        ))?;
        self.push_step(&format!(
            "(step {step} (cl (= {reference} {bbterm})) :rule trans :premises ({rewrite} {target_step}))"
        ))?;
        self.words.push(Word {
            reference,
            width,
            bits,
            step,
        });
        Some(self.words.len() - 1)
    }

    /// Give a word a short printed spelling: its own text when that is already
    /// short, otherwise a proof-local definition the checker inlines.
    fn bind_word_reference(&mut self, body: String, width: u32) -> Option<String> {
        if body.len() <= INLINE_REFERENCE_BYTES {
            return Some(body);
        }
        // Any gate this body names was interned before the body was built, so
        // flushing here keeps the single definition list topologically sorted.
        self.flush_gate_definitions()?;
        let name = format!("{}w{}", self.prefix, self.words.len());
        let definition = format!("(define-fun {name} () (_ BitVec {width}) {body})\n");
        self.charge(definition.len())?;
        self.definitions.push_str(&definition);
        Some(name)
    }

    /// Append the `define-fun` of every gate interned since the last flush.
    fn flush_gate_definitions(&mut self) -> Option<()> {
        while (self.flushed_gates as usize) < self.circuit.len() {
            let gate = self.flushed_gates;
            self.flushed_gates += 1;
            let Some(body) = self.circuit.definition(gate) else {
                continue;
            };
            let definition = format!(
                "(define-fun {} () Bool {body})\n",
                self.circuit.reference(gate)
            );
            self.charge(definition.len())?;
            self.definitions.push_str(&definition);
        }
        Some(())
    }
}

impl Blaster<'_, '_> {
    /// Bind a word and emit the steps that prove `(= reference (@bbterm …))`.
    fn new_word(&mut self, body: String, width: u32, op: WordOp) -> Option<usize> {
        let reference = self.bind_word_reference(body, width)?;
        let size = width as usize;
        let step = self.step_name("");

        let (bits, blasted) = match &op {
            WordOp::Leaf => {
                let bits = (0..size)
                    .map(|i| self.circuit.atom(format!("((_ @bit_of {i}) {reference})")))
                    .collect::<Vec<_>>();
                let bbterm = self.bbterm(&bits);
                self.push_step(&format!(
                    "(step {step} (cl (= {reference} {bbterm})) :rule bitblast_var)"
                ))?;
                self.words.push(Word {
                    reference,
                    width,
                    bits,
                    step,
                });
                return Some(self.words.len() - 1);
            }
            WordOp::Const(values) => {
                if values.len() != size {
                    return None;
                }
                let bits = values
                    .iter()
                    .map(|value| self.circuit.constant(*value))
                    .collect::<Vec<_>>();
                let bbterm = self.bbterm(&bits);
                self.push_step(&format!(
                    "(step {step} (cl (= {reference} {bbterm})) :rule bitblast_const)"
                ))?;
                self.words.push(Word {
                    reference,
                    width,
                    bits,
                    step,
                });
                self.literal_words.insert(self.words.len() - 1);
                return Some(self.words.len() - 1);
            }
            other => self.blast_operation(other, size)?,
        };

        // Re-spell the operands as their already-derived bit lists, so the
        // `bitblast_*` rule reads the bits this document has proved rather
        // than opaque `@bit_of` projections of a compound operand.
        let congruence = self.step_name(".cg");
        let rule_step = self.step_name(".bb");
        let premises = blasted.operand_steps.to_vec().join(" ");
        let bbterm = self.bbterm(&bits);
        let respelled = if let WordOp::ZeroExtend { zero, arg } = op {
            self.zero_extend_identity(&reference, zero, arg, &congruence, &blasted)?
        } else {
            self.push_step(&format!(
                "(step {congruence} (cl (= {reference} {})) :rule cong :premises ({premises}))",
                blasted.blasted_application
            ))?;
            congruence
        };
        self.push_step(&format!(
            "(step {rule_step} (cl (= {} {bbterm})) :rule {})",
            blasted.blasted_application, blasted.rule
        ))?;
        self.push_step(&format!(
            "(step {step} (cl (= {reference} {bbterm})) :rule trans :premises ({respelled} {rule_step}))"
        ))?;
        self.words.push(Word {
            reference,
            width,
            bits,
            step,
        });
        Some(self.words.len() - 1)
    }

    fn blast_operation(&mut self, op: &WordOp, size: usize) -> Option<(Vec<SRef>, Blasted)> {
        let blasted = match op {
            WordOp::And(args) | WordOp::Or(args) | WordOp::Xor(args) => {
                let (head, rule) = match op {
                    WordOp::And(_) => ("bvand", "bitblast_and"),
                    WordOp::Or(_) => ("bvor", "bitblast_or"),
                    _ => ("bvxor", "bitblast_xor"),
                };
                let mut bits = self.words[args[0]].bits.clone();
                for arg in &args[1..] {
                    let other = self.words[*arg].bits.clone();
                    if other.len() != size {
                        return None;
                    }
                    let mut next = Vec::with_capacity(size);
                    for i in 0..size {
                        next.push(match op {
                            WordOp::And(_) => self.circuit.and(vec![bits[i], other[i]]),
                            WordOp::Or(_) => self.circuit.or(vec![bits[i], other[i]]),
                            _ => self.circuit.xor(bits[i], other[i]),
                        });
                    }
                    bits = next;
                }
                (bits, self.blasted_application(head, args, rule)?)
            }
            WordOp::Add(args) => {
                let mut bits = self.words[args[0]].bits.clone();
                for arg in &args[1..] {
                    let other = self.words[*arg].bits.clone();
                    if other.len() != size {
                        return None;
                    }
                    bits = self.circuit.ripple_carry_adder(&bits, &other)?;
                }
                (
                    bits,
                    self.blasted_application("bvadd", args, "bitblast_add")?,
                )
            }
            WordOp::Mul(args) => {
                let mut bits = self.words[args[0]].bits.clone();
                for arg in &args[1..] {
                    let other = self.words[*arg].bits.clone();
                    if other.len() != size {
                        return None;
                    }
                    bits = self.circuit.multiplier(&bits, &other)?;
                }
                (
                    bits,
                    self.blasted_application("bvmul", args, "bitblast_mult")?,
                )
            }
            WordOp::Not(arg) => {
                let source = self.words[*arg].bits.clone();
                let bits = source
                    .iter()
                    .map(|bit| bit.not())
                    .collect::<Option<Vec<_>>>()?;
                (
                    bits,
                    self.blasted_application("bvnot", &[*arg], "bitblast_not")?,
                )
            }
            WordOp::Neg(arg) => {
                let source = self.words[*arg].bits.clone();
                let bits = self.circuit.negate_bits(&source)?;
                (
                    bits,
                    self.blasted_application("bvneg", &[*arg], "bitblast_neg")?,
                )
            }
            WordOp::Concat(args) => {
                let mut bits = Vec::with_capacity(size);
                for arg in args.iter().rev() {
                    bits.extend(self.words[*arg].bits.iter().copied());
                }
                if bits.len() != size {
                    return None;
                }
                (
                    bits,
                    self.blasted_application("concat", args, "bitblast_concat")?,
                )
            }
            WordOp::ZeroExtend { zero, arg } => {
                let mut bits = self.words[*arg].bits.clone();
                bits.extend(self.words[*zero].bits.iter().copied());
                if bits.len() != size {
                    return None;
                }
                // Reached through the `refl` identity `zero_extend_identity`
                // prints (and reports) in `new_word`.
                (
                    bits,
                    self.blasted_application("concat", &[*zero, *arg], "bitblast_concat")?,
                )
            }
            WordOp::Extract { low, arg } => {
                let source = &self.words[*arg].bits;
                let start = *low as usize;
                let end = start.checked_add(size)?;
                if end > source.len() {
                    return None;
                }
                let bits = source[start..end].to_vec();
                let source_bb = self.bbterm(&self.words[*arg].bits.clone());
                let high = low + size as u32 - 1;
                (
                    bits,
                    Blasted {
                        blasted_application: format!("((_ extract {high} {low}) {source_bb})"),
                        operand_steps: vec![self.words[*arg].step.clone()],
                        rule: CheckableRule::new("bitblast_extract")?,
                    },
                )
            }
            WordOp::SignExtend { by, arg } => {
                let source = self.words[*arg].bits.clone();
                let sign = *source.last()?;
                let mut bits = source.clone();
                for _ in 0..*by {
                    bits.push(sign);
                }
                if bits.len() != size {
                    return None;
                }
                let source_bb = self.bbterm(&source);
                (
                    bits,
                    Blasted {
                        blasted_application: format!("((_ sign_extend {by}) {source_bb})"),
                        operand_steps: vec![self.words[*arg].step.clone()],
                        rule: CheckableRule::new("bitblast_sign_extend")?,
                    },
                )
            }
            WordOp::Shift { op: shift, x, y } => self.blast_shift(*shift, *x, *y, size)?,
            WordOp::Div { x, y, remainder } => self.blast_division(*x, *y, *remainder)?,
            WordOp::Leaf | WordOp::Const(_) => return None,
        };
        if blasted.0.len() != size {
            return None;
        }
        Some(blasted)
    }

    /// `bvshl` / `bvlshr` / `bvashr` through the checker's barrel shifter.
    fn blast_shift(
        &mut self,
        shift: ShiftOp,
        x: usize,
        y: usize,
        size: usize,
    ) -> Option<(Vec<SRef>, Blasted)> {
        let xs = self.words[x].bits.clone();
        let ys = self.words[y].bits.clone();
        if shift == ShiftOp::AShr && !self.arithmetic_shift_is_admissible(&xs, &ys) {
            // Outside `arithmetic_shift_is_admissible` the pinned zero fill is
            // FALSE and Clean's adapter refuses the step: either way the
            // document would be wrong or a hard error, strictly worse than
            // the honest hole this lowering replaces.
            return None;
        }
        let size_bits = self.size_constant_bits(u32::try_from(size).ok()?)?;
        let bits = self.circuit.shift(shift, &xs, &ys, &size_bits)?;
        let rule = match shift {
            ShiftOp::Shl => "bitblast_shl",
            ShiftOp::LShr => "bitblast_lshr",
            ShiftOp::AShr => "bitblast_ashr",
        };
        let head = match shift {
            ShiftOp::Shl => "bvshl",
            ShiftOp::LShr => "bvlshr",
            ShiftOp::AShr => "bvashr",
        };
        Some((bits, self.blasted_application(head, &[x, y], rule)?))
    }

    /// Whether a `bvashr` instance stays inside the domain where the pinned
    /// zero-filled and Clean's sign-filled circuits agree: a provably
    /// non-negative operand, or an amount that cannot reach the width. It is
    /// the soundness precondition of `AletheDialect::PinnedCarcara` (upstream
    /// Carcara would accept a false zero-filled conclusion outside it), and it
    /// mirrors Clean's `cert verify-external` adapter (`proof-replay-consumer/.../
    /// carcara_verify/ashr.rs`, clean `5390f432b8`). Never relax it.
    fn arithmetic_shift_is_admissible(&self, word: &[SRef], amount: &[SRef]) -> bool {
        let is_false = |bit: &SRef| {
            bit.nots == 0 && matches!(self.circuit.kind(bit.gate), circuit::GateKind::Const(false))
        };
        if word.last().is_some_and(is_false) {
            return true;
        }
        let width = word.len() as u128;
        let mut largest: u128 = 0;
        for (index, bit) in amount.iter().enumerate() {
            if is_false(bit) {
                continue;
            }
            let Some(weight) = 1_u128.checked_shl(u32::try_from(index).unwrap_or(u32::MAX)) else {
                return false;
            };
            largest |= weight;
            if largest >= width {
                return false;
            }
        }
        true
    }

    fn blasted_application(&self, head: &str, operands: &[usize], rule: &str) -> Option<Blasted> {
        let rule = CheckableRule::new(rule)?;
        Some(self.blasted_application_with_rule(head, operands, rule))
    }

    fn blasted_application_with_rule(
        &self,
        head: &str,
        operands: &[usize],
        rule: CheckableRule,
    ) -> Blasted {
        let mut application = format!("({head}");
        let mut steps = Vec::with_capacity(operands.len());
        for operand in operands {
            application.push(' ');
            application.push_str(&self.bbterm(&self.words[*operand].bits));
            steps.push(self.words[*operand].step.clone());
        }
        application.push(')');
        Blasted {
            blasted_application: application,
            operand_steps: steps,
            rule,
        }
    }
}

/// The checker-facing spelling of one bit-blasting step.
struct Blasted {
    /// The operation with every operand replaced by its `@bbterm` list.
    blasted_application: String,
    /// The steps that justify those replacements, in argument order.
    operand_steps: Vec<String>,
    rule: CheckableRule,
}

// ------------------------------------------------------------------- atoms

impl Blaster<'_, '_> {
    fn true_step(&self) -> String {
        format!("{}.cbbtrue", self.id)
    }

    fn false_step(&self) -> String {
        format!("{}.cbbfalse", self.id)
    }

    /// The two Boolean constants are introduced once, before anything that
    /// consumes them, and re-used as planned input clauses afterwards.
    fn emit_constant_steps(&mut self) -> Option<()> {
        self.circuit.constant(true);
        self.circuit.constant(false);
        let (t, f) = (self.true_step(), self.false_step());
        self.push_step(&format!("(step {t} (cl true) :rule true)"))?;
        self.push_step(&format!("(step {f} (cl (not false)) :rule false)"))
    }

    fn build_bool(&mut self, term: TermId) -> Option<SRef> {
        let data = self.printer.terms.get(term).clone();
        match data {
            TermData::Const(Constant::Bool(value)) => Some(self.circuit.constant(value)),
            TermData::Var(..) => {
                let text = self.printer.format_term(term);
                Some(self.circuit.atom(text))
            }
            TermData::Not(inner) => self.bool_of.get(&inner).copied()?.not(),
            TermData::Ite(cond, then_branch, else_branch) => {
                let c = self.bool_of.get(&cond).copied()?;
                let t = self.bool_of.get(&then_branch).copied()?;
                let e = self.bool_of.get(&else_branch).copied()?;
                Some(self.circuit.ite(c, t, e))
            }
            TermData::App(Symbol::Named(name), args) => match name.as_ref() {
                "and" | "or" if args.len() >= 2 => {
                    let refs = args
                        .iter()
                        .map(|a| self.bool_of.get(a).copied())
                        .collect::<Option<Vec<_>>>()?;
                    Some(if name.as_ref() == "and" {
                        self.circuit.and(refs)
                    } else {
                        self.circuit.or(refs)
                    })
                }
                "xor" if args.len() == 2 => {
                    let a = self.bool_of.get(&args[0]).copied()?;
                    let b = self.bool_of.get(&args[1]).copied()?;
                    Some(self.circuit.xor(a, b))
                }
                "=>" if args.len() == 2 => {
                    let a = self.bool_of.get(&args[0]).copied()?;
                    let b = self.bool_of.get(&args[1]).copied()?;
                    Some(self.circuit.implies(a, b))
                }
                "=" if args.len() == 2 => {
                    if let Some(bridge) = self.offset_bridge(term) {
                        return self.offset_atom(bridge);
                    }
                    let sort = self.printer.terms.sort(args[0]).clone();
                    match sort {
                        Sort::Bool => {
                            let a = self.bool_of.get(&args[0]).copied()?;
                            let b = self.bool_of.get(&args[1]).copied()?;
                            Some(self.circuit.iff(a, b))
                        }
                        Sort::BitVec(_) => {
                            let a = self.word_of_term(args[0])?;
                            let b = self.word_of_term(args[1])?;
                            self.theory_atom(a, b, AtomKind::Equality)
                        }
                        _ => None,
                    }
                }
                "bvult" | "bvslt" if args.len() == 2 => {
                    let a = self.word_of_term(args[0])?;
                    let b = self.word_of_term(args[1])?;
                    let kind = if name.as_ref() == "bvult" {
                        AtomKind::UnsignedLessThan
                    } else {
                        AtomKind::SignedLessThan
                    };
                    self.theory_atom(a, b, kind)
                }
                "bvugt" | "bvuge" | "bvule" | "bvsgt" | "bvsge" | "bvsle" if args.len() == 2 => {
                    let a = self.word_of_term(args[0])?;
                    let b = self.word_of_term(args[1])?;
                    self.derived_order_atom(name.as_ref(), a, b)
                }
                _ => None,
            },
            _ => None,
        }
    }

    /// The conjunction of per-bit equivalences `bitblast_equal` builds. At
    /// width one the checker emits the single equivalence, not a conjunction.
    fn bit_equality(&mut self, left: &[SRef], right: &[SRef]) -> Option<SRef> {
        if left.len() != right.len() || left.is_empty() {
            return None;
        }
        let parts: Vec<SRef> = (0..left.len())
            .map(|i| self.circuit.iff(left[i], right[i]))
            .collect();
        Some(if parts.len() == 1 {
            parts[0]
        } else {
            self.circuit.and(parts)
        })
    }

    /// Link a bit-vector atom to its Boolean circuit and plan the two clauses
    /// that let the SAT layer move between them.
    fn theory_atom(&mut self, left: usize, right: usize, kind: AtomKind) -> Option<SRef> {
        if self.words[left].width != self.words[right].width {
            return None;
        }
        let left_bits = self.words[left].bits.clone();
        let right_bits = self.words[right].bits.clone();
        let (head, rule) = match kind {
            AtomKind::Equality => ("=", "bitblast_equal"),
            AtomKind::UnsignedLessThan => ("bvult", "bitblast_ult"),
            AtomKind::SignedLessThan => ("bvslt", "bitblast_slt"),
        };
        let rule = CheckableRule::new(rule)?;
        let body = format!("({head} {} {})", self.word_ref(left), self.word_ref(right));
        let atom = self.circuit.theory(body);
        let blasted = match kind {
            AtomKind::Equality => self.bit_equality(&left_bits, &right_bits)?,
            AtomKind::UnsignedLessThan => {
                self.circuit.unsigned_less_than(&left_bits, &right_bits)?
            }
            AtomKind::SignedLessThan => self.circuit.signed_less_than(&left_bits, &right_bits)?,
        };
        let application = format!(
            "({head} {} {})",
            self.bbterm(&left_bits),
            self.bbterm(&right_bits)
        );
        let atom_text = self.circuit.text(atom);
        let blasted_text = self.circuit.text(blasted);
        let congruence = self.step_name(".ac");
        let rule_step = self.step_name(".ab");
        let equivalence = self.step_name(".ae");
        let left_step = self.words[left].step.clone();
        let right_step = self.words[right].step.clone();
        self.push_step(&format!(
            "(step {congruence} (cl (= {atom_text} {application})) :rule cong :premises ({left_step} {right_step}))"
        ))?;
        self.push_step(&format!(
            "(step {rule_step} (cl (= {application} {blasted_text})) :rule {rule})"
        ))?;
        self.push_step(&format!(
            "(step {equivalence} (cl (= {atom_text} {blasted_text})) :rule trans :premises ({congruence} {rule_step}))"
        ))?;
        let positive = self.step_name(".ap");
        let negative = self.step_name(".an");
        self.push_step(&format!(
            "(step {positive} (cl (not {atom_text}) {blasted_text}) :rule equiv1 :premises ({equivalence}))"
        ))?;
        self.push_step(&format!(
            "(step {negative} (cl {atom_text} (not {blasted_text})) :rule equiv2 :premises ({equivalence}))"
        ))?;
        self.plan(vec![atom.not()?, blasted], ClauseEmit::Existing(positive))?;
        self.plan(vec![atom, blasted.not()?], ClauseEmit::Existing(negative))?;
        Some(atom)
    }

    /// The bits of the width constant `size`, as the checker spells them,
    /// each pinned to its real value by a `evaluate` step.
    ///
    /// The shift rules build `(bvult y size)` from a constructed bit-vector
    /// term, so the comparator reads `((_ @bit_of i) size)` projections. Those
    /// are free Boolean atoms to the SAT layer, and leaving them free would
    /// let a model set the shift out of range and satisfy the formula. Each is
    /// therefore DERIVED to its value: the projection is ground, so `evaluate`
    /// settles it, and one resolution turns that into the unit clause.
    fn size_constant_bits(&mut self, width: u32) -> Option<Vec<SRef>> {
        if let Some(cached) = self.size_constants.get(&width) {
            return Some(cached.clone());
        }
        if width == 0 || width > MAX_WIDTH {
            return None;
        }
        let literal = format!("#b{:0>width$b}", width, width = width as usize);
        if literal.len() != width as usize + 2 {
            return None;
        }
        let mut bits = Vec::with_capacity(width as usize);
        for index in 0..width {
            let atom = self
                .circuit
                .atom(format!("((_ @bit_of {index}) {literal})"));
            // `index` runs to `width - 1`, past `u32::BITS` at the widest
            // words, where every bit of `width` is zero.
            let value = width.checked_shr(index).is_some_and(|rest| rest & 1 == 1);
            let evaluated = self.step_name(".sv");
            let lifted = self.step_name(".sl");
            let unit = self.step_name(".su");
            let text = self.circuit.text(atom);
            self.push_step(&format!(
                "(step {evaluated} (cl (= {text} {})) :rule evaluate)",
                if value { "true" } else { "false" }
            ))?;
            if value {
                let true_step = self.true_step();
                self.push_step(&format!(
                    "(step {lifted} (cl {text} (not true)) :rule equiv2 :premises ({evaluated}))"
                ))?;
                self.push_step(&format!(
                    "(step {unit} (cl {text}) :rule resolution :premises ({lifted} {true_step}))"
                ))?;
                self.plan(vec![atom], ClauseEmit::Existing(unit))?;
            } else {
                let false_step = self.false_step();
                self.push_step(&format!(
                    "(step {lifted} (cl (not {text}) false) :rule equiv1 :premises ({evaluated}))"
                ))?;
                self.push_step(&format!(
                    "(step {unit} (cl (not {text})) :rule resolution :premises ({lifted} {false_step}))"
                ))?;
                self.plan(vec![atom.not()?], ClauseEmit::Existing(unit))?;
            }
            bits.push(atom);
        }
        self.size_constants.insert(width, bits.clone());
        Some(bits)
    }

    fn plan(&mut self, lits: Vec<SRef>, emit: ClauseEmit) -> Option<()> {
        if self.planned.len() >= MAX_PLANNED_CLAUSES {
            return None;
        }
        self.planned.push(PlannedClause { lits, emit });
        Some(())
    }
}

/// Which bit-vector predicate a theory atom stands for.
#[derive(Clone, Copy)]
enum AtomKind {
    Equality,
    UnsignedLessThan,
    SignedLessThan,
}
