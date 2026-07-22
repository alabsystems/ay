// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Semantic checker for bit-vector theory proof steps.
//!
//! Phase 6 (Alethe / proof-checking story). This module mirrors
//! [`crate::array_proof_check`]: it takes `ay`'s existing [`Proof`] objects and
//! *semantically* validates the bit-vector reasoning steps, rather than trusting
//! them by rule name or clause shape.
//!
//! ## Why this is separate from `ay-proof`'s `bv_bitblast` checker
//!
//! `ay-proof::checker::bv_bitblast` is a *structural / bounded* validator: it
//! pattern-matches the bit-blast clause schema and exhaustively evaluates the
//! clause over a tiny (≤ 8-bit) assignment space. It cannot call the solver,
//! because `ay-dpll` depends on `ay-proof` (a reverse dependency from here would
//! be a cycle). This module lives in `ay-dpll` precisely so it *can* discharge
//! each step with `ay`'s own QF_BV solver, with no width bound.
//!
//! ## What "semantic" means here
//!
//! For each BV [`TheoryLemma`] step we do **not** trust the
//! [`TheoryLemmaKind`] label. Instead we take the step's conclusion clause `C`
//! (a disjunction of literals) and ask `ay` to refute `¬C` under the bit-vector
//! theory. A clause `C` is a *genuine BV-theory tautology* iff `¬C` is UNSAT. We
//! translate the relevant sub-terms into a fresh solver, assert `¬C`, and require
//! `check_sat()` to return **UNSAT**. Anything else (`SAT`, `Unknown`, or a
//! translation we cannot model) is reported, never silently accepted.
//!
//! Because QF_BV (and QF_ABV / QF_AUFBV for the array+UF extensions) is fully
//! decidable, a well-formed BV clause should resolve to a crisp `Valid` or
//! `Invalid`; `Unchecked` is reserved for shapes the translator cannot model.
//!
//! This makes the checker independent of the prover's labelling: a clause that
//! is mislabelled but genuinely entailed is still validated, and a clause that
//! carries the right label but is *not* entailed (e.g. a forged bit-blast
//! conclusion) is rejected.
//!
//! ## Fail-closed contract (HARD requirement)
//!
//! [`check_bv_proof`] only ever reports [`BvStepVerdict::Valid`] for a step
//! whose `¬C` it actually discharged as UNSAT. If a step is outside the BV
//! fragment, contains a node kind the translator does not model, or the
//! discharge returns `SAT`/`Unknown`, the verdict is
//! [`BvStepVerdict::Unchecked`] or [`BvStepVerdict::Invalid`] — never `Valid`.
//! A checker that says "unchecked" is correct; a checker that says "valid" for
//! an unverified step is a bug.
//!
//! ## Fragment limits
//!
//! Only [`TheoryLemmaKind::BvBitBlast`] and [`TheoryLemmaKind::BvBitBlastGate`]
//! steps are *targeted*. Every other step (resolution, EUF/array/arithmetic
//! lemmas, Boolean rules, assumptions, ...) is skipped: this checker makes no
//! claim about it. Within a targeted step, the term translator models the
//! bit-vector + EUF + array + Boolean fragment (variables, constants, every
//! SMT-LIB `bv*` operator, `concat`/`extract`/`zero_extend`/`sign_extend`/
//! `rotate_*`/`repeat`, `select`/`store`, `=`, `distinct`, the Boolean
//! connectives, `ite`, and uninterpreted function applications). Quantifiers,
//! `Int`/`Real` arithmetic operators, floating-point, strings, and other
//! theories cause the step to be reported `Unchecked` (fail-closed), because a
//! fresh QF_(AUF)BV discharge cannot soundly model them.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{Constant, Proof, ProofId, ProofStep, Sort, Symbol, TermData, TermId, TermStore};

use crate::api::{FuncDecl, Logic, Solver, Term};

/// Verdict for a single proof step examined by the bit-vector checker.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BvStepVerdict {
    /// The step's conclusion clause was discharged: `¬clause` is UNSAT under the
    /// bit-vector theory, so the clause is a genuine BV-theory tautology.
    Valid,
    /// The step's conclusion clause is **not** entailed by the BV theory:
    /// `¬clause` is satisfiable. The `reason` gives a precise explanation.
    Invalid {
        /// Human-readable explanation of why the clause is not entailed.
        reason: String,
    },
    /// The checker could not model the step (a node kind outside the supported
    /// fragment, an empty/ill-formed clause, or a non-UNSAT/`Unknown` discharge
    /// result). Fail-closed: never treated as valid.
    Unchecked {
        /// Human-readable explanation of why the step could not be checked.
        reason: String,
    },
}

impl BvStepVerdict {
    /// True only for [`BvStepVerdict::Valid`].
    #[must_use]
    pub fn is_valid(&self) -> bool {
        matches!(self, Self::Valid)
    }

    /// True for [`BvStepVerdict::Invalid`].
    #[must_use]
    pub fn is_invalid(&self) -> bool {
        matches!(self, Self::Invalid { .. })
    }

    /// True for [`BvStepVerdict::Unchecked`].
    #[must_use]
    pub fn is_unchecked(&self) -> bool {
        matches!(self, Self::Unchecked { .. })
    }
}

/// Per-step verdict, paired with the originating [`ProofId`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BvStepReport {
    /// Identifier of the proof step this verdict refers to.
    pub step: ProofId,
    /// The bit-vector lemma kind for this (targeted) step.
    pub kind: ay_core::TheoryLemmaKind,
    /// The verdict for this step.
    pub verdict: BvStepVerdict,
}

/// Aggregate result of checking every step of a proof's bit-vector fragment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BvProofReport {
    /// Per-step reports for the *bit-vector theory-lemma* steps only. Steps the
    /// checker skips (non-BV steps) are not included here.
    pub steps: Vec<BvStepReport>,
}

impl BvProofReport {
    /// Number of targeted BV steps that were semantically validated.
    #[must_use]
    pub fn valid_count(&self) -> usize {
        self.steps.iter().filter(|s| s.verdict.is_valid()).count()
    }

    /// Number of targeted BV steps rejected as not entailed.
    #[must_use]
    pub fn invalid_count(&self) -> usize {
        self.steps.iter().filter(|s| s.verdict.is_invalid()).count()
    }

    /// Number of targeted BV steps the checker could not model (fail-closed).
    #[must_use]
    pub fn unchecked_count(&self) -> usize {
        self.steps
            .iter()
            .filter(|s| s.verdict.is_unchecked())
            .count()
    }

    /// True iff every targeted BV step was semantically validated.
    ///
    /// Returns `true` for a proof with no BV steps (vacuously sound for the BV
    /// fragment). It is the caller's responsibility to also require the
    /// surrounding (non-BV) proof structure to be checked elsewhere.
    #[must_use]
    pub fn all_bv_steps_valid(&self) -> bool {
        self.steps.iter().all(|s| s.verdict.is_valid())
    }

    /// First [`BvStepVerdict::Invalid`] verdict, if any. Useful for tests and
    /// for surfacing the precise rejection reason.
    #[must_use]
    pub fn first_invalid(&self) -> Option<&BvStepReport> {
        self.steps.iter().find(|s| s.verdict.is_invalid())
    }
}

/// Semantically check the bit-vector-theory steps of `proof`.
///
/// Walks every step of `proof`; for each [`ProofStep::TheoryLemma`] whose kind
/// is [`TheoryLemmaKind::BvBitBlast`] or [`TheoryLemmaKind::BvBitBlastGate`], it
/// discharges the negation of the step's conclusion clause with a fresh `ay`
/// solver in a quantifier-free BV-inclusive logic and records a
/// [`BvStepVerdict`]. Non-BV steps are not included in the report.
///
/// `terms` must be the [`TermStore`] the proof's [`TermId`]s belong to (the same
/// store the prover used to build the proof).
///
/// [`TheoryLemmaKind`]: ay_core::TheoryLemmaKind
/// [`TheoryLemmaKind::BvBitBlast`]: ay_core::TheoryLemmaKind::BvBitBlast
/// [`TheoryLemmaKind::BvBitBlastGate`]: ay_core::TheoryLemmaKind::BvBitBlastGate
#[must_use]
pub fn check_bv_proof(proof: &Proof, terms: &TermStore) -> BvProofReport {
    let mut steps = Vec::new();
    for (idx, step) in proof.steps.iter().enumerate() {
        let step_id = ProofId(idx as u32);
        if let ProofStep::TheoryLemma { clause, kind, .. } = step {
            use ay_core::TheoryLemmaKind as K;
            let is_bv = matches!(kind, K::BvBitBlast | K::BvBitBlastGate { .. });
            if !is_bv {
                continue;
            }
            let verdict = check_bv_clause(terms, clause);
            steps.push(BvStepReport {
                step: step_id,
                kind: *kind,
                verdict,
            });
        }
    }
    BvProofReport { steps }
}

/// Discharge a single BV clause: report `Valid` iff `¬clause` is UNSAT under the
/// bit-vector theory.
///
/// The clause is the disjunction of its literals. `¬clause` is the conjunction
/// of the negations of the literals, which we assert into a fresh solver and
/// require to be UNSAT.
pub fn check_bv_clause(terms: &TermStore, clause: &[TermId]) -> BvStepVerdict {
    if clause.is_empty() {
        return BvStepVerdict::Unchecked {
            reason: "bv lemma clause is empty; nothing to discharge".to_string(),
        };
    }

    // A single-element clause may itself be an `(or ...)` term: flatten it so we
    // negate the actual disjunction rather than a structurally-nested literal.
    let literals = flatten_clause(terms, clause);

    // Mixed Int+BV obligations cannot be soundly discharged by this thin
    // word-level translator (see `problem_mixes_int_and_bv`): the QF_BV coercion
    // of the unbounded `Int` sub-terms can forge a `Valid`. Fail closed.
    if problem_mixes_int_and_bv(terms, &literals) {
        return BvStepVerdict::Unchecked {
            reason: "clause mixes Int and BitVec sub-terms; the thin word-level \
                     checker would lossily coerce the Int side to QF_BV and risk a \
                     forged UNSAT, so it fails closed (the full Executor decides the \
                     BV<->LIA bridge)"
                .to_string(),
        };
    }

    // Pick the smallest QF logic that subsumes the clause content. Pure BV uses
    // QF_BV; clauses that also mention arrays and/or uninterpreted functions use
    // the BV-inclusive array+UF logic so the discharge can model them. All of
    // these are decidable, so a well-formed clause resolves to UNSAT or SAT.
    let logic = pick_logic(terms, &literals);
    let mut solver = Solver::new(logic);
    let mut translator = Translator::new();

    // Assert the negation of each literal of the clause. `¬(l1 ∨ ... ∨ ln)` is
    // `¬l1 ∧ ... ∧ ¬ln`.
    for &lit in &literals {
        let translated = match translator.translate(&mut solver, terms, lit) {
            Ok(t) => t,
            Err(reason) => {
                return BvStepVerdict::Unchecked {
                    reason: format!("cannot model clause literal: {reason}"),
                };
            }
        };
        // The literal must be Boolean-sorted to negate and assert it.
        if !solver_is_bool(&solver, translated) {
            return BvStepVerdict::Unchecked {
                reason: "clause literal is not Bool-sorted; BV lemma clauses must \
                         be propositional"
                    .to_string(),
            };
        }
        let negated = solver.not(translated);
        solver.assert_term(negated);
    }

    let result = solver.check_sat();
    if result.is_unsat() {
        BvStepVerdict::Valid
    } else if result.is_sat() {
        BvStepVerdict::Invalid {
            reason: "negation of the clause is satisfiable under the bit-vector \
                     theory: the clause is not a BV-theory tautology (e.g. a \
                     forged bit-blast conclusion, a wrong operand/width, or a \
                     gate identity that does not hold)"
                .to_string(),
        }
    } else {
        BvStepVerdict::Unchecked {
            reason: "discharge returned Unknown; cannot certify the clause".to_string(),
        }
    }
}

/// Independently re-discharge a whole problem's assertion set as UNSAT under the
/// bit-vector theory.
///
/// This is the assertion-set analogue of [`check_bv_clause`]. Where
/// `check_bv_clause` proves a single *clause* is a tautology by refuting its
/// negation, this proves a *conjunction of asserted obligations* is jointly
/// unsatisfiable: it translates each assertion into a fresh QF_(AUF)BV solver,
/// asserts it **positively** (no negation), and requires `check_sat()` to return
/// **UNSAT**.
///
/// It is the sound discharge for the degenerate proof shape `ay` emits when it
/// decides a problem UNSAT but exports only a bare terminal `trust` empty clause
/// (no premises, no theory-lemma content): the proof object carries nothing to
/// re-check, so the only honest independent certificate is to re-solve the
/// ORIGINAL assertions and confirm UNSAT here, in a fresh solver, with the
/// fail-closed translator.
///
/// Fail-closed exactly like [`check_bv_clause`]:
/// - any assertion the translator cannot model → [`BvStepVerdict::Unchecked`];
/// - a non-`Bool` assertion → `Unchecked`;
/// - `check_sat() == SAT` (the assertions are satisfiable, so the UNSAT claim is
///   bogus / forged) → [`BvStepVerdict::Invalid`];
/// - `Unknown` → `Unchecked`.
///
/// `Valid` is returned ONLY when an independent solve confirms the assertions are
/// jointly UNSAT. An empty assertion set is `Unchecked` (an empty conjunction is
/// trivially SAT, so it is never a valid UNSAT discharge).
pub fn check_bv_assertions_unsat(terms: &TermStore, assertions: &[TermId]) -> BvStepVerdict {
    if assertions.is_empty() {
        return BvStepVerdict::Unchecked {
            reason: "assertion set is empty; an empty conjunction is satisfiable, \
                     so it cannot witness UNSAT"
                .to_string(),
        };
    }

    // Mixed Int+BV assertion sets cannot be soundly discharged by this thin
    // word-level translator (see `problem_mixes_int_and_bv`): pure `QF_BV` would
    // lossily coerce the unbounded `Int` obligations (e.g. the `#nia-oom`
    // allocation VC's `count = bv2nat(bvshl(int2bv 1, int2bv 28))` pinned against
    // an integer ceiling and `u64::MAX` bounds) and can return a SPURIOUS UNSAT,
    // forging `Valid`. Fail closed — the deferred-trust rescue still re-confirms a
    // genuine UNSAT through the full Executor (`executor_reconfirms_unsat`).
    if problem_mixes_int_and_bv(terms, assertions) {
        return BvStepVerdict::Unchecked {
            reason: "assertion set mixes Int and BitVec sub-terms; the thin \
                     word-level checker would lossily coerce the Int side to QF_BV \
                     and risk a forged UNSAT, so it fails closed (the full Executor \
                     decides the BV<->LIA bridge)"
                .to_string(),
        };
    }

    let logic = pick_logic(terms, assertions);
    let mut solver = Solver::new(logic);
    let mut translator = Translator::new();

    // Assert each obligation POSITIVELY: we want UNSAT of their conjunction.
    for &assertion in assertions {
        let translated = match translator.translate(&mut solver, terms, assertion) {
            Ok(t) => t,
            Err(reason) => {
                return BvStepVerdict::Unchecked {
                    reason: format!("cannot model assertion: {reason}"),
                };
            }
        };
        if !solver_is_bool(&solver, translated) {
            return BvStepVerdict::Unchecked {
                reason: "assertion is not Bool-sorted; cannot assert it for an \
                         UNSAT discharge"
                    .to_string(),
            };
        }
        solver.assert_term(translated);
    }

    let result = solver.check_sat();
    if result.is_unsat() {
        BvStepVerdict::Valid
    } else if result.is_sat() {
        BvStepVerdict::Invalid {
            reason: "the asserted obligations are jointly satisfiable under the \
                     bit-vector theory: the UNSAT claim is not independently \
                     reproducible (a satisfying assignment exists)"
                .to_string(),
        }
    } else {
        BvStepVerdict::Unchecked {
            reason: "discharge returned Unknown; cannot independently certify the \
                     assertions as UNSAT"
                .to_string(),
        }
    }
}

/// True iff the term set mixes both `Int`-sorted and `BitVec`-sorted sub-terms.
///
/// SOUNDNESS GUARD for the thin word-level discharge (`check_bv_clause` /
/// `check_bv_assertions_unsat`). A mixed Int+BV obligation has NO sound home in
/// this checker's QF-logic menu: `pick_logic`'s LIA arm is gated on
/// `has_int && !has_bv`, so a mixed problem falls through to pure `QF_BV`, and the
/// `Translator` then LOSSILY coerces the unbounded `Int` sub-terms (and any wide
/// literal — e.g. `u64::MAX`, which a signed BV coercion turns into `-1`) into
/// bit-vectors. That coercion can flip a genuinely SATISFIABLE mixed problem to a
/// SPURIOUS `unsat`, which would be reported as `Valid` — a forged UNSAT (the
/// `#nia-oom` `bv2nat(bvshl(int2bv 1, int2bv 28)) == count >= ceiling` allocation
/// VC). Deciding the BV<->LIA bridge soundly is the full `Executor`'s job (logic
/// detection + the combined theory loop), not this re-translation checker; the
/// deferred-trust rescue already re-confirms via the Executor
/// (`executor_reconfirms_unsat`) and its forged-UNSAT dual
/// (`executor_redecides_definitive_sat`). So a mixed problem must fail-closed
/// (`Unchecked`) here rather than risk a `Valid`.
pub(crate) fn problem_mixes_int_and_bv(terms: &TermStore, literals: &[TermId]) -> bool {
    let mut has_array = false;
    let mut has_uf = false;
    let mut has_int = false;
    let mut has_bv = false;
    let mut visited = std::collections::HashSet::new();
    for &lit in literals {
        scan_features(
            terms,
            lit,
            &mut has_array,
            &mut has_uf,
            &mut has_int,
            &mut has_bv,
            &mut visited,
        );
    }
    has_int && has_bv
}

/// Choose the QF logic to discharge `literals` in. Defaults to pure `QF_BV`;
/// widens to `QF_ABV`/`QF_AUFBV` when the clause mentions arrays and/or
/// uninterpreted function applications, so those sub-terms can be modelled
/// soundly. Every choice is a decidable QF logic.
fn pick_logic(terms: &TermStore, literals: &[TermId]) -> Logic {
    let mut has_array = false;
    let mut has_uf = false;
    let mut has_int = false;
    let mut has_bv = false;
    let mut visited = std::collections::HashSet::new();
    for &lit in literals {
        scan_features(
            terms,
            lit,
            &mut has_array,
            &mut has_uf,
            &mut has_int,
            &mut has_bv,
            &mut visited,
        );
    }
    // LIA extension: an obligation mentioning Int terms (and no bit-vector terms)
    // is discharged under a linear-integer-arithmetic logic, so the modular `ite`
    // model of a `wrapping_{add,sub}` can be re-decided independently. A mixed
    // Int+BV obligation stays on the BV logic — its Int sub-terms then fail to
    // translate and the discharge returns Unchecked (fail-closed). Trust's
    // wrapping model is pure-Int, so the mixed case never bites it.
    if has_int && !has_bv {
        return match (has_array, has_uf) {
            (false, false) => Logic::QfLia,
            (false, true) => Logic::QfUflia,
            (true, _) => Logic::QfAuflia,
        };
    }
    match (has_array, has_uf) {
        (false, false) => Logic::QfBv,
        (true, false) => Logic::QfAbv,
        (false, true) => Logic::QfUfbv,
        (true, true) => Logic::QfAufbv,
    }
}

/// Walk a term, noting whether it mentions array sorts/operators or
/// uninterpreted function applications. Sub-term sharing is respected via a
/// `visited` set so this stays linear in the (hash-consed) DAG size.
fn scan_features(
    terms: &TermStore,
    tid: TermId,
    has_array: &mut bool,
    has_uf: &mut bool,
    has_int: &mut bool,
    has_bv: &mut bool,
    visited: &mut std::collections::HashSet<TermId>,
) {
    if !visited.insert(tid) {
        return;
    }
    match terms.sort(tid) {
        Sort::Array(_) => *has_array = true,
        Sort::Int => *has_int = true,
        Sort::BitVec(_) => *has_bv = true,
        _ => {}
    }
    match terms.get(tid) {
        TermData::App(sym, args) => {
            let name = sym.name();
            if matches!(name, "select" | "store") {
                *has_array = true;
            } else if is_uninterpreted_app(sym) {
                *has_uf = true;
            }
            for &a in args {
                scan_features(terms, a, has_array, has_uf, has_int, has_bv, visited);
            }
        }
        TermData::Not(inner) => {
            scan_features(terms, *inner, has_array, has_uf, has_int, has_bv, visited)
        }
        TermData::Ite(c, t, e) => {
            scan_features(terms, *c, has_array, has_uf, has_int, has_bv, visited);
            scan_features(terms, *t, has_array, has_uf, has_int, has_bv, visited);
            scan_features(terms, *e, has_array, has_uf, has_int, has_bv, visited);
        }
        _ => {}
    }
}

/// If `clause` is a single `(or l1 ... ln)` term, return its disjuncts;
/// otherwise return the clause literals as-is.
fn flatten_clause(terms: &TermStore, clause: &[TermId]) -> Vec<TermId> {
    if clause.len() == 1 {
        if let TermData::App(sym, args) = terms.get(clause[0]) {
            if sym.name() == "or" {
                return args.clone();
            }
        }
    }
    clause.to_vec()
}

fn solver_is_bool(solver: &Solver, term: Term) -> bool {
    matches!(solver.term_sort(term), Sort::Bool)
}

/// Translates terms from a proof's [`TermStore`] into a fresh [`Solver`],
/// preserving sub-term sharing so semantically-equal sub-terms map to identical
/// solver terms (required for a sound discharge).
struct Translator {
    /// Memo of proof `TermId` -> translated solver `Term`.
    memo: HashMap<TermId, Term>,
    /// Declared uninterpreted function symbols, keyed by `(name, arg_sorts, ret)`.
    funcs: HashMap<(String, Vec<Sort>, Sort), FuncDecl>,
    /// Counter for unique leaf-constant names.
    next_id: u32,
}

impl Translator {
    fn new() -> Self {
        Self {
            memo: HashMap::default(),
            funcs: HashMap::default(),
            next_id: 0,
        }
    }

    fn fresh_name(&mut self, prefix: &str) -> String {
        let id = self.next_id;
        self.next_id += 1;
        format!("{prefix}_{id}")
    }

    /// Translate proof term `tid` into the solver, recursively. Returns `Err`
    /// with a fragment-limit reason for any node kind we cannot soundly model.
    fn translate(
        &mut self,
        solver: &mut Solver,
        terms: &TermStore,
        tid: TermId,
    ) -> Result<Term, String> {
        if let Some(t) = self.memo.get(&tid) {
            return Ok(*t);
        }
        let result = self.translate_uncached(solver, terms, tid)?;
        self.memo.insert(tid, result);
        Ok(result)
    }

    fn translate_uncached(
        &mut self,
        solver: &mut Solver,
        terms: &TermStore,
        tid: TermId,
    ) -> Result<Term, String> {
        match terms.get(tid).clone() {
            TermData::Var(name, _) => {
                // Distinct proof TermIds are distinct terms in a hash-consed
                // store, so a per-TermId-unique solver constant is sound. We
                // include the original name only for readability.
                let sort = terms.sort(tid).clone();
                let sort = supported_sort(&sort)?;
                let cname = self.fresh_name(&format!("c_{name}"));
                Ok(solver.declare_const(&cname, sort))
            }
            TermData::Const(c) => self.translate_const(solver, &c),
            TermData::Not(inner) => {
                let t = self.translate(solver, terms, inner)?;
                Ok(solver.not(t))
            }
            TermData::Ite(cond, then_t, else_t) => {
                let c = self.translate(solver, terms, cond)?;
                let a = self.translate(solver, terms, then_t)?;
                let b = self.translate(solver, terms, else_t)?;
                Ok(solver.ite(c, a, b))
            }
            TermData::App(sym, args) => self.translate_app(solver, terms, tid, &sym, &args),
            TermData::Let(..) => {
                Err("`let` binding in clause (should be expanded before proof)".to_string())
            }
            TermData::Forall(..) | TermData::Exists(..) => {
                Err("quantifier in clause; QF discharge cannot model it".to_string())
            }
            // `TermData` is `#[non_exhaustive]`: fail closed on any future node.
            other => Err(format!(
                "unsupported term node {other:?} outside the modelled BV fragment"
            )),
        }
    }

    fn translate_const(&mut self, solver: &mut Solver, c: &Constant) -> Result<Term, String> {
        match c {
            Constant::Bool(b) => Ok(solver.bool_const(*b)),
            Constant::BitVec { value, width } => Ok(solver.bv_const_bigint(value, *width)),
            // Int constant (LIA extension): modelled directly as an integer
            // literal. Arbitrary-precision so a wide modulus (e.g. 2^32) is exact.
            Constant::Int(n) => Ok(solver.int_const_bigint(n)),
            Constant::Rational(_) => {
                Err("rational constant outside the QF_BV fragment".to_string())
            }
            Constant::String(_) => Err("string constant outside the QF_BV fragment".to_string()),
            // `Constant` is `#[non_exhaustive]`: fail closed on any future kind.
            other => Err(format!(
                "unsupported constant {other:?} outside the QF_BV fragment"
            )),
        }
    }

    #[allow(clippy::too_many_lines)]
    fn translate_app(
        &mut self,
        solver: &mut Solver,
        terms: &TermStore,
        tid: TermId,
        sym: &Symbol,
        args: &[TermId],
    ) -> Result<Term, String> {
        // Indexed BV operators (extract / extend / rotate / repeat) carry their
        // numeric parameters in the symbol, not the argument list.
        if let Symbol::Indexed(name, indices) = sym {
            return self.translate_indexed(solver, terms, name, indices, args);
        }

        let name = sym.name();
        // Translate children first (shared via memo).
        let mut targs: Vec<Term> = Vec::with_capacity(args.len());
        for &a in args {
            targs.push(self.translate(solver, terms, a)?);
        }

        // Boolean / core operators and equality / arrays.
        match (name, targs.as_slice()) {
            ("=", [a, b]) => {
                return solver
                    .try_eq(*a, *b)
                    .map_err(|e| format!("eq translation failed: {e}"));
            }
            ("distinct", _) if targs.len() >= 2 => {
                return solver
                    .try_distinct(&targs)
                    .map_err(|e| format!("distinct translation failed: {e}"));
            }
            ("not", [a]) => return Ok(solver.not(*a)),
            ("and", _) if !targs.is_empty() => {
                return Ok(fold_binary(&targs, |acc, t| solver.and(acc, t)));
            }
            ("or", _) if !targs.is_empty() => {
                return Ok(fold_binary(&targs, |acc, t| solver.or(acc, t)));
            }
            ("=>", [a, b]) => return Ok(solver.implies(*a, *b)),
            ("xor", [a, b]) => return Ok(solver.xor(*a, *b)),
            ("ite", [c, a, b]) => return Ok(solver.ite(*c, *a, *b)),
            ("select", [array, index]) => {
                return solver
                    .try_select(*array, *index)
                    .map_err(|e| format!("select translation failed: {e}"));
            }
            ("store", [array, index, value]) => {
                return solver
                    .try_store(*array, *index, *value)
                    .map_err(|e| format!("store translation failed: {e}"));
            }
            _ => {}
        }

        // Linear-integer arithmetic / order operators (LIA extension). Lets the
        // independent UNSAT re-discharge model the modular `ite` definitions
        // deductive-checksgen emits for `wrapping_{add,sub}` (`a+b`, `a-b`, the `>= 2^w`
        // wrap test, the operand range bounds). N-ary `+`/`*` fold left; `-` is
        // binary subtract — the wrapping model never emits unary negation.
        match (name, targs.as_slice()) {
            ("+", _) if !targs.is_empty() => {
                return Ok(fold_binary(&targs, |acc, t| solver.add(acc, t)));
            }
            ("*", _) if !targs.is_empty() => {
                return Ok(fold_binary(&targs, |acc, t| solver.mul(acc, t)));
            }
            ("-", [a, b]) => return Ok(solver.sub(*a, *b)),
            // Unary minus (negation) — ay canonicalises `a - b` to `a + (- b)`, so
            // the re-discharge must model `(- x)` as `0 - x`.
            ("-", [a]) => {
                let zero = solver.int_const(0);
                return Ok(solver.sub(zero, *a));
            }
            ("<", [a, b]) => return Ok(solver.lt(*a, *b)),
            ("<=", [a, b]) => return Ok(solver.le(*a, *b)),
            (">", [a, b]) => return Ok(solver.gt(*a, *b)),
            (">=", [a, b]) => return Ok(solver.ge(*a, *b)),
            _ => {}
        }

        // Named BV operators.
        if let Some(t) = self.translate_named_bv(solver, name, &targs) {
            return t;
        }

        // An uninterpreted function application (e.g. inside a BV congruence
        // clause). Model it as a declared function so congruence holds.
        if is_uninterpreted_app(sym) {
            return self.translate_uninterpreted(solver, terms, tid, name, args, &targs);
        }

        Err(format!(
            "operator `{name}`/{} outside the modelled BV+EUF+array+Bool fragment",
            args.len()
        ))
    }

    /// Translate a named (non-indexed) bit-vector operator. Returns `None` when
    /// `name` is not a recognised BV operator (so the caller can fall through to
    /// the uninterpreted-function path).
    #[allow(clippy::too_many_lines)]
    fn translate_named_bv(
        &mut self,
        solver: &mut Solver,
        name: &str,
        targs: &[Term],
    ) -> Option<Result<Term, String>> {
        // Binary BV arithmetic / bitwise / shift / comparison operators.
        if let [a, b] = targs {
            let (a, b) = (*a, *b);
            let r = match name {
                "bvadd" => solver.bvadd(a, b),
                "bvsub" => solver.bvsub(a, b),
                "bvmul" => solver.bvmul(a, b),
                "bvand" => solver.bvand(a, b),
                "bvor" => solver.bvor(a, b),
                "bvxor" => solver.bvxor(a, b),
                "bvnand" => solver.bvnand(a, b),
                "bvnor" => solver.bvnor(a, b),
                "bvxnor" => solver.bvxnor(a, b),
                "bvshl" => solver.bvshl(a, b),
                "bvlshr" => solver.bvlshr(a, b),
                "bvashr" => solver.bvashr(a, b),
                "bvudiv" => solver.bvudiv(a, b),
                "bvurem" => solver.bvurem(a, b),
                "bvsdiv" => solver.bvsdiv(a, b),
                "bvsrem" => solver.bvsrem(a, b),
                "bvsmod" => solver.bvsmod(a, b),
                "bvult" => solver.bvult(a, b),
                "bvule" => solver.bvule(a, b),
                "bvugt" => solver.bvugt(a, b),
                "bvuge" => solver.bvuge(a, b),
                "bvslt" => solver.bvslt(a, b),
                "bvsle" => solver.bvsle(a, b),
                "bvsgt" => solver.bvsgt(a, b),
                "bvsge" => solver.bvsge(a, b),
                "bvcomp" => solver.bvcomp(a, b),
                "concat" => return Some(self.bvconcat(solver, a, b)),
                _ => return None,
            };
            return Some(Ok(r));
        }

        // Unary BV operators.
        if let [a] = targs {
            let a = *a;
            let r = match name {
                "bvnot" => solver.bvnot(a),
                "bvneg" => solver.bvneg(a),
                _ => return None,
            };
            return Some(Ok(r));
        }

        // Variadic associative operators occasionally appear flattened.
        if !targs.is_empty() {
            match name {
                "bvadd" => return Some(Ok(fold_binary(targs, |acc, t| solver.bvadd(acc, t)))),
                "bvmul" => return Some(Ok(fold_binary(targs, |acc, t| solver.bvmul(acc, t)))),
                "bvand" => return Some(Ok(fold_binary(targs, |acc, t| solver.bvand(acc, t)))),
                "bvor" => return Some(Ok(fold_binary(targs, |acc, t| solver.bvor(acc, t)))),
                "bvxor" => return Some(Ok(fold_binary(targs, |acc, t| solver.bvxor(acc, t)))),
                "concat" => return Some(self.bvconcat_many(solver, targs)),
                _ => {}
            }
        }

        None
    }

    fn bvconcat(&mut self, solver: &mut Solver, a: Term, b: Term) -> Result<Term, String> {
        solver
            .try_bvconcat(a, b)
            .map_err(|e| format!("concat translation failed: {e}"))
    }

    fn bvconcat_many(&mut self, solver: &mut Solver, targs: &[Term]) -> Result<Term, String> {
        let mut iter = targs.iter().copied();
        let mut acc = iter.next().expect("non-empty checked by caller");
        for t in iter {
            acc = self.bvconcat(solver, acc, t)?;
        }
        Ok(acc)
    }

    /// Translate an indexed BV operator: `extract`, `zero_extend`,
    /// `sign_extend`, `rotate_left`, `rotate_right`, `repeat`.
    fn translate_indexed(
        &mut self,
        solver: &mut Solver,
        terms: &TermStore,
        name: &str,
        indices: &[u32],
        args: &[TermId],
    ) -> Result<Term, String> {
        let mut targs: Vec<Term> = Vec::with_capacity(args.len());
        for &a in args {
            targs.push(self.translate(solver, terms, a)?);
        }
        match (name, indices, targs.as_slice()) {
            ("extract", [high, low], [a]) => solver
                .try_bvextract(*a, *high, *low)
                .map_err(|e| format!("extract translation failed: {e}")),
            ("zero_extend", [n], [a]) => solver
                .try_bvzeroext(*a, *n)
                .map_err(|e| format!("zero_extend translation failed: {e}")),
            ("sign_extend", [n], [a]) => solver
                .try_bvsignext(*a, *n)
                .map_err(|e| format!("sign_extend translation failed: {e}")),
            ("rotate_left", [n], [a]) => Ok(solver.bvrotl(*a, *n)),
            ("rotate_right", [n], [a]) => Ok(solver.bvrotr(*a, *n)),
            ("repeat", [n], [a]) => Ok(solver.bvrepeat(*a, *n)),
            _ => Err(format!(
                "indexed operator `(_ {name} ...)` with {} indices / {} args is \
                 outside the modelled BV fragment",
                indices.len(),
                args.len()
            )),
        }
    }

    fn translate_uninterpreted(
        &mut self,
        solver: &mut Solver,
        terms: &TermStore,
        tid: TermId,
        name: &str,
        args: &[TermId],
        targs: &[Term],
    ) -> Result<Term, String> {
        // A reserved builtin theory-operator name must NEVER be re-declared as an
        // uninterpreted function. The explicit dispatch above already handles the
        // BV operators this checker models; anything reserved that reaches here
        // (e.g. a BV overflow predicate `bvsaddo`/`bvumulo`, or a `bv2nat`/
        // `int2bv` bridge op) is outside the faithfully-modelled fragment.
        // Declaring it would (a) drop the builtin's real semantics and, for the
        // indexed ops, its stripped indices — a wrong-Valid hazard — and (b) hit
        // ay-frontend's reserved-symbol gate, whose rejection the panicking
        // `Solver::declare_fun` wrapper turns into an ICE. Fail closed instead
        // (`Unchecked`); the whole-problem Executor re-solve is the sound
        // certificate for such clauses.
        if ay_frontend::is_reserved_symbol(name) {
            return Err(format!(
                "operator `{name}` is a reserved builtin theory operator; it is \
                 outside the modelled BV+EUF+array+Bool fragment and must not be \
                 re-declared as an uninterpreted function"
            ));
        }
        let arg_sorts: Vec<Sort> = args
            .iter()
            .map(|&a| supported_sort(terms.sort(a)))
            .collect::<Result<_, _>>()?;
        let ret = supported_sort(terms.sort(tid))?;
        let key = (name.to_string(), arg_sorts.clone(), ret.clone());
        let decl = if let Some(d) = self.funcs.get(&key) {
            d.clone()
        } else {
            let d = solver.declare_fun(name, &arg_sorts, ret);
            self.funcs.insert(key, d.clone());
            d
        };
        Ok(solver.apply(&decl, targs))
    }
}

/// Fold a non-empty slice of terms left-associatively with a binary builder.
fn fold_binary(terms: &[Term], f: impl FnMut(Term, Term) -> Term) -> Term {
    let mut iter = terms.iter().copied();
    let first = iter.next().expect("fold_binary requires a non-empty slice");
    iter.fold(first, f)
}

/// Built-in operators handled explicitly by the translator. Anything else with
/// a `Named` symbol is treated as an uninterpreted function symbol (the EUF
/// fragment). Indexed symbols are never uninterpreted here — they are handled by
/// [`Translator::translate_indexed`] or rejected.
fn is_uninterpreted_app(sym: &Symbol) -> bool {
    let Symbol::Named(name) = sym else {
        return false;
    };
    !matches!(
        name.as_str(),
        // Core / Boolean / equality / arrays.
        "=" | "distinct"
            | "not"
            | "and"
            | "or"
            | "=>"
            | "xor"
            | "ite"
            | "select"
            | "store"
            // Bit-vector operators.
            | "bvadd" | "bvsub" | "bvmul"
            | "bvand" | "bvor" | "bvxor" | "bvnand" | "bvnor" | "bvxnor"
            | "bvnot" | "bvneg"
            | "bvshl" | "bvlshr" | "bvashr"
            | "bvudiv" | "bvurem" | "bvsdiv" | "bvsrem" | "bvsmod"
            | "bvult" | "bvule" | "bvugt" | "bvuge"
            | "bvslt" | "bvsle" | "bvsgt" | "bvsge"
            | "bvcomp"
            | "concat"
            // Arithmetic operators are NOT uninterpreted; treating them so would
            // be unsound. List the common ones so they fall through to a
            // fragment error instead of being modelled as opaque UFs.
            | "+" | "-" | "*" | "/" | "div" | "mod" | "abs"
            | "<" | "<=" | ">" | ">="
    )
}

/// Accept only sorts that the QF_(AUF)BV discharge can model soundly. `Bool`,
/// `BitVec`, uninterpreted sorts, and arrays whose index/element sorts are
/// themselves supported are fine. Arithmetic (`Int`/`Real`), quantifier,
/// floating-point, string, datatype, and sequence sorts are rejected.
fn supported_sort(sort: &Sort) -> Result<Sort, String> {
    match sort {
        // `Sort::Int` admitted for the LIA extension (the independent UNSAT
        // re-discharge of an integer obligation, e.g. deductive-checksgen's modular
        // `ite` model of a `wrapping_{add,sub}`). `pick_logic` selects an LIA
        // logic whenever Int terms are present, so this is decidable.
        Sort::Bool | Sort::BitVec(_) | Sort::Int | Sort::Uninterpreted(_) => Ok(sort.clone()),
        Sort::Array(arr) => {
            let idx = supported_sort(&arr.index_sort)?;
            let elem = supported_sort(&arr.element_sort)?;
            Ok(Sort::array(idx, elem))
        }
        other => Err(format!(
            "sort {other:?} is outside the modelled BV fragment"
        )),
    }
}

#[cfg(test)]
#[path = "bv_proof_check_tests.rs"]
mod tests;
