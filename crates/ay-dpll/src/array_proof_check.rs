// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Semantic checker for theory-of-arrays (select/store) proof steps.
//!
//! Phase 6 (Alethe / proof-checking story). This module takes `ay`'s existing
//! [`Proof`] objects and *semantically* validates the array-theory reasoning
//! steps, rather than trusting them by rule name or clause shape.
//!
//! ## Why this is separate from `ay-proof`'s `array_axiom` checker
//!
//! `ay-proof::checker::array_axiom` is a *structural* (syntactic) validator: it
//! pattern-matches the canonical read-over-write / extensionality clause shapes.
//! It cannot call the solver, because `ay-dpll` depends on `ay-proof` (a
//! reverse dependency from here would be a cycle). This module lives in
//! `ay-dpll` precisely so it *can* discharge each step with `ay`'s own solver.
//!
//! ## What "semantic" means here
//!
//! For each array `TheoryLemma` step we do **not** trust the
//! [`TheoryLemmaKind`] label. Instead we take the step's conclusion clause `C`
//! (a disjunction of literals) and ask `ay` to refute `¬C` under the array
//! theory (`QF_AX`). A clause `C` is a *genuine array-theory tautology* iff
//! `¬C` is UNSAT. We translate the relevant sub-terms into a fresh solver,
//! assert `¬C`, and require `check_sat()` to return **UNSAT**. Anything else
//! (`SAT`, `Unknown`, or a translation we cannot model) is reported, never
//! silently accepted.
//!
//! This makes the checker independent of the prover's labelling: a clause that
//! is mislabelled but genuinely entailed (e.g. an EUF congruence clause tagged
//! `read_over_write_neg`) is still validated, and a clause that carries the
//! right label but is *not* entailed (e.g. a read-over-write conclusion with a
//! missing `i ≠ j` guard) is rejected.
//!
//! ## Fail-closed contract (HARD requirement)
//!
//! [`check_array_proof`] only ever reports [`ArrayStepVerdict::Valid`] for a
//! step whose `¬C` it actually discharged as UNSAT. If a step is outside the
//! array fragment, contains a node kind the translator does not model, or the
//! discharge returns `SAT`/`Unknown`, the verdict is
//! [`ArrayStepVerdict::Unchecked`] or [`ArrayStepVerdict::Invalid`] — never
//! `Valid`. A checker that says "unchecked" is correct; a checker that says
//! "valid" for an unverified step is a bug.
//!
//! ## Fragment limits
//!
//! Only [`TheoryLemmaKind::ArraySelectStore`] and
//! [`TheoryLemmaKind::ArrayExtensionality`] steps are *targeted*. Every other
//! step (resolution, EUF lemmas, Boolean rules, assumptions, ...) is reported
//! as [`ArrayStepVerdict::Skipped`]: this checker makes no claim about it.
//! Within a targeted step, the term translator models the array + EUF +
//! Boolean fragment (variables, constants, `select`, `store`, `=`, `distinct`,
//! `not`/`and`/`or`/`=>`/`xor`/`ite`, and uninterpreted function applications).
//! Quantifiers, arithmetic operators, bit-vectors, and other theories cause the
//! step to be reported `Unchecked` (fail-closed), because a fresh `QF_AX`
//! discharge cannot soundly model them.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{Constant, Proof, ProofId, ProofStep, Sort, TermData, TermId, TermStore};

use crate::api::proofs::TrustClauseDischargeControls;
use crate::api::{FuncDecl, Logic, Solver, Term};

/// Verdict for a single proof step examined by the array checker.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ArrayStepVerdict {
    /// This is not an array theory-lemma step; the array checker makes no claim.
    Skipped,
    /// The step's conclusion clause was discharged: `¬clause` is UNSAT under the
    /// array theory, so the clause is a genuine array-theory tautology.
    Valid,
    /// The step's conclusion clause is **not** entailed by the array axioms:
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

impl ArrayStepVerdict {
    /// True only for [`ArrayStepVerdict::Valid`].
    #[must_use]
    pub fn is_valid(&self) -> bool {
        matches!(self, Self::Valid)
    }

    /// True for [`ArrayStepVerdict::Invalid`].
    #[must_use]
    pub fn is_invalid(&self) -> bool {
        matches!(self, Self::Invalid { .. })
    }

    /// True for [`ArrayStepVerdict::Unchecked`].
    #[must_use]
    pub fn is_unchecked(&self) -> bool {
        matches!(self, Self::Unchecked { .. })
    }
}

/// Per-step verdict, paired with the originating [`ProofId`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArrayStepReport {
    /// Identifier of the proof step this verdict refers to.
    pub step: ProofId,
    /// The array-theory lemma kind, when the step was a targeted array lemma.
    pub kind: Option<ay_core::TheoryLemmaKind>,
    /// The verdict for this step.
    pub verdict: ArrayStepVerdict,
}

/// Aggregate result of checking every step of a proof's array fragment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArrayProofReport {
    /// Per-step reports for the *array theory-lemma* steps only. Steps the
    /// checker skips (non-array steps) are not included here.
    pub steps: Vec<ArrayStepReport>,
}

impl ArrayProofReport {
    /// Number of targeted array steps that were semantically validated.
    #[must_use]
    pub fn valid_count(&self) -> usize {
        self.steps.iter().filter(|s| s.verdict.is_valid()).count()
    }

    /// Number of targeted array steps rejected as not entailed.
    #[must_use]
    pub fn invalid_count(&self) -> usize {
        self.steps.iter().filter(|s| s.verdict.is_invalid()).count()
    }

    /// Number of targeted array steps the checker could not model (fail-closed).
    #[must_use]
    pub fn unchecked_count(&self) -> usize {
        self.steps
            .iter()
            .filter(|s| s.verdict.is_unchecked())
            .count()
    }

    /// True iff every targeted array step was semantically validated.
    ///
    /// Returns `true` for a proof with no array steps (vacuously sound for the
    /// array fragment). It is the caller's responsibility to also require the
    /// surrounding (non-array) proof structure to be checked elsewhere.
    #[must_use]
    pub fn all_array_steps_valid(&self) -> bool {
        self.steps.iter().all(|s| s.verdict.is_valid())
    }

    /// First [`ArrayStepVerdict::Invalid`] verdict, if any. Useful for tests and
    /// for surfacing the precise rejection reason.
    #[must_use]
    pub fn first_invalid(&self) -> Option<&ArrayStepReport> {
        self.steps.iter().find(|s| s.verdict.is_invalid())
    }
}

/// Semantically check the array-theory steps of `proof`.
///
/// Walks every step of `proof`; for each [`ProofStep::TheoryLemma`] whose kind
/// is [`TheoryLemmaKind::ArraySelectStore`] or
/// [`TheoryLemmaKind::ArrayExtensionality`], it discharges the negation of the
/// step's conclusion clause with a fresh `ay` solver in `QF_AX` and records a
/// [`ArrayStepVerdict`]. Non-array steps are not included in the report.
///
/// `terms` must be the [`TermStore`] the proof's [`TermId`]s belong to (the
/// same store the prover used to build the proof).
///
/// [`TheoryLemmaKind`]: ay_core::TheoryLemmaKind
/// [`TheoryLemmaKind::ArraySelectStore`]: ay_core::TheoryLemmaKind::ArraySelectStore
/// [`TheoryLemmaKind::ArrayExtensionality`]: ay_core::TheoryLemmaKind::ArrayExtensionality
#[must_use]
pub fn check_array_proof(proof: &Proof, terms: &TermStore) -> ArrayProofReport {
    let mut steps = Vec::new();
    for (idx, step) in proof.steps.iter().enumerate() {
        let step_id = ProofId(idx as u32);
        if let ProofStep::TheoryLemma { clause, kind, .. } = step {
            use ay_core::TheoryLemmaKind as K;
            let is_array = matches!(kind, K::ArraySelectStore { .. } | K::ArrayExtensionality);
            if !is_array {
                continue;
            }
            let verdict = check_array_clause(terms, clause);
            steps.push(ArrayStepReport {
                step: step_id,
                kind: Some(*kind),
                verdict,
            });
        }
    }
    ArrayProofReport { steps }
}

/// Discharge a single array clause: report `Valid` iff `¬clause` is UNSAT under
/// the array theory.
///
/// The clause is the disjunction of its literals. `¬clause` is the conjunction
/// of the negations of the literals, which we assert into a fresh `QF_AX`
/// solver and require to be UNSAT.
pub fn check_array_clause(terms: &TermStore, clause: &[TermId]) -> ArrayStepVerdict {
    check_array_clause_impl(terms, clause, None)
}

pub(crate) fn check_array_clause_with_controls(
    terms: &TermStore,
    clause: &[TermId],
    controls: &TrustClauseDischargeControls,
) -> ArrayStepVerdict {
    check_array_clause_impl(terms, clause, Some(controls))
}

fn check_array_clause_impl(
    terms: &TermStore,
    clause: &[TermId],
    controls: Option<&TrustClauseDischargeControls>,
) -> ArrayStepVerdict {
    let controlled_deadline = controls.map(TrustClauseDischargeControls::nested_deadline);
    if let (Some(controls), Some(deadline)) = (controls, controlled_deadline) {
        if !controls.live_until(terms, deadline) {
            return resource_unchecked();
        }
    }
    if clause.is_empty() {
        return ArrayStepVerdict::Unchecked {
            reason: "array lemma clause is empty; nothing to discharge".to_string(),
        };
    }

    // A single-element clause may itself be an `(or ...)` term: flatten it so we
    // negate the actual disjunction rather than a structurally-nested literal.
    let literals = flatten_clause(terms, clause);
    if let (Some(controls), Some(deadline)) = (controls, controlled_deadline) {
        if !controls.live_until(terms, deadline) {
            return resource_unchecked();
        }
    }

    let mut solver = Solver::new(Logic::QfAx);
    if let (Some(controls), Some(deadline)) = (controls, controlled_deadline) {
        if !controls.start_native_solver(&mut solver, deadline) {
            return resource_unchecked();
        }
    }
    let mut translator = Translator::new(controls.zip(controlled_deadline));

    // Assert the negation of each literal of the clause. `¬(l1 ∨ ... ∨ ln)` is
    // `¬l1 ∧ ... ∧ ¬ln`.
    for &lit in &literals {
        let translated = match translator.translate(&mut solver, terms, lit) {
            Ok(t) => t,
            Err(reason) => {
                return ArrayStepVerdict::Unchecked {
                    reason: format!("cannot model clause literal: {reason}"),
                };
            }
        };
        // The literal must be Boolean-sorted to negate and assert it.
        if !solver_is_bool(&solver, translated) {
            return ArrayStepVerdict::Unchecked {
                reason: "clause literal is not Bool-sorted; array axiom clauses \
                         must be propositional"
                    .to_string(),
            };
        }
        let negated = solver.not(translated);
        solver.assert_term(negated);
        if let (Some(controls), Some(deadline)) = (controls, controlled_deadline) {
            if !controls.native_solver_live(&solver, deadline) {
                return resource_unchecked();
            }
        }
    }

    let result = if let (Some(controls), Some(deadline)) = (controls, controlled_deadline) {
        let Some(result) = controls.check_native_solver_until(&mut solver, deadline) else {
            return resource_unchecked();
        };
        result
    } else {
        solver.check_sat_internal_query()
    };
    if result.is_unsat() {
        ArrayStepVerdict::Valid
    } else if result.is_sat() {
        ArrayStepVerdict::Invalid {
            reason: "negation of the clause is satisfiable under the array theory: \
                     the clause is not an array-theory tautology (e.g. a \
                     read-over-write conclusion missing its `i != j` guard, or a \
                     wrong index/value)"
                .to_string(),
        }
    } else {
        ArrayStepVerdict::Unchecked {
            reason: "discharge returned Unknown; cannot certify the clause".to_string(),
        }
    }
}

fn resource_unchecked() -> ArrayStepVerdict {
    ArrayStepVerdict::Unchecked {
        reason: "proof-discharge resource envelope expired or was exceeded".to_string(),
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
struct Translator<'a> {
    /// Memo of proof `TermId` -> translated solver `Term`.
    memo: HashMap<TermId, Term>,
    /// Declared uninterpreted function symbols, keyed by `(name, arg_sorts, ret)`.
    funcs: HashMap<(String, Vec<Sort>, Sort), FuncDecl>,
    /// Counter for unique leaf-constant names.
    next_id: u32,
    /// Mandatory-publication envelope, polled at every recursive node.
    controls: Option<(&'a TrustClauseDischargeControls, ay_core::time::Instant)>,
}

impl<'a> Translator<'a> {
    fn new(controls: Option<(&'a TrustClauseDischargeControls, ay_core::time::Instant)>) -> Self {
        Self {
            memo: HashMap::default(),
            funcs: HashMap::default(),
            next_id: 0,
            controls,
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
        if self
            .controls
            .is_some_and(|(controls, deadline)| !controls.native_solver_live(solver, deadline))
        {
            return Err("proof-discharge resource envelope expired or was exceeded".to_string());
        }
        if let Some(t) = self.memo.get(&tid) {
            return Ok(*t);
        }
        let result = self.translate_uncached(solver, terms, tid)?;
        if self
            .controls
            .is_some_and(|(controls, deadline)| !controls.native_solver_live(solver, deadline))
        {
            return Err("proof-discharge resource envelope expired or was exceeded".to_string());
        }
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
            TermData::App(sym, args) => self.translate_app(solver, terms, tid, sym, &args),
            TermData::Let(..) => {
                Err("`let` binding in clause (should be expanded before proof)".to_string())
            }
            TermData::Forall(..) | TermData::Exists(..) => {
                Err("quantifier in clause; QF_AX discharge cannot model it".to_string())
            }
            // `TermData` is `#[non_exhaustive]`: fail closed on any future node.
            other => Err(format!(
                "unsupported term node {other:?} outside the modelled array fragment"
            )),
        }
    }

    fn translate_const(&mut self, solver: &mut Solver, c: &Constant) -> Result<Term, String> {
        match c {
            Constant::Bool(b) => Ok(solver.bool_const(*b)),
            Constant::Int(v) => Ok(solver.int_const_bigint(v)),
            Constant::BitVec { value, width } => Ok(solver.bv_const_bigint(value, *width)),
            Constant::Rational(_) => {
                Err("rational constant outside the QF_AX fragment".to_string())
            }
            Constant::String(_) => Err("string constant outside the QF_AX fragment".to_string()),
            // `Constant` is `#[non_exhaustive]`: fail closed on any future kind.
            other => Err(format!(
                "unsupported constant {other:?} outside the QF_AX fragment"
            )),
        }
    }

    #[allow(clippy::too_many_lines)]
    fn translate_app(
        &mut self,
        solver: &mut Solver,
        terms: &TermStore,
        tid: TermId,
        sym: ay_core::Symbol,
        args: &[TermId],
    ) -> Result<Term, String> {
        let name = sym.name();
        // Translate children first (shared via memo).
        let mut targs: Vec<Term> = Vec::with_capacity(args.len());
        for &a in args {
            targs.push(self.translate(solver, terms, a)?);
        }

        match (name, targs.as_slice()) {
            ("select", [array, index]) => solver
                .try_select(*array, *index)
                .map_err(|e| format!("select translation failed: {e}")),
            ("store", [array, index, value]) => solver
                .try_store(*array, *index, *value)
                .map_err(|e| format!("store translation failed: {e}")),
            ("=", [a, b]) => solver
                .try_eq(*a, *b)
                .map_err(|e| format!("eq translation failed: {e}")),
            ("distinct", _) if targs.len() >= 2 => solver
                .try_distinct(&targs)
                .map_err(|e| format!("distinct translation failed: {e}")),
            ("not", [a]) => Ok(solver.not(*a)),
            ("and", _) if !targs.is_empty() => Ok(fold_binary(&targs, |acc, t| solver.and(acc, t))),
            ("or", _) if !targs.is_empty() => Ok(fold_binary(&targs, |acc, t| solver.or(acc, t))),
            ("=>", [a, b]) => Ok(solver.implies(*a, *b)),
            ("xor", [a, b]) => Ok(solver.xor(*a, *b)),
            ("ite", [c, a, b]) => Ok(solver.ite(*c, *a, *b)),
            // An uninterpreted function application (the EUF part of the
            // fragment, e.g. inside congruence clauses mislabelled as array
            // lemmas). Model it as a declared function so congruence holds.
            _ if is_uninterpreted_app(name) => {
                self.translate_uninterpreted(solver, terms, tid, name, args, &targs)
            }
            _ => Err(format!(
                "operator `{name}`/{} outside the modelled array+EUF+Bool fragment",
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
        // uninterpreted function here. Two reasons, both load-bearing:
        //
        // 1. SOUNDNESS: modelling a builtin as an opaque UF drops its semantics
        //    AND (for the indexed BV ops) its indices, since `Symbol::name()`
        //    strips them — e.g. `(_ int2bv 8) x` and `(_ extract 7 0) x` /
        //    `(_ extract 15 8) x` would all collapse to a single UF keyed only by
        //    `(name, arg_sorts, ret)`, conflating distinct operations. That is a
        //    wrong-Valid hazard (the checker could "prove" a non-tautology). The
        //    QF_AX array checker cannot faithfully model the BV<->LIA bridge ops
        //    (`int2bv`/`bv2nat`) at all, so the only sound answer is to decline.
        //
        // 2. NO-PANIC: `Solver::declare_fun` routes through ay-frontend's
        //    reserved-symbol gate, which rejects every reserved builtin name (see
        //    `elaborate::declare_fun`). The panicking `declare_fun` wrapper would
        //    turn that rejection into an ICE (the `int2bv` verify-time crash).
        //
        // Failing closed here yields `Unchecked`; the whole-problem Executor
        // re-solve remains the sound certificate for such clauses.
        if ay_frontend::is_reserved_symbol(name) {
            return Err(format!(
                "operator `{name}` is a reserved builtin theory operator; it is \
                 outside the modelled array+EUF+Bool fragment and must not be \
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

/// Operators that are *built-in* and handled explicitly above. Anything else is
/// treated as an uninterpreted function symbol (the EUF fragment).
fn is_uninterpreted_app(name: &str) -> bool {
    !matches!(
        name,
        "select"
            | "store"
            | "="
            | "distinct"
            | "not"
            | "and"
            | "or"
            | "=>"
            | "xor"
            | "ite"
            // arithmetic / bit-vector / other-theory operators are NOT
            // uninterpreted; treating them as such would be unsound. List the
            // common ones so they fall through to an explicit fragment error.
            | "+" | "-" | "*" | "/" | "div" | "mod" | "abs"
            | "<" | "<=" | ">" | ">="
            | "bvadd" | "bvsub" | "bvmul" | "bvand" | "bvor" | "bvxor"
            | "bvnot" | "bvneg" | "bvshl" | "bvlshr" | "bvashr"
            | "bvudiv" | "bvurem" | "bvsdiv" | "bvsrem"
            | "bvult" | "bvule" | "bvugt" | "bvuge"
            | "bvslt" | "bvsle" | "bvsgt" | "bvsge"
            | "concat" | "extract"
    )
}

/// Accept only sorts that the `QF_AX` discharge can model soundly. Arithmetic
/// (`Int`) and `BitVec` index/element sorts are fine as *opaque* sorts here
/// because we never assert arithmetic *operators* over them — only equalities
/// and array reads/writes. Quantifier/datatype/string/etc. sorts are rejected.
fn supported_sort(sort: &Sort) -> Result<Sort, String> {
    match sort {
        Sort::Bool | Sort::Int | Sort::BitVec(_) | Sort::Uninterpreted(_) => Ok(sort.clone()),
        Sort::Array(arr) => {
            let idx = supported_sort(&arr.index_sort)?;
            let elem = supported_sort(&arr.element_sort)?;
            Ok(Sort::array(idx, elem))
        }
        other => Err(format!(
            "sort {other:?} is outside the modelled array fragment"
        )),
    }
}

#[cfg(test)]
#[path = "array_proof_check_tests.rs"]
mod tests;
