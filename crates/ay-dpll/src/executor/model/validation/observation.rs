// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Per-term observation logic for model validation.
//!
//! Contains `validate_term_observation` (the per-assertion/assumption evaluator),
//! `apply_assumption_observation`, and `validate_sat_assumptions`.
//!
//! Extracted from `pipeline.rs` for code health (#5970).

use ay_core::{term::TermData, Sort, TermId, VerificationBoundary, VerificationVerdict};

use super::{
    dt_equality_decidable_by_reduction, dt_equality_operands_fully_ground, ValidationObservation,
    ValidationSkipKind, ValidationTarget, TERM_FLAG_ARRAY, TERM_FLAG_BV_CMP, TERM_FLAG_DATATYPE,
    TERM_FLAG_FP, TERM_FLAG_INTERNAL, TERM_FLAG_QUANTIFIER, TERM_FLAG_SEQ, TERM_FLAG_STRING,
};
use crate::executor::model::{EvalValue, Executor, Model, EVAL_STACK_RED_ZONE, EVAL_STACK_SIZE};
use crate::executor_types::{ModelValidationError, SolveResult};

impl Executor {
    fn strip_top_array_observation_not(&self, term: TermId) -> TermId {
        match self.ctx.terms.get(term) {
            TermData::Not(inner) => *inner,
            TermData::App(sym, args) if sym.name() == "not" && args.len() == 1 => args[0],
            _ => term,
        }
    }

    fn is_direct_array_observation_assertion(&self, term: TermId) -> bool {
        fn is_select(terms: &ay_core::TermStore, term: TermId) -> bool {
            matches!(terms.get(term), TermData::App(sym, _) if sym.name() == "select")
        }

        let inner = self.strip_top_array_observation_not(term);
        let TermData::App(sym, args) = self.ctx.terms.get(inner) else {
            return false;
        };
        match sym.name() {
            "=" if args.len() == 2 => args.iter().any(|&arg| is_select(&self.ctx.terms, arg)),
            "distinct" if args.len() >= 2 => {
                args.iter().any(|&arg| is_select(&self.ctx.terms, arg))
            }
            _ => false,
        }
    }

    /// True when the (possibly negated) top-level assertion is a direct
    /// equality/disequality whose operands are all array-theory shaped — i.e.
    /// an array variable, a `store`/`const-array` chain, or a `select`.
    ///
    /// These "array definition/observation" atoms are exactly the assertions a
    /// partial array-model reconstruction can render `Bool(false)` even when the
    /// formula is genuinely SAT (the array solver has already checked ROW/store
    /// consistency internally). Delegating their false evaluation back to the
    /// array theory is therefore acceptable.
    ///
    /// Anything more complex (e.g. a top-level boolean `(or ...)`/`(and ...)`
    /// formula that merely mentions arrays) is NOT covered: a concrete
    /// `Bool(false)` there is a full-formula refutation of the candidate model
    /// and must fail closed rather than be trusted, so a genuinely-UNSAT
    /// formula with a spurious array model cannot escape as SAT.
    fn is_array_definition_or_observation_atom(&self, term: TermId) -> bool {
        fn is_array_shaped(executor: &Executor, t: TermId) -> bool {
            match executor.ctx.terms.get(t) {
                TermData::Var(_, _) => matches!(executor.ctx.terms.sort(t), Sort::Array(_)),
                TermData::App(sym, _) => matches!(sym.name(), "store" | "const-array" | "select"),
                _ => false,
            }
        }

        let inner = self.strip_top_array_observation_not(term);
        let TermData::App(sym, args) = self.ctx.terms.get(inner) else {
            return false;
        };
        match sym.name() {
            "=" if args.len() == 2 => args.iter().all(|&arg| is_array_shaped(self, arg)),
            "distinct" if args.len() >= 2 => args.iter().all(|&arg| is_array_shaped(self, arg)),
            _ => false,
        }
    }

    fn direct_array_observation_has_concrete_value(&self, term: TermId) -> bool {
        let inner = self.strip_top_array_observation_not(term);
        let TermData::App(sym, args) = self.ctx.terms.get(inner) else {
            return false;
        };
        matches!(sym.name(), "=" | "distinct")
            && args
                .iter()
                .any(|&arg| matches!(self.ctx.terms.get(arg), TermData::Const(_)))
    }

    pub(in crate::executor::model) fn validate_term_observation(
        &self,
        model: &Model,
        term: TermId,
        index: usize,
        flags: u8,
        has_array_assertions: bool,
        target: ValidationTarget,
    ) -> ValidationObservation {
        if flags & TERM_FLAG_INTERNAL != 0 {
            return ValidationObservation::Skip(ValidationSkipKind::Internal);
        }
        if flags & TERM_FLAG_QUANTIFIER != 0 {
            // A SAT assignment to the quantifier's Boolean proxy proves only
            // that the finite set of emitted ground instances is consistent.
            // It does not validate the universal over its full domain. Record a
            // quantifier skip so the restoration and final emission gates demand
            // an exhaustive or explicitly constructed model certificate.
            return ValidationObservation::Skip(ValidationSkipKind::Quantifier);
        }

        // SOUNDNESS (#as-array-ext): an equality with a function-backed array
        // operand — `(_ as-array f)`, `lambda-array`, `map` — must never be
        // SAT-fallback'd. The eager `select(as-array f, i) -> f(i)` rewrite
        // leaves no `select` node for the array theory to connect the backing
        // functions, so the SAT solver's free truth value for the equality
        // literal is not evidence (circular self-validation). This guard runs
        // BEFORE the flag-based dispatch so it fires even when there is no
        // array model (e.g. `(= (_ as-array f) (lambda ((i Int)) 7))` with `f`
        // the only declared symbol): decide via the evaluator
        // (`function_backed_array_equality` probes for a disagreeing index) and
        // fail closed to `incomplete` (degrade SAT -> Unknown) when undecided.
        if self.equality_has_function_backed_array_operand(term) {
            let term_str = self.format_term(term);
            return match self.evaluate_term(model, term) {
                EvalValue::Bool(false) => ValidationObservation::violated(
                    target,
                    format!(
                        "{}: {term_str} function-backed array equality evaluates to false \
                         (#as-array-ext)",
                        target.violated_entry(index),
                    ),
                ),
                EvalValue::Bool(true) => ValidationObservation::independent(target, true),
                _ => ValidationObservation::incomplete(
                    target,
                    format!(
                        "{}: {term_str} function-backed array equality could not be \
                         independently validated (#as-array-ext)",
                        target.entry(index),
                    ),
                ),
            };
        }

        let has_datatype = flags & TERM_FLAG_DATATYPE != 0;
        // Witness-extensionality bypass fast-path (#dt-array-extensionality-witness;
        // companion of the soft-skip in `validate_model_attempt`). When the search
        // has soundly modeled the datatype-carrying-array fragment — the bypass
        // flag is set at ENTRY by `dt_array_extensionality_modeled` (every
        // datatype-carrying array is a datatype-ELEMENT array with a datatype-free
        // index) or the observational-completeness footprint — a datatype
        // (dis)equality is ALREADY enforced by the emitted extensionality / ROW /
        // selector-tester congruence axioms baked into the solved formula, so
        // INDEPENDENT re-validation is unnecessary. It is also the validation
        // perf sink: the datatype-value fold/eval below is O(terms), so on the
        // 92MB parser BMC instance (156 array eqs + 67 value eqs) it runs for
        // minutes AFTER model extraction and times the solve out. Short-circuit
        // ground datatype assertions to a soft datatype skip here, before that
        // work. SOUND: gated on the bypass predicate, whose whole-footprint
        // coverage is verified adversarially — the audit crafts UNSAT
        // datatype-array instances, so any residual modeling gap surfaces as a
        // false SAT there, not as a silently-skipped violation here.
        //
        // GATE-VACUITY GUARD (#qf-dt-gate-vacuity): the bypass predicate is
        // VACUOUSLY true on an array-free problem (empty datatype-array
        // footprint), and the witness-extensionality argument above only
        // vouches for assertions that touch the datatype-carrying-ARRAY
        // fragment. Without the `TERM_FLAG_ARRAY` requirement this fast-path
        // skipped EVERY ground datatype assertion on pure QF_DT problems,
        // making the QF_DT SAT model-validation gate vacuous (checked == 0).
        // Pure datatype assertions are enforced by the DT solver, not the
        // emitted array axioms, so they must be independently evaluated below.
        if has_datatype
            && flags & TERM_FLAG_ARRAY != 0
            && self.dt_array_injectivity_gate_bypass
            && matches!(target, ValidationTarget::GroundAssertion)
        {
            return ValidationObservation::Skip(ValidationSkipKind::Datatype);
        }
        // A datatype `=`/`distinct` atom whose operands collapse to the SAME term
        // under pure selector reduction is reflexively (un)satisfied and decidable
        // even when `resolve_ground` cannot confirm it (e.g. a field is an `Array`
        // or a `bv`-indexed selector chain with no canonical ground string). These
        // arise when a datatype const is substituted by its `Ctor(..)` binding
        // after elaboration: `(= X (fld_params (Parser_mk .. X ..)))` or
        // `(= V (fld_vec (VecIterMut_mk V pos)))`. Decide them directly, ahead of
        // BOTH datatype fail-close paths below, so a trivially-true equality is not
        // degraded to `unknown`. (#selector-over-ctor-ground)
        if has_datatype && matches!(target, ValidationTarget::GroundAssertion) {
            if let Some(satisfied) = dt_equality_decidable_by_reduction(self, term) {
                let term_str = self.format_term(term);
                return if satisfied {
                    ValidationObservation::independent(target, true)
                } else {
                    ValidationObservation::violated(
                        target,
                        format!(
                            "{}: {term_str} datatype (dis)equality violated under \
                             selector reduction",
                            target.violated_entry(index),
                        ),
                    )
                };
            }
        }
        // (#dt-bv-congruence, COMPOUND extension / #dt-embedded-cycle false-SAT)
        // A COMPOUND Boolean assertion (or/and/not/ite/=>/xor) that CONTAINS a
        // datatype-reconstruction (dis)equality with non-fully-ground operands
        // is no better evidence than the bare atom the per-block
        // #dt-bv-congruence guards below fail-close: whichever disjunct/branch
        // the SAT solver picked IS such an equality, its truth is read off EUF
        // equivalence-class identity, and neither the eager DT+BV bit-blast nor
        // the SAT core connects that literal to constructor congruence or
        // ACYCLICITY. Both the evaluator's Bool(true) and SAT-fallback here
        // rubber-stamped a CYCLIC model for
        //   `(or (= x (cons a y)) (= x (cons b y)))` ∧
        //   `(or (= y (cons a x)) (= y (cons b x)))`
        // — a FALSE SAT. Fail closed to incomplete (degrade SAT -> Unknown)
        // instead.
        //
        // Deliberately NOT affected (surgical):
        //   - BARE (dis)equalities — the term itself, possibly under one `not` —
        //     keep the existing per-block discipline (decidable-by-reduction,
        //     opaque-eq/diseq exceptions, ground-oracle authority);
        //   - compound assertions whose embedded dt equalities are all FULLY
        //     GROUND under the model (the DtOracle already had authority; they
        //     evaluate semantically below);
        //   - MODEL-INDEPENDENT datatype tautologies (the generated
        //     exhaustiveness/selector axioms such as
        //     `(or (= x (cons (hd x) (tl x))) (not (is-cons x)))`): true in
        //     EVERY model, so accepting them can never validate a wrong model
        //     of the user formula (#g4-dt-taut) — without this exemption every
        //     recursive-datatype SAT would spuriously degrade to Unknown.
        //   - SOLVER-GENERATED DT axioms (`dt_solver_added_axiom_terms`), like
        //     the model-independent tautologies: each is an entailed
        //     datatype-theory consequence (true in every model of the user
        //     formula), so accepting one can never validate a wrong model of
        //     the USER formula — while fail-closing on one (a deep
        //     `(or (= v (succ (pred v))) (not (is-succ v)))` (C)-axiom whose
        //     selector leaf is legitimately free) spuriously degrades genuine
        //     deep-recursion SATs to Unknown.
        if has_datatype
            && matches!(target, ValidationTarget::GroundAssertion)
            && !self.dt_reconstruction_equality(term)
            && !self.dt_solver_added_axiom_terms.contains(&term)
            && self.compound_contains_nonground_dt_reconstruction_equality(model, term)
            && !self.term_is_datatype_tautology(term)
        {
            // Before failing closed, try to confirm the assertion with the
            // MASKED three-valued evaluation: every non-ground
            // dt-reconstruction (dis)equality is treated as Unknown, and only
            // TRUSTED atoms may decide the compound — ground-decidable atoms,
            // plus claimed-TRUE positive constructor equalities certified by
            // the model-wide STRUCTURAL CONSISTENCY check (an occurs/clash
            // check over every constructor (dis)equality the model commits
            // true; a cyclic commitment like `x=cons(a,y) ∧ y=cons(a,x)` fails
            // it and stays masked). `Some(true)` means the assertion is
            // satisfied by trusted atoms alone, so the unsound EUF-identity
            // evidence is not load-bearing — accept. `Some(false)` means
            // trusted atoms already falsify it — fall through to the existing
            // Bool(false) discipline (violated / model-gap arms). `None` means
            // the verdict NECESSARILY rests on an uncertifiable dt equality's
            // free EUF truth value — fail closed.
            let structure_ok = self.dt_committed_ctor_equalities_consistent(model);
            match self.dt_masked_compound_eval(model, term, structure_ok) {
                Some(true) => return ValidationObservation::independent(target, true),
                Some(false) => {}
                None => {
                    let term_str = self.format_term(term);
                    return ValidationObservation::incomplete(
                        target,
                        format!(
                            "{}: {term_str} compound Boolean depends on a \
                             datatype-reconstruction (dis)equality that cannot \
                             be independently confirmed under the DT+BV \
                             bit-blast (selector/constructor congruence and \
                             acyclicity not encoded); fail-closed",
                            target.entry(index),
                        ),
                    );
                }
            }
        }
        if has_datatype && flags & TERM_FLAG_BV_CMP == 0 {
            // (#dt-bv-congruence) A datatype-sort (dis)equality over a datatype
            // with cross-theory (BV/Int/Real) fields: the model evaluator reads
            // its truth off EUF equivalence-class identity, but neither the eager
            // DT+BV bit-blast nor the bv2nat→LIA bridge enforces datatype
            // constructor congruence (single-constructor injectivity, constructor
            // distinctness). x and y can land in distinct EUF classes even though
            // the field theory constraints force their fields equal (e.g.
            // `bv2nat(v x) = bv2nat(v y)` forces `v x = v y`, hence `x = y`). The
            // global strict gate (DtOracle) already had the authoritative chance
            // to flag a violation; if it could resolve BOTH operands to ground it
            // did, so here we trust the evaluator. Otherwise the evaluator's Bool
            // verdict is unsound for this atom — fail closed (degrade SAT to
            // Unknown) rather than accept it as independent evidence. Genuine SAT
            // (e.g. `(not (= s t))` with `s=(mk-val #x01)`, `t=(mk-val #x02)`,
            // fields pinned) resolves to ground and is kept.
            if matches!(target, ValidationTarget::GroundAssertion)
                && self.datatype_sort_equality(term)
                && !dt_equality_operands_fully_ground(self, model, term)
            {
                // A positive equality between opaque datatype operands (never
                // observed by a selector/tester/constructor) is asserted-true and
                // provably satisfiable — accept it instead of fail-closing the
                // whole SAT to Unknown (#dt-opaque-eq). Disequalities and
                // selector/tester-observed operands still fail closed below.
                if self.dt_positive_eq_opaque_satisfiable(term) {
                    return ValidationObservation::independent(target, true);
                }
                // DUAL (#dt-opaque-diseq): a disequality between two opaque
                // datatype operands of a non-degenerate datatype, which the model
                // commits true (distinct EUF classes), is provably satisfiable —
                // accept it instead of fail-closing the SAT to Unknown. This is the
                // SAT-direction datatype model-distinguishability the deductive-checks
                // `eval_objective_exact` saturating control needs (two distinct
                // `Result<i128,_>`-valued UF applications take distinct values).
                if self.dt_diseq_opaque_satisfiable(term)
                    && matches!(self.evaluate_term(model, term), EvalValue::Bool(true))
                {
                    return ValidationObservation::independent(target, true);
                }
                let term_str = self.format_term(term);
                return ValidationObservation::incomplete(
                    target,
                    format!(
                        "{}: {term_str} datatype-sort (dis)equality cannot be \
                         independently confirmed under the DT+BV bit-blast \
                         (datatype congruence not encoded); fail-closed",
                        target.entry(index),
                    ),
                );
            }
            let term_str = self.format_term(term);
            return match self.evaluate_term(model, term) {
                EvalValue::Bool(true) => ValidationObservation::independent(target, true),
                EvalValue::Bool(false)
                    if matches!(target, ValidationTarget::GroundAssertion)
                        && self.dt_user_bool_uf_false_may_be_model_gap(model, term)
                        && self.sat_literal_assigned_true(model, term) =>
                {
                    ValidationObservation::fallback(format!(
                        "{}: {term_str} DT user UF evaluation false but SAT-assigned true (#9007)",
                        target.entry(index),
                    ))
                }
                EvalValue::Bool(false)
                    if matches!(target, ValidationTarget::GroundAssertion)
                        && self.datatype_seq_equality_false_may_be_model_gap(term)
                        && self.sat_literal_assigned_true(model, term) =>
                {
                    ValidationObservation::fallback(format!(
                        "{}: {term_str} DT+Seq UF equality evaluation false but SAT-assigned true (#9227)",
                        target.entry(index),
                    ))
                }
                EvalValue::Bool(false)
                    if matches!(target, ValidationTarget::GroundAssertion)
                        && flags & TERM_FLAG_SEQ != 0
                        && (model.euf_model.is_some() || model.seq_model.is_some()) =>
                {
                    // Mixed datatype/Seq assertions frequently contain UF-backed
                    // projections from datatype receivers to Seq values. The
                    // extracted datatype/Seq model is partial at that boundary, so
                    // a false evaluator result is not authoritative once EUF/Seq
                    // theory solving has accepted the SAT assignment (#9227).
                    ValidationObservation::delegated()
                }
                EvalValue::Bool(false)
                    if matches!(target, ValidationTarget::GroundAssertion)
                        && self.term_is_datatype_tautology(term) =>
                {
                    // A MODEL-INDEPENDENT datatype tautology (e.g. McCarthy
                    // read-over-equality congruence `(or (not (= a b)) (= (sel
                    // (select a i)) (sel (select b i))))`) is true in EVERY model.
                    // A `false` evaluation here means the theory-model
                    // reconstruction is internally inconsistent (a ROW2 /
                    // congruence gap), NOT a genuine refutation — the independent
                    // fail-closed gate proves the tautology and confirms a
                    // consistent model exists. Delegated, not violated, so a
                    // datatype tautology can never spuriously degrade a SAT.
                    // Model-independent => can never mask a real false. (#g4-dt-taut)
                    ValidationObservation::delegated()
                }
                EvalValue::Bool(false) => ValidationObservation::violated(
                    target,
                    format!(
                        "{}: {term_str} evaluates to false (datatype)",
                        target.violated_entry(index),
                    ),
                ),
                _ if matches!(target, ValidationTarget::GroundAssertion)
                    && flags & TERM_FLAG_SEQ != 0
                    && (model.euf_model.is_some() || model.seq_model.is_some()) =>
                {
                    // Same mixed DT+Seq extraction boundary as above, but the
                    // evaluator could not reduce the assertion to a Boolean.
                    // Count the EUF/Seq solver result as delegated evidence
                    // rather than poisoning mixed Seq+datatype validation with
                    // an incomplete datatype skip (#9227).
                    ValidationObservation::delegated()
                }
                _ if matches!(target, ValidationTarget::GroundAssertion) => {
                    ValidationObservation::Skip(ValidationSkipKind::Datatype)
                }
                _ => ValidationObservation::incomplete(
                    target,
                    format!(
                        "{}: {term_str} datatype assumption evaluates to Unknown",
                        target.entry(index),
                    ),
                ),
            };
        }

        if has_datatype {
            let term_str = self.format_term(term);
            return match self.evaluate_term(model, term) {
                EvalValue::Bool(true) => ValidationObservation::independent(target, true),
                // (#dt-bv-congruence) A (dis)equality whose operands are selector
                // chains over a datatype (e.g. `(not (= (counter s) (ok_val (tag
                // s))))`) is a datatype-reconstruction atom: its truth is fixed by
                // projecting the datatype value through its constructor. The eager
                // DT+BV bit-blast does not connect the selector results to the
                // datatype constructor, so neither SAT-fallback (the SAT literal's
                // free truth value) NOR a `skip` is sound evidence — the extracted
                // model can leave the selector results unconstrained while the
                // datatype value forces them equal. When the [`DtOracle`] could
                // resolve both operands to ground it already ran (global strict
                // gate) and would have demoted on a real violation; if it could
                // not, we must fail closed here rather than rubber-stamp via
                // SAT-fallback/skip. This does NOT fire for genuine UF
                // (dis)equalities like `(distinct (f x b) (f y b))` (f a declared
                // function, not a selector), which remain free.
                _ if matches!(target, ValidationTarget::GroundAssertion)
                    && self.dt_reconstruction_equality(term)
                    && !dt_equality_operands_fully_ground(self, model, term) =>
                {
                    ValidationObservation::incomplete(
                        target,
                        format!(
                            "{}: {term_str} datatype-reconstruction (dis)equality \
                             cannot be independently confirmed under the DT+BV \
                             bit-blast (selector/constructor congruence not \
                             encoded); fail-closed",
                            target.entry(index),
                        ),
                    )
                }
                _ if matches!(target, ValidationTarget::GroundAssertion) => {
                    if self.sat_term_assigned_true(model, term) {
                        ValidationObservation::fallback(format!(
                            "{}: {term_str} used SAT-fallback for DT+BV validation",
                            target.entry(index),
                        ))
                    } else {
                        ValidationObservation::Skip(ValidationSkipKind::Dtbv)
                    }
                }
                _ => ValidationObservation::incomplete(
                    target,
                    format!(
                        "{}: {term_str} datatype assumption evaluates to Unknown",
                        target.entry(index),
                    ),
                ),
            };
        }

        if matches!(target, ValidationTarget::GroundAssertion) && flags & TERM_FLAG_SEQ != 0 {
            let term_str = self.format_term(term);
            match self.evaluate_term(model, term) {
                EvalValue::Bool(true) => {
                    return ValidationObservation::independent(target, false);
                }
                EvalValue::Bool(false) => {
                    // Seq model extraction is incomplete: unconstrained Seq
                    // variables get no model value, so operations on them
                    // may evaluate incorrectly. If SAT assigned true, treat
                    // as a model extraction gap (#8456).
                    if self.sat_term_assigned_true(model, term) {
                        return ValidationObservation::fallback(format!(
                            "{}: {term_str} seq evaluation false but SAT-assigned true",
                            target.entry(index),
                        ));
                    }
                    return ValidationObservation::violated(
                        target,
                        format!(
                            "{}: {term_str} evaluates to false (seq theory)",
                            target.violated_entry(index),
                        ),
                    );
                }
                _ if self.sat_term_assigned_true(model, term) => {
                    return ValidationObservation::delegated();
                }
                _ => {
                    // Seq model extraction only populates values for
                    // concretizable terms (seq.unit/empty/concat).
                    // Unconstrained variables get no model value, causing
                    // evaluation to return Unknown. When the theory solver
                    // (EUF+Seq or EUF+Seq+LIA) found SAT, accept the
                    // result as delegated verification (#8456).
                    if model.euf_model.is_some() || model.seq_model.is_some() {
                        return ValidationObservation::delegated();
                    }
                }
            }
        }

        if matches!(target, ValidationTarget::GroundAssertion)
            && flags & TERM_FLAG_STRING != 0
            && model.string_model.is_some()
        {
            let term_str = self.format_term(term);
            match self.evaluate_term(model, term) {
                EvalValue::Bool(true) => {
                    return ValidationObservation::independent(target, false);
                }
                EvalValue::Bool(false) => {
                    // Definitive-ground check (#8779): for ground string predicates
                    // whose arguments fully resolve to concrete strings in the model,
                    // evaluation is authoritative and any mismatch with SAT is a genuine
                    // soundness violation, not a model-extraction gap.
                    if self.string_eval_is_definitive_false(model, term) {
                        return ValidationObservation::violated(
                            target,
                            format!(
                                "{}: {term_str} ground string predicate evaluates to false (definitive, #8779)",
                                target.violated_entry(index),
                            ),
                        );
                    }
                    if self.string_functional_equality_model_gap(model, term) {
                        return ValidationObservation::incomplete(
                            target,
                            format!(
                                "{}: {term_str} string functional equality could not be validated from extracted model",
                                target.entry(index),
                            ),
                        );
                    }
                    // String model extraction is incomplete: the CEGAR loop
                    // may not propagate all variable assignments into the
                    // string model (e.g., pivot enum variables, cross-theory
                    // equalities). If the SAT solver's truth assignment says
                    // the assertion is true, treat this as a model extraction
                    // gap rather than a soundness violation (#7460).
                    if self.sat_term_assigned_true(model, term) {
                        return ValidationObservation::fallback(format!(
                            "{}: {term_str} string evaluation false but SAT-assigned true",
                            target.entry(index),
                        ));
                    }
                    return ValidationObservation::violated(
                        target,
                        format!(
                            "{}: {term_str} evaluates to false (string theory)",
                            target.violated_entry(index),
                        ),
                    );
                }
                _ if self.string_predicate_is_structurally_ground(model, term) => {
                    return ValidationObservation::incomplete(
                        target,
                        format!(
                            "{}: {term_str} ground string predicate could not be evaluated from extracted model (#8779)",
                            target.entry(index),
                        ),
                    );
                }
                _ if self.string_functional_equality_model_gap(model, term) => {
                    return ValidationObservation::incomplete(
                        target,
                        format!(
                            "{}: {term_str} string functional equality could not be evaluated from extracted model",
                            target.entry(index),
                        ),
                    );
                }
                _ if self.sat_term_assigned_true(model, term) => {
                    return ValidationObservation::delegated();
                }
                _ => {}
            }
        }

        // FP assertions (#8456): evaluate and accept or fall back to SAT.
        if matches!(target, ValidationTarget::GroundAssertion) && flags & TERM_FLAG_FP != 0 {
            let term_str = self.format_term(term);
            match self.evaluate_term(model, term) {
                EvalValue::Bool(true) => {
                    return ValidationObservation::independent(target, false);
                }
                EvalValue::Bool(false) => {
                    // FP model extraction may be incomplete (non-RNE rounding modes,
                    // wide formats). If SAT solver assigned this true, treat as gap.
                    if self.sat_term_assigned_true(model, term) {
                        return ValidationObservation::fallback(format!(
                            "{}: {term_str} FP evaluation false but SAT-assigned true",
                            target.entry(index),
                        ));
                    }
                    return ValidationObservation::violated(
                        target,
                        format!(
                            "{}: {term_str} evaluates to false (FP theory)",
                            target.violated_entry(index),
                        ),
                    );
                }
                _ => {
                    // The evaluator could not confirm this FP ground assertion
                    // is satisfied (it returned Unknown).
                    //
                    // Soundness backstop (false-SAT fix): for a PURE-FP atom we
                    // must NOT delegate/accept an Unknown — that is exactly how
                    // a symbolic-variable QF_FP conflict (e.g. `x = 1.0 AND
                    // x = 2.0`) escaped as a false-SAT: the FP variable was
                    // never constrained, the model carried only an abstract
                    // placeholder (`@Float32!0`), evaluate_var returned Unknown,
                    // and the old code rubber-stamped it via `delegated()`.
                    // We fail CLOSED to Incomplete instead, so SAT degrades to
                    // Unknown — never reporting sat for an FP atom we did not
                    // actually satisfy. (Mirrors the QF_LRA/QF_ALIA validation
                    // rule that rejects models with <unknown>/unsatisfied atoms.)
                    //
                    // Exception — genuine mixed FP+Real delegation (#8456): when
                    // an LRA model is present (QF_FPLRA etc.), `fp.to_real` over
                    // NaN/Inf or wide formats may be unreconstructable by the
                    // FP-bit evaluator even though the LRA solver genuinely
                    // satisfied the atom (it assigned the `fp.to_real(..)` UF
                    // term a concrete real). That delegation is real evidence,
                    // not a free literal, so we keep it. The pure-FP false-SAT
                    // signature has no LRA model, so this exception cannot
                    // re-open it.
                    //
                    // QF_BVFP and concrete FP atoms are unaffected either way:
                    // their atoms evaluate to Bool(true) and take the arm above,
                    // never reaching here.
                    if model.lra_model.is_some() {
                        return ValidationObservation::delegated();
                    }
                    return ValidationObservation::incomplete(
                        target,
                        format!(
                            "{}: {term_str} FP atom could not be confirmed satisfied from extracted model (evaluates to <unknown>)",
                            target.entry(index),
                        ),
                    );
                }
            }
        }

        if matches!(target, ValidationTarget::Assumption)
            && matches!(self.ctx.terms.sort(term), Sort::Bool)
            && flags & TERM_FLAG_ARRAY == 0
            && self.sat_assumption_assigned_true(model, term)
        {
            return ValidationObservation::delegated();
        }

        // Defer format_term to avoid exponential DAG-to-tree blowup on success paths.
        // format_term has no memoization, so on deeply nested BV terms it can take
        // seconds even though the string is only needed for error messages.
        let term_str = || self.format_term(term);
        match self.evaluate_term(model, term) {
            EvalValue::Bool(true) => ValidationObservation::independent(target, false),
            EvalValue::Bool(false) => {
                if flags & TERM_FLAG_ARRAY != 0 {
                    let bv_backed = model.bv_model.is_some();
                    if bv_backed {
                        let is_direct_observation =
                            self.is_direct_array_observation_assertion(term);
                        let bv_solver_covered_assertion =
                            self.model_validation_delegated_assertions.contains(&term);
                        if !is_direct_observation && bv_solver_covered_assertion {
                            return ValidationObservation::delegated();
                        }
                        return ValidationObservation::incomplete(
                            target,
                            format!(
                                "{}: {} BV-backed array assertion evaluates to false; \
                                 fail-closed pending independent array model validation",
                                target.entry(index),
                                term_str(),
                            ),
                        );
                    }
                    // Array-theory-backed AUFLIA/QF_AX models can evaluate
                    // explicit store-chain definition assertions to false when
                    // the extracted array model is partial, even though the
                    // array solver has already checked ROW/store consistency.
                    // Mirror the Unknown path below and count this as delegated
                    // theory evidence instead of circular SAT-fallback (#8785).
                    //
                    // SOUNDNESS: only delegate (or SAT-fallback) for array
                    // definition/observation ATOMS — `(= array-shaped
                    // array-shaped)` and friends — the class whose false
                    // evaluation is plausibly a partial-extraction artifact of a
                    // genuinely-SAT model. A concrete `Bool(false)` on a richer
                    // boolean formula that merely mentions arrays is a
                    // full-formula refutation of the candidate model; delegating
                    // it back to the array theory would let a spurious model
                    // (e.g. store-congruence over arithmetic indices, where z3
                    // says UNSAT) escape as SAT. Such formulas fall through to
                    // the fail-closed `incomplete` below (SAT -> Unknown).
                    let array_eval_artifact_candidate =
                        self.is_array_definition_or_observation_atom(term);
                    if array_eval_artifact_candidate
                        && model.array_model.is_some()
                        && !self.direct_array_observation_has_concrete_value(term)
                        // SOUNDNESS (#as-array-ext): see Unknown-path note below.
                        && !self.equality_has_function_backed_array_operand(term)
                    {
                        return ValidationObservation::delegated();
                    }
                    // Non-BV path: accept SAT-fallback for array assertions
                    // where the model evaluator may be incomplete.
                    if array_eval_artifact_candidate
                        && matches!(target, ValidationTarget::GroundAssertion)
                        && self.sat_term_assigned_true(model, term)
                    {
                        return ValidationObservation::fallback(format!(
                            "{}: {} used SAT-fallback for array validation (eval=false)",
                            target.entry(index),
                            term_str(),
                        ));
                    }
                    return ValidationObservation::incomplete(
                        target,
                        format!(
                            "{}: {} array {} evaluates to false",
                            target.entry(index),
                            term_str(),
                            target.kind_name(),
                        ),
                    );
                }
                // NO BV delegation on a concrete refutation (#bv-ite-bool-model).
                // Two overrides used to sit here (the #8528/#8597 BV-coverage
                // delegations for ite-containing / BV_CMP-flagged assertions):
                // when the independent evaluator had CONCRETELY refuted the
                // emitted model (Bool(false)), they rubber-stamped the result as
                // Verified{DelegatedSolver} because the SAT solver satisfied the
                // corresponding bit-blast literal. That premise certifies the SAT
                // solver's internal assignment — NOT the emitted model, which is
                // reconstructed separately and can diverge (e.g. a Bool ite
                // condition dropped during extraction). Those overrides masked
                // genuinely invalid models as sat. A concrete Bool(false) from
                // the evaluator is final for the candidate model; delegation
                // remains available only in the EvalValue::Unknown arm below
                // (genuine evaluator incompleteness, no concrete refutation).
                if matches!(target, ValidationTarget::GroundAssertion)
                    && self.arithmetic_false_may_be_model_extraction_gap(model, term)
                    && self.sat_term_assigned_true(model, term)
                {
                    return ValidationObservation::fallback(format!(
                        "{}: {} arithmetic evaluation false but SAT-assigned true",
                        target.entry(index),
                        term_str(),
                    ));
                }
                if matches!(target, ValidationTarget::GroundAssertion)
                    && self.uf_arithmetic_false_may_be_model_extraction_gap(model, term)
                {
                    return ValidationObservation::delegated();
                }
                // #8373: ITE-containing assertions with arithmetic content may
                // evaluate to false due to model extraction gaps. The LRA simplex
                // model assigns values to individual variables without knowledge of
                // ITE-level branch constraints. The model evaluator may pick a
                // branch whose equality is not satisfied — even though the SAT +
                // theory assignment IS consistent. Use SAT-fallback when the SAT
                // solver assigned the assertion true and an arithmetic model exists.
                //
                // This is narrower than the reverted `contains_arithmetic_subterm`
                // approach: it only triggers when the assertion actually contains
                // an ITE node (structural branch-dependency), not for every assertion
                // that merely mentions arithmetic variables.
                if matches!(target, ValidationTarget::GroundAssertion)
                    && self.ite_false_may_be_model_extraction_gap(model, term)
                    && self.sat_term_assigned_true(model, term)
                {
                    return ValidationObservation::fallback(format!(
                        "{}: {} ITE evaluation false but SAT-assigned true (#8373)",
                        target.entry(index),
                        term_str(),
                    ));
                }
                if std::env::var_os("AY_F1_DIAG").is_some() {
                    if let TermData::App(sym, args) = self.ctx.terms.get(term) {
                        if sym.name() == "=" {
                            for &arg in args {
                                eprintln!(
                                    "AY_F1_DIAG: violated-eq side {:?} ({}) -> {:?}",
                                    arg,
                                    self.format_term(arg),
                                    self.evaluate_term(model, arg)
                                );
                            }
                        }
                    }
                }
                ValidationObservation::violated(
                    target,
                    format!(
                        "{}: {} evaluates to false",
                        target.violated_entry(index),
                        term_str(),
                    ),
                )
            }
            EvalValue::Unknown => {
                if matches!(target, ValidationTarget::GroundAssertion) {
                    if self.is_pure_boolean_formula(term)
                        && self.sat_term_assigned_true(model, term)
                    {
                        return ValidationObservation::delegated();
                    }
                    if flags & TERM_FLAG_ARRAY != 0 {
                        let bv_backed = model.bv_model.is_some();
                        if bv_backed {
                            let is_direct_observation =
                                self.is_direct_array_observation_assertion(term);
                            let bv_solver_covered_assertion =
                                self.model_validation_delegated_assertions.contains(&term);
                            if !is_direct_observation && bv_solver_covered_assertion {
                                return ValidationObservation::delegated();
                            }
                            return ValidationObservation::incomplete(
                                target,
                                format!(
                                    "{}: {} BV-backed array assertion evaluates to Unknown; \
                                     fail-closed pending independent array model validation",
                                    target.entry(index),
                                    term_str(),
                                ),
                            );
                        }
                        // Array-theory-backed (QF_AX, QF_AUFLIA):
                        // TheoryCombiner::array_euf runs ArraySolver +
                        // EufSolver which verify functional consistency
                        // (ROW1, ROW2, extensionality) at the theory level.
                        // The model evaluator may return Unknown for
                        // select/store chains when no arithmetic model is
                        // available (QF_AX with Int-indexed arrays creates
                        // no LIA solver). Accept via delegated verification
                        // since the theory solver already validated (#6820).
                        let array_theory_backed = model.array_model.is_some();
                        if array_theory_backed
                            && !self.direct_array_observation_has_concrete_value(term)
                            // SOUNDNESS (#as-array-ext): never delegate an equality
                            // with a function-backed array operand. The array solver
                            // does not connect the backing functions (the eager
                            // select-as-array rewrite leaves no select term for
                            // check_array_equality), so its silence is not evidence.
                            && !self.equality_has_function_backed_array_operand(term)
                        {
                            return ValidationObservation::delegated();
                        }
                        // SOUNDNESS (#as-array-ext): a function-backed array
                        // equality that the evaluator could not decide must NOT
                        // be SAT-fallback'd — that would launder the SAT solver's
                        // free truth value for the equality literal into evidence
                        // (circular self-validation). Fail closed to incomplete so
                        // the pipeline degrades SAT to Unknown.
                        if self.equality_has_function_backed_array_operand(term) {
                            return ValidationObservation::incomplete(
                                target,
                                format!(
                                    "{}: {} function-backed array equality could not be \
                                     independently validated (#as-array-ext)",
                                    target.entry(index),
                                    term_str(),
                                ),
                            );
                        }
                        // Non-BV, non-array-theory path: accept SAT-fallback
                        // for array assertions where the model evaluator may
                        // be incomplete.
                        if self.sat_term_assigned_true(model, term) {
                            return ValidationObservation::fallback(format!(
                                "{}: {} used SAT-fallback for array validation",
                                target.entry(index),
                                term_str(),
                            ));
                        }
                        return ValidationObservation::incomplete(
                            target,
                            format!(
                                "{}: {} array assertion evaluates to Unknown",
                                target.entry(index),
                                term_str(),
                            ),
                        );
                    }
                    // BV Unknown delegation (#8528, #8597): Unknown means the
                    // evaluator couldn't resolve the term. Delegate only when
                    // the current theory path recorded this restored assertion
                    // as covered by a preprocessed/encoded assertion.
                    if flags & TERM_FLAG_BV_CMP != 0
                        && model.bv_model.is_some()
                        && self.model_validation_delegated_assertions.contains(&term)
                    {
                        return ValidationObservation::delegated();
                    }
                    if model.bv_model.is_some()
                        && model.euf_model.is_none()
                        && self.uninterpreted_equality_assertion(term)
                    {
                        return ValidationObservation::delegated();
                    }
                    if self.is_arithmetic_boolean_assertion(term)
                        && self.sat_term_assigned_true(model, term)
                    {
                        return ValidationObservation::fallback(format!(
                            "{}: {} used SAT-fallback for arithmetic validation",
                            target.entry(index),
                            term_str(),
                        ));
                    }
                    if self.is_arithmetic_boolean_assertion(term) && has_array_assertions {
                        return ValidationObservation::Skip(ValidationSkipKind::ArithArrayMix);
                    }
                    if flags & TERM_FLAG_BV_CMP != 0 && model.bv_model.is_none() {
                        return ValidationObservation::incomplete(
                            target,
                            format!(
                                "{}: {} contains BV comparison without BV model (AUFLIA routing)",
                                target.entry(index),
                                term_str(),
                            ),
                        );
                    }
                    if flags & TERM_FLAG_BV_CMP != 0 {
                        let is_pure_bv = flags
                            & (TERM_FLAG_ARRAY
                                | TERM_FLAG_SEQ
                                | TERM_FLAG_DATATYPE
                                | TERM_FLAG_QUANTIFIER)
                            == 0;
                        if is_pure_bv {
                            return ValidationObservation::incomplete(
                                target,
                                format!(
                                    "{}: {} pure BV assertion evaluates to Unknown with BV model present",
                                    target.entry(index),
                                    term_str(),
                                ),
                            );
                        }
                        if self.sat_term_assigned_true(model, term) {
                            return ValidationObservation::fallback(format!(
                                "{}: {} used SAT-fallback for mixed BV validation",
                                target.entry(index),
                                term_str(),
                            ));
                        }
                        return ValidationObservation::incomplete(
                            target,
                            format!(
                                "{}: {} contains BV comparison predicate with Unknown value",
                                target.entry(index),
                                term_str(),
                            ),
                        );
                    }
                    if self.sat_term_assigned_true(model, term) {
                        return ValidationObservation::fallback(format!(
                            "{}: {} used generic SAT-fallback",
                            target.entry(index),
                            term_str(),
                        ));
                    }
                }
                ValidationObservation::incomplete(
                    target,
                    format!(
                        "{}: {} evaluates to Unknown",
                        target.entry(index),
                        term_str()
                    ),
                )
            }
            EvalValue::Element(_)
            | EvalValue::Rational(_)
            | EvalValue::Algebraic(_)
            | EvalValue::BitVec { .. }
            | EvalValue::Fp(_)
            | EvalValue::String(_)
            | EvalValue::Seq(_) => ValidationObservation::violated(
                target,
                format!(
                    "{} has non-Boolean value: {}",
                    target.entry(index),
                    term_str()
                ),
            ),
        }
    }

    fn dt_user_bool_uf_false_may_be_model_gap(&self, model: &Model, term: TermId) -> bool {
        let atom = match self.ctx.terms.get(term) {
            TermData::Not(inner) => *inner,
            _ => term,
        };
        let TermData::App(sym, args) = self.ctx.terms.get(atom) else {
            return false;
        };
        if *self.ctx.terms.sort(atom) != Sort::Bool || args.is_empty() {
            return false;
        }
        let name = sym.name();
        if Self::is_known_theory_symbol(name) || self.is_exact_dt_internal_symbol(name) {
            return false;
        }
        let Some(euf_model) = model.euf_model.as_ref() else {
            return false;
        };
        euf_model.function_tables.contains_key(name)
            && args.iter().any(|&arg| self.contains_datatype_term(arg))
    }

    fn datatype_seq_equality_false_may_be_model_gap(&self, term: TermId) -> bool {
        let atom = match self.ctx.terms.get(term) {
            TermData::Not(inner) => *inner,
            _ => term,
        };
        let TermData::App(sym, args) = self.ctx.terms.get(atom) else {
            return false;
        };
        if sym.name() != "=" || args.len() != 2 || *self.ctx.terms.sort(atom) != Sort::Bool {
            return false;
        }
        args.iter()
            .any(|&arg| self.contains_datatype_to_seq_uf(arg))
    }

    fn contains_datatype_to_seq_uf(&self, term: TermId) -> bool {
        stacker::maybe_grow(EVAL_STACK_RED_ZONE, EVAL_STACK_SIZE, || {
            match self.ctx.terms.get(term) {
                TermData::App(sym, args) => {
                    let name = sym.name();
                    if self.ctx.terms.sort(term).is_seq()
                        && !Self::is_known_theory_symbol(name)
                        && !self.is_exact_dt_internal_symbol(name)
                        && args.iter().any(|&arg| self.contains_datatype_term(arg))
                    {
                        return true;
                    }
                    args.iter()
                        .any(|&arg| self.contains_datatype_to_seq_uf(arg))
                }
                TermData::Not(inner) => self.contains_datatype_to_seq_uf(*inner),
                TermData::Ite(c, t, e) => {
                    self.contains_datatype_to_seq_uf(*c)
                        || self.contains_datatype_to_seq_uf(*t)
                        || self.contains_datatype_to_seq_uf(*e)
                }
                TermData::Let(_, body) => self.contains_datatype_to_seq_uf(*body),
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                    self.contains_datatype_to_seq_uf(*body)
                }
                TermData::Const(_) | TermData::Var(_, _) => false,
                other => unreachable!(
                    "unhandled TermData variant in contains_datatype_to_seq_uf(): {other:?}"
                ),
            }
        })
    }

    fn uninterpreted_equality_assertion(&self, term: TermId) -> bool {
        let TermData::App(sym, args) = self.ctx.terms.get(term) else {
            return false;
        };
        if sym.name() != "=" || args.len() != 2 {
            return false;
        }
        matches!(self.ctx.terms.sort(args[0]), Sort::Uninterpreted(_))
            && matches!(self.ctx.terms.sort(args[1]), Sort::Uninterpreted(_))
    }

    /// True if `term` is a (possibly negated) `=`/`distinct` whose operands have
    /// a datatype sort AND that datatype carries at least one field routed
    /// through a *separate* theory (BitVector / Int / Real), reachable directly
    /// or through nested datatype fields.
    ///
    /// The truth of a datatype (dis)equality is determined by datatype
    /// constructor congruence (single-constructor injectivity, constructor
    /// distinctness). When every field is itself a datatype, the standalone DT
    /// solver's congruence closure decides it soundly. But when a field is a
    /// BitVector / Int / Real, its value is constrained by the BV / LIA / LRA
    /// theory (e.g. `bv2nat(v x) = bv2nat(v y)` forces `v x = v y`, hence the two
    /// datatype values are equal) — and the DT/EUF equivalence-class model does
    /// NOT integrate those cross-theory field constraints. The eager DT+BV
    /// bit-blast and the bv2nat→LIA bridge both drop datatype congruence here, so
    /// the model evaluator's Bool verdict for the atom — read off EUF element
    /// identity — is NOT authoritative. Such an atom must fail closed unless its
    /// operands resolve to fully-ground canonical values (#dt-bv-congruence).
    pub(in crate::executor::model) fn datatype_sort_equality(&self, term: TermId) -> bool {
        let inner = match self.ctx.terms.get(term) {
            TermData::Not(i) => *i,
            _ => term,
        };
        let TermData::App(sym, args) = self.ctx.terms.get(inner) else {
            return false;
        };
        if !matches!(sym.name(), "=" | "distinct") || args.len() != 2 {
            return false;
        }
        let dt_name = |t: TermId| -> Option<String> {
            match self.ctx.terms.sort(t) {
                Sort::Datatype(dt) => Some(dt.name.clone()),
                Sort::Uninterpreted(n)
                    if self.ctx.datatype_iter().any(|(dt, _)| dt == n.as_str()) =>
                {
                    Some(n.clone())
                }
                _ => None,
            }
        };
        let (Some(n0), Some(_n1)) = (dt_name(args[0]), dt_name(args[1])) else {
            return false;
        };
        self.datatype_has_cross_theory_field(&n0, &mut Vec::new())
    }

    /// True when `term` is a TOP-LEVEL **positive** datatype `=` whose two
    /// operands are *opaque*: neither is a constructor application and neither is
    /// ever read by a datatype-internal symbol (constructor field arg, selector,
    /// or tester) anywhere in the problem (#dt-opaque-eq).
    ///
    /// The ONLY datatype reasoning the eager DT+BV bit-blast leaves unencoded is
    /// constructor congruence — injectivity (observed through selectors) and
    /// distinctness (observed through testers). When neither operand is ever
    /// projected by a selector, classified by a tester, or packed into a
    /// constructor, no such constraint can observe them, so the unencoded
    /// congruence is provably irrelevant to this atom. A positive equality is
    /// asserted true, and a model assigning both operands one shared (arbitrary)
    /// datatype value satisfies it while disturbing nothing else (UF congruence
    /// over datatype arguments IS encoded, so `f(a)`/`f(b)` already track `a=b`).
    ///
    /// SOUNDNESS: confined to POSITIVE equalities, so it can never launder the
    /// EUF-class-identity unsoundness the `#dt-bv-congruence` guard protects
    /// against (which is a *disequality* hazard). It only ever ACCEPTS an
    /// already-asserted, provably-satisfiable equality — it can neither
    /// manufacture a wrong UNSAT nor accept a violated atom.
    pub(in crate::executor::model) fn dt_positive_eq_opaque_satisfiable(
        &self,
        term: TermId,
    ) -> bool {
        // POSITIVE (non-negated) `=` only.
        if matches!(self.ctx.terms.get(term), TermData::Not(_)) {
            return false;
        }
        let TermData::App(sym, args) = self.ctx.terms.get(term) else {
            return false;
        };
        if sym.name() != "=" || args.len() != 2 {
            return false;
        }
        let operands = [args[0], args[1]];
        for &x in &operands {
            // Operand must be datatype-sorted (a real datatype, not a bare
            // uninterpreted sort — those use the element-model path).
            let is_dt = match self.ctx.terms.sort(x) {
                Sort::Datatype(_) => true,
                Sort::Uninterpreted(n) => self.ctx.datatype_iter().any(|(dt, _)| dt == n.as_str()),
                _ => false,
            };
            if !is_dt {
                return false;
            }
            // A constructor application is decided by reduction/resolve_ground.
            if let TermData::App(s, _) = self.ctx.terms.get(x) {
                if self.ctx.is_constructor(s.name()).is_some() {
                    return false;
                }
            }
            if self.dt_term_observed_by_dt_internal_op(x) {
                return false;
            }
        }
        true
    }

    /// True when `term` is a TOP-LEVEL **disequality** `(not (= a b))` whose two
    /// operands are *opaque* datatype values (the DUAL of
    /// [`Self::dt_positive_eq_opaque_satisfiable`]). Such a disequality is
    /// provably SATISFIABLE — and the model that committed it true is genuine —
    /// so it can be accepted rather than fail-closed to Unknown (#dt-opaque-diseq).
    ///
    /// SOUNDNESS. The only datatype fact the eager DT+BV bit-blast leaves
    /// unencoded is constructor CONGRUENCE (injectivity via selectors,
    /// distinctness via testers). The `#dt-bv-congruence` disequality hazard is:
    /// two operands the model places in DISTINCT EUF classes whose fields the
    /// field theory actually forces equal — they ought to be merged, so the
    /// disequality is spuriously SAT. That hazard requires a FIELD to be observed
    /// (a selector/tester/constructor reading an operand). When NEITHER operand is
    /// ever projected by a selector, classified by a tester, or packed into a
    /// constructor, no cross-theory constraint can force their fields — so two
    /// distinct values genuinely exist, PROVIDED the datatype is non-degenerate
    /// (has at least two distinct values). A single-valued datatype (one nullary
    /// constructor) would make `a != b` UNSAT even for opaque operands, so that
    /// case is explicitly excluded. The caller additionally requires the model to
    /// evaluate the disequality to `Bool(true)` (the operands really are in
    /// distinct classes), so this only ever ACCEPTS an asserted, model-confirmed,
    /// provably-satisfiable disequality — never launders a violated atom.
    pub(in crate::executor::model) fn dt_diseq_opaque_satisfiable(&self, term: TermId) -> bool {
        // NEGATED `=` only (a disequality).
        let TermData::Not(inner) = self.ctx.terms.get(term) else {
            return false;
        };
        let TermData::App(sym, args) = self.ctx.terms.get(*inner) else {
            return false;
        };
        if sym.name() != "=" || args.len() != 2 {
            return false;
        }
        let operands = [args[0], args[1]];
        for &x in &operands {
            // Operand must be a real datatype value (carrier sort of a registered
            // datatype), not a bare uninterpreted sort.
            let dt_name = match self.ctx.terms.sort(x) {
                Sort::Datatype(dt) => dt.name.clone(),
                Sort::Uninterpreted(n)
                    if self.ctx.datatype_iter().any(|(dt, _)| dt == n.as_str()) =>
                {
                    n.clone()
                }
                _ => return false,
            };
            // A constructor application is decided by reduction, not here.
            if let TermData::App(s, _) = self.ctx.terms.get(x) {
                if self.ctx.is_constructor(s.name()).is_some() {
                    return false;
                }
            }
            // Any selector/tester/constructor observation could pin a field across
            // theories — fail closed to the existing path (soundness).
            if self.dt_term_observed_by_dt_internal_op(x) {
                return false;
            }
            // A single-valued datatype makes `a != b` UNSAT even for opaque
            // operands; only accept when two distinct values demonstrably exist.
            if !self.datatype_has_two_distinct_values(&dt_name, &mut Vec::new()) {
                return false;
            }
        }
        true
    }

    /// Conservative lower bound on a datatype's cardinality: returns true only
    /// when the datatype provably has at least two distinct values — it has two
    /// or more constructors, or a single constructor carrying a field whose sort
    /// itself has at least two values (Bool, a non-empty BitVector, Int, Real,
    /// String, a Seq, a non-datatype uninterpreted sort, or a recursively
    /// non-degenerate datatype field). `seen` guards recursive datatypes; a
    /// purely-recursive cycle with no branching contributes no new values and is
    /// treated as not-yet-proven (returns false up that path).
    fn datatype_has_two_distinct_values(&self, dt_name: &str, seen: &mut Vec<String>) -> bool {
        if seen.iter().any(|s| s == dt_name) {
            return false;
        }
        seen.push(dt_name.to_string());
        let Some((_, ctors)) = self.ctx.datatype_iter().find(|(dt, _)| *dt == dt_name) else {
            return false;
        };
        let ctors: Vec<String> = ctors.iter().map(|c| c.to_string()).collect();
        if ctors.len() >= 2 {
            return true;
        }
        for ctor in &ctors {
            let Some(info) = self.ctx.constructor_selector_info(ctor) else {
                continue;
            };
            for (_sel, field_sort) in info {
                match field_sort {
                    Sort::Bool
                    | Sort::Int
                    | Sort::Real
                    | Sort::String
                    | Sort::Seq(_)
                    | Sort::Array(_) => return true,
                    Sort::BitVec(bv) if bv.width >= 1 => return true,
                    Sort::Datatype(inner) => {
                        if self.datatype_has_two_distinct_values(&inner.name, seen) {
                            return true;
                        }
                    }
                    Sort::Uninterpreted(n) => {
                        if self.ctx.datatype_iter().any(|(dt, _)| dt == n.as_str()) {
                            if self.datatype_has_two_distinct_values(n, seen) {
                                return true;
                            }
                        } else {
                            // A non-datatype uninterpreted sort is treated as
                            // having >= 2 elements (ay never imposes a
                            // cardinality-1 constraint), so a field of that sort
                            // yields >= 2 distinct datatype values.
                            return true;
                        }
                    }
                    _ => {}
                }
            }
        }
        false
    }

    /// True if `x` appears as an argument of any datatype-internal symbol
    /// application (constructor, selector, or tester) in the term store — i.e. a
    /// term through which datatype constructor congruence could observe `x`.
    fn dt_term_observed_by_dt_internal_op(&self, x: TermId) -> bool {
        for idx in 0..self.ctx.terms.len() {
            let tid = TermId(idx as u32);
            if let TermData::App(sym, args) = self.ctx.terms.get(tid) {
                if args.contains(&x) && self.is_exact_dt_internal_symbol(sym.name()) {
                    return true;
                }
            }
        }
        false
    }

    /// True if `term` is a (possibly negated) `=`/`distinct` where at least one
    /// operand is a SELECTOR application over a datatype-sorted term (or a
    /// constructor application). Such an atom is a datatype-reconstruction
    /// (dis)equality: its truth follows from projecting the datatype value
    /// through its constructor, a step the eager DT+BV bit-blast does not encode.
    /// User UF applications (a declared function head) are explicitly NOT
    /// selectors, so `(distinct (f x b) (f y b))` does not match.
    pub(in crate::executor::model) fn dt_reconstruction_equality(&self, term: TermId) -> bool {
        let inner = match self.ctx.terms.get(term) {
            TermData::Not(i) => *i,
            _ => term,
        };
        let TermData::App(sym, args) = self.ctx.terms.get(inner) else {
            return false;
        };
        if !matches!(sym.name(), "=" | "distinct") || args.len() != 2 {
            return false;
        }
        args.iter().any(|&a| self.is_dt_projection_operand(a))
    }

    /// True if `term` is a COMPOUND Boolean formula (or/and/not/ite/=>/xor,
    /// including Bool-sorted `=`/`distinct` used as iff) that CONTAINS —
    /// anywhere in its Boolean structure — a datatype-reconstruction
    /// (dis)equality (see [`Self::dt_reconstruction_equality`]) whose operands
    /// do NOT resolve to fully-ground canonical values under `model`
    /// (#dt-bv-congruence, compound extension / #dt-embedded-cycle).
    ///
    /// Such an assertion must not be validated by SAT-fallback or skip: the SAT
    /// solver satisfies it by making one embedded dt equality literal true, and
    /// that literal's truth is exactly the evidence the bare-atom
    /// `#dt-bv-congruence` guard refuses (constructor congruence/acyclicity is
    /// not encoded in the DT+BV bit-blast, so the free literal can describe an
    /// impossible — e.g. cyclic — datatype value).
    ///
    /// Deliberately NOT flagged: compound assertions whose embedded
    /// dt-reconstruction equalities are all fully ground (the evaluator/oracle
    /// already had authority over those), and non-datatype assertions.
    pub(in crate::executor::model) fn compound_contains_nonground_dt_reconstruction_equality(
        &self,
        model: &Model,
        term: TermId,
    ) -> bool {
        stacker::maybe_grow(EVAL_STACK_RED_ZONE, EVAL_STACK_SIZE, || {
            // A (possibly negated) dt-reconstruction (dis)equality: flag iff its
            // operands are not fully ground. (Top-level bare atoms are already
            // handled by the earlier match arm; recursing through them here is
            // harmless and keeps the definition uniform.)
            if self.dt_reconstruction_equality(term) {
                return !dt_equality_operands_fully_ground(self, model, term)
                    && dt_equality_decidable_by_reduction(self, term).is_none();
            }
            match self.ctx.terms.get(term) {
                TermData::Not(inner) => {
                    self.compound_contains_nonground_dt_reconstruction_equality(model, *inner)
                }
                TermData::Ite(c, t, e) => {
                    self.compound_contains_nonground_dt_reconstruction_equality(model, *c)
                        || self.compound_contains_nonground_dt_reconstruction_equality(model, *t)
                        || self.compound_contains_nonground_dt_reconstruction_equality(model, *e)
                }
                TermData::App(sym, args) => {
                    let recurse_all = match sym.name() {
                        "or" | "and" | "not" | "=>" | "xor" => true,
                        // Bool-sorted `=`/`distinct` (iff): descend into Boolean
                        // structure. (Datatype-sorted `=` was handled by the
                        // dt_reconstruction_equality check above.)
                        "=" | "distinct" => {
                            args.iter().all(|&a| *self.ctx.terms.sort(a) == Sort::Bool)
                        }
                        "ite" => true,
                        _ => false,
                    };
                    if !recurse_all {
                        return false;
                    }
                    let args = args.clone();
                    args.iter().any(|&a| {
                        self.compound_contains_nonground_dt_reconstruction_equality(model, a)
                    })
                }
                _ => false,
            }
        })
    }

    /// MASKED three-valued (Kleene) evaluation of a Boolean formula under
    /// `model`, where every datatype-reconstruction (dis)equality whose operands
    /// are neither fully ground nor decidable by selector reduction is treated
    /// as Unknown (`None`) instead of trusting the evaluator's EUF-identity
    /// verdict (#dt-bv-congruence, compound extension / #dt-embedded-cycle).
    ///
    /// Returns `Some(b)` only when the formula's truth value is decided by
    /// TRUSTED atoms alone: ground-resolvable dt equalities (the DtOracle
    /// already had authority over those), selector-reduction-decidable
    /// equalities, and ordinary non-dt-reconstruction atoms (evaluated exactly
    /// as `evaluate_term` does today). Returns `None` when the verdict would
    /// necessarily rest on a masked atom's free EUF truth value.
    ///
    /// SOUNDNESS: masking only ever REMOVES information (Kleene three-valued
    /// connectives are monotone), so `Some(true)` here implies the assertion is
    /// genuinely satisfied by the model's trusted, independently-confirmable
    /// part — a cyclic-model disjunct can never be the deciding literal because
    /// a cyclic datatype value has no ground resolution and is masked.
    fn dt_masked_compound_eval(
        &self,
        model: &Model,
        term: TermId,
        structure_ok: bool,
    ) -> Option<bool> {
        stacker::maybe_grow(EVAL_STACK_RED_ZONE, EVAL_STACK_SIZE, || {
            // Trusted-or-masked dt-reconstruction (dis)equality atom.
            if self.dt_reconstruction_equality(term)
                && !matches!(self.ctx.terms.get(term), TermData::Not(_))
            {
                if let Some(v) = dt_equality_decidable_by_reduction(self, term) {
                    return Some(v);
                }
                if dt_equality_operands_fully_ground(self, model, term) {
                    return match self.evaluate_term(model, term) {
                        EvalValue::Bool(b) => Some(b),
                        _ => None,
                    };
                }
                // Claimed-TRUE positive constructor equality, certified by the
                // model-wide structural consistency check: EUF merging the two
                // sides is REALIZABLE by a genuine datatype model whenever the
                // committed constructor-equality skeleton is occurs/clash
                // consistent (a datatype value is otherwise free), so trusting
                // the TRUE claim is sound. The FALSE claim (a disequality) is
                // NEVER trusted here: cross-theory field constraints can force
                // the sides equal in every genuine model, the very
                // #dt-bv-congruence hazard this guard exists for.
                if structure_ok {
                    if let TermData::App(sym, _) = self.ctx.terms.get(term) {
                        if sym.name() == "="
                            && matches!(self.evaluate_term(model, term), EvalValue::Bool(true))
                        {
                            return Some(true);
                        }
                    }
                }
                return None; // masked: EUF-identity verdict is not evidence
            }
            match self.ctx.terms.get(term) {
                TermData::Not(inner) => self
                    .dt_masked_compound_eval(model, *inner, structure_ok)
                    .map(|b| !b),
                TermData::Ite(c, t, e) => {
                    let (c, t, e) = (*c, *t, *e);
                    match self.dt_masked_compound_eval(model, c, structure_ok) {
                        Some(true) => self.dt_masked_compound_eval(model, t, structure_ok),
                        Some(false) => self.dt_masked_compound_eval(model, e, structure_ok),
                        None => {
                            let tv = self.dt_masked_compound_eval(model, t, structure_ok);
                            let ev = self.dt_masked_compound_eval(model, e, structure_ok);
                            if tv.is_some() && tv == ev {
                                tv
                            } else {
                                None
                            }
                        }
                    }
                }
                TermData::App(sym, args) => {
                    let args = args.clone();
                    match sym.name() {
                        "or" => {
                            let mut all_false = true;
                            for &a in &args {
                                match self.dt_masked_compound_eval(model, a, structure_ok) {
                                    Some(true) => return Some(true),
                                    Some(false) => {}
                                    None => all_false = false,
                                }
                            }
                            if all_false {
                                Some(false)
                            } else {
                                None
                            }
                        }
                        "and" => {
                            let mut all_true = true;
                            for &a in &args {
                                match self.dt_masked_compound_eval(model, a, structure_ok) {
                                    Some(false) => return Some(false),
                                    Some(true) => {}
                                    None => all_true = false,
                                }
                            }
                            if all_true {
                                Some(true)
                            } else {
                                None
                            }
                        }
                        "not" if args.len() == 1 => self
                            .dt_masked_compound_eval(model, args[0], structure_ok)
                            .map(|b| !b),
                        // `(=> a1 .. an c)` == `(or (not a1) .. (not an) c)`.
                        "=>" if args.len() >= 2 => {
                            let (ants, cons) = args.split_at(args.len() - 1);
                            let mut all_known = true;
                            for &a in ants {
                                match self.dt_masked_compound_eval(model, a, structure_ok) {
                                    Some(false) => return Some(true),
                                    Some(true) => {}
                                    None => all_known = false,
                                }
                            }
                            match self.dt_masked_compound_eval(model, cons[0], structure_ok) {
                                Some(true) => Some(true),
                                Some(false) if all_known => Some(false),
                                _ => None,
                            }
                        }
                        "xor" if args.len() >= 2 => {
                            let mut acc = false;
                            for &a in &args {
                                acc ^= self.dt_masked_compound_eval(model, a, structure_ok)?;
                            }
                            Some(acc)
                        }
                        // Bool-sorted `=` (iff): all pairwise equal.
                        "=" if args.len() >= 2
                            && args.iter().all(|&a| *self.ctx.terms.sort(a) == Sort::Bool) =>
                        {
                            let first =
                                self.dt_masked_compound_eval(model, args[0], structure_ok)?;
                            for &a in &args[1..] {
                                if self.dt_masked_compound_eval(model, a, structure_ok)? != first {
                                    return Some(false);
                                }
                            }
                            Some(true)
                        }
                        "ite" if args.len() == 3 => {
                            match self.dt_masked_compound_eval(model, args[0], structure_ok) {
                                Some(true) => {
                                    self.dt_masked_compound_eval(model, args[1], structure_ok)
                                }
                                Some(false) => {
                                    self.dt_masked_compound_eval(model, args[2], structure_ok)
                                }
                                None => {
                                    let tv =
                                        self.dt_masked_compound_eval(model, args[1], structure_ok);
                                    let ev =
                                        self.dt_masked_compound_eval(model, args[2], structure_ok);
                                    if tv.is_some() && tv == ev {
                                        tv
                                    } else {
                                        None
                                    }
                                }
                            }
                        }
                        // Ordinary atom (tester, BV comparison, UF predicate,
                        // non-reconstruction equality, ...): today's evaluator
                        // verdict, unchanged.
                        _ => match self.evaluate_term(model, term) {
                            EvalValue::Bool(b) => Some(b),
                            _ => None,
                        },
                    }
                }
                _ => match self.evaluate_term(model, term) {
                    EvalValue::Bool(b) => Some(b),
                    _ => None,
                },
            }
        })
    }

    /// STRUCTURAL CONSISTENCY certificate for the model's committed datatype
    /// skeleton (#dt-embedded-cycle). Collects every datatype equality and
    /// positive tester — anywhere in the Boolean structure of every assertion —
    /// that the model evaluator commits TRUE, feeds them to a throwaway
    /// [`ay_dt::DtSolver`] (full constructor DAG + selector signatures
    /// registered), and reports whether the pure-DT occurs/clash check accepts
    /// the set.
    ///
    /// `true` certifies that the EUF commitment "all these equalities hold" is
    /// realizable by a GENUINE (well-founded, finite) datatype model: merging
    /// datatype values is unconstrained except by constructor clash,
    /// injectivity, and acyclicity, which is exactly what the DtSolver checks.
    /// A CYCLIC commitment (`x = cons(a, y)` ∧ `y = cons(a, x)`) fails the
    /// occurs-check, so it can never be certified — the caller then keeps such
    /// equalities masked and fails closed. Fail-closed direction only: a
    /// `false` here merely withholds trust (SAT may degrade to Unknown); it
    /// never manufactures a verdict.
    fn dt_committed_ctor_equalities_consistent(&self, model: &Model) -> bool {
        let mut facts: Vec<TermId> = Vec::new();
        let mut seen: std::collections::HashSet<TermId> = std::collections::HashSet::new();
        for i in 0..self.ctx.assertions.len() {
            let a = self.ctx.assertions[i];
            self.collect_committed_dt_facts(model, a, &mut facts, &mut seen);
        }
        if facts.is_empty() {
            return true;
        }
        use ay_core::TheorySolver as _;
        let mut dt = ay_dt::DtSolver::new(&self.ctx.terms);
        for (dt_name, constructors) in self.ctx.datatype_iter() {
            dt.register_datatype(dt_name, constructors);
            for ctor_name in constructors {
                if let Some(info) = self.ctx.constructor_selector_info(ctor_name) {
                    let sel_names: Vec<String> = info.iter().map(|(n, _)| n.clone()).collect();
                    dt.register_ctor_selectors(ctor_name, &sel_names);
                }
            }
        }
        for &t in &facts {
            dt.assert_literal(t, true);
        }
        !matches!(dt.check(), ay_core::TheoryResult::Unsat(_))
    }

    /// Collect the datatype equalities / positive testers inside `term`'s
    /// Boolean structure that the model evaluator commits TRUE, for
    /// [`Self::dt_committed_ctor_equalities_consistent`]. Walks Boolean
    /// connectives only; atoms of other theories contribute nothing.
    fn collect_committed_dt_facts(
        &self,
        model: &Model,
        term: TermId,
        out: &mut Vec<TermId>,
        seen: &mut std::collections::HashSet<TermId>,
    ) {
        if !seen.insert(term) {
            return;
        }
        stacker::maybe_grow(EVAL_STACK_RED_ZONE, EVAL_STACK_SIZE, || {
            match self.ctx.terms.get(term) {
                TermData::Not(inner) => {
                    self.collect_committed_dt_facts(model, *inner, out, seen);
                }
                TermData::Ite(c, t, e) => {
                    let (c, t, e) = (*c, *t, *e);
                    self.collect_committed_dt_facts(model, c, out, seen);
                    self.collect_committed_dt_facts(model, t, out, seen);
                    self.collect_committed_dt_facts(model, e, out, seen);
                }
                TermData::App(sym, args) => {
                    let name = sym.name();
                    let args = args.clone();
                    match name {
                        "or" | "and" | "not" | "=>" | "xor" | "ite" => {
                            for &a in &args {
                                self.collect_committed_dt_facts(model, a, out, seen);
                            }
                        }
                        "=" if args.len() == 2 => {
                            if args.iter().all(|&a| *self.ctx.terms.sort(a) == Sort::Bool) {
                                for &a in &args {
                                    self.collect_committed_dt_facts(model, a, out, seen);
                                }
                            } else {
                                let dt_sorted = args.iter().any(|&a| {
                                    matches!(
                                        self.ctx.terms.sort(a),
                                        Sort::Datatype(_) | Sort::Uninterpreted(_)
                                    )
                                });
                                if dt_sorted
                                    && self.dt_reconstruction_equality(term)
                                    && matches!(
                                        self.evaluate_term(model, term),
                                        EvalValue::Bool(true)
                                    )
                                {
                                    out.push(term);
                                }
                            }
                        }
                        _ if args.len() == 1
                            && name
                                .strip_prefix("is-")
                                .is_some_and(|c| self.ctx.is_constructor(c).is_some()) =>
                        {
                            if matches!(self.evaluate_term(model, term), EvalValue::Bool(true)) {
                                out.push(term);
                            }
                        }
                        _ => {}
                    }
                }
                _ => {}
            }
        })
    }

    /// True if `term` is a selector application over a datatype term, or a
    /// constructor application, or a datatype-sorted term whose value depends on
    /// datatype reconstruction.
    fn is_dt_projection_operand(&self, term: TermId) -> bool {
        let TermData::App(sym, args) = self.ctx.terms.get(term) else {
            return false;
        };
        let name = sym.name();
        // Selector application `(sel d)` where `d` is datatype-sorted.
        let is_selector = self
            .ctx
            .ctor_selectors_iter()
            .any(|(_ctor, sels)| sels.iter().any(|sel| sel == name));
        if is_selector
            && args.len() == 1
            && matches!(
                self.ctx.terms.sort(args[0]),
                Sort::Datatype(_) | Sort::Uninterpreted(_)
            )
        {
            return true;
        }
        // Constructor application.
        self.ctx.is_constructor(name).is_some()
    }

    /// True if datatype `dt_name` has any field whose sort is a separate theory
    /// (BitVector / Int / Real), directly or through nested datatype fields.
    /// `seen` guards against recursive datatype definitions.
    fn datatype_has_cross_theory_field(&self, dt_name: &str, seen: &mut Vec<String>) -> bool {
        if seen.iter().any(|s| s == dt_name) {
            return false;
        }
        seen.push(dt_name.to_string());
        let Some((_, ctors)) = self.ctx.datatype_iter().find(|(dt, _)| *dt == dt_name) else {
            return false;
        };
        let ctors: Vec<String> = ctors.iter().map(|c| c.to_string()).collect();
        for ctor in &ctors {
            let Some(info) = self.ctx.constructor_selector_info(ctor) else {
                continue;
            };
            for (_sel, field_sort) in info {
                match field_sort {
                    Sort::BitVec(_) | Sort::Int | Sort::Real => return true,
                    Sort::Datatype(inner) => {
                        if self.datatype_has_cross_theory_field(&inner.name, seen) {
                            return true;
                        }
                    }
                    Sort::Uninterpreted(n)
                        if self.ctx.datatype_iter().any(|(dt, _)| dt == n.as_str()) =>
                    {
                        if self.datatype_has_cross_theory_field(n, seen) {
                            return true;
                        }
                    }
                    _ => {}
                }
            }
        }
        false
    }

    /// Check whether `term` is a string-theory predicate whose evaluation under
    /// `model` is structurally ground (no model-extraction gap possible) and
    /// evaluates definitively to false. When this returns true, a `Bool(false)`
    /// result from `evaluate_term` is a genuine soundness violation, not a gap
    /// (#8779). Unlike the general `#7460` fallback, ground `str.in_re` with a
    /// fully-resolved string has no hidden unassigned variables.
    ///
    /// Conjunctions `(and p1 p2 ...)` are recursively inspected: if any
    /// conjunct is a definitively-false string predicate, the whole `and`
    /// is definitively false. This lets the gate fire on top-level
    /// assertions like `(and (= sink x_14) (= sink atk_sink))` where the
    /// string inconsistency is nested inside.
    fn string_eval_is_definitive_false(&self, model: &Model, term: TermId) -> bool {
        let TermData::App(sym, args) = self.ctx.terms.get(term) else {
            return false;
        };

        // Descend into top-level conjunctions (#8779).
        if sym.name() == "and" {
            let conjuncts: Vec<TermId> = args.clone();
            return conjuncts
                .iter()
                .any(|&arg| self.string_eval_is_definitive_false(model, arg));
        }

        match sym.name() {
            "str.in_re" | "str.in.re" if args.len() == 2 => {
                let EvalValue::String(s) = self.evaluate_term(model, args[0]) else {
                    return false;
                };
                matches!(
                    ay_strings::ground_eval_in_re(&self.ctx.terms, &s, args[1]),
                    Some(false),
                )
            }
            "str.contains" if args.len() == 2 => {
                let EvalValue::String(s) = self.evaluate_term(model, args[0]) else {
                    return false;
                };
                let EvalValue::String(t) = self.evaluate_term(model, args[1]) else {
                    return false;
                };
                !s.contains(t.as_str())
            }
            "str.prefixof" if args.len() == 2 => {
                let EvalValue::String(s) = self.evaluate_term(model, args[0]) else {
                    return false;
                };
                let EvalValue::String(t) = self.evaluate_term(model, args[1]) else {
                    return false;
                };
                !t.starts_with(s.as_str())
            }
            "str.suffixof" if args.len() == 2 => {
                let EvalValue::String(s) = self.evaluate_term(model, args[0]) else {
                    return false;
                };
                let EvalValue::String(t) = self.evaluate_term(model, args[1]) else {
                    return false;
                };
                !t.ends_with(s.as_str())
            }
            // String equality (#8779): if both sides fully resolve to concrete
            // strings and they differ, the assertion is definitively false.
            // This catches cases like `(= atk_sink (str.++ ... atkPtn ...))`
            // where the extracted model has `atk_sink = ""` but the RHS
            // concat evaluates to a non-empty string — a genuine inconsistency
            // the string theory failed to detect, not a model-extraction gap.
            "=" if args.len() == 2
                && *self.ctx.terms.sort(args[0]) == Sort::String
                && *self.ctx.terms.sort(args[1]) == Sort::String =>
            {
                let EvalValue::String(s) = self.evaluate_term(model, args[0]) else {
                    return false;
                };
                let EvalValue::String(t) = self.evaluate_term(model, args[1]) else {
                    return false;
                };
                s != t
            }
            _ => false,
        }
    }

    fn string_functional_equality_model_gap(&self, model: &Model, term: TermId) -> bool {
        self.string_functional_equality_model_gap_rec(model, term, 16)
    }

    fn string_functional_equality_model_gap_rec(
        &self,
        model: &Model,
        term: TermId,
        depth: u32,
    ) -> bool {
        if depth == 0 {
            return false;
        }

        match self.ctx.terms.get(term) {
            TermData::App(sym, args)
                if sym.name() == "="
                    && args.len() == 2
                    && *self.ctx.terms.sort(args[0]) == Sort::String =>
            {
                let has_functional_side = self.string_term_has_functional_app(args[0], depth - 1)
                    || self.string_term_has_functional_app(args[1], depth - 1);
                has_functional_side
                    && !matches!(self.evaluate_term(model, term), EvalValue::Bool(true))
            }
            TermData::App(sym, args) if sym.name() == "and" => args
                .iter()
                .any(|&arg| self.string_functional_equality_model_gap_rec(model, arg, depth - 1)),
            TermData::App(sym, args)
                if sym.name() == "="
                    && args.len() == 2
                    && *self.ctx.terms.sort(args[0]) == Sort::Bool
                    && *self.ctx.terms.sort(args[1]) == Sort::Bool =>
            {
                args.iter().any(|&arg| {
                    self.string_functional_equality_model_gap_rec(model, arg, depth - 1)
                })
            }
            _ => false,
        }
    }

    fn string_term_has_functional_app(&self, term: TermId, depth: u32) -> bool {
        if depth == 0 {
            return false;
        }
        match self.ctx.terms.get(term) {
            TermData::App(sym, args) => {
                matches!(
                    sym.name(),
                    "str.++"
                        | "str.replace"
                        | "str.replace_all"
                        | "str.replace_re"
                        | "str.replace_re_all"
                        | "str.substr"
                        | "str.at"
                ) || args
                    .iter()
                    .any(|&arg| self.string_term_has_functional_app(arg, depth - 1))
            }
            TermData::Ite(cond, then_term, else_term) => {
                self.string_term_has_functional_app(*cond, depth - 1)
                    || self.string_term_has_functional_app(*then_term, depth - 1)
                    || self.string_term_has_functional_app(*else_term, depth - 1)
            }
            TermData::Let(bindings, body) => {
                bindings
                    .iter()
                    .any(|(_, value)| self.string_term_has_functional_app(*value, depth - 1))
                    || self.string_term_has_functional_app(*body, depth - 1)
            }
            TermData::Not(inner) => self.string_term_has_functional_app(*inner, depth - 1),
            _ => false,
        }
    }

    fn string_predicate_is_structurally_ground(&self, model: &Model, term: TermId) -> bool {
        let TermData::App(sym, args) = self.ctx.terms.get(term) else {
            return false;
        };

        match sym.name() {
            "str.in_re" | "str.in.re" if args.len() == 2 => {
                ay_strings::ground_eval_in_re(&self.ctx.terms, "", args[1]).is_some()
            }
            "str.contains" | "str.prefixof" | "str.suffixof" if args.len() == 2 => {
                matches!(self.evaluate_term(model, args[1]), EvalValue::String(_))
            }
            _ => false,
        }
    }

    fn apply_assumption_observation(
        accepted_assumptions: &mut usize,
        skipped_internal: &mut usize,
        skipped_quantifier: &mut usize,
        observation: ValidationObservation,
    ) -> Result<(), ModelValidationError> {
        match observation {
            ValidationObservation::Skip(kind) => match kind {
                ValidationSkipKind::Internal => {
                    *skipped_internal += 1;
                    Ok(())
                }
                ValidationSkipKind::Quantifier => {
                    *skipped_quantifier += 1;
                    Ok(())
                }
                other => Err(ModelValidationError::incomplete(
                    VerificationBoundary::SmtAssumption,
                    format!("unsupported assumption skip category: {other:?}"),
                )),
            },
            ValidationObservation::Fallback(failure) => {
                Err(ModelValidationError::Incomplete(failure))
            }
            ValidationObservation::Verdict { verdict, .. } => match verdict {
                VerificationVerdict::Verified { .. } => {
                    *accepted_assumptions += 1;
                    Ok(())
                }
                VerificationVerdict::Incomplete(failure) => {
                    Err(ModelValidationError::Incomplete(failure))
                }
                VerificationVerdict::Violated(failure) => {
                    Err(ModelValidationError::Violated(failure))
                }
                _ => {
                    unreachable!("unexpected verification verdict variant in assumption validation")
                }
            },
        }
    }

    /// Validate temporary assumptions used by `check_sat_assuming`.
    pub(in crate::executor::model) fn validate_sat_assumptions(
        &self,
        assumptions: &[TermId],
    ) -> Result<(), ModelValidationError> {
        let model = match (&self.last_result, &self.last_model) {
            (Some(SolveResult::Sat), Some(m)) => m,
            (Some(SolveResult::Sat), None) => {
                if assumptions.is_empty() {
                    return Ok(());
                }
                return Err(ModelValidationError::incomplete(
                    VerificationBoundary::SmtAssumption,
                    "no model available",
                ));
            }
            _ => {
                return Err(ModelValidationError::violated(
                    VerificationBoundary::SmtAssumption,
                    "Assumption validation requires SAT result",
                ));
            }
        };

        let mut accepted_assumptions = 0usize;
        let mut skipped_internal = 0usize;
        let mut skipped_quantifier = 0usize;
        let term_flags = self.precompute_term_flags();

        for (i, &assumption) in assumptions.iter().enumerate() {
            let observation = self.validate_term_observation(
                model,
                assumption,
                i,
                term_flags[assumption.index()],
                false,
                ValidationTarget::Assumption,
            );
            Self::apply_assumption_observation(
                &mut accepted_assumptions,
                &mut skipped_internal,
                &mut skipped_quantifier,
                observation,
            )?;
        }

        if accepted_assumptions == 0 && skipped_internal > 0 {
            return Err(ModelValidationError::incomplete(
                VerificationBoundary::SmtAssumption,
                format!(
                    "all {} assumptions were skipped or unevaluable \
                     (internal={}, quantifier={})",
                    assumptions.len(),
                    skipped_internal,
                    skipped_quantifier,
                ),
            ));
        }

        Ok(())
    }
}
