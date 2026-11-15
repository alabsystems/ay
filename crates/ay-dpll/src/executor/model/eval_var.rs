// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Variable evaluation: look up a `TermData::Var` in the appropriate theory model.
//!
//! Extracted from `mod.rs` for code health (#5970). Each sort (Bool, Int, Real,
//! BitVec, FP, String, Seq, Uninterpreted, Datatype) has its own lookup chain
//! with fallbacks across theory models.

use ay_core::term::TermData;
use ay_core::{Sort, TermId};
use num_rational::BigRational;
use num_traits::Zero;

use super::{EvalValue, Model};
use crate::executor::Executor;

impl Executor {
    /// Whether `model` itself assigns the integer variable `term` (a theory
    /// value or a merged EUF value), as opposed to the evaluator's default.
    pub(super) fn model_assigns_int(model: &Model, term: TermId) -> bool {
        model
            .lia_model
            .as_ref()
            .is_some_and(|lia| lia.values.contains_key(&term))
            || model
                .lra_model
                .as_ref()
                .is_some_and(|lra| lra.values.contains_key(&term))
            || model.euf_model.as_ref().is_some_and(|euf| {
                euf.term_values.contains_key(&term) || euf.int_values.contains_key(&term)
            })
            || model.completed_values.contains_key(&term)
    }

    /// Evaluate a `TermData::Var`: theory-model lookup chain first, then — only
    /// when every theory lookup yields Unknown — the model's completion slot
    /// (`Model::completed_values`, filled before validation by
    /// model/completion.rs for constants no theory model constrained).
    ///
    /// The completion slot is read LAST so it can never shadow a theory-model
    /// value, and it is read HERE — inside the evaluation chain — so the
    /// validation gate and the model printers see the identical value
    /// (#no-fabricated-model-values).
    pub(super) fn evaluate_var(&self, model: &Model, term_id: TermId, sort: &Sort) -> EvalValue {
        match model.field_assignment_value(self, term_id) {
            Ok(Some(value)) => return value,
            Ok(None) => {}
            Err(origin) => {
                self.record_evaluation_stop(origin);
                return EvalValue::Unknown;
            }
        }
        if sort == &Sort::Complex {
            return match self.evaluate_complex_variable(model, term_id) {
                EvalValue::Unknown => model
                    .completed_values
                    .get(&term_id)
                    .map(super::evaluation_copies::copy)
                    .unwrap_or(EvalValue::Unknown),
                value => value,
            };
        }
        match self.evaluate_var_theory(model, term_id, sort) {
            EvalValue::Unknown => model
                .completed_values
                .get(&term_id)
                .map(super::evaluation_copies::copy)
                .unwrap_or(EvalValue::Unknown),
            value => value,
        }
    }

    /// The EUF class element `(get-model)` prints for the declared constant
    /// `term_id` straight from `euf_model.term_values`, ahead of every theory
    /// model; `None` when the printer renders the constant through the
    /// evaluation chain instead.
    ///
    /// ONE owner for that read. The printer calls it to choose what to print,
    /// and the independent gate calls it to learn what WILL be printed, so a
    /// constant whose printed value differs from the value the gate checked
    /// cannot be published (`IndependentModelView::leaf_value`). Excluded are
    /// the sorts whose chain ([`Self::evaluate_var`]) reads another model
    /// first: Int/Real (LIA/LRA, #array-completion-order), Seq (the EUF entry
    /// is only a class label), BitVec, and the FP model's two sorts:
    /// FloatingPoint, and RoundingMode, whose value is the mode the FP circuit
    /// decoded from its three bits (`fp_model.rm_values`). Reading EUF first
    /// for a mode printed an FP-to-Real Real subproblem's own choice of mode
    /// (`RNE`) while get-value and the gate read the circuit's (`RTZ`).
    pub(in crate::executor) fn euf_printed_constant<'m>(
        &self,
        model: &'m Model,
        term_id: TermId,
        sort: &Sort,
    ) -> Option<&'m str> {
        if matches!(
            sort,
            Sort::Int
                | Sort::Real
                | Sort::Complex
                | Sort::Seq(_)
                | Sort::BitVec(_)
                | Sort::Array(_)
                | Sort::FloatingPoint(..)
        ) || crate::executor::rm_domain::is_rm_sort(sort)
        {
            return None;
        }
        model
            .euf_model
            .as_ref()?
            .term_values
            .get(&term_id)
            .map(String::as_str)
    }

    /// Theory-model lookup chain for a `TermData::Var` (no completion slot).
    ///
    /// The lookup chain depends on the variable's sort:
    /// - Bool: SAT model → BV bool_overrides → Unknown
    /// - Int: LIA → LRA → EUF term_values/int_values → default 0
    /// - Real: LRA → EUF term_values → default 0
    /// - BitVec: BV model → Unknown
    /// - FP: FP model → Unknown
    /// - String: String model → Unknown
    /// - Seq: Seq model → Unknown
    /// - RoundingMode: FP model's symbolic-mode values → EUF class naming a
    ///   mode → Unknown (never a minted element)
    /// - Uninterpreted: EUF term_values → Unknown
    /// - Datatype: constructor name resolution → Unknown
    fn evaluate_var_theory(&self, model: &Model, term_id: TermId, sort: &Sort) -> EvalValue {
        // A rounding-mode constant the FP bit-blaster gave three bits, else its
        // EUF class when that names a mode. A minted `@RoundingMode!n` element
        // is not a value of the sort (`rm_concrete.rs` replaces them before
        // completion); should one survive, the constant stays Unknown, so
        // completion or the gate decides it instead of a printer publishing it.
        if crate::executor::rm_domain::is_rm_sort(sort) {
            let mode = crate::executor::rm_domain::rm_literal_mode(&self.ctx.terms, term_id)
                .or_else(|| {
                    model
                        .fp_model
                        .as_ref()
                        .and_then(|fp| fp.rm_values.get(&term_id).copied())
                })
                .or_else(|| {
                    model
                        .euf_model
                        .as_ref()
                        .and_then(|euf| euf.term_values.get(&term_id))
                        .and_then(|element| ay_fp::RoundingMode::from_name(element))
                });
            return mode.map_or(EvalValue::Unknown, |mode| {
                EvalValue::Element(crate::executor::rm_domain::rm_long_name(mode).to_string())
            });
        }
        if matches!(sort, Sort::Bool) {
            // Boolean variable: check SAT model
            match self.term_value(&model.sat_model, &model.term_to_var, term_id) {
                Some(b) => EvalValue::Bool(b),
                None => {
                    // Check model-level bool_overrides for Bool variables recovered
                    // from VariableSubstitution (e.g., p -> (> x 0) in QF_LIA).
                    if let Some(&b) = model.bool_overrides.get(&term_id) {
                        return EvalValue::Bool(b);
                    }
                    // Check BV model bool_overrides for variables recovered
                    // from preprocessing substitution (e.g., p -> (bvult x #x42)) (#5524)
                    if let Some(ref bv_model) = model.bv_model {
                        if let Some(&b) = bv_model.bool_overrides.get(&term_id) {
                            return EvalValue::Bool(b);
                        }
                    }
                    // (#5542) Return Unknown for Bool variables not in any model.
                    // Previously defaulted to false, which could mask missing model
                    // entries as valid false assignments. Matches Int/Real behavior.
                    EvalValue::Unknown
                }
            }
        } else if matches!(sort, Sort::Int) {
            // Integer variable: check LIA model first, then LRA model
            if let Some(ref lia_model) = model.lia_model {
                if let Some(val) = lia_model.values.get(&term_id) {
                    if !super::evaluation_copies::integer(val) {
                        return EvalValue::Unknown;
                    }
                    return EvalValue::Rational(BigRational::from(val.clone()));
                }
            }
            // Fall back to LRA model (when using pure LRA solver for arithmetic)
            if let Some(ref lra_model) = model.lra_model {
                if let Some(val) = lra_model.values.get(&term_id) {
                    if !super::evaluation_copies::rational(val) {
                        return EvalValue::Unknown;
                    }
                    return EvalValue::Rational(val.clone());
                }
            }
            let has_arith_model = model.lia_model.is_some() || model.lra_model.is_some();
            // Fall back to merged EUF model values for model completion.
            // Combined AUF* solvers merge arithmetic assignments into EUF model
            // term-values, so this covers Int terms omitted by LIA/LRA extraction.
            if let Some(ref euf_model) = model.euf_model {
                if let Some(raw) = euf_model.term_values.get(&term_id) {
                    if let EvalValue::Rational(r) =
                        self.parse_model_value_string(raw, &Some(Sort::Int))
                    {
                        return EvalValue::Rational(r);
                    }
                }
                if let Some(val) = euf_model.int_values.get(&term_id) {
                    if !super::evaluation_copies::integer(val) {
                        return EvalValue::Unknown;
                    }
                    return EvalValue::Rational(BigRational::from(val.clone()));
                }
            }
            if has_arith_model {
                // If arithmetic theories and merged EUF values did not assign this term,
                // keep the result Unknown instead of inventing a value.
                return EvalValue::Unknown;
            }
            // #subst-key-no-default: a missing entry is not evidence that this
            // variable is FREE — it may have been eliminated by preprocessing
            // and be DEFINED by a recorded substitution, exactly the contract
            // the BitVec branch below already states. Fabricating 0 here is
            // not merely a guess: it is read back by model completion, whose
            // substitution fixpoint is fill-only (it derives `from` from its
            // RHS only while `from` still evaluates to Unknown), so the
            // phantom 0 PERMANENTLY shadows the definition and the strict
            // gate then refutes the very equality that defined it. Measured
            // on the LIA-less array+EUF lane: `(= x (select A i))` records
            // `x -> (select A i)`, `x` fabricated 0, and the arrays oracle
            // rejected assertion `(= x (select A i))` on a candidate whose
            // array content was correct. Keeping it Unknown hands the key to
            // completion, which either replays the definition or — when the
            // RHS is genuinely unconstrained — installs the same default in
            // phase 2.5, so a key completion cannot derive ends up exactly
            // where it was before.
            if self.recorded_var_substitutions.contains_key(&term_id) {
                return EvalValue::Unknown;
            }
            // An explicitly completed value is real model data and must win
            // over the unassigned-variable fabrication below: completion
            // derives pins the deciding lane never valued (e.g. Int pins in
            // a BV-lane model with no arithmetic sub-model at all), and
            // fabricating 0 here would shadow them permanently — the same
            // defect the substitution-key guard above prevents for keys.
            if let Some(completed) = model.completed_values.get(&term_id) {
                return super::evaluation_copies::copy(completed);
            }
            // Default to 0 for unassigned integer variables
            EvalValue::Rational(BigRational::zero())
        } else if matches!(sort, Sort::Real) {
            // Exact NRA algebraic witness first (e.g. x = √2 for `x*x = 2`,
            // TARGET nra_irrational): it is authoritative over any rational
            // model value — the rational theory models cannot represent the
            // irrational witness, and any leftover rational entry for the
            // variable would be a stale simplex assignment, not the model.
            if let Some(alg) = self.nra_algebraic_model.get(&term_id) {
                if !super::evaluation_copies::algebraic(alg) {
                    return EvalValue::Unknown;
                }
                return EvalValue::Algebraic(alg.clone());
            }
            // Real variable: check LRA model first
            if let Some(ref lra_model) = model.lra_model {
                if let Some(val) = lra_model.values.get(&term_id) {
                    if !super::evaluation_copies::rational(val) {
                        return EvalValue::Unknown;
                    }
                    return EvalValue::Rational(val.clone());
                }
            }
            let has_arith_model = model.lra_model.is_some();
            // Fall back to merged EUF model values for model completion.
            // Combined AUF* solvers merge LRA assignments into EUF model
            // term-values via merge_lra_values(), so this covers Real terms
            // omitted by LRA extraction in combined logics (QF_UFLRA, etc.).
            if let Some(ref euf_model) = model.euf_model {
                if let Some(raw) = euf_model.term_values.get(&term_id) {
                    if let EvalValue::Rational(r) =
                        self.parse_model_value_string(raw, &Some(Sort::Real))
                    {
                        return EvalValue::Rational(r);
                    }
                }
            }
            if has_arith_model {
                return EvalValue::Unknown;
            }
            // Default to 0 for unassigned real variables
            EvalValue::Rational(BigRational::zero())
        } else if let Sort::BitVec(bv) = sort {
            // BitVec variable: check BV model
            if let Some(ref bv_model) = model.bv_model {
                if let Some(val) = bv_model.values.get(&term_id) {
                    if !super::evaluation_copies::integer(val) {
                        return EvalValue::Unknown;
                    }
                    return EvalValue::BitVec {
                        value: val.clone(),
                        width: bv.width,
                    };
                }
            }
            // #subst-key-no-default, BitVec side: a variable ELIMINATED by
            // preprocessing is DEFINED by its recorded substitution, and that
            // exact definition outranks every lane-local value below. The
            // dtbv encoding's field variables are the measured case: DT
            // injectivity records `seed!f1 -> #x00000002`, the EUF lane —
            // which never models injectivity — then mints a free literal-
            // spelled class value (`#x00000004`) for the same variable, and
            // reading that here made the datatype-field oracle materialize
            // `(f1 (select m 0))` to 4 against a cell holding
            // `(mk #x1 #x2)` and refute a genuine `sat` (C-4 of the
            // 2026-09-16 solver-fix round). Keep it Unknown so completion
            // replays the definition INTO the BV model (fill-only, exactly
            // the contract the Int branch states above and
            // `missing_bv_entries_are_defaulted_only_after_substitution_recovery`
            // pins): the installed entry is then read by the first branch.
            if self.recorded_var_substitutions.contains_key(&term_id) {
                return EvalValue::Unknown;
            }
            // A missing entry is not evidence that the variable is free: it
            // may have been eliminated by preprocessing and be defined by a
            // recorded substitution. Keep it Unknown so model completion can
            // either replay that definition or explicitly install the
            // canonical value for a genuinely free variable. This also covers
            // the no-BV-model AUFLIA route, whose uninterpreted treatment does
            // not provide BV-semantic values (#5356).
            //
            // NO EUF-CLASS READ HERE (#bv-euf-class-literal-read, REVERTED
            // 2026-09-17). Answering a BitVec variable from its EUF CLASS
            // spelling recovers array-index identifications nothing else in
            // the model records (+111 `sat` over the 2540-query `sfz` corpus),
            // but EUF models no BitVec semantics, so the same spelling can
            // answer with a literal contradicting the query's own
            // `bvult`/`bvule` atoms: 17 `sat` verdicts LOST,
            // among them `sfz/q/dtn/dtn_0001_named.smt2` (the class literal
            // for `s2!h0` falsifies `(bvult (h0 s2) #x00000001)`),
            // `sfz/q/dta/dta_0024_plain.smt2` and
            // `sfz/q/abv/abv_0103_plain.smt2`, all of which z3 and the
            // previous commit answer `sat`. A RETRACTING version was built
            // and measured: it cannot contain the damage, because the reads
            // that matter happen during SEARCH — baked into the extracted
            // model (the `_BV_LIA_INDEP` reconcile's cell pins, the AUFLIA
            // lane's own model check) long before any validation pass could
            // retract them (`abv_0103` retracts and still fails; `dtn_0001`
            // spends all 39 reads before finalize is entered). A sound
            // version needs the candidate to be VERIFIED where it is taken —
            // per variable against the BV atoms that mention it — or the
            // whole solve re-run under the retraction. Model completion's
            // phase 0.5 is that verified version
            // (#uninterpreted-bitvec-class-values,
            // `completion/bitvec_classes.rs`): it offers the class value once,
            // to a BV-model-free witness, and never through this evaluator.
            EvalValue::Unknown
        } else if matches!(sort, Sort::FloatingPoint(..)) {
            // FloatingPoint variable: check FP model
            if let Some(ref fp_model) = model.fp_model {
                if let Some(val) = fp_model.values.get(&term_id) {
                    if !super::evaluation_copies::fp(val) {
                        return EvalValue::Unknown;
                    }
                    return EvalValue::Fp(val.clone());
                }
            }
            EvalValue::Unknown
        } else if matches!(sort, Sort::String) {
            // String variable: check String model.
            if let Some(ref string_model) = model.string_model {
                if let Some(value) = string_model.values.get(&term_id) {
                    if !super::evaluation_copies::string(value) {
                        return EvalValue::Unknown;
                    }
                    return EvalValue::String(value.clone());
                }
            }
            EvalValue::Unknown
        } else if let Sort::Seq(ref elem_sort) = sort {
            // Seq variable: check Seq model (#5995).
            // SeqModel stores Vec<String> per variable; convert each
            // element string to EvalValue using the element sort.
            if let Some(ref seq_model) = model.seq_model {
                if let Some(elems) = seq_model.values.get(&term_id) {
                    if !super::evaluation_copies::cells(elems.len())
                        || !elems
                            .iter()
                            .all(|value| super::evaluation_copies::string(value))
                    {
                        return EvalValue::Unknown;
                    }
                    let eval_elems: Vec<EvalValue> = elems
                        .iter()
                        .map(|s| {
                            self.parse_model_value_string_borrowed(s, Some(elem_sort.as_ref()))
                        })
                        .collect();
                    // Only return Seq if all elements resolved
                    if eval_elems.iter().all(|e| !matches!(e, EvalValue::Unknown)) {
                        return EvalValue::Seq(eval_elems);
                    }
                }
            }
            // Length-0 collapse (#seq-len-zero): a seq variable with no explicit
            // seq_model entry but whose `seq.len(var)` is pinned to 0 in the
            // (LIA-backed) model is the unique empty sequence. Returning the
            // concrete empty `Seq([])` lets the model evaluator and the SeqOracle
            // decide predicates over it (e.g. `seq.suffixof ([0]++s) [1]` where the
            // length axioms force `len(s) = 0`). Sound: length 0 <=> empty.
            if self.seq_var_len_is_zero(model, term_id) {
                return EvalValue::Seq(vec![]);
            }
            EvalValue::Unknown
        } else if let Some(ref euf_model) = model.euf_model {
            // Uninterpreted sort: check EUF model
            if let Some(elem) = euf_model.term_values.get(&term_id) {
                if !super::evaluation_copies::string(elem) {
                    return EvalValue::Unknown;
                }
                return EvalValue::Element(elem.clone());
            }
            EvalValue::Unknown
        } else {
            // Nullary DT constructors are stored as Var terms (#1745).
            // In pure QF_DT (no EUF model), resolve them to their
            // constructor names so assertion-based value extraction
            // works (#5450).
            if let TermData::Var(name, _) = self.ctx.terms.get(term_id) {
                if self.ctx.is_constructor(name).is_some() {
                    if !super::evaluation_copies::string(name) {
                        return EvalValue::Unknown;
                    }
                    return EvalValue::Element(name.clone());
                }
            }
            EvalValue::Unknown
        }
    }

    /// True when some `seq.len(seq_var)` application exists in the term store and
    /// is pinned to 0 by the integer (LIA) model. Used to collapse an
    /// otherwise-unresolved seq variable to the empty sequence (#seq-len-zero).
    ///
    /// The length value is read DIRECTLY from `lia_model.values` (and the SAT-int
    /// fallback), NOT via `evaluate_term`, because evaluating `seq.len(var)` would
    /// recurse back into `evaluate_var(var)` and this helper — an infinite loop.
    /// Bounded by the term store size; only invoked on the seq-var fallback path.
    fn seq_var_len_is_zero(&self, model: &Model, seq_var: TermId) -> bool {
        use ay_core::term::Symbol;
        let Some(ref lia_model) = model.lia_model else {
            return false;
        };
        for idx in 0..self.ctx.terms.len() {
            let tid = TermId(idx as u32);
            if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(tid) {
                if name == "seq.len" && args.len() == 1 && args[0] == seq_var {
                    if let Some(val) = lia_model.values.get(&tid) {
                        if val.is_zero() {
                            return true;
                        }
                    }
                }
            }
        }
        false
    }
}
