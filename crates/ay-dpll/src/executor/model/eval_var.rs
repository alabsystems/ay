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
        match self.evaluate_var_theory(model, term_id, sort) {
            EvalValue::Unknown => model
                .completed_values
                .get(&term_id)
                .cloned()
                .unwrap_or(EvalValue::Unknown),
            value => value,
        }
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
    /// - Uninterpreted: EUF term_values → Unknown
    /// - Datatype: constructor name resolution → Unknown
    fn evaluate_var_theory(&self, model: &Model, term_id: TermId, sort: &Sort) -> EvalValue {
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
                    return EvalValue::Rational(BigRational::from(val.clone()));
                }
            }
            // Fall back to LRA model (when using pure LRA solver for arithmetic)
            if let Some(ref lra_model) = model.lra_model {
                if let Some(val) = lra_model.values.get(&term_id) {
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
                    return EvalValue::Rational(BigRational::from(val.clone()));
                }
            }
            if has_arith_model {
                // If arithmetic theories and merged EUF values did not assign this term,
                // keep the result Unknown instead of inventing a value.
                return EvalValue::Unknown;
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
                return EvalValue::Algebraic(alg.clone());
            }
            // Real variable: check LRA model first
            if let Some(ref lra_model) = model.lra_model {
                if let Some(val) = lra_model.values.get(&term_id) {
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
                    return EvalValue::BitVec {
                        value: val.clone(),
                        width: bv.width,
                    };
                }
            }
            // A missing entry is not evidence that the variable is free: it
            // may have been eliminated by preprocessing and be defined by a
            // recorded substitution. Keep it Unknown so model completion can
            // either replay that definition or explicitly install the
            // canonical value for a genuinely free variable. This also covers
            // the no-BV-model AUFLIA route, whose uninterpreted treatment does
            // not provide BV-semantic values (#5356).
            EvalValue::Unknown
        } else if matches!(sort, Sort::FloatingPoint(..)) {
            // FloatingPoint variable: check FP model
            if let Some(ref fp_model) = model.fp_model {
                if let Some(val) = fp_model.values.get(&term_id) {
                    return EvalValue::Fp(val.clone());
                }
            }
            EvalValue::Unknown
        } else if matches!(sort, Sort::String) {
            // String variable: check String model.
            if let Some(ref string_model) = model.string_model {
                if let Some(value) = string_model.values.get(&term_id) {
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
                    let eval_elems: Vec<EvalValue> = elems
                        .iter()
                        .map(|s| {
                            self.parse_model_value_string(s, &Some(elem_sort.as_ref().clone()))
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
