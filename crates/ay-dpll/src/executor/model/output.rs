// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model output entry points: `get-model`, `get-value`, `get-objectives`.
//!
//! Formatting helpers (function tables, array values, eval-value rendering)
//! live in sibling `output_format.rs`.

use ay_core::term::TermData;
use ay_core::{quote_symbol, string_literal, Sort, TermId};

use crate::executor_format::{
    format_bigint, format_bitvec, format_default_value, format_model_atom, format_rational,
    format_real, format_sort,
};
use crate::executor_types::SolveResult;

use super::Executor;
use super::{debug_model, EvalValue, Model};

impl Executor {
    /// Generate objective output for get-objectives command.
    pub(crate) fn get_objectives(&self) -> String {
        // MaxSMT path: when the last solve came from `(assert-soft ...)`, the
        // soft-cost objective was materialized and popped inside a scope, so it
        // is no longer in `ctx.objectives()`. Report the minimized total
        // violated weight recorded by the MaxSMT solve.
        if self.ctx.objectives().is_empty() {
            if let Some(cost) = self.last_soft_cost {
                // `:approximate` marks a feasible-but-unproven bound
                // (resource-limited or weight-incomplete search); consumers
                // must not treat it as the optimum.
                if !self.last_soft_cost_optimal {
                    return format!("(objectives\n (__ay_soft_cost {cost} :approximate)\n)\n");
                }
                return format!("(objectives\n (__ay_soft_cost {cost})\n)\n");
            }
            // z3 parity: with no objectives and no soft cost, `(get-objectives)`
            // prints an empty objectives list (exit 0), even before any
            // `(check-sat)` — it does not error here.
            return "(objectives\n)\n".to_string();
        }

        // PARETO terminal-`unsat` path: Z3 keeps reporting the LAST emitted Pareto
        // point's objectives after the front is exhausted (the terminal
        // `(check-sat)` returns `unsat`, but `(get-objectives)` still shows the
        // last point). `finite_objective_values` was cleared by the unsat path, so we
        // render directly from the persisted `pareto_state.last_point`.
        if matches!(self.last_result, Some(SolveResult::Unsat(_))) {
            if let Some(state) = &self.pareto_state {
                if let Some(point) = &state.last_point {
                    let objs = self.ctx.objectives();
                    if objs.len() == point.len() {
                        let mut out = String::from("(objectives\n");
                        for (obj, val) in objs.iter().zip(point.iter()) {
                            let term_str = self.format_term(obj.term);
                            let value_str =
                                if matches!(self.ctx.terms.sort(obj.term), Sort::BitVec(_)) {
                                    val.numer().to_string()
                                } else {
                                    self.format_objective_rational(val, obj.term)
                                };
                            out.push_str(&format!(" ({term_str} {value_str})\n"));
                        }
                        out.push_str(")\n");
                        return out;
                    }
                }
            }
        }

        if !matches!(self.last_result, Some(SolveResult::Sat)) {
            return "(error \"objectives are not available\")".to_string();
        }

        let mut out = String::from("(objectives\n");
        for (objective_index, obj) in self.ctx.objectives().iter().enumerate() {
            if self.unavailable_objectives.contains(&objective_index) {
                // A lex predecessor with no attainable optimum — unbounded
                // (`oo`) or unattained (infinitesimal, #opt-epsilon) — leaves
                // no scalar to optimize under. z3 prints an interval for the
                // predecessor and a demonstrably FALSE scalar for the suffix
                // (measured 4.15.4: `(y (- 1))` where max y = 5); AY refuses
                // to fabricate one. Documented deviation.
                return format!(
                    "(error \"objective {objective_index} is unavailable after a lexicographic predecessor with no attainable optimum\")"
                );
            }
            let term_str = self.format_term(obj.term);
            // An objective with no finite optimum is reported as infinity per
            // SMT-LIB OMT conventions (matches z3): `oo` for an unbounded
            // maximize, `(- oo)` for an unbounded minimize. Reporting the
            // arbitrary finite value from the iterative fallback would be wrong.
            let value_str = match self.unbounded_objectives.get(&objective_index) {
                Some(ay_frontend::ObjectiveDirection::Maximize) => "oo".to_string(),
                Some(ay_frontend::ObjectiveDirection::Minimize) => "(* (- 1) oo)".to_string(),
                None => {
                    // A BitVector objective is reported by Z3 as a DECIMAL
                    // numeral in `(get-objectives)` (e.g. `(x 7)`), NOT the
                    // `#x7` bitvector literal that `format_eval_value` would emit
                    // (the bitvector literal is only used by `(get-value)`). The
                    // optimum is the unsigned value, stored as a whole rational,
                    // so we render its numerator (the integer) directly.
                    let is_bv = matches!(self.ctx.terms.sort(obj.term), Sort::BitVec(_));
                    if let Some((value, eps_coeff)) =
                        self.infinitesimal_objectives.get(&objective_index)
                    {
                        // Unattained optimum (#opt-epsilon): render the z3
                        // epsilon grammar. Checked BEFORE the finite map,
                        // matching `objective_optimum`'s resolution order.
                        self.format_epsilon_objective(value, eps_coeff, obj.term)
                    } else if let Some(recorded) =
                        self.finite_objective_values.get(&objective_index)
                    {
                        // Every finite outcome is explicitly recorded only after
                        // an optimizing query is admitted. Lex/Pareto values are
                        // bound to the final model; BOX values are independently
                        // authenticated and intentionally model-free.
                        if is_bv {
                            recorded.numer().to_string()
                        } else {
                            self.format_objective_rational(recorded, obj.term)
                        }
                    } else {
                        return format!(
                            "(error \"objective {objective_index} has no admitted optimization outcome\")"
                        );
                    }
                }
            };
            out.push_str(&format!(" ({term_str} {value_str})\n"));
        }
        out.push_str(")\n");
        out
    }

    /// Format a recorded BOX objective optimum (a `BigRational`) exactly as
    /// the lex path formats an objective value: sort-aware at the stdout
    /// boundary (#real-fmt) — a Real objective prints `2.0` / `(/ 7.0 2.0)`,
    /// an Int one a bare integer. Routed through
    /// [`Self::try_format_eval_value_user`] so box and lex objective output
    /// (and the certificate `bound`/`entails` strings) use one shared
    /// formatter (no divergence).
    fn format_objective_rational(
        &self,
        value: &num_rational::BigRational,
        term_id: TermId,
    ) -> String {
        self.try_format_eval_value_user(&EvalValue::Rational(value.clone()), term_id)
            .expect("a rational value always formats")
    }

    /// Render an UNATTAINED Real optimum `value + eps_coeff·ε` in z3 4.15.4's
    /// exact `(get-objectives)` epsilon grammar (#opt-epsilon, all shapes
    /// measured and pinned byte-exact in the opt-epsilon battery):
    ///
    /// * minimize (k > 0): k=1 elides the coefficient (`(+ (/ 3.0 2.0)
    ///   epsilon)`; v=0 → bare `epsilon`); k≠1 → `(* 2.0 epsilon)` /
    ///   `(+ v (* k epsilon))`.
    /// * maximize (k < 0): the coefficient is never elided:
    ///   `(* (- 1.0) epsilon)`; v≠0 → `(+ v (* (- |k|) epsilon))`.
    ///
    /// `eps_coeff` is nonzero by construction (a zero ε-part is exactly an
    /// attained `Optimal` and never lands in `infinitesimal_objectives`).
    fn format_epsilon_objective(
        &self,
        value: &num_rational::BigRational,
        eps_coeff: &num_rational::BigRational,
        term_id: TermId,
    ) -> String {
        use num_traits::{One, Signed, Zero};
        let value_str = self.format_objective_rational(value, term_id);
        if eps_coeff.is_positive() {
            if eps_coeff.is_one() {
                if value.is_zero() {
                    "epsilon".to_string()
                } else {
                    format!("(+ {value_str} epsilon)")
                }
            } else {
                let k_str = self.format_objective_rational(eps_coeff, term_id);
                if value.is_zero() {
                    format!("(* {k_str} epsilon)")
                } else {
                    format!("(+ {value_str} (* {k_str} epsilon))")
                }
            }
        } else {
            let k_abs = -eps_coeff.clone();
            let k_str = self.format_objective_rational(&k_abs, term_id);
            let inner = format!("(* (- {k_str}) epsilon)");
            if value.is_zero() {
                inner
            } else {
                format!("(+ {value_str} {inner})")
            }
        }
    }

    /// Generate output for the `(get-objective-certificates)` command
    /// (#lra-opt-cert, AY extension).
    ///
    /// For each objective whose last optimizing `(check-sat)` produced a dual
    /// (Farkas) optimality certificate, prints
    ///
    /// ```text
    /// (objective-certificates
    ///  ((objective <term>)
    ///   (sense minimize|maximize)
    ///   (bound <value>)
    ///   (entails (>=|<= <term> <value>))
    ///   (strict true|false)
    ///   (farkas
    ///    (<coeff> <literal>)
    ///    ...))
    /// )
    /// ```
    ///
    /// where each `<literal>` is the asserted atom (wrapped in `(not ...)`
    /// when it was asserted false) and `<coeff>` its positive Farkas
    /// multiplier: summing `coeff * literal` (each literal oriented as a
    /// `>= 0` fact) yields exactly the `entails` inequality, checkable without
    /// trusting AY.
    pub(crate) fn get_objective_certificates(&self) -> String {
        if self.ctx.objectives().is_empty() {
            return "(error \"no objectives\")".to_string();
        }
        let mut certified = 0usize;
        let mut out = String::from("(objective-certificates\n");
        for (objective_index, obj) in self.ctx.objectives().iter().enumerate() {
            let Some(cert) = self.objective_certificates.get(&objective_index) else {
                continue;
            };
            certified += 1;
            let term_str = self.format_term(obj.term);
            // Same formatter as `(get-objectives)` so the two never diverge.
            let bound_str = self.format_objective_rational(&cert.bound, obj.term);
            let (sense_str, rel) = match cert.sense {
                ay_lra::OptimizationSense::Minimize => ("minimize", ">="),
                ay_lra::OptimizationSense::Maximize => ("maximize", "<="),
            };
            out.push_str(&format!(
                " ((objective {term_str})\n  (sense {sense_str})\n  (bound {bound_str})\n  (entails ({rel} {term_str} {bound_str}))\n  (strict {strict})\n  (farkas\n",
                strict = cert.strict
            ));
            for atom in &cert.atoms {
                let atom_str = self.format_term(atom.atom);
                let literal_str = if atom.value {
                    atom_str
                } else {
                    format!("(not {atom_str})")
                };
                out.push_str(&format!(
                    "   ({} {literal_str})\n",
                    format_rational(&atom.coeff)
                ));
            }
            out.push_str("  ))\n");
        }
        out.push_str(")\n");
        if certified == 0 {
            return "(error \"no objective certificates available\")".to_string();
        }
        out
    }

    /// Generate model output for get-model command.
    pub(crate) fn model(&self) -> String {
        if !self.produce_models_enabled() {
            return "(error \"model generation is not enabled\")".to_string();
        }

        // Check if we have a model.  Some SAT paths have no concrete theory
        // model because assertions were simplified away; every declared
        // constant is then unconstrained, so print the completed default
        // model (the values exist in a model, nothing is fabricated at print
        // time — #no-fabricated-model-values).
        let dummy_model;
        let model = match (&self.last_result, &self.last_model) {
            (Some(SolveResult::Sat), Some(m)) => m,
            (Some(SolveResult::Sat), None) => {
                dummy_model = self.completed_default_model();
                &dummy_model
            }
            _ => {
                return "(error \"model is not available\")".to_string();
            }
        };

        // Collect model values for user-declared symbols.
        //
        // Datatype SELECTOR totalizations come first (#mv-total-selectors):
        // without them a model validator evaluating a selector applied to a
        // wrong-constructor value rejects the whole model as partial. Each
        // definition defers to the builtin selector on the owning constructor
        // and reproduces the internal model's committed value on every
        // constrained wrong-constructor case.
        let mut definitions = self.total_selector_definitions(model);

        // Entailed reconstruction of datatype/array-sorted constants, shared with
        // the independent gate (`gate_emit_reconstructions`): the printer's own
        // per-leaf materialization can leave a datatype field leaf `Unknown` (an
        // unavailable marker) or pick per-leaf values that are mutually
        // incoherent, so the emitted model does not re-check. Where the gate's
        // entailed-alias resolution yields a concrete, marker-free value, prefer
        // it — that is the model the gate confirmed, so it round-trips. A leaf
        // the gate leaves unresolved is simply absent here and falls through to
        // the existing renderer (fail-closed, no fabrication).
        let gate_emit = self.gate_emit_reconstructions(model);

        for (name, info) in self.ctx.symbol_iter() {
            // Skip DT-internal symbols (constructors, testers, selectors) (#5412).
            if self.is_dt_internal_symbol(name) {
                continue;
            }

            // #quantprod-g3: a DECLARED function adopted as a definitional
            // macro (`(assert (forall X. (= (f X) body)))` recognized as a
            // pure definition) still needs a model entry — z3 prints one —
            // and its interpretation IS the definition, satisfying the
            // definitional assertion by reflexivity. Emit it before the
            // defined-symbol skip below (adoption puts it in `fun_defs`).
            if let Some((params, body)) = self.ctx.adopted_macro_interp(name) {
                let params_str = params
                    .iter()
                    .map(|(n, s)| format!("({} {})", quote_symbol(n), format_sort(s)))
                    .collect::<Vec<_>>()
                    .join(" ");
                let body = *body;
                definitions.push(format!(
                    "  (define-fun {} ({}) {}\n    {})",
                    quote_symbol(name),
                    params_str,
                    format_sort(&info.sort),
                    self.format_term(body)
                ));
                continue;
            }

            // Skip problem-DEFINED symbols (define-fun/-rec): their
            // interpretation is fixed by the problem text. Re-emitting one is a
            // definition conflict for a model validator, and the solver has no
            // model entry keyed by the name anyway (defined applications are
            // macro-expanded at elaboration) — any table found here could only
            // be a completion default, i.e. a WRONG body (#mv-defined-fun-emit).
            if self.ctx.is_defined_fun(name) {
                continue;
            }

            // Skip SOLVER-INTERNAL symbol registrations (fresh single-ctor
            // elimination field constants): not user-declared, so a validator
            // treats their definitions as garbage — the pinned 2025 Dolmen
            // silently stops reading the model at the first one, orphaning
            // every later user symbol (#mv-internal-symbol-suppression). The
            // flag is cleared on user (re)declaration, so no user-DECLARED
            // symbol is ever suppressed.
            if self.ctx.is_internal_symbol(name) {
                continue;
            }

            // Handle functions with arguments (generate function tables).
            if !info.arg_sorts.is_empty() {
                // Check if we have EUF model with function tables.
                if let Some(ref euf_model) = model.euf_model {
                    let identity = self.ctx.symbol_identity_name(name, info);
                    if let Some(table) = euf_model.function_tables.get(identity) {
                        // Resolve @?N placeholders in function table values (#5452).
                        // The EUF model builds tables before theory values are merged,
                        // so Int/Real/BV-returning functions have @?N placeholders
                        // instead of concrete values. Resolve them now using the
                        // full model which has all theory values available.
                        let resolved = self.resolve_function_table(model, table);
                        // Single-source datatype branch keys/values (stage-4
                        // review F3, #mv-dt-single-source): a table over
                        // selector-bearing datatype sorts must key its branches
                        // on the SAME rendered values the constants print —
                        // abstract-element keys (`(as @N!k N)`) can never match
                        // the printed constants under a validator, sending every
                        // application to the default arm (E:bad-model, voiding).
                        // Fail-closed: an unmappable table OMITS the definition
                        // (partial, non-voiding) rather than print an
                        // unfaithful one.
                        let resolved = match self.dt_egraph_rewrite_uf_table(
                            model,
                            &info.arg_sorts,
                            &info.sort,
                            &resolved,
                        ) {
                            super::dt_egraph_values::DtUfTableRewrite::NotApplicable => resolved,
                            super::dt_egraph_values::DtUfTableRewrite::Rewritten(t) => t,
                            super::dt_egraph_values::DtUfTableRewrite::Drop => continue,
                        };
                        match self.format_function_table(
                            name,
                            &info.arg_sorts,
                            &info.sort,
                            &resolved,
                            model,
                        ) {
                            Ok(def) => definitions.push(def),
                            // A table value with no model value cannot be
                            // printed honestly — surface the gap as an error
                            // instead of a fabricated default
                            // (#no-fabricated-model-values).
                            Err(e) => {
                                return format!(
                                    "(error \"model value for function {} is not available: {e}\")",
                                    quote_symbol(name)
                                )
                            }
                        }
                    }
                }
                continue;
            }

            // For constants (no arguments), need term_id.
            if let Some(term_id) = info.term {
                // For constants (no arguments), look up value.
                let sort_str = format_sort(&info.sort);

                // Handle array-sorted symbols specially. Render a `store`-chain
                // that satisfies the asserted `(select a i) = v` constraints
                // (folding in reconstructed interpretation stores and the
                // definitional `(= a <array-expr>)` value, #5450) rather than the
                // bare const-array default, which would VIOLATE the assertions —
                // an invalid witness (#model-array-witness).
                if let Sort::Array(_) = &info.sort {
                    let array_value = if let Some(value) = gate_emit.get(&term_id) {
                        value.clone()
                    } else if let Some(value) =
                        self.format_array_witness_value(model, term_id, &info.sort)
                    {
                        value
                    } else {
                        return format!(
                            "(error \"model value for array {} is not available\")",
                            quote_symbol(name)
                        );
                    };
                    definitions.push(format!(
                        "  (define-fun {} () {}\n    {})",
                        quote_symbol(name),
                        sort_str,
                        array_value
                    ));
                    continue;
                }

                let quoted_name = quote_symbol(name);

                // Single-source DT value (#mv-dt-single-source): when the DT
                // lane exported its e-graph model, a datatype-sorted constant
                // reads the ONE per-class assignment shared with the total
                // selector definitions and `(get-value)` — printing any other
                // engine's value here (gate reconstruction included) could
                // disagree with a totalization branch key derived from the
                // assignment and un-fire it under Dolmen. Falls through when
                // absent (combined lanes) or the class fails closed.
                if self.datatype_sort_name(&info.sort).is_some() {
                    if let Some(v) = self.dt_egraph_value(model, term_id) {
                        definitions.push(format!("  (define-fun {quoted_name} () {sort_str} {v})"));
                        continue;
                    }
                    // Fail-closed omission (stage-4 review F2): a class the
                    // assignment POISONED (self-check failure / unrepairable
                    // collision) must NOT fall back to any legacy emitter —
                    // the legacy strategies re-derive the same incoherent
                    // value the check already proved wrong
                    // (`c8-tester-distinct`: byte-identical `distinct`-violating
                    // collision → E:bad-model, division-voiding). Omitting the
                    // definition is at worst a partial model (0 points to a
                    // validator), never a wrong one.
                    if self.dt_egraph_class_poisoned(model, term_id) {
                        continue;
                    }
                }

                // Entailed gate reconstruction wins for a datatype-sorted const
                // (coherent with the confirmed model, marker-free); otherwise fall
                // through to the per-leaf DT materializer below.
                if let Some(ctor_expr) = gate_emit.get(&term_id) {
                    definitions.push(format!(
                        "  (define-fun {quoted_name} () {sort_str} {ctor_expr})"
                    ));
                    continue;
                }

                // For DT-sorted variables, resolve to constructor expression (#5412).
                if let Sort::Uninterpreted(sort_name) = &info.sort {
                    if let Some(ctor_expr) = self.resolve_dt_value(sort_name, term_id, model) {
                        definitions.push(format!(
                            "  (define-fun {quoted_name} () {sort_str} {ctor_expr})"
                        ));
                        continue;
                    }
                }

                // Try EUF model first for uninterpreted sorts. This deliberately
                // EXCLUDES Int/Real: `evaluate_var` (the value the validation gate
                // checks) resolves an arithmetic variable LIA/LRA-FIRST and only
                // falls back to the merged EUF `term_values` on a miss. Reading
                // EUF first here inverted that order, so when a combined AUFLIA
                // solve committed one value to the arithmetic model (e.g. a
                // completion default `i2 = 0`) and left a STALE value in the merged
                // EUF map (`i2 = -2`), `(get-model)` printed the EUF value while
                // the gate validated the LIA value — the emitted witness then
                // falsified the formula (seed 21453, #array-completion-order). Int/
                // Real fall through to the LIA/LRA branches and the `evaluate_term`
                // renderer below, which share `evaluate_var`'s canonical order, so
                // emit stays faithful to what the gate checked.
                if !matches!(info.sort, Sort::Int | Sort::Real) {
                    if let Some(ref euf_model) = model.euf_model {
                        if let Some(elem) = euf_model.term_values.get(&term_id) {
                            let elem = format_model_atom(&info.sort, elem);
                            definitions
                                .push(format!("  (define-fun {quoted_name} () {sort_str} {elem})"));
                            continue;
                        }
                    }
                }

                // Try LRA model for Real sort — but an exact NRA algebraic
                // witness (e.g. x = √2 for `x*x = 2`) is authoritative and
                // prints in z3 `root-obj` syntax.
                if matches!(info.sort, Sort::Real) {
                    if let Some(alg) = self.nra_algebraic_model.get(&term_id) {
                        // A residue value can reduce to an exact rational (a
                        // triangular-assignment variable): print it as such.
                        let value_str = match alg.to_number() {
                            Some(ay_nra::RealScalar::Rational(r)) => format_real(&r),
                            Some(ay_nra::RealScalar::Algebraic(n)) => n.alpha().to_smtlib(),
                            None => alg
                                .to_smtlib()
                                .unwrap_or_else(|| "(root-obj unrepresentable)".to_string()),
                        };
                        definitions.push(format!(
                            "  (define-fun {quoted_name} () {sort_str} {value_str})"
                        ));
                        continue;
                    }
                    if let Some(ref lra_model) = model.lra_model {
                        if let Some(val) = lra_model.values.get(&term_id) {
                            // Use the actual value without minimization.
                            let value_str = format_real(val);
                            definitions.push(format!(
                                "  (define-fun {quoted_name} () {sort_str} {value_str})"
                            ));
                            continue;
                        }
                    }
                }

                // Try LIA model for Int sort.
                if matches!(info.sort, Sort::Int) {
                    let debug = debug_model();
                    if debug {
                        safe_eprintln!(
                            "[MODEL] Looking up Int symbol '{}' term_id={}, lia_model={}",
                            name,
                            term_id.0,
                            model.lia_model.is_some()
                        );
                        if let Some(ref lm) = model.lia_model {
                            safe_eprintln!(
                                "[MODEL]   LIA model keys: {:?}",
                                lm.values.keys().map(|k| k.0).collect::<Vec<_>>()
                            );
                        }
                    }
                    if let Some(ref lia_model) = model.lia_model {
                        if let Some(val) = lia_model.values.get(&term_id) {
                            if debug {
                                safe_eprintln!(
                                    "[MODEL]   Found value {} for term_id={}",
                                    val,
                                    term_id.0
                                );
                            }
                            // Only apply minimization if counterexample minimization is enabled
                            // and bounds are available. Otherwise use the actual value.
                            let value_str = format_bigint(val);
                            definitions.push(format!(
                                "  (define-fun {quoted_name} () {sort_str} {value_str})"
                            ));
                            continue;
                        } else if debug {
                            safe_eprintln!(
                                "[MODEL]   NOT found in LIA model for term_id={}",
                                term_id.0
                            );
                        }
                    }
                    // Also check LRA model for Int (when using pure LRA solver for arithmetic).
                    if let Some(ref lra_model) = model.lra_model {
                        if let Some(val) = lra_model.values.get(&term_id) {
                            // Convert rational to integer if it's a whole number.
                            if val.is_integer() {
                                // Use the actual value without minimization.
                                let value_str = format_bigint(val.numer());
                                definitions.push(format!(
                                    "  (define-fun {quoted_name} () {sort_str} {value_str})"
                                ));
                                continue;
                            }
                        }
                    }
                }

                // Try BV model for BitVec sort.
                if let Sort::BitVec(bv) = &info.sort {
                    if let Some(ref bv_model) = model.bv_model {
                        if let Some(val) = bv_model.values.get(&term_id) {
                            let hex_str = format_bitvec(val, bv.width);
                            definitions.push(format!(
                                "  (define-fun {quoted_name} () {sort_str} {hex_str})"
                            ));
                            continue;
                        }
                    }
                }

                // Try String model for String sort.
                if matches!(info.sort, Sort::String) {
                    if let Some(ref string_model) = model.string_model {
                        if let Some(val) = string_model.values.get(&term_id) {
                            let value_str = string_literal(val);
                            definitions.push(format!(
                                "  (define-fun {quoted_name} () {sort_str} {value_str})"
                            ));
                            continue;
                        }
                    }
                }

                // Try FP model for FloatingPoint sort.
                if matches!(info.sort, Sort::FloatingPoint(..)) {
                    if let Some(ref fp_model) = model.fp_model {
                        if let Some(val) = fp_model.values.get(&term_id) {
                            let value_str = val.to_smtlib();
                            definitions.push(format!(
                                "  (define-fun {quoted_name} () {sort_str} {value_str})"
                            ));
                            continue;
                        }
                    }
                }

                // Seq-sorted variables: render the witness through the SAME
                // per-term core `(get-value)` uses (`term_value_string`), so
                // `(get-model)` and `(get-value)` can never diverge
                // (#model-seq-witness). That path consults the seq theory model
                // first (via `evaluate_term`), then — on a miss — resolves the
                // var through its asserted `(= s (seq.++ ...))` equality and the
                // len/nth reconstruction, emitting a binary `seq.++` tree. The
                // previous code rendered only the direct seq-theory entry and
                // fell through to the bare `(as seq.empty ...)` default whenever
                // that entry was absent (e.g. the value lived only in an asserted
                // concat), printing an INVALID witness that contradicted the
                // assertions.
                if matches!(info.sort, Sort::Seq(..)) {
                    match self.term_value_string(model, term_id) {
                        Ok(value_str) => {
                            definitions.push(format!(
                                "  (define-fun {quoted_name} () {sort_str} {value_str})"
                            ));
                        }
                        Err(e) => {
                            return format!(
                                "(error \"model value for {quoted_name} is not available: {e}\")"
                            )
                        }
                    }
                    continue;
                }

                // Check bool_overrides for Bool variables recovered from
                // preprocessor substitutions or completed at finalize time
                // (#5512, #5524, model/completion.rs). Without this, a
                // variable whose value lives only in `bool_overrides` would
                // print as the SAT-model default (false) and contradict the
                // validated model. Solver-assigned SAT values still win: the
                // overrides are only consulted when the SAT model has no
                // entry, mirroring the `eval_var` lookup chain.
                if info.sort == Sort::Bool
                    && self
                        .term_value(&model.sat_model, &model.term_to_var, term_id)
                        .is_none()
                {
                    if let Some(&b) = model.bool_overrides.get(&term_id) {
                        let value_str = if b { "true" } else { "false" };
                        definitions.push(format!(
                            "  (define-fun {quoted_name} () {sort_str} {value_str})"
                        ));
                        continue;
                    }
                    if let Some(ref bv_model) = model.bv_model {
                        if let Some(&b) = bv_model.bool_overrides.get(&term_id) {
                            let value_str = if b { "true" } else { "false" };
                            definitions.push(format!(
                                "  (define-fun {quoted_name} () {sort_str} {value_str})"
                            ));
                            continue;
                        }
                    }
                }

                // For Int/Real variables with NO committed model value, resolve
                // from committed assertion equalities (e.g. `(= v (select a i))`)
                // and inequality bounds before defaulting to 0. This keeps
                // get-model consistent with the asserted equalities in pure
                // QF_(A)LIA where preprocessing eliminated the defining
                // equality and no arithmetic model was produced (#5450).
                //
                // GATE FAITHFULNESS (#array-completion-order, scalar variant):
                // run this re-derivation ONLY when the model commits no value for
                // the variable (`evaluate_term` is Unknown). When the model DOES
                // commit a value, that is the value the validation gates checked;
                // a print-time re-derivation from the assertions can DISAGREE with
                // it (a bound / equality the solver satisfied through a different
                // read), so printing the re-derived value would emit a witness the
                // gate never validated — the class caught by seed-21453, where the
                // gate confirmed `i2 = 0` (its committed value) while this path
                // re-derived `i2 = 2`, shipping an `(= 0 i2)` the emitted model
                // falsifies. The committed value falls through to the
                // `evaluate_term` renderer below, keeping emit faithful to the gate.
                if matches!(info.sort, Sort::Int | Sort::Real)
                    && matches!(self.evaluate_term(model, term_id), EvalValue::Unknown)
                {
                    let mut resolved = self.extract_value_from_asserted_equalities(model, term_id);
                    if resolved.is_none() {
                        resolved = match info.sort {
                            Sort::Int => self
                                .extract_int_from_assertion_bounds(term_id)
                                .map(|v| EvalValue::Rational(num_rational::BigRational::from(v))),
                            Sort::Real => self
                                .extract_real_from_assertion_bounds(term_id)
                                .map(EvalValue::Rational),
                            _ => None,
                        };
                    }
                    if let Some(value) = resolved {
                        if !matches!(value, EvalValue::Unknown) {
                            let value_str = match self.try_format_eval_value_user(&value, term_id)
                            {
                                Ok(s) => s,
                                Err(e) => {
                                    return format!(
                                        "(error \"model value for {quoted_name} is not available: {e}\")"
                                    )
                                }
                            };
                            definitions.push(format!(
                                "  (define-fun {quoted_name} () {sort_str} {value_str})"
                            ));
                            continue;
                        }
                    }
                }

                // Fall back to the SAT model for Bool, then to the full
                // evaluation chain (theory models + the completion slot filled
                // before validation). Every value printed here EXISTS in the
                // model the validation gate saw; if none exists, that is an
                // internal invariant violation (the model was accepted without
                // a total assignment) and it surfaces as an explicit error —
                // never as a fabricated sort default
                // (#no-fabricated-model-values).
                if matches!(info.sort, Sort::Bool) {
                    if let Some(b) = self.term_value(&model.sat_model, &model.term_to_var, term_id)
                    {
                        let value_str = if b { "true" } else { "false" };
                        definitions.push(format!(
                            "  (define-fun {quoted_name} () {sort_str} {value_str})"
                        ));
                        continue;
                    }
                }
                let eval_value = self.evaluate_term(model, term_id);
                let value_str = match &eval_value {
                    // Unknown keeps its specific invariant-violation message
                    // (ordered BEFORE the user-facing delegation so the
                    // "sat accepted without a total model" diagnostic text is
                    // preserved).
                    EvalValue::Unknown => {
                        return format!(
                            "(error \"model value for {quoted_name} is not available \
                             (internal error: sat accepted without a total model)\")"
                        );
                    }
                    // Sort-aware user-facing formatting (#real-fmt): Real
                    // constants print as z3-exact Real literals (`0.0`,
                    // `(- 5.0)`, `(/ 7.0 2.0)`), everything else exactly as
                    // before.
                    _ => match self.try_format_eval_value_user(&eval_value, term_id) {
                        Ok(s) => s,
                        Err(e) => {
                            return format!(
                                "(error \"model value for {quoted_name} is not available: {e}\")"
                            )
                        }
                    },
                };
                definitions.push(format!(
                    "  (define-fun {quoted_name} () {sort_str} {value_str})"
                ));
            }
        }

        // Uninterpreted-sort universe elements (`@Sort!n`) are emitted ONLY as
        // sort-ascribed abstract values `(as @Sort!n Sort)` at their use sites
        // — never with `(declare-fun @Sort!n () Sort)` headers. The SMT-LIB
        // get-model response grammar (and Dolmen, the SMT-COMP Model-Validation
        // validator: `SAT OPEN MODEL? definition* CLOSE`) admits nothing but
        // define-fun forms inside the response, so a declare-fun header makes
        // the whole model unparseable (E:parsing-error — the QF_UFDT
        // stream_processor ModelParsingError class). Self-containment is
        // carried by the standard instead: an `@`-prefixed symbol is an
        // abstract value (SMT-LIB 2.7), a distinguished fresh constant of the
        // ascribed sort that needs no declaration — Dolmen accepts and
        // evaluates these natively (and rejects attempts to re-define them
        // with E:id-def-conflict). This is the same declaration-free form
        // cvc5 emits for uninterpreted-sort models.
        if definitions.is_empty() {
            "(model\n)".to_string()
        } else {
            format!("(model\n{}\n)", definitions.join("\n"))
        }
    }

    /// Resolve the model to evaluate query terms against, mirroring the
    /// dummy-model fallback used for trivially-SAT cases (#8743).
    ///
    /// Returns the active `Model` on success, or an SMT-LIB `(error ...)`
    /// string when no model is available. The `dummy` slot is borrowed by the
    /// caller to own a synthesized empty model for the trivially-SAT path.
    fn value_query_model<'m>(&'m self, dummy: &'m mut Option<Model>) -> Result<&'m Model, String> {
        if !self.produce_models_enabled() {
            return Err("(error \"model generation is not enabled\")".to_string());
        }
        match (&self.last_result, &self.last_model) {
            (Some(SolveResult::Sat), Some(m)) => Ok(m),
            (Some(SolveResult::Sat), None) => {
                // Trivially-SAT: every declared constant is unconstrained, so
                // queries evaluate against the completed default model
                // (#no-fabricated-model-values).
                *dummy = Some(self.completed_default_model());
                Ok(dummy.as_ref().expect("dummy model just assigned"))
            }
            _ => Err("(error \"model is not available\")".to_string()),
        }
    }

    /// Compute the printed value of a single term against `model`.
    ///
    /// This is the per-term core shared by `(get-value ...)` and `(eval ...)`.
    /// It performs array/datatype/uninterpreted resolution and the Unknown
    /// fallbacks (asserted-equality and inequality-bound extraction) exactly as
    /// `get-value` does, returning just the value text (no `(term value)`
    /// wrapper).
    ///
    /// `Err` when the term has NO value under the model: the former behavior
    /// printed a fabricated sort default (a lie — e.g. `(get-value ((f 1)))`
    /// answered `0` while the printed `(define-fun f ...)` said `5`); callers
    /// surface the error at the command level (#no-fabricated-model-values).
    pub(in crate::executor) fn term_value_string(
        &self,
        model: &Model,
        term_id: TermId,
    ) -> Result<String, String> {
        let sort = self.ctx.terms.sort(term_id);
        if matches!(sort, Sort::Array(_)) {
            // Render a `store`-chain that satisfies the asserted
            // `(select term i) = v` constraints, mirroring `(get-model)`
            // (#model-array-witness).
            self.format_array_witness_value(model, term_id, sort)
                .ok_or_else(|| "array model value is incomplete".to_string())
        } else if let Some(witness) = self.array_witness_scalar_select(model, term_id) {
            // A scalar `(select b i)` read on a store-equality-dependent array
            // must agree with the `store`-chain `(get-model)` prints for `b` (the
            // raw evaluator can return a stale don't-care that the printed witness
            // overrides via the store axiom, #model-array-witness).
            Ok(witness)
        } else if let Sort::Uninterpreted(sort_name) = sort {
            // DT-sorted terms: resolve to constructor expression (#5412).
            match self.resolve_dt_value(sort_name, term_id, model) {
                Some(ctor_expr) => Ok(ctor_expr),
                None => {
                    let eval_value = self.evaluate_term(model, term_id);
                    self.try_format_eval_value_user(&eval_value, term_id)
                }
            }
        } else {
            let eval_value = self.evaluate_term(model, term_id);
            // For selector apps returning Unknown, scan assertions (#5432).
            let eval_value = if matches!(eval_value, EvalValue::Unknown) {
                self.extract_value_from_asserted_equalities(model, term_id)
                    .unwrap_or(eval_value)
            } else {
                eval_value
            };
            // For Real/Int-sorted terms still Unknown after equality scan,
            // try bound extraction from inequality assertions (#5506).
            let eval_value = if matches!(eval_value, EvalValue::Unknown) {
                match sort {
                    Sort::Real => self
                        .extract_real_from_assertion_bounds(term_id)
                        .map(EvalValue::Rational)
                        .unwrap_or(eval_value),
                    Sort::Int => self
                        .extract_int_from_assertion_bounds(term_id)
                        .map(|v| EvalValue::Rational(num_rational::BigRational::from(v)))
                        .unwrap_or(eval_value),
                    _ => eval_value,
                }
            } else {
                eval_value
            };
            // For a Seq-sorted term with no direct theory value or defining
            // `(= s ...)` equality, reconstruct the witness from its
            // `(seq.len s) = N` / `(seq.nth s i) = v` constraints (#model-seq-witness).
            // Without this, the bare `(as seq.empty ...)` default (length 0)
            // VIOLATES a `(seq.len s) = N>0` constraint and re-feeds to unsat.
            let eval_value =
                if matches!(eval_value, EvalValue::Unknown) && matches!(sort, Sort::Seq(_)) {
                    self.reconstruct_seq_from_len_nth(model, term_id)
                        .unwrap_or(eval_value)
                } else {
                    eval_value
                };
            // A UF application at an argument point the function table does
            // not list reads back the printed define-fun's ELSE branch, so
            // (get-value) never contradicts (get-model).
            if matches!(eval_value, EvalValue::Unknown) {
                if let Some(else_value) = self.uf_unlisted_point_value(model, term_id) {
                    return else_value;
                }
            }
            self.try_format_eval_value_user(&eval_value, term_id)
        }
    }

    /// Model-completion read of a UF application at an argument tuple its
    /// function table does not list.
    ///
    /// The printed `(define-fun f ...)` is TOTAL: its else branch is the last
    /// resolved table entry (see `format_function_table`), or the canonical
    /// default body for an empty table. `(get-value ((f <unlisted args>)))`
    /// must therefore answer exactly that else value — the former sort-default
    /// fabrication contradicted the printed model
    /// (#no-fabricated-model-values). `None` when the term is not a UF
    /// application with a table, or when an argument itself has no model value
    /// (the read is then genuinely unavailable and the caller errors).
    fn uf_unlisted_point_value(
        &self,
        model: &Model,
        term_id: TermId,
    ) -> Option<Result<String, String>> {
        let TermData::App(sym, args) = self.ctx.terms.get(term_id) else {
            return None;
        };
        if args.is_empty() {
            return None;
        }
        let euf_model = model.euf_model.as_ref()?;
        let table = euf_model.function_tables.get(sym.name())?;
        // Every argument must itself have a concrete model value; otherwise
        // no specific point is being read and no table row can be excluded.
        for &arg in args {
            if matches!(self.evaluate_term(model, arg), EvalValue::Unknown) {
                return None;
            }
        }
        let result_sort = self.ctx.terms.sort(term_id);
        let resolved = self.resolve_function_table(model, table);
        Some(match resolved.last() {
            // Same else value `format_function_table` prints.
            Some((_, else_value)) => self.resolve_table_value(else_value, result_sort, model),
            // Empty table: the same unconstrained-function body `(get-model)`
            // prints.
            None => Ok(format_default_value(result_sort)),
        })
    }

    /// Generate output for get-value command.
    pub(crate) fn values(&self, requested: &[(String, TermId)]) -> String {
        // Check if we have a model.
        //
        // For trivially-SAT cases where `last_model` is `None` (e.g., all
        // assertions simplified away during preprocessing), we still need
        // to evaluate `(select (store ...) i)` terms against the term DAG
        // via `evaluate_term`/`evaluate_select`. Mirror the dummy-model
        // pattern used by `get_objectives` so that store-chain resolution
        // and `const-array` evaluation still work (#8743).
        let mut dummy = None;
        let model = match self.value_query_model(&mut dummy) {
            Ok(m) => m,
            Err(e) => return e,
        };

        // Memoize evaluation across ALL requested terms (#eval-memo). `get-value`
        // over N terms that share large subterms — e.g. a Kani query's ~190
        // violation flags, each a boolean expression reading the same 20M-node
        // model — otherwise re-evaluates every shared subterm once PER term (the
        // result memo is inert outside a session). One session computes each
        // unique subterm exactly once. Verdict-preserving (the model is immutable
        // for the query); dropped at function exit.
        let _eval_memo = super::EvalMemoSession::new();
        let _t_gv = std::time::Instant::now();

        // Echo the term's ORIGINAL SMT-LIB text as the key (per the SMT-LIB
        // spec), not a reconstruction of the elaborated term — a
        // single-constructor datatype constant `w` is eagerly eliminated to
        // `(wrap <field>)`, whose fresh field var must not leak into the key.
        let mut pairs: Vec<String> = Vec::with_capacity(requested.len());
        for (term_str, term_id) in requested {
            match self.term_value_string(model, *term_id) {
                Ok(value_str) => pairs.push(format!("({term_str} {value_str})")),
                // A term with no value under the model errors honestly —
                // never a fabricated default (#no-fabricated-model-values).
                Err(e) => return format!("(error \"value of {term_str} is not available: {e}\")"),
            }
        }

        if std::env::var_os("AY_PHASE_TRACE").is_some() {
            eprintln!(
                "c phase-trace TIMING get-value n={} {:.1}s",
                requested.len(),
                _t_gv.elapsed().as_secs_f64()
            );
        }
        format!("({})", pairs.join(" "))
    }

    /// Generate output for the Z3 `(eval <term>)` command.
    ///
    /// Evaluates a single term in the current model and prints just its value
    /// (no `(term value)` pairing), matching Z3's `eval` surface. Shares the
    /// model resolution and per-term evaluation with `(get-value ...)`.
    pub(crate) fn eval_term(&self, term_id: TermId) -> String {
        let mut dummy = None;
        let model = match self.value_query_model(&mut dummy) {
            Ok(m) => m,
            Err(e) => return e,
        };
        match self.term_value_string(model, term_id) {
            Ok(value_str) => value_str,
            Err(e) => format!("(error \"value is not available: {e}\")"),
        }
    }
}
