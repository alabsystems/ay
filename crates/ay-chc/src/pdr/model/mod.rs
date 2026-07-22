// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model types for PDR solver - predicate interpretations and inductive invariants.

use std::sync::Arc;

use crate::{ChcError, ChcExpr, ChcOp, ChcProblem, ChcResult, ChcSort, ChcVar};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use ay_core::quote_symbol;

use super::invariant_parser::InvariantParser;

/// Interpretation of a predicate (what Inv(x) means)
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct PredicateInterpretation {
    /// Variables that the interpretation is over
    pub vars: Vec<ChcVar>,
    /// Formula defining the predicate
    pub formula: ChcExpr,
}

impl PredicateInterpretation {
    pub fn new(vars: Vec<ChcVar>, formula: ChcExpr) -> Self {
        Self { vars, formula }
    }
}

/// Kind of external SMT obligation generated for replaying a CHC certificate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ChcReplayObligationKind {
    Initiation,
    Consecution,
    Safety,
    TraceValidity,
}

impl ChcReplayObligationKind {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Initiation => "initiation",
            Self::Consecution => "consecution",
            Self::Safety => "safety",
            Self::TraceValidity => "trace-validity",
        }
    }

    pub fn from_label(label: &str) -> Option<Self> {
        match label {
            "initiation" => Some(Self::Initiation),
            "consecution" => Some(Self::Consecution),
            "safety" => Some(Self::Safety),
            "trace-validity" => Some(Self::TraceValidity),
            _ => None,
        }
    }
}

/// A standalone SMT-LIB query that replays one certificate obligation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ChcReplayObligation {
    pub name: String,
    pub kind: ChcReplayObligationKind,
    pub clause_index: usize,
    pub smtlib: String,
}

/// Records how an invariant model was produced internally (informational only).
///
/// This enum does NOT affect validation behavior — the portfolio ALWAYS runs
/// full verification regardless of how the model was produced. It exists for
/// logging and debugging. Add variants as needed when new production paths
/// are instrumented.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub(crate) enum InvariantVerificationMethod {
    /// Default/unspecified production method
    #[default]
    Unspecified,
    /// Produced by TRL engine via expanded system encoding
    TrlExpandedSystem,
    /// Produced by TPA engine via Craig interpolation
    TpaInterpolation,
    /// Produced by algebraic invariant synthesis (n-elimination from polynomial closed forms)
    AlgebraicClosedForm,
}

/// Invariant model assigning interpretations to predicates
#[derive(Debug, Clone, Default)]
pub struct InvariantModel {
    pub(crate) interpretations: FxHashMap<crate::PredicateId, PredicateInterpretation>,
    /// Records the internal production method for logging/debugging.
    /// Does NOT affect portfolio validation — full verification always runs.
    pub(crate) verification_method: InvariantVerificationMethod,
    /// Set when every lemma in the model was individually verified as
    /// self-inductive (and entry-inductive for multi-predicate) by
    /// `check_invariants_prove_safety`. When true, the whole-model
    /// `verify_model_with_budget` check in `try_main_loop_direct_safety_proof`
    /// is skipped — the portfolio's back-translation verification provides the
    /// soundness guarantee instead. (#5877)
    ///
    /// This flag addresses a BvToInt-relaxed regression where individual lemmas
    /// pass self-inductiveness (per-clause per-lemma SMT with ITE case-split)
    /// but the whole-model conjunction against the full transition clause gets
    /// SAT from the SMT solver due to integer counterexamples that are infeasible
    /// in the original BV encoding.
    pub(crate) individually_inductive: bool,
    /// Set when the model was built from the full converged frame without any
    /// conjunct filtering. Frame convergence (Frame[k] = Frame[k+1]) proves
    /// the full frame conjunction is inductive. When true, `verify_model` and
    /// `verify_model_fresh` are skipped — their only possible failure mode is
    /// SMT budget exhaustion on the (now larger) unfiltered model.
    ///
    /// SOUNDNESS: Must ONLY be set when `build_model_from_frame_impl` did not
    /// remove any conjuncts via `filter_non_canonical_conjuncts`. Filtering
    /// weakens the model below the inductiveness threshold that convergence
    /// proved. (#5970, #7410)
    pub(crate) convergence_proven: bool,
    /// Sealed quantified array-invariant certificate (FORALL-ARR ghost-pair
    /// lane, agenda #16). When set, the true model of the ORIGINAL problem is
    /// the quantified `forall i. I'(args, i, select(arr, i))` denoted by the
    /// certificate — it has no quantifier-free `ChcExpr` representation, so
    /// `interpretations` is intentionally EMPTY. The certificate can only be
    /// constructed by `GhostPairCertificate::certify_and_seal`, which runs the
    /// full instantiation-based per-rule discharge on the original clauses;
    /// downstream Safe gates re-check it via `recheck_ghost_pair_certificate`
    /// instead of the quantifier-free `verify_model_*` paths.
    pub(crate) ghost_pair_certificate: Option<Arc<crate::transform::GhostPairCertificate>>,
}

impl InvariantModel {
    pub fn new() -> Self {
        Self::default()
    }

    /// True when this model carries a sealed quantified array-invariant
    /// certificate (ghost-pair lane). Such models have intentionally empty
    /// quantifier-free interpretations; the certificate is the witness.
    pub fn has_quantified_array_certificate(&self) -> bool {
        self.ghost_pair_certificate.is_some()
    }

    /// The sealed quantified array-invariant certificate, if any.
    pub(crate) fn ghost_pair_certificate(
        &self,
    ) -> Option<&Arc<crate::transform::GhostPairCertificate>> {
        self.ghost_pair_certificate.as_ref()
    }

    /// Attach a sealed quantified array-invariant certificate.
    pub(crate) fn set_ghost_pair_certificate(
        &mut self,
        certificate: Arc<crate::transform::GhostPairCertificate>,
    ) {
        self.ghost_pair_certificate = Some(certificate);
    }

    pub fn set(&mut self, pred: crate::PredicateId, interp: PredicateInterpretation) {
        self.interpretations.insert(pred, interp);
    }

    pub fn get(&self, pred: &crate::PredicateId) -> Option<&PredicateInterpretation> {
        self.interpretations.get(pred)
    }

    /// Iterate over all predicate interpretations
    pub fn iter(&self) -> impl Iterator<Item = (&crate::PredicateId, &PredicateInterpretation)> {
        self.interpretations.iter()
    }

    /// Get the number of predicates in the model
    pub fn len(&self) -> usize {
        self.interpretations.len()
    }

    /// Check if the model is empty
    pub fn is_empty(&self) -> bool {
        self.interpretations.is_empty()
    }

    /// Remove conjuncts containing free variables not declared as parameters.
    ///
    /// For each predicate interpretation, walks the formula and drops any
    /// top-level conjunct that references a variable not in the parameter list.
    /// This prevents model output from containing undeclared variables that
    /// would cause Z3 "unknown constant" errors during model verification.
    ///
    /// Fixes #5246: ay-chc-native model output references undeclared variables.
    /// Returns `true` if any conjuncts were removed (model was weakened).
    pub fn sanitize_free_variables(&mut self) -> bool {
        use ay_core::kani_compat::DetHashSet as FxHashSet;
        let mut modified = false;
        for interp in self.interpretations.values_mut() {
            let param_names: FxHashSet<&str> =
                interp.vars.iter().map(|v| v.name.as_str()).collect();
            let formula_vars = interp.formula.vars();
            let has_free = formula_vars
                .iter()
                .any(|v| !param_names.contains(v.name.as_str()));
            if !has_free {
                continue;
            }
            // Filter top-level conjuncts: keep only those whose variables are all parameters
            let conjuncts: Vec<ChcExpr> = interp.formula.conjuncts().into_iter().cloned().collect();
            let original_count = conjuncts.len();
            let filtered: Vec<ChcExpr> = conjuncts
                .into_iter()
                .filter(|c| {
                    c.vars()
                        .iter()
                        .all(|v| param_names.contains(v.name.as_str()))
                })
                .collect();
            if filtered.len() < original_count {
                modified = true;
            }
            interp.formula = if filtered.is_empty() {
                ChcExpr::Bool(true)
            } else {
                filtered
                    .into_iter()
                    .reduce(ChcExpr::and)
                    .unwrap_or(ChcExpr::Bool(true))
            };
        }
        modified
    }

    /// Export the model to SMT-LIB 2.6 format
    ///
    /// Returns a string with `(define-fun ...)` declarations for each predicate.
    /// This format is compatible with Z3 and other SMT solvers.
    ///
    /// Example output:
    /// ```text
    /// (define-fun Inv ((x Int)) Bool
    ///   (and (<= 0 x) (<= x 10)))
    /// ```
    pub fn to_smtlib(&self, problem: &ChcProblem) -> String {
        let mut output = String::new();
        output.push_str("; CHC Solution (Inductive Invariants)\n");
        output.push_str("; Generated by AY PDR solver\n\n");

        // Sort by predicate ID for deterministic output
        let mut preds: Vec<_> = self.interpretations.iter().collect();
        preds.sort_by_key(|(id, _)| id.index());

        for (pred_id, interp) in preds {
            // Get predicate name from problem
            let pred_name = problem
                .predicates()
                .iter()
                .find(|p| p.id == *pred_id)
                .map_or("unknown", |p| p.name.as_str());

            output.push_str(&format!("(define-fun {} (", quote_symbol(pred_name)));

            // Parameter list
            for (i, var) in interp.vars.iter().enumerate() {
                if i > 0 {
                    output.push(' ');
                }
                output.push_str(&format!("({} {})", quote_symbol(&var.name), var.sort));
            }

            // Sanitize: output only the formula with declared parameters (#5246)
            let formula = Self::sanitize_formula_for_output(&interp.vars, &interp.formula);
            output.push_str(") Bool\n  ");
            output.push_str(&Self::expr_to_smtlib(&formula));
            output.push_str(")\n\n");
        }

        output
    }

    /// Export the model as a machine-checkable inductive invariant certificate.
    ///
    /// The certificate includes:
    /// 1. Valid SMT-LIB `define-fun` declarations for each predicate invariant
    /// 2. Comments describing the proof obligations that can be checked independently
    ///
    /// The proof obligation comments describe what a verifier should check:
    /// - Initiation: the initial states satisfy the invariant
    /// - Consecution: the invariant is preserved by transitions
    /// - Safety: the invariant implies the safety property (query clauses are UNSAT)
    pub fn to_certificate(&self, problem: &ChcProblem) -> String {
        use std::fmt::Write;
        let mut out = String::new();

        // Header
        let _ = writeln!(out, ";; AY CHC Certificate: SAFE");
        let _ = writeln!(out, ";; Format: ay-chc-cert v1");
        let _ = writeln!(out, ";;");
        let _ = writeln!(out, ";; Inductive invariant:");

        // Emit define-fun declarations (reuses to_smtlib formatting)
        let mut preds: Vec<_> = self.interpretations.iter().collect();
        preds.sort_by_key(|(id, _)| id.index());

        for (pred_id, interp) in &preds {
            let pred_name = problem
                .predicates()
                .iter()
                .find(|p| p.id == **pred_id)
                .map_or("unknown", |p| p.name.as_str());

            let _ = write!(out, "(define-fun {} (", quote_symbol(pred_name));
            for (i, var) in interp.vars.iter().enumerate() {
                if i > 0 {
                    out.push(' ');
                }
                let _ = write!(out, "({} {})", quote_symbol(&var.name), var.sort);
            }
            let formula = Self::sanitize_formula_for_output(&interp.vars, &interp.formula);
            let _ = write!(out, ") Bool\n  ");
            out.push_str(&Self::expr_to_smtlib(&formula));
            let _ = writeln!(out, ")");
        }

        // Proof obligations as comments
        let _ = writeln!(out, ";;");
        let _ = writeln!(
            out,
            ";; Proof obligations (verify by checking each is UNSAT):"
        );

        let mut obligation_idx = 1u32;
        for (clause_idx, clause) in problem.clauses().iter().enumerate() {
            let body_preds = &clause.body.predicates;
            let has_body_preds = !body_preds.is_empty();

            match &clause.head {
                crate::ClauseHead::Predicate(head_pred_id, _) => {
                    let head_name = problem
                        .get_predicate(*head_pred_id)
                        .map_or("?", |p| p.name.as_str());
                    if !has_body_preds {
                        // Initiation clause: constraint => Pred(args)
                        let _ = writeln!(
                            out,
                            ";; {obligation_idx}. Initiation (clause {clause_idx}): init-body => {head_name}(init-vars)"
                        );
                    } else {
                        // Transition clause: Pred(pre) /\ constraint => Pred(post)
                        let body_names: Vec<&str> = body_preds
                            .iter()
                            .map(|(pid, _)| {
                                problem.get_predicate(*pid).map_or("?", |p| p.name.as_str())
                            })
                            .collect();
                        let _ = writeln!(
                            out,
                            ";; {obligation_idx}. Consecution (clause {clause_idx}): {} /\\ trans-body => {head_name}(post)",
                            body_names.join(", ")
                        );
                    }
                    obligation_idx += 1;
                }
                crate::ClauseHead::False => {
                    // Query clause: Pred(vars) /\ constraint => false
                    let body_names: Vec<&str> = body_preds
                        .iter()
                        .map(|(pid, _)| {
                            problem.get_predicate(*pid).map_or("?", |p| p.name.as_str())
                        })
                        .collect();
                    let _ = writeln!(
                        out,
                        ";; {obligation_idx}. Safety (clause {clause_idx}): {} /\\ query-body => false",
                        body_names.join(", ")
                    );
                    obligation_idx += 1;
                }
            }
        }

        out
    }

    /// Generate standalone SMT-LIB obligations for external safe-certificate replay.
    ///
    /// Each generated query must be UNSAT. The queries use the emitted predicate
    /// interpretations as `define-fun` bodies, assert one possible violation of
    /// the corresponding Horn clause, and leave the background theory check to an
    /// external SMT solver such as Z3.
    pub fn replay_obligations(&self, problem: &ChcProblem) -> ChcResult<Vec<ChcReplayObligation>> {
        problem
            .clauses()
            .iter()
            .enumerate()
            .map(|(clause_index, clause)| {
                let (kind, violation) = self.clause_violation_formula(problem, clause)?;
                let name = format!("clause-{clause_index}-{}", kind.as_str());
                let smtlib = self.render_replay_obligation(
                    problem,
                    clause_index,
                    kind,
                    &name,
                    clause,
                    &violation,
                );
                Ok(ChcReplayObligation {
                    name,
                    kind,
                    clause_index,
                    smtlib,
                })
            })
            .collect()
    }

    fn clause_violation_formula(
        &self,
        problem: &ChcProblem,
        clause: &crate::HornClause,
    ) -> ChcResult<(ChcReplayObligationKind, ChcExpr)> {
        let mut terms = self.body_replay_terms(problem, &clause.body)?;
        let kind = match &clause.head {
            crate::ClauseHead::Predicate(pred_id, args) => {
                let instantiated = self.instantiate_predicate(problem, *pred_id, args)?;
                terms.push(ChcExpr::not(instantiated));
                if clause.body.predicates.is_empty() {
                    ChcReplayObligationKind::Initiation
                } else {
                    ChcReplayObligationKind::Consecution
                }
            }
            crate::ClauseHead::False => ChcReplayObligationKind::Safety,
        };
        Ok((kind, ChcExpr::and_all(terms)))
    }

    fn body_replay_terms(
        &self,
        problem: &ChcProblem,
        body: &crate::ClauseBody,
    ) -> ChcResult<Vec<ChcExpr>> {
        let mut terms = Vec::new();
        for (pred_id, args) in &body.predicates {
            terms.push(self.instantiate_predicate(problem, *pred_id, args)?);
        }
        if let Some(constraint) = &body.constraint {
            terms.push(constraint.clone());
        }
        Ok(terms)
    }

    fn instantiate_predicate(
        &self,
        problem: &ChcProblem,
        pred_id: crate::PredicateId,
        args: &[ChcExpr],
    ) -> ChcResult<ChcExpr> {
        let pred = problem
            .get_predicate(pred_id)
            .ok_or_else(|| ChcError::UndefinedPredicate(format!("P{}", pred_id.index())))?;
        let interp = self.get(&pred_id).ok_or_else(|| {
            ChcError::Verification(format!(
                "missing invariant interpretation for predicate {}",
                pred.name
            ))
        })?;
        if interp.vars.len() != args.len() {
            return Err(ChcError::ArityMismatch {
                name: pred.name.clone(),
                expected: interp.vars.len(),
                actual: args.len(),
            });
        }

        let formula = Self::sanitize_formula_for_output(&interp.vars, &interp.formula);
        let subst = interp
            .vars
            .iter()
            .cloned()
            .zip(args.iter().cloned())
            .collect::<Vec<_>>();
        Ok(formula.substitute(&subst))
    }

    fn render_replay_obligation(
        &self,
        problem: &ChcProblem,
        clause_index: usize,
        kind: ChcReplayObligationKind,
        name: &str,
        clause: &crate::HornClause,
        violation: &ChcExpr,
    ) -> String {
        use std::fmt::Write;

        let mut out = String::new();
        let _ = writeln!(out, "; AY CHC certificate replay obligation: {name}");
        let _ = writeln!(out, "; kind: {}", kind.as_str());
        let _ = writeln!(out, "; clause: {clause_index}");
        let _ = writeln!(out, "(set-logic ALL)");
        out.push('\n');
        out.push_str(&self.to_smtlib(problem));

        let mut vars = clause.vars();
        vars.sort_by(|a, b| a.name.cmp(&b.name).then_with(|| a.sort.cmp(&b.sort)));
        for var in vars {
            let _ = writeln!(
                out,
                "(declare-const {} {})",
                quote_symbol(&var.name),
                var.sort
            );
        }
        let _ = writeln!(out, "(assert {})", Self::expr_to_smtlib(violation));
        let _ = writeln!(out, "(check-sat)");
        let _ = writeln!(out, "(exit)");
        out
    }

    /// Export the model to Spacer-compatible format
    ///
    /// Returns a string in the format used by Z3 Spacer's output:
    /// ```text
    /// (
    ///   (define-fun Inv ((x Int)) Bool (and ...))
    /// )
    /// ```
    pub fn to_spacer_format(&self, problem: &ChcProblem) -> String {
        let mut output = String::new();
        output.push_str("(\n");

        let mut preds: Vec<_> = self.interpretations.iter().collect();
        preds.sort_by_key(|(id, _)| id.index());

        for (pred_id, interp) in preds {
            let pred_name = problem
                .predicates()
                .iter()
                .find(|p| p.id == *pred_id)
                .map_or("unknown", |p| p.name.as_str());

            output.push_str("  (define-fun ");
            output.push_str(&quote_symbol(pred_name));
            output.push_str(" (");

            for (i, var) in interp.vars.iter().enumerate() {
                if i > 0 {
                    output.push(' ');
                }
                output.push_str(&format!("({} {})", quote_symbol(&var.name), var.sort));
            }

            // Sanitize: output only the formula with declared parameters (#5246)
            let formula = Self::sanitize_formula_for_output(&interp.vars, &interp.formula);
            output.push_str(") Bool ");
            output.push_str(&Self::expr_to_smtlib(&formula));
            output.push_str(")\n");
        }

        output.push_str(")\n");
        output
    }

    /// Remove conjuncts containing variables not declared as parameters.
    ///
    /// This is the inline sanitization used by output methods to ensure
    /// all variables in the formula body are declared in the define-fun
    /// parameter list. Prevents Z3 "unknown constant" errors (#5246).
    fn sanitize_formula_for_output(params: &[ChcVar], formula: &ChcExpr) -> ChcExpr {
        use ay_core::kani_compat::DetHashSet as FxHashSet;
        let param_names: FxHashSet<&str> = params.iter().map(|v| v.name.as_str()).collect();
        let formula_vars = formula.vars();
        let has_free = formula_vars
            .iter()
            .any(|v| !param_names.contains(v.name.as_str()));
        if !has_free {
            return formula.clone();
        }
        // Filter conjuncts, keeping only those with declared-parameter variables
        let conjuncts: Vec<ChcExpr> = formula.conjuncts().into_iter().cloned().collect();
        let filtered: Vec<ChcExpr> = conjuncts
            .into_iter()
            .filter(|c| {
                c.vars()
                    .iter()
                    .all(|v| param_names.contains(v.name.as_str()))
            })
            .collect();
        if filtered.is_empty() {
            ChcExpr::Bool(true)
        } else {
            filtered
                .into_iter()
                .reduce(ChcExpr::and)
                .unwrap_or(ChcExpr::Bool(true))
        }
    }

    /// Format a named function/predicate application as SMT-LIB.
    fn fmt_app(name: String, args: &[Arc<ChcExpr>]) -> String {
        if args.is_empty() {
            name
        } else {
            let a: Vec<_> = args.iter().map(|a| Self::expr_to_smtlib(a)).collect();
            format!("({} {})", name, a.join(" "))
        }
    }

    /// Convert a CHC expression to SMT-LIB format string
    ///
    /// This handles proper formatting of boolean constants and negative integers.
    /// Can be used to generate SMT-LIB strings for any CHC expression.
    pub fn expr_to_smtlib(expr: &ChcExpr) -> String {
        crate::expr::maybe_grow_expr_stack(|| match expr {
            ChcExpr::Bool(true) => "true".to_string(),
            ChcExpr::Bool(false) => "false".to_string(),
            ChcExpr::Int(n) if *n < 0 => format!("(- {})", n.unsigned_abs()),
            ChcExpr::Int(n) => n.to_string(),
            ChcExpr::BitVec(val, width) => format!("(_ bv{val} {width})"),
            ChcExpr::Real(num, denom) => {
                if *num < 0 {
                    format!("(/ (- {}) {})", num.unsigned_abs(), denom)
                } else {
                    format!("(/ {num} {denom})")
                }
            }
            ChcExpr::Var(v) => quote_symbol(&v.name),
            ChcExpr::PredicateApp(name, _, args) => Self::fmt_app(quote_symbol(name), args),
            ChcExpr::FuncApp(name, sort, args) => {
                // Qualify datatype constructors: (as Name Sort) (#3362)
                let qn = match sort {
                    ChcSort::Uninterpreted(sn) | ChcSort::Datatype { name: sn, .. } => {
                        format!("(as {} {})", quote_symbol(name), quote_symbol(sn))
                    }
                    _ => quote_symbol(name),
                };
                Self::fmt_app(qn, args)
            }
            ChcExpr::Op(op, args) => {
                let op_str = match op {
                    ChcOp::Not => "not",
                    ChcOp::And => "and",
                    ChcOp::Or => "or",
                    ChcOp::Implies => "=>",
                    ChcOp::Iff => "=",
                    ChcOp::Add => "+",
                    ChcOp::Sub => "-",
                    ChcOp::Mul => "*",
                    ChcOp::Div => "div",
                    ChcOp::Mod => "mod",
                    ChcOp::Neg => "-",
                    ChcOp::Eq => "=",
                    ChcOp::Ne => "distinct",
                    ChcOp::Lt => "<",
                    ChcOp::Le => "<=",
                    ChcOp::Gt => ">",
                    ChcOp::Ge => ">=",
                    ChcOp::Ite => "ite",
                    ChcOp::Select => "select",
                    ChcOp::Store => "store",
                    // Bitvector arithmetic
                    ChcOp::BvAdd => "bvadd",
                    ChcOp::BvSub => "bvsub",
                    ChcOp::BvMul => "bvmul",
                    ChcOp::BvUDiv => "bvudiv",
                    ChcOp::BvURem => "bvurem",
                    ChcOp::BvSDiv => "bvsdiv",
                    ChcOp::BvSRem => "bvsrem",
                    ChcOp::BvSMod => "bvsmod",
                    // Bitvector bitwise
                    ChcOp::BvAnd => "bvand",
                    ChcOp::BvOr => "bvor",
                    ChcOp::BvXor => "bvxor",
                    ChcOp::BvNand => "bvnand",
                    ChcOp::BvNor => "bvnor",
                    ChcOp::BvXnor => "bvxnor",
                    // Bitvector unary
                    ChcOp::BvNot => "bvnot",
                    ChcOp::BvNeg => "bvneg",
                    // Bitvector shift
                    ChcOp::BvShl => "bvshl",
                    ChcOp::BvLShr => "bvlshr",
                    ChcOp::BvAShr => "bvashr",
                    // Bitvector comparison
                    ChcOp::BvULt => "bvult",
                    ChcOp::BvULe => "bvule",
                    ChcOp::BvUGt => "bvugt",
                    ChcOp::BvUGe => "bvuge",
                    ChcOp::BvSLt => "bvslt",
                    ChcOp::BvSLe => "bvsle",
                    ChcOp::BvSGt => "bvsgt",
                    ChcOp::BvSGe => "bvsge",
                    ChcOp::BvComp => "bvcomp",
                    // Bitvector concat
                    ChcOp::BvConcat => "concat",
                    // Bitvector conversion
                    ChcOp::Bv2Nat => "bv2nat",
                    // Bitvector indexed operations — use (_ op params) syntax
                    ChcOp::BvExtract(hi, lo) => {
                        let args_str: Vec<_> =
                            args.iter().map(|a| Self::expr_to_smtlib(a)).collect();
                        return format!("((_ extract {hi} {lo}) {})", args_str.join(" "));
                    }
                    ChcOp::BvZeroExtend(n) => {
                        let args_str: Vec<_> =
                            args.iter().map(|a| Self::expr_to_smtlib(a)).collect();
                        return format!("((_ zero_extend {n}) {})", args_str.join(" "));
                    }
                    ChcOp::BvSignExtend(n) => {
                        let args_str: Vec<_> =
                            args.iter().map(|a| Self::expr_to_smtlib(a)).collect();
                        return format!("((_ sign_extend {n}) {})", args_str.join(" "));
                    }
                    ChcOp::BvRotateLeft(n) => {
                        let args_str: Vec<_> =
                            args.iter().map(|a| Self::expr_to_smtlib(a)).collect();
                        return format!("((_ rotate_left {n}) {})", args_str.join(" "));
                    }
                    ChcOp::BvRotateRight(n) => {
                        let args_str: Vec<_> =
                            args.iter().map(|a| Self::expr_to_smtlib(a)).collect();
                        return format!("((_ rotate_right {n}) {})", args_str.join(" "));
                    }
                    ChcOp::BvRepeat(n) => {
                        let args_str: Vec<_> =
                            args.iter().map(|a| Self::expr_to_smtlib(a)).collect();
                        return format!("((_ repeat {n}) {})", args_str.join(" "));
                    }
                    ChcOp::Int2Bv(w) => {
                        let args_str: Vec<_> =
                            args.iter().map(|a| Self::expr_to_smtlib(a)).collect();
                        return format!("((_ int2bv {w}) {})", args_str.join(" "));
                    }
                };
                let args_str: Vec<_> = args.iter().map(|a| Self::expr_to_smtlib(a)).collect();
                format!("({} {})", op_str, args_str.join(" "))
            }
            ChcExpr::ConstArrayMarker(_) => "(as const)".to_string(),
            ChcExpr::IsTesterMarker(name) => format!("(_ is {})", quote_symbol(name)),
            ChcExpr::ConstArray(key_sort, val) => {
                let val_str = Self::expr_to_smtlib(val);
                let val_sort = val.sort();
                format!("((as const (Array {key_sort} {val_sort})) {val_str})")
            }
        })
    }

    /// Parse invariants from SMT-LIB format string
    ///
    /// Parses `(define-fun ...)` declarations and creates predicate interpretations.
    /// The input format should match the output of `to_smtlib()`:
    ///
    /// ```text
    /// (define-fun Inv ((x Int)) Bool
    ///   (and (<= 0 x) (<= x 10)))
    /// ```
    ///
    /// # Arguments
    /// * `input` - SMT-LIB format string containing define-fun declarations
    /// * `problem` - The CHC problem to match predicates against
    ///
    /// # Returns
    /// An InvariantModel containing the parsed interpretations, or an error if parsing fails
    pub fn parse_smtlib(input: &str, problem: &ChcProblem) -> ChcResult<Self> {
        let mut parser = InvariantParser::new(input, problem);
        parser.parse()
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
mod tests;
