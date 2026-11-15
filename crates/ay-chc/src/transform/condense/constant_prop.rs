// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Inter-clause constant propagation for the condense superpass.
//!
//! Reimplements the *idea* of Eldarica's `ConstantPropagator` dataflow (no
//! code copied): compute, for every predicate argument position, whether the
//! argument is the same scalar or bounded ground-array constant `c` in every fact derivable for the
//! predicate. Positions proven constant let us strengthen clause bodies with
//! `arg = c`, project those positions, and fold constraints (which
//! guards, prunes dead branches, and unlocks reachability/inlining in later
//! condense rounds).
//!
//! # Soundness (G1)
//!
//! Two phases keep both verdict directions exact:
//!
//! 1. **Optimistic dataflow** over the lattice `Unknown -> Const(c) -> Varies`
//!    computes candidate constant positions (sound for the least model by
//!    induction over derivations).
//! 2. **Justification demotion** keeps only positions where EVERY defining
//!    clause forces the constant using exact ground evaluation, constraint
//!    equalities, or other *justified* constant positions of body
//!    predicates. This is exactly the condition needed for model-level
//!    back-translation: `M(P) := M'(P) /\ (x_i = c_i)` satisfies every
//!    ORIGINAL clause whenever `M'` satisfies the transformed clauses,
//!    because each restored head conjunct is implied per-clause by the body
//!    hypotheses.
//!
//! UNSAT direction: bodies are only strengthened with facts that hold in
//! every derivation of the transformed system, so derivations transfer to the
//! original clause set after completing projected positions. Clauses and
//! indices are retained, including constraints folded to false.
//!
//! Array values are private to this analysis: the shared SPLIT-SYM scalar
//! literal/pin interface is unchanged. Ground BV->Bool arrays use exact finite
//! domain equality, not structural store equality. One captured caller stop
//! and cumulative work/growth allowance spans both phases and rewriting;
//! unsupported terms decline pins, while any resource stop returns identity.

use crate::{ChcExpr, ChcOp, ChcProblem, HornClause, PredicateId, PredicateInterpretation};
use ay_core::kani_compat::DetHashMap as FxHashMap;

use super::super::{
    BackTranslator, IdentityBackTranslator, InvalidityWitness, TransformMemoryReport,
    TransformObligation, TransformationResult, Transformer, ValidityWitness,
};

mod analysis;
mod evaluate;
mod ground;
mod projection;
mod rewrite_budget;

#[cfg(test)]
mod tests;

pub(crate) struct ConstantPropagator {
    verbose: bool,
}

impl ConstantPropagator {
    pub(crate) fn new() -> Self {
        Self { verbose: false }
    }

    pub(crate) fn with_verbose(mut self, verbose: bool) -> Self {
        self.verbose = verbose;
        self
    }

    /// Whether `expr` is a literal constant (shared with the SPLIT-SYM
    /// symbol splitter, which reuses the same pin analysis).
    pub(in crate::transform) fn is_literal(expr: &ChcExpr) -> bool {
        matches!(
            expr,
            ChcExpr::Bool(_) | ChcExpr::Int(_) | ChcExpr::Real(_, _) | ChcExpr::BitVec(_, _)
        )
    }

    /// Collect `var = literal` pins from top-level constraint conjuncts.
    ///
    /// Returns `None` when two pins conflict (`v = c1 /\ v = c2`, `c1 != c2`):
    /// the clause constraint is unsatisfiable and the clause never fires.
    pub(in crate::transform) fn constraint_pins(
        clause: &HornClause,
    ) -> Option<FxHashMap<String, ChcExpr>> {
        let mut pins: FxHashMap<String, ChcExpr> = FxHashMap::default();
        let Some(constraint) = &clause.body.constraint else {
            return Some(pins);
        };
        for conj in constraint.collect_conjuncts() {
            let ChcExpr::Op(ChcOp::Eq, args) = &conj else {
                continue;
            };
            if args.len() != 2 {
                continue;
            }
            let (var, lit) = match (args[0].as_ref(), args[1].as_ref()) {
                (ChcExpr::Var(v), lit) if Self::is_literal(lit) => (v, lit),
                (lit, ChcExpr::Var(v)) if Self::is_literal(lit) => (v, lit),
                _ => continue,
            };
            if let Some(existing) = pins.get(&var.name) {
                if existing != lit {
                    // v = c1 and v = c2 with c1 != c2: the clause never fires.
                    return None;
                }
            } else {
                pins.insert(var.name.clone(), lit.clone());
            }
        }
        Some(pins)
    }
}

impl Transformer for ConstantPropagator {
    fn transform(self: Box<Self>, problem: ChcProblem) -> TransformationResult {
        let mut budget = ground::Budget::new();
        let Ok(consts) = analysis::constants(&problem, &mut budget) else {
            return identity(problem);
        };
        if consts.is_empty() {
            return identity(problem);
        }

        let Ok((new_problem, kept)) = projection::project(&problem, &consts, &mut budget) else {
            return identity(problem);
        };
        if self.verbose {
            safe_eprintln!(
                "CHC condense constant-prop: {} justified constant argument positions projected",
                consts.values().map(Vec::len).sum::<usize>()
            );
        }

        // Restore the exact input signature after projecting constants.
        let mut original_sorts: FxHashMap<PredicateId, Vec<crate::ChcSort>> = FxHashMap::default();
        for pred in problem.predicates() {
            original_sorts.insert(pred.id, pred.arg_sorts.clone());
        }

        if budget.charge(0).is_err() {
            return identity(problem);
        }
        TransformationResult {
            problem: new_problem,
            back_translator: Box::new(ConstantPropBackTranslator {
                consts,
                original_sorts,
                kept,
                input_problem: crate::ground_derivation::ground_backtranslation_enabled()
                    .then(|| std::sync::Arc::new(problem)),
            }),
        }
    }
}

fn identity(problem: ChcProblem) -> TransformationResult {
    TransformationResult {
        problem,
        back_translator: Box::new(IdentityBackTranslator),
    }
}

/// Back-translator for [`ConstantPropagator`]: strengthens each affected
/// predicate's interpretation with its justified constant-argument equalities
/// so the model satisfies the ORIGINAL (unstrengthened) clauses.
struct ConstantPropBackTranslator {
    consts: FxHashMap<PredicateId, Vec<(usize, ChcExpr)>>,
    original_sorts: FxHashMap<PredicateId, Vec<crate::ChcSort>>,
    kept: Vec<Vec<usize>>,
    /// INPUT problem, retained for ground back-translation only.
    input_problem: Option<std::sync::Arc<ChcProblem>>,
}

impl BackTranslator for ConstantPropBackTranslator {
    fn translate_ground_derivation(
        &self,
        derivation: &crate::ground_derivation::GroundDerivation,
    ) -> Option<crate::ground_derivation::GroundDerivation> {
        let original = self.input_problem.clone()?;
        let candidates = (0..original.clauses().len())
            .map(|index| vec![index])
            .collect();
        crate::ground_derivation::clause_map::ClauseMapGroundTranslator::new(
            "constant-propagator",
            original,
            candidates,
        )
        .translate(derivation)
    }

    fn ground_translation_name(&self) -> &'static str {
        "constant-propagator"
    }

    fn translate_validity(&self, witness: ValidityWitness) -> ValidityWitness {
        let mut new_witness = ValidityWitness::new();
        for (pred_id, interp) in witness.iter() {
            let Some(positions) = self.consts.get(pred_id) else {
                new_witness.set(*pred_id, interp.clone());
                continue;
            };
            let Some(sorts) = self.original_sorts.get(pred_id) else {
                continue;
            };
            let Some(kept) = self.kept.get(pred_id.0 as usize) else {
                continue;
            };
            let Some(vars) = super::super::parameter_vars::restore(
                interp,
                sorts,
                kept,
                &format!("__cprop_{}", pred_id.0),
            ) else {
                // A malformed model must still fail original validation.
                continue;
            };
            let mut conjuncts = vec![interp.formula.clone()];
            for (j, c) in positions {
                if let Some(v) = vars.get(*j) {
                    conjuncts.push(ChcExpr::eq(ChcExpr::var(v.clone()), c.clone()));
                }
            }
            new_witness.set(
                *pred_id,
                PredicateInterpretation::new(vars, ChcExpr::and_all(conjuncts)),
            );
        }
        new_witness
    }

    fn translate_invalidity(&self, witness: InvalidityWitness) -> InvalidityWitness {
        witness
    }

    fn transform_memory(&self) -> TransformMemoryReport {
        TransformMemoryReport::with_original_validation_obligations(
            "constant_propagation",
            [
                TransformObligation::named("original-validation-on-safe"),
                TransformObligation::named("original-replay-on-unsafe"),
            ],
        )
    }
}
