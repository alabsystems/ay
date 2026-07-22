// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Inter-clause constant propagation for the condense superpass.
//!
//! Reimplements the *idea* of Eldarica's `ConstantPropagator` dataflow (no
//! code copied): compute, for every predicate argument position, whether the
//! argument is the same literal constant `c` in every fact derivable for the
//! predicate. Positions proven constant let us strengthen clause bodies with
//! `arg = c`, substitute the constant into clause constraints (which folds
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
//!    clause syntactically forces the constant using literals, constraint
//!    equalities `v = lit`, or other *justified* constant positions of body
//!    predicates. This is exactly the condition needed for model-level
//!    back-translation: `M(P) := M'(P) /\ (x_i = c_i)` satisfies every
//!    ORIGINAL clause whenever `M'` satisfies the transformed clauses,
//!    because each added head conjunct is implied per-clause by the body
//!    hypotheses.
//!
//! UNSAT direction: bodies are only strengthened with facts that hold in
//! every derivation of the transformed system, so derivations transfer to the
//! original clause set unchanged (indices remapped when constraint folding
//! prunes a clause).

use crate::{
    ChcExpr, ChcOp, ChcProblem, ChcVar, ClauseBody, ClauseHead, HornClause, PredicateId,
    PredicateInterpretation,
};
use ay_core::kani_compat::DetHashMap as FxHashMap;

use super::super::{
    BackTranslator, IdentityBackTranslator, InvalidityWitness, TransformMemoryReport,
    TransformObligation, TransformationResult, Transformer, ValidityWitness,
};
use super::ClauseIndexMap;

/// Constant-propagation lattice value for one predicate argument position.
#[derive(Clone, Debug, PartialEq)]
enum Cpv {
    /// No defining clause evaluated yet (optimistic top).
    Unknown,
    /// Every evaluated defining clause yields this literal.
    Const(ChcExpr),
    /// Defining clauses disagree or produce non-literal values.
    Varies,
}

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

    /// Extend constraint pins with pins from body-predicate constant
    /// positions. `values` supplies the position lattice; `justified_only`
    /// restricts pins to `Const` (skipping `Unknown`) during the demotion
    /// phase. Returns `None` when pins conflict (clause never fires).
    fn clause_pins(
        clause: &HornClause,
        values: &FxHashMap<(PredicateId, usize), Cpv>,
    ) -> Option<(FxHashMap<String, ChcExpr>, bool)> {
        let mut pins = Self::constraint_pins(clause)?;
        let mut has_unknown_pin = false;
        for (pid, args) in &clause.body.predicates {
            for (j, arg) in args.iter().enumerate() {
                let ChcExpr::Var(v) = arg else { continue };
                match values.get(&(*pid, j)) {
                    Some(Cpv::Const(c)) => {
                        if let Some(existing) = pins.get(&v.name) {
                            if existing != c {
                                return None;
                            }
                        } else {
                            pins.insert(v.name.clone(), c.clone());
                        }
                    }
                    Some(Cpv::Unknown) => has_unknown_pin = true,
                    _ => {}
                }
            }
        }
        Some((pins, has_unknown_pin))
    }

    /// Evaluate one head argument under the clause's pins.
    fn eval_head_arg(
        arg: &ChcExpr,
        pins: &FxHashMap<String, ChcExpr>,
        unknown_vars_may_pin: bool,
    ) -> Cpv {
        if Self::is_literal(arg) {
            return Cpv::Const(arg.clone());
        }
        if let ChcExpr::Var(v) = arg {
            if let Some(lit) = pins.get(&v.name) {
                return Cpv::Const(lit.clone());
            }
            if unknown_vars_may_pin {
                // Optimistic phase: the variable might become pinned once a
                // body position currently at Unknown resolves to Const.
                return Cpv::Unknown;
            }
        }
        Cpv::Varies
    }

    fn join(a: Cpv, b: Cpv) -> Cpv {
        match (a, b) {
            (Cpv::Unknown, x) | (x, Cpv::Unknown) => x,
            (Cpv::Varies, _) | (_, Cpv::Varies) => Cpv::Varies,
            (Cpv::Const(c1), Cpv::Const(c2)) => {
                if c1 == c2 {
                    Cpv::Const(c1)
                } else {
                    Cpv::Varies
                }
            }
        }
    }

    /// Phase 1: optimistic candidate fixpoint over all head positions.
    ///
    /// The sweep is capped: vacuity detection (conflicting optimistic pins)
    /// is not monotone, so in pathological cases the iteration could cycle.
    /// Any output is safe — phase 2 demotes every unjustified candidate.
    fn optimistic_fixpoint(problem: &ChcProblem) -> FxHashMap<(PredicateId, usize), Cpv> {
        let mut values: FxHashMap<(PredicateId, usize), Cpv> = FxHashMap::default();
        for pred in problem.predicates() {
            for j in 0..pred.arity() {
                values.insert((pred.id, j), Cpv::Unknown);
            }
        }
        let max_sweeps = 2 * values.len() + 4;
        for _ in 0..max_sweeps {
            let mut next: FxHashMap<(PredicateId, usize), Cpv> =
                values.keys().map(|key| (*key, Cpv::Unknown)).collect();
            for clause in problem.clauses() {
                let Some(head) = clause.head.predicate_id() else {
                    continue;
                };
                let (pins, has_unknown_pin) = match Self::clause_pins(clause, &values) {
                    Some(result) => result,
                    None => continue, // vacuous clause: contributes nothing
                };
                let head_args = match &clause.head {
                    ClauseHead::Predicate(_, args) => args,
                    ClauseHead::False => continue,
                };
                for (i, arg) in head_args.iter().enumerate() {
                    let eval = Self::eval_head_arg(arg, &pins, has_unknown_pin);
                    let slot = next.entry((head, i)).or_insert(Cpv::Unknown);
                    *slot = Self::join(slot.clone(), eval);
                }
            }
            if next == values {
                break;
            }
            values = next;
        }
        values
    }

    /// Phase 2: demote `Const` positions that are not per-clause justified by
    /// literals, constraint equalities, or other justified `Const` positions.
    fn justify(
        problem: &ChcProblem,
        mut values: FxHashMap<(PredicateId, usize), Cpv>,
    ) -> FxHashMap<(PredicateId, usize), Cpv> {
        loop {
            let mut demote: Vec<(PredicateId, usize)> = Vec::new();
            for clause in problem.clauses() {
                let Some(head) = clause.head.predicate_id() else {
                    continue;
                };
                // Justified pins only: Unknown positions provide no pin here.
                let pins = match Self::clause_pins(clause, &values) {
                    Some((pins, _)) => pins,
                    None => continue, // clause never fires: imposes nothing
                };
                let head_args = match &clause.head {
                    ClauseHead::Predicate(_, args) => args,
                    ClauseHead::False => continue,
                };
                for (i, arg) in head_args.iter().enumerate() {
                    let Some(Cpv::Const(expected)) = values.get(&(head, i)) else {
                        continue;
                    };
                    match Self::eval_head_arg(arg, &pins, false) {
                        Cpv::Const(c) if c == *expected => {}
                        _ => demote.push((head, i)),
                    }
                }
            }
            if demote.is_empty() {
                return values;
            }
            for key in demote {
                values.insert(key, Cpv::Varies);
            }
        }
    }
}

impl Transformer for ConstantPropagator {
    fn transform(self: Box<Self>, problem: ChcProblem) -> TransformationResult {
        let values = Self::justify(&problem, Self::optimistic_fixpoint(&problem));

        // Justified constant positions per predicate.
        let mut consts: FxHashMap<PredicateId, Vec<(usize, ChcExpr)>> = FxHashMap::default();
        for ((pid, j), value) in &values {
            if let Cpv::Const(c) = value {
                consts.entry(*pid).or_default().push((*j, c.clone()));
            }
        }
        for positions in consts.values_mut() {
            positions.sort_by_key(|(j, _)| *j);
        }
        if consts.is_empty() {
            return TransformationResult {
                problem,
                back_translator: Box::new(IdentityBackTranslator),
            };
        }

        // Rewrite clauses: conjoin `v = c` for body occurrences at constant
        // positions and substitute the constant into the constraint.
        let mut new_problem = ChcProblem::new();
        for pred in problem.predicates() {
            new_problem.declare_predicate(&pred.name, pred.arg_sorts.clone());
        }
        let mut index_map = ClauseIndexMap::new();
        let mut strengthened = 0usize;
        for (idx, clause) in problem.clauses().iter().enumerate() {
            let mut subst: Vec<(ChcVar, ChcExpr)> = Vec::new();
            for (pid, args) in &clause.body.predicates {
                let Some(positions) = consts.get(pid) else {
                    continue;
                };
                for (j, c) in positions {
                    if let Some(ChcExpr::Var(v)) = args.get(*j) {
                        if !subst.iter().any(|(sv, _)| sv == v) {
                            subst.push((v.clone(), c.clone()));
                        }
                    }
                }
            }
            if subst.is_empty() {
                index_map.record_add(&mut new_problem, clause.clone(), idx);
                continue;
            }
            strengthened += 1;
            let mut conjuncts: Vec<ChcExpr> = clause
                .body
                .constraint
                .as_ref()
                .map(|c| c.substitute(&subst).simplify_constants())
                .into_iter()
                .filter(|c| !matches!(c, ChcExpr::Bool(true)))
                .collect();
            // Keep the pinning equalities: they justify head constants in
            // later dataflow rounds and back-translated model verification.
            for (v, c) in &subst {
                conjuncts.push(ChcExpr::eq(ChcExpr::var(v.clone()), c.clone()));
            }
            let new_body = ClauseBody::new(
                clause.body.predicates.clone(),
                Some(ChcExpr::and_all(conjuncts)),
            );
            let mut new_clause = HornClause::new(new_body, clause.head.clone());
            new_clause.action_id = clause.action_id;
            index_map.record_add(&mut new_problem, new_clause, idx);
        }
        if problem.is_fixedpoint_format() {
            new_problem.set_fixedpoint_format();
        }

        if self.verbose {
            safe_eprintln!(
                "CHC condense constant-prop: {} constant argument positions, {} clauses strengthened",
                consts.values().map(Vec::len).sum::<usize>(),
                strengthened
            );
        }

        // Original sorts feed fresh vars when a model interp is missing vars.
        let mut original_sorts: FxHashMap<PredicateId, Vec<crate::ChcSort>> = FxHashMap::default();
        for pred in problem.predicates() {
            original_sorts.insert(pred.id, pred.arg_sorts.clone());
        }

        TransformationResult {
            problem: new_problem,
            back_translator: Box::new(ConstantPropBackTranslator {
                consts,
                original_sorts,
                index_map,
                input_problem: crate::ground_derivation::ground_backtranslation_enabled()
                    .then(|| std::sync::Arc::new(problem)),
            }),
        }
    }
}

/// Back-translator for [`ConstantPropagator`]: strengthens each affected
/// predicate's interpretation with its justified constant-argument equalities
/// so the model satisfies the ORIGINAL (unstrengthened) clauses.
struct ConstantPropBackTranslator {
    consts: FxHashMap<PredicateId, Vec<(usize, ChcExpr)>>,
    original_sorts: FxHashMap<PredicateId, Vec<crate::ChcSort>>,
    index_map: ClauseIndexMap,
    /// INPUT problem, retained for ground back-translation only.
    input_problem: Option<std::sync::Arc<ChcProblem>>,
}

impl BackTranslator for ConstantPropBackTranslator {
    fn translate_ground_derivation(
        &self,
        derivation: &crate::ground_derivation::GroundDerivation,
    ) -> Option<crate::ground_derivation::GroundDerivation> {
        self.index_map
            .ground_translator("constant-propagator", self.input_problem.clone()?)
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
            let mut vars = interp.vars.clone();
            if let Some(sorts) = self.original_sorts.get(pred_id) {
                // Defensive: models normally carry one var per argument.
                while vars.len() < sorts.len() {
                    let i = vars.len();
                    vars.push(ChcVar::new(
                        format!("__cprop_{}_{i}", pred_id.0),
                        sorts[i].clone(),
                    ));
                }
            }
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
        self.index_map.translate_invalidity(witness)
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
