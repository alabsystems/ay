//! Randomized differential test for the [`PropagationEngine`] state machine.
//!
//! The engine's answers are cheap to state and expensive to compute: for a set of constraints and
//! a choice of `only_core`, unit propagation from the empty assignment either reaches a conflict
//! or reaches a unique fixpoint of implied literals. Everything else in the engine --
//! enabling/disabling propagation sets, saving and loading trail levels, poisoning after a
//! deletion, and resetting watcher resume state -- exists only to make those answers cheap to
//! *recompute* as constraints come and go. That machinery is the least directly tested part of
//! the crate and has produced wrong verdicts before (the watcher slack overflow, and
//! `reset_watch()` skipping disabled propagation sets).
//!
//! So: drive random scripts of attach / detach / enable / disable / propagate / RUP operations
//! against the engine, and against a reference implementation that recomputes the fixpoint from
//! scratch every time, and assert that both agree on
//!   * whether propagation conflicts, and
//!   * which literals are implied when it does not.
//!
//! Because unit propagation is a monotone closure, its fixpoint and the *existence* of a conflict
//! do not depend on the propagation order, so the reference can be a straightforward
//! round-robin loop. The literals assigned before a conflict is hit *are* order dependent, so the
//! assignment is only compared when neither side conflicts.
//!
//! Set `VERIPB_DIFF_CASES` to run more than the default number of scripts.

use std::rc::Rc;

use veripb_formula::prelude::*;
use veripb_propagator::propagation_engine::{
    CORE_CLAUSES_CARD, CORE_GENERAL, DERIVED_CLAUSES_CARD, DERIVED_GENERAL, PropagationEngine,
};

/// Index of the propagation set the checker uses for a subproof's extra premises.
const AUTOPROVING: usize = 4;

const NUM_VARS: usize = 8;
const DEFAULT_CASES: usize = 400;
const OPS_PER_CASE: usize = 40;

// ---------------------------------------------------------------------------------------------
// Deterministic PRNG, so a failing case can be replayed from its seed alone.
// ---------------------------------------------------------------------------------------------

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self {
        // Avoid the xorshift fixed point at zero.
        Rng(seed.wrapping_mul(6364136223846793005).wrapping_add(1) | 1)
    }

    fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }

    fn below(&mut self, bound: usize) -> usize {
        (self.next_u64() % (bound as u64)) as usize
    }

    fn chance(&mut self, percent: u64) -> bool {
        self.next_u64() % 100 < percent
    }
}

// ---------------------------------------------------------------------------------------------
// Reference model.
// ---------------------------------------------------------------------------------------------

/// The shape a constraint is stored in, which decides which propagator of a propagation set it
/// lands in. Covered so the scripts exercise the clause and cardinality watchers next to the
/// general PB watcher whose resume state the engine has to reset.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Shape {
    Clause,
    Cardinality,
    GeneralPB,
}

/// A constraint as the reference understands it: `sum of coeff * literal >= degree`, where a term
/// `(coeff, var, negated)` denotes the literal `x{var}` or `~x{var}`.
#[derive(Clone, Debug)]
struct ModelConstraint {
    terms: Vec<(i64, usize, bool)>,
    degree: i64,
    shape: Shape,
}

impl ModelConstraint {
    fn coeff_sum(&self) -> i64 {
        self.terms.iter().map(|term| term.0).sum()
    }

    /// The negation of a PB constraint: `sum ci ~li >= (sum ci) - degree + 1`.
    fn negated(&self) -> ModelConstraint {
        ModelConstraint {
            terms: self
                .terms
                .iter()
                .map(|&(coeff, var, negated)| (coeff, var, !negated))
                .collect(),
            degree: self.coeff_sum() - self.degree + 1,
            // The shape is irrelevant to the reference; the engine builds its own negation.
            shape: Shape::GeneralPB,
        }
    }

    fn to_db_constraint(&self) -> Rc<DBConstraint> {
        let lits: Vec<Lit> = self
            .terms
            .iter()
            .map(|&(_, var, negated)| Lit::from_var(var, negated))
            .collect();
        match self.shape {
            Shape::Clause => Rc::new(DBConstraint::from(Clause::from_lits(lits))),
            Shape::Cardinality => Rc::new(DBConstraint::from(Cardinality::from_lits(
                lits,
                self.degree,
            ))),
            Shape::GeneralPB => {
                let terms: Vec<GeneralPBTerm<i64>> = self
                    .terms
                    .iter()
                    .map(|&(coeff, var, negated)| {
                        GeneralPBTerm::new(coeff, Lit::from_var(var, negated))
                    })
                    .collect();
                Rc::new(DBConstraint::from(PBConstraintEnum::from(
                    GeneralPBConstraint::<i64>::from_terms(terms, self.coeff_sum(), self.degree),
                )))
            }
        }
    }

    fn render(&self) -> String {
        let mut out = String::new();
        for &(coeff, var, negated) in self.terms.iter() {
            out.push_str(&format!(
                "{coeff} {}x{} ",
                if negated { "~" } else { "" },
                var + 1
            ));
        }
        out.push_str(&format!(">= {}", self.degree));
        out
    }
}

/// The result of propagating a constraint set to a fixpoint from the empty assignment.
#[derive(Debug, PartialEq, Eq)]
enum Reference {
    Conflict,
    /// `assignment[v]` is `Some(true)` / `Some(false)` for an implied variable and `None`
    /// otherwise.
    Fixpoint(Vec<Option<bool>>),
}

/// Propagate `constraints` to a fixpoint over `NUM_VARS` variables, from scratch.
///
/// This is deliberately the naive algorithm: recompute every constraint's slack in every round
/// until nothing changes. No watches, no trail, no resume positions.
fn reference_propagate(constraints: &[&ModelConstraint]) -> Reference {
    let mut assignment: Vec<Option<bool>> = vec![None; NUM_VARS];
    loop {
        let mut changed = false;
        for constraint in constraints {
            // Slack: the sum of the coefficients of the non-falsified literals, minus the degree.
            let mut slack = -constraint.degree;
            for &(coeff, var, negated) in constraint.terms.iter() {
                // The literal `x{var}` / `~x{var}` is falsified when its value is false, i.e.
                // when `value != negated` is false, i.e. when `value == negated`.
                let falsified = assignment[var].is_some_and(|value| value == negated);
                if !falsified {
                    slack += coeff;
                }
            }
            if slack < 0 {
                return Reference::Conflict;
            }
            // Every unassigned literal whose coefficient exceeds the slack has to be true.
            for &(coeff, var, negated) in constraint.terms.iter() {
                if assignment[var].is_none() && coeff > slack {
                    assignment[var] = Some(!negated);
                    changed = true;
                }
            }
        }
        if !changed {
            return Reference::Fixpoint(assignment);
        }
    }
}

// ---------------------------------------------------------------------------------------------
// Script generation and execution.
// ---------------------------------------------------------------------------------------------

#[derive(Clone, Debug)]
enum Op {
    /// Attach a fresh constraint to the core or derived set, as `update_propagation_index` does.
    Attach {
        core: bool,
        constraint: ModelConstraint,
    },
    /// Delete an attached constraint, poisoning the trail as `Database::delete_constraint` does.
    Detach { slot: usize },
    /// A RUP check, as `RUPRule::compute` / `Proofgoal::autoprove` runs it.
    Rup {
        only_core: bool,
        conclusion: Option<ModelConstraint>,
        assumption: Option<ModelConstraint>,
    },
    /// Read the saved trail's assignment, as `utils::check_substituted_implication` does. This is
    /// the one checker entry point that leaves the trail extended.
    ProbeAssignment { only_core: bool },
    /// Add a subproof premise and put its set in front, as `SubproofContext::finalize` does.
    EnableAutoproving { constraint: ModelConstraint },
    /// Drop the subproof premises again.
    DisableAutoproving,
}

/// A constraint attached to the engine, with the database id it was registered under.
struct Attached {
    model: ModelConstraint,
    handle: Rc<DBConstraint>,
    core: bool,
    id: usize,
}

struct Case {
    seed: u64,
    ops: Vec<Op>,
}

/// How often each interesting state the generator is *supposed* to reach was
/// actually reached, summed over every script in a run.
///
/// Without these the test asserts only `failures.is_empty()`, which a generator
/// that had stopped producing conflicts, detaches or autoproving sets would
/// satisfy while comparing nothing -- the same hole the three sibling
/// randomized tests in this tree already guard (`rup.rs`'s `accepts > 100`,
/// `width_guards.rs`'s `narrow_accepts > 1000`, `kernel_divergence.rs`'s
/// `trivial_accepts > 100`).
///
/// Every counter is bumped off the **reference's** answer, never the engine's,
/// so a broken engine cannot satisfy a floor by agreeing with itself.
#[derive(Default, Debug)]
struct Counters {
    attach: usize,
    detach: usize,
    detach_skipped: usize,
    probe: usize,
    probe_conflict: usize,
    probe_nonempty_fixpoint: usize,
    rup: usize,
    rup_conflict: usize,
    enable_autoproving: usize,
    disable_autoproving: usize,
    clause: usize,
    cardinality: usize,
    general: usize,
}

fn random_constraint(rng: &mut Rng) -> ModelConstraint {
    // Weighted towards general PB constraints: those are the only ones with watcher resume
    // state (`next_pos`, `next_pos_prop`, `watched_but_not_contributing`), which is the part of
    // the state machine this test is aimed at. Clauses and cardinalities still appear so the
    // clause/cardinality watchers and the `*_CLAUSES_CARD` propagation sets are exercised.
    let shape = match rng.below(5) {
        0 => Shape::Clause,
        1 => Shape::Cardinality,
        _ => Shape::GeneralPB,
    };
    let arity = 1 + rng.below(4);
    let mut vars: Vec<usize> = (0..NUM_VARS).collect();
    // Partial Fisher-Yates: pick `arity` distinct variables.
    for i in 0..arity {
        let j = i + rng.below(NUM_VARS - i);
        vars.swap(i, j);
    }
    let terms: Vec<(i64, usize, bool)> = vars[..arity]
        .iter()
        .map(|&var| {
            let coeff = match shape {
                Shape::Clause | Shape::Cardinality => 1,
                Shape::GeneralPB => 1 + rng.below(5) as i64,
            };
            (coeff, var, rng.chance(50))
        })
        .collect();
    let coeff_sum: i64 = terms.iter().map(|term| term.0).sum();
    // Keep `1 <= degree <= coeff_sum`, so the constraint is neither trivially true nor
    // contradicting and neither is its negation. Those cases are covered by dedicated tests and
    // would only make the reference's job be to re-derive normalization rules.
    let degree = match shape {
        Shape::Clause => 1,
        _ => 1 + rng.below(coeff_sum as usize) as i64,
    };
    ModelConstraint {
        terms,
        degree,
        shape,
    }
}

fn generate_case(seed: u64) -> Case {
    let mut rng = Rng::new(seed);
    let mut ops = Vec::with_capacity(OPS_PER_CASE);
    // Track how many constraints are live so `Detach` can name one.
    let mut live: usize = 0;
    let mut autoproving = false;
    for _ in 0..OPS_PER_CASE {
        let roll = rng.below(100);
        let op = if roll < 25 || live == 0 {
            live += 1;
            Op::Attach {
                core: rng.chance(50),
                constraint: random_constraint(&mut rng),
            }
        } else if roll < 35 {
            let slot = rng.below(live);
            Op::Detach { slot }
        } else if roll < 45 {
            Op::ProbeAssignment {
                only_core: rng.chance(50),
            }
        } else if roll < 55 && !autoproving {
            autoproving = true;
            Op::EnableAutoproving {
                constraint: random_constraint(&mut rng),
            }
        } else if roll < 60 && autoproving {
            autoproving = false;
            Op::DisableAutoproving
        } else {
            Op::Rup {
                only_core: rng.chance(50),
                conclusion: if rng.chance(75) {
                    Some(random_constraint(&mut rng))
                } else {
                    None
                },
                assumption: if rng.chance(20) {
                    Some(random_constraint(&mut rng))
                } else {
                    None
                },
            }
        };
        ops.push(op);
    }
    Case { seed, ops }
}

fn engine_with_checker_sets() -> PropagationEngine {
    let mut engine = PropagationEngine::default();
    for _ in 0..5 {
        engine.add_set();
    }
    engine.enable_back(CORE_CLAUSES_CARD);
    engine.enable_back(CORE_GENERAL);
    engine.enable_back(DERIVED_CLAUSES_CARD);
    engine.enable_back(DERIVED_GENERAL);
    engine
}

/// A mismatch, rendered so the case can be reconstructed by hand.
fn report(case: &Case, op_index: usize, detail: String) -> String {
    let mut out = format!(
        "differential mismatch in case seed {} at operation {}\n  {}\n  script:\n",
        case.seed, op_index, detail
    );
    for (index, op) in case.ops.iter().enumerate().take(op_index + 1) {
        let marker = if index == op_index { "->" } else { "  " };
        let rendered = match op {
            Op::Attach { core, constraint } => format!(
                "attach {} {}",
                if *core { "core" } else { "derived" },
                constraint.render()
            ),
            Op::Detach { slot } => format!("detach slot {slot}"),
            Op::Rup {
                only_core,
                conclusion,
                assumption,
            } => format!(
                "rup only_core={only_core} conclusion={} assumption={}",
                conclusion
                    .as_ref()
                    .map_or("<contradiction>".to_string(), |c| c.render()),
                assumption
                    .as_ref()
                    .map_or("<none>".to_string(), |c| c.render())
            ),
            Op::ProbeAssignment { only_core } => format!("probe assignment only_core={only_core}"),
            Op::EnableAutoproving { constraint } => {
                format!("enable autoproving with {}", constraint.render())
            }
            Op::DisableAutoproving => "disable autoproving".to_string(),
        };
        out.push_str(&format!("  {marker} {index}: {rendered}\n"));
    }
    out
}

/// Run one script against the engine and the reference. Returns a description of the first
/// mismatch, if any.
fn run_case(case: &Case, counters: &mut Counters) -> Option<String> {
    let mut names = VarNameManager::with_capacity(NUM_VARS);
    for i in 0..NUM_VARS {
        names.add_by_name(&format!("x{}", i + 1));
    }

    let mut engine = engine_with_checker_sets();
    let mut attached: Vec<Attached> = Vec::new();
    let mut autoproving: Vec<Rc<DBConstraint>> = Vec::new();
    let mut autoproving_models: Vec<ModelConstraint> = Vec::new();
    let mut next_id = 1usize;

    for (op_index, op) in case.ops.iter().enumerate() {
        match op {
            Op::Attach { core, constraint } => {
                counters.attach += 1;
                match constraint.shape {
                    Shape::Clause => counters.clause += 1,
                    Shape::Cardinality => counters.cardinality += 1,
                    Shape::GeneralPB => counters.general += 1,
                }
                let handle = constraint.to_db_constraint();
                handle.add_id(next_id, *core);
                next_id += 1;
                engine.attach_checker(*core, &handle).unwrap();
                attached.push(Attached {
                    model: constraint.clone(),
                    handle,
                    core: *core,
                    id: next_id - 1,
                });
            }
            Op::Detach { slot } => {
                if attached.is_empty() {
                    counters.detach_skipped += 1;
                    continue;
                }
                counters.detach += 1;
                let entry = attached.remove(slot % attached.len());
                engine
                    .detach_checker(entry.core, &entry.handle, true)
                    .unwrap();
                // Mirror `Database::delete_constraint`: the id stops being valid, which is what
                // `reset_to_valid` reads to decide the trail is stale.
                entry.handle.remove_id(entry.id);
            }
            Op::EnableAutoproving { constraint } => {
                counters.enable_autoproving += 1;
                let handle = constraint.to_db_constraint();
                engine.attach(AUTOPROVING, &handle).unwrap();
                engine.enable_front(AUTOPROVING);
                autoproving.push(handle);
                autoproving_models.push(constraint.clone());
            }
            Op::DisableAutoproving => {
                counters.disable_autoproving += 1;
                engine.disable(AUTOPROVING);
                engine.clear_set(AUTOPROVING);
                autoproving.clear();
                autoproving_models.clear();
            }
            Op::ProbeAssignment { only_core } => {
                let expected = reference_propagate(&enabled_models(
                    &attached,
                    &autoproving_models,
                    *only_core,
                    None,
                ));
                let assignment: Vec<Option<bool>> = {
                    let actual = engine.get_propagated_assignment(NUM_VARS, *only_core);
                    (0..NUM_VARS)
                        .map(|var| match actual.get_value(var) {
                            BoolValue::Assigned(value) => Some(value),
                            BoolValue::Unassigned => None,
                        })
                        .collect()
                };
                let conflicting = engine.get_trail().conflict.is_some();
                counters.probe += 1;
                match &expected {
                    Reference::Conflict => counters.probe_conflict += 1,
                    Reference::Fixpoint(implied) => {
                        if implied.iter().any(Option::is_some) {
                            counters.probe_nonempty_fixpoint += 1;
                        }
                    }
                }
                match (&expected, conflicting) {
                    (Reference::Conflict, true) => {}
                    (Reference::Conflict, false) => {
                        return Some(report(
                            case,
                            op_index,
                            "reference propagation conflicts but the engine's saved trail does not"
                                .to_string(),
                        ));
                    }
                    (Reference::Fixpoint(_), true) => {
                        return Some(report(
                            case,
                            op_index,
                            "the engine's saved trail conflicts but reference propagation reaches \
                             a fixpoint -- the engine invented a conflict"
                                .to_string(),
                        ));
                    }
                    (Reference::Fixpoint(expected), false) => {
                        if *expected != assignment {
                            return Some(report(
                                case,
                                op_index,
                                format!(
                                    "saved trail assignment differs\n    reference: {}\n    engine:    {}",
                                    render_assignment(expected),
                                    render_assignment(&assignment)
                                ),
                            ));
                        }
                    }
                }
            }
            Op::Rup {
                only_core,
                conclusion,
                assumption,
            } => {
                let mut extra: Vec<ModelConstraint> = Vec::new();
                if let Some(conclusion) = conclusion {
                    extra.push(conclusion.negated());
                }
                if let Some(assumption) = assumption {
                    extra.push(assumption.clone());
                }
                let expected = reference_propagate(&enabled_models(
                    &attached,
                    &autoproving_models,
                    *only_core,
                    Some(&extra),
                ));
                let conclusion_handle = conclusion.as_ref().map(|c| c.to_db_constraint());
                let assumption_handles: Vec<Rc<DBConstraint>> = assumption
                    .as_ref()
                    .map(|c| vec![c.to_db_constraint()])
                    .unwrap_or_default();
                let actual = engine
                    .reverse_unit_propagation_check(
                        &names,
                        &assumption_handles,
                        conclusion_handle.as_ref(),
                        *only_core,
                        false,
                        false,
                    )
                    .unwrap()
                    .is_conflict();
                let expected_conflict = expected == Reference::Conflict;
                counters.rup += 1;
                if expected_conflict {
                    counters.rup_conflict += 1;
                }
                if actual != expected_conflict {
                    return Some(report(
                        case,
                        op_index,
                        format!(
                            "RUP verdict differs: reference says {}, engine says {}{}",
                            if expected_conflict {
                                "conflict"
                            } else {
                                "no conflict"
                            },
                            if actual { "conflict" } else { "no conflict" },
                            if actual {
                                " -- the engine accepted a goal unit propagation does not imply"
                            } else {
                                " -- the engine missed a propagation"
                            }
                        ),
                    ));
                }
            }
        }
    }
    None
}

/// The constraints unit propagation may use for a check with this `only_core` setting: every live
/// constraint that is in the core or, when derived constraints are allowed, in either set, plus
/// the enabled subproof premises and any temporary constraints.
fn enabled_models<'a>(
    attached: &'a [Attached],
    autoproving: &'a [ModelConstraint],
    only_core: bool,
    extra: Option<&'a [ModelConstraint]>,
) -> Vec<&'a ModelConstraint> {
    let mut models: Vec<&ModelConstraint> = attached
        .iter()
        .filter(|entry| entry.core || !only_core)
        .map(|entry| &entry.model)
        .collect();
    models.extend(autoproving.iter());
    if let Some(extra) = extra {
        models.extend(extra.iter());
    }
    models
}

fn render_assignment(assignment: &[Option<bool>]) -> String {
    let mut out = String::new();
    for (var, value) in assignment.iter().enumerate() {
        match value {
            Some(true) => out.push_str(&format!("x{} ", var + 1)),
            Some(false) => out.push_str(&format!("~x{} ", var + 1)),
            None => {}
        }
    }
    if out.is_empty() {
        out.push_str("<empty>");
    }
    out
}

#[test]
fn engine_agrees_with_reference_propagation() {
    let cases: usize = std::env::var("VERIPB_DIFF_CASES")
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(DEFAULT_CASES);

    let mut failures = Vec::new();
    let mut counters = Counters::default();
    for seed in 0..cases as u64 {
        let case = generate_case(seed);
        if let Some(failure) = run_case(&case, &mut counters) {
            failures.push(failure);
            if failures.len() >= 3 {
                break;
            }
        }
    }

    // The mismatch report wins: on a real disagreement the loop breaks early,
    // so the counters below are short and would otherwise bury the diagnosis.
    assert!(
        failures.is_empty(),
        "{} of {} randomized engine scripts disagreed with reference propagation:\n\n{}",
        failures.len(),
        cases,
        failures.join("\n")
    );

    // Non-degeneracy. Only for a full-length run: `VERIPB_DIFF_CASES` is also
    // how a single failing seed gets replayed, and `VERIPB_DIFF_CASES=5` must
    // not fail for a reason that says nothing about the engine. The counts are
    // monotone in the seed count, so floors calibrated at 400 hold for every
    // larger run (checked at 2000).
    //
    // Measured 2026-08-23 over the default 400 scripts:
    //   attach 4382  detach 1458 (skipped 88)
    //   probe 1567 (conflict 362, non-empty fixpoint 803)
    //   rup 6783 (conflict 2266)
    //   enable_autoproving 947  disable_autoproving 775
    //   shapes: clause 897, cardinality 917, general 2568
    // Floors are set near half of each, so ordinary reshuffling of the
    // generator passes and a collapse does not. What they catch, concretely:
    // raising NUM_VARS to 200 makes almost every script satisfiable and
    // conflict-free (rup_conflict 126, probe_conflict 14) while the test stays
    // green today -- the engine would still be compared, but only ever on the
    // easy half of its answer.
    if cases >= DEFAULT_CASES {
        let floor = |what: &str, got: usize, want: usize| {
            assert!(
                got >= want,
                "the generator has stopped exercising {what}: {got} in {cases} scripts, \
                 expected at least {want}. Full profile: {counters:?}"
            );
        };
        floor("RUP checks that conflict", counters.rup_conflict, 1000);
        floor(
            "RUP checks that do not conflict",
            counters.rup - counters.rup_conflict,
            2000,
        );
        floor(
            "probes of a conflicting trail",
            counters.probe_conflict,
            150,
        );
        floor(
            "probes reaching a non-empty fixpoint",
            counters.probe_nonempty_fixpoint,
            350,
        );
        floor("detaches actually performed", counters.detach, 600);
        floor(
            "subproof premise sets enabled",
            counters.enable_autoproving,
            400,
        );
        // All three watcher families must stay in play: that is the stated
        // design of `random_constraint`, and each has its own resume state.
        floor("clause-shaped constraints", counters.clause, 300);
        floor("cardinality-shaped constraints", counters.cardinality, 300);
        floor("general PB constraints", counters.general, 1000);
    }
}

/// The reference itself has to be right about the two answers it gives, or the test above is
/// vacuous. These pin it on cases whose fixpoint is obvious by hand.
#[test]
fn reference_propagation_is_sane() {
    let unit = ModelConstraint {
        terms: vec![(1, 0, false)],
        degree: 1,
        shape: Shape::Clause,
    };
    let unit_negated = ModelConstraint {
        terms: vec![(1, 0, true)],
        degree: 1,
        shape: Shape::Clause,
    };
    // `x1 >= 1` implies x1 and nothing else.
    match reference_propagate(&[&unit]) {
        Reference::Fixpoint(assignment) => {
            assert_eq!(assignment[0], Some(true));
            assert!(assignment[1..].iter().all(|value| value.is_none()));
        }
        Reference::Conflict => panic!("a single unit clause does not conflict"),
    }
    // Together with `~x1 >= 1` it does.
    assert_eq!(
        reference_propagate(&[&unit, &unit_negated]),
        Reference::Conflict
    );
    // `3 x1 2 x2 1 x3 >= 4` has slack 2, so only x1 propagates.
    let general = ModelConstraint {
        terms: vec![(3, 0, false), (2, 1, false), (1, 2, false)],
        degree: 4,
        shape: Shape::GeneralPB,
    };
    match reference_propagate(&[&general]) {
        Reference::Fixpoint(assignment) => {
            assert_eq!(assignment[0], Some(true));
            assert_eq!(assignment[1], None);
            assert_eq!(assignment[2], None);
        }
        Reference::Conflict => panic!("slack is 2, so this does not conflict"),
    }
    // Negation flips every literal and takes the complementary degree.
    let negated = general.negated();
    assert_eq!(negated.degree, 6 - 4 + 1);
    assert!(negated.terms.iter().all(|&(_, _, negated)| negated));
}
