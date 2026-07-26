// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ground environment completion.
//!
//! A derivation step over a TRANSFORMED clause carries values for that clause's
//! variables. The corresponding ORIGINAL clause usually has MORE variables: the
//! locals a pass projected away, the constants it pinned, the array "table" it
//! concretized, the argument positions a slicer dropped, the datatype terms a
//! flattener split into columns.
//!
//! Recovering those values is not a search. Their defining equalities are still
//! present in the original clause's own constraint, so ground unit propagation
//! recovers them: repeatedly bind any variable that some equality conjunct
//! determines from already-bound values. Arrays that survive only as reads get
//! reassembled from their ground `select` pins. A projected integer constrained
//! only by ground affine bounds is placed at a satisfying extremum. Whatever
//! remains genuinely unconstrained is filled with a sort default.
//!
//! # Soundness
//!
//! Completion is a HEURISTIC and is allowed to be wrong. Nothing here decides
//! anything: the completed environment is handed to
//! [`super::validate_ground_derivation`], which re-evaluates the entire clause
//! against it. A bad guess makes a constraint evaluate to `false` (rejection)
//! or leaves it indeterminate (rejection). It can never manufacture a verdict.

use super::{eval_ground, is_concrete};
use crate::clause::HornClause;
use crate::smt::SmtValue;
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use num_bigint::BigInt;
use num_integer::Integer;

/// Maximum unit-propagation rounds before giving up.
///
/// Each round binds at least one variable or stops, so this only bounds
/// pathological clauses; ordinary chains converge in a handful of rounds.
const MAX_ROUNDS: usize = 64;

/// Fill in values for every variable of `clause` that `env` does not already
/// bind.
///
/// Returns `true` when the environment ends up total for the clause. A `false`
/// return means some variable could not be given any value at all, so the step
/// cannot possibly ground-evaluate.
pub(crate) fn complete_env_for_clause(
    clause: &HornClause,
    env: &mut FxHashMap<String, SmtValue>,
) -> bool {
    complete_env_for_clause_with_fallback(clause, env, &FxHashMap::default())
}

/// [`complete_env_for_clause`], with a WITNESS FALLBACK consulted at the one
/// point the plain version would fabricate a sort default.
///
/// `fallback` carries values the search actually used, transported down the
/// transform chain and renamed back into this clause's variable space (see
/// `CompositionStep::var_renames`). A variable the clause constrains only
/// through an ITE, a tester or a disjunction is not determined by any equality
/// and is not pinned by any premise, so the plain version gives it an arbitrary
/// sort default — which then falsifies the very conjunct the counterexample
/// satisfied. Consulting the witness first replaces a guess with the value the
/// derivation was actually built from.
///
/// # Why this cannot regress a step that completes today
///
/// The fallback is read at EXACTLY one place: the branch that would otherwise
/// call [`sort_default`]. Equality propagation, array reconstruction and
/// premise seeding all run first and unchanged, and `propagate` never
/// overwrites an existing binding — so every variable the clause's own
/// equalities DETERMINE still gets exactly the value it gets today.
///
/// What changes is confined to the variables that were about to be guessed:
/// they may now be filled from the witness, or from a tester the clause forces,
/// or (via the ITE normalization, which only ever rewrites a term to one the
/// current environment proves it equal to) by ordinary propagation over a
/// conjunct whose determined branch has been resolved. That is exactly the
/// population where the current code is guessing, and a guess that happened to
/// be right is reproduced by an exact rule rather than contradicted.
///
/// # Soundness
///
/// Unchanged from the plain version, and for the same reason: this is value
/// SYNTHESIS, not a relaxed check. A fallback value's provenance is an
/// OVER-APPROXIMATING transformed problem, so it may well be wrong; it is
/// written into an environment that [`super::validate_ground_derivation`] then
/// re-evaluates in full against the ORIGINAL clauses. A wrong value makes some
/// conjunct read `false` or some premise link disagree, and the derivation is
/// REJECTED. It can never manufacture a verdict.
pub(crate) fn complete_env_for_clause_with_fallback(
    clause: &HornClause,
    env: &mut FxHashMap<String, SmtValue>,
    fallback: &FxHashMap<String, SmtValue>,
) -> bool {
    // Drop any binding that is not a genuine concrete value: an `Opaque`
    // placeholder inherited from a transformed model would block propagation
    // AND defeat the validator's groundness check.
    env.retain(|_, value| is_concrete(value));

    let conjuncts: Vec<ChcExpr> = clause
        .body
        .constraint
        .as_ref()
        .map(ChcExpr::collect_conjuncts)
        .unwrap_or_default();

    propagate(&conjuncts, env);
    reconstruct_arrays(&conjuncts, env);
    propagate(&conjuncts, env);

    // Anything still unbound is determined by no equality of this clause
    // (typically a sliced-away dead parameter, a value the transform proved
    // irrelevant, or an existential the clause touches only through an ITE, a
    // tester or a disjunction). Five sources fill those in, in DECREASING
    // order of authority: the witness the search actually used, a value the
    // clause's own testers force, a satisfying extremum forced by ground affine
    // integer bounds, a bounded per-clause solve for the residuals, and finally
    // an arbitrary sort default. The validator decides whether the result was
    // acceptable, so provenance affects completeness only, never soundness.
    //
    // CORRECTION OF A PRIOR RECORD: a bounded solve here was tried before and
    // recorded as useless, on the stated ground that "the executor returns
    // Unknown on those clauses in ~97ms whatever timeout it is given ... the
    // DT+array+BV theory gap the ground path exists to route AROUND". That is
    // false. All 357 constraint-bearing ORIGINAL clauses of the iterator_count
    // archetype are decided SAT by this solver in <=40ms each, z3 concurring on
    // all 357; clause 297 (the DT-tester-over-ITE-over-BV-extract shape that
    // was blamed) decides in <10ms at every timeout from 100ms to 30s. There is
    // no theory gap. The "~97ms whatever timeout" signature was a BUDGET
    // artifact: back-translation runs inside the BMC probe's ScopedSmtDeadline,
    // which by design only ever tightens, so a nested solve got the probe's
    // few-ms remainder no matter what it requested. See `super::witness` for
    // the mechanism and the deadline-scope fix.
    //
    // First exhaust exact inexpensive completion. Besides avoiding needless
    // solver calls, the fixpoint lets a carried array/index value ground an
    // affine local bound before we decide which variables are true residuals.
    let mut filled_names: Vec<String> = Vec::new();
    deterministic_complete_fixpoint(clause, &conjuncts, env, fallback, &mut filled_names);

    // The bounded solve fills ONLY what the carried witness and deterministic
    // rules cannot. Solving for a variable the search already pinned would
    // replace a value that is globally consistent BY CONSTRUCTION (it is the
    // model the counterexample was found in) with a merely locally-satisfying
    // one. Asking SMT to rediscover an affine extremum likewise wastes the
    // per-step budget on the Solidity array shards. So exclude anything
    // `fallback` covers and solve only the true residuals.
    let unbound: Vec<crate::ChcVar> = clause_vars(clause)
        .into_iter()
        .filter(|var| !env.contains_key(&var.name) && !fallback.contains_key(&var.name))
        .collect();
    if super::ground_backtranslation_debug() && !unbound.is_empty() {
        let simplified = simplify_determined_ites_fixpoint(&conjuncts, env);
        let summary: Vec<String> = unbound
            .iter()
            .take(32)
            .map(|var| {
                let disposition = match complete_int_from_ground_bounds(&simplified, var, env) {
                    IntBoundCompletion::NotApplicable => "not-applicable",
                    IntBoundCompletion::Value(_) => "value",
                    IntBoundCompletion::Reject => "reject",
                };
                format!("{}:{:?}:{disposition}", var.name, var.sort)
            })
            .collect();
        super::log_ground_translation_detail(format_args!(
            "complete: {} residual vars before SMT: {summary:?}",
            unbound.len()
        ));
        for var in unbound.iter().take(32) {
            let occurrences: Vec<String> = simplified
                .iter()
                .filter(|conjunct| conjunct.vars().contains(var))
                .take(3)
                .map(|conjunct| bounded_expr_debug(conjunct, 480))
                .collect();
            super::log_ground_translation_detail(format_args!(
                "complete: residual {} occurs in {} shown conjunct(s): {occurrences:?}",
                var.name,
                occurrences.len()
            ));
        }
    }
    if !unbound.is_empty() {
        super::witness::witness_unbound_vars(clause, &conjuncts, &unbound, env);
        propagate(&conjuncts, env);
        reconstruct_arrays(&conjuncts, env);
        deterministic_complete_fixpoint(clause, &conjuncts, env, fallback, &mut filled_names);
    }

    let simplified = simplify_determined_ites_fixpoint(&conjuncts, env);
    let mut defaulted = false;
    for var in clause_vars(clause) {
        if env.contains_key(&var.name) {
            continue;
        }
        // 1. The witness the search actually used, if it reached us (Part 1).
        // 2. Failing that, a value the clause's own testers FORCE (Part 2).
        // 3. Failing that, satisfy ground affine integer bounds exactly.
        // 4. Failing that, an arbitrary sort default, as before.
        let (value, source) = match fallback
            .get(&var.name)
            .filter(|value| is_concrete(value) && value_matches_sort(value, &var.sort))
        {
            Some(value) => (Some(value.clone()), "witness"),
            None => match tester_driven_value(
                &simplified,
                &ChcExpr::var(var.clone()),
                &var.sort,
                env,
                8,
            ) {
                Some(value) => (Some(value), "tester"),
                None => match complete_int_from_ground_bounds(&simplified, &var, env) {
                    IntBoundCompletion::NotApplicable => (sort_default(&var.sort), "default"),
                    IntBoundCompletion::Value(value) => (Some(value), "bound"),
                    IntBoundCompletion::Reject => return false,
                },
            },
        };
        let Some(value) = value else {
            return false;
        };
        if super::ground_backtranslation_debug() {
            filled_names.push(format!("{}<-{source}", var.name));
        }
        env.insert(var.name.clone(), value);
        defaulted = true;
    }
    if !filled_names.is_empty() {
        super::log_ground_translation_detail(format_args!(
            "complete: {} clause vars had no determining equality; filled from \
             witness/tester/bound/sort-default: {:?}",
            filled_names.len(),
            &filled_names[..filled_names.len().min(10)]
        ));
    }
    if defaulted {
        propagate(&conjuncts, env);
    }

    clause_vars(clause)
        .iter()
        .all(|var| env.contains_key(&var.name))
}

fn bounded_expr_debug(expr: &ChcExpr, max_chars: usize) -> String {
    let rendered = format!("{expr:?}");
    let Some((cut, _)) = rendered.char_indices().nth(max_chars) else {
        return rendered;
    };
    format!("{}…", &rendered[..cut])
}

enum IntBoundCompletion {
    /// The variable is not an integer constrained by any conjunct.
    NotApplicable,
    /// A concrete satisfying extremal value.
    Value(SmtValue),
    /// The variable is mentioned, but its bounds are symbolic, ambiguous, or
    /// inconsistent. Never replace that uncertainty with a sort default.
    Reject,
}

enum GroundIntBound {
    Lower(BigInt),
    Upper(BigInt),
}

/// Apply exact, inexpensive completion rules until no new binding appears.
///
/// This deliberately runs before the bounded SMT witness solve. In particular,
/// local-variable elimination commonly projects an affine one-sided bound such
/// as `0 <= (select table i) + 2*x`; once `table` and `i` are ground, choosing
/// the integer extremum is arithmetic, not a reason to spend the whole clause
/// solve budget. A rejected or not-yet-ground rule simply leaves the variable
/// for SMT. Full original-clause validation remains the trust anchor.
fn deterministic_complete_fixpoint(
    clause: &HornClause,
    conjuncts: &[ChcExpr],
    env: &mut FxHashMap<String, SmtValue>,
    fallback: &FxHashMap<String, SmtValue>,
    filled_names: &mut Vec<String>,
) {
    for _ in 0..MAX_ROUNDS {
        let before = env.len();
        let simplified = simplify_determined_ites_fixpoint(conjuncts, env);
        for var in clause_vars(clause) {
            if env.contains_key(&var.name) {
                continue;
            }
            let candidate = fallback
                .get(&var.name)
                .filter(|value| is_concrete(value) && value_matches_sort(value, &var.sort))
                .map(|value| (value.clone(), "witness"))
                .or_else(|| {
                    tester_driven_value(&simplified, &ChcExpr::var(var.clone()), &var.sort, env, 8)
                        .map(|value| (value, "tester"))
                })
                .or_else(
                    || match complete_int_from_ground_bounds(&simplified, &var, env) {
                        IntBoundCompletion::Value(value) => Some((value, "bound")),
                        IntBoundCompletion::NotApplicable | IntBoundCompletion::Reject => None,
                    },
                );
            let Some((value, source)) = candidate else {
                continue;
            };
            if super::ground_backtranslation_debug() {
                filled_names.push(format!("{}<-{source}", var.name));
            }
            env.insert(var.name.clone(), value);
        }
        complete_int_alias_classes(&simplified, clause, env, filled_names);
        propagate(conjuncts, env);
        reconstruct_arrays(conjuncts, env);
        propagate(conjuncts, env);
        if env.len() == before {
            break;
        }
    }
}

/// Complete connected classes of unbound integer variables equated by bare
/// aliases, for example `x = y ∧ 0 <= x ∧ x <= 255`.
///
/// Per-variable completion must reject that shape: while `x` and `y` are both
/// unknown, the equality is a non-bound occurrence and neither variable alone
/// has a justified value. As a CLASS, however, the equality says that both
/// names denote one integer. Replace every class member by one representative,
/// ignore only the alias equalities that become tautologies, and require every
/// other occurrence to be an exact ground affine bound. The intersection then
/// supplies one value for every member.
///
/// This is the shape produced by Solidity preprocessing: eleven independent
/// alias pairs survive in the richer pre-LVE clause while their bounded
/// representative was projected out. Binding the class before propagation
/// avoids a large mixed array/arithmetic SMT query. Any unsupported occurrence,
/// symbolic bound, or empty intersection leaves the whole class untouched for
/// the ordinary fail-closed SMT/validation path.
fn complete_int_alias_classes(
    conjuncts: &[ChcExpr],
    clause: &HornClause,
    env: &mut FxHashMap<String, SmtValue>,
    filled_names: &mut Vec<String>,
) {
    fn find(parent: &mut [usize], index: usize) -> usize {
        let mut root = index;
        while parent[root] != root {
            root = parent[root];
        }
        let mut current = index;
        while parent[current] != current {
            let next = parent[current];
            parent[current] = root;
            current = next;
        }
        root
    }

    fn union(parent: &mut [usize], left: usize, right: usize) {
        let left = find(parent, left);
        let right = find(parent, right);
        if left != right {
            parent[right] = left;
        }
    }

    fn bare_int_alias(conjunct: &ChcExpr) -> Option<(&ChcVar, &ChcVar)> {
        let ChcExpr::Op(ChcOp::Eq, args) = conjunct else {
            return None;
        };
        let [left, right] = args.as_slice() else {
            return None;
        };
        let (ChcExpr::Var(left), ChcExpr::Var(right)) = (left.as_ref(), right.as_ref()) else {
            return None;
        };
        (left.sort == ChcSort::Int && right.sort == ChcSort::Int).then_some((left, right))
    }

    let vars: Vec<ChcVar> = clause_vars(clause)
        .into_iter()
        .filter(|var| var.sort == ChcSort::Int && !env.contains_key(&var.name))
        .collect();
    if vars.len() < 2 {
        return;
    }
    let indices: FxHashMap<String, usize> = vars
        .iter()
        .enumerate()
        .map(|(index, var)| (var.name.clone(), index))
        .collect();
    let mut parent: Vec<usize> = (0..vars.len()).collect();
    for conjunct in conjuncts {
        let Some((left, right)) = bare_int_alias(conjunct) else {
            continue;
        };
        let (Some(&left), Some(&right)) = (indices.get(&left.name), indices.get(&right.name))
        else {
            continue;
        };
        union(&mut parent, left, right);
    }

    let mut classes: FxHashMap<usize, Vec<ChcVar>> = FxHashMap::default();
    for (index, var) in vars.into_iter().enumerate() {
        let root = find(&mut parent, index);
        classes.entry(root).or_default().push(var);
    }
    for mut members in classes.into_values().filter(|members| members.len() > 1) {
        members.sort_by(|left, right| left.name.cmp(&right.name));
        let representative = members[0].clone();
        let substitutions: Vec<(ChcVar, ChcExpr)> = members
            .iter()
            .skip(1)
            .cloned()
            .map(|var| (var, ChcExpr::var(representative.clone())))
            .collect();
        let mut lower: Option<BigInt> = None;
        let mut upper: Option<BigInt> = None;
        let mut saw_bound = false;
        let mut complete = true;

        for conjunct in conjuncts {
            let conjunct_vars = conjunct.vars();
            if !members.iter().any(|member| conjunct_vars.contains(member)) {
                continue;
            }
            if bare_int_alias(conjunct)
                .is_some_and(|(left, right)| members.contains(left) && members.contains(right))
            {
                continue;
            }
            let rewritten = conjunct.substitute(&substitutions);
            let Some(bound) = ground_int_bound(&rewritten, &representative, env) else {
                complete = false;
                break;
            };
            saw_bound = true;
            match bound {
                GroundIntBound::Lower(value) => {
                    if lower.as_ref().is_none_or(|current| value > *current) {
                        lower = Some(value);
                    }
                }
                GroundIntBound::Upper(value) => {
                    if upper.as_ref().is_none_or(|current| value < *current) {
                        upper = Some(value);
                    }
                }
            }
        }

        if !complete
            || !saw_bound
            || lower
                .as_ref()
                .zip(upper.as_ref())
                .is_some_and(|(lo, hi)| lo > hi)
        {
            continue;
        }
        let Some(value) = lower.or(upper).map(SmtValue::int_from_bigint) else {
            continue;
        };
        for member in members {
            if super::ground_backtranslation_debug() {
                filled_names.push(format!("{}<-alias-bound", member.name));
            }
            env.insert(member.name, value.clone());
        }
    }
}

/// Choose a satisfying value for an otherwise-unbound integer constrained by
/// ground affine bounds.
///
/// Lower bounds select their maximum, upper bounds their minimum, and strict
/// bounds are shifted by one because the domain is integral. A mixture is
/// accepted only when the resulting closed interval is non-empty. Any
/// non-bound occurrence or a bound whose other side is not ground rejects
/// completion rather than silently guessing zero.
fn complete_int_from_ground_bounds(
    conjuncts: &[ChcExpr],
    var: &ChcVar,
    env: &FxHashMap<String, SmtValue>,
) -> IntBoundCompletion {
    if var.sort != ChcSort::Int {
        return IntBoundCompletion::NotApplicable;
    }

    let mut lower: Option<BigInt> = None;
    let mut upper: Option<BigInt> = None;
    let mut saw_bound = false;
    let mut saw_other_occurrence = false;
    for conjunct in conjuncts {
        if !conjunct.vars().contains(var) {
            continue;
        }
        let Some(bound) = ground_int_bound(conjunct, var, env) else {
            // An ordering relation that mentions `var` but is not a ground
            // affine bound is symbolic or structurally ambiguous (for example
            // `x >= y` with unbound `y`, or `x*y >= 4`). It must not fall
            // through to the integer sort default.
            if matches!(
                conjunct,
                ChcExpr::Op(ChcOp::Ge | ChcOp::Gt | ChcOp::Le | ChcOp::Lt, _)
            ) {
                return IntBoundCompletion::Reject;
            }
            saw_other_occurrence = true;
            continue;
        };
        saw_bound = true;
        match bound {
            GroundIntBound::Lower(value) => {
                if lower.as_ref().is_none_or(|current| value > *current) {
                    lower = Some(value);
                }
            }
            GroundIntBound::Upper(value) => {
                if upper.as_ref().is_none_or(|current| value < *current) {
                    upper = Some(value);
                }
            }
        }
    }

    if !saw_bound {
        return IntBoundCompletion::NotApplicable;
    }
    // The extremal rule is complete only when every constraint on `var` is one
    // of the bounds it analyzed. A mixture with an equality, disjunction, or
    // other occurrence is not guessed through; the caller rejects this replay.
    if saw_other_occurrence {
        return IntBoundCompletion::Reject;
    }
    if lower
        .as_ref()
        .zip(upper.as_ref())
        .is_some_and(|(lo, hi)| lo > hi)
    {
        return IntBoundCompletion::Reject;
    }
    lower.or(upper).map_or(IntBoundCompletion::Reject, |value| {
        IntBoundCompletion::Value(SmtValue::int_from_bigint(value))
    })
}

fn ground_int_bound(
    conjunct: &ChcExpr,
    var: &ChcVar,
    env: &FxHashMap<String, SmtValue>,
) -> Option<GroundIntBound> {
    let ChcExpr::Op(op @ (ChcOp::Ge | ChcOp::Gt | ChcOp::Le | ChcOp::Lt), args) = conjunct else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }

    // Normalize a linear inequality to `coefficient * var OP target`.
    //
    // LocalVarEliminator projects not only direct `x >= t` bounds, but affine
    // one-sided bounds such as `0 <= (select S u) + x` and
    // `3*x - y < 7`. The old completion recognized only a bare-variable side,
    // so replay reached these Solidity clauses with every shared value ground
    // yet rejected the projected local and fell into a futile whole-clause SMT
    // solve. Mirror the transform's linear class here and choose the exact
    // integer extremum.
    let lhs_coeff = ground_linear_coefficient(args[0].as_ref(), var, env)?;
    let rhs_coeff = ground_linear_coefficient(args[1].as_ref(), var, env)?;
    let coefficient = lhs_coeff - rhs_coeff;
    if coefficient == BigInt::from(0) {
        return None;
    }
    let lhs_zero = eval_ground_int_with_var_zero(args[0].as_ref(), var, env)?;
    let rhs_zero = eval_ground_int_with_var_zero(args[1].as_ref(), var, env)?;
    let mut target = rhs_zero - lhs_zero;

    // Over integers, `a*x > b` is `a*x >= b+1`, and `<` is `<= b-1`.
    let greater = matches!(*op, ChcOp::Ge | ChcOp::Gt);
    match *op {
        ChcOp::Gt => target += 1,
        ChcOp::Lt => target -= 1,
        ChcOp::Ge | ChcOp::Le => {}
        _ => return None,
    }

    let zero = BigInt::from(0);
    if coefficient > zero {
        Some(if greater {
            GroundIntBound::Lower(target.div_ceil(&coefficient))
        } else {
            GroundIntBound::Upper(target.div_floor(&coefficient))
        })
    } else {
        let positive = -coefficient;
        let reflected = -target;
        Some(if greater {
            GroundIntBound::Upper(reflected.div_floor(&positive))
        } else {
            GroundIntBound::Lower(reflected.div_ceil(&positive))
        })
    }
}

/// Coefficient of `var` in a ground-linear integer expression.
///
/// Every subexpression not mentioning `var` must evaluate under `env`; a
/// product may have at most one `var`-bearing factor. Anything nonlinear or
/// indeterminate returns `None` and completion stays fail-closed.
fn ground_linear_coefficient(
    expr: &ChcExpr,
    var: &ChcVar,
    env: &FxHashMap<String, SmtValue>,
) -> Option<BigInt> {
    crate::expr::maybe_grow_expr_stack(|| match expr {
        ChcExpr::Var(found) if found == var => Some(BigInt::from(1)),
        ChcExpr::Op(ChcOp::Add, args) => {
            let mut coefficient = BigInt::from(0);
            for arg in args {
                coefficient += ground_linear_coefficient(arg, var, env)?;
            }
            Some(coefficient)
        }
        ChcExpr::Op(ChcOp::Sub, args) if args.len() == 2 => Some(
            ground_linear_coefficient(&args[0], var, env)?
                - ground_linear_coefficient(&args[1], var, env)?,
        ),
        ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => {
            Some(-ground_linear_coefficient(&args[0], var, env)?)
        }
        ChcExpr::Op(ChcOp::Mul, args) if !args.is_empty() => {
            let mut coefficient: Option<BigInt> = None;
            let mut ground_product = BigInt::from(1);
            for arg in args {
                if arg.vars().contains(var) {
                    if coefficient.is_some() {
                        return None;
                    }
                    coefficient = Some(ground_linear_coefficient(arg, var, env)?);
                } else {
                    ground_product *= eval_ground_int(arg, env)?;
                }
            }
            Some(coefficient.unwrap_or_else(|| BigInt::from(0)) * ground_product)
        }
        _ if !expr.vars().contains(var) => Some(BigInt::from(0)),
        _ => None,
    })
}

fn eval_ground_int_with_var_zero(
    expr: &ChcExpr,
    var: &ChcVar,
    env: &FxHashMap<String, SmtValue>,
) -> Option<BigInt> {
    let mut zero_env = env.clone();
    zero_env.insert(var.name.clone(), SmtValue::Int(0));
    eval_ground_int(expr, &zero_env)
}

fn eval_ground_int(expr: &ChcExpr, env: &FxHashMap<String, SmtValue>) -> Option<BigInt> {
    crate::expr::maybe_grow_expr_stack(|| match expr {
        ChcExpr::Int(value) => Some(BigInt::from(*value)),
        ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => Some(-eval_ground_int(&args[0], env)?),
        ChcExpr::Op(ChcOp::Add, args) => {
            let mut sum = BigInt::from(0);
            for arg in args {
                sum += eval_ground_int(arg, env)?;
            }
            Some(sum)
        }
        ChcExpr::Op(ChcOp::Sub, args) if !args.is_empty() => {
            let mut value = eval_ground_int(&args[0], env)?;
            if args.len() == 1 {
                return Some(-value);
            }
            for arg in &args[1..] {
                value -= eval_ground_int(arg, env)?;
            }
            Some(value)
        }
        ChcExpr::Op(ChcOp::Mul, args) => {
            let mut product = BigInt::from(1);
            for arg in args {
                product *= eval_ground_int(arg, env)?;
            }
            Some(product)
        }
        // Variables, array reads, and any other ground integer atom stay on
        // the canonical evaluator. Only arithmetic trees are intercepted above
        // so their intermediate values cannot overflow i128.
        _ => match eval_ground(expr, env)? {
            SmtValue::Int(value) => Some(BigInt::from(value)),
            SmtValue::BigInt(value) => Some(value.as_ref().clone()),
            _ => None,
        },
    })
}

/// Instantiate a clause's body-argument variables from the premises that
/// justify them.
///
/// A clause variable that no equality in the clause determines is not
/// arbitrary when it sits in a body-predicate argument: the derivation says
/// that position holds whatever the premise derived for the matching head
/// argument. Completing it with a SORT DEFAULT instead picks an instantiation
/// the derivation never made, and the two sides of the same link then disagree
/// as soon as either one is known — the argument check reports a mismatch that
/// is an artifact of the completion, not of the counterexample.
///
/// So seed these positions from the premise first, and leave the sort default
/// for what remains genuinely free.
///
/// Only bare-variable argument positions are seeded, and only when the
/// environment does not already bind them: a value the clause's own equalities
/// determined always wins, and a compound argument expression is left to the
/// validator (its value is a function of variables seeded elsewhere).
///
/// SOUNDNESS: this instantiates free variables, it does not weaken any check.
/// The clause's constraint is still evaluated under the result, both clauses in
/// the link are still re-evaluated independently, and a premise whose head
/// argument is a compound expression is still compared value-for-value. Making
/// a free position agree with its premise is what a derivation IS; it cannot
/// make an unsatisfiable clause fire.
pub(crate) fn seed_env_from_premises(
    clause: &HornClause,
    premises: &[usize],
    steps: &[super::GroundDerivationStep],
    clauses: &[HornClause],
    env: &mut FxHashMap<String, SmtValue>,
) {
    for (position, (_, args)) in clause.body.predicates.iter().enumerate() {
        let Some(premise) = premises.get(position).and_then(|idx| steps.get(*idx)) else {
            continue;
        };
        let Some(premise_clause) = clauses.get(premise.clause_index) else {
            continue;
        };
        let crate::ClauseHead::Predicate(_, head_args) = &premise_clause.head else {
            continue;
        };
        for (arg, head_arg) in args.iter().zip(head_args.iter()) {
            let ChcExpr::Var(var) = arg else {
                continue;
            };
            if env.contains_key(&var.name) {
                continue;
            }
            if let Some(value) = eval_ground(head_arg, &premise.env) {
                env.insert(var.name.clone(), value);
            }
        }
    }
}

/// All variables occurring anywhere in the clause (body constraint, body
/// predicate arguments, head arguments).
fn clause_vars(clause: &HornClause) -> Vec<crate::ChcVar> {
    let mut vars = clause.body.vars();
    for var in clause.head.vars() {
        if !vars.contains(&var) {
            vars.push(var);
        }
    }
    vars
}

/// Bind variables determined by ground equality conjuncts, to a fixpoint.
///
/// A conjunct binds `v` when it is an equality with `Var(v)` unbound on one
/// side and a fully evaluable expression on the other. Later conflicting
/// equalities are simply left alone — they become concretely false and the
/// validator rejects the step.
fn propagate(conjuncts: &[ChcExpr], env: &mut FxHashMap<String, SmtValue>) {
    for _ in 0..MAX_ROUNDS {
        let mut progressed = false;
        for conjunct in conjuncts {
            let ChcExpr::Op(ChcOp::Eq, args) = conjunct else {
                continue;
            };
            if args.len() != 2 {
                continue;
            }
            for (candidate, source) in [(&args[0], &args[1]), (&args[1], &args[0])] {
                match candidate.as_ref() {
                    ChcExpr::Var(var) => {
                        if env.contains_key(&var.name) {
                            continue;
                        }
                        if let Some(value) = eval_ground(source, env) {
                            env.insert(var.name.clone(), value);
                            progressed = true;
                        }
                    }
                    // `v = C(f0, f1, …)` determines the FIELDS once `v` is
                    // known, not just `v` once the fields are.
                    candidate @ ChcExpr::FuncApp(..) => {
                        if let Some(value) = eval_ground(source, env) {
                            progressed |= decompose_constructor(candidate, &value, env, 8);
                        }
                    }
                    _ => {}
                }
            }
        }
        if !progressed {
            return;
        }
    }
}

/// Bind the variables a datatype equality determines by DECONSTRUCTION.
///
/// Forward propagation only reads a constructor application: given every field,
/// it builds the value. A clause that REBUILDS a datatype term —
/// `v = C(f0, f1, …)` — also runs the other way: constructors are injective, so
/// a known `v` determines every `fi` exactly. This is the shape a flattened
/// problem's original clauses take when they reassemble a datatype from the
/// columns the flattener split it into, and without the inverse rule those
/// column variables look "unconstrained" and get sort defaults that then
/// contradict the very equality that defined them.
///
/// Only genuine constructor applications of the expression's own datatype sort
/// are decomposed, and only against a matching constructor tag — a value built
/// by a DIFFERENT constructor means the equality is false, which is the
/// validator's business to report, not something to bind variables from.
///
/// Exact, not heuristic: every binding it makes is entailed by the conjunct.
fn decompose_constructor(
    expr: &ChcExpr,
    value: &SmtValue,
    env: &mut FxHashMap<String, SmtValue>,
    fuel: usize,
) -> bool {
    if fuel == 0 {
        return false;
    }
    match expr {
        ChcExpr::Var(var) => {
            if env.contains_key(&var.name) || !is_concrete(value) {
                return false;
            }
            env.insert(var.name.clone(), value.clone());
            true
        }
        ChcExpr::FuncApp(name, ChcSort::Datatype { constructors, .. }, args) => {
            let SmtValue::Datatype(ctor, fields) = value else {
                return false;
            };
            if ctor != name || fields.len() != args.len() {
                return false;
            }
            if !constructors
                .iter()
                .any(|c| &c.name == name && c.selectors.len() == args.len())
            {
                return false;
            }
            let mut progressed = false;
            for (arg, field) in args.iter().zip(fields.iter()) {
                progressed |= decompose_constructor(arg, field, env, fuel - 1);
            }
            progressed
        }
        _ => false,
    }
}

/// Rebuild array-sorted variables that the clause only ever reads at ground
/// indices.
///
/// This is the inverse of ground-table read concretization: the pass proved a
/// read-only table is touched only through positive ground pins
/// `(= (select T i) v)` and replaced those reads by their values. The original
/// clause still carries the pins, so the table is recovered exactly by
/// collecting them into an `ArrayMap`.
///
/// The default element is a sort default. That is a guess about indices the
/// clause never reads — which is precisely why it cannot matter to any
/// constraint the validator then evaluates, and if it does, the step is
/// rejected.
fn reconstruct_arrays(conjuncts: &[ChcExpr], env: &mut FxHashMap<String, SmtValue>) {
    let mut pins: FxHashMap<String, Vec<(SmtValue, SmtValue)>> = FxHashMap::default();
    let mut sorts: FxHashMap<String, ChcSort> = FxHashMap::default();

    for conjunct in conjuncts {
        let ChcExpr::Op(ChcOp::Eq, args) = conjunct else {
            continue;
        };
        if args.len() != 2 {
            continue;
        }
        for (read, source) in [(&args[0], &args[1]), (&args[1], &args[0])] {
            let ChcExpr::Op(ChcOp::Select, select_args) = read.as_ref() else {
                continue;
            };
            if select_args.len() != 2 {
                continue;
            }
            let ChcExpr::Var(array_var) = select_args[0].as_ref() else {
                continue;
            };
            let (Some(index), Some(value)) =
                (eval_ground(&select_args[1], env), eval_ground(source, env))
            else {
                continue;
            };
            sorts.insert(array_var.name.clone(), array_var.sort.clone());
            pins.entry(array_var.name.clone())
                .or_default()
                .push((index, value));
        }
    }

    for (name, entries) in pins {
        match env.get(&name) {
            // The environment carries a value for this table already — usually
            // one transported down from the transformed problem. It is only
            // usable if it AGREES with every ground pin the original clause
            // states. When it does, leave it exactly as it is.
            //
            // When it does NOT, the carried value is stale: the concretizing
            // pass replaced this clause's reads by their values, which left the
            // table unconstrained in the transformed problem, so the model was
            // free to assign it anything (in practice an empty map over the
            // sort default). The pins are entailed by the original clause, so
            // applying them as point overrides is EXACT recovery, not a guess —
            // and it can only affect steps that are rejected today, since a pin
            // the carried value contradicts makes that conjunct read `false`.
            Some(existing) => {
                let disagrees = entries.iter().any(|(index, value)| {
                    !matches!(
                        crate::expr::eval_array_select(existing, index),
                        Some(ref found) if found == value
                    )
                });
                if !disagrees {
                    continue;
                }
                let mut refined = existing.clone();
                for (index, value) in entries {
                    refined = array_point_override(refined, index, value);
                }
                super::log_ground_translation_detail(format_args!(
                    "complete: table {name} disagreed with the clause's own ground pins; \
                     refined to satisfy them"
                ));
                env.insert(name, refined);
            }
            None => {
                let element_sort = match sorts.get(&name) {
                    Some(ChcSort::Array(_, element)) => (**element).clone(),
                    _ => continue,
                };
                let Some(default) = sort_default(&element_sort) else {
                    continue;
                };
                env.insert(
                    name,
                    SmtValue::ArrayMap {
                        default: Box::new(default),
                        entries,
                    },
                );
            }
        }
    }
}

/// Maximum ITE-normalization rounds. Each round either rewrites at least one
/// ITE away or stops, so this only bounds pathological nesting.
const MAX_ITE_ROUNDS: usize = 8;

/// True when `value` inhabits `sort`.
///
/// Used to reject a witness value whose sort does not match the variable it
/// would be written to — a stale or mis-flattened model entry (a datatype value
/// left over from a truncated flattening, say). Such an entry is simply
/// ignored, reproducing the previous behavior for that variable, rather than
/// being written where a differently-sorted value belongs.
fn value_matches_sort(value: &SmtValue, sort: &ChcSort) -> bool {
    match (value, sort) {
        (SmtValue::Bool(_), ChcSort::Bool) => true,
        (SmtValue::Int(_) | SmtValue::BigInt(_), ChcSort::Int | ChcSort::Real) => true,
        (SmtValue::Real(_), ChcSort::Real) => true,
        (SmtValue::BitVec(_, width), ChcSort::BitVec(expected)) => width == expected,
        (SmtValue::ConstArray(default), ChcSort::Array(_, element)) => {
            value_matches_sort(default, element)
        }
        (SmtValue::ArrayMap { default, entries }, ChcSort::Array(index, element)) => {
            value_matches_sort(default, element)
                && entries.iter().all(|(key, entry)| {
                    value_matches_sort(key, index) && value_matches_sort(entry, element)
                })
        }
        (SmtValue::Datatype(ctor, fields), ChcSort::Datatype { constructors, .. }) => {
            constructors.iter().any(|constructor| {
                constructor.name == *ctor
                    && constructor.selectors.len() == fields.len()
                    && constructor
                        .selectors
                        .iter()
                        .zip(fields.iter())
                        .all(|(selector, field)| value_matches_sort(field, &selector.sort))
            })
        }
        _ => false,
    }
}

/// Rewrite every ITE whose condition the environment already determines to the
/// branch that condition selects, to a fixpoint.
///
/// EXACT, not heuristic: each rewrite replaces a term by one the current
/// environment proves it equal to, so the rewritten conjunct set has the same
/// truth value under this environment as the original. Nothing is bound here;
/// the value of the rewrite is that it EXPOSES structure the other rules read.
/// `(= out (is-Some (ite cond x None)))` becomes `(= out (is-Some x))` once
/// `cond` is determined, which is what lets the tester rule see a subject it
/// can instantiate — and `(= v (ite c a b))` becomes `(= v a)`, which the
/// existing propagation loop then consumes with no new rule at all.
///
/// Conditions whose value is still unknown are left alone, so this can only run
/// forward as the environment grows.
fn simplify_determined_ites_fixpoint(
    conjuncts: &[ChcExpr],
    env: &mut FxHashMap<String, SmtValue>,
) -> Vec<ChcExpr> {
    let mut current: Vec<ChcExpr> = conjuncts.to_vec();
    for _ in 0..MAX_ITE_ROUNDS {
        let next: Vec<ChcExpr> = current
            .iter()
            .map(|conjunct| simplify_determined_ites(conjunct, env, 16))
            .collect();
        if next == current {
            break;
        }
        current = next;
        // A resolved branch can turn `(= v (ite …))` into a plain defining
        // equality; let the existing loop bind whatever that unlocks, which in
        // turn may determine the next condition.
        propagate(&current, env);
    }
    current
}

fn simplify_determined_ites(
    expr: &ChcExpr,
    env: &FxHashMap<String, SmtValue>,
    fuel: usize,
) -> ChcExpr {
    if fuel == 0 {
        return expr.clone();
    }
    match expr {
        ChcExpr::Op(ChcOp::Ite, args) if args.len() == 3 => {
            let condition = simplify_determined_ites(&args[0], env, fuel - 1);
            let then_branch = simplify_determined_ites(&args[1], env, fuel - 1);
            let else_branch = simplify_determined_ites(&args[2], env, fuel - 1);
            match eval_ground(&condition, env) {
                Some(SmtValue::Bool(true)) => then_branch,
                Some(SmtValue::Bool(false)) => else_branch,
                _ => ChcExpr::Op(
                    ChcOp::Ite,
                    vec![
                        std::sync::Arc::new(condition),
                        std::sync::Arc::new(then_branch),
                        std::sync::Arc::new(else_branch),
                    ],
                ),
            }
        }
        ChcExpr::Op(op, args) => ChcExpr::Op(
            *op,
            args.iter()
                .map(|arg| std::sync::Arc::new(simplify_determined_ites(arg, env, fuel - 1)))
                .collect(),
        ),
        ChcExpr::FuncApp(name, sort, args) => ChcExpr::FuncApp(
            name.clone(),
            sort.clone(),
            args.iter()
                .map(|arg| std::sync::Arc::new(simplify_determined_ites(arg, env, fuel - 1)))
                .collect(),
        ),
        _ => expr.clone(),
    }
}

/// A datatype-tester fact the clause FORCES: `(is-C subject)` must hold
/// (`expected` true) or must not hold (`expected` false).
struct TesterFact<'a> {
    constructor: &'a str,
    subject: &'a ChcExpr,
    expected: bool,
}

/// Read the tester facts a clause's top-level conjuncts force.
///
/// A clause body is a CONJUNCTION, so every top-level conjunct is forced true.
/// Three shapes carry a tester: the bare tester, its negation, and an equality
/// against an already-determined Boolean. Nothing else is read — in particular
/// a tester under a disjunction is NOT a forced fact and is skipped.
fn tester_facts<'a>(
    conjuncts: &'a [ChcExpr],
    env: &FxHashMap<String, SmtValue>,
) -> Vec<TesterFact<'a>> {
    fn as_tester(expr: &ChcExpr) -> Option<(&str, &ChcExpr)> {
        let ChcExpr::FuncApp(name, ChcSort::Bool, args) = expr else {
            return None;
        };
        if args.len() != 1 {
            return None;
        }
        Some((name.strip_prefix("is-")?, args[0].as_ref()))
    }

    let mut facts = Vec::new();
    for conjunct in conjuncts {
        if let Some((constructor, subject)) = as_tester(conjunct) {
            facts.push(TesterFact {
                constructor,
                subject,
                expected: true,
            });
            continue;
        }
        if let ChcExpr::Op(ChcOp::Not, args) = conjunct {
            if args.len() == 1 {
                if let Some((constructor, subject)) = as_tester(&args[0]) {
                    facts.push(TesterFact {
                        constructor,
                        subject,
                        expected: false,
                    });
                }
            }
            continue;
        }
        if let ChcExpr::Op(ChcOp::Eq, args) = conjunct {
            if args.len() != 2 {
                continue;
            }
            for (tester_side, value_side) in [(&args[0], &args[1]), (&args[1], &args[0])] {
                let Some((constructor, subject)) = as_tester(tester_side) else {
                    continue;
                };
                if let Some(SmtValue::Bool(expected)) = eval_ground(value_side, env) {
                    facts.push(TesterFact {
                        constructor,
                        subject,
                        expected,
                    });
                }
            }
        }
    }
    facts
}

/// Synthesize a value for `subject` from the tester facts the clause forces.
///
/// A variable that occurs only inside a tester (or inside an ITE that a tester
/// then inspects) is determined by no equality and pinned by no premise, so
/// completion would otherwise give it an arbitrary sort default. But the clause
/// is not silent about it: a forced `(is-C v)` says v's constructor tag is
/// exactly `C`, and a forced `¬(is-C v)` says it is anything else. Building the
/// demanded constructor is the unique tag the conjunct admits; the FIELDS stay
/// free, and are refined by recursing on nested facts about `(sel v)` before
/// falling back to their own defaults.
///
/// Deliberately abstains — returns `None`, leaving [`sort_default`] to run —
/// whenever the facts do not single out a tag:
///
/// * two forced-true testers naming DIFFERENT constructors: the clause is
///   contradictory, and that is the validator's finding to report, not
///   something to paper over by picking one;
/// * a forced-false tester on the only constructor of the datatype: likewise
///   unsatisfiable;
/// * no fact at all about this subject.
///
/// SOUNDNESS: pure ground reasoning, no search, and synthesis only. Every value
/// it produces is re-evaluated by [`super::validate_ground_derivation`] against
/// the ORIGINAL clauses. Instantiating a tag the clause demands cannot make an
/// unsatisfiable clause fire — if the rest of the clause disagrees with the
/// synthesized value, the disagreeing conjunct reads `false` and the step is
/// REJECTED.
fn tester_driven_value(
    conjuncts: &[ChcExpr],
    subject: &ChcExpr,
    sort: &ChcSort,
    env: &FxHashMap<String, SmtValue>,
    fuel: usize,
) -> Option<SmtValue> {
    if fuel == 0 {
        return None;
    }
    let ChcSort::Datatype { constructors, .. } = sort else {
        return None;
    };

    let facts = tester_facts(conjuncts, env);
    let mut required: Option<&str> = None;
    let mut excluded: Vec<&str> = Vec::new();
    for fact in &facts {
        if fact.subject != subject {
            continue;
        }
        if fact.expected {
            match required {
                // Contradictory demands: abstain, let the validator reject.
                Some(existing) if existing != fact.constructor => return None,
                _ => required = Some(fact.constructor),
            }
        } else {
            excluded.push(fact.constructor);
        }
    }
    if let Some(required) = required {
        if excluded.contains(&required) {
            return None;
        }
    }

    let constructor = match required {
        Some(name) => constructors.iter().find(|c| c.name == name)?,
        None => {
            if excluded.is_empty() {
                return None;
            }
            constructors
                .iter()
                .find(|c| !excluded.contains(&c.name.as_str()))?
        }
    };

    let mut fields = Vec::with_capacity(constructor.selectors.len());
    for selector in &constructor.selectors {
        // A nested fact about `(sel v)` refines that field; otherwise the field
        // is genuinely free and takes its own default.
        let selector_app = ChcExpr::FuncApp(
            selector.name.clone(),
            selector.sort.clone(),
            vec![std::sync::Arc::new(subject.clone())],
        );
        let field = tester_driven_value(conjuncts, &selector_app, &selector.sort, env, fuel - 1)
            .or_else(|| sort_default(&selector.sort))?;
        fields.push(field);
    }
    Some(SmtValue::Datatype(constructor.name.clone(), fields))
}

/// Override one index of an array value, mirroring `store` semantics (last
/// entry wins, so appending is enough).
fn array_point_override(array: SmtValue, index: SmtValue, value: SmtValue) -> SmtValue {
    match array {
        SmtValue::ConstArray(default) => SmtValue::ArrayMap {
            default,
            entries: vec![(index, value)],
        },
        SmtValue::ArrayMap {
            default,
            mut entries,
        } => {
            entries.retain(|(key, _)| key != &index);
            entries.push((index, value));
            SmtValue::ArrayMap { default, entries }
        }
        // Not an array value at all; a pin cannot be applied to it. Leave the
        // carried value alone and let the validator report the disagreement.
        other => other,
    }
}

/// A canonical value of `sort`, used only for variables no equality constrains.
///
/// Returns `None` for sorts with no obvious inhabitant (uninterpreted sorts,
/// datatypes with no nullary-reachable constructor within the recursion bound),
/// which makes completion fail closed rather than fabricate.
pub(crate) fn sort_default(sort: &ChcSort) -> Option<SmtValue> {
    sort_default_bounded(sort, 8)
}

fn sort_default_bounded(sort: &ChcSort, fuel: usize) -> Option<SmtValue> {
    if fuel == 0 {
        return None;
    }
    match sort {
        ChcSort::Bool => Some(SmtValue::Bool(false)),
        ChcSort::Int => Some(SmtValue::Int(0)),
        ChcSort::Real => Some(SmtValue::Int(0)),
        ChcSort::BitVec(width) => Some(SmtValue::BitVec(0, *width)),
        ChcSort::Array(_, element) => Some(SmtValue::ConstArray(Box::new(sort_default_bounded(
            element,
            fuel - 1,
        )?))),
        ChcSort::Datatype { constructors, .. } => {
            // Prefer a nullary constructor; otherwise build the shallowest
            // constructor whose fields all have defaults.
            let nullary = constructors
                .iter()
                .find(|constructor| constructor.selectors.is_empty());
            if let Some(constructor) = nullary {
                return Some(SmtValue::Datatype(constructor.name.clone(), Vec::new()));
            }
            for constructor in constructors.iter() {
                let mut fields = Vec::with_capacity(constructor.selectors.len());
                let mut ok = true;
                for field in &constructor.selectors {
                    match sort_default_bounded(&field.sort, fuel - 1) {
                        Some(value) => fields.push(value),
                        None => {
                            ok = false;
                            break;
                        }
                    }
                }
                if ok {
                    return Some(SmtValue::Datatype(constructor.name.clone(), fields));
                }
            }
            None
        }
        _ => None,
    }
}

/// Recover values determined by `clause`'s own equalities WITHOUT filling
/// anything in by default.
///
/// Used where a guessed value would be actively misleading rather than merely
/// checkable: recovering the fresh intermediates an inliner existentially
/// projected out of a surviving clause. Those intermediates are determined by
/// the composite clause's linking equalities given its endpoints, so
/// propagation finds them; a sort default would instead silently name a
/// different derivation.
pub(crate) fn propagate_env_for_clause(clause: &HornClause, env: &mut FxHashMap<String, SmtValue>) {
    env.retain(|_, value| is_concrete(value));
    let conjuncts = clause
        .body
        .constraint
        .as_ref()
        .map(ChcExpr::collect_conjuncts)
        .unwrap_or_default();
    propagate(&conjuncts, env);
    reconstruct_arrays(&conjuncts, env);
    propagate(&conjuncts, env);
}
