// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl PdrSolver {
    /// Scale factors worth trying, mirroring the unguarded pass: the small
    /// defaults plus any coefficient the problem itself multiplies by.
    pub(super) fn guarded_equality_scale_factors(&self) -> Vec<i128> {
        let mut factors = vec![1i128, 2, 3, 4];
        let mut coeffs = Vec::new();
        for clause in self.problem.clauses() {
            if let Some(ref c) = clause.body.constraint {
                Self::collect_mul_coefficients(c, &mut coeffs);
            }
        }
        for k in coeffs {
            let Some(abs_k) = k.checked_abs() else {
                continue;
            };
            if (2..=20).contains(&abs_k) && !factors.contains(&abs_k) {
                factors.push(abs_k);
            }
        }
        factors
    }

    /// Mode guards for a predicate: `arg == const` tests that (a) occur as an
    /// equality atom in some self-loop's constraint, and (b) test an argument
    /// every self-loop passes through UNCHANGED.
    ///
    /// LOOK IN THE CONSTRAINT, NOT FOR AN `ite`. The front end has already
    /// case-split the source `ite` by the time PDR sees the problem: one
    /// `(ite (= J 1) (+ E F) E)` in the input becomes two self-loop clauses,
    /// one carrying `(= J 1)` and one carrying `(not (= J 1))`, with no `Ite`
    /// node left anywhere. Harvesting `ite` conditions therefore finds nothing —
    /// the branch condition survives as a plain conjunct of the guarded
    /// clause's constraint, which is where this looks.
    ///
    /// The latch requirement is what makes preservation meaningful: if the mode
    /// could change mid-loop the implication's antecedent would differ between
    /// pre- and post-state and the check would be about a different condition.
    pub(super) fn mode_guard_candidates(&self, predicate: PredicateId) -> Vec<ModeGuard> {
        let Some(canonical_vars) = self.canonical_vars(predicate) else {
            return Vec::new();
        };
        let arity = canonical_vars.len();

        // Arguments carried through unchanged by EVERY self-loop.
        let mut latch = vec![true; arity];
        let mut saw_self_loop = false;
        for clause in self.problem.clauses_defining(predicate) {
            if clause.body.predicates.len() != 1 || clause.body.predicates[0].0 != predicate {
                continue;
            }
            let (_, body_args) = &clause.body.predicates[0];
            let crate::ClauseHead::Predicate(_, head_args) = &clause.head else {
                continue;
            };
            if body_args.len() != arity || head_args.len() != arity {
                return Vec::new();
            }
            saw_self_loop = true;
            for idx in 0..arity {
                if !Self::same_variable(&body_args[idx], &head_args[idx]) {
                    latch[idx] = false;
                }
            }
        }
        if !saw_self_loop {
            return Vec::new();
        }

        // `ite` conditions of the form `(= v const)` over a latched argument.
        let mut guards: Vec<ModeGuard> = Vec::new();
        for clause in self.problem.clauses_defining(predicate) {
            if clause.body.predicates.len() != 1 || clause.body.predicates[0].0 != predicate {
                continue;
            }
            let (_, body_args) = &clause.body.predicates[0];
            let Some(ref constraint) = clause.body.constraint else {
                continue;
            };
            let mut atoms = Vec::new();
            Self::collect_constant_equality_atoms(constraint, &mut atoms);
            for (var_expr, value) in atoms {
                for idx in 0..arity {
                    if !latch[idx] {
                        continue;
                    }
                    if !Self::same_variable(&body_args[idx], &var_expr) {
                        continue;
                    }
                    let guard = ModeGuard { idx, value };
                    if !guards.contains(&guard) {
                        guards.push(guard);
                    }
                }
            }
        }
        guards
    }

    /// Whether two expressions are the same variable.
    fn same_variable(lhs: &ChcExpr, rhs: &ChcExpr) -> bool {
        match (lhs, rhs) {
            (ChcExpr::Var(a), ChcExpr::Var(b)) => a.name == b.name,
            _ => false,
        }
    }

    /// Collect every `(= v const)` / `(= const v)` atom in an expression,
    /// returning the variable side paired with the constant.
    ///
    /// Recurses through all operators, so a branch guard survives being buried
    /// under the `and` that the case-split front end builds.
    fn collect_constant_equality_atoms(expr: &ChcExpr, out: &mut Vec<(ChcExpr, i128)>) {
        crate::expr::maybe_grow_expr_stack(|| match expr {
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                match (args[0].as_ref(), args[1].as_ref()) {
                    (v @ ChcExpr::Var(_), ChcExpr::Int(k))
                    | (ChcExpr::Int(k), v @ ChcExpr::Var(_)) => {
                        out.push((v.clone(), *k));
                    }
                    _ => {}
                }
            }
            ChcExpr::Op(_, args) => {
                for a in args {
                    Self::collect_constant_equality_atoms(a, out);
                }
            }
            _ => {}
        });
    }

    /// `B - k*A = c`, optionally guarded, over canonical variables.
    pub(super) fn guarded_scaled_equality_expr(
        canonical_vars: &[ChcVar],
        cand: GuardedEquality,
    ) -> ChcExpr {
        let args = canonical_vars
            .iter()
            .cloned()
            .map(ChcExpr::var)
            .collect::<Vec<_>>();
        Self::guarded_scaled_equality_on_args(&args, cand)
    }

    /// The same implication instantiated on a clause's argument expressions.
    pub(super) fn guarded_scaled_equality_on_args(
        args: &[ChcExpr],
        cand: GuardedEquality,
    ) -> ChcExpr {
        let diff = ChcExpr::sub(
            args[cand.b_idx].clone(),
            ChcExpr::mul(ChcExpr::Int(cand.k), args[cand.a_idx].clone()),
        );
        let body = ChcExpr::eq(diff, ChcExpr::Int(cand.c));
        match cand.guard {
            None => body,
            Some(guard) => ChcExpr::or(
                ChcExpr::not(ChcExpr::eq(
                    args[guard.idx].clone(),
                    ChcExpr::Int(guard.value),
                )),
                body,
            ),
        }
    }
}
