// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact, memoized expansion of Diophantine substitutions (D3,
//! 2026-09-23 hunt).
//!
//! The elimination loop records each eliminated variable's substitution over
//! the variables that are live at that moment, and never rewrites an earlier
//! substitution when a later step eliminates one of its variables. The
//! substitution set is therefore a DAG, not Griggio's solved form: the full
//! expression of a variable is the composition of substitutions along every
//! path down to the variables that have none. Walking that DAG as a TREE —
//! one worklist pop per path — costs exponentially in its depth (the hunt
//! measured 4,575 to 246,324 pops on its witnesses), which is why the old walk
//! stopped after 100 pops. It then returned the PARTIAL sum as if it were the
//! whole expansion. A partial sum's coefficient GCD can exceed 1 where the true
//! one is 1, so the modular check derived a false `var ≡ r (mod g)` and
//! reported every asserted literal as a conflict: a wrong `unsat`. The same
//! partial sums entered the cached substitutions that bound propagation reads.
//!
//! Here every substituted variable is expanded ONCE, bottom-up, and each
//! variable that depends on it reuses that expansion — the solved form z3's
//! `dioph_eq.cpp` maintains, computed on demand. The result is exact or absent:
//! a work budget or coefficient-size ceiling that runs out makes the expansion
//! `None`, never a partial sum, and every caller reads `None` as "no claim".

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use num_bigint::BigInt;
use num_traits::Zero;

/// Coefficient multiply-adds one expansion pass may spend before every
/// expansion it has not finished becomes `None`. Memoized expansion is
/// polynomial (substitutions × width × leaves); the budget only bounds a
/// pathological system, and exhausting it costs completeness, never soundness.
const EXPANSION_WORK_BUDGET: usize = 2_000_000;

/// Largest bit length a coefficient or constant of an expansion may reach.
/// Composition multiplies coefficients along a path, so a deep chain can grow
/// them without bound; past this size the expansion is abandoned (`None`).
const EXPANSION_MAX_BITS: u64 = 1 << 16;

/// Which variables an expansion stops at.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum ExpansionPolicy {
    /// Stop at original variables (`< num_original_vars`), even ones that are
    /// themselves substituted; expand substituted fresh variables. A fresh
    /// variable with no substitution is a free parameter, and an expression
    /// that needs one is refused (#4830): the caller wants the variable in
    /// terms of original variables only.
    StopAtOriginals { num_original_vars: usize },
    /// Expand every substituted variable, original or fresh, and keep every
    /// unsubstituted one (original or free fresh parameter) as a leaf. Every
    /// leaf is integer-valued, so the coefficient GCD of the result is a valid
    /// modulus for the expanded variable.
    FreeParams,
}

/// What an expansion does with one dependency.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DepRole {
    /// Keep the variable as a term of the result.
    Leaf,
    /// Replace the variable by its own (memoized) expansion.
    Expand,
    /// The result cannot be expressed under this policy.
    Refuse,
}

/// A linear form `constant + Σ coeff * var` (zero coefficients removed).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct LinearForm {
    pub(super) coeffs: HashMap<usize, BigInt>,
    pub(super) constant: BigInt,
}

type SubstitutionMap = HashMap<usize, (HashMap<usize, BigInt>, BigInt)>;

/// Memoized expander over one solver's substitution DAG.
pub(super) struct SubstitutionExpander<'a> {
    substitutions: &'a SubstitutionMap,
    policy: ExpansionPolicy,
    /// `Some(form)` = exact expansion of the variable's substitution;
    /// `None` = no exact expansion exists under the policy or the budget.
    memo: HashMap<usize, Option<LinearForm>>,
    work_left: usize,
}

impl<'a> SubstitutionExpander<'a> {
    pub(super) fn new(substitutions: &'a SubstitutionMap, policy: ExpansionPolicy) -> Self {
        Self::with_budget(substitutions, policy, EXPANSION_WORK_BUDGET)
    }

    pub(super) fn with_budget(
        substitutions: &'a SubstitutionMap,
        policy: ExpansionPolicy,
        work_budget: usize,
    ) -> Self {
        Self {
            substitutions,
            policy,
            memo: HashMap::default(),
            work_left: work_budget,
        }
    }

    fn role(&self, var: usize) -> DepRole {
        let substituted = self.substitutions.contains_key(&var);
        match self.policy {
            ExpansionPolicy::StopAtOriginals { num_original_vars } => {
                if var < num_original_vars {
                    DepRole::Leaf
                } else if substituted {
                    DepRole::Expand
                } else {
                    DepRole::Refuse
                }
            }
            ExpansionPolicy::FreeParams => {
                if substituted {
                    DepRole::Expand
                } else {
                    DepRole::Leaf
                }
            }
        }
    }

    /// The exact expansion of `var`'s substitution, or `None` when `var` has
    /// no substitution or no exact expansion exists within the budget.
    pub(super) fn expand(&mut self, var: usize) -> Option<&LinearForm> {
        self.fill(var);
        self.memo.get(&var).and_then(Option::as_ref)
    }

    /// Expand `root` and every substituted variable below it, children first
    /// (iterative post-order: the DAG can be as deep as the substitution
    /// count).
    fn fill(&mut self, root: usize) {
        if self.memo.contains_key(&root) || !self.substitutions.contains_key(&root) {
            return;
        }
        let mut in_progress: HashSet<usize> = HashSet::default();
        let mut stack: Vec<(usize, bool)> = vec![(root, false)];
        while let Some((var, children_done)) = stack.pop() {
            if self.memo.contains_key(&var) {
                continue;
            }
            if children_done {
                in_progress.remove(&var);
                let form = self.combine(var);
                self.memo.insert(var, form);
                continue;
            }
            // A variable met again while it is still being expanded is its own
            // ancestor. Elimination never produces that (an eliminated variable
            // leaves every equation), but if it did, the ancestor's combine
            // finds no memo entry for it and yields `None` — no claim.
            if !in_progress.insert(var) {
                continue;
            }
            stack.push((var, true));
            let Some((coeffs, _)) = self.substitutions.get(&var) else {
                continue;
            };
            for &dep in coeffs.keys() {
                if self.role(dep) == DepRole::Expand && !self.memo.contains_key(&dep) {
                    stack.push((dep, false));
                }
            }
        }
    }

    /// Compose `var`'s substitution with its dependencies' expansions.
    fn combine(&mut self, var: usize) -> Option<LinearForm> {
        let (coeffs, constant) = self.substitutions.get(&var)?;
        let mut acc = LinearForm {
            coeffs: HashMap::default(),
            constant: constant.clone(),
        };
        for (&dep, coeff) in coeffs {
            match self.role(dep) {
                DepRole::Refuse => return None,
                DepRole::Leaf => {
                    self.charge(1)?;
                    *acc.coeffs.entry(dep).or_insert_with(BigInt::zero) += coeff;
                }
                DepRole::Expand => {
                    // Missing or `None` = the dependency has no exact
                    // expansion, so neither does this variable.
                    let cost = self.memo.get(&dep)?.as_ref()?.coeffs.len();
                    self.charge(cost.saturating_add(1))?;
                    let child = self.memo.get(&dep)?.as_ref()?;
                    acc.constant += coeff * &child.constant;
                    for (&leaf, leaf_coeff) in &child.coeffs {
                        *acc.coeffs.entry(leaf).or_insert_with(BigInt::zero) += coeff * leaf_coeff;
                    }
                }
            }
        }
        acc.coeffs.retain(|_, c| !c.is_zero());
        let too_big = acc.constant.bits() > EXPANSION_MAX_BITS
            || acc.coeffs.values().any(|c| c.bits() > EXPANSION_MAX_BITS);
        if too_big {
            return None;
        }
        Some(acc)
    }

    /// Spend `cost` units of the work budget; `None` once it is exhausted.
    fn charge(&mut self, cost: usize) -> Option<()> {
        if self.work_left < cost {
            self.work_left = 0;
            return None;
        }
        self.work_left -= cost;
        Some(())
    }
}
