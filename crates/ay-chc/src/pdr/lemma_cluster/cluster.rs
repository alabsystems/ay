// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Default initial gas for new clusters
pub(crate) const DEFAULT_CLUSTER_GAS: u32 = 10;

/// Maximum cluster size before pruning (Spacer: MAX_CLUSTER_SIZE)
pub(crate) const MAX_CLUSTER_SIZE: usize = 5;

/// Minimum cluster size before attempting MVP min/max generalization.
const MIN_CLUSTER_GENERALIZE_SIZE: usize = 3;

/// A lemma instance within a cluster.
///
/// Each member stores its substitution values (mapping pattern variables to
/// integer constants) and the frame level where it was learned.
#[derive(Debug, Clone)]
pub(crate) struct LemmaInstance {
    /// Frame level where this lemma was learned (for min-level heuristic)
    pub(crate) level: usize,
    /// Integer values for each pattern variable, parallel to `LemmaCluster::pattern_vars`
    pub(crate) subst_values: Vec<i128>,
}

impl LemmaInstance {
    pub(crate) fn new(level: usize, subst_values: Vec<i128>) -> Self {
        Self {
            level,
            subst_values,
        }
    }
}

/// A cluster of lemmas sharing a common pattern.
///
/// The pattern is a blocking cube with numeric constants abstracted to pattern
/// variables (e.g., `__gg_k0`, `__gg_k1`). Each member lemma is an instance of
/// the pattern obtained by substituting specific integer values.
///
/// # Example
///
/// Pattern: `x > __gg_k0 ∧ y > __gg_k1`
/// Member 1: level=2, subst_values=[0, 0] → `x > 0 ∧ y > 0`
/// Member 2: level=3, subst_values=[1, 0] → `x > 1 ∧ y > 0`
#[derive(Debug, Clone)]
pub(crate) struct LemmaCluster {
    /// Predicate this cluster is about
    pub(crate) predicate: PredicateId,
    /// Pattern formula with pattern variables instead of constants
    pub(crate) pattern: ChcExpr,
    /// Pattern variables in stable order (all Int for MVP)
    pub(crate) pattern_vars: Vec<ChcVar>,
    /// Member lemmas with their substitution values
    pub(crate) members: VecDeque<LemmaInstance>,
    /// Count of distinct member substitutions observed for this cluster.
    ///
    /// This is separate from `members.len()` because dominance pruning can remove members
    /// while we still want to gate min/max proposals on seeing enough distinct samples.
    pub(crate) samples_seen: usize,
    /// Minimum frame level observed across all members ever added to the cluster.
    ///
    /// This is separate from `members` because dominance pruning can remove the
    /// lowest-level member while we still want to target that level for global generalization.
    min_level_seen: Option<usize>,
    /// Gas for cluster-based generalization attempts (Spacer-style limiting)
    pub(crate) gas: u32,
}

/// Subsumption direction for a pattern variable within a comparison.
///
/// Determines how values compare when checking if member A subsumes member B.
/// See the development design notes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SubsumptionDirection {
    /// Lower values subsume higher values (for `>=`, `>` patterns)
    LowerSubsumes,
    /// Higher values subsume lower values (for `<=`, `<` patterns)
    HigherSubsumes,
    /// Values must be equal for subsumption (for `=` patterns)
    Equal,
}

impl LemmaCluster {
    /// Create a new cluster with the given pattern.
    pub(crate) fn new(predicate: PredicateId, pattern: ChcExpr, pattern_vars: Vec<ChcVar>) -> Self {
        Self {
            predicate,
            pattern,
            pattern_vars,
            members: VecDeque::new(),
            samples_seen: 0,
            min_level_seen: None,
            gas: DEFAULT_CLUSTER_GAS,
        }
    }

    /// Get the minimum frame level among all members ever added to the cluster.
    ///
    /// Used by global generalizer to choose target level for subsume lemma.
    /// Returns None if no members were ever added to the cluster.
    pub(crate) fn min_level(&self) -> Option<usize> {
        self.min_level_seen
    }

    /// Get cluster size (number of members).
    pub(crate) fn size(&self) -> usize {
        self.members.len()
    }

    /// Check if cluster is eligible for subsume attempt.
    ///
    /// Requires at least 2 members (pointless otherwise) and non-zero gas.
    pub(crate) fn is_eligible(&self) -> bool {
        self.members.len() >= 2 && self.gas > 0
    }

    /// Decrement gas after a subsume attempt.
    pub(crate) fn dec_gas(&mut self) {
        self.gas = self.gas.saturating_sub(1);
    }

    /// Find the unique mono-var literal in the pattern for conjecture mechanism.
    ///
    /// Z3's definition (spacer_conjecture.cpp:45-64):
    /// 1. The entire pattern has exactly 1 pattern variable
    /// 2. Exactly one literal in the pattern is an arithmetic inequality
    ///    containing that variable in a linear context
    ///
    /// Returns the literal (with the pattern variable still inside).
    /// Returns None if the pattern doesn't meet the mono-var criteria.
    pub(crate) fn find_mono_var_literal(&self) -> Option<ChcExpr> {
        if self.pattern_vars.len() != 1 {
            return None;
        }

        let pattern_var_name = &self.pattern_vars[0].name;
        let mut lits = Vec::new();
        self.pattern.collect_conjuncts_into(&mut lits);

        let mut mono_var_lit: Option<ChcExpr> = None;
        for lit in &lits {
            if is_mono_var_lit(lit, pattern_var_name) {
                if mono_var_lit.is_some() {
                    return None;
                }
                mono_var_lit = Some(lit.clone());
            }
        }

        mono_var_lit
    }

    /// Add a member to the cluster with proactive dominance-based pruning.
    ///
    /// Caller must verify the member's substitution values are compatible
    /// with the pattern (correct length, semantic match).
    ///
    /// Pruning strategy (per design the development design notes
    /// and issue #1700):
    /// 1. If the new member is dominated by an existing member, drop it (can't improve proposals).
    /// 2. Otherwise, remove all existing members dominated by the new member.
    /// 3. Append the new member.
    /// 4. If still over `MAX_CLUSTER_SIZE` (incomparable Pareto frontier), apply FIFO eviction.
    pub(crate) fn add_member(&mut self, member: LemmaInstance) {
        debug_assert_eq!(
            member.subst_values.len(),
            self.pattern_vars.len(),
            "substitution values length must match pattern vars"
        );

        self.min_level_seen = Some(match self.min_level_seen {
            Some(prev) => prev.min(member.level),
            None => member.level,
        });

        let already_present = self
            .members
            .iter()
            .any(|m| m.subst_values == member.subst_values);
        if already_present {
            return;
        }

        self.samples_seen += 1;

        if let Some(directions) = analyze_subsumption_directions(&self.pattern, &self.pattern_vars)
        {
            let new_is_dominated = self
                .members
                .iter()
                .any(|m| member_subsumes(&m.subst_values, &member.subst_values, &directions));
            if new_is_dominated {
                return;
            }

            self.members
                .retain(|m| !member_subsumes(&member.subst_values, &m.subst_values, &directions));
        }

        self.members.push_back(member);

        if self.members.len() > MAX_CLUSTER_SIZE {
            self.members.pop_front();
        }
    }

    /// Propose generalized blocking cubes using the MVP "min/max over constants" rule.
    pub(crate) fn propose_min_max_blocking_cubes(&self) -> Vec<ChcExpr> {
        if self.samples_seen < MIN_CLUSTER_GENERALIZE_SIZE {
            return Vec::new();
        }
        if self.pattern_vars.is_empty() {
            return Vec::new();
        }

        let mut mins = vec![i128::MAX; self.pattern_vars.len()];
        let mut maxs = vec![i128::MIN; self.pattern_vars.len()];
        for m in &self.members {
            if m.subst_values.len() != self.pattern_vars.len() {
                return Vec::new();
            }
            for (i, &v) in m.subst_values.iter().enumerate() {
                mins[i] = mins[i].min(v);
                maxs[i] = maxs[i].max(v);
            }
        }

        let mut var_to_idx: FxHashMap<String, usize> = FxHashMap::default();
        for (i, v) in self.pattern_vars.iter().enumerate() {
            var_to_idx.insert(v.name.clone(), i);
        }

        let mut lits = Vec::new();
        self.pattern.collect_conjuncts_into(&mut lits);

        let mut common: Vec<ChcExpr> = Vec::new();
        let mut eq_ge: Vec<ChcExpr> = Vec::new();
        let mut eq_le: Vec<ChcExpr> = Vec::new();

        for lit in lits {
            if let ChcExpr::Op(op, args) = &lit {
                if args.len() == 2 {
                    if let (ChcExpr::Var(a), ChcExpr::Var(b)) = (args[0].as_ref(), args[1].as_ref())
                    {
                        let a_idx = var_to_idx.get(&a.name).copied();
                        let b_idx = var_to_idx.get(&b.name).copied();
                        if a_idx.is_some() && b_idx.is_some() {
                            return Vec::new();
                        }

                        let (state_v, idx, op) = match (a_idx, b_idx) {
                            (None, Some(idx)) => (a, idx, *op),
                            (Some(idx), None) => {
                                let swapped = match op {
                                    ChcOp::Eq => Some(ChcOp::Eq),
                                    ChcOp::Lt => Some(ChcOp::Gt),
                                    ChcOp::Le => Some(ChcOp::Ge),
                                    ChcOp::Gt => Some(ChcOp::Lt),
                                    ChcOp::Ge => Some(ChcOp::Le),
                                    _ => None,
                                };
                                match swapped {
                                    Some(swapped) => (b, idx, swapped),
                                    None => return Vec::new(),
                                }
                            }
                            _ => (a, 0, ChcOp::And),
                        };

                        if !matches!(op, ChcOp::And) {
                            match op {
                                ChcOp::Ge => {
                                    common.push(ChcExpr::ge(
                                        ChcExpr::var(state_v.clone()),
                                        ChcExpr::Int(mins[idx]),
                                    ));
                                    continue;
                                }
                                ChcOp::Gt => {
                                    common.push(ChcExpr::gt(
                                        ChcExpr::var(state_v.clone()),
                                        ChcExpr::Int(mins[idx]),
                                    ));
                                    continue;
                                }
                                ChcOp::Le => {
                                    common.push(ChcExpr::le(
                                        ChcExpr::var(state_v.clone()),
                                        ChcExpr::Int(maxs[idx]),
                                    ));
                                    continue;
                                }
                                ChcOp::Lt => {
                                    common.push(ChcExpr::lt(
                                        ChcExpr::var(state_v.clone()),
                                        ChcExpr::Int(maxs[idx]),
                                    ));
                                    continue;
                                }
                                ChcOp::Eq => {
                                    eq_ge.push(ChcExpr::ge(
                                        ChcExpr::var(state_v.clone()),
                                        ChcExpr::Int(mins[idx]),
                                    ));
                                    eq_le.push(ChcExpr::le(
                                        ChcExpr::var(state_v.clone()),
                                        ChcExpr::Int(maxs[idx]),
                                    ));
                                    continue;
                                }
                                _ => return Vec::new(),
                            }
                        }
                    }
                }
            }

            if expr_mentions_pattern_var(&lit, &var_to_idx) {
                return Vec::new();
            }

            common.push(lit);
        }

        let mut out = Vec::new();
        if eq_ge.is_empty() {
            let cube = normalize_cube(&build_cube(common));
            if cube != ChcExpr::Bool(true) {
                out.push(cube);
            }
            return out;
        }

        let cube_le = normalize_cube(&build_cube(common.iter().cloned().chain(eq_le).collect()));
        if cube_le != ChcExpr::Bool(true) {
            out.push(cube_le);
        }

        let cube_ge = normalize_cube(&build_cube(common.into_iter().chain(eq_ge).collect()));
        if cube_ge != ChcExpr::Bool(true) {
            out.push(cube_ge);
        }

        out
    }
}

fn build_cube(lits: Vec<ChcExpr>) -> ChcExpr {
    match lits.len() {
        0 => ChcExpr::Bool(true),
        1 => lits.into_iter().next().expect("len == 1"),
        _ => ChcExpr::Op(ChcOp::And, lits.into_iter().map(Arc::new).collect()),
    }
}

fn analyze_subsumption_directions(
    pattern: &ChcExpr,
    pattern_vars: &[ChcVar],
) -> Option<Vec<SubsumptionDirection>> {
    let mut var_to_idx: FxHashMap<&str, usize> = FxHashMap::default();
    for (i, v) in pattern_vars.iter().enumerate() {
        var_to_idx.insert(v.name.as_str(), i);
    }

    let mut directions: Vec<Option<SubsumptionDirection>> = vec![None; pattern_vars.len()];
    let mut lits = Vec::new();
    pattern.collect_conjuncts_into(&mut lits);

    for lit in &lits {
        if let ChcExpr::Op(op, args) = lit {
            if args.len() == 2 {
                let (left_arg, right_arg) = (&args[0], &args[1]);

                let pattern_var_in_left = if let ChcExpr::Var(v) = left_arg.as_ref() {
                    var_to_idx.get(v.name.as_str()).copied()
                } else {
                    None
                };
                let pattern_var_in_right = if let ChcExpr::Var(v) = right_arg.as_ref() {
                    var_to_idx.get(v.name.as_str()).copied()
                } else {
                    None
                };

                if let (Some(idx), None) = (pattern_var_in_left, pattern_var_in_right) {
                    let dir = match op {
                        ChcOp::Ge | ChcOp::Gt => SubsumptionDirection::HigherSubsumes,
                        ChcOp::Le | ChcOp::Lt => SubsumptionDirection::LowerSubsumes,
                        ChcOp::Eq => SubsumptionDirection::Equal,
                        _ => return None,
                    };
                    if let Some(existing) = directions[idx] {
                        if existing != dir {
                            return None;
                        }
                    }
                    directions[idx] = Some(dir);
                } else if let (None, Some(idx)) = (pattern_var_in_left, pattern_var_in_right) {
                    let dir = match op {
                        ChcOp::Ge | ChcOp::Gt => SubsumptionDirection::LowerSubsumes,
                        ChcOp::Le | ChcOp::Lt => SubsumptionDirection::HigherSubsumes,
                        ChcOp::Eq => SubsumptionDirection::Equal,
                        _ => return None,
                    };
                    if let Some(existing) = directions[idx] {
                        if existing != dir {
                            return None;
                        }
                    }
                    directions[idx] = Some(dir);
                } else if pattern_var_in_left.is_some() && pattern_var_in_right.is_some() {
                    return None;
                }
            }
        }
    }

    directions.into_iter().collect()
}

fn member_subsumes(a: &[i128], b: &[i128], directions: &[SubsumptionDirection]) -> bool {
    debug_assert_eq!(a.len(), b.len());
    debug_assert_eq!(a.len(), directions.len());

    for i in 0..a.len() {
        let subsumes_at_i = match directions[i] {
            SubsumptionDirection::LowerSubsumes => a[i] <= b[i],
            SubsumptionDirection::HigherSubsumes => a[i] >= b[i],
            SubsumptionDirection::Equal => a[i] == b[i],
        };
        if !subsumes_at_i {
            return false;
        }
    }
    true
}

fn expr_mentions_pattern_var(expr: &ChcExpr, var_to_idx: &FxHashMap<String, usize>) -> bool {
    let mut stack = vec![expr];
    while let Some(e) = stack.pop() {
        match e {
            ChcExpr::Var(v) => {
                if var_to_idx.contains_key(&v.name) {
                    return true;
                }
            }
            ChcExpr::Op(_, args) => {
                for a in args {
                    stack.push(a);
                }
            }
            ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
                for a in args {
                    stack.push(a);
                }
            }
            ChcExpr::ConstArray(_ks, val) => stack.push(val),
            ChcExpr::Bool(_) | ChcExpr::Int(_) | ChcExpr::BitVec(_, _) | ChcExpr::Real(_, _) => {}
            ChcExpr::ConstArrayMarker(_) | ChcExpr::IsTesterMarker(_) => {}
        }
    }
    false
}

pub(crate) fn is_mono_var_lit(lit: &ChcExpr, pattern_var_name: &str) -> bool {
    if let ChcExpr::Op(ChcOp::Not, args) = lit {
        if args.len() == 1 {
            return is_mono_var_lit(&args[0], pattern_var_name);
        }
    }

    if let ChcExpr::Op(op, args) = lit {
        if !matches!(
            op,
            ChcOp::Eq | ChcOp::Lt | ChcOp::Le | ChcOp::Gt | ChcOp::Ge
        ) {
            return false;
        }

        if args.len() != 2 {
            return false;
        }

        if !lit.contains_var_name(pattern_var_name) {
            return false;
        }

        return !has_nonlinear_var_mul(lit, pattern_var_name);
    }

    false
}

pub(crate) fn has_nonlinear_var_mul(expr: &ChcExpr, var_name: &str) -> bool {
    let mut stack = vec![expr];
    while let Some(e) = stack.pop() {
        match e {
            ChcExpr::Op(ChcOp::Mul, args) => {
                let var_count = args
                    .iter()
                    .filter(|a| a.contains_var_name(var_name))
                    .count();
                if var_count > 1 {
                    return true;
                }
                for a in args {
                    stack.push(a);
                }
            }
            ChcExpr::Op(_, args) => {
                for a in args {
                    stack.push(a);
                }
            }
            _ => {}
        }
    }
    false
}
