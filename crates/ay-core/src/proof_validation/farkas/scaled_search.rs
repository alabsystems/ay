// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `farkas.rs` to preserve private item paths.

/// One orientation-branching position of a [`ScaledPlan`].
///
/// Only literals that genuinely offer more than one normalized form (an
/// equality's two orientations, a disequality's two strict branches) become a
/// branch; everything else is folded into [`ScaledPlan::base`] once.
struct ScaledBranch {
    /// Position in the original `alternatives`/`lambdas` vectors, so
    /// `search_recording_choice` can report the choice at the right index.
    idx: usize,
    /// `λ·e` for each candidate, in the original candidate order.
    scaled: Vec<LinearExpr>,
    /// `λ != 0 && alt.strict` for each candidate.
    strict: Vec<bool>,
}

/// The orientation search, pre-scaled and pre-folded (#8404 perf).
///
/// The naive formulation walks all `alternatives.len()` positions recursively,
/// cloning the accumulator and running one `BigRational` multiplication per
/// coefficient at every node. On a conflict with `n` literals of which `k` are
/// orientation-bearing that is `Θ(2^k · (n − k))` clones and multiplications,
/// and it was measured at ~80 % of total solver time on the `#8404` Seq-dense
/// `ghost_vec` benchmark — every recorded theory conflict pays it.
///
/// Nothing about the search *space* changes here. The same combinations are
/// enumerated in the same order; only the arithmetic is hoisted:
///
/// * every `λ·e` product is computed ONCE at plan-build time rather than once
///   per visit of the subtree beneath it, and
/// * the `n − k` single-candidate positions contribute a fixed sum, so they are
///   summed once into `base` instead of forming a clone-per-node chain under
///   every one of the `2^k` leaves.
///
/// Both rewrites are exact: `BigRational` addition is associative and
/// commutative, `LinearExpr::coeffs` is canonical (present iff non-zero), and
/// the strict flag is an OR — so reassociating the sum cannot change any
/// leaf's [`is_contradiction`] verdict. Branches are kept in ascending position
/// order with candidates in ascending index order, which preserves the
/// lexicographic enumeration `search_recording_choice` depends on.
struct ScaledPlan {
    /// `Σ λᵢ·eᵢ` over every position with exactly one candidate.
    base: LinearExpr,
    /// The strict flag contributed by those same positions.
    base_strict: bool,
    /// The multi-candidate positions, ascending by `idx`.
    branches: Vec<ScaledBranch>,
    /// `remaining[d][v]` is the largest absolute coefficient the branches at
    /// depth `d..` can still contribute to variable `v`; `v` absent means zero.
    /// Length is `branches.len() + 1`, so `remaining[branches.len()]` is empty.
    ///
    /// This is what makes the search sublinear in the leaf count on the
    /// conflicts that dominate runtime. `is_contradiction` demands that EVERY
    /// variable coefficient cancel, and a partial sum's coefficient for `v` can
    /// only move by at most `remaining[d][v]` over the rest of the walk — so
    /// once `|acc[v]| > remaining[d][v]`, no completion of this prefix can
    /// contradict and the entire subtree is dead. The common case is decided at
    /// depth 0: an all-ones certificate guessed against a wide conflict usually
    /// leaves `base` carrying variables no orientation choice even mentions, and
    /// the search returns without visiting a single leaf.
    ///
    /// The prune is exact, not heuristic — it removes only subtrees in which
    /// every leaf provably fails `is_contradiction` — so the accept/reject
    /// verdict and the recorded orientation choice are unchanged.
    ///
    /// EMPTY when the plan was built for a consumer that never walks
    /// (`build_scaled_plan(.., false)`); [`search_plan`] then simply does not
    /// prune, which costs work and decides nothing.
    remaining: Vec<BTreeMap<TermId, BigRational>>,
}

/// `with_prune_bounds` selects whether [`ScaledPlan::remaining`] is
/// materialized. Pass `false` only from a consumer that never calls
/// [`search_plan`]: the capped fast path in `farkas_combination_contradicts`
/// reads `base`/`branches` alone, while the bounds cost `Θ(k · |vars|)`
/// `BigRational` clones (one suffix map per branching position, each cloned
/// from the next). On a wide all-equality conflict that is the whole
/// verification — measured on the `inc_some_list` dual-vocabulary obligation
/// (#dt-uf-bridge-congruence), `build_remaining_bounds` and its drop were
/// 947 of the 1502 samples inside `build_scaled_plan`, itself 58% of
/// `farkas_combination_contradicts`, on a conflict whose search space
/// (2^258) can only ever take the bounds-free fast path.
///
/// The accept/reject verdict is unchanged in both directions: the fast path
/// never consulted the bounds, and `search_plan` treats a missing bound as
/// "cannot prune here" rather than as a zero bound.
fn build_scaled_plan(
    alternatives: &[Vec<NormalizedConstraint>],
    lambdas: &[BigRational],
    with_prune_bounds: bool,
) -> ScaledPlan {
    let mut base = LinearExpr::zero();
    let mut base_strict = false;
    let mut branches = Vec::new();

    for (idx, (alts, lambda)) in alternatives.iter().zip(lambdas.iter()).enumerate() {
        // A zero multiplier contributes nothing, so its orientation is not a
        // real choice — pin it to the first alternative exactly as the
        // node-at-a-time search did.
        let candidates: &[NormalizedConstraint] = if lambda.is_zero() { &alts[0..1] } else { alts };

        if candidates.len() <= 1 {
            let alt = &candidates[0];
            base.add_scaled(&alt.expr, lambda);
            base_strict = base_strict || (!lambda.is_zero() && alt.strict);
            continue;
        }

        let mut scaled = Vec::with_capacity(candidates.len());
        let mut strict = Vec::with_capacity(candidates.len());
        for alt in candidates {
            let mut row = LinearExpr::zero();
            row.add_scaled(&alt.expr, lambda);
            scaled.push(row);
            strict.push(!lambda.is_zero() && alt.strict);
        }
        branches.push(ScaledBranch {
            idx,
            scaled,
            strict,
        });
    }

    let remaining = if with_prune_bounds {
        build_remaining_bounds(&branches)
    } else {
        Vec::new()
    };
    ScaledPlan {
        base,
        base_strict,
        branches,
        remaining,
    }
}

/// Suffix bounds for [`ScaledPlan::remaining`], built back-to-front so each
/// depth is the next depth plus this branch's worst-case contribution.
fn build_remaining_bounds(branches: &[ScaledBranch]) -> Vec<BTreeMap<TermId, BigRational>> {
    let mut remaining = vec![BTreeMap::new(); branches.len() + 1];
    for depth in (0..branches.len()).rev() {
        let mut bounds = remaining[depth + 1].clone();
        // Worst case over this branch's candidates, per variable.
        let mut worst: BTreeMap<TermId, BigRational> = BTreeMap::new();
        for row in &branches[depth].scaled {
            for (var, coeff) in &row.coeffs {
                let magnitude = coeff.abs();
                match worst.get_mut(var) {
                    Some(current) if *current >= magnitude => {}
                    Some(current) => *current = magnitude,
                    None => {
                        worst.insert(*var, magnitude);
                    }
                }
            }
        }
        for (var, magnitude) in worst {
            *bounds.entry(var).or_insert_with(BigRational::zero) += magnitude;
        }
        remaining[depth] = bounds;
    }
    remaining
}

/// Whether any completion of `acc` from depth `depth` could still cancel every
/// variable. `false` means the whole subtree is provably contradiction-free.
fn subtree_can_cancel(acc: &LinearExpr, bounds: &BTreeMap<TermId, BigRational>) -> bool {
    acc.coeffs
        .iter()
        .all(|(var, coeff)| bounds.get(var).is_some_and(|bound| coeff.abs() <= *bound))
}

/// Depth-first walk over the branching positions of `plan`, accumulating in
/// place and undoing on the way out (see [`LinearExpr::sub_expr`]).
///
/// When `choice` is `Some`, the alternative index taken at each branch is
/// recorded at that branch's ORIGINAL position; single-candidate positions keep
/// the caller's zero initialization, which is the index they would have been
/// assigned anyway.
fn search_plan(
    plan: &ScaledPlan,
    depth: usize,
    acc: &mut LinearExpr,
    strict_acc: bool,
    choice: &mut Option<&mut [usize]>,
) -> bool {
    // Exact subtree prune (see `ScaledPlan::remaining`). At the leaf the bound
    // map is empty, so this reduces to `is_contradiction`'s own
    // "every coefficient eliminated" requirement. A plan built without prune
    // bounds has no entry at any depth and simply does not prune — never a
    // zero bound, which would prune every non-cancelled prefix.
    if let Some(bounds) = plan.remaining.get(depth) {
        if !subtree_can_cancel(acc, bounds) {
            return false;
        }
    }

    let Some(branch) = plan.branches.get(depth) else {
        return is_contradiction(acc, strict_acc);
    };

    for (alt_idx, scaled) in branch.scaled.iter().enumerate() {
        acc.add_expr(scaled);
        if let Some(choice) = choice.as_deref_mut() {
            choice[branch.idx] = alt_idx;
        }
        let hit = search_plan(
            plan,
            depth + 1,
            acc,
            strict_acc || branch.strict[alt_idx],
            choice,
        );
        acc.sub_expr(scaled);
        if hit {
            return true;
        }
    }
    if let Some(choice) = choice.as_deref_mut() {
        choice[branch.idx] = 0;
    }

    false
}

/// Like [`search_plan`], but records which alternative index was chosen for each
/// literal in `choice` when a contradicting combination is found. Alternatives
/// are explored first-alternative-first, so when the all-first combination
/// already contradicts, `choice` stays all-zero (deterministic, and keeps
/// pure-inequality certificates byte-identical downstream). `choice` must be
/// zero-initialized and as long as `alternatives`.
fn search_recording_choice(
    alternatives: &[Vec<NormalizedConstraint>],
    lambdas: &[BigRational],
    choice: &mut [usize],
) -> bool {
    let plan = build_scaled_plan(alternatives, lambdas, true);
    let mut acc = plan.base.clone();
    search_plan(
        &plan,
        0,
        &mut acc,
        plan.base_strict,
        &mut Some(&mut choice[..]),
    )
}
