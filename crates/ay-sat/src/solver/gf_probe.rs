// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! GF(p) one-hot linear-system probe (constructive startup preprocessing).
//!
//! The SAT-COMP 2026 Main Track "bare-numeric" family ("1".."16": every CNF
//! is `p cnf 1200 21040`) encodes a random linear system over GF(3): 400
//! one-hot triples (per unknown: one all-positive width-3 ALO clause plus the
//! 3 all-negative pairwise AMO binaries) and 360 scopes of 4 ternary
//! unknowns, each scope materializing one equation
//! `a0*x0 + a1*x1 + a2*x2 + a3*x3 ≡ c (mod 3)` as its 54 (= 3^4 − 3^3)
//! forbidden all-negative width-4 tuples. CDCL is hopeless here (AY solved
//! 0/12 at 1500 s; the 2026 winner solved none), but the system itself is
//! trivial: detect the structure, fit the equations, run dense Gaussian
//! elimination over GF(p), and reconstruct a boolean model in milliseconds.
//!
//! Architectural template: `lucky_scratch.rs`. The probe reads the clause
//! arena IMMUTABLY, is budget-bounded, self-verifies the reconstructed model
//! against EVERY active clause, and falls through silently on any failure.
//! It never derives UNSAT — an inconsistent fitted system only proves the
//! FIT saw an inconsistency, not the formula (detection could have mis-fit),
//! so the probe bails without a verdict. This makes it fully proof-mode
//! compatible: the only verdict it can produce is a SAT whose model is its
//! own certificate (re-checked by `finalize_sat_model` +
//! `verify_external_model`, the model gate).
//!
//! Detection is written for a general one-hot domain size `d` (prime) and
//! scope width `r`, is permutation-robust (group values are ranks in sorted
//! variable order; a per-coordinate relabeling of GF(3) values is affine and
//! therefore preserves linear-equation solution sets), and bails on the
//! FIRST mixed-polarity clause — off-family instances pay essentially
//! nothing.
//!
//! Placement: BEFORE preprocessing. BVE freely eliminates the one-hot
//! scaffolding (each variable has exactly one positive occurrence, so
//! elimination is always occurrence-bounded), which destroys the structure
//! this probe detects; the pristine clause DB is the only reliable surface.
//!
//! CLI opt-out: `--sat-gf-probe false` (default ON).

mod gauss;

use super::*;
use std::collections::HashMap;
use std::time::{Duration, Instant};

/// Total wall budget for the whole probe (detection + fit + elimination +
/// verification). The family completes in single-digit milliseconds; the
/// budget only caps pathological near-family giants.
const GF_PROBE_BUDGET: Duration = Duration::from_secs(2);
/// Throttle for deadline / interrupt checks inside the classification scan.
const GF_PROBE_CHECK_INTERVAL: usize = 4096;
/// Cheap pre-gates: never scan formulas far outside the family's size class.
const GF_PROBE_MAX_ACTIVE_CLAUSES: usize = 5_000_000;
const GF_PROBE_MAX_VARS: usize = 1_000_000;
/// Structural caps (the family is 400 groups / 360 scopes; generous headroom).
const GF_PROBE_MAX_GROUPS: usize = 4096;
const GF_PROBE_MAX_SCOPES: usize = 8192;
/// Domain cap: `d` must be prime; fit work grows as `(d-1)^(r-1) * d^r`.
const GF_PROBE_MAX_DOMAIN: usize = 32;
/// Per-scope tuple-space cap (`d^r`).
const GF_PROBE_MAX_TUPLE_SPACE: usize = 1 << 20;
/// Per-scope fit-work cap: `(d-1)^(r-1) * d^r` (family: 8 * 81 = 648).
const GF_PROBE_MAX_FIT_WORK: u64 = 1 << 26;

/// CLI-owned tri-state: `--sat-gf-probe false` disables; default ON.
fn gf_probe_enabled() -> bool {
    ay_core::sat_ab_switches().gf_probe.unwrap_or(true)
}

/// Trial-division primality (d <= GF_PROBE_MAX_DOMAIN, so this is trivial).
/// GF(d) arithmetic — in particular the modular inverses Gaussian
/// elimination divides by — requires d prime.
fn is_prime(d: usize) -> bool {
    d >= 2
        && (2..d)
            .take_while(|p| p * p <= d)
            .all(|p| !d.is_multiple_of(p))
}

/// Detected one-hot linear-system structure.
struct GfDetection {
    /// One-hot domain size (prime).
    d: usize,
    /// Per group: its `d` variable indices sorted ascending. A variable's
    /// value label is its RANK in this order — canonical and therefore
    /// robust to clause/literal permutation.
    groups: Vec<Vec<u32>>,
    /// Per scope: the equation's variable groups and forbidden tuples.
    scopes: Vec<GfScope>,
}

/// One equation scope: `r` distinct groups plus the forbidden-tuple bitmap.
struct GfScope {
    /// Sorted distinct group ids (length `r`).
    groups: Vec<u32>,
    /// Bitmap over tuple codes `0..d^r`; code digit `i` (base `d`, least
    /// significant first) is the value of `groups[i]`.
    forbidden: Vec<bool>,
    n_forbidden: usize,
}

/// Clause offsets bucketed by polarity shape, plus the uniform ALO width.
struct GfClassified {
    d: usize,
    alo: Vec<usize>,
    neg: Vec<usize>,
}

/// One-hot group table: `groups[g]` is group `g`'s sorted variable list;
/// `group_of[v]` maps a variable to its group id (`u32::MAX` = ungrouped).
struct GfGroups {
    groups: Vec<Vec<u32>>,
    group_of: Vec<u32>,
}

impl Solver {
    /// Run the GF(p) probe at startup-preprocessing entry. Returns
    /// `Some(result)` only for a fully verified SAT; `None` falls through to
    /// normal preprocessing + CDCL with the solver untouched.
    pub(super) fn try_gf_linear_probe_at_startup(&mut self) -> Option<SatResult> {
        if !gf_probe_enabled() {
            return None;
        }
        // IC3/PDR drives the solver through assumption/domain queries; this
        // is a plain-CNF startup construction only (mirrors the lucky gate).
        if self.cold.ic3_mode {
            return None;
        }
        let t0 = Instant::now();
        let model = self.gf_linear_probe(GF_PROBE_BUDGET);
        let elapsed = t0.elapsed().as_nanos().min(u128::from(u64::MAX)) as u64;
        self.stats.gf_probe_time_ns = self.stats.gf_probe_time_ns.saturating_add(elapsed);

        model.map(|model| {
            self.tla_trace_step(CdclTraceState::Sat, Some(CdclTraceAction::DeclareSat));
            // Model gate: finalize_sat_model + verify_external_model. On
            // failure this downgrades to Unknown rather than declaring SAT.
            self.declare_sat_from_model(model)
        })
    }

    /// The probe proper: detect, fit, eliminate, reconstruct, verify.
    /// Immutable on solver state; `None` on any bail-out.
    pub(super) fn gf_linear_probe(&self, budget: Duration) -> Option<Vec<bool>> {
        let deadline = Instant::now() + budget;
        // Cheap count gates first: the family is 1200 vars / 21K clauses.
        let active = self.arena.active_clause_count();
        if active == 0 || active > GF_PROBE_MAX_ACTIVE_CLAUSES || self.num_vars > GF_PROBE_MAX_VARS
        {
            return None;
        }

        let det = self.gf_detect(deadline)?;

        // Fit one linear equation per scope; any unfittable scope bails.
        let mut eqs: Vec<(Vec<u32>, Vec<u8>, u8)> = Vec::with_capacity(det.scopes.len());
        for scope in &det.scopes {
            if self.is_interrupted() || Instant::now() >= deadline {
                return None;
            }
            let (coefs, c) = gauss::fit_scope(det.d, scope.groups.len(), &scope.forbidden)?;
            eqs.push((scope.groups.clone(), coefs, c));
        }

        // Dense Gaussian elimination over GF(d). Underdetermined is fine
        // (free unknowns take value 0); inconsistent bails WITHOUT a verdict.
        let values = gauss::solve_linear_system(det.d, det.groups.len(), &eqs, deadline)?;

        // Boolean reconstruction: in each one-hot group, exactly the variable
        // whose rank equals the group's GF(d) value is true. Variables in no
        // active clause stay false.
        let mut model = vec![false; self.num_vars];
        for (g, vars) in det.groups.iter().enumerate() {
            model[vars[values[g] as usize] as usize] = true;
        }

        // Defensive final check: every active clause satisfied (the
        // lucky_scratch pattern). A fit/elimination bug can only cost time.
        if !self.gf_verify_model(&model) {
            tracing::warn!("gf probe: model failed self-verification; abandoning probe");
            debug_assert!(false, "gf probe model failed self-verification");
            return None;
        }
        tracing::info!(
            d = det.d,
            groups = det.groups.len(),
            scopes = det.scopes.len(),
            "gf probe: satisfying assignment constructed"
        );
        Some(model)
    }

    /// Structural detection. Strict: every active clause must be exactly one
    /// of {uniform-width all-positive ALO, within-group all-negative AMO
    /// binary, uniform-width all-negative cross-group forbidden tuple}.
    fn gf_detect(&self, deadline: Instant) -> Option<GfDetection> {
        let classified = self.gf_classify(deadline)?;
        let d = classified.d;
        if !is_prime(d) || d > GF_PROBE_MAX_DOMAIN {
            return None;
        }
        let table = self.gf_build_groups(&classified.alo, d)?;
        let scopes = self.gf_build_scopes(&classified.neg, &table, d, deadline)?;
        Some(GfDetection {
            d,
            groups: table.groups,
            scopes,
        })
    }

    /// Pass 1 — polarity/width census over the active clause DB. Bails on
    /// the first mixed-polarity clause (which almost every off-family
    /// instance has within its first few clauses) or non-uniform ALO width.
    fn gf_classify(&self, deadline: Instant) -> Option<GfClassified> {
        let mut d = 0usize;
        let mut alo: Vec<usize> = Vec::new();
        let mut neg: Vec<usize> = Vec::new();
        let mut since_check = 0usize;
        for off in self.arena.indices() {
            if !self.arena.is_active(off) {
                continue;
            }
            since_check += 1;
            if since_check >= GF_PROBE_CHECK_INTERVAL {
                since_check = 0;
                if self.is_interrupted() || Instant::now() >= deadline {
                    return None;
                }
            }
            let lits = self.arena.literals(off);
            if lits.is_empty() {
                return None;
            }
            let positives = lits.iter().filter(|l| l.is_positive()).count();
            if positives == lits.len() {
                if d == 0 {
                    d = lits.len();
                } else if lits.len() != d {
                    return None;
                }
                if alo.len() >= GF_PROBE_MAX_GROUPS {
                    return None;
                }
                alo.push(off);
            } else if positives == 0 {
                neg.push(off);
            } else {
                return None; // mixed polarity — not this family
            }
        }
        // Need one-hot groups of width >= 2 (width-1 "groups" are units).
        if d < 2 || alo.is_empty() {
            return None;
        }
        Some(GfClassified { d, alo, neg })
    }

    /// Pass 2 — each ALO clause defines one one-hot group. Every variable
    /// must belong to at most one group and appear once per clause.
    fn gf_build_groups(&self, alo: &[usize], d: usize) -> Option<GfGroups> {
        const UNGROUPED: u32 = u32::MAX;
        let mut group_of = vec![UNGROUPED; self.num_vars];
        let mut groups: Vec<Vec<u32>> = Vec::with_capacity(alo.len());
        for &off in alo {
            let g = groups.len() as u32;
            let mut vars: Vec<u32> = Vec::with_capacity(d);
            for &lit in self.arena.literals(off) {
                let v = lit.variable().index();
                if v >= self.num_vars || group_of[v] != UNGROUPED {
                    return None; // out of range, duplicate, or overlapping
                }
                group_of[v] = g;
                vars.push(v as u32);
            }
            // Canonical value labeling: rank in ascending variable order.
            vars.sort_unstable();
            groups.push(vars);
        }
        Some(GfGroups { groups, group_of })
    }

    /// Pass 3 — split the all-negative clauses into within-group AMO
    /// binaries (must be COMPLETE per group) and cross-group forbidden-tuple
    /// clauses (uniform width `r`, one variable per group, exactly
    /// `d^r - d^(r-1)` distinct tuples per scope).
    fn gf_build_scopes(
        &self,
        neg: &[usize],
        table: &GfGroups,
        d: usize,
        deadline: Instant,
    ) -> Option<Vec<GfScope>> {
        const UNGROUPED: u32 = u32::MAX;
        // Pairwise AMO presence per group: (lo_rank, hi_rank) bit per group.
        let mut amo_seen = vec![false; table.groups.len() * d * d];
        let mut amo_count = vec![0u32; table.groups.len()];
        let mut scopes: Vec<GfScope> = Vec::new();
        let mut scope_ids: HashMap<Vec<u32>, usize> = HashMap::new();
        let mut r = 0usize;
        let mut tuple_space = 0usize;
        let mut since_check = 0usize;
        // Scratch: (group, rank) per literal of the current clause.
        let mut members: Vec<(u32, u32)> = Vec::new();

        for &off in neg {
            since_check += 1;
            if since_check >= GF_PROBE_CHECK_INTERVAL {
                since_check = 0;
                if self.is_interrupted() || Instant::now() >= deadline {
                    return None;
                }
            }
            members.clear();
            for &lit in self.arena.literals(off) {
                let v = lit.variable().index();
                if v >= table.group_of.len() || table.group_of[v] == UNGROUPED {
                    return None; // every all-negative literal must be a group var
                }
                let g = table.group_of[v];
                // Rank of v inside its (sorted, tiny) group.
                let rank = table.groups[g as usize]
                    .iter()
                    .position(|&x| x == v as u32)? as u32;
                members.push((g, rank));
            }
            if members.len() == 2 && members[0].0 == members[1].0 {
                // Within-group binary: one AMO pair.
                let g = members[0].0 as usize;
                let (a, b) = (
                    members[0].1.min(members[1].1),
                    members[0].1.max(members[1].1),
                );
                if a == b {
                    return None; // duplicate literal
                }
                let slot = g * d * d + a as usize * d + b as usize;
                if !amo_seen[slot] {
                    amo_seen[slot] = true;
                    amo_count[g] += 1;
                }
                continue;
            }
            // Forbidden-tuple clause: uniform width, r DISTINCT groups.
            if r == 0 {
                r = members.len();
                if r < 2 {
                    return None;
                }
                tuple_space = gauss::checked_pow(d, r, GF_PROBE_MAX_TUPLE_SPACE)?;
                let candidates = gauss::checked_pow(d - 1, r - 1, usize::MAX)? as u64;
                if candidates.checked_mul(tuple_space as u64)? > GF_PROBE_MAX_FIT_WORK {
                    return None;
                }
            } else if members.len() != r {
                return None;
            }
            members.sort_unstable_by_key(|&(g, _)| g);
            if members.windows(2).any(|w| w[0].0 == w[1].0) {
                return None; // two variables from one group — not a tuple
            }
            let key: Vec<u32> = members.iter().map(|&(g, _)| g).collect();
            let scope_id = *scope_ids.entry(key.clone()).or_insert_with(|| {
                scopes.push(GfScope {
                    groups: key,
                    forbidden: vec![false; tuple_space],
                    n_forbidden: 0,
                });
                scopes.len() - 1
            });
            if scopes.len() > GF_PROBE_MAX_SCOPES {
                return None;
            }
            // Mixed-radix tuple code: digit i (LSD-first) = rank in groups[i].
            let mut code = 0usize;
            for &(_, rank) in members.iter().rev() {
                code = code * d + rank as usize;
            }
            let scope = &mut scopes[scope_id];
            if !scope.forbidden[code] {
                scope.forbidden[code] = true;
                scope.n_forbidden += 1;
            }
        }
        gf_structure_complete(&amo_count, &scopes, d, tuple_space).then_some(scopes)
    }

    /// Every active clause satisfied by `model` (immutable defensive check).
    fn gf_verify_model(&self, model: &[bool]) -> bool {
        self.arena.indices().all(|off| {
            !self.arena.is_active(off)
                || self.arena.literals(off).iter().any(|&lit| {
                    let v = lit.variable().index();
                    v < model.len() && (model[v] == lit.is_positive())
                })
        })
    }
}

/// Final structural predicates: every group carries its COMPLETE pairwise
/// AMO, at least one equation scope exists, and every scope holds EXACTLY
/// `d^r - d^(r-1)` distinct forbidden tuples.
fn gf_structure_complete(
    amo_count: &[u32],
    scopes: &[GfScope],
    d: usize,
    tuple_space: usize,
) -> bool {
    let full_amo = (d * (d - 1) / 2) as u32;
    if amo_count.iter().any(|&c| c != full_amo) {
        return false;
    }
    if scopes.is_empty() {
        return false;
    }
    let expected = tuple_space - tuple_space / d;
    scopes.iter().all(|s| s.n_forbidden == expected)
}
