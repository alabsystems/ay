// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Support computation for the independent-support brancher: gate recovery,
//! the order sweep, the acyclic-removal greedy, and the closure check.
//!
//! See `solver/indep_support.rs` for the algorithm and the soundness
//! argument; this file is the machinery.

use super::*;

impl Solver {
    /// Classify variables at the root: `(fixed, decidable)`. Root-fixed
    /// variables are constants for the rest of the solve; eliminated
    /// variables are neither (they are reconstructed only after SAT, so no
    /// definition depending on one can fire under BCP during search).
    pub(in crate::solver) fn classify_root_vars(&self) -> (Vec<bool>, Vec<bool>) {
        let num_vars = self.num_vars;
        let mut fixed = vec![false; num_vars];
        let mut decidable = vec![false; num_vars];
        for idx in 0..num_vars {
            if self.var_lifecycle.is_removed(idx) {
                continue;
            }
            if self.vals[Literal::positive(Variable(idx as u32)).index()] != 0 {
                fixed[idx] = true;
                continue;
            }
            decidable[idx] = true;
        }
        (fixed, decidable)
    }

    /// The support proper. `None` = no restriction (bailed, unverified, or
    /// not a meaningful reduction). Immutable on search state.
    pub(in crate::solver) fn compute_indep_support(&mut self) -> Option<Vec<u32>> {
        let num_vars = self.num_vars;
        let (fixed, decidable) = self.classify_root_vars();
        let decidable_count = decidable.iter().filter(|&&d| d).count();
        self.stats.indep_support_decidable_vars = decidable_count as u64;
        if decidable_count == 0 {
            return None;
        }

        let graph = self.collect_definitions(num_vars, &decidable, &fixed)?;
        self.stats.indep_support_gates = graph.defs.len() as u64;
        if graph.defs.is_empty() && graph.ge_exprs.is_empty() {
            return None;
        }

        // ORDER SWEEP: the greedy is exact-order-dependent (module docs), so
        // run a fixed deterministic set of orders and keep the smallest
        // result. All of these are sound; only their size differs.
        let mut best: Option<Vec<u32>> = None;
        for order in Self::support_orders(num_vars, &graph, &decidable) {
            let in_set = Self::greedy_support(&order, &graph, &decidable, &fixed);
            let support: Vec<u32> = (0..num_vars)
                .filter(|&v| in_set[v])
                .map(|v| v as u32)
                .collect();
            if best.as_ref().is_none_or(|b| support.len() < b.len()) {
                best = Some(support);
            }
        }

        // Completeness check for THIS gate set: replay the definitions from
        // the support exactly as BCP would and require every decidable
        // variable to come out. A support that does not close is refused.
        // The GE candidate (below) is verified against the definitions plus
        // its basis expressions, which are functional determinations of the
        // same shape (pivot := XOR of free inputs).
        let mut candidates: Vec<Vec<u32>> = Vec::new();
        if let Some(greedy) = best {
            if Self::verify_closure(num_vars, &graph, &greedy, &decidable, &fixed) {
                candidates.push(greedy);
            } else {
                self.stats.indep_support_closure_rejected += 1;
            }
        }
        if !graph.ge_exprs.is_empty() {
            if let Some(ge) = Self::ge_candidate(num_vars, &graph, &decidable, &fixed) {
                candidates.push(ge);
            }
        }
        let support = candidates.into_iter().min_by_key(Vec::len)?;

        // Restriction policy: small in absolute terms AND a real reduction.
        if support.is_empty()
            || support.len() > INDEP_SUPPORT_MAX_SIZE
            || support.len() * INDEP_SUPPORT_MAX_FRACTION_DEN > decidable_count
        {
            self.stats.indep_support_rejected_size = support.len() as u64;
            return None;
        }
        Some(support)
    }

    /// Recover gate definitions from the irredundant clause database and
    /// reduce them to the closure's `(output, distinct input variables)` form.
    pub(super) fn collect_definitions(
        &mut self,
        num_vars: usize,
        decidable: &[bool],
        fixed: &[bool],
    ) -> Option<DefinitionGraph> {
        let gates = self.recover_gates(num_vars)?;
        // GE basis over the same gates, before reduction drops the signs
        // the equations are read from (`ge.rs` module docs).
        let basis = ge::build_ge_basis(&gates, decidable, fixed, |v| {
            self.lit_value(Literal::positive(Variable(v)))
        });
        let mut graph = Self::reduce_to_definitions(&gates, num_vars, decidable, fixed);
        if let Some(basis) = basis {
            self.stats.indep_support_ge_free_vars = basis.free.len() as u64;
            graph.ge_free = basis.free;
            graph.ge_exprs = basis.exprs;
        }
        Some(graph)
    }

    /// Run both gate extractors over the irredundant clause database.
    fn recover_gates(&mut self, num_vars: usize) -> Option<Vec<Gate>> {
        let mut gates: Vec<Gate> = Vec::new();
        let mut extractor = GateExtractor::new(num_vars);
        let mut marks = LitMarks::new(num_vars.max(1));
        let mut effort_spent = 0u64;
        let extract_start = ay_core::time::Instant::now();
        // Under `--sat-deterministic-inproc` the 2 s wall is counted work: the
        // XOR group pass is bounded by its effort budget, and the per-pivot
        // loop by `det_work`, which adds the clause visits of the unfiltered
        // ITE base-pair scan that `effort_spent` does not charge.
        let det = self.deterministic_inproc();
        let mut det_work = 0u64;
        let frozen = vec![false; num_vars];

        // Clause-driven XOR group pass: one gate per group variable as
        // output. Essential here — see the module docs.
        extractor.extract_xor_groups_clause_driven(
            &self.arena,
            num_vars,
            &frozen,
            &mut effort_spent,
            INDEP_SUPPORT_EXTRACT_EFFORT,
            extract_start,
            if det {
                u128::MAX
            } else {
                INDEP_SUPPORT_EXTRACT_BUDGET_MS
            },
            &mut gates,
        );

        // Per-pivot equivalence / AND / ITE pass (XOR already owned above).
        let occ = self.build_occurrences(num_vars)?;
        for var_idx in 0..num_vars {
            if effort_spent >= INDEP_SUPPORT_EXTRACT_EFFORT {
                break;
            }
            if var_idx & 0x3FF == 0
                && var_idx > 0
                && if det {
                    det_work >= crate::determinism::GATE_EXTRACT_DET_WORK_BUDGET
                } else {
                    extract_start.elapsed().as_millis() >= INDEP_SUPPORT_EXTRACT_BUDGET_MS
                }
            {
                break;
            }
            // `occ.ranges` holds `2 * num_vars` slots (`build_occurrences`),
            // so both lookups succeed; an unmappable slot bails like a budget.
            let pos_slot = var_idx.checked_mul(2)?;
            let pos = occ.ranges.get(pos_slot)?;
            let neg = occ.ranges.get(pos_slot.checked_add(1)?)?;
            if pos.is_empty() || neg.is_empty() {
                continue;
            }
            effort_spent += (pos.len() + neg.len()) as u64;
            let found = extractor.find_gate_for_congruence_with_marks(
                Variable(var_idx as u32),
                &self.arena,
                &occ.pos[pos.clone()],
                &occ.neg[neg.clone()],
                false, // XOR handled by the clause-driven group pass
                &[],
                &mut marks,
            );
            if det {
                det_work = det_work
                    .saturating_add((pos.len() + neg.len()) as u64)
                    .saturating_add(extractor.take_ite_scan_visits());
            }
            if let Some(gate) = found {
                gates.push(gate);
            }
        }

        if gates.len() > INDEP_SUPPORT_MAX_GATES {
            gates.truncate(INDEP_SUPPORT_MAX_GATES);
        }
        Some(gates)
    }

    /// Reduce recovered gates to `(output, distinct input variables)`,
    /// dropping definitions that cannot fire under BCP during search.
    fn reduce_to_definitions(
        gates: &[Gate],
        num_vars: usize,
        decidable: &[bool],
        fixed: &[bool],
    ) -> DefinitionGraph {
        // Capacity is a hint (bounded by a fallible reservation): if it is
        // refused, `push` grows the vector on demand.
        let mut defs: Vec<Definition> = Vec::new();
        let _ = defs.try_reserve(gates.len());
        let mut as_lhs: Vec<Vec<u32>> = vec![Vec::new(); num_vars];
        let mut rhs_count: Vec<u32> = vec![0; num_vars];
        let mut seen_epoch: Vec<u32> = vec![0; num_vars];
        let mut epoch = 0u32;
        for gate in gates {
            let out = gate.output.index();
            if out >= num_vars || decidable.get(out) != Some(&true) {
                // A fixed or eliminated output needs no definition; a fixed
                // one is already known, an eliminated one is not decided.
                continue;
            }
            // Past u32::MAX gates, restart the epochs from a cleared stamp
            // array: the stamps stay exact instead of colliding.
            epoch = match epoch.checked_add(1) {
                Some(next) => next,
                None => {
                    seen_epoch.fill(0);
                    1
                }
            };
            let mut inputs: Vec<u32> = Vec::new();
            let _ = inputs.try_reserve(gate.inputs.len());
            let mut usable = true;
            seen_epoch[out] = epoch; // self-reference guard: v ∉ inputs(v)
            for lit in &gate.inputs {
                let iv = lit.variable().index();
                if iv >= num_vars
                    || (decidable.get(iv) != Some(&true) && fixed.get(iv) != Some(&true))
                {
                    // Eliminated input: the defining clauses no longer
                    // constrain the output during search.
                    usable = false;
                    break;
                }
                if seen_epoch[iv] == epoch {
                    if iv == out {
                        usable = false;
                        break;
                    }
                    continue; // duplicate input variable
                }
                seen_epoch[iv] = epoch;
                inputs.push(iv as u32);
            }
            if !usable || inputs.is_empty() {
                continue;
            }
            let def_idx = defs.len() as u32;
            for &iv in &inputs {
                rhs_count[iv as usize] = rhs_count[iv as usize].saturating_add(1);
            }
            as_lhs[out].push(def_idx);
            defs.push(Definition {
                output: out as u32,
                inputs,
            });
        }

        DefinitionGraph {
            defs,
            as_lhs,
            rhs_count,
            ge_free: Vec::new(),
            ge_exprs: Vec::new(),
        }
    }

    /// Occurrence lists over active irredundant clauses, in CSR form.
    fn build_occurrences(&self, num_vars: usize) -> Option<Occurrences> {
        let num_lits = num_vars.checked_mul(2)?;
        let mut counts = vec![0u32; num_lits];
        let mut total_pos = 0usize;
        let mut total_neg = 0usize;
        for off in self.arena.indices() {
            if !self.arena.is_active(off) || self.arena.is_learned(off) {
                continue;
            }
            for &lit in self.arena.literals(off) {
                let v = lit.variable().index();
                if v >= num_vars {
                    continue;
                }
                let slot = v
                    .checked_mul(2)?
                    .checked_add(usize::from(!lit.is_positive()))?;
                let count = counts.get_mut(slot)?;
                *count = count.checked_add(1)?;
                if !lit.is_positive() {
                    total_neg = total_neg.checked_add(1)?;
                } else {
                    total_pos = total_pos.checked_add(1)?;
                }
            }
        }
        let mut ranges: Vec<std::ops::Range<usize>> = Vec::new();
        ranges.try_reserve_exact(num_lits).ok()?;
        let mut pos_at = 0usize;
        let mut neg_at = 0usize;
        for (slot, &count) in counts[..num_lits].iter().enumerate() {
            let n = count as usize;
            if slot % 2 == 0 {
                let end = pos_at.checked_add(n)?;
                ranges.push(pos_at..end);
                pos_at = end;
            } else {
                let end = neg_at.checked_add(n)?;
                ranges.push(neg_at..end);
                neg_at = end;
            }
        }
        debug_assert_eq!(pos_at, total_pos);
        debug_assert_eq!(neg_at, total_neg);
        let mut pos_flat = vec![0usize; total_pos];
        let mut neg_flat = vec![0usize; total_neg];
        let mut fill: Vec<usize> = ranges.iter().map(|r| r.start).collect();
        for off in self.arena.indices() {
            if !self.arena.is_active(off) || self.arena.is_learned(off) {
                continue;
            }
            for &lit in self.arena.literals(off) {
                let v = lit.variable().index();
                if v >= num_vars {
                    continue;
                }
                let slot = v
                    .checked_mul(2)?
                    .checked_add(usize::from(!lit.is_positive()))?;
                let at = fill[slot];
                fill[slot] = at.checked_add(1)?;
                if !lit.is_positive() {
                    neg_flat[at] = off;
                } else {
                    pos_flat[at] = off;
                }
            }
        }
        Some(Occurrences {
            pos: pos_flat,
            neg: neg_flat,
            ranges,
        })
    }

    /// The deterministic order sweep (module docs). Every order yields a
    /// sound support; only the size differs.
    pub(super) fn support_orders(
        num_vars: usize,
        graph: &DefinitionGraph,
        decidable: &[bool],
    ) -> Vec<Vec<u32>> {
        let live: Vec<u32> = (0..num_vars)
            .filter(|&v| decidable.get(v) == Some(&true))
            .map(|v| v as u32)
            .collect();
        // A sort key: a u32 count plus a list length never reaches u64::MAX.
        let incidence = |v: u32| -> u64 {
            let i = v as usize;
            u64::from(graph.rhs_count[i]).saturating_add(graph.as_lhs[i].len() as u64)
        };

        // Reverse-topological for a circuit CNF emitted in evaluation order:
        // this is the order that recovers 32/1773 on xorshift.
        let mut desc = live.clone();
        desc.reverse();
        // Forward variable order.
        let asc = live.clone();
        // kissat-sup `explicit_search`'s LESS_INCIDENCE order.
        let mut inc_asc = live.clone();
        inc_asc.sort_by_key(|&v| (incidence(v), v));
        // Fewest-consumers first: drop the variables that block the least.
        let mut rhs_asc = live.clone();
        rhs_asc.sort_by_key(|&v| (graph.rhs_count[v as usize], v));
        // ...and its mirror.
        let mut rhs_desc = live;
        rhs_desc.sort_by_key(|&v| (std::cmp::Reverse(graph.rhs_count[v as usize]), v));

        vec![desc, asc, inc_asc, rhs_asc, rhs_desc]
    }

    /// Acyclic-removal greedy (`indepsup.c` `explicit_search`). Returns the
    /// in-set membership vector; `true` = kept in the support.
    pub(super) fn greedy_support(
        order: &[u32],
        graph: &DefinitionGraph,
        decidable: &[bool],
        fixed: &[bool],
    ) -> Vec<bool> {
        let mut in_set: Vec<bool> = decidable.to_vec();
        for &v in order {
            let vi = v as usize;
            if !in_set[vi] {
                continue;
            }
            for &def_idx in &graph.as_lhs[vi] {
                let def = &graph.defs[def_idx as usize];
                // Every input must still be available as a source: either a
                // root constant, or still a member of the candidate set.
                if def.inputs.iter().all(|&u| {
                    // An input outside the vectors is never available.
                    fixed.get(u as usize) == Some(&true) || in_set.get(u as usize) == Some(&true)
                }) {
                    in_set[vi] = false;
                    break;
                }
            }
        }
        in_set
    }

    /// Replay the definitions from the support with the same worklist
    /// closure BCP performs, and require every decidable variable to be
    /// derived. This is the "verify the invariant holds for your definition
    /// set" gate; the runtime fallback covers everything after it.
    pub(super) fn verify_closure(
        num_vars: usize,
        graph: &DefinitionGraph,
        support: &[u32],
        decidable: &[bool],
        fixed: &[bool],
    ) -> bool {
        match Self::closure_known(num_vars, &graph.defs, &[], support, decidable, fixed) {
            Some(known) => (0..num_vars)
                .all(|v| decidable.get(v) != Some(&true) || known.get(v) == Some(&true)),
            None => false,
        }
    }

    /// The GE candidate support (DR-AY-SAT-GE-SUPPORT-20261111): the basis
    /// free variables, plus every decidable variable the composed closure
    /// (gate definitions + basis expressions) does not determine from them.
    /// Verified against the same composed closure before it may compete
    /// with the greedy support on size.
    fn ge_candidate(
        num_vars: usize,
        graph: &DefinitionGraph,
        decidable: &[bool],
        fixed: &[bool],
    ) -> Option<Vec<u32>> {
        let known = Self::closure_known(
            num_vars,
            &graph.defs,
            &graph.ge_exprs,
            &graph.ge_free,
            decidable,
            fixed,
        )?;
        let mut candidate: Vec<u32> = graph.ge_free.clone();
        for v in 0..num_vars {
            if decidable.get(v) == Some(&true) && known.get(v) != Some(&true) {
                candidate.push(v as u32);
            }
        }
        candidate.sort_unstable();
        candidate.dedup();
        let verified = Self::closure_known(
            num_vars,
            &graph.defs,
            &graph.ge_exprs,
            &candidate,
            decidable,
            fixed,
        )?;
        if (0..num_vars).all(|v| decidable.get(v) != Some(&true) || verified.get(v) == Some(&true))
        {
            Some(candidate)
        } else {
            None
        }
    }

    /// Worklist closure over `defs` chained with `extra` definitions,
    /// seeded by `support` plus root constants. Returns the known-variable
    /// set, or `None` when a reservation fails (refuse, never guess).
    fn closure_known(
        num_vars: usize,
        defs: &[Definition],
        extra: &[Definition],
        support: &[u32],
        decidable: &[bool],
        fixed: &[bool],
    ) -> Option<Vec<bool>> {
        // Per-definition count of inputs not yet known.
        // An unreservable definition count refuses the support (sound: the
        // caller then applies no restriction).
        let all: Vec<&Definition> = defs.iter().chain(extra.iter()).collect();
        let mut remaining: Vec<u32> = Vec::new();
        if remaining.try_reserve_exact(all.len()).is_err() {
            return None;
        }
        let mut known = vec![false; num_vars];
        let mut queue: Vec<u32> = Vec::new();
        for (v, known) in known[..num_vars].iter_mut().enumerate() {
            if fixed.get(v) == Some(&true) || decidable.get(v) != Some(&true) {
                // Root constants are known; eliminated variables are not
                // decided and carry no obligation.
                *known = true;
            }
        }
        for &v in support {
            if !known[v as usize] {
                known[v as usize] = true;
            }
        }
        // `as_rhs` CSR built lazily here (only the verifier needs it).
        let mut rhs_head: Vec<Vec<u32>> = vec![Vec::new(); num_vars];
        for (def_idx, def) in all.iter().enumerate() {
            let unknown = def.inputs.iter().filter(|&&u| !known[u as usize]).count() as u32;
            remaining.push(unknown);
            for &u in &def.inputs {
                if !known[u as usize] {
                    rhs_head[u as usize].push(def_idx as u32);
                }
            }
            if unknown == 0 && !known[def.output as usize] {
                known[def.output as usize] = true;
                queue.push(def.output);
            }
        }
        while let Some(v) = queue.pop() {
            let consumers = std::mem::take(&mut rhs_head[v as usize]);
            for def_idx in consumers {
                let d = def_idx as usize;
                remaining[d] = remaining[d].saturating_sub(1);
                if remaining[d] == 0 {
                    let out = all[d].output as usize;
                    if !known[out] {
                        known[out] = true;
                        queue.push(out as u32);
                    }
                }
            }
        }
        Some(known)
    }
}
