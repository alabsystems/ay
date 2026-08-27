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
    /// The support proper. `None` = no restriction (bailed, unverified, or
    /// not a meaningful reduction). Immutable on search state.
    pub(in crate::solver) fn compute_indep_support(&mut self) -> Option<Vec<u32>> {
        let num_vars = self.num_vars;

        // Root-fixed variables are constants for the rest of the solve: they
        // never need a decision and they are legitimate inputs to a
        // definition. Eliminated variables are NOT available during search
        // (they are reconstructed only after SAT), so a definition that
        // depends on one cannot fire under BCP — those are excluded below.
        let mut fixed = vec![false; num_vars];
        let mut decidable = vec![false; num_vars];
        let mut decidable_count = 0usize;
        for idx in 0..num_vars {
            if self.var_lifecycle.is_removed(idx) {
                continue;
            }
            if self.vals[Literal::positive(Variable(idx as u32)).index()] != 0 {
                fixed[idx] = true;
                continue;
            }
            decidable[idx] = true;
            decidable_count += 1;
        }
        self.stats.indep_support_decidable_vars = decidable_count as u64;
        if decidable_count == 0 {
            return None;
        }

        let graph = self.collect_definitions(num_vars, &decidable, &fixed)?;
        self.stats.indep_support_gates = graph.defs.len() as u64;
        if graph.defs.is_empty() {
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
        let support = best?;

        // Completeness check for THIS gate set: replay the definitions from
        // the support exactly as BCP would and require every decidable
        // variable to come out. A support that does not close is refused.
        if !Self::verify_closure(num_vars, &graph, &support, &decidable, &fixed) {
            self.stats.indep_support_closure_rejected += 1;
            return None;
        }

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
        Some(Self::reduce_to_definitions(
            &gates, num_vars, decidable, fixed,
        ))
    }

    /// Run both gate extractors over the irredundant clause database.
    fn recover_gates(&mut self, num_vars: usize) -> Option<Vec<Gate>> {
        let mut gates: Vec<Gate> = Vec::new();
        let mut extractor = GateExtractor::new(num_vars);
        let mut marks = LitMarks::new(num_vars.max(1));
        let mut effort_spent = 0u64;
        let extract_start = ay_core::time::Instant::now();
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
            INDEP_SUPPORT_EXTRACT_BUDGET_MS,
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
                && extract_start.elapsed().as_millis() >= INDEP_SUPPORT_EXTRACT_BUDGET_MS
            {
                break;
            }
            let pos = &occ.ranges[var_idx * 2];
            let neg = &occ.ranges[var_idx * 2 + 1];
            if pos.is_empty() || neg.is_empty() {
                continue;
            }
            effort_spent += (pos.len() + neg.len()) as u64;
            if let Some(gate) = extractor.find_gate_for_congruence_with_marks(
                Variable(var_idx as u32),
                &self.arena,
                &occ.pos[pos.clone()],
                &occ.neg[neg.clone()],
                false, // XOR handled by the clause-driven group pass
                &[],
                &mut marks,
            ) {
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
        let mut defs: Vec<Definition> = Vec::with_capacity(gates.len());
        let mut as_lhs: Vec<Vec<u32>> = vec![Vec::new(); num_vars];
        let mut rhs_count: Vec<u32> = vec![0; num_vars];
        let mut seen_epoch: Vec<u32> = vec![0; num_vars];
        let mut epoch = 0u32;
        for gate in gates {
            let out = gate.output.index();
            if out >= num_vars || !decidable[out] {
                // A fixed or eliminated output needs no definition; a fixed
                // one is already known, an eliminated one is not decided.
                continue;
            }
            epoch += 1;
            let mut inputs: Vec<u32> = Vec::with_capacity(gate.inputs.len());
            let mut usable = true;
            seen_epoch[out] = epoch; // self-reference guard: v ∉ inputs(v)
            for lit in &gate.inputs {
                let iv = lit.variable().index();
                if iv >= num_vars || (!decidable[iv] && !fixed[iv]) {
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
                let slot = v * 2 + usize::from(!lit.is_positive());
                counts[slot] += 1;
                if !lit.is_positive() {
                    total_neg += 1;
                } else {
                    total_pos += 1;
                }
            }
        }
        let mut ranges: Vec<std::ops::Range<usize>> = Vec::with_capacity(num_lits);
        let mut pos_at = 0usize;
        let mut neg_at = 0usize;
        for slot in 0..num_lits {
            let n = counts[slot] as usize;
            if slot % 2 == 0 {
                ranges.push(pos_at..pos_at + n);
                pos_at += n;
            } else {
                ranges.push(neg_at..neg_at + n);
                neg_at += n;
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
                let slot = v * 2 + usize::from(!lit.is_positive());
                let at = fill[slot];
                fill[slot] = at + 1;
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
            .filter(|&v| decidable[v])
            .map(|v| v as u32)
            .collect();
        let incidence = |v: u32| -> u64 {
            let i = v as usize;
            u64::from(graph.rhs_count[i]) + graph.as_lhs[i].len() as u64
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
                if def
                    .inputs
                    .iter()
                    .all(|&u| fixed[u as usize] || in_set[u as usize])
                {
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
        // Per-definition count of inputs not yet known.
        let mut remaining: Vec<u32> = Vec::with_capacity(graph.defs.len());
        let mut known = vec![false; num_vars];
        let mut queue: Vec<u32> = Vec::new();
        for v in 0..num_vars {
            if fixed[v] || !decidable[v] {
                // Root constants are known; eliminated variables are not
                // decided and carry no obligation.
                known[v] = true;
            }
        }
        for &v in support {
            if !known[v as usize] {
                known[v as usize] = true;
            }
        }
        // `as_rhs` CSR built lazily here (only the verifier needs it).
        let mut rhs_head: Vec<Vec<u32>> = vec![Vec::new(); num_vars];
        for (def_idx, def) in graph.defs.iter().enumerate() {
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
                    let out = graph.defs[d].output as usize;
                    if !known[out] {
                        known[out] = true;
                        queue.push(out as u32);
                    }
                }
            }
        }
        (0..num_vars).all(|v| !decidable[v] || known[v])
    }
}
