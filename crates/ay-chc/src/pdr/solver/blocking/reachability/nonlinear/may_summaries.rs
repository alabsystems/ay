// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! May summaries of the nonlinear Spacer lane: each body atom's hypothesis in
//! a lane query — the delta frame at frame index `f ≥ 1`, the disjunction of
//! the atom's renamed facts at `f == 0` (`blocking/reachability/nonlinear.rs`).

use super::super::*;

/// One body atom's hypothesis in a lane query.
pub(in crate::pdr::solver) struct AtomHyp {
    /// `F_f(Q)(y)`: the delta frame on the atom's arguments (`Bool(true)` when
    /// no lemma), or at `f == 0` the disjunction of the atom's renamed facts.
    pub(in crate::pdr::solver) expr: ChcExpr,
    /// At `f == 0`: each fact clause index with its disjunct of `expr`.
    pub(in crate::pdr::solver) facts: Vec<(usize, ChcExpr)>,
}

impl PdrSolver {
    /// The body hypotheses of a lane query over `atoms` at frame index `f`
    /// (`F_f` = the delta frame for `f ≥ 1`; `f == 0`: the disjunction of each
    /// atom's facts, renamed apart per `(atom, fact)` against `roots` and every
    /// other part of the query). `None` ⇒ an `apply_to_args` or rename failure
    /// (callers answer `Unknown`); `Some(None)` ⇒ an atom has no fact at
    /// `f == 0` (the clause is vacuous: UNSAT with the empty core).
    pub(in crate::pdr::solver) fn lane_body_hyps(
        &self,
        atoms: &[(PredicateId, Vec<ChcExpr>)],
        f: usize,
        roots: &[ChcExpr],
    ) -> Option<Option<Vec<AtomHyp>>> {
        let mut out: Vec<AtomHyp> = Vec::with_capacity(atoms.len());
        if f >= 1 {
            for (pred, args) in atoms {
                let expr = match self.frame_hyp(f, *pred) {
                    Some(frame) => self.apply_to_args(*pred, &frame, args)?,
                    None => ChcExpr::Bool(true),
                };
                out.push(AtomHyp {
                    expr,
                    facts: Vec::new(),
                });
            }
            return Some(Some(out));
        }
        let names = self.source_names()?;
        let mut open = || !self.is_cancelled();
        let arg_roots: Vec<ChcExpr> = atoms
            .iter()
            .flat_map(|(_, args)| args.iter().cloned())
            .collect();
        for (atom, (pred, args)) in atoms.iter().enumerate() {
            let mut facts: Vec<(usize, ChcExpr)> = Vec::new();
            for (fact_index, fact) in self
                .problem
                .clauses_defining_with_index(*pred)
                .filter(|(_, c)| c.is_fact())
            {
                let fact_head_args = match &fact.head {
                    crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                    crate::ClauseHead::False => continue,
                };
                if fact_head_args.len() != args.len() {
                    continue;
                }
                let fact_constraint = fact.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
                let (renamed, renamed_args) = names.rename(
                    &fact_constraint,
                    fact_head_args,
                    &format!("__nl{atom}_f{fact_index}_"),
                    roots
                        .iter()
                        .chain(arg_roots.iter())
                        .chain(out.iter().map(|h| &h.expr)),
                    &mut open,
                )?;
                // Every variable of the renamed fact is fresh (`rename` renames
                // all of them): exactly these are the disjunct's locals.
                let fresh: ay_core::kani_compat::DetHashSet<String> = renamed
                    .vars()
                    .into_iter()
                    .chain(renamed_args.iter().flat_map(ChcExpr::vars))
                    .map(|v| v.name)
                    .collect();
                let mut conj = vec![renamed];
                conj.extend(
                    args.iter()
                        .cloned()
                        .zip(renamed_args)
                        .map(|(a, b)| ChcExpr::eq(a, b)),
                );
                // The fact's renamed variables defined by its equalities are
                // eliminated (a fact `v = 3 → P(v)` is the disjunct `y = 3`),
                // and duplicate facts contribute one disjunct.
                let is_fact_local = |v: &crate::ChcVar| fresh.contains(&v.name);
                let Some(conj) = super::roots::eliminate_locals(conj, &is_fact_local) else {
                    continue; // an UNSAT fact contributes nothing
                };
                let disjunct = ChcExpr::and_all(conj);
                if !facts.iter().any(|(_, d)| *d == disjunct) {
                    facts.push((fact_index, disjunct));
                }
            }
            if facts.is_empty() {
                return Some(None);
            }
            let expr = ChcExpr::or_all(facts.iter().map(|(_, d)| d.clone()));
            out.push(AtomHyp { expr, facts });
        }
        Some(Some(out))
    }
}
