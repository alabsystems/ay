// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Saturation solve and closure tables for the finite-domain UF
//! certificate, split from the producer for the size ratchet.

use super::types::{FragmentScan, UfDomains};
use super::*;

impl Executor {
    /// Domain-constrained ground saturation: solve grounds + every
    /// seed-domain forall instance with the EUF theory, additionally
    /// deciding every depth-1 closure application (a tabled symbol over
    /// representative arguments) equal to a domain representative, by
    /// scoped backtracking search in candidate-preference order.
    /// Exhibits the resulting congruence-consistent finite structure.
    /// Literal-shaped fragment only; `None` declines to the candidate
    /// fallback.
    pub(super) fn uf_saturation_model(
        &mut self,
        grounds: &[TermId],
        forall_quants: &[TermId],
        seed: &UfDomains,
        candidate: &Model,
        scan: &FragmentScan,
    ) -> Option<(Model, UfDomains)> {
        let (literals, decisions) =
            self.uf_saturation_problem(grounds, forall_quants, seed, candidate, scan)?;
        let mut solver = ay_euf::EufSolver::new(&self.ctx.terms);
        for (atom, polarity) in literals {
            solver.assert_literal(atom, polarity);
        }
        if !matches!(solver.check(), ay_core::TheoryResult::Sat) {
            return None;
        }
        let mut nodes = 0usize;
        if !Self::uf_decide_apps(&mut solver, &decisions, 0, &mut nodes) {
            return None;
        }
        let euf_model = solver.extract_model();
        // Domains in the saturation model's own naming: one entry per
        // distinct value the seed representatives received there.
        let mut domains = UfDomains::default();
        domains.seed_bool(&self.ctx.terms);
        for sort in scan.sorts.iter().filter(|s| !matches!(s, Sort::Bool)) {
            for rep in seed.reps(sort) {
                let element = euf_model.term_values.get(&rep)?.clone();
                domains.insert(sort.clone(), element, rep)?;
            }
            if domains.reps(sort).is_empty() {
                return None;
            }
        }
        let mut wrapper = Model::empty();
        wrapper.euf_model = Some(euf_model);
        Some((wrapper, domains))
    }

    /// The saturation problem: fixed literals (grounds + seed-domain
    /// instances) and per-application decision options.
    fn uf_saturation_problem(
        &mut self,
        grounds: &[TermId],
        forall_quants: &[TermId],
        seed: &UfDomains,
        candidate: &Model,
        scan: &FragmentScan,
    ) -> Option<(Vec<(TermId, bool)>, Vec<(TermId, Vec<TermId>)>)> {
        // ---- Fixed literals: grounds + all seed-domain instances.
        let mut literals: Vec<(TermId, bool)> = Vec::new();
        for &ground in grounds {
            literals.push(self.uf_literal(ground)?);
        }
        for &q in forall_quants {
            let TermData::Forall(bindings, body, _) = self.ctx.terms.get(q).clone() else {
                return None;
            };
            let columns: Vec<Vec<TermId>> =
                bindings.iter().map(|(_, sort)| seed.reps(sort)).collect();
            let tuples = Self::rep_tuples(&columns, MAX_FORALL_TUPLES);
            if tuples.is_empty() && !bindings.is_empty() {
                return None;
            }
            for tuple in tuples {
                let substitution: HashMap<String, TermId> = bindings
                    .iter()
                    .map(|(name, _)| name.clone())
                    .zip(tuple)
                    .collect();
                let instance = subst_vars(&mut self.ctx.terms, body, &substitution);
                literals.push(self.uf_literal(instance)?);
            }
        }
        // ---- Decision applications: every tabled symbol over every
        // seed-representative tuple, with candidate-preferred reps first.
        let mut decisions: Vec<(TermId, Vec<TermId>)> = Vec::new();
        for sig in scan.signatures.values() {
            if sig.arg_sorts.is_empty() {
                continue;
            }
            let columns: Vec<Vec<TermId>> =
                sig.arg_sorts.iter().map(|sort| seed.reps(sort)).collect();
            for tuple in Self::rep_tuples(&columns, MAX_CLOSURE_APPS) {
                let app = self
                    .ctx
                    .terms
                    .mk_app(sig.symbol.clone(), tuple, sig.result_sort.clone());
                let mut options: Vec<TermId> = Vec::new();
                if matches!(sig.result_sort, Sort::Bool) {
                    options.push(app);
                } else {
                    if let EvalValue::Element(atom) = self.evaluate_term(candidate, app) {
                        if let Some(rep) = seed.rep_for(&sig.result_sort, &atom) {
                            options.push(self.ctx.terms.mk_eq(app, rep));
                        }
                    }
                    for rep in seed.reps(&sig.result_sort) {
                        let eq = self.ctx.terms.mk_eq(app, rep);
                        if !options.contains(&eq) {
                            options.push(eq);
                        }
                    }
                }
                decisions.push((app, options));
                if decisions.len() > MAX_SATURATION_DECISIONS {
                    return None;
                }
            }
        }
        Some((literals, decisions))
    }

    /// Scoped backtracking over closure-application decisions. Bool
    /// applications get a single "option" (the application itself):
    /// try it true in a scope, else false.
    fn uf_decide_apps(
        solver: &mut ay_euf::EufSolver<'_>,
        decisions: &[(TermId, Vec<TermId>)],
        index: usize,
        nodes: &mut usize,
    ) -> bool {
        use ay_core::TheorySolver as _;
        if index == decisions.len() {
            return true;
        }
        *nodes += 1;
        if *nodes > MAX_SATURATION_NODES {
            return false;
        }
        let (app, options) = &decisions[index];
        // A Bool application's sole option is itself: try both
        // polarities. An equality option is only ever asserted true.
        let attempts: Vec<(TermId, bool)> = if options.len() == 1 && options[0] == *app {
            vec![(*app, true), (*app, false)]
        } else {
            options.iter().map(|&eq| (eq, true)).collect()
        };
        for (literal, polarity) in attempts {
            solver.push();
            solver.assert_literal(literal, polarity);
            let outcome = solver.check();
            if matches!(outcome, ay_core::TheoryResult::Sat)
                && Self::uf_decide_apps(solver, decisions, index + 1, nodes)
            {
                return true;
            }
            solver.pop();
        }
        false
    }

    /// `(atom, polarity)` when `term` is a ground literal the EUF
    /// saturation accepts directly.
    fn uf_literal(&self, term: TermId) -> Option<(TermId, bool)> {
        match self.ctx.terms.get(term) {
            TermData::App(_, _) => Some((term, true)),
            TermData::Not(inner) => match self.ctx.terms.get(*inner) {
                TermData::App(_, _) => Some((*inner, false)),
                _ => None,
            },
            _ => None,
        }
    }

    /// Bounded cross-product of representative columns.
    fn rep_tuples(columns: &[Vec<TermId>], limit: usize) -> Vec<Vec<TermId>> {
        let mut out: Vec<Vec<TermId>> = vec![Vec::new()];
        for column in columns {
            let mut next: Vec<Vec<TermId>> = Vec::new();
            for prefix in &out {
                for &rep in column {
                    if next.len() >= limit {
                        return next;
                    }
                    let mut tuple = prefix.clone();
                    tuple.push(rep);
                    next.push(tuple);
                }
            }
            out = next;
        }
        out
    }

    /// Complete pending closure rows with each symbol's modal known
    /// result (first domain element when nothing is known, false for
    /// Bool).
    fn uf_complete_pending(
        terms: &mut ay_core::TermStore,
        scan: &FragmentScan,
        domains: &UfDomains,
        tables: &mut HashMap<String, HashMap<Vec<String>, (Vec<TermId>, TermId, String)>>,
        pending: Vec<(String, Vec<String>, Vec<TermId>)>,
    ) -> Option<()> {
        for (name, key, rep_terms) in pending {
            let sig = &scan.signatures[&name];
            let modal = tables.get(&name).and_then(|rows| {
                let mut counts: HashMap<&String, usize> = HashMap::default();
                for (_, _, result) in rows.values() {
                    *counts.entry(result).or_default() += 1;
                }
                counts
                    .into_iter()
                    .max_by_key(|(_, count)| *count)
                    .map(|(value, _)| value.clone())
            });
            let (result_key, result_rep) = match modal {
                Some(value) => {
                    let rep = if matches!(sig.result_sort, Sort::Bool) {
                        if value == "true" {
                            terms.true_term()
                        } else {
                            terms.false_term()
                        }
                    } else {
                        domains.rep_for(&sig.result_sort, &value)?
                    };
                    (value, rep)
                }
                None if matches!(sig.result_sort, Sort::Bool) => {
                    ("false".to_string(), terms.false_term())
                }
                None => domains.entries(&sig.result_sort).into_iter().next()?,
            };
            tables
                .entry(name)
                .or_default()
                .insert(key, (rep_terms, result_rep, result_key));
        }
        Some(())
    }

    /// Close the domains under every tabled symbol and build its total
    /// table: rows keyed by VALUE tuples (representative term tuples
    /// for the installer), with functionality checked across
    /// representatives. Returns name → installer rows.
    pub(super) fn uf_closure_tables(
        &mut self,
        candidate: &Model,
        scan: &FragmentScan,
        domains: &UfDomains,
    ) -> Option<(UfDomains, HashMap<String, Vec<(Vec<TermId>, TermId)>>)> {
        let mut domains = domains.clone();
        let mut tables: HashMap<String, HashMap<Vec<String>, (Vec<TermId>, TermId, String)>> =
            HashMap::default();
        let mut pending: Vec<(String, Vec<String>, Vec<TermId>)> = Vec::new();
        let mut apps = 0usize;
        loop {
            let mut grew = false;
            for sig in scan.signatures.values() {
                if sig.arg_sorts.is_empty() {
                    continue;
                }
                let columns: Vec<Vec<(String, TermId)>> = sig
                    .arg_sorts
                    .iter()
                    .map(|sort| domains.entries(sort))
                    .collect();
                for tuple in Self::value_tuples(&columns, MAX_CLOSURE_APPS - apps) {
                    apps += 1;
                    if apps > MAX_CLOSURE_APPS {
                        return None;
                    }
                    let key: Vec<String> = tuple.iter().map(|(value, _)| value.clone()).collect();
                    let rows = tables.entry(sig.symbol.name().to_string()).or_default();
                    if rows.contains_key(&key) {
                        continue;
                    }
                    let rep_terms: Vec<TermId> = tuple.iter().map(|(_, rep)| *rep).collect();
                    let app = self.ctx.terms.mk_app(
                        sig.symbol.clone(),
                        rep_terms.clone(),
                        sig.result_sort.clone(),
                    );
                    // The candidate model need not be total on unseen
                    // tuples: those rows stay pending here and are
                    // completed below with the symbol's modal known
                    // result. The completion is a CHOICE that the
                    // verification below must discharge against every
                    // ground assertion and forall tuple. Installer rows
                    // carry a REPRESENTATIVE term for the result value
                    // (the installer re-evaluates it), never the
                    // application itself when the value was chosen.
                    let (result_key, result_rep) = match self.evaluate_term(candidate, app) {
                        EvalValue::Element(atom) => {
                            if domains.insert(sig.result_sort.clone(), atom.clone(), app)? {
                                grew = true;
                            }
                            let rep = domains.rep_for(&sig.result_sort, &atom)?;
                            (atom, rep)
                        }
                        EvalValue::Bool(false) => {
                            ("false".to_string(), self.ctx.terms.false_term())
                        }
                        EvalValue::Bool(true) => ("true".to_string(), self.ctx.terms.true_term()),
                        EvalValue::Unknown => {
                            pending.push((sig.symbol.name().to_string(), key, rep_terms));
                            continue;
                        }
                        _ => return None,
                    };
                    rows.insert(key, (rep_terms, result_rep, result_key));
                }
            }
            if !grew {
                break;
            }
        }
        Self::uf_complete_pending(&mut self.ctx.terms, scan, &domains, &mut tables, pending)?;
        // Functionality across representatives is already enforced by
        // value keying (one row per value tuple); totality needs every
        // value tuple present, which the loop guarantees by enumerating
        // the closed domains. Re-key to installer rows.
        let mut out: HashMap<String, Vec<(Vec<TermId>, TermId)>> = HashMap::default();
        for (name, rows) in tables {
            let sig = &scan.signatures[&name];
            let expected: usize = sig
                .arg_sorts
                .iter()
                .map(|sort| domains.reps(sort).len())
                .product();
            if rows.len() != expected {
                return None;
            }
            out.insert(
                name,
                rows.into_values()
                    .map(|(reps, app, _)| (reps, app))
                    .collect(),
            );
        }
        Some((domains, out))
    }

    /// Verify one forall over the full domain cross-product under the
    /// installed finite model.
    pub(super) fn uf_forall_holds_on_domains(
        &mut self,
        model: &Model,
        quant: TermId,
        domains: &UfDomains,
    ) -> bool {
        let TermData::Forall(bindings, body, _) = self.ctx.terms.get(quant).clone() else {
            return false;
        };
        let columns: Vec<Vec<TermId>> = bindings
            .iter()
            .map(|(_, sort)| domains.reps(sort))
            .collect();
        if columns.iter().any(Vec::is_empty) {
            return false;
        }
        let mut tuples = 0usize;
        self.uf_forall_tuples(
            model,
            body,
            &bindings,
            &columns,
            0,
            &mut Vec::new(),
            &mut tuples,
        )
    }

    fn uf_forall_tuples(
        &mut self,
        model: &Model,
        body: TermId,
        bindings: &[(String, Sort)],
        columns: &[Vec<TermId>],
        depth: usize,
        chosen: &mut Vec<TermId>,
        tuples: &mut usize,
    ) -> bool {
        if depth == columns.len() {
            *tuples += 1;
            if *tuples > MAX_FORALL_TUPLES {
                return false;
            }
            let substitution: HashMap<String, TermId> = bindings
                .iter()
                .map(|(name, _)| name.clone())
                .zip(chosen.iter().copied())
                .collect();
            let instance = subst_vars(&mut self.ctx.terms, body, &substitution);
            let value = self.evaluate_term(model, instance);
            return matches!(value, EvalValue::Bool(true));
        }
        for &rep in &columns[depth] {
            chosen.push(rep);
            let holds =
                self.uf_forall_tuples(model, body, bindings, columns, depth + 1, chosen, tuples);
            chosen.pop();
            if !holds {
                return false;
            }
        }
        true
    }

    /// Bounded cross-product of (value, representative) columns.
    fn value_tuples(columns: &[Vec<(String, TermId)>], limit: usize) -> Vec<Vec<(String, TermId)>> {
        let mut out: Vec<Vec<(String, TermId)>> = vec![Vec::new()];
        for column in columns {
            let mut next: Vec<Vec<(String, TermId)>> = Vec::new();
            for prefix in &out {
                for entry in column {
                    if next.len() >= limit {
                        return next;
                    }
                    let mut tuple = prefix.clone();
                    tuple.push(entry.clone());
                    next.push(tuple);
                }
            }
            out = next;
        }
        out
    }
}
