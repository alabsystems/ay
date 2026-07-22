// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! EUF model extraction.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, TermData, TermId};
use ay_core::Sort;
use std::collections::BTreeMap;

use crate::solver::EufSolver;
use crate::types::EufModel;

/// SMT-LIB long name of a rounding-mode literal symbol (either spelling).
/// Local map (both spellings) — `ay-euf` does not depend on `ay-fp`.
fn rounding_mode_long_name(name: &str) -> Option<&'static str> {
    match name {
        "RNE" | "roundNearestTiesToEven" => Some("roundNearestTiesToEven"),
        "RNA" | "roundNearestTiesToAway" => Some("roundNearestTiesToAway"),
        "RTP" | "roundTowardPositive" => Some("roundTowardPositive"),
        "RTN" | "roundTowardNegative" => Some("roundTowardNegative"),
        "RTZ" | "roundTowardZero" => Some("roundTowardZero"),
        _ => None,
    }
}

fn format_bitvec_value(value: &num_bigint::BigInt, width: u32) -> String {
    let modulus = num_bigint::BigInt::from(1u8) << width;
    let normalized = ((value % &modulus) + &modulus) % &modulus;
    if width.is_multiple_of(4) {
        let digits = (width / 4) as usize;
        format!("#x{:0>digits$}", normalized.to_str_radix(16))
    } else {
        format!(
            "#b{:0>width$}",
            normalized.to_str_radix(2),
            width = width as usize
        )
    }
}

impl EufSolver<'_> {
    fn model_table_arg_value(&self, model: &EufModel, arg: TermId) -> String {
        if matches!(self.terms.sort(arg), Sort::Bool) {
            if let Some(value) = self.assigns.get(&arg).copied() {
                return if value {
                    "true".to_string()
                } else {
                    "false".to_string()
                };
            }
            if let Some(raw) = model.term_values.get(&arg) {
                if raw == "true" || raw == "false" {
                    return raw.clone();
                }
            }
            return format!("@?{}", arg.0);
        }
        if let Some(value) = model.term_values.get(&arg) {
            return value.clone();
        }
        format!("@?{}", arg.0)
    }

    /// Extract a model after solving (call after check() returns Sat)
    ///
    /// Returns an `EufModel` containing:
    /// - Element representatives for uninterpreted sorts
    /// - Term-to-element mappings
    /// - Function table interpretations for uninterpreted functions
    pub fn extract_model(&mut self) -> EufModel {
        // Ensure congruence closure is up-to-date
        self.rebuild_closure();

        let mut model = EufModel::default();
        let model_terms = self.scoped_model_terms();

        // Collect equivalence class representatives per sort
        // Maps (sort_name, representative_id) -> element_name
        let mut rep_to_elem: HashMap<(String, u32), String> = HashMap::default();
        // Counter for generating element names per sort
        let mut sort_counters: HashMap<String, usize> = HashMap::default();

        // Pre-pass (#P0.2 symbolic RoundingMode): a `RoundingMode` class that
        // contains a literal mode constant (`RNE` … `RTZ`, nullary apps) takes
        // that literal's SMT-LIB long name as its element name instead of a
        // minted `@RoundingMode!n` token. RoundingMode is a FIXED 5-element
        // domain — an abstract token is not a valid value of the sort (z3
        // prints `roundTowardPositive` etc., and re-asserting a token model
        // fails), and the executor's finite-domain coverage pass guarantees
        // every constrained RM term's class contains a literal. Runs before
        // the general pass so the literal name wins regardless of member
        // visit order.
        for &term_id in &model_terms {
            if !matches!(self.terms.sort(term_id), Sort::Uninterpreted(name) if name == "RoundingMode")
            {
                continue;
            }
            let long_name = match self.terms.get(term_id) {
                TermData::App(sym, args) if args.is_empty() => rounding_mode_long_name(sym.name()),
                _ => None,
            };
            if let Some(long_name) = long_name {
                let key = ("RoundingMode".to_string(), self.uf.find(term_id.0));
                rep_to_elem.entry(key).or_insert_with(|| {
                    model
                        .sort_elements
                        .entry("RoundingMode".to_string())
                        .or_default()
                        .push(long_name.to_string());
                    long_name.to_string()
                });
            }
        }

        // First pass: assign element names to representatives
        for &term_id in &model_terms {
            let sort = self.terms.sort(term_id);

            // Only process uninterpreted sorts
            let sort_name = match sort {
                Sort::Uninterpreted(name) => name.clone(),
                _ => continue,
            };

            let rep = self.uf.find(term_id.0);
            let key = (sort_name.clone(), rep);

            if !rep_to_elem.contains_key(&key) {
                let counter = sort_counters.entry(sort_name.clone()).or_insert(0);
                let elem_name = format!("@{sort_name}!{counter}");
                *counter += 1;

                rep_to_elem.insert(key.clone(), elem_name.clone());

                // Add to sort_elements
                model
                    .sort_elements
                    .entry(sort_name)
                    .or_default()
                    .push(elem_name);
            }
        }

        // Second pass: map each term to its element name
        for &term_id in &model_terms {
            let sort = self.terms.sort(term_id);

            let sort_name = match sort {
                Sort::Uninterpreted(name) => name.clone(),
                _ => continue,
            };

            let rep = self.uf.find(term_id.0);
            let key = (sort_name, rep);

            if let Some(elem_name) = rep_to_elem.get(&key) {
                model.term_values.insert(term_id, elem_name.clone());
            }
        }

        // Assign distinct integer values to Int-sorted equivalence classes (#3172).
        // When EUF manages Int-sorted terms without a LIA/LRA solver, the model
        // validator defaults all unassigned ints to 0, violating disequalities.
        // Prefer actual constant values from terms in each class so that
        // validate_model sees consistent values for (= c 5) style assertions.
        {
            use num_bigint::BigInt;

            // First pass: find constant values per equivalence class.
            //
            // #uflia-scoped-class-const: the class constant must be searched over
            // the WHOLE equivalence class, not just the model SCOPE. `model_terms`
            // is scoped to the terms reachable from `ctx.assertions`
            // (`scope_model_to_roots`), a perf restriction on which terms receive a
            // value — but an Int constant merged into a class by an atom created
            // DURING search (e.g. the value-enumeration atom `(= s5 (- 1))`, whose
            // `(- 1)` constant term is not reachable from any original assertion)
            // is outside that scope. Scanning only scoped members therefore missed
            // it and fabricated a fresh counter value for a class the solver had
            // already pinned to a concrete integer — a model that contradicts the
            // committed SAT trail, which the independent model gate then (rightly)
            // refuted, degrading a genuine `sat` to `unknown`.
            // `find_int_const_in_class` walks the e-graph class itself, so it sees
            // the out-of-scope constant. Reps with no constant are memoized in
            // `rep_no_const` so a constant-free class is scanned once, not once per
            // member (no quadratic blow-up on large classes).
            let mut rep_const_val: HashMap<u32, BigInt> = HashMap::default();
            // (a) Scoped members (also the only path in legacy, non-e-graph mode,
            // where `find_int_const_in_class` cannot answer).
            for &term_id in &model_terms {
                if !matches!(self.terms.sort(term_id), Sort::Int) {
                    continue;
                }
                if let TermData::Const(Constant::Int(n)) = self.terms.get(term_id) {
                    let rep = self.uf.find(term_id.0);
                    rep_const_val.entry(rep).or_insert_with(|| n.clone());
                }
            }
            // (b) Out-of-scope class members, via the e-graph class itself.
            let mut rep_no_const: HashSet<u32> = HashSet::default();
            for &term_id in &model_terms {
                if !matches!(self.terms.sort(term_id), Sort::Int) {
                    continue;
                }
                let rep = self.uf.find(term_id.0);
                if rep_const_val.contains_key(&rep) || !rep_no_const.insert(rep) {
                    continue;
                }
                if let Some((n, _)) = self.find_int_const_in_class(term_id) {
                    rep_no_const.remove(&rep);
                    rep_const_val.insert(rep, n);
                }
            }

            // Second pass: assign values - use constant if available, else counter
            let mut int_rep_to_val: HashMap<u32, BigInt> = HashMap::default();
            // #uflia-arith-arg-key: reps whose value is a fresh counter, not
            // a class constant — recorded per-term below.
            let mut fabricated_reps: HashSet<u32> = HashSet::default();
            // Start counter from a value unlikely to collide with constants
            let mut used_values: HashSet<BigInt> = rep_const_val.values().cloned().collect();
            let mut int_counter: i64 = 0;

            for &term_id in &model_terms {
                if !matches!(self.terms.sort(term_id), Sort::Int) {
                    continue;
                }

                let rep = self.uf.find(term_id.0);
                let val = int_rep_to_val
                    .entry(rep)
                    .or_insert_with(|| {
                        if let Some(const_val) = rep_const_val.get(&rep) {
                            const_val.clone()
                        } else {
                            fabricated_reps.insert(rep);
                            // Find a value not used by any constant
                            loop {
                                let v = BigInt::from(int_counter);
                                int_counter += 1;
                                if !used_values.contains(&v) {
                                    used_values.insert(v.clone());
                                    return v;
                                }
                            }
                        }
                    })
                    .clone();
                if fabricated_reps.contains(&rep) {
                    model.speculative_int_terms.insert(term_id);
                }
                model.int_values.insert(term_id, val);
            }
        }

        // Materialize BitVec-sorted equivalence classes into the generic term
        // value map. Array+EUF deliberately has no separate BV solver: it uses
        // EUF for equality-only BV indices/elements and passes this map directly
        // to ArraySolver::extract_model. Previously extract_model populated only
        // uninterpreted sorts (plus the separate Int bridge), so every BV index
        // and select was absent and a valid array counterexample degraded to an
        // incomplete model/Unknown.
        //
        // Concrete literals are authoritative for their whole e-class. For an
        // unpinned class choose a deterministic value, preferring a globally
        // fresh value and reusing one only after the finite domain is exhausted.
        // Reuse excludes values already assigned to a committed-disequal class.
        // If a greedy finite-domain completion cannot find a value, leave that
        // class absent: downstream validation then fails closed instead of
        // accepting a fabricated BV model.
        {
            use num_bigint::BigInt;

            let mut rep_to_terms: BTreeMap<(u32, u32), Vec<TermId>> = BTreeMap::new();
            for &term_id in &model_terms {
                let Sort::BitVec(sort) = self.terms.sort(term_id) else {
                    continue;
                };
                let rep = self.uf.find(term_id.0);
                rep_to_terms
                    .entry((sort.width, rep))
                    .or_default()
                    .push(term_id);
            }

            let mut rep_constants: HashMap<(u32, u32), BigInt> = HashMap::default();
            for (&key, terms) in &rep_to_terms {
                let scoped = terms.iter().find_map(|&term| match self.terms.get(term) {
                    TermData::Const(Constant::BitVec { value, width }) if *width == key.0 => {
                        Some(value.clone())
                    }
                    _ => None,
                });
                let whole_class = scoped.or_else(|| {
                    if !self.enodes_init || key.1 as usize >= self.enodes.len() {
                        return None;
                    }
                    self.enode_class_iter(key.1).find_map(|member| {
                        match self.terms.get(TermId(member)) {
                            TermData::Const(Constant::BitVec { value, width })
                                if *width == key.0 =>
                            {
                                Some(value.clone())
                            }
                            _ => None,
                        }
                    })
                });
                if let Some(value) = whole_class {
                    rep_constants.insert(key, value);
                }
            }

            // Build the e-class disequality graph from committed false
            // equalities and true `distinct` atoms. This matters only when a
            // tiny BV domain has fewer values than reachable e-classes.
            let mut disequal: HashMap<(u32, u32), HashSet<(u32, u32)>> = HashMap::default();
            let mut disequal_pairs = Vec::new();
            for (&literal, &value) in &self.assigns {
                if !value {
                    if let Some((lhs, rhs)) = self.decode_eq(literal) {
                        disequal_pairs.push((lhs, rhs));
                    }
                    continue;
                }
                if let Some(args) = self.decode_distinct(literal) {
                    for i in 0..args.len() {
                        for j in (i + 1)..args.len() {
                            disequal_pairs.push((args[i], args[j]));
                        }
                    }
                }
            }
            for (lhs, rhs) in disequal_pairs {
                let (Sort::BitVec(lhs_sort), Sort::BitVec(rhs_sort)) =
                    (self.terms.sort(lhs), self.terms.sort(rhs))
                else {
                    continue;
                };
                if lhs_sort.width != rhs_sort.width {
                    continue;
                }
                let lhs_key = (lhs_sort.width, self.uf.find(lhs.0));
                let rhs_key = (rhs_sort.width, self.uf.find(rhs.0));
                if lhs_key == rhs_key {
                    continue;
                }
                disequal.entry(lhs_key).or_default().insert(rhs_key);
                disequal.entry(rhs_key).or_default().insert(lhs_key);
            }

            let mut assigned: HashMap<(u32, u32), BigInt> = HashMap::default();
            let mut used_by_width: HashMap<u32, HashSet<BigInt>> = HashMap::default();
            for (&key, value) in &rep_constants {
                assigned.insert(key, value.clone());
                used_by_width
                    .entry(key.0)
                    .or_default()
                    .insert(value.clone());
            }

            for (&key, terms) in &rep_to_terms {
                if !assigned.contains_key(&key) {
                    let modulus = BigInt::from(1u8) << key.0;
                    let used = used_by_width.entry(key.0).or_default();
                    let mut candidate = BigInt::from(0u8);
                    while candidate < modulus && used.contains(&candidate) {
                        candidate += 1u8;
                    }

                    // Once all values have appeared somewhere, reuse a value
                    // that is not used by any already-valued disequal neighbor.
                    if candidate == modulus {
                        candidate = BigInt::from(0u8);
                        while candidate < modulus
                            && disequal.get(&key).is_some_and(|neighbors| {
                                neighbors.iter().any(|neighbor| {
                                    assigned.get(neighbor).is_some_and(|v| v == &candidate)
                                })
                            })
                        {
                            candidate += 1u8;
                        }
                    }

                    if candidate < modulus {
                        used.insert(candidate.clone());
                        assigned.insert(key, candidate);
                    }
                }

                if let Some(value) = assigned.get(&key) {
                    let formatted = format_bitvec_value(value, key.0);
                    for &term in terms {
                        model.term_values.insert(term, formatted.clone());
                    }
                }
            }
        }

        // Third pass: build function tables for uninterpreted functions
        // Use BTreeMap for deterministic ordering
        let mut fn_entries: BTreeMap<String, Vec<(Vec<String>, String, TermId)>> = BTreeMap::new();
        // Separate tracking for predicates (Bool-returning functions)
        let mut pred_entries: BTreeMap<String, Vec<(Vec<String>, String, TermId)>> =
            BTreeMap::new();

        for &term_id in &model_terms {
            // Get function applications
            let (sym, args) = match self.terms.get(term_id) {
                TermData::App(sym, args) if !Self::is_builtin_symbol(sym) => {
                    (sym.clone(), args.clone())
                }
                _ => continue,
            };

            // Skip nullary functions (constants) - handled in second pass
            if args.is_empty() {
                continue;
            }

            let result_sort = self.terms.sort(term_id);

            // Get element names for arguments
            let arg_values: Vec<String> = args
                .iter()
                .map(|&arg| self.model_table_arg_value(&model, arg))
                .collect();

            // Handle predicates (Bool-sorted functions) using assigns
            if matches!(result_sort, Sort::Bool) {
                // Get value from assigns (SAT model propagated to theory)
                let result_value = match self.assigns.get(&term_id) {
                    Some(true) => "true".to_string(),
                    Some(false) | None => "false".to_string(), // Default unassigned to false
                };

                pred_entries.entry(sym.to_string()).or_default().push((
                    arg_values,
                    result_value,
                    term_id,
                ));
                continue;
            }

            // Get element name for result (non-Bool functions)
            let result_value = model
                .term_values
                .get(&term_id)
                .cloned()
                .unwrap_or_else(|| format!("@?{}", term_id.0));

            fn_entries.entry(sym.to_string()).or_default().push((
                arg_values,
                result_value,
                term_id,
            ));
        }

        // Deduplicate function table entries by representative
        for (fn_name, entries) in fn_entries {
            let mut seen: HashMap<Vec<String>, String> = HashMap::default();
            let mut table = Vec::new();
            let mut source_terms = Vec::new();

            for (args, result, term_id) in entries {
                // Use first occurrence for each argument combination
                if !seen.contains_key(&args) {
                    seen.insert(args.clone(), result.clone());
                    table.push((args, result));
                    source_terms.push(term_id);
                }
            }

            if !table.is_empty() {
                model
                    .function_table_terms
                    .insert(fn_name.clone(), source_terms);
                model.function_tables.insert(fn_name, table);
            }
        }

        // Deduplicate predicate table entries
        for (pred_name, entries) in pred_entries {
            let mut seen: HashMap<Vec<String>, String> = HashMap::default();
            let mut table = Vec::new();
            let mut source_terms = Vec::new();

            for (args, result, term_id) in entries {
                // Use first occurrence for each argument combination
                if !seen.contains_key(&args) {
                    seen.insert(args.clone(), result.clone());
                    table.push((args, result));
                    source_terms.push(term_id);
                }
            }

            if !table.is_empty() {
                model
                    .function_table_terms
                    .insert(pred_name.clone(), source_terms);
                model.function_tables.insert(pred_name, table);
            }
        }

        // Populate func_app_const_terms from tracked values (#385)
        // This enables get-value to return actual values for UF applications returning Int/Real/BV
        model.func_app_const_terms.clone_from(&self.func_app_values);

        model
    }

    /// Extract SMT-LIB values for Int-sorted terms based on the current EUF equivalence classes.
    ///
    /// This is used for model printing in contexts that rely on EUF equalities but do not run
    /// the dedicated arithmetic theories (e.g., `QF_AX` with `Int` indices/elements).
    ///
    /// The returned map assigns a *distinct* integer to each equivalence class, preferring a
    /// concrete integer constant if one is present in the class.
    /// Returns the per-term Int class values, plus the subset of terms whose
    /// value is a FABRICATED fresh integer (#uflia-arith-arg-key).
    pub fn extract_int_term_values(
        &mut self,
    ) -> (
        HashMap<TermId, String>,
        ay_core::kani_compat::DetHashSet<TermId>,
    ) {
        self.rebuild_closure();
        let model_terms = self.scoped_model_terms();

        // Group Int-sorted terms by their equivalence-class representative.
        let mut rep_to_terms: BTreeMap<u32, Vec<TermId>> = BTreeMap::new();
        for &term_id in &model_terms {
            if self.terms.sort(term_id) != &Sort::Int {
                continue;
            }
            let rep = self.uf.find(term_id.0);
            rep_to_terms.entry(rep).or_default().push(term_id);
        }

        // Prefer a concrete Int constant if present; otherwise assign fresh integers.
        let mut used_values: HashSet<String> = HashSet::default();
        let mut rep_to_value: BTreeMap<u32, String> = BTreeMap::new();

        let format_int_value = |n_str: &str| -> String {
            if let Some(rest) = n_str.strip_prefix('-') {
                format!("(- {rest})")
            } else {
                n_str.to_string()
            }
        };

        for (&rep, terms) in &rep_to_terms {
            // #uflia-scoped-class-const: search the WHOLE e-graph class, not just
            // its members inside the model scope. A constant merged into the class
            // by a search-created atom (e.g. `(= s5 (- 1))` from value enumeration)
            // is not reachable from `ctx.assertions` and so never appears in
            // `rep_to_terms`; missing it fabricated a fresh integer for a class the
            // solver had already pinned, producing a model that contradicts the
            // committed trail. The scoped scan stays first: it is the only path in
            // legacy (non-e-graph) mode, where `find_int_const_in_class` is `None`.
            let const_value = terms
                .iter()
                .find_map(|&t| match self.terms.get(t) {
                    TermData::Const(Constant::Int(n)) => Some(n.clone()),
                    _ => None,
                })
                .or_else(|| {
                    terms
                        .first()
                        .and_then(|&t| self.find_int_const_in_class(t))
                        .map(|(n, _)| n)
                })
                .map(|n| format_int_value(&n.to_string()));
            if let Some(v) = const_value {
                used_values.insert(v.clone());
                rep_to_value.insert(rep, v);
            }
        }

        let mut next_fresh: u64 = 0;
        // #uflia-arith-arg-key: reps assigned a fresh counter (no class
        // constant) — their members are reported as speculative.
        let mut fabricated_reps: HashSet<u32> = HashSet::default();
        for &rep in rep_to_terms.keys() {
            if rep_to_value.contains_key(&rep) {
                continue;
            }
            fabricated_reps.insert(rep);
            loop {
                let cand = next_fresh.to_string();
                next_fresh += 1;
                if used_values.insert(cand.clone()) {
                    rep_to_value.insert(rep, cand);
                    break;
                }
            }
        }

        // Expand class values back to term_id -> value.
        let mut term_values: HashMap<TermId, String> = HashMap::default();
        let mut speculative: ay_core::kani_compat::DetHashSet<TermId> = Default::default();
        for (rep, terms) in rep_to_terms {
            let value = rep_to_value
                .get(&rep)
                .cloned()
                .unwrap_or_else(|| "0".to_string());
            for term in terms {
                if fabricated_reps.contains(&rep) {
                    speculative.insert(term);
                }
                term_values.insert(term, value.clone());
            }
        }

        (term_values, speculative)
    }
}
