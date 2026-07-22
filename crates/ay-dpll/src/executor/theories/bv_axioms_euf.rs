// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BV-return EUF congruence axiom generation for combined BV theories (UFBV, AUFBV).
//!
//! Generates congruence axioms for uninterpreted functions with BV return types
//! as CNF clauses using bit-level XOR diff vars. Also contains the shared
//! `collect_uf_applications` traversal used by both this module and sibling
//! `bv_axioms_non_bv.rs` (non-BV return type congruence).
//!
//! Split from `bv_axioms.rs` for code health (#7006, #5970).

// #8529: Use deterministic hash maps in all builds.
use ay_bv::BvSolver;
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Symbol, TermData};
use ay_core::TermId;

use super::super::Executor;
use super::EufAxiomResult;

impl Executor {
    /// Reify array-sorted equality atoms for UF arguments so the array theory ↔
    /// EUF congruence interface can share them (#12, Nelson-Oppen gap).
    ///
    /// In QF_AUFBV, an uninterpreted function can take whole-array arguments
    /// (e.g. `h(a)`, `h(b)` with `a`, `b` of array sort). Congruence requires
    /// `(= a b) → (= h(a) h(b))`. The BV congruence generator drops such pairs
    /// because arrays have no BV bits, and the non-BV congruence generator
    /// (`generate_non_bv_euf_congruence` / `build_arg_diff_vars`) can only encode
    /// the argument-difference when a Tseitin variable already exists for the
    /// equality atom `(= a b)`.
    ///
    /// When `a = b` is only *derivable* by the array theory (e.g. a store that
    /// is a no-op: `a = store(b, i, select a i)` with `select a i = select b i`),
    /// the atom `(= a b)` is never syntactically present, so it has no Tseitin
    /// variable, `build_arg_diff_vars` reports `Unencodable`, and the congruence
    /// pair is silently skipped. The array theory derives `a = b` but it never
    /// reaches the UF layer, so `h(a) = h(b)` does not fire and a disequality
    /// `(distinct (h a) (h b))` is wrongly satisfiable.
    ///
    /// Fix: for every pair of array-sorted argument terms feeding the same UF
    /// function, materialize the equality atom `(= a b)` as a *tautology*
    /// assertion `(or (= a b) (not (= a b)))`. This is semantically vacuous (it
    /// adds no constraint) but forces the atom into Tseitin internalization AND
    /// array-axiom generation (ROW / extensionality reason about `(= a b)`),
    /// closing the sharing gap: the array theory can now drive `(= a b)` true,
    /// and the already-generated congruence clause then forces `h(a) = h(b)`.
    ///
    /// Returns the number of array-equality atoms newly reified.
    pub(in crate::executor) fn reify_array_uf_arg_equalities(
        &mut self,
        extra_terms: &[TermId],
    ) -> usize {
        use ay_core::Sort;

        // Keyed by (name, arity): in EUF/Ackermannization `f/2` and `f/3` are
        // DISTINCT function symbols, so applications at different arities must
        // not share a bucket (#4661).
        let mut uf_apps: HashMap<(String, usize), Vec<(TermId, Vec<TermId>)>> = HashMap::default();
        let mut visited = HashSet::default();
        for &assertion in &self.ctx.assertions {
            self.collect_uf_applications(assertion, &mut uf_apps, &mut visited);
        }
        for &term in extra_terms {
            self.collect_uf_applications(term, &mut uf_apps, &mut visited);
        }

        // Collect the unordered array-sorted argument pairs that need a reified
        // equality atom. Use a dedup set so we add each tautology at most once.
        let mut arg_pairs: Vec<(TermId, TermId)> = Vec::new();
        let mut seen_pairs: HashSet<(TermId, TermId)> = HashSet::default();
        for applications in uf_apps.values() {
            if applications.len() < 2 {
                continue;
            }
            for i in 0..applications.len() {
                for j in (i + 1)..applications.len() {
                    let (_t1, args1) = &applications[i];
                    let (_t2, args2) = &applications[j];
                    if args1.len() != args2.len() {
                        continue;
                    }
                    for (&a1, &a2) in args1.iter().zip(args2.iter()) {
                        if a1 == a2 {
                            continue;
                        }
                        // Only array-sorted args need this — BV args get bit-level
                        // diff vars and never hit the Unencodable path.
                        if !matches!(self.ctx.terms.sort(a1), Sort::Array(_)) {
                            continue;
                        }
                        if self.ctx.terms.sort(a1) != self.ctx.terms.sort(a2) {
                            continue;
                        }
                        let key = if a1.0 <= a2.0 { (a1, a2) } else { (a2, a1) };
                        if seen_pairs.insert(key) {
                            arg_pairs.push(key);
                        }
                    }
                }
            }
        }

        let mut reified = 0usize;
        for (a1, a2) in arg_pairs {
            let eq = self.ctx.terms.mk_eq(a1, a2);
            // If mk_eq folded to a constant (e.g. identical canonical form), the
            // congruence is trivial — nothing to reify.
            if matches!(self.ctx.terms.get(eq), TermData::Const(_)) {
                continue;
            }
            let not_eq = self.ctx.terms.mk_not(eq);
            let taut = self.ctx.terms.mk_or(vec![eq, not_eq]);
            // Skip if mk_or folded to `true` constant with no reifiable atom; in
            // practice it stays an Or over the eq atom so Tseitin internalizes eq.
            self.ctx.assertions.push(taut);
            reified += 1;
        }
        reified
    }

    /// Ensure UF application arguments that are BV-sorted are bitblasted before
    /// congruence axiom generation. Complex BV sub-expressions (e.g., `bvadd(x, #x01)`)
    /// inside UF calls are opaque to the BV bitblaster and need explicit materialization,
    /// just like array indices need materialization in `materialize_array_bv_terms`.
    /// Without this, `get_term_bits` returns None for complex BV args, causing the
    /// congruence axiom to be skipped entirely (#5475 Gap B).
    pub(in crate::executor) fn materialize_uf_arg_bv_terms(
        &self,
        bv_solver: &mut BvSolver<'_>,
        extra_terms: &[TermId],
    ) {
        // Keyed by (name, arity) — distinct arities are distinct UF symbols (#4661).
        let mut uf_apps: HashMap<(String, usize), Vec<(TermId, Vec<TermId>)>> = HashMap::default();
        let mut visited = HashSet::default();
        for &assertion in &self.ctx.assertions {
            self.collect_uf_applications(assertion, &mut uf_apps, &mut visited);
        }
        for &term in extra_terms {
            self.collect_uf_applications(term, &mut uf_apps, &mut visited);
        }

        for (_key, applications) in &uf_apps {
            for (_term, args) in applications {
                for &arg in args {
                    let _ = bv_solver.ensure_term_bits(arg);
                }
            }
            // Also ensure result term bits are available
            for (term, _args) in applications {
                let _ = bv_solver.ensure_term_bits(*term);
            }
        }
    }

    /// Collect the Bool-sorted argument terms of UF applications that can form
    /// congruence pairs (buckets with >= 2 same-symbol, same-arity
    /// applications), in deterministic order (#boolarg-congruence).
    ///
    /// Bool-sorted UF arguments have no BV bits, so both congruence generators
    /// previously dropped every application pair containing one — congruence
    /// over Bool argument positions was silently lost in the eager-bitblast
    /// route (QF_UFBV / QF_AUFBV). With 256 ground instances of
    /// `(= (BoolUnbox (BoolBox c)) c)` from finite-domain quantifier
    /// expansion, the missing 2-into-256 pigeonhole made an UNSAT instance
    /// answer `sat` (wrong-SAT; the quantified path defers model validation,
    /// so the independent-model-check gate never caught it).
    ///
    /// The caller materializes a single CNF literal for each returned term via
    /// `BvSolver::ensure_bool_literal` BEFORE Tseitin↔BV linking, so
    /// `build_linking_batch` bridges the literal to an existing Tseitin
    /// variable for the same term (when one exists) and the congruence
    /// generators can encode the argument difference as a 1-bit XOR.
    pub(in crate::executor) fn collect_uf_bool_args(&self, extra_terms: &[TermId]) -> Vec<TermId> {
        use ay_core::Sort;
        // Keyed by (name, arity) — distinct arities are distinct UF symbols (#4661).
        let mut uf_apps: HashMap<(String, usize), Vec<(TermId, Vec<TermId>)>> = HashMap::default();
        let mut visited = HashSet::default();
        for &assertion in &self.ctx.assertions {
            self.collect_uf_applications(assertion, &mut uf_apps, &mut visited);
        }
        for &term in extra_terms {
            self.collect_uf_applications(term, &mut uf_apps, &mut visited);
        }

        let mut seen: HashSet<TermId> = HashSet::default();
        let mut bool_args: Vec<TermId> = Vec::new();
        for applications in uf_apps.values() {
            // A single application never forms a congruence pair — skip to
            // avoid allocating dead literals.
            if applications.len() < 2 {
                continue;
            }
            for (_term, args) in applications {
                for &arg in args {
                    if matches!(self.ctx.terms.sort(arg), Sort::Bool) && seen.insert(arg) {
                        bool_args.push(arg);
                    }
                }
            }
        }
        // Deterministic literal allocation order regardless of map iteration.
        bool_args.sort_unstable_by_key(|t| t.0);
        bool_args
    }

    /// Generate EUF congruence axiom clauses for QF_UFBV/QF_AUFBV (with debug output)
    pub(in crate::executor) fn generate_euf_bv_axioms_debug(
        &self,
        bv_solver: &BvSolver<'_>,
        bv_offset: u32,
        var_offset: u32,
        debug: bool,
        extra_terms: &[TermId],
    ) -> EufAxiomResult {
        let mut result = EufAxiomResult {
            clauses: Vec::new(),
            num_vars: 0,
        };

        // Collect all uninterpreted function applications from assertions AND
        // extra terms (e.g., assumptions). UF applications in assumptions like
        // `distinct(f(x), f(y))` must be included for congruence axiom generation.
        // Keyed by (name, arity): `f/2` and `f/3` are distinct symbols and
        // congruence only relates equal-arity applications (#4661).
        let mut uf_apps: HashMap<(String, usize), Vec<(TermId, Vec<TermId>)>> = HashMap::default();
        let mut visited = HashSet::default();

        for &assertion in &self.ctx.assertions {
            self.collect_uf_applications(assertion, &mut uf_apps, &mut visited);
        }
        for &term in extra_terms {
            self.collect_uf_applications(term, &mut uf_apps, &mut visited);
        }

        if debug {
            safe_eprintln!("DEBUG: Collected UF applications:");
            for ((name, _arity), apps) in &uf_apps {
                safe_eprintln!("  Function '{}' has {} applications:", name, apps.len());
                for (term, args) in apps {
                    let term_bits = bv_solver.get_term_bits(*term);
                    safe_eprintln!(
                        "    Term {:?} with args {:?}, bits: {:?}",
                        term,
                        args,
                        term_bits.map(<[i32]>::to_vec)
                    );
                    for (i, arg) in args.iter().enumerate() {
                        let arg_bits = bv_solver.get_term_bits(*arg);
                        safe_eprintln!(
                            "      Arg {}: term {:?}, bits: {:?}",
                            i,
                            arg,
                            arg_bits.map(<[i32]>::to_vec)
                        );
                    }
                }
            }
        }

        let mut next_var = var_offset + 1;

        // Single-literal view of a term in the BV solver's variable space
        // (#boolarg-congruence): BV-sorted terms yield their bit vector;
        // Bool-sorted terms yield the 1-element vector of their
        // `bool_to_var` literal (materialized by `collect_uf_bool_args` +
        // `ensure_bool_literal` before linking, so the literal is bridged to
        // any Tseitin variable for the same term). Both literal kinds live in
        // the same BV variable space and take the same `bv_offset` shift.
        // Bool results are covered too, so nested Bool-return applications
        // (e.g. `(BoolBox c)` appearing only as a `BoolUnbox` argument) get
        // congruence over their BV arguments as well. Terms with neither
        // representation return None and keep the historical skip behavior.
        let bv_lits_for = |t: TermId| -> Option<Vec<i32>> {
            if let Some(bits) = bv_solver.get_term_bits(t) {
                return Some(bits.to_vec());
            }
            if matches!(self.ctx.terms.sort(t), ay_core::Sort::Bool) {
                return bv_solver.bool_to_var().get(&t).map(|&lit| vec![lit]);
            }
            None
        };

        for ((func_name, arity), applications) in &uf_apps {
            if applications.len() < 2 {
                continue;
            }

            // Because the map is keyed by (name, arity), every application in this
            // bucket shares `arity`. This documents/guards that invariant (#4661):
            // in EUF, `f/2` and `f/3` are distinct symbols and only equal-arity
            // applications are congruence-related. (Previously `uf_apps` was keyed
            // by name only, which conflated arities and tripped this assert on
            // mixed-arity `*`/`+` abstractions — the compiler_consumer Group-B ICE.)
            debug_assert!(
                applications.iter().all(|(_, args)| args.len() == *arity),
                "BUG: UF '{func_name}/{arity}' bucket has application with wrong arity"
            );

            for i in 0..applications.len() {
                for j in (i + 1)..applications.len() {
                    let (term1, args1) = &applications[i];
                    let (term2, args2) = &applications[j];

                    // Same-bucket applications share `arity`, so this is a no-op
                    // guard kept for defensive clarity.
                    if args1.len() != args2.len() {
                        continue;
                    }

                    // Result-sort guard (#dt-shared-selector-result-sort): a
                    // symbol NAME can be shared across sorts, and a Bool
                    // 1-literal view must never be congruence-paired with a
                    // BV1 bit vector of an unrelated same-name application.
                    // Same-sorted pairs (the well-typed case) always pass.
                    if self.ctx.terms.sort(*term1) != self.ctx.terms.sort(*term2) {
                        continue;
                    }
                    let bits1 = match bv_lits_for(*term1) {
                        Some(b) => b,
                        None => {
                            if debug {
                                safe_eprintln!(
                                    "DEBUG: Skipping pair - term1 {:?} has no bits",
                                    term1
                                );
                            }
                            continue;
                        }
                    };
                    let bits2 = match bv_lits_for(*term2) {
                        Some(b) => b,
                        None => {
                            if debug {
                                safe_eprintln!(
                                    "DEBUG: Skipping pair - term2 {:?} has no bits",
                                    term2
                                );
                            }
                            continue;
                        }
                    };

                    if bits1.len() != bits2.len() || bits1.is_empty() {
                        continue;
                    }

                    if debug {
                        safe_eprintln!(
                            "DEBUG: Generating congruence axiom for {}({:?}) and {}({:?})",
                            func_name,
                            args1,
                            func_name,
                            args2
                        );
                        safe_eprintln!("  term1 bits (unoffset): {:?}", bits1);
                        safe_eprintln!("  term2 bits (unoffset): {:?}", bits2);
                    }

                    let offset_bit = |bit: i32| -> i32 {
                        if bit > 0 {
                            bit + bv_offset as i32
                        } else {
                            bit - bv_offset as i32
                        }
                    };

                    let mut all_diff_vars = Vec::new();
                    let mut all_args_have_bits = true;

                    for (arg_idx, (arg1, arg2)) in args1.iter().zip(args2.iter()).enumerate() {
                        // Identical arguments cannot differ — skip (#5457).
                        // Without this, get_term_bits on a shared arg that was
                        // never independently bitblasted returns None, which
                        // sets all_args_have_bits=false and drops the entire
                        // congruence axiom for the pair.
                        if arg1 == arg2 {
                            continue;
                        }
                        // Arg-sort guard: mirror of the result-sort guard —
                        // never relate a Bool literal to a BV1 bit under a
                        // shared symbol name. Different-sorted args can never
                        // be equal, so the pair's congruence premise "all
                        // args equal" is unsatisfiable and the whole pair can
                        // be skipped (no clause needed) — matching the
                        // non-BV generator's #2682 handling.
                        if self.ctx.terms.sort(*arg1) != self.ctx.terms.sort(*arg2) {
                            all_args_have_bits = false;
                            break;
                        }
                        let arg1_bits = bv_lits_for(*arg1);
                        let arg2_bits = bv_lits_for(*arg2);

                        match (arg1_bits.as_deref(), arg2_bits.as_deref()) {
                            (Some(b1), Some(b2)) if b1.len() == b2.len() && !b1.is_empty() => {
                                if debug {
                                    safe_eprintln!(
                                        "  Arg {} pair: {:?} vs {:?}",
                                        arg_idx,
                                        arg1,
                                        arg2
                                    );
                                    safe_eprintln!("    arg1 bits (unoffset): {:?}", b1);
                                    safe_eprintln!("    arg2 bits (unoffset): {:?}", b2);
                                }

                                for (bit_idx, (&bit1, &bit2)) in
                                    b1.iter().zip(b2.iter()).enumerate()
                                {
                                    let ob1 = offset_bit(bit1);
                                    let ob2 = offset_bit(bit2);
                                    let diff_var = next_var as i32;
                                    next_var += 1;
                                    all_diff_vars.push(diff_var);

                                    if debug && bit_idx < 2 {
                                        safe_eprintln!(
                                            "    bit {}: diff_var={}, ob1={}, ob2={}",
                                            bit_idx,
                                            diff_var,
                                            ob1,
                                            ob2
                                        );
                                    }

                                    // diff_j ↔ (b1[j] XOR b2[j])
                                    result
                                        .clauses
                                        .push(ay_core::CnfClause::new(vec![-diff_var, ob1, ob2]));
                                    result
                                        .clauses
                                        .push(ay_core::CnfClause::new(vec![-diff_var, -ob1, -ob2]));
                                    result
                                        .clauses
                                        .push(ay_core::CnfClause::new(vec![-ob1, ob2, diff_var]));
                                    result
                                        .clauses
                                        .push(ay_core::CnfClause::new(vec![ob1, -ob2, diff_var]));
                                }
                            }
                            _ => {
                                if debug {
                                    safe_eprintln!(
                                        "  Arg {} pair: {:?} vs {:?} - MISSING BITS",
                                        arg_idx,
                                        arg1,
                                        arg2
                                    );
                                    safe_eprintln!("    arg1_bits: {:?}", arg1_bits);
                                    safe_eprintln!("    arg2_bits: {:?}", arg2_bits);
                                }
                                all_args_have_bits = false;
                                break;
                            }
                        }
                    }

                    if !all_args_have_bits || all_diff_vars.is_empty() {
                        if debug {
                            safe_eprintln!(
                                "  SKIPPING - all_args_have_bits={}, diff_vars={}",
                                all_args_have_bits,
                                all_diff_vars.len()
                            );
                        }
                        continue;
                    }

                    if debug {
                        safe_eprintln!("  Generated {} diff vars", all_diff_vars.len());
                    }

                    // For each result bit, add the congruence constraint:
                    // diff_0 ∨ diff_1 ∨ ... ∨ ¬f(a)[i] ∨ f(b)[i]
                    // diff_0 ∨ diff_1 ∨ ... ∨ f(a)[i] ∨ ¬f(b)[i]
                    // These two clauses encode: (args differ) ∨ (f(a)[i] = f(b)[i])
                    //
                    // Optimization: Pre-allocate clause buffer to avoid O(n²) cloning.
                    // The shared prefix (diff vars) is copied once; suffix is modified in-place.
                    let suffix_start = all_diff_vars.len();
                    let mut clause_buf = Vec::with_capacity(suffix_start + 2);
                    clause_buf.extend_from_slice(&all_diff_vars);
                    clause_buf.push(0); // Placeholder for bit1 literal
                    clause_buf.push(0); // Placeholder for bit2 literal

                    for (&bit1, &bit2) in bits1.iter().zip(bits2.iter()) {
                        let ob1 = offset_bit(bit1);
                        let ob2 = offset_bit(bit2);

                        // Clause 1: diff_0 ∨ ... ∨ ¬f(a)[i] ∨ f(b)[i]
                        clause_buf[suffix_start] = -ob1;
                        clause_buf[suffix_start + 1] = ob2;
                        result
                            .clauses
                            .push(ay_core::CnfClause::new(clause_buf.clone()));

                        // Clause 2: diff_0 ∨ ... ∨ f(a)[i] ∨ ¬f(b)[i]
                        clause_buf[suffix_start] = ob1;
                        clause_buf[suffix_start + 1] = -ob2;
                        result
                            .clauses
                            .push(ay_core::CnfClause::new(clause_buf.clone()));
                    }
                }
            }
        }

        result.num_vars = next_var.saturating_sub(var_offset + 1);
        result
    }

    /// Recursively collect uninterpreted function applications from an expression
    pub(in crate::executor) fn collect_uf_applications(
        &self,
        term: TermId,
        uf_apps: &mut HashMap<(String, usize), Vec<(TermId, Vec<TermId>)>>,
        visited: &mut HashSet<TermId>,
    ) {
        if visited.contains(&term) {
            return;
        }
        visited.insert(term);

        match self.ctx.terms.get(term) {
            TermData::App(Symbol::Named(name), args) => {
                // Check if this is an uninterpreted function (not a built-in BV or array op)
                let is_builtin = matches!(
                    name.as_str(),
                    "bvadd"
                        | "bvsub"
                        | "bvmul"
                        | "bvudiv"
                        | "bvurem"
                        | "bvsdiv"
                        | "bvsrem"
                        | "bvand"
                        | "bvor"
                        | "bvxor"
                        | "bvnot"
                        | "bvneg"
                        | "bvshl"
                        | "bvlshr"
                        | "bvashr"
                        | "concat"
                        | "extract"
                        | "repeat"
                        | "zero_extend"
                        | "sign_extend"
                        | "rotate_left"
                        | "rotate_right"
                        | "bvult"
                        | "bvule"
                        | "bvugt"
                        | "bvuge"
                        | "bvslt"
                        | "bvsle"
                        | "bvsgt"
                        | "bvsge"
                        | "="
                        | "distinct"
                        | "ite"
                        | "and"
                        | "or"
                        | "not"
                        | "=>"
                        | "xor"
                        | "select"
                        | "store"
                        | "true"
                        | "false"
                );

                if !is_builtin && !args.is_empty() {
                    // This is an uninterpreted function application. Key by
                    // (name, arity): `f/2` and `f/3` are distinct symbols (#4661).
                    uf_apps
                        .entry((name.clone(), args.len()))
                        .or_default()
                        .push((term, args.clone()));
                }

                // Recurse into arguments
                for &arg in args {
                    self.collect_uf_applications(arg, uf_apps, visited);
                }
            }
            TermData::App(Symbol::Indexed(name, _), args) => {
                // Indexed symbols like (_ extract ...) are built-in
                // Just recurse into arguments
                for &arg in args {
                    self.collect_uf_applications(arg, uf_apps, visited);
                }

                // But user-defined indexed functions should be tracked
                let is_builtin = matches!(
                    name.as_str(),
                    "extract"
                        | "repeat"
                        | "zero_extend"
                        | "sign_extend"
                        | "rotate_left"
                        | "rotate_right"
                );

                if !is_builtin && !args.is_empty() {
                    // Key by (name, arity) — distinct arities are distinct symbols.
                    uf_apps
                        .entry((name.clone(), args.len()))
                        .or_default()
                        .push((term, args.clone()));
                }
            }
            TermData::Not(inner) => {
                self.collect_uf_applications(*inner, uf_apps, visited);
            }
            TermData::Ite(c, t, e) => {
                self.collect_uf_applications(*c, uf_apps, visited);
                self.collect_uf_applications(*t, uf_apps, visited);
                self.collect_uf_applications(*e, uf_apps, visited);
            }
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::Executor;
    use ay_bv::BvSolver;
    use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
    use ay_core::term::Symbol;
    use ay_core::{Sort, TermId};

    /// Regression (compiler_consumer Group-B ICE): a UF whose *name* is reused at two
    /// different arities — as the deductive verifier does when abstracting nonlinear
    /// `*`/`+` in aterm_scene's raster/atlas math — must NOT be conflated. In
    /// EUF/Ackermannization `*/2` and `*/3` are DISTINCT function symbols and
    /// congruence only relates equal-arity applications.
    ///
    /// Before keying `uf_apps` by (name, arity) the collector bucketed both
    /// arities under `"*"`, so the dev-only `debug_assert!` in
    /// `generate_euf_bv_axioms_debug` ("UF '*' has applications with inconsistent
    /// arities") tripped and ICEd compiler_consumer. This test would panic under the old
    /// name-only keying and must pass under the (name, arity) keying.
    #[test]
    fn mixed_arity_uf_keyed_by_name_and_arity_no_panic() {
        let mut exec = Executor::new();
        let bv8 = Sort::bitvec(8);

        // BV-sorted argument variables.
        let a = exec.ctx.terms.mk_var("a", bv8.clone());
        let b = exec.ctx.terms.mk_var("b", bv8.clone());
        let c = exec.ctx.terms.mk_var("c", bv8.clone());

        // Same symbol name "*" applied at arity 2 (twice) AND arity 3 (twice).
        // Two applications per arity so each (name, arity) bucket has >= 2 apps
        // and the congruence loop's arity `debug_assert!` is actually reached.
        let star2_ab =
            exec.ctx
                .terms
                .mk_app(Symbol::Named("*".to_string()), vec![a, b], bv8.clone());
        let star2_ca =
            exec.ctx
                .terms
                .mk_app(Symbol::Named("*".to_string()), vec![c, a], bv8.clone());
        let star3_abc =
            exec.ctx
                .terms
                .mk_app(Symbol::Named("*".to_string()), vec![a, b, c], bv8.clone());
        let star3_cba =
            exec.ctx
                .terms
                .mk_app(Symbol::Named("*".to_string()), vec![c, b, a], bv8.clone());

        exec.ctx.assertions.push(star2_ab);
        exec.ctx.assertions.push(star2_ca);
        exec.ctx.assertions.push(star3_abc);
        exec.ctx.assertions.push(star3_cba);

        // 1) collect_uf_applications must produce two DISTINCT buckets keyed by
        //    (name, arity) — not one conflated "*" bucket of mixed arity.
        let mut uf_apps: HashMap<(String, usize), Vec<(TermId, Vec<TermId>)>> = HashMap::default();
        let mut visited: HashSet<TermId> = HashSet::default();
        for &assertion in &exec.ctx.assertions {
            exec.collect_uf_applications(assertion, &mut uf_apps, &mut visited);
        }
        assert!(
            uf_apps.contains_key(&("*".to_string(), 2)),
            "expected a (\"*\", 2) bucket"
        );
        assert!(
            uf_apps.contains_key(&("*".to_string(), 3)),
            "expected a (\"*\", 3) bucket"
        );
        assert_eq!(
            uf_apps.len(),
            2,
            "arity-2 and arity-3 applications must not be conflated"
        );
        assert_eq!(uf_apps[&("*".to_string(), 2)].len(), 2);
        assert_eq!(uf_apps[&("*".to_string(), 3)].len(), 2);
        // Per-arity congruence: every application in a bucket shares the key
        // arity, so an arity-2 app is only ever grouped with other arity-2 apps.
        for ((_name, arity), apps) in &uf_apps {
            assert!(
                apps.iter().all(|(_t, args)| args.len() == *arity),
                "bucket for arity {arity} holds an application of a different arity"
            );
        }

        // 2) The full BV-EUF axiom generator must NOT panic on the mixed-arity
        //    input. Under the old name-only keying the arity `debug_assert!`
        //    fired here (the ICE). It now runs to completion.
        let bv_solver = BvSolver::new(&exec.ctx.terms);
        let _ = exec.generate_euf_bv_axioms_debug(&bv_solver, 0, 0, false, &[]);
    }
}
