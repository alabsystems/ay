// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Non-BV EUF congruence axiom generation for combined BV theories.
//!
//! Handles congruence for UF applications whose return type is non-BV
//! (uninterpreted sorts, datatypes, Int, Bool, etc.) by connecting argument
//! equality to Tseitin variables rather than BV bit-level XOR encoding.
//!
//! Split from `bv_axioms_euf.rs` for code health (#5970).

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{Sort, Symbol, TermData, TermId};
use std::sync::atomic::Ordering;

use super::super::Executor;

/// Result of attempting to build argument-difference SAT variables (#5457).
enum ArgDiffResult {
    /// All argument pairs are identical TermIds — outputs must be equivalent.
    AllIdentical,
    /// All different pairs have BV bits — conditional congruence with diff vars.
    Encoded(Vec<i32>),
    /// Some argument pairs differ but lack BV bits (e.g., DT-sorted) — cannot
    /// encode difference, so congruence must be skipped to avoid unsoundness.
    Unencodable,
}

/// Outcome of [`Executor::generate_non_bv_euf_congruence`].
pub(in crate::executor) struct NonBvCongruenceOutcome {
    /// Fresh SAT variables allocated.
    pub(in crate::executor) num_vars: u32,
    /// True when the all-pairs loop stopped early on interrupt / deadline /
    /// memory pressure. PARTIAL congruence axioms are SOUND FOR UNSAT ONLY
    /// (they are a subset of the full axiomatization): the caller MUST
    /// degrade any subsequent CDCL SAT to Unknown while this flag is set —
    /// a model found under the bailed axiomatization may violate an
    /// unemitted congruence constraint (wrong-SAT class, 2026-06-20 hunt).
    pub(in crate::executor) bailed: bool,
}

/// Poll cadence for the pair-loop interrupt check: every 1024 pairs.
const CONGRUENCE_POLL_MASK: u64 = 1023;

/// Same-symbol groups at or below this application count always construct
/// the probe terms exactly as the pre-hoist code did (the O(n²) cost is
/// trivial, and small groups include the constructor-application clusters
/// whose `mk_eq` may rewrite structurally rather than intern a plain `=`).
const SMALL_GROUP_MAX: usize = 8;

impl Executor {
    /// Generate congruence axioms for UF applications with non-BV return types (#5433).
    ///
    /// The standard `generate_euf_bv_axioms_debug` handles only BV-return UFs (it
    /// needs BV bits for the result). For UFs returning uninterpreted sorts, datatypes,
    /// Int, etc., we connect argument equality to the Tseitin variable for the result
    /// equality term `(= f(a) f(b))`.
    ///
    /// Takes `term_bits` (a snapshot of `bv_solver.term_to_bits()`) to avoid borrow
    /// conflicts with `&mut self.ctx.terms` needed for `mk_eq`.
    ///
    /// Returns the allocated fresh-variable count plus a bail flag; see
    /// [`NonBvCongruenceOutcome`] for the caller's soundness obligation.
    pub(in crate::executor) fn generate_non_bv_euf_congruence(
        &mut self,
        term_bits: &HashMap<TermId, Vec<i32>>,
        bool_to_var: &HashMap<TermId, i32>,
        tseitin_result: &ay_core::TseitinResult,
        var_offset: u32,
        all_clauses: &mut Vec<ay_core::CnfClause>,
        extra_terms: &[TermId],
    ) -> NonBvCongruenceOutcome {
        #[cfg(test)]
        if self.test_force_non_bv_congruence_bail {
            return NonBvCongruenceOutcome {
                num_vars: 0,
                bailed: true,
            };
        }

        // Keyed by (name, arity) — distinct arities are distinct UF symbols and
        // congruence only relates equal-arity applications (#4661).
        let mut uf_apps: HashMap<(String, usize), Vec<(TermId, Vec<TermId>)>> = HashMap::default();
        let mut visited = HashSet::default();
        for &assertion in &self.ctx.assertions {
            self.collect_uf_applications(assertion, &mut uf_apps, &mut visited);
        }
        for &term in extra_terms {
            self.collect_uf_applications(term, &mut uf_apps, &mut visited);
        }

        // Hoisted consumer detection (item 4 Stage 2): ONE pre-scan of the
        // Tseitin-mapped terms collects every equality/distinct atom over a
        // term pair, so the all-pairs loop below can reject consumer-less
        // pairs WITHOUT interning three probe terms per pair. On large BMC
        // instances the probe interning itself (O(n²) `mk_eq`/`mk_not`/
        // `mk_distinct` store insertions) was the memory/time wall.
        //
        // Completeness of the pre-filter (must never skip a pair the
        // authoritative check below would keep — losing congruence clauses
        // for a consumed atom would be a wrong-SAT): for same-sort UF
        // applications of NON-Real, NON-Datatype sort, `mk_eq(t1, t2)`
        // interns the canonical `(= min max)` atom (no rewrite rule fires:
        // the operands are Named applications, not consts/ites/stores/nots),
        // `mk_not` of it interns `Not(eq)`, and 2-ary `mk_distinct`
        // normalizes to that same `Not(eq)`. All three shapes are covered by
        // the scan patterns below, and the Bool-Tseitin-var consumer arm is
        // checked directly against `term_to_var`. Real-sorted pairs
        // (`to_real` stripping) and Datatype-sorted pairs (constructor
        // structural rewrites) can rewrite into other shapes, so those — and
        // every small group — construct unconditionally, preserving exact
        // pre-hoist behavior.
        let mut consumed_pairs: HashSet<(TermId, TermId)> = HashSet::default();
        let ordered = |a: TermId, b: TermId| if a < b { (a, b) } else { (b, a) };
        for &term in tseitin_result.term_to_var.keys() {
            match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args)
                    if args.len() == 2 && (name == "=" || name == "distinct") =>
                {
                    consumed_pairs.insert(ordered(args[0], args[1]));
                }
                TermData::Not(inner) => {
                    if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(*inner) {
                        if args.len() == 2 && (name == "=" || name == "distinct") {
                            consumed_pairs.insert(ordered(args[0], args[1]));
                        }
                    }
                }
                _ => {}
            }
        }

        let bv_offset = tseitin_result.num_vars;
        let mut next_var = var_offset + 1;
        let mut bailed = false;
        let mut pair_index: u64 = 0;

        'groups: for (_key, applications) in &uf_apps {
            if applications.len() < 2 {
                continue;
            }
            let small_group = applications.len() <= SMALL_GROUP_MAX;

            for i in 0..applications.len() {
                for j in (i + 1)..applications.len() {
                    // Interrupt / deadline / memory poll (item 4 Stage 2):
                    // the all-pairs loop over same-symbol applications is the
                    // executor wall on large table-read instances — poll
                    // every ~1024 pairs and stop emitting on expiry. The
                    // partial axiomatization emitted so far stays in
                    // `all_clauses` (sound for UNSAT); the caller degrades
                    // SAT to Unknown via the returned flag.
                    pair_index += 1;
                    if pair_index & CONGRUENCE_POLL_MASK == 0
                        && self.non_bv_congruence_interrupted()
                    {
                        bailed = true;
                        break 'groups;
                    }

                    let (term1, args1) = &applications[i];
                    let (term2, args2) = &applications[j];

                    if args1.len() != args2.len() {
                        continue;
                    }

                    // Skip pairs that generate_euf_bv_axioms_debug fully handles:
                    // both results AND all differing args have BV bits (#5439).
                    let has_bits1 = term_bits.contains_key(term1);
                    let has_bits2 = term_bits.contains_key(term2);
                    if has_bits1 && has_bits2 {
                        let all_args_bv = args1.iter().zip(args2.iter()).all(|(a1, a2)| {
                            a1 == a2 || (term_bits.contains_key(a1) && term_bits.contains_key(a2))
                        });
                        if all_args_bv {
                            continue;
                        }
                    }

                    // BV-return congruence with NON-BV arguments (#2774 K2,
                    // left-inverse ground non-injectivity): a pair like
                    // `Unbox(Box a)` / `Unbox(Box b)` — BV-sorted results,
                    // uninterpreted-sort args — is skipped by BOTH generators:
                    // `generate_euf_bv_axioms_debug` needs BV bits on every
                    // differing argument, and the Tseitin-consumer sections
                    // below need a ground `(= f(a) f(b))` / `distinct` atom or
                    // Bool-return Tseitin vars, none of which exist when the
                    // results are consumed only through their BV bits. The
                    // congruence `Box a = Box b ⇒ Unbox(Box a) = Unbox(Box b)`
                    // was silently dropped, letting the SAT core produce an
                    // invalid model (caught by the model gate → fail-closed
                    // `unknown` instead of the sound `unsat`). When both
                    // results carry equal-width BV bits AND every differing
                    // argument pair is encodable WITHOUT interning fresh probe
                    // atoms (BV bits on both sides, an existing consumed
                    // `=`/`distinct` atom over the pair, or Bool literals),
                    // this pair emits bit-level result congruence in section
                    // 1c below and must bypass the consumer gates. The
                    // no-probe-interning precondition keeps the hoisted O(n²)
                    // memory guard intact: candidacy is decided from existing
                    // maps only.
                    let bit_congruence_candidate = has_bits1
                        && has_bits2
                        && term_bits[term1].len() == term_bits[term2].len()
                        && !term_bits[term1].is_empty()
                        && args1.iter().zip(args2.iter()).all(|(a1, a2)| {
                            a1 == a2
                                || (self.ctx.terms.sort(*a1) == self.ctx.terms.sort(*a2)
                                    && ((term_bits.contains_key(a1) && term_bits.contains_key(a2))
                                        || consumed_pairs.contains(&ordered(*a1, *a2))
                                        || (matches!(self.ctx.terms.sort(*a1), Sort::Bool)
                                            && bool_to_var.contains_key(a1)
                                            && bool_to_var.contains_key(a2))))
                        });

                    // Consumer check FIRST: the congruence clauses below can only
                    // constrain (a) the `(= f(a) f(b))` equality atom, (b) the
                    // `(distinct f(a) f(b))` atom, or (c) the Bool-return Tseitin
                    // vars of the two applications. If NONE of those has a Tseitin
                    // variable, every clause this pair could emit is either skipped
                    // below or references only the fresh arg-diff DEFINITION vars
                    // (which nothing else consumes) — pure dead weight. Skipping
                    // the pair is semantics-preserving: fresh-var definitions with
                    // no consumer never constrain the original variables.
                    //
                    // This matters because the loop is all-pairs O(n²) over
                    // same-symbol applications: on a large BMC instance (aterm
                    // parser dispatch) consumer-less pairs contributed ~94M of a
                    // 200M-clause CNF (~47%) — the difference between a solvable
                    // instance and a memout.
                    //
                    // Result-sort guard (#dt-shared-selector-result-sort): a
                    // selector NAME can be SHARED across datatypes — e.g.
                    // `fld_data` declared on both `Slice_PbConstraint` and
                    // `Slice_PbTerm` under the explicit-constructor
                    // datatype-in-array encoding — so this same-symbol pair can
                    // have DIFFERENT result sorts. `mk_eq` requires same-sort
                    // operands (its documented precondition; ill-typed otherwise),
                    // and two different-sorted terms can never be equal, so no
                    // congruence clause is needed. Skip the pair, exactly as the
                    // arg-sort-mismatch case below already does (#2682).
                    if self.ctx.terms.sort(*term1) != self.ctx.terms.sort(*term2) {
                        continue;
                    }
                    // Hoisted pre-filter (item 4 Stage 2): reject
                    // consumer-less pairs BEFORE interning the three probe
                    // terms. Small groups and Real-/Datatype-sorted pairs
                    // construct unconditionally (their `mk_eq` may rewrite
                    // structurally — see the pre-scan completeness note);
                    // the authoritative has_consumer check below is
                    // unchanged for every constructed pair.
                    if !small_group
                        && !matches!(self.ctx.terms.sort(*term1), Sort::Real | Sort::Datatype(_))
                    {
                        let direct_consumer = tseitin_result.var_for_term(*term1).is_some()
                            && tseitin_result.var_for_term(*term2).is_some();
                        if !direct_consumer
                            && !consumed_pairs.contains(&ordered(*term1, *term2))
                            && !bit_congruence_candidate
                        {
                            continue;
                        }
                    }
                    let eq_term = self.ctx.terms.mk_eq(*term1, *term2);
                    let not_eq_term = self.ctx.terms.mk_not(eq_term);
                    let dist_term_probe = self.ctx.terms.mk_distinct(vec![*term1, *term2]);
                    let has_consumer = tseitin_result.var_for_term(eq_term).is_some()
                        || tseitin_result.var_for_term(not_eq_term).is_some()
                        || tseitin_result.var_for_term(dist_term_probe).is_some()
                        || (tseitin_result.var_for_term(*term1).is_some()
                            && tseitin_result.var_for_term(*term2).is_some());
                    if !has_consumer && !bit_congruence_candidate {
                        continue;
                    }

                    // Pre-compute Tseitin literals for argument-pair equalities
                    // so build_arg_diff_vars can handle non-BV args (#5439).
                    let arg_eq_lits: Vec<Option<i32>> = args1
                        .iter()
                        .zip(args2.iter())
                        .map(|(&a1, &a2)| {
                            if a1 == a2 {
                                return None;
                            }
                            // Sort mismatch means args can never be equal (#2682).
                            if self.ctx.terms.sort(a1) != self.ctx.terms.sort(a2) {
                                return None;
                            }
                            let eq = self.ctx.terms.mk_eq(a1, a2);
                            if let Some(v) = tseitin_result.var_for_term(eq) {
                                Some(v as i32)
                            } else {
                                let not_eq = self.ctx.terms.mk_not(eq);
                                tseitin_result.var_for_term(not_eq).map(|v| -(v as i32))
                            }
                        })
                        .collect();

                    // Build argument-difference variables (once per pair)
                    let diff_result = Self::build_arg_diff_vars(
                        &mut self.ctx.terms,
                        args1,
                        args2,
                        term_bits,
                        bool_to_var,
                        tseitin_result,
                        bv_offset,
                        &arg_eq_lits,
                        &mut next_var,
                        all_clauses,
                    );

                    // If arguments differ but we can't encode the difference (e.g.,
                    // DT-sorted args with no BV bits), skip this congruence pair entirely.
                    // Generating unconditional congruence here is UNSOUND (#5457):
                    // e.g., is-SomeOpt(x) ↔ is-SomeOpt(NoneOpt) forced unconditionally
                    // creates false UNSAT when x ≠ NoneOpt.
                    if matches!(diff_result, ArgDiffResult::Unencodable) {
                        continue;
                    }

                    let diff_vars = match &diff_result {
                        ArgDiffResult::Encoded(v) => Some(v),
                        _ => None,
                    };

                    // 1c. Bit-level result congruence for BV-return pairs whose
                    // argument equality is only expressible at the Tseitin level
                    // (#2774 K2, see `bit_congruence_candidate` above): encode
                    // `(args equal) ⇒ (result bits pairwise equal)` directly
                    // against the results' BV bits. This is plain EUF congruence
                    // — a valid consequence in every interpretation — so adding
                    // the clauses is sound for both SAT and UNSAT directions.
                    // The `diff_vars` premise reuses the same argument-difference
                    // definitions sections 1/1b/2 rely on (Tseitin `(= a1 a2)`
                    // literals for the non-BV argument positions).
                    if bit_congruence_candidate {
                        let offset_bit = |bit: i32| -> i32 {
                            if bit > 0 {
                                bit + bv_offset as i32
                            } else {
                                bit - bv_offset as i32
                            }
                        };
                        let bits1 = &term_bits[term1];
                        let bits2 = &term_bits[term2];
                        for (&bit1, &bit2) in bits1.iter().zip(bits2.iter()) {
                            let ob1 = offset_bit(bit1);
                            let ob2 = offset_bit(bit2);
                            if let Some(dv) = diff_vars {
                                // (args differ) ∨ (f(a)[i] = f(b)[i])
                                let mut c1 = dv.clone();
                                c1.push(-ob1);
                                c1.push(ob2);
                                all_clauses.push(ay_core::CnfClause::new(c1));
                                let mut c2 = dv.clone();
                                c2.push(ob1);
                                c2.push(-ob2);
                                all_clauses.push(ay_core::CnfClause::new(c2));
                            } else {
                                // All args identical — result bits must agree.
                                all_clauses.push(ay_core::CnfClause::new(vec![-ob1, ob2]));
                                all_clauses.push(ay_core::CnfClause::new(vec![ob1, -ob2]));
                            }
                        }
                    }

                    // 1. Equality atom congruence: find (= term1 term2) Tseitin var
                    let eq_term = self.ctx.terms.mk_eq(*term1, *term2);
                    if let Some(eq_tvar) = tseitin_result.var_for_term(eq_term) {
                        let eq_lit = eq_tvar as i32;
                        if let Some(diff_vars) = diff_vars {
                            // Congruence: (args_differ) ∨ (f(a) = f(b))
                            let mut clause = diff_vars.clone();
                            clause.push(eq_lit);
                            all_clauses.push(ay_core::CnfClause::new(clause));
                        } else {
                            // All args identical — equality must hold
                            all_clauses.push(ay_core::CnfClause::unit(eq_lit));
                        }
                    }
                    // No Tseitin variable for (= f(a) f(b)): skip equality atom
                    // congruence. Previously allocated an unconstrained fresh var
                    // which the SAT solver could freely set true, making the clause
                    // vacuous (#5439 Gap 2). Sections 1b (distinct) and 2 (Bool-return
                    // Tseitin) still enforce congruence where possible.

                    // 1b. Distinct atom congruence: find (distinct term1 term2)
                    // The old inline code handled both = and distinct; mk_eq only
                    // finds =. Without this, (distinct f(a) f(b)) loses congruence
                    // when f returns a non-BV sort.
                    let dist_term = self.ctx.terms.mk_distinct(vec![*term1, *term2]);
                    if let Some(dist_tvar) = tseitin_result.var_for_term(dist_term) {
                        let dist_lit = dist_tvar as i32;
                        if let Some(diff_vars) = diff_vars {
                            // Congruence: (args_differ) ∨ ¬(distinct f(a) f(b))
                            let mut clause = diff_vars.clone();
                            clause.push(-dist_lit);
                            all_clauses.push(ay_core::CnfClause::new(clause));
                        } else {
                            // All args identical — distinct must be false
                            all_clauses.push(ay_core::CnfClause::unit(-dist_lit));
                        }
                    }

                    // 2. Direct Tseitin variable congruence for Bool-return UFs (#5437)
                    // When f returns Bool, f(a) and f(b) have Tseitin variables directly
                    // but no explicit (= f(a) f(b)) atom. Encode: args same → tv1 ↔ tv2
                    let tvar1 = tseitin_result.var_for_term(*term1);
                    let tvar2 = tseitin_result.var_for_term(*term2);
                    if let (Some(tv1), Some(tv2)) = (tvar1, tvar2) {
                        if let Some(diff_vars) = diff_vars {
                            // diff_vars ∨ ¬tv1 ∨ tv2 (args same → tv1 implies tv2)
                            let mut c1 = diff_vars.clone();
                            c1.push(-(tv1 as i32));
                            c1.push(tv2 as i32);
                            all_clauses.push(ay_core::CnfClause::new(c1));
                            // diff_vars ∨ tv1 ∨ ¬tv2 (args same → tv2 implies tv1)
                            let mut c2 = diff_vars.clone();
                            c2.push(tv1 as i32);
                            c2.push(-(tv2 as i32));
                            all_clauses.push(ay_core::CnfClause::new(c2));
                        } else {
                            // All args identical — Tseitin vars must be equivalent
                            all_clauses
                                .push(ay_core::CnfClause::new(vec![-(tv1 as i32), tv2 as i32]));
                            all_clauses
                                .push(ay_core::CnfClause::new(vec![tv1 as i32, -(tv2 as i32)]));
                        }
                    }

                    // Distinct atom congruence (#5451): if (distinct f(a) f(b)) has a
                    // Tseitin variable, add congruence axioms for it too. Tseitin gives
                    // `distinct` its own standalone variable with NO built-in relationship
                    // to the `=` variable, so we must explicitly constrain it.
                    let dist_term = self.ctx.terms.mk_distinct(vec![*term1, *term2]);
                    if let Some(dist_tvar) = tseitin_result.var_for_term(dist_term) {
                        let dist_lit = dist_tvar as i32;
                        if let Some(dv) = diff_vars {
                            // Congruence: (args_differ) OR NOT(distinct f(a) f(b))
                            let mut clause = dv.clone();
                            clause.push(-dist_lit);
                            all_clauses.push(ay_core::CnfClause::new(clause));
                        } else {
                            // All args identical — distinct must be false
                            all_clauses.push(ay_core::CnfClause::unit(-dist_lit));
                        }
                    }
                }
            }
        }

        NonBvCongruenceOutcome {
            num_vars: next_var.saturating_sub(var_offset + 1),
            bailed,
        }
    }

    /// Pair-loop poll for [`Self::generate_non_bv_euf_congruence`]:
    /// API interrupt flag, live solve deadline, or process memory ceiling.
    fn non_bv_congruence_interrupted(&self) -> bool {
        if let Some(flag) = self.solve_interrupt.as_ref() {
            if flag.load(Ordering::Relaxed) {
                return true;
            }
        }
        self.solve_deadline.expired() || ay_sys::process_memory_exceeded()
    }

    /// Build argument-difference SAT variables for a pair of UF applications.
    ///
    /// For each argument pair `(a_i, b_i)` that has BV bits, allocates a fresh
    /// `diff_i` variable encoding `a_i ≠ b_i` (XOR of corresponding bits).
    /// For non-BV argument pairs, looks up the Tseitin variable for `(= a_i b_i)`
    /// and encodes `diff_i ↔ ¬eq_var` (#5439). Bool-sorted pairs with no such
    /// Tseitin atom fall back to the BV solver's `bool_to_var` literals
    /// (materialized for UF Bool args before linking, #boolarg-congruence) and
    /// encode `diff_i ↔ (l_a XOR l_b)` like a 1-bit BV argument.
    ///
    /// Returns:
    /// - `ArgDiffResult::AllIdentical` — all argument pairs are the same TermId
    /// - `ArgDiffResult::Encoded(diff_vars)` — all different pairs encodable
    /// - `ArgDiffResult::Unencodable` — some pairs differ but lack encoding (#5457)
    #[allow(clippy::too_many_arguments)]
    fn build_arg_diff_vars(
        terms: &mut ay_core::TermStore,
        args1: &[TermId],
        args2: &[TermId],
        term_bits: &HashMap<TermId, Vec<i32>>,
        bool_to_var: &HashMap<TermId, i32>,
        tseitin_result: &ay_core::TseitinResult,
        bv_offset: u32,
        _arg_eq_lits: &[Option<i32>],
        next_var: &mut u32,
        clauses: &mut Vec<ay_core::CnfClause>,
    ) -> ArgDiffResult {
        let offset_bit = |bit: i32| -> i32 {
            if bit > 0 {
                bit + bv_offset as i32
            } else {
                bit - bv_offset as i32
            }
        };

        let mut all_diff_vars = Vec::new();
        let mut has_unencodable_diff = false;

        for (arg1, arg2) in args1.iter().zip(args2.iter()) {
            if arg1 == arg2 {
                // Identical arguments — no difference possible
                continue;
            }
            let arg1_bits = term_bits.get(arg1).map(Vec::as_slice);
            let arg2_bits = term_bits.get(arg2).map(Vec::as_slice);

            match (arg1_bits, arg2_bits) {
                (Some(b1), Some(b2)) if b1.len() == b2.len() && !b1.is_empty() => {
                    for (&bit1, &bit2) in b1.iter().zip(b2.iter()) {
                        let ob1 = offset_bit(bit1);
                        let ob2 = offset_bit(bit2);
                        let diff_var = *next_var as i32;
                        *next_var += 1;
                        all_diff_vars.push(diff_var);

                        // diff_var ↔ (bit1 XOR bit2)
                        clauses.push(ay_core::CnfClause::new(vec![-diff_var, ob1, ob2]));
                        clauses.push(ay_core::CnfClause::new(vec![-diff_var, -ob1, -ob2]));
                        clauses.push(ay_core::CnfClause::new(vec![-ob1, ob2, diff_var]));
                        clauses.push(ay_core::CnfClause::new(vec![ob1, -ob2, diff_var]));
                    }
                }
                _ => {
                    // Non-BV argument pair: try Tseitin-variable encoding (#5439).
                    // Look up (= arg1 arg2) in Tseitin result; if present, encode
                    // diff_i ↔ ¬eq_var (arguments differ ↔ equality is false).
                    // Sort mismatch means args can never be equal (#2682).
                    if terms.sort(*arg1) != terms.sort(*arg2) {
                        has_unencodable_diff = true;
                        continue;
                    }
                    let eq_term = terms.mk_eq(*arg1, *arg2);
                    if let Some(eq_tvar) = tseitin_result.var_for_term(eq_term) {
                        let eq_lit = eq_tvar as i32;
                        let diff_var = *next_var as i32;
                        *next_var += 1;
                        all_diff_vars.push(diff_var);
                        // diff_var ↔ ¬eq_lit
                        clauses.push(ay_core::CnfClause::new(vec![-diff_var, -eq_lit]));
                        clauses.push(ay_core::CnfClause::new(vec![eq_lit, diff_var]));
                    } else if let (Sort::Bool, Some(&l1), Some(&l2)) = (
                        terms.sort(*arg1),
                        bool_to_var.get(arg1),
                        bool_to_var.get(arg2),
                    ) {
                        // Bool-sorted argument pair with single-literal BV-side
                        // encodings (#boolarg-congruence): the argument
                        // difference is a 1-bit XOR, exactly like a 1-bit BV
                        // argument. Without this, the pair was Unencodable and
                        // congruence over Bool argument positions was lost.
                        let ol1 = offset_bit(l1);
                        let ol2 = offset_bit(l2);
                        let diff_var = *next_var as i32;
                        *next_var += 1;
                        all_diff_vars.push(diff_var);
                        // diff_var ↔ (l1 XOR l2)
                        clauses.push(ay_core::CnfClause::new(vec![-diff_var, ol1, ol2]));
                        clauses.push(ay_core::CnfClause::new(vec![-diff_var, -ol1, -ol2]));
                        clauses.push(ay_core::CnfClause::new(vec![-ol1, ol2, diff_var]));
                        clauses.push(ay_core::CnfClause::new(vec![ol1, -ol2, diff_var]));
                    } else {
                        // No BV bits and no Tseitin variable — unencodable (#5457).
                        has_unencodable_diff = true;
                    }
                    continue;
                }
            }
        }

        if has_unencodable_diff {
            ArgDiffResult::Unencodable
        } else if all_diff_vars.is_empty() {
            ArgDiffResult::AllIdentical
        } else {
            ArgDiffResult::Encoded(all_diff_vars)
        }
    }
}
