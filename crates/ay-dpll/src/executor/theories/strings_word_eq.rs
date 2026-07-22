// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Nielsen word-equation pre-pass (Track A3, Milestones 1–2).
//!
//! Decides conjunctions of symbolic word equations — `(= (str.++ x "ab")
//! (str.++ "a" y))` and friends — that the CEGAR string pipeline stalls on
//! (its `EmptySplit` dedup latches `incomplete` and yields `unknown`).
//!
//! The pass extracts the *word-equation fragment* of the toplevel assertion
//! set — equalities/disequalities whose sides are built purely from string
//! variables, string literals, and `str.++`, plus exact `(= (str.len x) N)`
//! facts and (Stage 2) single-variable `str.in_re` memberships translated
//! exactly into [`ay_strings::we_regex::WeRegex`] — and runs the bounded
//! Nielsen-transform search from [`ay_strings::word_eq`]. Soundness
//! contract:
//!
//! * **SAT** is only reported after each candidate assignment is pinned as
//!   hard assumptions and the FULL model is validated by the existing
//!   assumption machinery (identical to the other witness pre-passes: a wrong
//!   candidate falls through, never escapes).
//! * **UNSAT** is only reported when the Nielsen graph is *exhaustively*
//!   closed by conflicts. That proves the extracted equations (plus the exact
//!   lengths used for pruning) — a subset of the asserted conjuncts — are
//!   jointly unsatisfiable, which soundly implies UNSAT for the whole
//!   formula. Disequations never contribute to UNSAT (they are only used to
//!   filter SAT candidates), except the trivial syntactic `w != w`.
//! * **Budget exhaustion** falls through to the normal pipeline (`Ok(None)`).

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, Symbol, TermData, TermId};
use ay_core::Sort;
use ay_strings::we_regex::WeRegex;
use ay_strings::word_eq::{
    solve_word_equations, WeConfig, WeEquation, WeLenBound, WeMembership, WeOutcome, WeProblem,
    WeSym, WeWord,
};

use crate::executor_types::{Result, SolveResult};

use super::super::Executor;
use super::debug_auflia_enabled;

/// Maximum number of distinct string variables in the fragment.
const MAX_WE_VARS: usize = 20;
/// Maximum total symbols (variables + literal characters) across all
/// extracted equations. Kept well under `WeConfig::max_word_len` (512) so
/// the initial Nielsen state is never dead on arrival. Strings S1
/// (`AY_WE_S1`) lifts both in lockstep: industrial sanitizer benchmarks
/// (slog/Stranger) inline multi-hundred-character HTML literals, and the
/// definitional Gaussian elimination collapses them without branching, so a
/// larger budget converts those files at bounded extra cost.
const MAX_WE_SYMS: usize = 320;
const MAX_WE_SYMS_S1: usize = 4096;
const MAX_WORD_LEN_S1: usize = 4096;

fn max_we_syms() -> usize {
    if ay_strings::we_regex::s1_enabled() {
        MAX_WE_SYMS_S1
    } else {
        MAX_WE_SYMS
    }
}

fn we_config() -> WeConfig {
    let mut cfg = WeConfig::default();
    if ay_strings::we_regex::s1_enabled() {
        cfg.max_word_len = MAX_WORD_LEN_S1;
    }
    cfg
}
/// Maximum number of equations / disequations extracted.
const MAX_WE_EQS: usize = 16;
/// Maximum node size of a translated `str.in_re` regex (larger constraints
/// are skipped — sound: Unsat uses a subset of assertions, Sat candidates
/// are validated against the full set).
const MAX_WE_REGEX_SIZE: usize = 256;
/// Raised cap under the strings witness-construction flag (`AY_STR_WITNESS=1`,
/// default OFF). Industrial regex chains (automatark / stringfuzz) inline
/// hundred-character literals and wide `re.union` classes whose EXACT
/// translation exceeds 256 nodes, so the default cap drops the membership
/// entirely and no witness can be constructed from it. Raising the cap changes
/// only how much work the exact translation may do: the translation itself is
/// exact-or-bail either way, Sat candidates are still model-validated, and
/// Unsat still rests on an exactly-translated subset of the assertions.
const MAX_WE_REGEX_SIZE_WITNESS: usize = 1024;

fn max_we_regex_size() -> usize {
    if crate::executor::model::string_witness::str_witness_enabled() {
        MAX_WE_REGEX_SIZE_WITNESS
    } else {
        MAX_WE_REGEX_SIZE
    }
}
/// Maximum `(_ re.loop lo hi)` upper bound unrolled during translation.
/// Env-tunable via `AY_WE_MAX_LOOP` (strings S1 feasibility knob): default
/// unchanged; a larger unroll only grows the translated regex. The configured
/// value is capped before allocation by `MAX_WE_REGEX_SIZE`, and the translated
/// result is checked against that same size bound. Sat witnesses stay
/// model-validated fail-closed.
const MAX_WE_LOOP: u32 = 12;

fn parse_max_we_loop(value: Option<&str>) -> u32 {
    value
        .and_then(|s| s.parse().ok())
        .unwrap_or(MAX_WE_LOOP)
        .min(MAX_WE_REGEX_SIZE as u32)
}

fn max_we_loop() -> u32 {
    static V: std::sync::OnceLock<u32> = std::sync::OnceLock::new();
    *V.get_or_init(|| parse_max_we_loop(std::env::var("AY_WE_MAX_LOOP").ok().as_deref()))
}

/// The extracted word-equation fragment plus the TermId for each variable
/// index (`var_terms[i]` is the term for `WeSym::Var(i as u32)`).
///
/// `var_terms[i]` is `None` for extraction-internal skolem variables
/// (introduced by the M2 predicate reductions below); those are solved for
/// but never pinned as assumptions.
struct WordEqExtraction {
    problem: WeProblem,
    var_terms: Vec<Option<TermId>>,
}

impl Executor {
    /// Nielsen word-equation pre-pass. See module docs.
    ///
    /// Returns `Ok(Some(Sat))` / `Ok(Some(Unsat))` only on a sound decision,
    /// `Ok(None)` to fall through to the normal pipeline.
    pub(in crate::executor) fn try_word_equation_nielsen(&mut self) -> Result<Option<SolveResult>> {
        // Re-entry guard: the SAT path recurses through the solver with the
        // candidate pinned, which must NOT re-trigger this pre-pass.
        if self.pivot_enum_depth != 0 {
            return Ok(None);
        }

        let Some(extraction) = self.extract_word_eq_problem() else {
            return Ok(None);
        };

        if debug_auflia_enabled() {
            let render = |w: &WeWord| -> String {
                w.iter()
                    .map(|s| match s {
                        WeSym::Var(v) => format!("V{v}"),
                        WeSym::Ch(c) => format!("{c:?}"),
                    })
                    .collect::<Vec<_>>()
                    .join("·")
            };
            for (i, eq) in extraction.problem.equations.iter().enumerate() {
                safe_eprintln!(
                    "[WORDEQ] eq{}: {} = {}",
                    i,
                    render(&eq.lhs),
                    render(&eq.rhs)
                );
            }
            for (v, n) in &extraction.problem.exact_lens {
                safe_eprintln!("[WORDEQ] exact len: |V{v}| = {n}");
            }
            for b in &extraction.problem.len_bounds {
                safe_eprintln!("[WORDEQ] bound: {} <= |V{}| <= {:?}", b.lo, b.var, b.hi);
            }
            for (i, t) in extraction.var_terms.iter().enumerate() {
                safe_eprintln!("[WORDEQ] var V{i} = {t:?}");
            }
        }
        let outcome = solve_word_equations(&extraction.problem, &we_config());
        if debug_auflia_enabled() {
            safe_eprintln!(
                "[WORDEQ] fragment: {} eqs, {} diseqs, {} res, {} vars → {:?}",
                extraction.problem.equations.len(),
                extraction.problem.disequations.len(),
                extraction.problem.memberships.len(),
                extraction.problem.num_vars,
                match &outcome {
                    WeOutcome::Sat(sols) => format!("Sat({} candidates)", sols.len()),
                    WeOutcome::Unsat => "Unsat".to_string(),
                    WeOutcome::Exhausted => "Exhausted".to_string(),
                }
            );
        }

        match outcome {
            WeOutcome::Unsat => Ok(Some(SolveResult::unsat())),
            WeOutcome::Exhausted => Ok(None),
            WeOutcome::Sat(solutions) => {
                // Pin only USER variables; extraction skolems (from the M2
                // predicate reductions) are internal witnesses.
                let solutions: Vec<Vec<(TermId, String)>> = solutions
                    .into_iter()
                    .map(|sol| {
                        sol.into_iter()
                            .filter_map(|(v, s)| extraction.var_terms[v as usize].map(|t| (t, s)))
                            .collect()
                    })
                    .collect();
                self.try_word_eq_assignments(&solutions)
            }
        }
    }

    /// Extract the word-equation fragment of the toplevel assertions.
    ///
    /// Returns `None` when the fragment is empty, has no symbolic equation
    /// (nothing for the Nielsen search to add over the existing pipeline), or
    /// exceeds the size caps.
    fn extract_word_eq_problem(&self) -> Option<WordEqExtraction> {
        let mut var_ids: HashMap<TermId, u32> = HashMap::default();
        let mut var_terms: Vec<Option<TermId>> = Vec::new();
        let mut equations: Vec<WeEquation> = Vec::new();
        let mut disequations: Vec<WeEquation> = Vec::new();
        let mut memberships: Vec<WeMembership> = Vec::new();

        // Allocate an extraction-internal skolem variable (no TermId).
        let fresh_skolem = |var_terms: &mut Vec<Option<TermId>>| -> Option<u32> {
            let id = u32::try_from(var_terms.len()).ok()?;
            var_terms.push(None);
            Some(id)
        };

        // Intern a direct string VARIABLE (memberships couple only through
        // single-variable `str.in_re`; anything else stays out — sound:
        // Unsat uses a subset of assertions, Sat validates the full set).
        let intern_var = |t: TermId,
                          var_ids: &mut HashMap<TermId, u32>,
                          var_terms: &mut Vec<Option<TermId>>|
         -> Option<u32> {
            if !matches!(self.ctx.terms.get(t), TermData::Var(..))
                || *self.ctx.terms.sort(t) != Sort::String
            {
                return None;
            }
            let next = u32::try_from(var_terms.len()).ok()?;
            Some(*var_ids.entry(t).or_insert_with(|| {
                var_terms.push(Some(t));
                next
            }))
        };

        // Unit-propagated boolean closure: `forced_true` / `forced_false`
        // contain terms ENTAILED by the assertion set (toplevel assertions,
        // conjunct expansion, negation flips, and forced boolean-equality
        // sides). Extracting from the closure instead of the raw toplevel
        // keeps every extracted fact entailed — sound for the Unsat path —
        // while reaching the string equations sanitizer benchmarks hide
        // under `(= b_flag (and (= x …) b_prev))` definition chains.
        let (forced_true, forced_false) = self.forced_literal_closure();

        for &assertion in &forced_true {
            match self.ctx.terms.get(assertion) {
                TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
                    if *self.ctx.terms.sort(args[0]) != Sort::String {
                        // Strings S1: a forced-TRUE boolean equality of two
                        // membership atoms over the SAME subject is exactly
                        // one membership in the XNOR combination
                        // (R1∩R2) ∪ (¬R1∩¬R2) — see
                        // `translate_membership_pair`.
                        if ay_strings::we_regex::s1_enabled()
                            && *self.ctx.terms.sort(args[0]) == Sort::Bool
                        {
                            if let Some((word, regex)) = self.translate_membership_pair(
                                args[0],
                                args[1],
                                true,
                                &mut var_ids,
                                &mut var_terms,
                            ) {
                                let var = match word.as_slice() {
                                    [WeSym::Var(v)] => *v,
                                    _ => {
                                        let Some(s) = fresh_skolem(&mut var_terms) else {
                                            continue;
                                        };
                                        equations.push(WeEquation {
                                            lhs: vec![WeSym::Var(s)],
                                            rhs: word,
                                        });
                                        s
                                    }
                                };
                                memberships.push(WeMembership {
                                    var,
                                    regex,
                                    positive: true,
                                });
                            }
                        }
                        continue;
                    }
                    let (Some(lhs), Some(rhs)) = (
                        self.flatten_word(args[0], &mut var_ids, &mut var_terms),
                        self.flatten_word(args[1], &mut var_ids, &mut var_terms),
                    ) else {
                        continue;
                    };
                    // Syntactic tautologies (e.g. folded `lit = lit`) carry
                    // no information and only burn the symbol budget.
                    if lhs == rhs {
                        continue;
                    }
                    equations.push(WeEquation { lhs, rhs });
                }
                // M2: POSITIVE predicate reductions to concat form. Each is a
                // faithful existential elimination, so the reduced equation
                // set stays a sound basis for UNSAT:
                //   (str.contains s t)  ⟺  ∃ k1 k2. s = k1 · t · k2
                //   (str.prefixof p s)  ⟺  ∃ k.     s = p · k
                //   (str.suffixof p s)  ⟺  ∃ k.     s = k · p
                // Negative occurrences are NOT reducible this way and stay
                // out of the fragment (the full-model validation covers them
                // on the SAT path).
                TermData::App(Symbol::Named(name), args)
                    if name == "str.contains" && args.len() == 2 =>
                {
                    let (Some(s), Some(t)) = (
                        self.flatten_word(args[0], &mut var_ids, &mut var_terms),
                        self.flatten_word(args[1], &mut var_ids, &mut var_terms),
                    ) else {
                        continue;
                    };
                    let (Some(k1), Some(k2)) =
                        (fresh_skolem(&mut var_terms), fresh_skolem(&mut var_terms))
                    else {
                        continue;
                    };
                    let mut rhs = vec![WeSym::Var(k1)];
                    rhs.extend(t);
                    rhs.push(WeSym::Var(k2));
                    equations.push(WeEquation { lhs: s, rhs });
                }
                TermData::App(Symbol::Named(name), args)
                    if (name == "str.prefixof" || name == "str.suffixof") && args.len() == 2 =>
                {
                    let is_prefix = name == "str.prefixof";
                    let (Some(p), Some(s)) = (
                        self.flatten_word(args[0], &mut var_ids, &mut var_terms),
                        self.flatten_word(args[1], &mut var_ids, &mut var_terms),
                    ) else {
                        continue;
                    };
                    let Some(k) = fresh_skolem(&mut var_terms) else {
                        continue;
                    };
                    let rhs = if is_prefix {
                        let mut w = p;
                        w.push(WeSym::Var(k));
                        w
                    } else {
                        let mut w = vec![WeSym::Var(k)];
                        w.extend(p);
                        w
                    };
                    equations.push(WeEquation { lhs: s, rhs });
                }
                // Stage 2: regex memberships over a single string variable.
                // POSITIVE memberships prune Nielsen branches by derivative
                // (they participate in Unsat), so the regex translation must
                // be EXACT — `translate_we_regex` bails on anything else.
                TermData::App(sym, args)
                    if matches!(sym.name(), "str.in_re" | "str.in.re") && args.len() == 2 =>
                {
                    let Some(word) = self.flatten_word(args[0], &mut var_ids, &mut var_terms)
                    else {
                        continue;
                    };
                    let Some(regex) = self.translate_we_regex(args[1], 0) else {
                        continue;
                    };
                    // A membership constrains ONE variable, but its subject may be
                    // a CONCATENATION (`(str.++ x y) ∈ R`). Bind the whole word to
                    // a fresh `s` (`s = x·y`) and constrain `s ∈ R`. Sound: `s` is
                    // fresh and equal to the concat, so `s ∈ R ⟺ (x·y) ∈ R`; the
                    // Nielsen solver then propagates it — with `x = "b"`,
                    // `s = "b"·y` and `derive(R,"b") = ∅` gives Unsat. Previously
                    // a concat subject was not a single variable, so the whole
                    // membership was silently dropped and `(str.++ x y) ∈ a*` ∧
                    // `x = "b"` came back `unknown` instead of `unsat`.
                    let var = match word.as_slice() {
                        [WeSym::Var(v)] => *v,
                        _ => {
                            let Some(s) = fresh_skolem(&mut var_terms) else {
                                continue;
                            };
                            equations.push(WeEquation {
                                lhs: vec![WeSym::Var(s)],
                                rhs: word,
                            });
                            s
                        }
                    };
                    memberships.push(WeMembership {
                        var,
                        regex,
                        positive: true,
                    });
                }
                _ => {}
            }
        }

        // Entailed-FALSE terms: disequations and negative memberships. A
        // negative membership `x ∉ R` is complemented to `x ∈ ¬R` at seeding
        // (Bucket B) and so DOES participate in Unsat via the exact complement;
        // disequations remain SAT-candidate filters only, except the trivial
        // syntactic `w != w`, which is entailed-false ⇒ Unsat.
        for &assertion in &forced_false {
            let TermData::App(sym, args) = self.ctx.terms.get(assertion) else {
                continue;
            };
            if matches!(sym.name(), "str.in_re" | "str.in.re") && args.len() == 2 {
                let Some(word) = self.flatten_word(args[0], &mut var_ids, &mut var_terms) else {
                    continue;
                };
                let Some(regex) = self.translate_we_regex(args[1], 0) else {
                    continue;
                };
                // Same concat handling as the positive case above: a negative
                // membership over a concatenation binds the word to a fresh
                // `s = x·y` and constrains `s ∉ R`. Sound because `s` is fresh
                // and equal to the concat, so `s ∉ R ⟺ (x·y) ∉ R`.
                let var = match word.as_slice() {
                    [WeSym::Var(v)] => *v,
                    _ => {
                        let Some(s) = fresh_skolem(&mut var_terms) else {
                            continue;
                        };
                        equations.push(WeEquation {
                            lhs: vec![WeSym::Var(s)],
                            rhs: word,
                        });
                        s
                    }
                };
                memberships.push(WeMembership {
                    var,
                    regex,
                    positive: false,
                });
                continue;
            }
            let Symbol::Named(name) = sym else {
                continue;
            };
            if name != "=" || args.len() != 2 {
                continue;
            }
            if *self.ctx.terms.sort(args[0]) != Sort::String {
                // Strings S1: a forced-FALSE boolean equality of two
                // membership atoms over the SAME subject (the sygus-qgen
                // shape `(not (= (str.in_re x R1) (str.in_re x R2)))`) is
                // exactly one membership in the XOR combination
                // (R1∩¬R2) ∪ (¬R1∩R2) — see `translate_membership_pair`.
                if ay_strings::we_regex::s1_enabled() && *self.ctx.terms.sort(args[0]) == Sort::Bool
                {
                    if let Some((word, regex)) = self.translate_membership_pair(
                        args[0],
                        args[1],
                        false,
                        &mut var_ids,
                        &mut var_terms,
                    ) {
                        let var = match word.as_slice() {
                            [WeSym::Var(v)] => *v,
                            _ => {
                                let Some(s) = fresh_skolem(&mut var_terms) else {
                                    continue;
                                };
                                equations.push(WeEquation {
                                    lhs: vec![WeSym::Var(s)],
                                    rhs: word,
                                });
                                s
                            }
                        };
                        memberships.push(WeMembership {
                            var,
                            regex,
                            positive: true,
                        });
                    }
                }
                continue;
            }
            // A pure string disequation `x != "lit"` (a single string
            // VARIABLE vs a constant string literal, either orientation) is
            // EXACTLY the negated membership `x ∉ (str.to_re "lit")`, i.e.
            // `x ∈ ¬Lit("lit") = x ∈ Comp(Lit("lit"))`. Seed it as a NEGATIVE
            // membership (Bucket B) so it (a) becomes a first-class firing
            // trigger and (b) flows through the product-derivative witness
            // search (`find_witness` over the intersected `⋂ Rᵢ ∩ ⋂ ¬Lit(sⱼ)`),
            // instead of stranding as a SAT-candidate-filter-only disequation
            // that never anchors a witness — the currently-`unknown` unanchored
            // bare-disequation case. Sound both ways: the constraint is
            // entailed (from `forced_false`), the complement is EXACT, the
            // witness `≠` every forbidden literal by construction, and the SAT
            // path re-validates by pinning `x = witness` and re-running the
            // full solver. The disequation is ALSO retained below (redundant
            // but harmless: same forbidden literal, re-checked by the candidate
            // filter — preserves the existing var-vs-var / var-vs-concat path
            // unchanged).
            for (v_side, c_side) in [(args[0], args[1]), (args[1], args[0])] {
                let Some(var) = intern_var(v_side, &mut var_ids, &mut var_terms) else {
                    continue;
                };
                let TermData::Const(Constant::String(lit)) = self.ctx.terms.get(c_side) else {
                    continue;
                };
                memberships.push(WeMembership {
                    var,
                    regex: WeRegex::lit(lit),
                    positive: false,
                });
                break;
            }

            let (Some(lhs), Some(rhs)) = (
                self.flatten_word(args[0], &mut var_ids, &mut var_terms),
                self.flatten_word(args[1], &mut var_ids, &mut var_terms),
            ) else {
                continue;
            };
            disequations.push(WeEquation { lhs, rhs });
        }

        // Fire when the fragment gives the search something to decide beyond
        // the existing folding paths. Two independent triggers:
        //
        //  (a) a SYMBOLIC word equation (the original Nielsen trigger);
        //  (b) a symbolic `str.in_re` membership over a single string
        //      variable — POSITIVE (Bucket A) or NEGATIVE / `re.comp`
        //      (Bucket B, decided via the Boolean-closed complement). With no
        //      equations the Nielsen search starts at a solved form, so the
        //      decision is exactly the product-derivative witness search /
        //      definite emptiness check on the intersected memberships
        //      `⋂ Rᵢ ∩ ⋂ ¬Sⱼ` — a SAT witness (validated by pinning
        //      `x = witness` and re-running the full solver, which re-evaluates
        //      every membership, `re.comp` included, through the ground
        //      `regexp` evaluator) or a sound `is_empty_lang`/leaf-conflict
        //      UNSAT over the (entailed, exactly-translated and exactly-
        //      complemented) memberships.
        //
        // Purely-ground / equation-and-membership-free fragments are left to
        // the existing paths.
        let has_symbolic_eq = equations.iter().any(|eq| {
            eq.lhs
                .iter()
                .chain(eq.rhs.iter())
                .any(|s| matches!(s, WeSym::Var(_)))
        });
        // Bucket B: ANY symbolic membership — positive OR negative — is a
        // firing trigger, because complement makes a negated membership
        // `x ∉ R ≡ x ∈ ¬R` a first-class decidable constraint.
        let has_membership = !memberships.is_empty();
        if (equations.is_empty() || !has_symbolic_eq) && !has_membership {
            if debug_auflia_enabled() {
                safe_eprintln!(
                    "[WORDEQ] bail: {} eqs, symbolic={has_symbolic_eq}, membership={has_membership}",
                    equations.len()
                );
            }
            return None;
        }
        if var_terms.len() > MAX_WE_VARS
            || equations.len() > MAX_WE_EQS
            || disequations.len() > MAX_WE_EQS
            || memberships.len() > MAX_WE_EQS
        {
            if debug_auflia_enabled() {
                safe_eprintln!(
                    "[WORDEQ] bail: caps vars={} eqs={} diseqs={} res={}",
                    var_terms.len(),
                    equations.len(),
                    disequations.len(),
                    memberships.len()
                );
            }
            return None;
        }
        let total_syms: usize = equations
            .iter()
            .chain(disequations.iter())
            .map(|eq| eq.lhs.len() + eq.rhs.len())
            .sum();
        if total_syms > max_we_syms() {
            if debug_auflia_enabled() {
                safe_eprintln!("[WORDEQ] bail: total_syms={total_syms}");
            }
            return None;
        }

        // Faithful exact lengths ONLY: toplevel `(= (str.len x) N)` in either
        // orientation, unscaled. (The looser bound detector divides scaled
        // coefficients with integer division, which is not faithful enough to
        // participate in an UNSAT conclusion.)
        let mut exact_lens: Vec<(u32, usize)> = Vec::new();
        for &assertion in &forced_true {
            let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(assertion) else {
                continue;
            };
            if name != "=" || args.len() != 2 {
                continue;
            }
            for (a, b) in [(args[0], args[1]), (args[1], args[0])] {
                let TermData::App(Symbol::Named(f), fargs) = self.ctx.terms.get(a) else {
                    continue;
                };
                if f != "str.len" || fargs.len() != 1 {
                    continue;
                }
                let TermData::Const(Constant::Int(n)) = self.ctx.terms.get(b) else {
                    continue;
                };
                let Ok(len) = usize::try_from(n) else {
                    continue;
                };
                if let Some(&vid) = var_ids.get(&fargs[0]) {
                    exact_lens.push((vid, len));
                }
                break;
            }
        }
        // Contradictory exact lengths for the same variable are NOT resolved
        // here; keep the first only (the solver treats the map as ground
        // truth). A genuine `len=1 ∧ len=2` contradiction is decided by
        // `has_exact_string_length_contradiction` in the normal pipeline.
        exact_lens.sort_unstable_by_key(|(v, _)| *v);
        exact_lens.dedup_by_key(|(v, _)| *v);

        // Stage 3b: FAITHFUL interval length bounds from toplevel unscaled
        // comparisons `(op (str.len x) N)` (either orientation, strict or
        // non-strict). These participate in Nielsen pruning, hence in UNSAT
        // conclusions — so only exact, unscaled shapes are taken (the LIA
        // lane's scaled-bound detector divides with integer rounding and is
        // used for enumeration only, never here).
        let mut len_bounds = self.extract_faithful_len_bounds(&forced_true, &var_ids);

        // DERIVED per-variable bounds: exact interval propagation over the
        // ENTAILED linear length facts (forced-true `str.len` comparisons —
        // including multi-variable sums like `len(x) + len(sink) < 50` — plus
        // the length abstraction of the extracted equations). Every emitted
        // bound is a proven consequence, never a model value, so it is sound
        // to prune on. This is what lets the Nielsen search refute sanitizer
        // benchmarks whose only length fact is a budget over a concat chain.
        len_bounds.extend(self.derive_entailed_len_bounds(
            &forced_true,
            &var_ids,
            &equations,
            var_terms.len(),
        ));

        Some(WordEqExtraction {
            problem: WeProblem {
                equations,
                disequations,
                num_vars: u32::try_from(var_terms.len()).ok()?,
                exact_lens,
                len_bounds,
                memberships,
            },
            var_terms,
        })
    }

    /// Compute the unit-propagated boolean closure of the toplevel assertion
    /// set: `(forced_true, forced_false)` term lists (deterministic order).
    ///
    /// Every returned term is ENTAILED by the assertions (true resp. false in
    /// every model), by construction:
    /// * toplevel assertions are true;
    /// * a true `and` forces each conjunct; a false `or` forces each disjunct;
    /// * `not` flips polarity;
    /// * a true boolean equality with one side forced propagates the same
    ///   polarity to the other side (iterated to fixpoint).
    ///
    /// No case-splitting is performed (an unforced `or` contributes nothing),
    /// so the closure is pure unit propagation — sound for Unsat extraction.
    fn forced_literal_closure(&self) -> (Vec<TermId>, Vec<TermId>) {
        self.forced_literal_closure_ext(false)
    }

    /// [`Self::forced_literal_closure`] with an optional extra propagation rule
    /// (strings increment W4).
    ///
    /// `decode_ite_int`: additionally decode the PyEx/CVC integer-encoded
    /// Boolean idiom `(= (ite C a b) k)` (`a`, `b`, `k` distinct integer
    /// literals) — the atom being true forces `C` to a definite polarity, so
    /// `C` joins the closure. This is exact unit propagation on a tautologous
    /// rewriting (`(= (ite C 1 0) 0)` ⟺ `¬C`), so every emitted term stays
    /// ENTAILED and the closure keeps its soundness contract.
    ///
    /// `decode_ite_int == false` reproduces the original closure byte for
    /// byte, so the default (non-W4) callers are unaffected.
    pub(super) fn forced_literal_closure_ext(
        &self,
        decode_ite_int: bool,
    ) -> (Vec<TermId>, Vec<TermId>) {
        let mut true_set: HashSet<TermId> = HashSet::default();
        let mut false_set: HashSet<TermId> = HashSet::default();
        let mut true_list: Vec<TermId> = Vec::new();
        let mut false_list: Vec<TermId> = Vec::new();
        // Boolean equalities seen while expanding, re-checked to fixpoint.
        let mut bool_eqs: Vec<(TermId, TermId)> = Vec::new();

        let mut work: Vec<(TermId, bool)> =
            self.ctx.assertions.iter().map(|&a| (a, true)).collect();
        while let Some((t, polarity)) = work.pop() {
            let (set, list) = if polarity {
                (&mut true_set, &mut true_list)
            } else {
                (&mut false_set, &mut false_list)
            };
            if !set.insert(t) {
                continue;
            }
            list.push(t);
            if decode_ite_int {
                if let Some((cond, same_polarity)) = self.decode_ite_int_eq(t) {
                    work.push((cond, if same_polarity { polarity } else { !polarity }));
                }
            }
            match self.ctx.terms.get(t) {
                TermData::Not(inner) => work.push((*inner, !polarity)),
                TermData::App(Symbol::Named(name), args) if name == "and" && polarity => {
                    work.extend(args.iter().map(|&a| (a, true)));
                }
                TermData::App(Symbol::Named(name), args) if name == "or" && !polarity => {
                    work.extend(args.iter().map(|&a| (a, false)));
                }
                TermData::App(Symbol::Named(name), args)
                    if name == "="
                        && args.len() == 2
                        && polarity
                        && *self.ctx.terms.sort(args[0]) == Sort::Bool =>
                {
                    bool_eqs.push((args[0], args[1]));
                }
                _ => {}
            }
            // Re-check forced boolean equalities after every NEW decision:
            // when one side is decided, push the other with the same
            // polarity. The decided sets only grow, so this terminates.
            for &(a, b) in &bool_eqs {
                for (x, y) in [(a, b), (b, a)] {
                    if true_set.contains(&x) && !true_set.contains(&y) {
                        work.push((y, true));
                    }
                    if false_set.contains(&x) && !false_set.contains(&y) {
                        work.push((y, false));
                    }
                }
            }
        }
        (true_list, false_list)
    }

    /// Decode the integer-encoded Boolean idiom `(= (ite C a b) k)` with
    /// integer literals `a`, `b`, `k`: returns `(C, same_polarity)` where
    /// `same_polarity` says whether the ATOM being true forces `C` true.
    ///
    /// `(= (ite C 1 0) 1)` ⟺ `C`; `(= (ite C 1 0) 0)` ⟺ `¬C`. Exactly one of
    /// the branches may equal `k` for the equivalence to hold, so the
    /// ambiguous `a == b` case yields `None`.
    pub(super) fn decode_ite_int_eq(&self, t: TermId) -> Option<(TermId, bool)> {
        let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(t) else {
            return None;
        };
        if name != "=" || args.len() != 2 {
            return None;
        }
        let int_const = |x: TermId| -> Option<num_bigint::BigInt> {
            match self.ctx.terms.get(x) {
                TermData::Const(Constant::Int(n)) => Some(n.clone()),
                _ => None,
            }
        };
        for (ite_side, k_side) in [(args[0], args[1]), (args[1], args[0])] {
            let Some(k) = int_const(k_side) else { continue };
            let TermData::Ite(cond, then_v, else_v) = self.ctx.terms.get(ite_side) else {
                continue;
            };
            let (Some(tv), Some(ev)) = (int_const(*then_v), int_const(*else_v)) else {
                continue;
            };
            if tv == k && ev != k {
                return Some((*cond, true));
            }
            if ev == k && tv != k {
                return Some((*cond, false));
            }
        }
        None
    }

    /// Extract faithful interval length bounds `lo ≤ |x| ≤ hi` for interned
    /// word-equation variables from toplevel assertions of the shape
    /// `(<= (str.len x) N)`, `(< N (str.len x))`, etc. (both orientations).
    ///
    /// Every emitted bound is an EXACT consequence of a single asserted
    /// comparison against an integer constant — sound to prune on. `str.len`
    /// is intrinsically ≥ 0, so an upper bound below 0 is recorded as the
    /// infeasible window `1 ≤ |x| ≤ 0` (the solver reports Unsat, which is
    /// correct: the assertion itself is unsatisfiable).
    fn extract_faithful_len_bounds(
        &self,
        forced_true: &[TermId],
        var_ids: &HashMap<TermId, u32>,
    ) -> Vec<WeLenBound> {
        let mut out: Vec<WeLenBound> = Vec::new();
        let strlen_var = |t: TermId| -> Option<u32> {
            let TermData::App(Symbol::Named(f), fargs) = self.ctx.terms.get(t) else {
                return None;
            };
            if f != "str.len" || fargs.len() != 1 {
                return None;
            }
            var_ids.get(&fargs[0]).copied()
        };
        let int_const = |t: TermId| -> Option<i64> {
            let TermData::Const(Constant::Int(n)) = self.ctx.terms.get(t) else {
                return None;
            };
            i64::try_from(n).ok()
        };
        for &assertion in forced_true {
            let TermData::App(Symbol::Named(op), args) = self.ctx.terms.get(assertion) else {
                continue;
            };
            if args.len() != 2 || !matches!(op.as_str(), "<=" | ">=" | "<" | ">") {
                continue;
            }
            // Normalize to `str.len(x) REL n` with REL ∈ {≤, ≥} inclusive.
            let (vid, mut n, len_is_upper) = match (
                strlen_var(args[0]),
                int_const(args[1]),
                int_const(args[0]),
                strlen_var(args[1]),
            ) {
                (Some(v), Some(n), _, _) => {
                    // (op (str.len x) n)
                    match op.as_str() {
                        "<=" => (v, n, true),
                        "<" => (v, n.saturating_sub(1), true),
                        ">=" => (v, n, false),
                        ">" => (v, n.saturating_add(1), false),
                        _ => continue,
                    }
                }
                (_, _, Some(n), Some(v)) => {
                    // (op n (str.len x)) — direction flips.
                    match op.as_str() {
                        "<=" => (v, n, false),
                        "<" => (v, n.saturating_add(1), false),
                        ">=" => (v, n, true),
                        ">" => (v, n.saturating_sub(1), true),
                        _ => continue,
                    }
                }
                _ => continue,
            };
            if len_is_upper {
                // |x| ≤ n. n < 0 is infeasible outright (|x| ≥ 0).
                if n < 0 {
                    out.push(WeLenBound {
                        var: vid,
                        lo: 1,
                        hi: Some(0),
                    });
                    continue;
                }
                let Ok(hi) = usize::try_from(n) else { continue };
                out.push(WeLenBound {
                    var: vid,
                    lo: 0,
                    hi: Some(hi),
                });
            } else {
                // |x| ≥ n. n ≤ 0 carries no information.
                if n <= 0 {
                    n = 0;
                }
                let Ok(lo) = usize::try_from(n) else { continue };
                if lo > 0 {
                    out.push(WeLenBound {
                        var: vid,
                        lo,
                        hi: None,
                    });
                }
            }
        }
        out
    }

    /// Derive per-variable interval length bounds ENTAILED by the forced-true
    /// linear `str.len` facts plus the length abstraction of the extracted
    /// word equations, by exact integer interval propagation.
    ///
    /// Soundness (bounds participate in Unsat pruning):
    /// * every parsed comparison is a forced-true assertion — entailed;
    /// * `|lhs| = |rhs|` is entailed by each extracted equation (which is
    ///   itself entailed, see `forced_literal_closure`); `|s·t| = |s| + |t|`
    ///   and `|lit|` = its char count are definitional;
    /// * `|v| ≥ 0` is intrinsic;
    /// * each propagation step is an exact integer consequence: from
    ///   `Σ cⱼ·xⱼ ≤ K` and interval bounds on the other variables,
    ///   `cᵢ·xᵢ ≤ K − Σ_{j≠i} min(cⱼ·xⱼ)`, with floor/ceil division exact
    ///   over the integers.
    ///
    /// No model values are consulted anywhere — only proven consequences.
    /// Strict comparisons are tightened by 1 (integers). Unparseable terms
    /// (non-linear, non-var `str.len` arguments, …) drop the whole
    /// comparison — sound: fewer facts, weaker bounds.
    fn derive_entailed_len_bounds(
        &self,
        forced_true: &[TermId],
        var_ids: &HashMap<TermId, u32>,
        equations: &[WeEquation],
        num_fragment_atoms: usize,
    ) -> Vec<WeLenBound> {
        const MAX_ATOMS: usize = 128;
        const MAX_CONSTRAINTS: usize = 128;
        const MAX_COEFF: i128 = 1 << 20;
        /// Values beyond this carry no usable pruning information.
        const MAX_VALUE: i128 = 1_000_000_000_000_000;

        // Atom space: fragment variable ids `0..num_fragment_atoms`, plus
        // fresh ids for OTHER string variables mentioned in length facts
        // (they participate in propagation but are never emitted).
        let mut extra_atoms: HashMap<TermId, usize> = HashMap::default();
        let mut n_atoms = num_fragment_atoms;

        // A linear constraint `Σ coeffs ≤ bound` over atom ids.
        let mut constraints: Vec<(Vec<(usize, i128)>, i128)> = Vec::new();

        // Parse `t` into `Σ coeff·|atom| + k` (iterative; multiplier-scaled).
        // Returns None when any sub-term is outside the linear-length
        // fragment.
        let parse_linear = |exec: &Executor,
                            t: TermId,
                            extra_atoms: &mut HashMap<TermId, usize>,
                            n_atoms: &mut usize|
         -> Option<(HashMap<usize, i128>, i128)> {
            let mut coeffs: HashMap<usize, i128> = HashMap::default();
            let mut k: i128 = 0;
            let mut stack: Vec<(TermId, i128)> = vec![(t, 1)];
            while let Some((t, mult)) = stack.pop() {
                if mult.abs() > MAX_COEFF {
                    return None;
                }
                match exec.ctx.terms.get(t) {
                    TermData::Const(Constant::Int(n)) => {
                        k += mult * i128::try_from(n).ok()?;
                    }
                    TermData::App(Symbol::Named(name), args) if name == "+" => {
                        stack.extend(args.iter().map(|&a| (a, mult)));
                    }
                    TermData::App(Symbol::Named(name), args) if name == "-" && !args.is_empty() => {
                        if args.len() == 1 {
                            stack.push((args[0], -mult));
                        } else {
                            stack.push((args[0], mult));
                            stack.extend(args[1..].iter().map(|&a| (a, -mult)));
                        }
                    }
                    TermData::App(Symbol::Named(name), args) if name == "*" && args.len() == 2 => {
                        let (c, other) =
                            match (exec.ctx.terms.get(args[0]), exec.ctx.terms.get(args[1])) {
                                (TermData::Const(Constant::Int(n)), _) => {
                                    (i128::try_from(n).ok()?, args[1])
                                }
                                (_, TermData::Const(Constant::Int(n))) => {
                                    (i128::try_from(n).ok()?, args[0])
                                }
                                _ => return None,
                            };
                        stack.push((other, mult.checked_mul(c)?));
                    }
                    TermData::App(Symbol::Named(name), args)
                        if name == "str.len" && args.len() == 1 =>
                    {
                        // |v| → atom; |lit| → constant; |s·t| → sum.
                        let mut wstack: Vec<TermId> = vec![args[0]];
                        while let Some(s) = wstack.pop() {
                            match exec.ctx.terms.get(s) {
                                TermData::Const(Constant::String(lit)) => {
                                    k += mult * lit.chars().count() as i128;
                                }
                                TermData::Var(..) if *exec.ctx.terms.sort(s) == Sort::String => {
                                    let atom = match var_ids.get(&s) {
                                        Some(&vid) => vid as usize,
                                        None => *extra_atoms.entry(s).or_insert_with(|| {
                                            let id = *n_atoms;
                                            *n_atoms += 1;
                                            id
                                        }),
                                    };
                                    *coeffs.entry(atom).or_insert(0) += mult;
                                }
                                TermData::App(Symbol::Named(op), sargs) if op == "str.++" => {
                                    wstack.extend(sargs.iter().copied());
                                }
                                _ => return None,
                            }
                        }
                    }
                    _ => return None,
                }
            }
            Some((coeffs, k))
        };

        // 1. Forced-true integer comparisons over linear length expressions.
        for &assertion in forced_true {
            let TermData::App(Symbol::Named(op), args) = self.ctx.terms.get(assertion) else {
                continue;
            };
            if args.len() != 2 || !matches!(op.as_str(), "<=" | "<" | ">=" | ">" | "=") {
                continue;
            }
            if *self.ctx.terms.sort(args[0]) != Sort::Int {
                continue;
            }
            let (Some((cl, kl)), Some((cr, kr))) = (
                parse_linear(self, args[0], &mut extra_atoms, &mut n_atoms),
                parse_linear(self, args[1], &mut extra_atoms, &mut n_atoms),
            ) else {
                continue;
            };
            // diff = lhs − rhs = Σ c·x + k; the comparison becomes bounds on
            // Σ c·x relative to −k.
            let mut diff: HashMap<usize, i128> = cl;
            for (a, c) in cr {
                *diff.entry(a).or_insert(0) -= c;
            }
            let k = kl - kr;
            let coeffs: Vec<(usize, i128)> = diff.into_iter().filter(|&(_, c)| c != 0).collect();
            if coeffs.is_empty() || coeffs.len() > MAX_ATOMS {
                continue;
            }
            let neg = |cs: &[(usize, i128)]| -> Vec<(usize, i128)> {
                cs.iter().map(|&(a, c)| (a, -c)).collect()
            };
            match op.as_str() {
                // Σ c·x + k ≤ 0  ⇔  Σ c·x ≤ −k
                "<=" => constraints.push((coeffs, -k)),
                "<" => constraints.push((coeffs, -k - 1)),
                ">=" => constraints.push((neg(&coeffs), k)),
                ">" => constraints.push((neg(&coeffs), k - 1)),
                "=" => {
                    constraints.push((neg(&coeffs), k));
                    constraints.push((coeffs, -k));
                }
                _ => {}
            }
        }
        if constraints.is_empty() {
            return Vec::new();
        }

        // 2. Length abstraction of the extracted (entailed) equations:
        //    Σ_{v∈lhs} |v| + #chars(lhs) = Σ_{v∈rhs} |v| + #chars(rhs).
        for eq in equations {
            let mut coeffs: HashMap<usize, i128> = HashMap::default();
            let mut k: i128 = 0;
            for sym in &eq.lhs {
                match sym {
                    WeSym::Ch(_) => k += 1,
                    WeSym::Var(v) => *coeffs.entry(*v as usize).or_insert(0) += 1,
                }
            }
            for sym in &eq.rhs {
                match sym {
                    WeSym::Ch(_) => k -= 1,
                    WeSym::Var(v) => *coeffs.entry(*v as usize).or_insert(0) -= 1,
                }
            }
            let coeffs: Vec<(usize, i128)> = coeffs.into_iter().filter(|&(_, c)| c != 0).collect();
            if coeffs.is_empty() {
                continue;
            }
            let neg: Vec<(usize, i128)> = coeffs.iter().map(|&(a, c)| (a, -c)).collect();
            constraints.push((coeffs, -k));
            constraints.push((neg, k));
        }

        if n_atoms > MAX_ATOMS || constraints.len() > MAX_CONSTRAINTS {
            return Vec::new();
        }

        // 3. Exact interval propagation to a bounded fixpoint.
        let mut lo: Vec<i128> = vec![0; n_atoms];
        let mut hi: Vec<Option<i128>> = vec![None; n_atoms];
        'rounds: for _ in 0..16 {
            let mut changed = false;
            for (coeffs, bound) in &constraints {
                // Minimum contribution of each term; count unbounded ones.
                let mut finite_sum: i128 = 0;
                let mut inf_count = 0usize;
                let mut inf_atom = usize::MAX;
                for &(a, c) in coeffs {
                    if c > 0 {
                        finite_sum += c * lo[a];
                    } else {
                        match hi[a] {
                            Some(h) => finite_sum += c * h,
                            None => {
                                inf_count += 1;
                                inf_atom = a;
                            }
                        }
                    }
                }
                for &(a, c) in coeffs {
                    let residual = if inf_count == 0 {
                        let own = if c > 0 {
                            c * lo[a]
                        } else {
                            c * hi[a].unwrap_or(0)
                        };
                        bound - (finite_sum - own)
                    } else if inf_count == 1 && a == inf_atom {
                        bound - finite_sum
                    } else {
                        continue;
                    };
                    // c·x ≤ residual, exact integer division.
                    if c > 0 {
                        let new_hi = residual.div_euclid(c);
                        if new_hi < lo[a] {
                            // Entailed contradiction. Emit an infeasible
                            // window when it lands on a fragment atom (the
                            // solver reports Unsat, which is correct);
                            // otherwise stop with what is already proven.
                            if a < num_fragment_atoms {
                                return vec![WeLenBound {
                                    var: a as u32,
                                    lo: 1,
                                    hi: Some(0),
                                }];
                            }
                            break 'rounds;
                        }
                        if new_hi <= MAX_VALUE && hi[a].is_none_or(|h| new_hi < h) {
                            hi[a] = Some(new_hi);
                            changed = true;
                        }
                    } else {
                        // c < 0: x ≥ ⌈residual / c⌉ (div_euclid with a
                        // negative divisor rounds up).
                        let new_lo = residual.div_euclid(c).max(0);
                        if matches!(hi[a], Some(h) if new_lo > h) {
                            if a < num_fragment_atoms {
                                return vec![WeLenBound {
                                    var: a as u32,
                                    lo: 1,
                                    hi: Some(0),
                                }];
                            }
                            break 'rounds;
                        }
                        if new_lo > lo[a] && new_lo <= MAX_VALUE {
                            lo[a] = new_lo;
                            changed = true;
                        }
                    }
                }
            }
            if !changed {
                break;
            }
        }

        // 4. Emit informative windows for fragment variables only.
        let mut out = Vec::new();
        for vid in 0..num_fragment_atoms {
            let l = usize::try_from(lo[vid]).unwrap_or(0);
            let h = hi[vid].and_then(|h| usize::try_from(h).ok());
            if l > 0 || h.is_some() {
                out.push(WeLenBound {
                    var: vid as u32,
                    lo: l,
                    hi: h,
                });
            }
        }
        out
    }

    /// Strings S1: translate a boolean (in)equality between two `str.in_re`
    /// atoms over the SAME subject into a single EXACT membership.
    ///
    /// ```text
    ///   (= (str.in_re w R1) (str.in_re w R2))   ⟺  w ∈ (R1∩R2) ∪ (¬R1∩¬R2)
    ///   ¬(= (str.in_re w R1) (str.in_re w R2))  ⟺  w ∈ (R1∩¬R2) ∪ (¬R1∩R2)
    /// ```
    ///
    /// SOUNDNESS: the equivalences are plain Boolean set algebra, and
    /// [`WeRegex::comp`] is exact over the full alphabet, so the combined
    /// membership is EXACTLY the asserted (entailed) constraint — it may
    /// participate in Unsat conclusions on the same footing as any other
    /// exactly-translated membership; SAT witnesses stay model-validated
    /// fail-closed. Returns `None` (constraint skipped — sound: Unsat uses a
    /// subset, SAT validates the full set) when either side is not a
    /// membership, the subjects differ, the regexes do not translate
    /// exactly, or the combination exceeds the size cap.
    fn translate_membership_pair(
        &self,
        lhs: TermId,
        rhs: TermId,
        equal: bool,
        var_ids: &mut HashMap<TermId, u32>,
        var_terms: &mut Vec<Option<TermId>>,
    ) -> Option<(WeWord, WeRegex)> {
        let membership = |t: TermId| -> Option<(TermId, TermId)> {
            let TermData::App(sym, args) = self.ctx.terms.get(t) else {
                return None;
            };
            if !matches!(sym.name(), "str.in_re" | "str.in.re") || args.len() != 2 {
                return None;
            }
            Some((args[0], args[1]))
        };
        let (s1, r1t) = membership(lhs)?;
        let (s2, r2t) = membership(rhs)?;
        let w1 = self.flatten_word(s1, var_ids, var_terms)?;
        let w2 = self.flatten_word(s2, var_ids, var_terms)?;
        if w1 != w2 {
            return None;
        }
        let r1 = self.translate_we_regex(r1t, 0)?;
        let r2 = self.translate_we_regex(r2t, 0)?;
        let combined = if equal {
            WeRegex::union(vec![
                WeRegex::inter(vec![r1.clone(), r2.clone()]),
                WeRegex::inter(vec![WeRegex::comp(r1), WeRegex::comp(r2)]),
            ])
        } else {
            WeRegex::union(vec![
                WeRegex::inter(vec![r1.clone(), WeRegex::comp(r2.clone())]),
                WeRegex::inter(vec![WeRegex::comp(r1), r2]),
            ])
        };
        if combined.size() > max_we_regex_size() {
            return None;
        }
        Some((w1, combined))
    }

    /// Translate a ground regex term into a [`WeRegex`] — EXACT or bail.
    ///
    /// Memberships participate in `Unsat` conclusions, so the translation must
    /// denote exactly the term's language. `re.comp`/`re.diff` are supported
    /// exactly via the Boolean-closed `WeRegex::comp` (Bucket B); any remaining
    /// unsupported or non-ground construct returns `None` and the membership is
    /// skipped entirely.
    ///
    /// Visible across `crate::executor` so the model-construction bridge
    /// (`model::string_witness`, strings W1/W1b/W2) can reuse the SAME exact
    /// translation instead of duplicating it — construction and refutation
    /// must agree on what a regex term denotes.
    pub(in crate::executor) fn translate_we_regex(
        &self,
        t: TermId,
        depth: usize,
    ) -> Option<WeRegex> {
        if depth > 32 {
            return None;
        }
        let TermData::App(sym, args) = self.ctx.terms.get(t) else {
            return None;
        };
        let str_const = |t: TermId| -> Option<String> {
            match self.ctx.terms.get(t) {
                TermData::Const(Constant::String(s)) => Some(s.clone()),
                _ => None,
            }
        };
        let translate_all = |args: &[TermId]| -> Option<Vec<WeRegex>> {
            args.iter()
                .map(|&a| self.translate_we_regex(a, depth + 1))
                .collect()
        };
        let out = match sym.name() {
            "re.none" if args.is_empty() => WeRegex::None,
            "re.all" if args.is_empty() => WeRegex::All,
            "re.allchar" if args.is_empty() => WeRegex::AnyChar,
            // SMT-LIB `re.range` semantics (empty language for non-singleton
            // endpoints or reversed bounds) live in the constructor.
            "re.range" if args.len() == 2 => {
                WeRegex::range(&str_const(args[0])?, &str_const(args[1])?)
            }
            "str.to_re" | "str.to.re" if args.len() == 1 => WeRegex::lit(&str_const(args[0])?),
            "re.++" if !args.is_empty() => WeRegex::concat(translate_all(args)?),
            "re.union" if !args.is_empty() => WeRegex::union(translate_all(args)?),
            "re.inter" if !args.is_empty() => WeRegex::inter(translate_all(args)?),
            "re.*" if args.len() == 1 => {
                WeRegex::star(self.translate_we_regex(args[0], depth + 1)?)
            }
            "re.+" if args.len() == 1 => {
                WeRegex::plus(self.translate_we_regex(args[0], depth + 1)?)
            }
            "re.opt" if args.len() == 1 => {
                WeRegex::opt(self.translate_we_regex(args[0], depth + 1)?)
            }
            // re.comp(R): complement over the FULL Unicode string alphabet.
            // Boolean-closed (Bucket B) — `WeRegex::comp` is exact, so a
            // complemented regex participates soundly in both witness search
            // (SAT) and definite-emptiness (UNSAT).
            "re.comp" if args.len() == 1 => {
                WeRegex::comp(self.translate_we_regex(args[0], depth + 1)?)
            }
            // re.diff(R, S) = R ∩ ¬S.
            "re.diff" if args.len() == 2 => WeRegex::inter(vec![
                self.translate_we_regex(args[0], depth + 1)?,
                WeRegex::comp(self.translate_we_regex(args[1], depth + 1)?),
            ]),
            // (_ re.loop lo hi) R = ⋃_{k=lo}^{hi} R^k, unrolled exactly as
            // R^lo · (R?)^(hi-lo) up to the unroll cap. `lo > hi` is the
            // empty language. Beyond the cap, S1 (`AY_WE_S1`) translates to
            // the EXACT bounded-repeat counter node [`WeRegex::loop_bounded`]
            // instead of bailing (corpus bounds reach 680) — same exactness
            // contract, so it participates in Unsat soundly; flags-off
            // behavior is unchanged (bail).
            "re.loop" if args.len() == 1 => {
                let Symbol::Indexed(_, indices) = sym else {
                    return None;
                };
                if indices.len() != 2 {
                    return None;
                }
                let (lo, hi) = (indices[0], indices[1]);
                if lo > hi {
                    WeRegex::None
                } else if hi > max_we_loop() {
                    if !ay_strings::we_regex::s1_enabled() {
                        return None;
                    }
                    let body = self.translate_we_regex(args[0], depth + 1)?;
                    WeRegex::loop_bounded(body, lo, hi)
                } else {
                    let body = self.translate_we_regex(args[0], depth + 1)?;
                    let mut parts: Vec<WeRegex> = Vec::new();
                    for _ in 0..lo {
                        parts.push(body.clone());
                    }
                    for _ in lo..hi {
                        parts.push(WeRegex::opt(body.clone()));
                    }
                    WeRegex::concat(parts)
                }
            }
            _ => return None,
        };
        if out.size() > max_we_regex_size() {
            return None;
        }
        Some(out)
    }

    /// Flatten a string term into a word over `WeSym`, returning `None` when
    /// the term contains anything besides variables, literals, and `str.++`.
    fn flatten_word(
        &self,
        term: TermId,
        var_ids: &mut HashMap<TermId, u32>,
        var_terms: &mut Vec<Option<TermId>>,
    ) -> Option<WeWord> {
        let mut out: WeWord = Vec::new();
        let mut stack: Vec<TermId> = vec![term];
        while let Some(t) = stack.pop() {
            match self.ctx.terms.get(t) {
                TermData::Const(Constant::String(s)) => {
                    out.extend(s.chars().map(WeSym::Ch));
                }
                TermData::Var(..) if *self.ctx.terms.sort(t) == Sort::String => {
                    let next = u32::try_from(var_terms.len()).ok()?;
                    let id = *var_ids.entry(t).or_insert_with(|| {
                        var_terms.push(Some(t));
                        next
                    });
                    out.push(WeSym::Var(id));
                }
                TermData::App(Symbol::Named(name), args) if name == "str.++" => {
                    // Push in reverse so children pop in left-to-right order.
                    for &arg in args.iter().rev() {
                        stack.push(arg);
                    }
                }
                _ => return None,
            }
        }
        Some(out)
    }

    /// Pin each candidate assignment as hard assumptions and accept SAT only
    /// after full model + assumption validation (the witness contract of
    /// [`Executor::try_string_var_witnesses`], generalized to simultaneous
    /// multi-variable assignments).
    fn try_word_eq_assignments(
        &mut self,
        solutions: &[Vec<(TermId, String)>],
    ) -> Result<Option<SolveResult>> {
        if solutions.is_empty() {
            return Ok(None);
        }

        let assertions_snapshot = self.ctx.assertions.clone();
        let saved_deadline = self.solve_deadline.get();
        let saved_last_model = self.last_model.clone();
        let saved_last_result = self.last_result.clone();
        let saved_last_unknown_reason = self.last_unknown_reason;
        let saved_last_model_validated = self.last_model_validated;
        let saved_last_validation_stats = self.last_validation_stats.clone();
        let saved_last_assumption_core = self.last_assumption_core.clone();
        let saved_bypass_taut = self.bypass_string_tautology_guard;
        let saved_slia_accepted = self.slia_accepted_unknown;
        let saved_skip_model_eval = self.skip_model_eval;

        for (i, solution) in solutions.iter().enumerate() {
            if self.should_abort_theory_loop() {
                self.restore_witness_state(
                    saved_deadline,
                    &saved_last_model,
                    &saved_last_result,
                    saved_last_unknown_reason,
                    saved_last_model_validated,
                    &saved_last_validation_stats,
                    &saved_last_assumption_core,
                    saved_bypass_taut,
                    saved_slia_accepted,
                    saved_skip_model_eval,
                );
                return Ok(Some(SolveResult::Unknown));
            }

            let assumptions: Vec<TermId> = solution
                .iter()
                .map(|(var, value)| {
                    let str_term = self.ctx.terms.mk_string(value.clone());
                    self.ctx.terms.mk_eq(*var, str_term)
                })
                .collect();

            self.restore_witness_state(
                saved_deadline,
                &saved_last_model,
                &saved_last_result,
                saved_last_unknown_reason,
                saved_last_model_validated,
                &saved_last_validation_stats,
                &saved_last_assumption_core,
                saved_bypass_taut,
                saved_slia_accepted,
                saved_skip_model_eval,
            );

            let candidate_deadline =
                ay_core::time::Instant::now() + std::time::Duration::from_secs(2);
            self.solve_deadline.set(Some(match saved_deadline {
                Some(dl) => dl.min(candidate_deadline),
                None => candidate_deadline,
            }));

            self.pivot_enum_depth += 1;
            let result = match self
                .solve_strings_lia_with_assumptions(&assertions_snapshot, &assumptions)
            {
                Ok(SolveResult::Sat) => {
                    self.last_result = Some(SolveResult::Sat);
                    match self.finalize_sat_model_validation()? {
                        SolveResult::Sat => self.finalize_sat_assumption_validation(&assumptions),
                        other => Ok(other),
                    }
                }
                other => other,
            };

            if let Ok(SolveResult::Sat) = result {
                self.merge_explicit_string_assignments_into_model(&assumptions);
                // Materialize witnesses for any OTHER string variables at the
                // outer level before accepting (same rationale as the
                // prefix/suffix witness pass: the inner validation ran at
                // `pivot_enum_depth > 0` where the materializer is a no-op).
                self.pivot_enum_depth -= 1;
                let full_model_ok = self.materialize_string_witnesses();
                if full_model_ok {
                    if debug_auflia_enabled() {
                        safe_eprintln!(
                            "[WORDEQ] candidate {} validated → SAT ({:?})",
                            i,
                            solution
                                .iter()
                                .map(|(v, s)| format!("{v:?}={s:?}"))
                                .collect::<Vec<_>>()
                        );
                    }
                    self.solve_deadline.set(saved_deadline);
                    return Ok(Some(SolveResult::Sat));
                }
            } else {
                self.pivot_enum_depth -= 1;
            }
            if debug_auflia_enabled() {
                safe_eprintln!("[WORDEQ] candidate {i} rejected — trying next");
            }
        }

        // No candidate validated — restore state and fall through.
        self.restore_witness_state(
            saved_deadline,
            &saved_last_model,
            &saved_last_result,
            saved_last_unknown_reason,
            saved_last_model_validated,
            &saved_last_validation_stats,
            &saved_last_assumption_core,
            saved_bypass_taut,
            saved_slia_accepted,
            saved_skip_model_eval,
        );
        Ok(None)
    }
}

#[cfg(test)]
mod config_tests {
    use super::*;

    #[test]
    fn max_we_loop_defaults_accepts_overrides_and_caps_before_allocation() {
        assert_eq!(parse_max_we_loop(None), MAX_WE_LOOP);
        assert_eq!(parse_max_we_loop(Some("64")), 64);
        assert_eq!(parse_max_we_loop(Some("invalid")), MAX_WE_LOOP);
        assert_eq!(
            parse_max_we_loop(Some("4294967295")),
            MAX_WE_REGEX_SIZE as u32
        );
    }
}
