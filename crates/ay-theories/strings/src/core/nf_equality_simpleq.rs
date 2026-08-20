// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Word equation solver: component-by-component NF comparison.
//!
//! `process_simple_neq` implements Cases 0-9 of CVC5's processSimpleNEq
//! (Liang et al. CAV 2014). The propagation-only caller is in `nf_equality`.

use super::*;

impl CoreSolver {
    /// Compare two normal forms component-by-component (processSimpleNEq).
    ///
    /// Implements Cases 0-5 of processSimpleNEq (Liang et al. CAV 2014)
    /// for the general NF-pair case.
    ///
    /// Cases:
    /// - 0: Both NFs exhausted — consistent (Ok).
    /// - 1: One side has remaining non-empty components — conflict.
    /// - 2: Same EQC representative — advance both.
    /// - 3b: Variable components with equal lengths — infer equality (N_UNIFY).
    /// - 4: One side exhausted, other has remaining — infer empty (N_ENDPOINT_EQ).
    /// - 5: Both constants — compare characters.
    ///
    /// `skolems` is used to deduplicate EmptySplit requests: if an EmptySplit
    /// on variable `x` was already requested (by a prior NF pair in the same
    /// check round), the cache returns false and we skip the duplicate request.
    ///
    /// Reference: `reference/cvc5/src/theory/strings/core_solver.cpp:1247-1750`
    pub(super) fn process_simple_neq(
        terms: &TermStore,
        state: &SolverState,
        nf1: &NormalForm,
        nf2: &NormalForm,
        infer: &mut InferenceManager,
        skolems: &mut SkolemCache,
    ) -> NfCheckResult {
        // Compute guarded NF pair explanation for lemma clauses. Without
        // guards, ConstSplit/VarSplit clauses persist after DPLL backtracking
        // when the NF context changes, causing false-UNSAT (#4094, #6261).
        //
        // EmptySplit is a tautology (x="" OR x!="") and needs no guards.
        // ConstSplit, VarSplit, ConstUnify, LengthSplit depend on NF context.
        //
        // build_pair_explanation_for_lemma validates NF deps strictly AND
        // augments with component→constant equalities. Returns None when
        // the explanation is empty or deps are unexplainable (#6273).
        //
        // Lazy NF explanation (#6309): compute on first use. EmptySplit
        // is a tautology (x="" OR x!="") and needs no guards. Gating the
        // entire function on explanation availability would block EmptySplit
        // from making CEGAR progress on formulas like prefixof+suffixof.
        let mut nf_reasons: Option<Vec<TheoryLit>> = None;
        macro_rules! require_nf_reasons {
            () => {{
                if nf_reasons.is_none() {
                    match Self::build_pair_explanation_for_lemma(terms, nf1, nf2, state) {
                        Some(reasons) => nf_reasons = Some(reasons),
                        None => return NfCheckResult::Incomplete,
                    }
                }
                nf_reasons
                    .clone()
                    .expect("invariant: nf_reasons populated above or early-returned Incomplete")
            }};
        }

        // Reverse pass: trim matching suffix components first.
        //
        // CVC5 performs a reverse-direction pre-pass before forward comparison.
        // Trimming shared suffixes up front avoids unnecessary split lemmas on
        // equations like `x ++ "c" = y ++ "c"`.
        let mut rproc = 0usize;
        while rproc < nf1.base.len() && rproc < nf2.base.len() {
            let idx1 = nf1.base.len() - 1 - rproc;
            let idx2 = nf2.base.len() - 1 - rproc;
            if state.find(nf1.base[idx1]) == state.find(nf2.base[idx2]) {
                rproc += 1;
            } else {
                break;
            }
        }

        let len1 = nf1.base.len().saturating_sub(rproc);
        let len2 = nf2.base.len().saturating_sub(rproc);

        let mut i = 0usize;
        let mut j = 0usize;
        let mut off1 = 0usize; // char offset into current nf1 constant
        let mut off2 = 0usize; // char offset into current nf2 constant

        while i < len1 && j < len2 {
            let c1 = nf1.base[i];
            let c2 = nf2.base[j];
            let r1 = state.find(c1);
            let r2 = state.find(c2);

            // Case 2: Same EQC representative and no partial offsets → advance.
            if r1 == r2 && off1 == 0 && off2 == 0 {
                i += 1;
                j += 1;
                continue;
            }

            let s1 = Self::component_constant_owned(terms, state, c1);
            let s2 = Self::component_constant_owned(terms, state, c2);

            match (&s1, &s2) {
                (Some(cs1), Some(cs2)) => {
                    // Case 5: Both constants — compare remaining characters.
                    let chars1: Vec<char> = cs1.chars().skip(off1).collect();
                    let chars2: Vec<char> = cs2.chars().skip(off2).collect();

                    let common_chars = chars1
                        .iter()
                        .zip(chars2.iter())
                        .take_while(|(a, b)| a == b)
                        .count();

                    let len1 = chars1.len();
                    let len2 = chars2.len();

                    if common_chars < len1 && common_chars < len2 {
                        // Characters diverge — conflict.
                        // One-sided explanations are sound for direct
                        // constant-vs-constant mismatches (the asserted
                        // equality literal itself witnesses the contradiction),
                        // but not for metadata-only constant resolution.
                        let allow_one_sided = Self::get_string_constant(terms, c1).is_some()
                            && Self::get_string_constant(terms, c2).is_some();
                        let Some(explanation) = Self::build_pair_explanation_strict(
                            terms,
                            nf1,
                            nf2,
                            state,
                            allow_one_sided,
                        ) else {
                            return NfCheckResult::Incomplete;
                        };
                        if *DEBUG_STRING_CORE {
                            eprintln!(
                                "[STRING_CORE] Case5 conflict: c1={c1:?} c2={c2:?} expl({}):",
                                explanation.len(),
                            );
                            for (k, lit) in explanation.iter().enumerate() {
                                eprintln!(
                                    "  expl[{k}]: {:?} [{:?}] val={}",
                                    lit.term,
                                    terms.get(lit.term),
                                    lit.value
                                );
                            }
                            eprintln!("  NF1 deps: {:?}", nf1.deps);
                            eprintln!("  NF2 deps: {:?}", nf2.deps);
                        }
                        // When both NF components are actual string constants
                        // (not variables resolved through EQC), this is a ground
                        // conflict — the constants directly disagree. Use
                        // ConstantConflict so the SLIA adapter trusts it (#6275).
                        let kind = if allow_one_sided {
                            InferenceKind::ConstantConflict
                        } else {
                            InferenceKind::ConstantSplit
                        };
                        infer.add_conflict(kind, explanation);
                        return NfCheckResult::Conflict;
                    }

                    if common_chars == len1 && common_chars == len2 {
                        i += 1;
                        j += 1;
                        off1 = 0;
                        off2 = 0;
                    } else if common_chars == len1 {
                        i += 1;
                        off1 = 0;
                        off2 += common_chars;
                    } else {
                        j += 1;
                        off2 = 0;
                        off1 += common_chars;
                    }
                }
                _ if off1 == 0 && off2 == 0 => {
                    // Case 3b (N_UNIFY): At least one side is a variable.
                    // If both components have equal lengths, infer c1 = c2 and
                    // assert it in the next internal fact-processing round.
                    //
                    // CVC5 reference: core_solver.cpp:1331
                    //   if (areEqual(len_x, len_y)) { ... sendInference(x == y) }
                    if Self::are_lengths_equal_with_entail(terms, state, c1, c2) {
                        if *DEBUG_STRING_CORE {
                            eprintln!(
                                "[STRING_CORE] process_simple_neq: N_UNIFY c1={c1:?} c2={c2:?}"
                            );
                        }
                        // Lengths are equal — add an internal equality fact.
                        // Use build_pair_explanation_for_lemma to get a guarded
                        // explanation. If the explanation is empty, skip the
                        // internal equality to avoid poisoning the proof forest
                        // with unjustified merges (#6273).
                        let Some(mut explanation) =
                            Self::build_pair_explanation_for_lemma(terms, nf1, nf2, state)
                        else {
                            return NfCheckResult::Incomplete;
                        };
                        // Closure 2 (`--str-nf`, sub-flag 2): the derived
                        // equality depends on len(c1) = len(c2) — include the
                        // guarding length literals so backtracking the length
                        // decision retracts the merge justification too.
                        // Reason-free entailments (pure ArithEntail) keep the
                        // pre-closure explanation.
                        if crate::str_nf_closure_enabled(2) {
                            if let Some(len_reasons) =
                                Self::length_equality_reasons(terms, state, c1, c2)
                            {
                                let mut seen: HashSet<TheoryLit> =
                                    explanation.iter().copied().collect();
                                Self::extend_dedup(&mut explanation, &mut seen, len_reasons);
                            }
                        }
                        infer.add_internal_equality(InferenceKind::Unify, c1, c2, explanation);
                        return NfCheckResult::Incomplete;
                    }
                    // Closure 2 (`--str-nf`, sub-flag 2): prefix
                    // component-transfer N_UNIFY. When one component has an
                    // entailed concrete length and the other decomposes (via
                    // an EQC concat, reduced webs included) into an
                    // entailed-empty prefix plus a leading sub-component of
                    // the SAME entailed length, both are the same-length
                    // prefix of equal remainders ⇒ unify them. This is the
                    // inference that closes nested substr/at skolem webs
                    // (the pyex zz core) without enumerating length splits.
                    if crate::str_nf_closure_enabled(2) {
                        if let Some((x, y, transfer_reasons)) =
                            Self::find_component_transfer(terms, state, c1, c2)
                        {
                            let Some(mut explanation) =
                                Self::build_pair_explanation_for_lemma(terms, nf1, nf2, state)
                            else {
                                return NfCheckResult::Incomplete;
                            };
                            let mut seen: HashSet<TheoryLit> =
                                explanation.iter().copied().collect();
                            Self::extend_dedup(&mut explanation, &mut seen, transfer_reasons);
                            if explanation.is_empty() {
                                // No guards at all — never launder an empty
                                // explanation into the proof forest (#6273).
                                return NfCheckResult::Incomplete;
                            }
                            if *DEBUG_STRING_CORE {
                                eprintln!(
                                    "[STRING_CORE] process_simple_neq: component-transfer N_UNIFY x={x:?} y={y:?} c1={c1:?} c2={c2:?} expl_len={}",
                                    explanation.len()
                                );
                            }
                            infer.add_internal_equality(InferenceKind::Unify, x, y, explanation);
                            return NfCheckResult::Incomplete;
                        }
                    }
                    // Lengths not known equal — determine which split is needed.
                    let s1 = Self::component_constant_owned(terms, state, c1);
                    let s2 = Self::component_constant_owned(terms, state, c2);
                    if *DEBUG_STRING_CORE {
                        eprintln!("[STRING_CORE] process_simple_neq: var branch s1={} s2={} c1={c1:?} c2={c2:?}", s1.is_some(), s2.is_some());
                    }
                    match (&s1, &s2) {
                        (None, None) => {
                            // Both non-constant. Check if lengths are known disequal.
                            if state.are_lengths_disequal(terms, c1, c2) {
                                // Case 9 (SSPLIT_VAR): lengths disequal, emit VarSplit.
                                // `(x = y ++ k) OR (y = x ++ k)` where k is fresh.
                                //
                                // CVC5 reference: core_solver.cpp:1642-1747
                                if !skolems.mark_var_split(c1, c2) {
                                    return NfCheckResult::Incomplete;
                                }
                                let vs_reasons = require_nf_reasons!();
                                if *DEBUG_STRING_CORE {
                                    eprintln!("[STRING_CORE] VarSplit EMIT c1={c1:?} c2={c2:?} reasons({}):", vs_reasons.len());
                                    for (k, lit) in vs_reasons.iter().enumerate() {
                                        eprintln!(
                                            "  vs_reason[{k}]: {:?} [{:?}] val={}",
                                            lit.term,
                                            terms.get(lit.term),
                                            lit.value
                                        );
                                    }
                                }
                                return NfCheckResult::NeedLemma(StringLemma {
                                    kind: StringLemmaKind::VarSplit,
                                    x: c1,
                                    y: c2,
                                    char_offset: 0,
                                    start_offset: 0,
                                    reason: vs_reasons,
                                });
                            }
                            // Case 6: lengths unknown — LengthSplit.
                            return NfCheckResult::NeedLemma(StringLemma {
                                kind: StringLemmaKind::LengthSplit,
                                x: c1,
                                y: c2,
                                char_offset: 0,
                                start_offset: 0,
                                reason: require_nf_reasons!(),
                            });
                        }
                        _ => {
                            // Case 8/9: One or both are constants with non-empty
                            // variable. Emit EmptySplit on the non-constant side
                            // as a prerequisite for ConstSplit.
                            let nc = if s1.is_none() { c1 } else { c2 };
                            let cst_component = if s1.is_some() { c1 } else { c2 };
                            let cst_str = if s1.is_some() { &s1 } else { &s2 };

                            if *DEBUG_STRING_CORE {
                                let kl = state.known_length_full(terms, nc);
                                let kne = state.is_known_nonempty(terms, nc);
                                eprintln!(
                                    "[STRING_CORE] process_simple_neq: _ branch nc={nc:?} cst={cst_component:?} known_len={kl:?} known_nonempty={kne}"
                                );
                            }

                            // Length-aware constant unification (#4055): when the
                            // variable has a known length via the N-O bridge and
                            // that length fits within the constant, emit a
                            // ConstUnify lemma. The CEGAR executor creates the
                            // prefix string constant and asserts the equality in
                            // one step, avoiding character-by-character ConstSplit
                            // that stalls on dual-concat NF comparisons.
                            if let (Some(var_len), Some(cst_val)) =
                                (state.known_length_full(terms, nc), cst_str.as_deref())
                            {
                                let cst_chars: Vec<char> = cst_val.chars().collect();
                                if var_len <= cst_chars.len() {
                                    let Some(cst) = Self::constant_term_for_component(
                                        terms,
                                        state,
                                        cst_component,
                                    ) else {
                                        return NfCheckResult::Incomplete;
                                    };
                                    if *DEBUG_STRING_CORE {
                                        eprintln!("[STRING_CORE] process_simple_neq: ConstUnify nc={nc:?} cst={cst:?} var_len={var_len}");
                                    }
                                    return NfCheckResult::NeedLemma(StringLemma {
                                        kind: StringLemmaKind::ConstUnify,
                                        x: nc,
                                        y: cst,
                                        char_offset: var_len,
                                        start_offset: 0,
                                        reason: require_nf_reasons!(),
                                    });
                                }
                            }

                            if state.is_known_nonempty(terms, nc) {
                                // Non-empty variable vs constant: ConstSplit.
                                let Some(cst) =
                                    Self::constant_term_for_component(terms, state, cst_component)
                                else {
                                    if *DEBUG_STRING_CORE {
                                        eprintln!("[STRING_CORE] process_simple_neq: ConstSplit FAIL no const term nc={nc:?} cst_comp={cst_component:?}");
                                    }
                                    return NfCheckResult::Incomplete;
                                };
                                if !skolems.mark_const_split(nc, cst, 0) {
                                    if *DEBUG_STRING_CORE {
                                        eprintln!("[STRING_CORE] process_simple_neq: ConstSplit DEDUP nc={nc:?} cst={cst:?}");
                                    }
                                    return NfCheckResult::Incomplete;
                                }
                                if *DEBUG_STRING_CORE {
                                    eprintln!("[STRING_CORE] process_simple_neq: ConstSplit EMIT nc={nc:?} cst={cst:?}");
                                }
                                return NfCheckResult::NeedLemma(StringLemma {
                                    kind: StringLemmaKind::ConstSplit,
                                    x: nc,
                                    y: cst,
                                    char_offset: 0,
                                    start_offset: 0,
                                    reason: require_nf_reasons!(),
                                });
                            }
                            // Use SkolemCache to deduplicate: if we already
                            // requested EmptySplit on this variable in this
                            // check round, skip the duplicate and mark incomplete.
                            if !skolems.mark_empty_split(nc) {
                                if *DEBUG_STRING_CORE {
                                    eprintln!("[STRING_CORE] process_simple_neq: EmptySplit DEDUP nc={nc:?}");
                                }
                                return NfCheckResult::Incomplete;
                            }
                            if *DEBUG_STRING_CORE {
                                eprintln!("[STRING_CORE] process_simple_neq: EmptySplit nc={nc:?}");
                            }
                            return NfCheckResult::NeedLemma(StringLemma {
                                kind: StringLemmaKind::EmptySplit,
                                x: nc,
                                y: nc,
                                char_offset: 0,
                                start_offset: 0,
                                reason: vec![],
                            });
                        }
                    }
                }
                _ => {
                    // Variable component with partial offset into a constant.
                    //
                    // Scenario: NF1 = ["ab", x], NF2 = ["abc"]. After consuming
                    // "ab" from "abc", we have off2=2 into "abc" (remaining "c")
                    // and x at off1=0 (or vice versa). The variable must match
                    // the remaining portion of the constant.
                    //
                    // Identify the variable (no constant) side. If it has zero
                    // offset, apply the same EmptySplit/ConstSplit logic as
                    // Cases 8/9.
                    //
                    // CVC5 reference: core_solver.cpp:1514-1639 (SSPLIT_CST)
                    let (nc, cst_component, cst_off, cst_is_last) = match (&s1, &s2) {
                        (None, Some(_)) if off1 == 0 => {
                            // nc = c1 (variable in nf1), constant = c2 in nf2 at
                            // index j. The constant is the last consumable piece
                            // of nf2 iff every component after index j (within the
                            // reverse-trimmed length len2) is the empty string.
                            let is_last = nf2.base[j + 1..len2]
                                .iter()
                                .all(|&t| state.is_empty_string(terms, t));
                            (c1, c2, off2, is_last)
                        }
                        (Some(_), None) if off2 == 0 => {
                            // nc = c2 (variable in nf2), constant = c1 in nf1 at
                            // index i. Symmetric last-component check on nf1.
                            let is_last = nf1.base[i + 1..len1]
                                .iter()
                                .all(|&t| state.is_empty_string(terms, t));
                            (c2, c1, off1, is_last)
                        }
                        _ => {
                            // Both have offsets or both are variables — too complex.
                            return NfCheckResult::Incomplete;
                        }
                    };

                    let Some(cst) = Self::constant_term_for_component(terms, state, cst_component)
                    else {
                        // The component is known-constant only via EQC metadata, but we
                        // need the concrete constant term ID for ConstSplit lowering.
                        return NfCheckResult::Incomplete;
                    };

                    // Length-aware ConstUnify in partial-offset context (#4055):
                    // if the variable has a known length via the N-O bridge and
                    // that length fits within the remaining constant portion,
                    // emit ConstUnify to unify in one step instead of splitting
                    // one character at a time (which diverges on dual-concat NFs).
                    let cst_str_val = Self::component_constant_owned(terms, state, cst_component);
                    if let Some(var_len) = state.known_length_full(terms, nc) {
                        if let Some(ref cst_val) = cst_str_val {
                            let remaining_chars: Vec<char> =
                                cst_val.chars().skip(cst_off).collect();
                            if var_len > remaining_chars.len() {
                                // The variable is longer than what remains of THIS
                                // constant component. This is only a conflict when
                                // the constant component is the last consumable
                                // piece of its normal form: otherwise the variable
                                // legitimately spans into the following components
                                // (e.g. NF1=[x], NF2=["ab","cd"] with len(x)=3 —
                                // x="abc" is fine). Soundness bug #4817: previously
                                // this always conflicted, refuting satisfiable word
                                // equations like the woorpje track05 benchmark
                                // (C="ed",E="ca" in z3). When the constant is not
                                // last, fall through to the ConstSplit/EmptySplit
                                // decomposition below, which advances correctly.
                                if cst_is_last {
                                    let allow_one_sided = true;
                                    let Some(explanation) = Self::build_pair_explanation_strict(
                                        terms,
                                        nf1,
                                        nf2,
                                        state,
                                        allow_one_sided,
                                    ) else {
                                        return NfCheckResult::Incomplete;
                                    };
                                    infer.add_conflict(InferenceKind::ConstantSplit, explanation);
                                    return NfCheckResult::Conflict;
                                }
                                // Not last — do not ConstUnify (var_len does not fit
                                // this component) and do not conflict. Fall through.
                            } else {
                                // var_len <= remaining_chars.len(): the variable
                                // fits within this constant component, so unify in
                                // one step. The variable equals the *substring*
                                // y[cst_off..cst_off+var_len] — the constant has
                                // already been partially consumed by a preceding
                                // component, so start_offset carries cst_off so the
                                // executor extracts the right slice (#4055 fix: the
                                // prefix-only encoding mis-assigned later components,
                                // e.g. y="ab" instead of y="b" on `x++y="ab"`).
                                return NfCheckResult::NeedLemma(StringLemma {
                                    kind: StringLemmaKind::ConstUnify,
                                    x: nc,
                                    y: cst,
                                    char_offset: cst_off + var_len,
                                    start_offset: cst_off,
                                    reason: require_nf_reasons!(),
                                });
                            }
                        }
                    }

                    // The constant side has a partial offset, so remaining chars
                    // are non-empty. This means the variable must also be non-empty
                    // (the constant side is definitely consuming from the same NF
                    // comparison, and it has remaining characters).
                    //
                    // But we still need to check: is the variable known non-empty?
                    if state.is_known_nonempty(terms, nc) {
                        // Non-empty variable vs constant with offset: ConstSplit.
                        // Pass char_offset so the executor extracts the correct
                        // character from the constant (skipping already-consumed
                        // prefix characters).
                        if !skolems.mark_const_split(nc, cst, cst_off) {
                            return NfCheckResult::Incomplete;
                        }
                        return NfCheckResult::NeedLemma(StringLemma {
                            kind: StringLemmaKind::ConstSplit,
                            x: nc,
                            y: cst,
                            char_offset: cst_off,
                            start_offset: 0,
                            reason: require_nf_reasons!(),
                        });
                    }
                    // Variable emptiness unknown: EmptySplit first.
                    if !skolems.mark_empty_split(nc) {
                        return NfCheckResult::Incomplete;
                    }
                    return NfCheckResult::NeedLemma(StringLemma {
                        kind: StringLemmaKind::EmptySplit,
                        x: nc,
                        y: nc,
                        char_offset: 0,
                        start_offset: 0,
                        reason: vec![],
                    });
                }
            }
        }

        // Case 0: Both exhausted in the forward prefix after reverse trimming.
        if i == len1 && j == len2 && off1 == 0 && off2 == 0 {
            return NfCheckResult::Ok;
        }

        // Partial-offset conflict: a constant component has remaining
        // characters but the other side's NF is fully exhausted. Those
        // characters cannot match anything — this is a direct conflict.
        //
        // Example: NF1 = ["abc"], NF2 = ["ab"]. After matching the shared
        // "ab" prefix, off1=2 into "abc" (remaining "c") and j >= len2.
        // The "c" has nothing to match → conflict.
        //
        // This is distinct from the endpoint-eq case (#4055, #3826) where
        // remaining *variable* components are inferred empty. Here the
        // remaining characters are concrete constant data.
        if (off1 > 0 && j >= len2) || (off2 > 0 && i >= len1) {
            let allow_one_sided = true; // constants match directly
            let Some(explanation) =
                Self::build_pair_explanation_strict(terms, nf1, nf2, state, allow_one_sided)
            else {
                return NfCheckResult::Incomplete;
            };
            infer.add_conflict(InferenceKind::ConstantSplit, explanation);
            return NfCheckResult::Conflict;
        }

        // Case 4 (N_ENDPOINT_EQ): One side exhausted, other has remaining
        // components. If no partial offset, infer each remaining component
        // equals the empty string.
        //
        // CVC5 reference: core_solver.cpp:1680-1720
        //   for remaining components: sendInference(y_i == "")
        let remaining = if i < len1 {
            &nf1.base[i..len1]
        } else {
            &nf2.base[j..len2]
        };

        let all_empty = remaining.iter().all(|&t| state.is_empty_string(terms, t));
        if all_empty {
            return NfCheckResult::Ok;
        }

        // Infer each remaining component = "" via internal equality.
        //
        // CVC5 reference: core_solver.cpp:1270-1286 (N_ENDPOINT_EMP)
        // CVC5 never immediately declares conflict when remaining components
        // are non-empty. Instead, it infers each remaining component = ""
        // and lets the equality engine detect contradictions with correct
        // explanations. Declaring conflict directly here caused false UNSAT
        // when NFs from different concat equations on the same variable
        // had misaligned components due to component-by-component matching
        // that doesn't account for cross-boundary length differences.
        // (#4055, #3826)
        if let Some(empty_id) = state.empty_string_id() {
            // Use guarded explanation to protect proof forest integrity
            // (#6273). For internal equalities, the strict version is needed:
            // if explanation is unavailable, skip the merge to avoid poisoning
            // the proof forest with unjustified equalities.
            let Some(explanation) = Self::build_pair_explanation_for_lemma(terms, nf1, nf2, state)
            else {
                return NfCheckResult::Incomplete;
            };
            if *DEBUG_STRING_CORE {
                eprintln!(
                    "[STRING_CORE] N_ENDPOINT_EQ: remaining {} components, explanation {} lits, nf1_deps={} nf2_deps={}",
                    remaining.len(), explanation.len(), nf1.deps.len(), nf2.deps.len()
                );
                for (di, dep) in nf1.deps.iter().chain(nf2.deps.iter()).enumerate() {
                    let expl = state.explain(dep.lhs, dep.rhs);
                    eprintln!(
                        "[STRING_CORE]   dep[{}]: {:?} -> {:?} (explain_len={}, same_eqc={})",
                        di,
                        dep.lhs,
                        dep.rhs,
                        expl.len(),
                        state.find(dep.lhs) == state.find(dep.rhs)
                    );
                }
            }
            for &component in remaining {
                if !state.is_empty_string(terms, component) {
                    infer.add_internal_equality(
                        InferenceKind::EndpointEq,
                        component,
                        empty_id,
                        explanation.clone(),
                    );
                }
            }
            NfCheckResult::Incomplete
        } else {
            // If empty string hasn't been registered in this scope yet, request an
            // EmptySplit on a remaining component to introduce the branch.
            for &component in remaining {
                if state.is_empty_string(terms, component) {
                    continue;
                }
                if !skolems.mark_empty_split(component) {
                    continue;
                }
                return NfCheckResult::NeedLemma(StringLemma {
                    kind: StringLemmaKind::EmptySplit,
                    x: component,
                    y: component,
                    char_offset: 0,
                    start_offset: 0,
                    reason: vec![],
                });
            }
            NfCheckResult::Incomplete
        }
    }
}
