// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded single-theory core search inside a mixed theory conflict
//! (#combined-theory-decompose), and the sort-gated presence cache the
//! classifier chain consults while it runs.
//!
//! Extracted from `theory_inference/mod.rs` for file-size hygiene, together
//! with the necessary-condition gate described on
//! [`AttemptFeasibility`].

use ay_core::{Sort, TermId, TermStore, TheoryLemmaKind, TheoryLit};

use super::{classify_whole_conflict_gated, decode_eq, HashMap, HashSet};

/// How many literals the core search may drop from a mixed conflict.
///
/// The mixed conflicts observed in practice carry a small number of foreign
/// literals (sampled shapes: a datatype-tester core plus one or two equalities,
/// a set/array core plus a select). Three covers those while keeping the search
/// small; the attempt cap below is the real bound.
pub(super) const DECOMPOSE_MAX_DROPPED: usize = 3;

/// Hard cap on classifier invocations per conflict, so a wide conflict cannot
/// turn proof production into a combinatorial search.
pub(super) const DECOMPOSE_MAX_ATTEMPTS: usize = 512;

/// Which sort-gated recognizers in the chain can possibly fire.
///
/// `recognize_string_ground_eval`, `recognize_fp_ground_eval` and
/// `recognize_regex_intersect_empty` each open with a hygiene gate — "does this
/// clause mention any String/RegLan term", "…any FloatingPoint term" —
/// implemented as a full walk of the clause's term DAG behind a freshly
/// allocated visited-set. On a problem in neither theory the walk runs to
/// completion and returns `false`, every time. `recognize_array_theory_lemma`
/// has no such published gate at all and walks its fourteen schemas instead.
///
/// That is invisible at one call per conflict and dominant at 512 (see
/// [`DECOMPOSE_MAX_ATTEMPTS`]): profiled on the #7956 AUFLIA ext_eq refutation
/// — no strings, no floats — the two original gates were 8.9% of runtime EACH,
/// ~18% together, entirely inside [`classifiable_core_decomposition`].
///
/// Deciding the gates once per conflict is exact, not an approximation. Every
/// sub-clause the decomposition builds is a SUBSET of `clause`, so the terms
/// reachable from it are a subset of those reachable from `clause`; if no
/// String/RegLan (resp. FloatingPoint, Array) term is reachable from the whole
/// clause, none is reachable from any sub-clause, and the skipped recognizer
/// would have returned `false` anyway. No conflict changes lemma kind, so no
/// verdict and no proof artifact changes — only the work does.
///
/// Every gate is computed LAZILY, and that is load-bearing rather than tidy:
/// the chain is ordered cheap-first, and a conflict classified by EUF or Farkas
/// never reached the later arms before this change. Computing the presence
/// eagerly would have paid the walk on exactly the conflicts that used to skip
/// it — turning a saving into a tax on the common path.
pub(super) struct SortedTheoryPresence<'a> {
    terms: &'a TermStore,
    clause: &'a [TermId],
    string_or_regex: std::cell::OnceCell<bool>,
    floating_point: std::cell::OnceCell<bool>,
    array: std::cell::OnceCell<bool>,
}

impl<'a> SortedTheoryPresence<'a> {
    /// Presence over the WHOLE conflict clause. Sub-clauses of `clause` share
    /// this instance; see the type docs for why that is exact.
    pub(super) fn over(terms: &'a TermStore, clause: &'a [TermId]) -> Self {
        Self {
            terms,
            clause,
            string_or_regex: std::cell::OnceCell::new(),
            floating_point: std::cell::OnceCell::new(),
            array: std::cell::OnceCell::new(),
        }
    }

    /// Delegates to the recognizers' OWN gate predicates, so the fast path and
    /// the strict validator cannot drift apart.
    pub(super) fn string_or_regex(&self) -> bool {
        *self
            .string_or_regex
            .get_or_init(|| ay_proof::clause_mentions_string_or_regex(self.terms, self.clause))
    }

    pub(super) fn floating_point(&self) -> bool {
        *self
            .floating_point
            .get_or_init(|| ay_proof::clause_mentions_floating_point(self.terms, self.clause))
    }

    /// Whether any term reachable from the clause carries an array sort.
    ///
    /// `ay-proof` publishes `clause_mentions_*` predicates for the string and
    /// floating-point gates but none for arrays, so the walk is stated here.
    /// It is a NECESSARY condition for every schema
    /// `ay_proof::recognize_array_theory_lemma` accepts: each is stated over a
    /// `select`, a `store`, an `(as const …)` fill, or an equality between two
    /// array-sorted terms, and each of those makes an Array-sorted term
    /// reachable from the clause — `select`'s first argument, the `store`/const
    /// application itself, and both sides of the equality respectively. Pinned
    /// by `array_recognizers_all_decline_without_an_array_sorted_term`.
    pub(super) fn array(&self) -> bool {
        *self.array.get_or_init(|| {
            let mut stack: Vec<TermId> = self.clause.to_vec();
            let mut visited: HashSet<TermId> = HashSet::default();
            while let Some(term) = stack.pop() {
                if !visited.insert(term) {
                    continue;
                }
                if matches!(self.terms.sort(term), Sort::Array(_)) {
                    return true;
                }
                stack.extend(self.terms.children(term));
            }
            false
        })
    }
}

/// Which subsets the bounded core search actually classifies.
///
/// `Gated` is production. `Exhaustive` is the pre-#4751 behaviour, retained so
/// `core_search_tests` can decide the two modes agree rather than assert it;
/// it is `cfg(test)` so production cannot select it.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum SubsetSearch {
    Gated,
    #[cfg(test)]
    Exhaustive,
}

/// Per-literal facts the feasibility gate reads, computed ONCE per conflict.
struct LiteralAdmissibility {
    /// `conflict[i].term` decodes as a binary `=` application.
    equality: Vec<bool>,
    /// `conflict[i]` is a shape SOME arithmetic route could consume.
    arith_shaped: Vec<bool>,
    non_equalities: usize,
    non_arith: usize,
}

impl LiteralAdmissibility {
    fn over(terms: &TermStore, conflict: &[TheoryLit]) -> Self {
        let equality: Vec<bool> = conflict
            .iter()
            .map(|lit| decode_eq(terms, lit.term).is_some())
            .collect();
        let arith_shaped: Vec<bool> = conflict
            .iter()
            .map(|lit| literal_is_arith_shaped(terms, lit.term))
            .collect();
        let non_equalities = equality.iter().filter(|is_eq| !**is_eq).count();
        let non_arith = arith_shaped.iter().filter(|is_arith| !**is_arith).count();
        Self {
            equality,
            arith_shaped,
            non_equalities,
            non_arith,
        }
    }
}

/// Whether the literal is a shape SOME arithmetic route could consume — a
/// binary comparison or equality whose operands are Int/Real-sorted.
///
/// Both routes in `infer_arith_farkas` are per-literal `.all(..)` predicates
/// over exactly this alphabet, and each is NARROWER than it:
/// `conflict_all_arith_literals` -> `is_la_generic_eligible_literal` takes only
/// `<`/`<=`/`>`/`>=` over pure-LA operands, and `opaque_arith_farkas_valid`
/// takes those plus an ASSERTED `=`. One literal outside the union therefore
/// refuses the whole clause under either route.
fn literal_is_arith_shaped(terms: &TermStore, term: TermId) -> bool {
    let atom = super::strip_not(terms, term);
    match terms.get(atom) {
        ay_core::TermData::App(ay_core::Symbol::Named(name), args) if args.len() == 2 => {
            matches!(name.as_str(), "<" | "<=" | ">" | ">=" | "=")
                && matches!(terms.sort(args[0]), Sort::Int | Sort::Real)
                && matches!(terms.sort(args[1]), Sort::Int | Sort::Real)
        }
        _ => false,
    }
}

/// A NECESSARY condition for the classifier chain to accept one sub-clause.
///
/// `classify_whole_conflict_gated` is a fixed chain of arms, and every arm
/// refuses a clause outright unless the clause satisfies a property this gate
/// can decide from facts computed once per conflict. Returning `false` means NO
/// arm can accept, so running the chain is guaranteed to return `None`; the
/// attempt is skipped and the answer is unchanged. Returning `true` runs the
/// chain exactly as before.
///
/// Arm by arm, with the line each condition comes from:
///
/// * `euf::infer_euf_lemma`. `infer_euf_congruent` and `infer_euf_transitive`
///   open `let _ = decode_eq(terms, lit.term)?;` over EVERY literal, so they
///   need zero non-equalities. `infer_euf_congruent_pred` sorts each literal
///   into `premise_eqs` (an equality) or `pred_lits` (Bool-sorted) and refuses
///   `pred_lits.len() != 2`, so it needs exactly two. Hence
///   `kept_non_equalities ∈ {0, 2}`.
/// * `infer_arith_diseq_split_lemma` opens `if clause.len() != 3 { return None }`.
/// * `infer_arith_farkas`: every kept literal must be arith-shaped, see
///   [`literal_is_arith_shaped`].
/// * `infer_array_lemma`, `infer_string_ground_eval_lemma`,
///   `infer_regex_intersect_empty_lemma`, `infer_fp_ground_eval_lemma`: the
///   sort-gated arms, decided by [`SortedTheoryPresence`] over the WHOLE
///   clause, which is a superset of every sub-clause.
/// * The datatype arm receives `None` from this search by construction (see the
///   call below), so it can never fire here.
///
/// A STRONGER arithmetic condition was built and REJECTED on measurement, and
/// the negative is recorded so it is not rebuilt: a model of `pool ∖ {i}` is a
/// model of every pool this search reaches by dropping a set containing `i`
/// (dropping more literals only weakens the conjunction), so
/// `blocking_clause_negation_has_verified_model` decides the whole arithmetic
/// arm for every such drop set with ONE probe per literal. It is exact, and it
/// prunes 18-22% of the attempts on dillig12_m — and the search still measured
/// 877.8ms -> 983.4ms (unguarded: 553.7ms -> 621.1ms) at comparable load,
/// because one `ay_lra` feasibility solve over the pool costs several hundred µs
/// against ~124µs for the classifier attempt it replaces. Same-binary A/B,
/// three runs per arm.
struct AttemptFeasibility<'a> {
    admissibility: LiteralAdmissibility,
    present: &'a SortedTheoryPresence<'a>,
}

impl AttemptFeasibility<'_> {
    fn attempt_may_classify(&self, clause: &[TermId], drop_idx: &[usize]) -> bool {
        let dropped_non_equalities = drop_idx
            .iter()
            .filter(|&&idx| !self.admissibility.equality[idx])
            .count();
        let kept_non_equalities = self
            .admissibility
            .non_equalities
            .saturating_sub(dropped_non_equalities);
        if kept_non_equalities == 0 || kept_non_equalities == 2 {
            return true;
        }
        if clause.len() - drop_idx.len() == 3 {
            return true;
        }
        let dropped_non_arith = drop_idx
            .iter()
            .filter(|&&idx| !self.admissibility.arith_shaped[idx])
            .count();
        if dropped_non_arith == self.admissibility.non_arith {
            return true;
        }
        self.present.array() || self.present.string_or_regex() || self.present.floating_point()
    }
}

/// Find a single-theory core inside a mixed conflict (#combined-theory-decompose).
///
/// Returns `(kind, core_clause, full_clause)` where `core_clause` is the
/// classifier's own ordering of the core literals and `full_clause` is the
/// complete blocking clause with `core_clause` as a PREFIX — the exact shape
/// `weakening` requires (`ay-proof` `validate_weakening`: the premise clause
/// must be a prefix of the result).
///
/// Soundness: the emitted core lemma is checked by its own kind's validator, and
/// weakening a valid clause by appending literals preserves validity. The full
/// clause is literal-for-literal the same SET the caller would have emitted as
/// `Generic`, so nothing downstream sees a different fact — only a checkable
/// justification for it.
pub(super) fn classifiable_core_decomposition(
    terms: &TermStore,
    negations: &HashMap<TermId, TermId>,
    conflict: &[TheoryLit],
    clause: &[TermId],
) -> Option<(TheoryLemmaKind, Vec<TermId>, Vec<TermId>)> {
    classifiable_core_decomposition_with(terms, negations, conflict, clause, SubsetSearch::Gated)
}

/// Turn one classified sub-conflict into the full weakened clause, or decline it.
///
/// The ACCEPTANCE half of the bounded core search: the driver in
/// [`classifiable_core_decomposition_with`] chooses WHICH literals to drop,
/// and this decides whether the core the classifier handed back may be
/// recorded at all. `None` means KEEP SEARCHING — every rejection here is a
/// reason to try the next combination and never a reason to abort, which is
/// why both reject paths simply fall out to the caller's `advance_combination`
/// exactly as they did when this was inline.
fn accept_decomposed_core(
    kind: TheoryLemmaKind,
    core_clause: Vec<TermId>,
    clause: &[TermId],
) -> Option<(TheoryLemmaKind, Vec<TermId>, Vec<TermId>)> {
    // (#ground-conflict-decomp) The weakened recorder
    // (`add_theory_lemma_weakened` -> `add_theory_lemma_with_kind`)
    // carries no LIA evidence, so a `LiaGeneric` core downgrades
    // to a Generic trust CORE step there — and that is actively
    // wrong: the integer gate classifies any all-integer
    // sub-conflict WITHOUT semantic verification, so a
    // manufactured core can be standalone-INVALID (measured: the
    // guard-dropped `(cl (<= sk 0) (<= 2 sk))`, falsified at
    // sk=1, recorded as trust). Refuse exactly that kind; the
    // search continues, and an unclassifiable conflict falls back
    // to the full-clause Generic exactly as before. `LraFarkas`
    // cores are deliberately KEPT: the linear verifier accepted
    // their certificate over the sub-conflict at classification
    // time, so the recorded core is verified-valid (baseline
    // behavior, and refusing them measurably regressed the
    // un-guarded array-frame certification).
    // Covered by `--no-ground-conflict-decomp` (off = baseline).
    if matches!(kind, TheoryLemmaKind::LiaGeneric)
        && crate::quant_unit_authority::ground_conflict_decomp_enabled()
    {
        return None;
    }
    // The classifier may reorder its literals; the core must stay a
    // prefix, so rebuild the full clause as core ++ dropped.
    let core_set: HashSet<TermId> = core_clause.iter().copied().collect();
    if core_set.len() == core_clause.len() {
        let mut full_clause = core_clause.clone();
        for &lit in clause {
            if !core_set.contains(&lit) {
                full_clause.push(lit);
            }
        }
        // Only accept when the weakened clause still covers the
        // original blocking clause exactly. A malformed candidate
        // must not abort the bounded search: a later subset can
        // still expose an unambiguous core.
        let full_set: HashSet<TermId> = full_clause.iter().copied().collect();
        let orig_set: HashSet<TermId> = clause.iter().copied().collect();
        if full_set == orig_set {
            return Some((kind, core_clause, full_clause));
        }
    }
    None
}

pub(super) fn classifiable_core_decomposition_with(
    terms: &TermStore,
    negations: &HashMap<TermId, TermId>,
    conflict: &[TheoryLit],
    clause: &[TermId],
    search: SubsetSearch,
) -> Option<(TheoryLemmaKind, Vec<TermId>, Vec<TermId>)> {
    if conflict.len() != clause.len() || conflict.len() < 2 {
        return None;
    }

    let mut attempts = 0usize;
    let max_dropped = DECOMPOSE_MAX_DROPPED.min(conflict.len().saturating_sub(1));
    // Share each lazy theory-presence walk across the bounded core search.
    let present = SortedTheoryPresence::over(terms, clause);
    let feasibility = AttemptFeasibility {
        admissibility: LiteralAdmissibility::over(terms, conflict),
        present: &present,
    };

    // Prefer the LARGEST core: dropping fewer literals keeps more of the
    // conflict inside the checked lemma.
    for dropped in 1..=max_dropped {
        let mut drop_idx = (0..dropped).collect::<Vec<usize>>();
        loop {
            if attempts >= DECOMPOSE_MAX_ATTEMPTS {
                return None;
            }
            // The attempt is CONSUMED whether or not the chain runs, so the cap
            // binds on exactly the same subset it always did and the gate
            // cannot make a previously-capped core reachable.
            attempts += 1;

            let feasible = match search {
                SubsetSearch::Gated => feasibility.attempt_may_classify(clause, &drop_idx),
                #[cfg(test)]
                SubsetSearch::Exhaustive => true,
            };
            if !feasible {
                if !advance_combination(&mut drop_idx, conflict.len()) {
                    break;
                }
                continue;
            }

            let keep: Vec<usize> = (0..conflict.len())
                .filter(|i| !drop_idx.contains(i))
                .collect();
            let sub_conflict: Vec<TheoryLit> = keep.iter().map(|&i| conflict[i]).collect();
            let sub_clause: Vec<TermId> = keep.iter().map(|&i| clause[i]).collect();

            if let Some((kind, core_clause)) = classify_whole_conflict_gated(
                terms,
                negations,
                &sub_conflict,
                &sub_clause,
                &present,
                // Sub-clause core search: skip the DT lane — running the
                // ground refuter up to DECOMPOSE_MAX_ATTEMPTS times per
                // conflict is the wrong cost model, and the whole-conflict
                // pass above already probed it.
                None,
            ) {
                if let Some(found) = accept_decomposed_core(kind, core_clause, clause) {
                    return Some(found);
                }
            }

            // Next combination of dropped indices (lexicographic). Exhausting
            // this cardinality continues the outer loop so cores that require
            // dropping two or three foreign literals are still considered.
            if !advance_combination(&mut drop_idx, conflict.len()) {
                break;
            }
        }
    }
    None
}

fn advance_combination(indices: &mut [usize], universe_len: usize) -> bool {
    let selected = indices.len();
    for position in (0..selected).rev() {
        let Some(max_index) = universe_len.checked_sub(selected - position) else {
            return false;
        };
        if indices[position] < max_index {
            indices[position] += 1;
            for later in position + 1..selected {
                indices[later] = indices[later - 1] + 1;
            }
            return true;
        }
    }
    false
}

#[cfg(test)]
#[path = "core_search_tests.rs"]
mod core_search_tests;
