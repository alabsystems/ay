// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// #8529: Use deterministic hash sets in all builds.
use ay_core::kani_compat::DetHashSet as HashSet;
// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::TermData;
use ay_core::{AletheRule, Proof, ProofId, ProofStep, Symbol, TermId, TermStore, TheoryLemmaKind};

use super::empty_clause::collect_assumptions_and_theory_lemmas;

/// Red zone size for `stacker::maybe_grow` in congruence substitution recursion (#8414).
const CONG_SUBST_STACK_RED_ZONE: usize = 32 * 1024;

/// Stack segment size allocated by stacker for congruence substitution recursion.
const CONG_SUBST_STACK_SIZE: usize = 1024 * 1024;

/// Per-literal bridge instruction for congruence-based empty-clause derivation.
///
/// Used by [`try_derive_empty_via_congruence_bridging`] to record
/// how each theory-lemma literal resolves against the proof assumptions.
pub(crate) enum CongruenceBridge {
    /// Literal resolves directly against assumption at `assumptions[idx]`.
    Direct(usize),
    /// Literal requires an `eq_congruent_pred` step bridging `from → to`
    /// via the equality assumption at `eq_pid`, then resolves with `assumptions[assume_idx]`.
    ViaCongruence {
        assume_idx: usize,
        eq_pid: ProofId,
        from: TermId,
        to: TermId,
    },
}

/// Bridge VarSubst-induced term mismatches via EUF congruence steps.
pub(crate) fn try_derive_empty_via_congruence_bridging(
    terms: &mut TermStore,
    proof: &mut Proof,
) -> bool {
    let (assumptions, theory_lemmas) = collect_assumptions_and_theory_lemmas(proof);
    if assumptions.is_empty() || theory_lemmas.is_empty() {
        return false;
    }

    let equality_assumptions: Vec<(ProofId, TermId, TermId)> = assumptions
        .iter()
        .filter_map(|&(pid, term)| {
            if let TermData::App(Symbol::Named(name), args) = terms.get(term) {
                if name == "=" && args.len() == 2 {
                    return Some((pid, args[0], args[1]));
                }
            }
            None
        })
        .collect();

    if equality_assumptions.is_empty() {
        return false;
    }

    let complements = ComplementIndex::new(terms, &assumptions);
    for (lemma_id, lemma_clause) in &theory_lemmas {
        if let Some(derivation) = try_bridge_lemma_with_congruence(
            terms,
            lemma_clause,
            &complements,
            &equality_assumptions,
        ) {
            apply_congruence_bridged_derivation(
                terms,
                proof,
                *lemma_id,
                lemma_clause,
                &assumptions,
                &derivation,
            );
            return true;
        }
    }

    false
}

/// Which assumption resolves directly with a literal (its complement),
/// indexed once per proof.
///
/// The bridging search asks that question for every theory-lemma literal and
/// again for every equality substitution of it; answering by a linear scan
/// (`find_direct_resolution_assumption`, kept as the test oracle) made the
/// search cost `lemmas x equalities x assumptions`. Each map keeps the FIRST
/// index a term occurs at, which is exactly the index the scan's `position`
/// returns, so every answer — and therefore every derivation the search
/// finds — is unchanged.
struct ComplementIndex {
    /// `a` -> first `i` with `assumptions[i] == a`.
    positive: HashMap<TermId, usize>,
    /// `t` -> first `i` with `assumptions[i] == (not t)`.
    negated: HashMap<TermId, usize>,
}

impl ComplementIndex {
    fn new(terms: &TermStore, assumptions: &[(ProofId, TermId)]) -> Self {
        let mut positive = HashMap::default();
        let mut negated = HashMap::default();
        for (index, &(_, assumption)) in assumptions.iter().enumerate() {
            positive.entry(assumption).or_insert(index);
            if let TermData::Not(inner) = terms.get(assumption) {
                negated.entry(*inner).or_insert(index);
            }
        }
        Self { positive, negated }
    }

    /// The same answer as `find_direct_resolution_assumption(terms, lit, ..)`.
    fn complement_of(&self, terms: &TermStore, lit: TermId) -> Option<usize> {
        match terms.get(lit) {
            TermData::Not(inner) => self.positive.get(inner).copied(),
            _ => self.negated.get(&lit).copied(),
        }
    }
}

/// Every subterm [`substitute_in_term`] descends to inside `term` (through
/// `Not` and application arguments), `term` included, each visited once.
///
/// `substitute_in_term(term, from, to)` returns `term` itself — unchanged and
/// without interning anything — unless `from` is one of these sites, so an
/// equality orientation whose `from` is not a site cannot bridge the literal.
fn substitution_sites(terms: &TermStore, term: TermId) -> HashSet<TermId> {
    let mut sites = HashSet::default();
    let mut pending = vec![term];
    while let Some(current) = pending.pop() {
        if !sites.insert(current) {
            continue;
        }
        match terms.get(current) {
            TermData::Not(inner) => pending.push(*inner),
            TermData::App(_, args) => pending.extend(args.iter().copied()),
            _ => {}
        }
    }
    sites
}

fn try_bridge_lemma_with_congruence(
    terms: &mut TermStore,
    lemma_clause: &[TermId],
    complements: &ComplementIndex,
    equality_assumptions: &[(ProofId, TermId, TermId)],
) -> Option<Vec<CongruenceBridge>> {
    let mut bridges = Vec::with_capacity(lemma_clause.len());
    let mut used_assumptions: HashSet<usize> = HashSet::default();

    for &lit in lemma_clause {
        if let Some(idx) = complements.complement_of(terms, lit) {
            if used_assumptions.insert(idx) {
                bridges.push(CongruenceBridge::Direct(idx));
                continue;
            }
        }

        // Only an equality with a side inside the literal can rewrite it;
        // every other pair was a `substituted == lit` no-op below. Measured on
        // the `nested_query_false_unsat` corpus row: 4,130 unit lemmas x 377
        // equalities x 2 orientations re-walked a literal ~3.1M times and
        // scanned 1,665 assumptions per rewrite, 8-27 s per call inside a 2 s
        // checked-ground probe, to conclude there was no bridge.
        let sites = substitution_sites(terms, lit);
        let mut bridged = false;
        for &(eq_pid, lhs, rhs) in equality_assumptions {
            for &(from, to) in &[(lhs, rhs), (rhs, lhs)] {
                if !sites.contains(&from) {
                    continue;
                }
                let substituted = substitute_in_term(terms, lit, from, to);
                if substituted == lit {
                    continue;
                }
                if let Some(idx) = complements.complement_of(terms, substituted) {
                    if used_assumptions.insert(idx) {
                        bridges.push(CongruenceBridge::ViaCongruence {
                            assume_idx: idx,
                            eq_pid,
                            from,
                            to,
                        });
                        bridged = true;
                        break;
                    }
                }
            }
            if bridged {
                break;
            }
        }
        if !bridged {
            return None;
        }
    }

    Some(bridges)
}

/// Find the assumption index that resolves directly with a lemma literal.
///
/// The linear-scan definition `ComplementIndex::complement_of` must agree
/// with; the search itself uses the index.
#[cfg(test)]
pub(crate) fn find_direct_resolution_assumption(
    terms: &TermStore,
    lit: TermId,
    assumptions: &[(ProofId, TermId)],
) -> Option<usize> {
    let target = if let TermData::Not(inner) = terms.get(lit) {
        *inner
    } else {
        return assumptions
            .iter()
            .position(|&(_, a)| matches!(terms.get(a), TermData::Not(inner) if *inner == lit));
    };
    assumptions.iter().position(|&(_, a)| a == target)
}

/// Substitute one term for another within a composite term.
/// Uses `stacker::maybe_grow` for stack safety on deeply nested terms (#8414).
pub(crate) fn substitute_in_term(
    terms: &mut TermStore,
    term: TermId,
    from: TermId,
    to: TermId,
) -> TermId {
    stacker::maybe_grow(CONG_SUBST_STACK_RED_ZONE, CONG_SUBST_STACK_SIZE, || {
        if term == from {
            return to;
        }
        match terms.get(term).clone() {
            TermData::Not(inner) => {
                let new_inner = substitute_in_term(terms, inner, from, to);
                if new_inner == inner {
                    term
                } else {
                    terms.mk_not(new_inner)
                }
            }
            TermData::App(sym, args) => {
                let mut changed = false;
                let new_args: Vec<TermId> = args
                    .into_iter()
                    .map(|a| {
                        let na = substitute_in_term(terms, a, from, to);
                        changed |= na != a;
                        na
                    })
                    .collect();
                if !changed {
                    term
                } else {
                    terms.mk_app(sym, new_args, terms.sort(term).clone())
                }
            }
            _ => term,
        }
    }) // stacker::maybe_grow
}

/// Build the proof steps for a congruence-bridged derivation.
fn apply_congruence_bridged_derivation(
    terms: &mut TermStore,
    proof: &mut Proof,
    lemma_id: ProofId,
    lemma_clause: &[TermId],
    assumptions: &[(ProofId, TermId)],
    bridges: &[CongruenceBridge],
) {
    let mut current_id = lemma_id;
    let mut current_clause = lemma_clause.to_vec();

    for (lit_idx, bridge) in bridges.iter().enumerate() {
        let lemma_lit = lemma_clause[lit_idx];

        match bridge {
            CongruenceBridge::Direct(assume_idx) => {
                let (assume_id, _) = assumptions[*assume_idx];
                current_clause.retain(|&t| t != lemma_lit);
                current_id = proof.add_step(ProofStep::Step {
                    rule: AletheRule::ThResolution,
                    clause: current_clause.clone(),
                    premises: vec![current_id, assume_id],
                    args: vec![],
                });
            }
            CongruenceBridge::ViaCongruence {
                assume_idx,
                eq_pid,
                from,
                to,
            } => {
                let (assume_id, assume_term) = assumptions[*assume_idx];
                let eq_term = terms.mk_eq(*from, *to);
                let neg_eq = terms.mk_not(eq_term);
                let neg_assume = if let TermData::Not(inner) = terms.get(assume_term) {
                    *inner
                } else {
                    terms.mk_not_raw(assume_term)
                };

                // The unit this bridge must derive is the COMPLEMENT of
                // `lemma_lit`, because the final resolution below removes
                // `lemma_lit` from `current_clause` (#eq-cong-pred-polarity).
                //
                // `find_direct_resolution_assumption` returns the assumption
                // that is the complement of the substituted literal, so with
                // `lemma_lit = P(x)` we hold `assume_term = ¬P(y)` for
                // `y = x[from := to]`, and `neg_assume = P(y)`. Congruence then
                // gives `from = to ∧ ¬P(y) ⟹ ¬P(x)`, i.e. the clause
                // `¬(from = to) ∨ P(y) ∨ ¬P(x)` — note the LAST literal is the
                // complement of `lemma_lit`, not `lemma_lit`.
                //
                // Emitting `lemma_lit` here instead produced
                // `¬(A = B) ∨ (0 ≤ A) ∨ (0 ≤ B)`, which is falsified by
                // `A = B = -1`: an INVALID theory lemma, and a resolution that
                // "removed" a literal against a unit of the same polarity. It
                // went unnoticed while UNSAT publication did not require a
                // checked proof; the mandatory certification gate rejects it,
                // which is what surfaced this.
                let neg_lemma_lit = match terms.get(lemma_lit) {
                    TermData::Not(inner) => *inner,
                    _ => terms.mk_not_raw(lemma_lit),
                };

                // `eq_congruent_pred` is checked positionally: the negated
                // predicate must be second-to-last and the positive one last
                // (`ay-proof/src/checker/euf.rs` validate_euf_congruent_pred).
                // Which of the two predicate literals carries the negation
                // depends on `lemma_lit`'s polarity, so order them by polarity
                // rather than by role. A clause is a set of literals, so this
                // reordering is presentational only — it changes nothing about
                // which literals the resolutions below consume.
                let (pred_neg, pred_pos) = if matches!(terms.get(neg_assume), TermData::Not(_)) {
                    (neg_assume, neg_lemma_lit)
                } else {
                    (neg_lemma_lit, neg_assume)
                };

                let cong_id = match boolean_transport_rule(terms, eq_term, pred_neg, pred_pos) {
                    // The substituted term IS the literal (a Boolean
                    // definition `b ≡ φ` replaced `b` by `φ`), so there is no
                    // predicate application to be congruent over: the step
                    // is Boolean equality transport, `equiv_pos1`/`2`,
                    // which the strict checker validates by shape.
                    Some(rule) => proof.add_step(ProofStep::Step {
                        rule,
                        clause: vec![neg_eq, pred_neg, pred_pos],
                        premises: Vec::new(),
                        args: Vec::new(),
                    }),
                    None => proof.add_step(ProofStep::TheoryLemma {
                        theory: "eq_congruent_pred".to_string(),
                        clause: vec![neg_eq, pred_neg, pred_pos],
                        farkas: None,
                        kind: TheoryLemmaKind::EufCongruentPred,
                        lia: None,
                    }),
                };

                let after_eq_id = proof.add_step(ProofStep::Step {
                    rule: AletheRule::ThResolution,
                    clause: vec![neg_assume, neg_lemma_lit],
                    premises: vec![cong_id, *eq_pid],
                    args: vec![],
                });

                let unit_id = proof.add_step(ProofStep::Step {
                    rule: AletheRule::ThResolution,
                    clause: vec![neg_lemma_lit],
                    premises: vec![after_eq_id, assume_id],
                    args: vec![],
                });

                current_clause.retain(|&t| t != lemma_lit);
                current_id = proof.add_step(ProofStep::Step {
                    rule: AletheRule::ThResolution,
                    clause: current_clause.clone(),
                    premises: vec![current_id, unit_id],
                    args: vec![],
                });
            }
        }
    }

    debug_assert!(
        current_clause.is_empty(),
        "congruence-bridged derivation did not derive empty clause"
    );
}

#[cfg(test)]
#[path = "congruence_tests.rs"]
mod tests;

/// The Alethe rule deriving `(cl (not (= a0 a1)) l1 l2)` by Boolean equality
/// transport, when `{l1, l2}` is exactly `{a0, (not a1)}` (`equiv_pos1`) or
/// `{(not a0), a1}` (`equiv_pos2`) over a Boolean equality `(= a0 a1)`.
///
/// `None` for every other shape, including a genuine congruence over a
/// predicate application, which keeps its `eq_congruent_pred` lemma.
fn boolean_transport_rule(
    terms: &TermStore,
    eq_term: TermId,
    l1: TermId,
    l2: TermId,
) -> Option<AletheRule> {
    let TermData::App(symbol, args) = terms.get(eq_term) else {
        return None;
    };
    if symbol.name() != "=" || args.len() != 2 || *terms.sort(args[0]) != ay_core::Sort::Bool {
        return None;
    }
    let (a0, a1) = (args[0], args[1]);
    let negates = |lit: TermId, atom: TermId| {
        matches!(terms.get(lit), TermData::Not(inner) if *inner == atom)
            || matches!(terms.get(atom), TermData::Not(inner) if *inner == lit)
    };
    let pair = |positive: TermId, negated: TermId| {
        (l1 == positive && negates(l2, negated)) || (l2 == positive && negates(l1, negated))
    };
    if pair(a0, a1) {
        Some(AletheRule::EquivPos1)
    } else if pair(a1, a0) {
        Some(AletheRule::EquivPos2)
    } else {
        None
    }
}
