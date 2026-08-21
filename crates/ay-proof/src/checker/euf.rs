// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! EUF (Equality with Uninterpreted Functions) strict proof validation.
//!
//! Validates three Alethe rules: `eq_transitive`, `eq_congruent`, `eq_congruent_pred`.
//! EUF lemmas are self-certifying — the clause structure IS the certificate.

// #8529/#8857: Use deterministic hash map for reproducible proof output.
use ay_core::kani_compat::DetHashMap as HashMap;
use std::collections::VecDeque;

use ay_core::{ProofId, Symbol, TermData, TermId, TermStore};

use super::ProofCheckError;

/// Decode a term as an equality `(= lhs rhs)`, returning the two sides.
fn decode_eq(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
            Some((args[0], args[1]))
        }
        _ => None,
    }
}

/// Flatten a single-literal clause whose one literal is an `(or L1 .. Ln)`
/// disjunction into `[L1, .., Ln]`; every other clause is returned unchanged.
///
/// A clause `(cl (or L1 .. Ln))` denotes the SAME disjunction `L1 ∨ .. ∨ Ln`
/// as the flat clause `(cl L1 .. Ln)` — the single-literal packing is a
/// surface-syntax difference, not a semantic one. The lazy-EUF /
/// array-extensionality lanes emit some `eq_transitive` / `eq_congruent`
/// leaves in this packed `(or …)` form; without flattening the validators
/// would reject a genuinely valid tautology purely on its shape. This mirrors
/// `array_axiom::flatten_clause_literals`, and is applied EXACTLY (only when
/// the clause is a single `or` of ≥ 2 disjuncts) so no other clause shape is
/// reinterpreted. All downstream structural checks (chain connectivity,
/// no-redundant-premise, per-argument matching) run on the flattened literals,
/// so soundness is unchanged: the clause certifies iff the flat form does.
fn flatten_or_clause(terms: &TermStore, clause: &[TermId]) -> Vec<TermId> {
    if clause.len() == 1 {
        if let TermData::App(Symbol::Named(sym), args) = terms.get(clause[0]) {
            if sym == "or" && args.len() >= 2 {
                return args.clone();
            }
        }
    }
    clause.to_vec()
}

/// Strip `Not` wrappers and return (inner_term, is_negated).
fn strip_not(terms: &TermStore, mut term: TermId) -> (TermId, bool) {
    let mut negated = false;
    while let TermData::Not(inner) = terms.get(term) {
        term = *inner;
        negated = !negated;
    }
    (term, negated)
}

/// Validate an EUF transitive chain lemma.
///
/// Clause structure: `(not (= a b)) (not (= b c)) ... (= lhs rhs)`
/// - Last literal is a positive equality (conclusion)
/// - All other literals are negated equalities (premises)
/// - The premise equalities must form a path from `lhs` to `rhs`
/// - Every premise must be on the path (no redundant premises)
pub(crate) fn validate_euf_transitive(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    let flattened = flatten_or_clause(terms, clause);
    let clause = flattened.as_slice();
    if clause.len() < 2 {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: "EufTransitive clause must have at least 2 literals".to_string(),
        });
    }

    // Last literal is the positive conclusion equality
    let conclusion = clause[clause.len() - 1];
    let (conc_inner, conc_negated) = strip_not(terms, conclusion);
    if conc_negated {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: "EufTransitive conclusion must be a positive equality".to_string(),
        });
    }
    let (goal_lhs, goal_rhs) =
        decode_eq(terms, conc_inner).ok_or_else(|| ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: "EufTransitive conclusion is not an equality".to_string(),
        })?;

    // All other literals are negated equalities (premises)
    let mut edges: Vec<(TermId, TermId)> = Vec::with_capacity(clause.len() - 1);
    for &lit in &clause[..clause.len() - 1] {
        let (inner, negated) = strip_not(terms, lit);
        if !negated {
            return Err(ProofCheckError::InvalidTheoryLemma {
                step: step_id,
                reason: "EufTransitive premise must be a negated equality".to_string(),
            });
        }
        let (a, b) =
            decode_eq(terms, inner).ok_or_else(|| ProofCheckError::InvalidTheoryLemma {
                step: step_id,
                reason: "EufTransitive premise is not an equality".to_string(),
            })?;
        edges.push((a, b));
    }

    // Build adjacency list: node -> [(neighbor, edge_index)]
    let num_edges = edges.len();
    let mut adj: HashMap<TermId, Vec<(TermId, usize)>> = HashMap::default();
    for (i, &(a, b)) in edges.iter().enumerate() {
        adj.entry(a).or_default().push((b, i));
        adj.entry(b).or_default().push((a, i));
    }

    // BFS from goal_lhs to goal_rhs, recording parent edge for path reconstruction
    let mut parent: HashMap<TermId, (TermId, usize)> = HashMap::default();
    parent.insert(goal_lhs, (goal_lhs, usize::MAX));
    let mut bfs_queue: VecDeque<TermId> = VecDeque::new();
    bfs_queue.push_back(goal_lhs);

    while let Some(current) = bfs_queue.pop_front() {
        if current == goal_rhs {
            break;
        }
        if let Some(neighbors) = adj.get(&current) {
            for &(next, edge_idx) in neighbors {
                if !parent.contains_key(&next) {
                    parent.insert(next, (current, edge_idx));
                    bfs_queue.push_back(next);
                }
            }
        }
    }

    if !parent.contains_key(&goal_rhs) {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: "EufTransitive: premise equalities do not form a chain from lhs to rhs"
                .to_string(),
        });
    }

    // Reconstruct path and count edges actually used
    let mut path_len = 0usize;
    let mut curr = goal_rhs;
    while curr != goal_lhs {
        let (prev, _edge_idx) = parent[&curr];
        path_len += 1;
        curr = prev;
    }

    // Every premise must be on the path (no redundant premises)
    if path_len != num_edges {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: format!(
                "EufTransitive: {} of {} premise equalities are redundant",
                num_edges - path_len,
                num_edges
            ),
        });
    }

    Ok(())
}

/// Validate an EUF congruence lemma.
///
/// Clause structure: `(not (= a1 b1)) ... (not (= an bn)) (= (f a1..an) (f b1..bn))`
/// - Last literal is a positive equality between two applications of the same function
/// - All other literals are negated equalities pairing arguments
pub(crate) fn validate_euf_congruent(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    let flattened = flatten_or_clause(terms, clause);
    let clause = flattened.as_slice();
    if clause.len() < 2 {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: "EufCongruent clause must have at least 2 literals".to_string(),
        });
    }

    // Last literal: positive equality (= (f a1..an) (f b1..bn))
    let conclusion = clause[clause.len() - 1];
    let (conc_inner, conc_negated) = strip_not(terms, conclusion);
    if conc_negated {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: "EufCongruent conclusion must be a positive equality".to_string(),
        });
    }
    let (conc_lhs, conc_rhs) =
        decode_eq(terms, conc_inner).ok_or_else(|| ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: "EufCongruent conclusion is not an equality".to_string(),
        })?;

    // Both sides must be App with the same symbol and arity
    let (f_sym, f_args) = match terms.get(conc_lhs) {
        TermData::App(sym, args) => (sym.clone(), args.clone()),
        _ => {
            return Err(ProofCheckError::InvalidTheoryLemma {
                step: step_id,
                reason: "EufCongruent: conclusion LHS is not a function application".to_string(),
            });
        }
    };
    let (g_sym, g_args) = match terms.get(conc_rhs) {
        TermData::App(sym, args) => (sym.clone(), args.clone()),
        _ => {
            return Err(ProofCheckError::InvalidTheoryLemma {
                step: step_id,
                reason: "EufCongruent: conclusion RHS is not a function application".to_string(),
            });
        }
    };

    if f_sym != g_sym {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: "EufCongruent: conclusion sides have different function symbols".to_string(),
        });
    }
    if f_args.len() != g_args.len() {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: "EufCongruent: conclusion sides have different arities".to_string(),
        });
    }

    // Premise equalities (all literals except the conclusion).
    //
    // Same identical-argument omission as `validate_euf_congruent_pred`
    // directly below, for the same completeness reason: a position whose two
    // terms are the SAME term id needs no premise — `t = t` holds by
    // reflexivity and its disjunct `¬(t = t)` is false, so dropping it
    // preserves validity and cannot admit an invalid lemma. The canonical
    // producer is array extensionality instantiation,
    // `¬(a = e) ∨ (select a d) = (select e d)`, where the index position is
    // shared. Both spellings accepted; every premise must be consumed in
    // argument order, so a spurious or out-of-order premise still rejects.
    validate_euf_congruent_arguments(
        terms,
        step_id,
        &f_args,
        &g_args,
        &clause[..clause.len() - 1],
    )
}

fn validate_euf_congruent_arguments(
    terms: &TermStore,
    step_id: ProofId,
    f_args: &[TermId],
    g_args: &[TermId],
    premises: &[TermId],
) -> Result<(), ProofCheckError> {
    if premises.len() > f_args.len() {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: format!(
                "EufCongruent: {}-ary function admits at most {} premise equalities, got {}",
                f_args.len(),
                f_args.len(),
                premises.len()
            ),
        });
    }

    let mut next_premise = 0usize;
    for i in 0..f_args.len() {
        let consumed = if next_premise < premises.len() {
            let lit = premises[next_premise];
            let (inner, negated) = strip_not(terms, lit);
            if !negated {
                return Err(ProofCheckError::InvalidTheoryLemma {
                    step: step_id,
                    reason: format!(
                        "EufCongruent: premise {next_premise} must be a negated equality"
                    ),
                });
            }
            let (a, b) =
                decode_eq(terms, inner).ok_or_else(|| ProofCheckError::InvalidTheoryLemma {
                    step: step_id,
                    reason: format!("EufCongruent: premise {next_premise} is not an equality"),
                })?;
            let matches = (a == f_args[i] && b == g_args[i]) || (a == g_args[i] && b == f_args[i]);
            if matches {
                next_premise += 1;
            }
            matches
        } else {
            false
        };
        if !consumed && f_args[i] != g_args[i] {
            return Err(ProofCheckError::InvalidTheoryLemma {
                step: step_id,
                reason: format!(
                    "EufCongruent: argument position {i} differs but no premise equality                      connects it"
                ),
            });
        }
    }
    if next_premise != premises.len() {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: "EufCongruent: unconsumed premise equality".to_string(),
        });
    }

    Ok(())
}

/// Recognize the exact EUF congruence clause shape `validate_euf_congruent`
/// accepts (#trust->0 C1.ii): `(not (= a1 b1)) .. (not (= an bn))
/// (= (f a1..an) (f b1..bn))` with a premise per DIFFERING argument position
/// (identical-argument positions may omit theirs, exactly as in
/// `eq_congruent_pred`), also in the packed single-literal `(or …)` form.
///
/// Recognition IS the strict validator run on the clause — classifier and
/// checker cannot drift, and a clause is only classified `EufCongruent` when
/// strict checking is guaranteed to accept it (fail-closed).
#[must_use]
pub fn recognize_euf_congruent(terms: &TermStore, clause: &[TermId]) -> bool {
    validate_euf_congruent(terms, ProofId(0), clause).is_ok()
}

/// Recognize the exact EUF transitive-chain clause shape
/// `validate_euf_transitive` accepts (#trust->0 C3): `(not (= a b))
/// (not (= b c)) .. (= lhs rhs)` — premises forming a chain from `lhs` to
/// `rhs` with no redundant premise, conclusion LAST. Like
/// [`recognize_euf_congruent`], recognition IS the strict validator run on the
/// clause, so classifier and checker cannot drift and the ORDER-SENSITIVE
/// placement of the conclusion is verified on exactly the clause the caller
/// intends to record (fail-closed).
#[must_use]
pub fn recognize_euf_transitive(terms: &TermStore, clause: &[TermId]) -> bool {
    validate_euf_transitive(terms, ProofId(0), clause).is_ok()
}

/// Recognize the exact EUF congruent-predicate clause shape
/// `validate_euf_congruent_pred` accepts (#trust->0 C3): `(not (= a1 b1)) ..
/// (not (= an bn)) (not (p a1..an)) (p b1..bn)` — per-position premise
/// equalities in argument order (identical-argument positions may omit
/// theirs), negated predicate second-to-last, positive predicate LAST.
/// Recognition IS the strict validator (fail-closed, order verified).
#[must_use]
pub fn recognize_euf_congruent_pred(terms: &TermStore, clause: &[TermId]) -> bool {
    validate_euf_congruent_pred(terms, ProofId(0), clause).is_ok()
}

/// Recognize the exact reflexivity clause shape the strict checker's
/// `EufReflexive` arm accepts (#trust->0 C3): a single positive binary
/// equality relating a term to ITSELF. Recognition IS
/// `validate_eq_reflexive` — the same routine backing the `eq_reflexive`
/// Alethe rule and the `TheoryLemmaKind::EufReflexive` dispatch — so
/// classifier and checker cannot drift (fail-closed).
#[must_use]
pub fn recognize_euf_reflexive(terms: &TermStore, clause: &[TermId]) -> bool {
    super::boolean_derived::validate_eq_reflexive(terms, ProofId(0), clause).is_ok()
}

/// Validate an EUF congruent predicate lemma.
///
/// Clause structure: `(not (= a1 b1)) ... (not (= an bn)) (not (p a1..an)) (p b1..bn)`
/// - Last literal: positive predicate application `(p b1..bn)`
/// - Second-to-last: negated predicate application `(not (p a1..an))`
/// - All other literals: negated equalities pairing arguments
pub(crate) fn validate_euf_congruent_pred(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    if clause.len() < 3 {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: "EufCongruentPred clause must have at least 3 literals".to_string(),
        });
    }

    // Last literal: positive predicate application (p b1..bn)
    let pos_pred_lit = clause[clause.len() - 1];
    let (pos_pred_inner, pos_negated) = strip_not(terms, pos_pred_lit);
    if pos_negated {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: "EufCongruentPred: last literal must be a positive predicate".to_string(),
        });
    }

    // Second-to-last: negated predicate application (not (p a1..an))
    let neg_pred_lit = clause[clause.len() - 2];
    let (neg_pred_inner, neg_negated) = strip_not(terms, neg_pred_lit);
    if !neg_negated {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: "EufCongruentPred: second-to-last literal must be a negated predicate"
                .to_string(),
        });
    }

    // Both predicates must be App with same symbol and arity
    let (p_sym, p_args) = match terms.get(neg_pred_inner) {
        TermData::App(sym, args) => (sym.clone(), args.clone()),
        _ => {
            return Err(ProofCheckError::InvalidTheoryLemma {
                step: step_id,
                reason: "EufCongruentPred: negated predicate is not a function application"
                    .to_string(),
            });
        }
    };
    let (q_sym, q_args) = match terms.get(pos_pred_inner) {
        TermData::App(sym, args) => (sym.clone(), args.clone()),
        _ => {
            return Err(ProofCheckError::InvalidTheoryLemma {
                step: step_id,
                reason: "EufCongruentPred: positive predicate is not a function application"
                    .to_string(),
            });
        }
    };

    if p_sym != q_sym {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: "EufCongruentPred: predicate symbols differ".to_string(),
        });
    }
    if p_args.len() != q_args.len() {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: "EufCongruentPred: predicate arities differ".to_string(),
        });
    }

    // Premise equalities (all literals except the last two).
    //
    // An argument position whose two terms are the SAME term id needs no
    // premise: `t = t` holds by reflexivity, and the corresponding disjunct
    // `¬(t = t)` is false, so dropping it from the clause preserves validity.
    // Requiring one anyway rejected valid congruence lemmas over predicates
    // that share a literal argument — e.g. `(<= 0 A)` against `(<= 0 B)`, where
    // only the second position differs. That is a COMPLETENESS gap: accepting a
    // clause with fewer premises, exactly at positions where the arguments are
    // syntactically identical, cannot admit an invalid lemma, because the
    // omitted premise was entailed unconditionally.
    //
    // Both spellings are accepted, so proof producers that do emit the
    // reflexive premise keep validating unchanged: walk the argument positions
    // in order and consume a premise for a position only when the next unused
    // premise actually matches it; a position with no premise must have
    // identical arguments. Every premise must be consumed, so a spurious or
    // out-of-order premise is still rejected.
    let premises = &clause[..clause.len() - 2];
    if premises.len() > p_args.len() {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: format!(
                "EufCongruentPred: {}-ary predicate admits at most {} premise equalities, got {}",
                p_args.len(),
                p_args.len(),
                premises.len()
            ),
        });
    }

    let mut next_premise = 0usize;
    for i in 0..p_args.len() {
        let consumed = if next_premise < premises.len() {
            let lit = premises[next_premise];
            let (inner, negated) = strip_not(terms, lit);
            if !negated {
                return Err(ProofCheckError::InvalidTheoryLemma {
                    step: step_id,
                    reason: format!(
                        "EufCongruentPred: premise {next_premise} must be a negated equality"
                    ),
                });
            }
            let (a, b) =
                decode_eq(terms, inner).ok_or_else(|| ProofCheckError::InvalidTheoryLemma {
                    step: step_id,
                    reason: format!("EufCongruentPred: premise {next_premise} is not an equality"),
                })?;
            let matches = (a == p_args[i] && b == q_args[i]) || (a == q_args[i] && b == p_args[i]);
            if matches {
                next_premise += 1;
            }
            matches
        } else {
            false
        };

        if !consumed && p_args[i] != q_args[i] {
            return Err(ProofCheckError::InvalidTheoryLemma {
                step: step_id,
                reason: format!(
                    "EufCongruentPred: argument position {i} differs but has no premise equality"
                ),
            });
        }
    }

    if next_premise != premises.len() {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: format!(
                "EufCongruentPred: premise {next_premise} does not match any argument position"
            ),
        });
    }

    Ok(())
}

/// Validate `distinct_elim`: the clause is a single equivalence
/// `(= (distinct t1 .. tn) <expansion>)` where the expansion is the pairwise
/// `i < j` disequality conjunction — for `n == 2` the bare `(not (= t1 t2))`,
/// for `n >= 3` `(and (not (= t1 t2)) (not (= t1 t3)) .. (not (= t_{n-1} tn)))`
/// in exactly that order.
pub(crate) fn validate_distinct_elim(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    let fail = |reason: &str| ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason: format!("DistinctElim: {reason}"),
    };
    if clause.len() != 1 {
        return Err(fail("clause must be a single equivalence"));
    }
    let (lhs, rhs) = decode_eq(terms, clause[0]).ok_or_else(|| fail("not an equivalence"))?;
    let xs = match terms.get(lhs) {
        TermData::App(Symbol::Named(name), args) if name == "distinct" && args.len() >= 2 => {
            args.clone()
        }
        _ => return Err(fail("LHS is not an n-ary distinct application")),
    };
    // Collect the expected pairwise conjuncts from the RHS.
    let conjs: Vec<TermId> = if xs.len() == 2 {
        vec![rhs]
    } else {
        match terms.get(rhs) {
            TermData::App(Symbol::Named(name), args) if name == "and" => args.clone(),
            _ => return Err(fail("RHS is not a conjunction")),
        }
    };
    if conjs.len() != xs.len() * (xs.len() - 1) / 2 {
        return Err(fail("wrong number of pairwise disequalities"));
    }
    let mut k = 0usize;
    for i in 0..xs.len() {
        for j in (i + 1)..xs.len() {
            let TermData::Not(inner) = terms.get(conjs[k]) else {
                return Err(fail("expansion conjunct is not a negated equality"));
            };
            let (a, b) = decode_eq(terms, *inner)
                .ok_or_else(|| fail("expansion conjunct is not a negated equality"))?;
            if a != xs[i] || b != xs[j] {
                return Err(fail(
                    "expansion conjunct does not match the i < j pair order",
                ));
            }
            k += 1;
        }
    }
    Ok(())
}

include!("euf/recognizer_tests.rs");
