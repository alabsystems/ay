// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! EUF strict proof validation for Alethe step rules.

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

/// Strip `Not` wrappers and return (inner_term, is_negated).
fn strip_not(terms: &TermStore, mut term: TermId) -> (TermId, bool) {
    let mut negated = false;
    while let TermData::Not(inner) = terms.get(term) {
        term = *inner;
        negated = !negated;
    }
    (term, negated)
}

/// Validate the `refl` rule: `(cl (= t t))`.
///
/// The clause must contain exactly one literal, a positive equality with
/// identical left and right sides.
pub(crate) fn validate_refl(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    if clause.len() != 1 {
        return Err(ProofCheckError::InvalidBooleanRule {
            step: step_id,
            rule: "refl".to_string(),
            reason: format!(
                "refl clause must have exactly 1 literal, got {}",
                clause.len()
            ),
        });
    }
    let (inner, negated) = strip_not(terms, clause[0]);
    if negated {
        return Err(ProofCheckError::InvalidBooleanRule {
            step: step_id,
            rule: "refl".to_string(),
            reason: "refl literal must be a positive equality".to_string(),
        });
    }
    let (lhs, rhs) =
        decode_eq(terms, inner).ok_or_else(|| ProofCheckError::InvalidBooleanRule {
            step: step_id,
            rule: "refl".to_string(),
            reason: "refl literal is not an equality".to_string(),
        })?;
    if lhs != rhs {
        return Err(ProofCheckError::InvalidBooleanRule {
            step: step_id,
            rule: "refl".to_string(),
            reason: "refl: equality sides are not identical".to_string(),
        });
    }
    Ok(())
}

/// Validate the `symm` rule: premise `(= a b)` → conclusion `(= b a)`.
///
/// Takes a single premise clause containing one equality literal and produces
/// a clause with that equality reversed.
pub(crate) fn validate_symm(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    premise_clauses: &[&[TermId]],
) -> Result<(), ProofCheckError> {
    if premise_clauses.len() != 1 {
        return Err(ProofCheckError::InvalidBooleanRule {
            step: step_id,
            rule: "symm".to_string(),
            reason: format!(
                "symm requires exactly 1 premise, got {}",
                premise_clauses.len()
            ),
        });
    }
    if clause.len() != 1 {
        return Err(ProofCheckError::InvalidBooleanRule {
            step: step_id,
            rule: "symm".to_string(),
            reason: format!(
                "symm clause must have exactly 1 literal, got {}",
                clause.len()
            ),
        });
    }
    let premise = premise_clauses[0];
    if premise.len() != 1 {
        return Err(ProofCheckError::InvalidBooleanRule {
            step: step_id,
            rule: "symm".to_string(),
            reason: format!(
                "symm premise must have exactly 1 literal, got {}",
                premise.len()
            ),
        });
    }

    let (prem_inner, prem_neg) = strip_not(terms, premise[0]);
    let (a, b) =
        decode_eq(terms, prem_inner).ok_or_else(|| ProofCheckError::InvalidBooleanRule {
            step: step_id,
            rule: "symm".to_string(),
            reason: "symm premise is not an equality".to_string(),
        })?;

    let (conc_inner, conc_neg) = strip_not(terms, clause[0]);
    if conc_neg != prem_neg {
        return Err(ProofCheckError::InvalidBooleanRule {
            step: step_id,
            rule: "symm".to_string(),
            reason: "symm: premise and conclusion polarity must match".to_string(),
        });
    }
    let (c, d) =
        decode_eq(terms, conc_inner).ok_or_else(|| ProofCheckError::InvalidBooleanRule {
            step: step_id,
            rule: "symm".to_string(),
            reason: "symm conclusion is not an equality".to_string(),
        })?;

    if c != b || d != a {
        return Err(ProofCheckError::InvalidBooleanRule {
            step: step_id,
            rule: "symm".to_string(),
            reason: "symm: conclusion is not the reverse of the premise equality".to_string(),
        });
    }
    Ok(())
}

/// Validate the `trans` rule: premises `(= a b)`, `(= b c)` → conclusion `(= a c)`.
///
/// In general, takes n premises forming a transitivity chain and produces a
/// single equality connecting the chain endpoints.
pub(crate) fn validate_trans(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    premise_clauses: &[&[TermId]],
) -> Result<(), ProofCheckError> {
    if premise_clauses.len() < 2 {
        return Err(ProofCheckError::InvalidBooleanRule {
            step: step_id,
            rule: "trans".to_string(),
            reason: format!(
                "trans requires at least 2 premises, got {}",
                premise_clauses.len()
            ),
        });
    }
    if clause.len() != 1 {
        return Err(ProofCheckError::InvalidBooleanRule {
            step: step_id,
            rule: "trans".to_string(),
            reason: format!(
                "trans clause must have exactly 1 literal, got {}",
                clause.len()
            ),
        });
    }

    let (conc_inner, conc_neg) = strip_not(terms, clause[0]);
    if conc_neg {
        return Err(ProofCheckError::InvalidBooleanRule {
            step: step_id,
            rule: "trans".to_string(),
            reason: "trans conclusion must be a positive equality".to_string(),
        });
    }
    let (goal_lhs, goal_rhs) =
        decode_eq(terms, conc_inner).ok_or_else(|| ProofCheckError::InvalidBooleanRule {
            step: step_id,
            rule: "trans".to_string(),
            reason: "trans conclusion is not an equality".to_string(),
        })?;

    let mut edges: Vec<(TermId, TermId)> = Vec::with_capacity(premise_clauses.len());
    for (i, prem) in premise_clauses.iter().enumerate() {
        if prem.len() != 1 {
            return Err(ProofCheckError::InvalidBooleanRule {
                step: step_id,
                rule: "trans".to_string(),
                reason: format!(
                    "trans premise {i} must have exactly 1 literal, got {}",
                    prem.len()
                ),
            });
        }
        let (inner, negated) = strip_not(terms, prem[0]);
        if negated {
            return Err(ProofCheckError::InvalidBooleanRule {
                step: step_id,
                rule: "trans".to_string(),
                reason: format!("trans premise {i} must be a positive equality"),
            });
        }
        let (a, b) =
            decode_eq(terms, inner).ok_or_else(|| ProofCheckError::InvalidBooleanRule {
                step: step_id,
                rule: "trans".to_string(),
                reason: format!("trans premise {i} is not an equality"),
            })?;
        edges.push((a, b));
    }

    let num_edges = edges.len();
    let mut adj: HashMap<TermId, Vec<(TermId, usize)>> = HashMap::default();
    for (i, &(a, b)) in edges.iter().enumerate() {
        adj.entry(a).or_default().push((b, i));
        adj.entry(b).or_default().push((a, i));
    }

    let mut parent: HashMap<TermId, (TermId, usize)> = HashMap::default();
    parent.insert(goal_lhs, (goal_lhs, usize::MAX));
    let mut queue: VecDeque<TermId> = VecDeque::new();
    queue.push_back(goal_lhs);

    while let Some(current) = queue.pop_front() {
        if current == goal_rhs {
            break;
        }
        if let Some(neighbors) = adj.get(&current) {
            for &(next, edge_idx) in neighbors {
                if !parent.contains_key(&next) {
                    parent.insert(next, (current, edge_idx));
                    queue.push_back(next);
                }
            }
        }
    }

    if !parent.contains_key(&goal_rhs) {
        return Err(ProofCheckError::InvalidBooleanRule {
            step: step_id,
            rule: "trans".to_string(),
            reason: "trans: premises do not form a chain from lhs to rhs".to_string(),
        });
    }

    let mut path_len = 0usize;
    let mut curr = goal_rhs;
    while curr != goal_lhs {
        let (prev, _) = parent[&curr];
        path_len += 1;
        curr = prev;
    }

    if path_len != num_edges {
        return Err(ProofCheckError::InvalidBooleanRule {
            step: step_id,
            rule: "trans".to_string(),
            reason: format!(
                "trans: {} of {} premises are redundant",
                num_edges - path_len,
                num_edges
            ),
        });
    }

    Ok(())
}

/// Validate the `cong` rule: premises `(= a1 b1) ... (= an bn)` →
/// conclusion `(= (f a1..an) (f b1..bn))`.
///
/// Same structure as EufCongruent but appears as a Step rule, not a TheoryLemma.
pub(crate) fn validate_cong(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    premise_clauses: &[&[TermId]],
) -> Result<(), ProofCheckError> {
    if clause.len() != 1 {
        return Err(ProofCheckError::InvalidBooleanRule {
            step: step_id,
            rule: "cong".to_string(),
            reason: format!(
                "cong clause must have exactly 1 literal, got {}",
                clause.len()
            ),
        });
    }

    let (conc_inner, conc_neg) = strip_not(terms, clause[0]);
    if conc_neg {
        return Err(ProofCheckError::InvalidBooleanRule {
            step: step_id,
            rule: "cong".to_string(),
            reason: "cong conclusion must be a positive equality".to_string(),
        });
    }
    let (conc_lhs, conc_rhs) =
        decode_eq(terms, conc_inner).ok_or_else(|| ProofCheckError::InvalidBooleanRule {
            step: step_id,
            rule: "cong".to_string(),
            reason: "cong conclusion is not an equality".to_string(),
        })?;

    #[derive(PartialEq, Eq)]
    enum CongruenceHead {
        App(Symbol),
        Ite,
        Not,
    }
    let application = |term| match terms.get(term) {
        TermData::App(sym, args) => Some((CongruenceHead::App(sym.clone()), args.clone())),
        // `ite` is represented by a dedicated TermData node rather than an
        // App, but it is still an ordinary ternary function for congruence.
        TermData::Ite(condition, then_branch, else_branch) => Some((
            CongruenceHead::Ite,
            vec![*condition, *then_branch, *else_branch],
        )),
        // `not` is likewise a dedicated TermData node rather than an App, and
        // is an ordinary UNARY function for congruence: `a = b` entails
        // `(not a) = (not b)`. Admitting it does not widen what `cong` proves
        // — every argument pair is still discharged by a premise equality
        // below, exactly as for App and Ite heads.
        TermData::Not(inner) => Some((CongruenceHead::Not, vec![*inner])),
        _ => None,
    };
    let (f_sym, f_args) = match application(conc_lhs) {
        Some(application) => application,
        _ => {
            return Err(ProofCheckError::InvalidBooleanRule {
                step: step_id,
                rule: "cong".to_string(),
                reason: "cong: conclusion LHS is not a function application".to_string(),
            });
        }
    };
    let (g_sym, g_args) = match application(conc_rhs) {
        Some(application) => application,
        _ => {
            return Err(ProofCheckError::InvalidBooleanRule {
                step: step_id,
                rule: "cong".to_string(),
                reason: "cong: conclusion RHS is not a function application".to_string(),
            });
        }
    };

    if f_sym != g_sym {
        return Err(ProofCheckError::InvalidBooleanRule {
            step: step_id,
            rule: "cong".to_string(),
            reason: "cong: conclusion sides have different function symbols".to_string(),
        });
    }
    if f_args.len() != g_args.len() {
        return Err(ProofCheckError::InvalidBooleanRule {
            step: step_id,
            rule: "cong".to_string(),
            reason: "cong: conclusion sides have different arities".to_string(),
        });
    }

    let mut premise_eqs: Vec<(TermId, TermId)> = Vec::with_capacity(premise_clauses.len());
    for (i, prem) in premise_clauses.iter().enumerate() {
        if prem.len() != 1 {
            return Err(ProofCheckError::InvalidBooleanRule {
                step: step_id,
                rule: "cong".to_string(),
                reason: format!(
                    "cong premise {i} must have exactly 1 literal, got {}",
                    prem.len()
                ),
            });
        }
        let (inner, negated) = strip_not(terms, prem[0]);
        if negated {
            return Err(ProofCheckError::InvalidBooleanRule {
                step: step_id,
                rule: "cong".to_string(),
                reason: format!("cong premise {i} must be a positive equality"),
            });
        }
        let (a, b) =
            decode_eq(terms, inner).ok_or_else(|| ProofCheckError::InvalidBooleanRule {
                step: step_id,
                rule: "cong".to_string(),
                reason: format!("cong premise {i} is not an equality"),
            })?;
        premise_eqs.push((a, b));
    }

    let mut used_premises = vec![false; premise_eqs.len()];
    for i in 0..f_args.len() {
        if f_args[i] == g_args[i] {
            continue;
        }
        let found = premise_eqs.iter().enumerate().find(|(j, (a, b))| {
            !used_premises[*j]
                && ((*a == f_args[i] && *b == g_args[i]) || (*a == g_args[i] && *b == f_args[i]))
        });
        match found {
            Some((j, _)) => {
                used_premises[j] = true;
            }
            None => {
                return Err(ProofCheckError::InvalidBooleanRule {
                    step: step_id,
                    rule: "cong".to_string(),
                    reason: format!(
                        "cong: argument position {i} differs but no matching premise equality"
                    ),
                });
            }
        }
    }

    Ok(())
}
