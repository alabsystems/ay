// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::term::{Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};

use super::arithmetic::{is_lia_relevant_term, is_lra_relevant_term};
use super::interface_terms::involves_uninterpreted_function;

/// If `term` is an equality `(= a b)` (excluding Boolean equality), return `(a, b)`.
pub(crate) fn decode_non_bool_eq(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
            let lhs = args[0];
            let rhs = args[1];
            if terms.sort(lhs) == &Sort::Bool && terms.sort(rhs) == &Sort::Bool {
                return None;
            }
            Some((lhs, rhs))
        }
        _ => None,
    }
}

/// If `term` is an `and` with exactly two non-Boolean equalities, return the two eq terms.
pub(super) fn decode_and_two_eqs(
    terms: &TermStore,
    term: TermId,
) -> Option<((TermId, TermId), (TermId, TermId))> {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) if name == "and" && args.len() == 2 => {
            let eq1 = decode_non_bool_eq(terms, args[0])?;
            let eq2 = decode_non_bool_eq(terms, args[1])?;
            Some((eq1, eq2))
        }
        _ => None,
    }
}

/// If two equalities form a length-2 chain `a=b` and `b=c`, return `(a, c)` (canonical order).
pub(super) fn chain_endpoints(
    eq1: (TermId, TermId),
    eq2: (TermId, TermId),
) -> Option<(TermId, TermId)> {
    let terms = [eq1.0, eq1.1, eq2.0, eq2.1];
    let mut uniq: [TermId; 4] = [terms[0], terms[0], terms[0], terms[0]];
    let mut counts: [u8; 4] = [0, 0, 0, 0];
    let mut uniq_len: usize = 0;

    for t in terms {
        let found = uniq[..uniq_len].iter().position(|&u| u == t);
        if let Some(i) = found {
            counts[i] = counts[i].saturating_add(1);
        } else {
            uniq[uniq_len] = t;
            counts[uniq_len] = 1;
            uniq_len += 1;
        }
    }

    if uniq_len != 3 {
        return None;
    }

    let mut endpoints: [TermId; 2] = [TermId(0), TermId(0)];
    let mut end_len = 0;
    for i in 0..uniq_len {
        if counts[i] == 1 {
            if end_len >= 2 {
                return None;
            }
            endpoints[end_len] = uniq[i];
            end_len += 1;
        } else if counts[i] != 2 {
            return None;
        }
    }
    if end_len != 2 {
        return None;
    }

    let [a, b] = endpoints;
    #[allow(clippy::tuple_array_conversions)]
    if a <= b {
        Some((a, b))
    } else {
        Some((b, a))
    }
}

/// Check if a literal is an Int-sorted equality involving UF subterms.
pub(crate) fn is_uf_int_equality(terms: &TermStore, literal: TermId) -> Option<(TermId, TermId)> {
    let inner = match terms.get(literal) {
        TermData::Not(inner) => *inner,
        _ => literal,
    };
    let (lhs, rhs) = decode_non_bool_eq(terms, inner)?;

    if !matches!(terms.sort(lhs), Sort::Int) || !matches!(terms.sort(rhs), Sort::Int) {
        return None;
    }
    if is_lia_relevant_term(terms, lhs) && is_lia_relevant_term(terms, rhs) {
        return None;
    }

    let lhs_has_uf = involves_uninterpreted_function(terms, lhs);
    let rhs_has_uf = involves_uninterpreted_function(terms, rhs);
    if !lhs_has_uf && !rhs_has_uf {
        return None;
    }

    Some((lhs, rhs))
}

/// INTERFACE-DIET withhold predicate (C1/C2): a "pure UF=UF" Int equality is
/// one where BOTH sides are Int-sorted and NEITHER side is LIA-relevant — i.e.
/// both are opaque uninterpreted applications (datatype selectors, `logic_sum`,
/// tuple-gets), NOT an Int constant / Int variable / linear-arithmetic term.
///
/// These are exactly the `(= selector selector)` dual-vocabulary equalities
/// that flood the LIA Nelson-Oppen interface (avg ~880 shared eqs / result on
/// the rusthorn base-SAT wall). `UF=const`, `UF=var`, and `UF=linear` all have
/// one LIA-relevant side, so they stay eager (bridge const-propagation intact);
/// disequalities are handled at the call site (always eager).
pub(crate) fn is_pure_uf_uf_int_equality(terms: &TermStore, lhs: TermId, rhs: TermId) -> bool {
    matches!(terms.sort(lhs), Sort::Int)
        && matches!(terms.sort(rhs), Sort::Int)
        && !is_lia_relevant_term(terms, lhs)
        && !is_lia_relevant_term(terms, rhs)
}

/// Detect Real-sorted equalities involving uninterpreted functions (#5050).
pub(crate) fn is_uf_real_equality(terms: &TermStore, literal: TermId) -> Option<(TermId, TermId)> {
    let inner = match terms.get(literal) {
        TermData::Not(inner) => *inner,
        _ => literal,
    };
    let (lhs, rhs) = decode_non_bool_eq(terms, inner)?;

    if !matches!(terms.sort(lhs), Sort::Real) || !matches!(terms.sort(rhs), Sort::Real) {
        return None;
    }
    if is_lra_relevant_term(terms, lhs) && is_lra_relevant_term(terms, rhs) {
        return None;
    }

    let lhs_has_uf = involves_uninterpreted_function(terms, lhs);
    let rhs_has_uf = involves_uninterpreted_function(terms, rhs);
    if !lhs_has_uf && !rhs_has_uf {
        return None;
    }

    Some((lhs, rhs))
}

/// Detect Real-sorted equalities where at least one side is `select` (#5109).
pub(crate) fn is_select_real_equality(
    terms: &TermStore,
    literal: TermId,
) -> Option<(TermId, TermId)> {
    let inner = match terms.get(literal) {
        TermData::Not(inner) => *inner,
        _ => literal,
    };
    let (lhs, rhs) = decode_non_bool_eq(terms, inner)?;
    if !matches!(terms.sort(lhs), Sort::Real) || !matches!(terms.sort(rhs), Sort::Real) {
        return None;
    }
    let is_select =
        |t: TermId| matches!(terms.get(t), TermData::App(Symbol::Named(n), _) if n == "select");
    if is_select(lhs) || is_select(rhs) {
        Some((lhs, rhs))
    } else {
        None
    }
}

/// A Bool-argument congruence lemma: two UF applications `app_a` and `app_b`
/// that share the same function symbol, arity, and result sort, are identical
/// in every non-Bool argument position, and differ in one-or-more Bool argument
/// positions. The lemma asserts
/// `(/\_i bool_pairs[i].0 = bool_pairs[i].1) -> (app_a = app_b)`,
/// i.e. when all differing Bool args agree in truth value, the applications are
/// congruent. `bool_pairs` lists the differing Bool-arg term pairs. (#bool-arg-congruence)
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct BoolArgCongruenceLemma {
    pub app_a: TermId,
    pub app_b: TermId,
    pub bool_pairs: Vec<(TermId, TermId)>,
}

/// Enumerate Bool-argument congruence lemmas over all UF applications in `terms`.
///
/// For every pair of UF applications with the same (symbol, arity, result sort)
/// that are syntactically identical in all non-Bool argument positions and
/// differ in at least one Bool-sorted position, emit a `BoolArgCongruenceLemma`.
/// These are valid functional-congruence axiom instances: a UF `f` applied to
/// Bool arguments must agree whenever the arguments share a truth value.
///
/// The non-Bool positions must match *syntactically* (same `TermId`). Semantic
/// equality of non-Bool positions is already handled by the EUF congruence
/// closure itself; the gap this closes is purely the Bool-valued positions,
/// whose truth values would otherwise never be reasoned about by the SAT layer
/// when the args appear only inside opaque UF applications.
///
/// Grouping by a structural key keeps this `O(group_size^2)` within each group
/// rather than `O(apps^2)` overall.
pub(crate) fn collect_bool_arg_congruence_lemmas(
    terms: &TermStore,
    reachable: &ay_core::kani_compat::DetHashSet<TermId>,
) -> Vec<BoolArgCongruenceLemma> {
    use ay_core::kani_compat::DetHashMap as HashMap;

    // Group applications by (symbol-name, arity, result-sort, non-Bool-arg
    // signature). Within a group every member has identical non-Bool args; only
    // the Bool-arg positions can differ.
    //
    // Only consider applications reachable from the current assertion set. The
    // TermStore is append-only across incremental check-sats; without this
    // filter the collector re-processes every dead term from popped scopes on
    // each call, turning the per-check-sat cost quadratic in the accumulated
    // (not the live) term count. (#bool-arg-congruence)
    let mut groups: HashMap<(String, usize, Sort, Vec<TermId>), Vec<TermId>> = HashMap::default();

    // Iterate the reachable set (live terms only) rather than the full
    // append-only store. On deep incremental files the store accumulates ~100k
    // dead terms from popped scopes; scanning `0..terms.len()` every check-sat
    // is the dominant cost. Sort for deterministic grouping/lemma order.
    let mut reachable_sorted: Vec<TermId> = reachable.iter().copied().collect();
    reachable_sorted.sort_unstable();
    // NOTE: we intentionally do NOT restrict to "directly compared" or
    // "surfaced" apps — congruence propagates through nesting (e.g.
    // `f(fb(a))` vs `f(fb(b))`), so every reachable UF application with a Bool
    // arg is a lemma candidate. Cost is bounded by the star topology below and
    // by gating injection to non-incremental mode at the call site.
    for term_id in reachable_sorted {
        let TermData::App(Symbol::Named(name), args) = terms.get(term_id) else {
            continue;
        };
        // Skip Boolean connectives / builtins — only genuine UF applications take
        // Bool arguments opaquely.
        match name.as_str() {
            "and" | "or" | "xor" | "=>" | "not" | "=" | "distinct" | "ite" => continue,
            _ => {}
        }
        if args.is_empty() {
            continue;
        }
        // Must have at least one Bool-sorted argument to be relevant.
        let has_bool_arg = args.iter().any(|&a| terms.sort(a) == &Sort::Bool);
        if !has_bool_arg {
            continue;
        }
        // Signature: the non-Bool args in order (these must match syntactically
        // for two apps to be congruent-modulo-Bool-args here).
        let non_bool_sig: Vec<TermId> = args
            .iter()
            .copied()
            .filter(|&a| terms.sort(a) != &Sort::Bool)
            .collect();
        let key = (
            name.to_string(),
            args.len(),
            terms.sort(term_id).clone(),
            non_bool_sig,
        );
        groups.entry(key).or_default().push(term_id);
    }

    // Deterministic group ordering.
    let mut group_keys: Vec<_> = groups.keys().cloned().collect();
    group_keys.sort();

    let mut lemmas = Vec::new();
    for key in group_keys {
        let members = &groups[&key];
        if members.len() < 2 {
            continue;
        }
        // Pairwise over the group (members are in ascending TermId order because
        // the scan above is ascending).
        //
        // STAR (not all-pairs) topology: pair every member against a single
        // fixed representative (`members[0]`) rather than enumerating all
        // O(n^2) pairs. This yields O(n) lemmas per group. It is congruence-
        // COMPLETE because the lemmas surface every member's Bool-arg equality
        // atom `(a_i = a_rep)` to the SAT solver; once those atoms are decided,
        // EUF's native equality-atom congruence closure (already sound and
        // complete) derives every transitive consequence (e.g. `a_i = a_j` via
        // `a_i = a_rep = a_j`, merging `f(a_i)` and `f(a_j)`). The all-pairs
        // form injected up to ~1540 redundant clauses per check-sat on dense
        // CLEARSY groups, timing out files that the star form solves in seconds.
        let rep = members[0];
        let TermData::App(_, args_rep) = terms.get(rep) else {
            continue;
        };
        for &member in &members[1..] {
            let TermData::App(_, args_m) = terms.get(member) else {
                continue;
            };
            // Collect the differing Bool-arg positions between rep and member.
            let mut bool_pairs: Vec<(TermId, TermId)> = Vec::new();
            let mut ok = true;
            for pos in 0..args_rep.len() {
                let a = args_rep[pos];
                let b = args_m[pos];
                if a == b {
                    continue;
                }
                if terms.sort(a) == &Sort::Bool && terms.sort(b) == &Sort::Bool {
                    bool_pairs.push((a, b));
                } else {
                    // A non-Bool position differs — the structural key should
                    // have prevented this, but guard defensively.
                    ok = false;
                    break;
                }
            }
            if ok && !bool_pairs.is_empty() {
                lemmas.push(BoolArgCongruenceLemma {
                    app_a: rep,
                    app_b: member,
                    bool_pairs,
                });
            }
        }
    }
    lemmas
}

/// Detect the EUF transitivity pattern.
pub(crate) fn or_implies_eq_endpoints(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    let TermData::App(Symbol::Named(name), or_args) = terms.get(term) else {
        return None;
    };
    if name != "or" || or_args.len() != 2 {
        return None;
    }

    let (a1, a2) = decode_and_two_eqs(terms, or_args[0])?;
    let (b1, b2) = decode_and_two_eqs(terms, or_args[1])?;

    let e1 = chain_endpoints(a1, a2)?;
    let e2 = chain_endpoints(b1, b2)?;

    if e1 == e2 {
        Some(e1)
    } else {
        None
    }
}
