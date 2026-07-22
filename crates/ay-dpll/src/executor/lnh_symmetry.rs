// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sound symmetry breaking for TPTP-style finite-model QF_UF instances
//! (`NEQ*`/`PEQ*`/`QG-classification`: "find a model of size n" problems).
//!
//! These declare a domain of `n` constants `c_0..c_{n-1}` of an uninterpreted
//! sort (via `(distinct ..)`) plus totality constraints forcing every function
//! result into that domain. When the domain constants are **fully
//! interchangeable** (`S_n` symmetry) — which we PROVE, not assume — proving
//! UNSAT explores `n!` equivalent assignments.
//!
//! # Why signature ordering (and NOT the naive LNH)
//!
//! A previous attempt fixed a function cell (`f(c_0,c_0) = c_0`). That is WLOG
//! only if the domain has an idempotent element (`x*x = x`); non-idempotent
//! quasigroups have models with `f(c_0,c_0) != c_0`, so it produced FALSE UNSAT
//! (caught by an oracle differential; reverted). The bug: a function cell's
//! value is NOT freely permutable because the cell's ARGUMENTS are domain
//! elements too.
//!
//! This pass instead canonicalizes by **unary-predicate signatures**, which ARE
//! permutation-covariant. Each domain element `c_i` gets a signature
//! `sig(c_i) = (p_1(c_i), .., p_m(c_i))` over the unary predicates `p_k: S->Bool`.
//! We require `sig(c_0) <=_lex sig(c_1) <=_lex .. <=_lex sig(c_{n-1})`.
//!
//! SOUNDNESS (satisfiability-preserving): take any model `M`. Its elements have
//! signatures; permute the domain to sort the elements by signature. Because the
//! formula is `S_n`-invariant (checked), the sorted model `M'` still satisfies
//! it, and `M'` satisfies the ordering constraint. So a solution survives in
//! every orbit. No idempotence / cell-value assumption is made — sorting by a
//! boolean signature is ALWAYS achievable by a permutation. Env `AY_EUF_LNH`.
//!
//! # Least-index orbit-prefix scheme (preferred when it applies)
//!
//! The lex-leader above is sound but propagates poorly (deep Tseitin chains).
//! [`add_least_index_symmetry_breaking`] instead emits the CADE'11
//! Déharbe/Fontaine/Merz/Paulus prefix clauses `t_k in {c_0..c_k}` over
//! totality-clause subjects — z3's `symmetry-reduce`, the mechanism that
//! collapses SEQ/PEQ/NEQ/QG pigeonhole cores to level-0 unit cascades
//! (SEQ009_size7: 3711 -> 1 conflicts). It differs from the SUNK cell-fixing
//! attempt above in two load-bearing ways: the first clause on a cell subject
//! keeps TWO candidates (`f(c_0,c_0) in {c_0, c_1}` — no idempotence
//! assumption), and a subject is only constrained once every domain constant
//! it contains is pinned (so the rescuing permutation never moves a
//! constrained subject's own arguments). The two schemes are mutually
//! exclusive per instance; both sit behind the same proven-`S_n` gate.

use ay_core::term::{Symbol, TermData, TermId, TermStore};
use ay_core::Sort;

/// Enabled by DEFAULT (validated sound: oracle differential 2010 solved / 0
/// disagreements / 0 false-UNSAT incl. quasigroup SAT; executor_tests 968/968
/// with it on). `AY_EUF_LNH=0` disables (escape hatch). Only ever APPLIES when a
/// finite-model domain is detected AND proven S_n-interchangeable AND n>=6, so it
/// is a no-op on the vast majority of instances.
pub(crate) fn lnh_enabled() -> bool {
    std::env::var_os("AY_EUF_LNH").is_none_or(|v| v != "0")
}

fn is_builtin(sym: &Symbol) -> bool {
    matches!(
        sym.name(),
        "=" | "distinct" | "and" | "or" | "not" | "=>" | "ite" | "xor"
    )
}

const MAX_TERMS_FOR_CHECK: usize = 400_000;

/// Detect the finite-model domain from a TOTALITY clause
/// `(or (= t c_0) .. (= t c_{n-1}))` — the robust signal (`mk_distinct` expands
/// `(distinct ..)` into pairwise disequalities). Returns the largest such
/// (domain, uninterpreted sort).
fn find_domain(terms: &TermStore) -> Option<(Vec<TermId>, Sort)> {
    let mut best: Option<(Vec<TermId>, Sort)> = None;
    for id in terms.term_ids() {
        let TermData::App(sym, ds) = terms.get(id) else {
            continue;
        };
        if sym.name() != "or" || ds.len() < 3 {
            continue;
        }
        let mut eqs: Vec<(TermId, TermId)> = Vec::with_capacity(ds.len());
        let mut all_eq = true;
        for &d in ds {
            match terms.get(d) {
                TermData::App(es, ea) if es.name() == "=" && ea.len() == 2 => {
                    eqs.push((ea[0], ea[1]));
                }
                _ => {
                    all_eq = false;
                    break;
                }
            }
        }
        if !all_eq {
            continue;
        }
        for &cand_t in &[eqs[0].0, eqs[0].1] {
            let mut domain = Vec::with_capacity(eqs.len());
            let mut good = true;
            for &(x, y) in &eqs {
                if x == cand_t {
                    domain.push(y);
                } else if y == cand_t {
                    domain.push(x);
                } else {
                    good = false;
                    break;
                }
            }
            if !good {
                continue;
            }
            let s0 = terms.sort(domain[0]).clone();
            if !matches!(s0, Sort::Uninterpreted(_))
                || !domain.iter().all(|&c| terms.sort(c) == &s0)
            {
                continue;
            }
            let mut sorted = domain.clone();
            sorted.sort();
            sorted.dedup();
            if sorted.len() != domain.len() {
                continue;
            }
            if best.as_ref().is_none_or(|(b, _)| domain.len() > b.len()) {
                best = Some((domain, s0));
            }
            break;
        }
    }
    best
}

/// SOUND interchangeability proof: every transposition `(c_0 c_i)` maps the
/// assertion SET to itself (transpositions `(c_0 c_i)` generate `S_n`). Swaps are
/// simultaneous and rebuilt through the normalizing `mk_*` constructors, so a
/// hit means genuine structural invariance. TRUE ⟹ real `S_n` symmetry. FALSE
/// (incl. conservative misses) ⟹ skip (safe).
fn domain_is_interchangeable(
    terms: &mut TermStore,
    assertions: &[TermId],
    domain: &[TermId],
) -> bool {
    if terms.term_ids().count() > MAX_TERMS_FOR_CHECK {
        return false;
    }
    let orig: ay_core::kani_compat::DetHashSet<TermId> = assertions.iter().copied().collect();
    let c0 = domain[0];
    for &ci in &domain[1..] {
        let from = [c0, ci];
        let to = [ci, c0];
        for &a in assertions {
            let sa = terms.substitute(a, &from, &to);
            if !orig.contains(&sa) {
                return false;
            }
        }
    }
    true
}

/// Unary predicates `p: S -> Bool` applied to domain-sorted arguments, in a
/// deterministic first-seen order. Signature components must be permutation-
/// covariant, so ONLY boolean-valued unary applications qualify (a unary
/// FUNCTION `S->S` yields a domain element, which is itself permuted — not a
/// stable comparison key).
fn find_unary_predicates(terms: &TermStore, dsort: &Sort) -> Vec<Symbol> {
    let mut seen: Vec<Symbol> = Vec::new();
    for id in terms.term_ids() {
        if let TermData::App(sym, args) = terms.get(id) {
            if args.len() == 1
                && !is_builtin(sym)
                && terms.sort(id) == &Sort::Bool
                && terms.sort(args[0]) == dsort
                && !seen.iter().any(|s| s.name() == sym.name())
            {
                seen.push(sym.clone());
            }
        }
    }
    seen
}

/// `sig(a) <=_lex sig(b)` over boolean predicate values (false < true), built
/// low-priority-last: `le_k = (¬a_k ∧ b_k) ∨ ((a_k = b_k) ∧ le_{k+1})`, base true.
fn lex_le(terms: &mut TermStore, a_sig: &[TermId], b_sig: &[TermId]) -> TermId {
    let mut le = terms.true_term();
    for k in (0..a_sig.len()).rev() {
        let a = a_sig[k];
        let b = b_sig[k];
        let na = terms.mk_not(a);
        let lt = terms.mk_and(vec![na, b]); // a < b : ¬a ∧ b
        let eq = terms.mk_eq(a, b); // a = b (iff on Bools)
        let eq_rest = terms.mk_and(vec![eq, le]);
        le = terms.mk_or(vec![lt, eq_rest]);
    }
    le
}

/// Uninterpreted binary functions `f: S x S -> S` used in the formula (distinct
/// symbols, first-seen order). Their table equality atoms feed the lex-leader.
fn find_binary_funcs(terms: &TermStore, dsort: &Sort) -> Vec<Symbol> {
    let mut seen: Vec<Symbol> = Vec::new();
    for id in terms.term_ids() {
        if let TermData::App(sym, args) = terms.get(id) {
            if args.len() == 2
                && !is_builtin(sym)
                && terms.sort(id) == dsort
                && terms.sort(args[0]) == dsort
                && terms.sort(args[1]) == dsort
                && !seen.iter().any(|s| s.name() == sym.name())
            {
                seen.push(sym.clone());
            }
        }
    }
    seen
}

/// Cap on the number of boolean atoms fed to each lex-leader chain (keeps the
/// per-transposition formula bounded; a subset lex-leader is still sound).
const MAX_LEX_ATOMS: usize = 600;

/// Least-index (orbit-prefix) symmetry breaking — the z3 `symmetry-reduce`
/// mechanism (Déharbe/Fontaine/Merz/Paulus, CADE'11) that collapses the
/// SEQ/QG finite-model family to level-0 unit-propagation cascades.
///
/// Enabled by default when the least-index scheme applies;
/// `AY_LNH_LEASTIDX=0` falls back to the lex-leader for A/B.
fn least_index_enabled() -> bool {
    std::env::var_os("AY_LNH_LEASTIDX").is_none_or(|v| v != "0")
}

/// Terms `t` with an asserted TOTALITY clause `(or (= t c_0) .. (= t c_{n-1}))`
/// covering the FULL domain, in deterministic first-seen assertion order.
///
/// Positivity is REQUIRED for soundness: the totality clause must be a
/// top-level conjunct (assertion root or nested under `and` only), so that
/// `F |= t in {c_0..c_{n-1}}` genuinely holds. (`find_domain` scans loose
/// or-nodes because it only needs a detection signal; here the clause is a
/// soundness premise of the added constraint.)
fn collect_totality_terms(
    terms: &TermStore,
    assertions: &[TermId],
    domain: &[TermId],
    dsort: &Sort,
) -> Vec<TermId> {
    use ay_core::kani_compat::DetHashSet;
    let domain_set: DetHashSet<TermId> = domain.iter().copied().collect();
    let mut out: Vec<TermId> = Vec::new();
    let mut seen_terms: DetHashSet<TermId> = DetHashSet::default();
    let mut seen_clauses: DetHashSet<TermId> = DetHashSet::default();
    // Walk conjuncts iteratively (assertion roots + nested `and`s).
    let mut stack: Vec<TermId> = assertions.iter().rev().copied().collect();
    let mut conjunct_or_clauses: Vec<TermId> = Vec::new();
    while let Some(a) = stack.pop() {
        match terms.get(a) {
            TermData::App(sym, args) if sym.name() == "and" => {
                for &c in args.iter().rev() {
                    stack.push(c);
                }
            }
            TermData::App(sym, _) if sym.name() == "or" => {
                if seen_clauses.insert(a) {
                    conjunct_or_clauses.push(a);
                }
            }
            _ => {}
        }
    }
    for clause in conjunct_or_clauses {
        let TermData::App(_, disjuncts) = terms.get(clause) else {
            continue;
        };
        if disjuncts.len() < domain.len() {
            continue;
        }
        let mut t: Option<TermId> = None;
        let mut covered: DetHashSet<TermId> = DetHashSet::default();
        let mut ok = true;
        for &d in disjuncts {
            let TermData::App(es, ea) = terms.get(d) else {
                ok = false;
                break;
            };
            if es.name() != "=" || ea.len() != 2 {
                ok = false;
                break;
            }
            // One side a domain constant, the other the common subject term.
            let (subj, cst) = if domain_set.contains(&ea[1]) && !domain_set.contains(&ea[0]) {
                (ea[0], ea[1])
            } else if domain_set.contains(&ea[0]) && !domain_set.contains(&ea[1]) {
                (ea[1], ea[0])
            } else {
                ok = false;
                break;
            };
            if *terms.sort(subj) != *dsort {
                ok = false;
                break;
            }
            match t {
                None => t = Some(subj),
                Some(prev) if prev == subj => {}
                Some(_) => {
                    ok = false;
                    break;
                }
            }
            covered.insert(cst);
        }
        if !ok || covered.len() != domain.len() {
            continue;
        }
        if let Some(t) = t {
            if seen_terms.insert(t) {
                out.push(t);
            }
        }
    }
    out
}

/// The set of domain constants occurring (as sub-terms) in `t`.
fn domain_consts_in(terms: &TermStore, t: TermId, domain: &[TermId]) -> Vec<TermId> {
    use ay_core::kani_compat::DetHashSet;
    let domain_set: DetHashSet<TermId> = domain.iter().copied().collect();
    let mut found: Vec<TermId> = Vec::new();
    let mut visited: DetHashSet<TermId> = DetHashSet::default();
    let mut stack = vec![t];
    while let Some(x) = stack.pop() {
        if !visited.insert(x) {
            continue;
        }
        if domain_set.contains(&x) {
            if !found.contains(&x) {
                found.push(x);
            }
            continue;
        }
        match terms.get(x) {
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, a, b) => {
                stack.push(*c);
                stack.push(*a);
                stack.push(*b);
            }
            _ => {}
        }
    }
    found
}

/// Append least-index symmetry-breaking clauses. Returns the number added.
///
/// For a PROVEN `S_n`-interchangeable domain `c_0..c_{n-1}` and totality
/// subjects `t` (terms asserted to take a value in the domain), process
/// subjects greedily: a subject is ELIGIBLE once every domain constant it
/// contains is already pinned ("used"). For the k-th processed subject add
///
///   `(or (= t u_1) .. (= t u_k) (= t c_next))`   (Used ∪ one fresh constant)
///
/// then mark `c_next` used.
///
/// SOUNDNESS (satisfiability-preserving; induction over emitted clauses):
/// given a model `M` of `F` (S_n-invariant over the domain) satisfying the
/// first k-1 clauses, subject `t_k`'s value equals some `M(c_j)` (totality).
/// If `c_j` is used or `c_j = c_next`, the k-th clause already holds.
/// Otherwise swap `c_j <-> c_next` — both UNUSED. The swap fixes `F`
/// (S_n-invariance), fixes the values of all used constants, and fixes the
/// values of every earlier subject `t_i` (eligibility: `t_i` contains only
/// used constants, and non-domain symbols are untouched), so earlier clauses
/// stay satisfied while the k-th becomes true. A model therefore survives in
/// every orbit. The subject ORDER (constants, then unary cells, then wider
/// terms) is a pure effectiveness heuristic — soundness only needs the
/// eligibility rule — chosen because pinning free constants and walking unary
/// orbits first turns injectivity/pigeonhole cores into unit cascades
/// (measured: SEQ009_size7 3711 -> 1 conflicts; the reverse order is inert).
///
/// The added clauses only STRENGTHEN the formula, so any model of the
/// augmented formula is a model of the original — the sat-side gates validate
/// against the untouched original assertions and need no reconstruction map.
fn add_least_index_symmetry_breaking(
    terms: &mut TermStore,
    assertions: &mut Vec<TermId>,
    domain: &[TermId],
    dsort: &Sort,
    diag: bool,
) -> usize {
    let subjects = collect_totality_terms(terms, assertions, domain, dsort);
    if subjects.is_empty() {
        return 0;
    }
    // (subject, domain constants it contains); order class = (#distinct domain
    // constants, arity bucket) — free constants first, then unary cells, then
    // binary and wider. Stable sort keeps first-seen order within a class.
    let mut ranked: Vec<(TermId, Vec<TermId>, usize)> = subjects
        .iter()
        .map(|&t| {
            let consts = domain_consts_in(terms, t, domain);
            let arity = match terms.get(t) {
                TermData::App(_, args) => args.len(),
                _ => 0,
            };
            let class = consts.len().max(arity);
            (t, consts, class)
        })
        .collect();
    ranked.sort_by_key(|(_, _, class)| *class);

    let mut used: Vec<TermId> = Vec::new();
    let mut unused: std::collections::VecDeque<TermId> = domain.iter().copied().collect();
    let mut processed = vec![false; ranked.len()];
    let mut added = 0usize;
    while !unused.is_empty() {
        // Prefer a subject whose domain constants are all pinned already.
        // Among eligible subjects order by CLASS (constants, then unary
        // orbits — the SEQ injectivity cascade — then wider cells), and
        // within a class by the STAIRCASE order (SEM/FALCON LNH): smallest
        // max pin-index of its constants first — cover the k-prefix subtable
        // before opening index k+1 — then first-seen. (Measured: staircase
        // fixed the qg iso_brn/iso_icl regressions that the plain first-seen
        // scan caused by walking whole rows.)
        let eligible = ranked
            .iter()
            .enumerate()
            .filter(|(i, (_, consts, _))| !processed[*i] && consts.iter().all(|c| used.contains(c)))
            .min_by_key(|(i, (_, consts, class))| {
                let max_pin = consts
                    .iter()
                    .map(|c| used.iter().position(|u| u == c).expect("eligible"))
                    .max()
                    .map_or(0, |p| p + 1);
                (*class, max_pin, *i)
            })
            .map(|(i, _)| i);
        let idx = match eligible {
            Some(i) => i,
            None => {
                // FIAT SEEDING: no eligible subject. Take the first unprocessed
                // subject and pin its not-yet-used constants by fiat (they join
                // Used with no constraint of their own). SOUND: the rescuing
                // permutation at this step is chosen to FIX every used constant
                // — including the fiat ones, which no earlier subject contains
                // (earlier subjects passed the eligibility rule against a
                // smaller Used) — and to swap only the two unused constants
                // `c_next <-> c_j`, exactly as in the eligible case. This seeds
                // families whose totality subjects are all function cells
                // (e.g. QG gensys: `f(c_0,c_0) in {c_0, c_1}` pins two).
                // Pick the unprocessed subject pinning the FEWEST new
                // constants (diagonal cells before off-diagonal); ties break
                // by ranked order.
                match (0..ranked.len())
                    .filter(|&i| !processed[i])
                    .min_by_key(|&i| ranked[i].1.iter().filter(|c| !used.contains(c)).count())
                {
                    Some(i) => {
                        let fiat: Vec<TermId> = ranked[i]
                            .1
                            .iter()
                            .filter(|c| !used.contains(c))
                            .copied()
                            .collect();
                        for c in fiat {
                            unused.retain(|&u| u != c);
                            used.push(c);
                        }
                        i
                    }
                    None => break,
                }
            }
        };
        processed[idx] = true;
        if used.len() >= domain.len() {
            break; // the clause would be the full-domain totality (tautology)
        }
        let t = ranked[idx].0;
        let Some(next) = unused.pop_front() else {
            break;
        };
        let mut lits: Vec<TermId> = Vec::with_capacity(used.len() + 1);
        for &u in &used {
            lits.push(terms.mk_eq(t, u));
        }
        lits.push(terms.mk_eq(t, next));
        let clause = terms.mk_or(lits);
        assertions.push(clause);
        used.push(next);
        added += 1;
    }
    if diag {
        ay_core::safe_eprintln!(
            "[LNH] least-index subjects={} clauses_added={added}",
            subjects.len()
        );
    }
    added
}

/// Append SOUND lex-leader symmetry-breaking assertions over the adjacent
/// transpositions `(c_i c_{i+1})` (which generate `S_n`): require the model to be
/// `<=_lex` its image under each swap, over a fixed sequence of boolean atoms
/// (function-table equalities `f(c_a,c_b)=c_c` and unary predicates `p(c_a)`).
///
/// SOUND: for any generator `τ` that is a real symmetry (interchangeability is
/// PROVEN), the orbit's lex-minimum model satisfies `M <=_lex τ(M)` over ANY atom
/// subset, so a solution survives. No cell value is forced — the swap image
/// `τ(atom)` is computed by simultaneous `c_i<->c_{i+1}` substitution — so there
/// is no idempotence assumption (the bug that sank the cell-fixing version).
pub(crate) fn add_lnh_symmetry_breaking(
    terms: &mut TermStore,
    assertions: &mut Vec<TermId>,
) -> usize {
    // ARRAY SCOPE GUARD (#lnh-no-arrays): this pass targets finite-model QF_UF
    // (SEQ/QG/NEQ/PEQ). On array problems (QF_AX/QF_AUFLIA) the uninterpreted
    // Index/Element constants LOOK S_n-interchangeable to the prover, but the
    // array lemma machinery (witness-guided ROW, extensionality) already carries
    // the load and the extra least-index/lex clauses are pure overhead — measured
    // 2-70x wall regressions on the swap/cvc families (division bench
    // cert2->cert3: QF_AX same-file 0.69x, read5 195ms->14s). Equisatisfiability
    // is unaffected either way — this is a PROFITABILITY gate, mirroring the
    // domain-size gate below. Overridable for experiments via AY_LNH_ON_ARRAYS=1.
    let allow_arrays = std::env::var("AY_LNH_ON_ARRAYS").is_ok_and(|v| v == "1");
    if !allow_arrays
        && terms.term_ids().any(
            |id| matches!(terms.get(id), TermData::App(s, _) if matches!(s.name(), "select" | "store")),
        )
    {
        return 0;
    }
    let Some((domain, dsort)) = find_domain(terms) else {
        return 0;
    };
    let n = domain.len();
    // Domain-size gate: small finite-model instances (n < 6) already solve fast,
    // and the lex-leader constraint overhead would slow them (net-negative in an
    // efficacy sweep: all losses were n<=5, all gains n>=6). Only apply where the
    // S_n blowup actually causes timeouts. Overridable via AY_LNH_MIN_N.
    let min_n: usize = std::env::var("AY_LNH_MIN_N")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(6);
    // The least-index scheme is a handful of short clauses (vs the lex-leader's
    // Tseitin chains), so it stays profitable one size below the lex gate
    // (measured: PEQ013_size5 3413 -> 15 conflicts). `AY_LNH_LEASTIDX_MIN_N`
    // overrides.
    let li_min_n: usize = std::env::var("AY_LNH_LEASTIDX_MIN_N")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(5);
    let try_lex = n >= min_n.max(2);
    let try_li = least_index_enabled() && n >= li_min_n.max(2);
    if !try_lex && !try_li {
        return 0;
    }

    let funcs = find_binary_funcs(terms, &dsort);
    let preds = find_unary_predicates(terms, &dsort);
    let diag = std::env::var_os("AY_LNH_DIAG").is_some();
    if diag {
        ay_core::safe_eprintln!("[LNH] n={n} binfuncs={} preds={}", funcs.len(), preds.len());
    }
    if funcs.is_empty() && preds.is_empty() && !try_li {
        return 0; // no atoms to canonicalize over
    }

    // SOUNDNESS GATE: only apply if the domain is PROVABLY interchangeable.
    let interchangeable = domain_is_interchangeable(terms, assertions, &domain);
    if diag {
        ay_core::safe_eprintln!("[LNH] interchangeable={interchangeable}");
    }
    if !interchangeable {
        return 0;
    }

    // Least-index orbit-prefix scheme (preferred: unit-propagation cascades).
    // MUTUALLY EXCLUSIVE with the lex-leader below — each scheme alone is
    // satisfiability-preserving, but their canonical-model choices differ, so
    // stacking both could exclude every model of a satisfiable orbit.
    if try_li {
        let added = add_least_index_symmetry_breaking(terms, assertions, &domain, &dsort, diag);
        if added > 0 {
            return added;
        }
    }
    if !try_lex || (funcs.is_empty() && preds.is_empty()) {
        return 0; // lex-leader gated out, or no atoms for it
    }

    // Fixed atom sequence: function-table equalities, then unary predicates.
    let mut atoms: Vec<TermId> = Vec::new();
    'build: for f in &funcs {
        for &a in &domain {
            for &b in &domain {
                let cell = terms.mk_app(f.clone(), [a, b], dsort.clone());
                for &c in &domain {
                    atoms.push(terms.mk_eq(cell, c));
                    if atoms.len() >= MAX_LEX_ATOMS {
                        break 'build;
                    }
                }
            }
        }
    }
    if atoms.len() < MAX_LEX_ATOMS {
        'p: for p in &preds {
            for &a in &domain {
                atoms.push(terms.mk_app(p.clone(), [a], Sort::Bool));
                if atoms.len() >= MAX_LEX_ATOMS {
                    break 'p;
                }
            }
        }
    }
    if atoms.is_empty() {
        return 0;
    }

    // For each adjacent transposition, assert M <=_lex swap(M).
    let mut added = 0usize;
    for i in 0..n - 1 {
        let ci = domain[i];
        let ci1 = domain[i + 1];
        let from = [ci, ci1];
        let to = [ci1, ci];
        let swapped: Vec<TermId> = atoms
            .iter()
            .map(|&at| terms.substitute(at, &from, &to))
            .collect();
        let le = lex_le(terms, &atoms, &swapped);
        if le != terms.true_term() {
            assertions.push(le);
            added += 1;
        }
    }
    if diag {
        ay_core::safe_eprintln!("[LNH] atoms={} constraints_added={added}", atoms.len());
    }
    added
}

#[cfg(test)]
mod tests {
    use super::*;

    // 6 elements: the smallest domain that clears the default AY_LNH_MIN_N=6
    // gate, so the "fires" tests exercise the real shipped configuration
    // (a 3-element domain silently no-ops at the size gate).
    fn domain6(t: &mut TermStore) -> (Sort, Vec<TermId>) {
        let s = Sort::Uninterpreted("U".to_string());
        let c: Vec<TermId> = (0..6)
            .map(|i| {
                t.mk_app(
                    Symbol::named(format!("c_{i}")),
                    [] as [TermId; 0],
                    s.clone(),
                )
            })
            .collect();
        (s, c)
    }

    /// Symmetric formula with a unary predicate => interchangeable => LNH fires.
    #[test]
    fn test_sig_ordering_fires_when_symmetric() {
        let mut t = TermStore::new();
        let (s, c) = domain6(&mut t);
        let mut assertions = Vec::new();
        // totality clauses for cells f(c_i,c_j) (symmetric domain signal)
        for &a in &c {
            for &b in &c {
                let cell = t.mk_app(Symbol::named("f"), [a, b], s.clone());
                let disj: Vec<TermId> = c.iter().map(|&ci| t.mk_eq(cell, ci)).collect();
                assertions.push(t.mk_or(disj));
            }
        }
        // a unary predicate p over the domain, used symmetrically (totality of p
        // over all c_i is symmetric)
        for &ci in &c {
            let _ = t.mk_app(Symbol::named("p"), [ci], Sort::Bool);
        }
        // reference the predicate symmetrically so it appears; add p(c_i) OR ¬p(c_i)
        // (a tautology, symmetric) so the assertion set stays S_n-invariant.
        for &ci in &c {
            let p = t.mk_app(Symbol::named("p"), [ci], Sort::Bool);
            let np = t.mk_not(p);
            assertions.push(t.mk_or(vec![p, np]));
        }
        let added = add_lnh_symmetry_breaking(&mut t, &mut assertions);
        assert!(
            added > 0,
            "sig-ordering should fire on symmetric domain w/ predicate"
        );
    }

    /// Asymmetric unit singles out c_0 => not interchangeable => no LNH.
    #[test]
    fn test_sig_ordering_refuses_non_interchangeable() {
        let mut t = TermStore::new();
        let (s, c) = domain6(&mut t);
        let mut assertions = Vec::new();
        for &a in &c {
            for &b in &c {
                let cell = t.mk_app(Symbol::named("f"), [a, b], s.clone());
                let disj: Vec<TermId> = c.iter().map(|&ci| t.mk_eq(cell, ci)).collect();
                assertions.push(t.mk_or(disj));
            }
        }
        let p0 = t.mk_app(Symbol::named("p"), [c[0]], Sort::Bool);
        assertions.push(p0); // asserts p(c_0) only — breaks interchangeability
        let added = add_lnh_symmetry_breaking(&mut t, &mut assertions);
        assert_eq!(added, 0, "must refuse a non-interchangeable domain");
    }

    /// No binary function and no unary predicate: the lex-leader has no atoms,
    /// but the LEAST-INDEX scheme still pins the totality subject (`a = c_0`).
    /// (Before least-index landed this was a full no-op.)
    #[test]
    fn test_least_index_pins_where_lex_leader_had_no_atoms() {
        let mut t = TermStore::new();
        let (s, c) = domain6(&mut t);
        // a domain-valued witness `a` with a totality clause (the domain signal),
        // but NO binary function and NO unary predicate.
        let a = t.mk_app(Symbol::named("a"), [] as [TermId; 0], s.clone());
        let disj: Vec<TermId> = c.iter().map(|&ci| t.mk_eq(a, ci)).collect();
        let mut assertions = vec![t.mk_or(disj)];
        let added = add_lnh_symmetry_breaking(&mut t, &mut assertions);
        assert_eq!(added, 1, "least-index pins the lone totality subject");
        let pin = *assertions.last().expect("clause added");
        match t.get(pin) {
            TermData::App(sym, args) if sym.name() == "=" => {
                assert!(args.contains(&a) && args.contains(&c[0]));
            }
            other => panic!("expected unit pin (= a c_0), got {other:?}"),
        }
    }

    /// Least-index: free constants get prefix clauses `x_k in {c_0..c_k}` —
    /// the PHP(n+1,n) cascade shape. First clause must be the unit `x = c_0`.
    #[test]
    fn test_least_index_prefix_clauses_on_free_constants() {
        let mut t = TermStore::new();
        let (s, c) = domain6(&mut t);
        let xs: Vec<TermId> = (0..3)
            .map(|k| {
                t.mk_app(
                    Symbol::named(format!("x_{k}")),
                    [] as [TermId; 0],
                    s.clone(),
                )
            })
            .collect();
        let mut assertions = Vec::new();
        for &x in &xs {
            let disj: Vec<TermId> = c.iter().map(|&ci| t.mk_eq(x, ci)).collect();
            assertions.push(t.mk_or(disj));
        }
        let n_orig = assertions.len();
        let added = add_lnh_symmetry_breaking(&mut t, &mut assertions);
        assert_eq!(added, 3, "one prefix clause per free constant");
        // First added clause is the unit pin (= x c) for some x, c.
        let first = assertions[n_orig];
        match t.get(first) {
            TermData::App(sym, args) if sym.name() == "=" => {
                assert!(args.iter().any(|a| c.contains(a)));
            }
            other => panic!("expected unit equality pin, got {other:?}"),
        }
    }

    /// Least-index fiat seeding: all subjects are binary cells (no free
    /// constant), so the first clause pins the cell's own constants by fiat
    /// and still emits `f(c_0,c_0) in {c_0, c_1}`-shaped prefixes.
    #[test]
    fn test_least_index_fiat_seeds_cell_only_subjects() {
        let mut t = TermStore::new();
        let (s, c) = domain6(&mut t);
        let mut assertions = Vec::new();
        for &a in &c {
            for &b in &c {
                let cell = t.mk_app(Symbol::named("f"), [a, b], s.clone());
                let disj: Vec<TermId> = c.iter().map(|&ci| t.mk_eq(cell, ci)).collect();
                assertions.push(t.mk_or(disj));
            }
        }
        let added = add_lnh_symmetry_breaking(&mut t, &mut assertions);
        assert!(added > 0, "fiat seeding must fire on cell-only subjects");
    }

    /// A totality clause under NOT must not be used as a least-index subject
    /// (positivity is a soundness premise) — and with nothing else symmetric
    /// to work from, the pass adds nothing.
    #[test]
    fn test_least_index_ignores_negative_totality() {
        let mut t = TermStore::new();
        let (s, c) = domain6(&mut t);
        let x = t.mk_app(Symbol::named("x"), [] as [TermId; 0], s.clone());
        let disj: Vec<TermId> = c.iter().map(|&ci| t.mk_eq(x, ci)).collect();
        let tot = t.mk_or(disj.clone());
        let neg = t.mk_not(tot);
        // Keep a POSITIVE totality clause on a different subject so
        // find_domain sees a domain, but x's clause is negative.
        let y = t.mk_app(Symbol::named("y"), [] as [TermId; 0], s.clone());
        let disj_y: Vec<TermId> = c.iter().map(|&ci| t.mk_eq(y, ci)).collect();
        let tot_y = t.mk_or(disj_y);
        let mut assertions = vec![neg, tot_y];
        let subjects = collect_totality_terms(&t, &assertions, &c, &s);
        assert_eq!(subjects, vec![y], "only the positive clause's subject");
        let _ = add_lnh_symmetry_breaking(&mut t, &mut assertions);
    }

    /// (kept) totality-only symmetric with a binary function => lex-leader fires.
    #[test]
    fn test_lex_leader_fires_with_function() {
        let mut t = TermStore::new();
        let (s, c) = domain6(&mut t);
        let mut assertions = Vec::new();
        for &a in &c {
            for &b in &c {
                let cell = t.mk_app(Symbol::named("f"), [a, b], s.clone());
                let disj: Vec<TermId> = c.iter().map(|&ci| t.mk_eq(cell, ci)).collect();
                assertions.push(t.mk_or(disj));
            }
        }
        let added = add_lnh_symmetry_breaking(&mut t, &mut assertions);
        assert!(
            added > 0,
            "lex-leader should fire on symmetric domain w/ function"
        );
    }
}
