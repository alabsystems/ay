// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Candidate-REJECTION diagnosis instrumentation (env-gated, verdict-neutral).
//!
//! Answers the decisive rusthorn-family question: `repro_slow1.smt2` is SAT
//! (z3: sat, 2.5s, one check-sat) yet ay's inner DPLL(T) enumerates 660k+
//! candidate models that LIA rubber-stamps `Sat`, and the depth-4 DT solve
//! NEVER CONCLUDES. Something REJECTS each Sat-stamped candidate and demands
//! another round. This module counts, per solve, WHY each round fails to
//! conclude: the categorised `TheoryResult` the N-O combiner returns for each
//! candidate, plus the term-store growth curve (matching-loop signature).
//!
//! ALL behaviour is gated on `AY_REJECT_INSTRUMENT` (any non-empty value).
//! When unset the hot-path calls read one cached thread-local bool and return
//! immediately, so the search is byte-identical (no verdict dependence). This
//! file mints no terms, asserts nothing, and never influences a result — it is
//! a pure observer of the candidate-rejection loop.

use std::cell::RefCell;

use ay_core::{TermData, TermId, TermStore, TheoryResult};

/// Coarse classification of a rejector atom's head symbol — enough to tell a
/// `logic_sum` recursive-unfolding matching loop from a datatype-selector
/// bridge from a plain interface equality.
fn head_bucket(terms: &TermStore, t: TermId) -> &'static str {
    match terms.get(t) {
        TermData::Not(inner) => head_bucket(terms, *inner),
        TermData::App(sym, _) => {
            let n = sym.name();
            if n.contains("logic_sum") {
                "logic_sum"
            } else if n.contains("enum_payload_get")
                || n.contains("list_cons")
                || n.contains("payload_cons")
                || n.contains("method_discriminant")
                || n.contains("tuple_get")
            {
                "selector"
            } else if n == "=" || n.contains("eq") {
                "eq"
            } else if n == "+"
                || n == "-"
                || n == "*"
                || n == "<="
                || n == "<"
                || n == ">="
                || n == ">"
            {
                "arith"
            } else if n.starts_with("is-") || n.contains("is_") {
                "tester"
            } else {
                "uf"
            }
        }
        TermData::Const(_) => "const",
        TermData::Var(..) => "var",
        TermData::Ite(..) => "ite",
        _ => "other",
    }
}

#[derive(Default)]
struct RejectState {
    checked: bool,
    enabled: bool,

    // ---- N-O combiner (nelson_oppen_check) return categorisation ----
    combiner_calls: u64,
    r_sat: u64,
    r_unsat: u64,        // TheoryResult::Unsat(lits) (EUF/array/model-eq)
    r_unsat_farkas: u64, // TheoryResult::UnsatWithFarkas (LIA/LRA)
    r_unknown: u64,
    // empty-conflict tally per kind (0-literal blocking clauses = non-learning)
    empty_unsat: u64,
    empty_farkas: u64,
    r_need_split: u64,
    r_need_diseq_split: u64,
    r_need_expr_split: u64,
    r_need_expr_splits: u64,
    r_need_lemmas: u64,
    r_need_model_eq: u64,
    r_need_model_eqs: u64,
    r_need_string_lemma: u64,

    // ---- lemma / model-eq / expr-split head-bucket histogram ----
    // key index: logic_sum, selector, eq, arith, tester, uf, const, var, ite, other
    lemma_bucket: [u64; 10],
    modeleq_bucket: [u64; 10],
    // for NeedExpressionSplit(s): bucket the two SIDES of the violated
    // disequality atom (the term the combiner insists must be distinct).
    exprsplit_side_bucket: [u64; 10],
    // distinct disequality atoms seen (by TermId) — cardinality tells
    // progress (bounded set, revisited) vs cycling (unbounded fresh atoms).
    exprsplit_distinct_atoms: std::collections::BTreeSet<u32>,
    modeleq_distinct_atoms: std::collections::BTreeSet<u64>,
    // Unsat (theory-conflict) diagnosis: distinguishes PROGRESS (each conflict
    // distinct, SAT learns and enumerates a real space) from CYCLING (the same
    // conflict regenerated — learned clause fails to block the model).
    unsat_distinct: std::collections::BTreeSet<u64>,
    unsat_size_sum: u64,
    unsat_side_bucket: [u64; 10],
    unsat_samples_printed: u32,

    // ---- INTERFACE-DIET M0/C5+R4 observables ----
    // shared_equalities_len sampled at every combiner result (the LIA N-O
    // interface size AT conflict time — the flood metric the diet withholds).
    shared_eq_len_sum: u64,
    shared_eq_len_max: usize,
    shared_eq_len_last: usize,
    // Per-kind conflict-length histograms + size sums, so a rejection MIGRATING
    // from LIA-Farkas to EUF with FAT explanations (the R4 "explanation-quality
    // wall" refutation signature) is visible separately from Farkas shrinkage.
    // Buckets: [0], [1-5], [6-15], [16-30], [31-60], [61-100], [101+].
    euf_len_hist: [u64; 7],
    farkas_len_hist: [u64; 7],
    euf_size_sum: u64,
    farkas_size_sum: u64,

    // ---- candidate-loop growth curve (matching-loop signature) ----
    cand_iters: u64,
    first_term_len: usize,
    last_term_len: usize,
    // sampled (iteration, term_len) milestones for the growth curve
    growth_samples: Vec<(u64, usize)>,
    // term-store length observed AT the combiner check (universal across all
    // pipeline variants, unlike cand_iters which only sees the eager arm)
    comb_first_term_len: usize,
    comb_last_term_len: usize,

    // concrete captured rounds — first occurrence of each distinct variant
    sampled_variants: std::collections::BTreeSet<&'static str>,
}

/// Fingerprint + bucket a theory conflict's literal set (order-independent),
/// so repeated identical conflicts collapse to one distinct entry and we can
/// see WHICH terms the conflict is over. `kind` tags EUF vs FARKAS in samples.
fn record_conflict(
    s: &mut RejectState,
    terms: &TermStore,
    lits: &[ay_core::TheoryLit],
    kind: &str,
) {
    let mut h: u64 = 1469598103934665603;
    // fold the kind so an empty EUF and an empty FARKAS don't collapse together
    h ^= kind.len() as u64;
    for lit in lits {
        let k = (u64::from(lit.term.0) << 1) | u64::from(lit.value);
        let mut x = k.wrapping_mul(1099511628211);
        x ^= x >> 29;
        h ^= x;
        let bi = bucket_idx(head_bucket(terms, lit.term));
        s.unsat_side_bucket[bi] += 1;
    }
    s.unsat_distinct.insert(h);
    s.unsat_size_sum += lits.len() as u64;
    // Per-kind length histogram + size sum (R4 EUF-vs-Farkas migration check).
    let lb = len_bucket(lits.len());
    if kind == "EUF" {
        s.euf_len_hist[lb] += 1;
        s.euf_size_sum += lits.len() as u64;
    } else {
        s.farkas_len_hist[lb] += 1;
        s.farkas_size_sum += lits.len() as u64;
    }
    if s.unsat_samples_printed < 6 {
        s.unsat_samples_printed += 1;
        let heads: Vec<String> = lits
            .iter()
            .take(8)
            .map(|l| format!("T{}={}[{}]", l.term.0, l.value, head_bucket(terms, l.term)))
            .collect();
        eprintln!(
            "c reject-instrument UNSAT-CONFLICT#{} kind={} call={} size={} lits={:?}",
            s.unsat_samples_printed,
            kind,
            s.combiner_calls,
            lits.len(),
            heads
        );
        for l in lits.iter().take(6) {
            eprintln!(
                "c reject-instrument     T{}={} {}",
                l.term.0,
                l.value,
                short_term(terms, l.term)
            );
        }
    }
}

/// Record the two SIDES of a violated disequality atom (a `(= a b)` /
/// `(distinct a b)` term, possibly under `not`) plus its TermId, so we can
/// tell WHICH terms the combiner keeps insisting are distinct and whether the
/// set of such atoms is bounded (progress) or unbounded (cycling).
fn bucket_diseq_atom(s: &mut RejectState, terms: &TermStore, atom: TermId) {
    s.exprsplit_distinct_atoms.insert(atom.0);
    let inner = match terms.get(atom) {
        TermData::Not(i) => *i,
        _ => atom,
    };
    if let TermData::App(_, args) = terms.get(inner) {
        for a in args.iter().take(2) {
            let bi = bucket_idx(head_bucket(terms, *a));
            s.exprsplit_side_bucket[bi] += 1;
        }
    }
}

/// Conflict-length histogram bucket: [0],[1-5],[6-15],[16-30],[31-60],[61-100],[101+].
fn len_bucket(n: usize) -> usize {
    match n {
        0 => 0,
        1..=5 => 1,
        6..=15 => 2,
        16..=30 => 3,
        31..=60 => 4,
        61..=100 => 5,
        _ => 6,
    }
}

const LEN_BUCKET_NAMES: [&str; 7] = ["0", "1-5", "6-15", "16-30", "31-60", "61-100", "101+"];

fn bucket_idx(b: &str) -> usize {
    match b {
        "logic_sum" => 0,
        "selector" => 1,
        "eq" => 2,
        "arith" => 3,
        "tester" => 4,
        "uf" => 5,
        "const" => 6,
        "var" => 7,
        "ite" => 8,
        _ => 9,
    }
}

const BUCKET_NAMES: [&str; 10] = [
    "logic_sum",
    "selector",
    "eq",
    "arith",
    "tester",
    "uf",
    "const",
    "var",
    "ite",
    "other",
];

thread_local! {
    static STATE: RefCell<RejectState> = RefCell::new(RejectState::default());
}

fn enabled(s: &mut RejectState) -> bool {
    if !s.checked {
        s.checked = true;
        s.enabled = std::env::var_os("AY_REJECT_INSTRUMENT").is_some();
    }
    s.enabled
}

/// Record one candidate-loop iteration + the current term-store length.
/// Emits a periodic rejection-table snapshot so partial data survives a
/// SIGTERM/timeout kill (the diverging solve never returns cleanly).
pub(crate) fn record_candidate_iteration(iteration: usize, term_len: usize) {
    STATE.with(|st| {
        let mut s = st.borrow_mut();
        if !enabled(&mut s) {
            return;
        }
        if s.cand_iters == 0 {
            s.first_term_len = term_len;
        }
        s.cand_iters += 1;
        s.last_term_len = term_len;
        let _ = iteration;
        // sample the growth curve every 2k iterations
        if s.cand_iters % 2_000 == 0 {
            let it = s.cand_iters;
            s.growth_samples.push((it, term_len));
        }
    });
}

/// Categorise the `TheoryResult` the N-O combiner returned for a candidate
/// model. This is the rejector: anything other than `Sat`/`Unsat` means the
/// combiner refused to conclude and demanded another round.
pub(crate) fn record_combiner_result(
    result: &TheoryResult,
    terms: &TermStore,
    shared_eq_len: usize,
) {
    STATE.with(|st| {
        let mut s = st.borrow_mut();
        if !enabled(&mut s) {
            return;
        }
        if s.combiner_calls == 0 {
            s.comb_first_term_len = terms.len();
        }
        s.combiner_calls += 1;
        s.comb_last_term_len = terms.len();
        // C5/R4: sample the LIA shared-equality interface size at every result.
        s.shared_eq_len_sum += shared_eq_len as u64;
        if shared_eq_len > s.shared_eq_len_max {
            s.shared_eq_len_max = shared_eq_len;
        }
        s.shared_eq_len_last = shared_eq_len;
        match result {
            TheoryResult::Sat => s.r_sat += 1,
            TheoryResult::Unsat(lits) => {
                s.r_unsat += 1;
                if lits.is_empty() {
                    s.empty_unsat += 1;
                }
                record_conflict(&mut s, terms, lits, "EUF");
            }
            TheoryResult::UnsatWithFarkas(conflict) => {
                s.r_unsat_farkas += 1;
                if conflict.literals.is_empty() {
                    s.empty_farkas += 1;
                }
                record_conflict(&mut s, terms, &conflict.literals, "FARKAS");
            }
            TheoryResult::Unknown => s.r_unknown += 1,
            TheoryResult::NeedSplit(_) => s.r_need_split += 1,
            TheoryResult::NeedDisequalitySplit(_) => s.r_need_diseq_split += 1,
            TheoryResult::NeedExpressionSplit(req) => {
                s.r_need_expr_split += 1;
                bucket_diseq_atom(&mut s, terms, req.disequality_term);
            }
            TheoryResult::NeedExpressionSplits(reqs) => {
                s.r_need_expr_splits += 1;
                for req in reqs {
                    bucket_diseq_atom(&mut s, terms, req.disequality_term);
                }
            }
            TheoryResult::NeedStringLemma(_) => s.r_need_string_lemma += 1,
            TheoryResult::NeedLemmas(lemmas) => {
                s.r_need_lemmas += 1;
                for lemma in lemmas {
                    for lit in &lemma.clause {
                        let idx = bucket_idx(head_bucket(terms, lit.term));
                        s.lemma_bucket[idx] += 1;
                    }
                }
            }
            TheoryResult::NeedModelEquality(eq) => {
                s.r_need_model_eq += 1;
                let li = bucket_idx(head_bucket(terms, eq.lhs));
                let ri = bucket_idx(head_bucket(terms, eq.rhs));
                s.modeleq_bucket[li] += 1;
                s.modeleq_bucket[ri] += 1;
                s.modeleq_distinct_atoms
                    .insert((u64::from(eq.lhs.0) << 32) | u64::from(eq.rhs.0));
            }
            TheoryResult::NeedModelEqualities(eqs) => {
                s.r_need_model_eqs += 1;
                for eq in eqs {
                    let li = bucket_idx(head_bucket(terms, eq.lhs));
                    let ri = bucket_idx(head_bucket(terms, eq.rhs));
                    s.modeleq_bucket[li] += 1;
                    s.modeleq_bucket[ri] += 1;
                    s.modeleq_distinct_atoms
                        .insert((u64::from(eq.lhs.0) << 32) | u64::from(eq.rhs.0));
                }
            }
            _ => {}
        }

        // Capture ONE concrete round that DEMANDS ANOTHER ROUND (a Need*
        // rejector — not Sat/Unsat/Unknown, which are terminal for the loop).
        let is_demand = matches!(
            result,
            TheoryResult::NeedLemmas(_)
                | TheoryResult::NeedModelEquality(_)
                | TheoryResult::NeedModelEqualities(_)
                | TheoryResult::NeedSplit(_)
                | TheoryResult::NeedDisequalitySplit(_)
                | TheoryResult::NeedExpressionSplit(_)
                | TheoryResult::NeedExpressionSplits(_)
                | TheoryResult::NeedStringLemma(_)
        );
        if is_demand {
            let vname = variant_name(result);
            if s.sampled_variants.insert(vname) {
                eprintln!(
                    "c reject-instrument SAMPLE combiner_call={} term_len={} variant={}",
                    s.combiner_calls,
                    terms.len(),
                    vname
                );
                describe_result(result, terms);
            }
        }
        // Periodic full-table dump keyed on combiner calls — universal across
        // all pipeline variants, so it fires regardless of which split loop
        // drives the depth-4 candidate enumeration. Survives a SIGTERM/timeout.
        if s.combiner_calls % 2_000 == 0 {
            dump_locked(&s, "periodic-combiner");
        }
    });
}

fn variant_name(r: &TheoryResult) -> &'static str {
    match r {
        TheoryResult::Sat => "Sat",
        TheoryResult::Unsat(_) => "Unsat",
        TheoryResult::UnsatWithFarkas(_) => "UnsatWithFarkas",
        TheoryResult::Unknown => "Unknown",
        TheoryResult::NeedSplit(_) => "NeedSplit",
        TheoryResult::NeedDisequalitySplit(_) => "NeedDisequalitySplit",
        TheoryResult::NeedExpressionSplit(_) => "NeedExpressionSplit",
        TheoryResult::NeedExpressionSplits(_) => "NeedExpressionSplits",
        TheoryResult::NeedStringLemma(_) => "NeedStringLemma",
        TheoryResult::NeedLemmas(_) => "NeedLemmas",
        TheoryResult::NeedModelEquality(_) => "NeedModelEquality",
        TheoryResult::NeedModelEqualities(_) => "NeedModelEqualities",
        _ => "Other",
    }
}

fn describe_diseq(terms: &TermStore, atom: TermId) -> String {
    let inner = match terms.get(atom) {
        TermData::Not(i) => *i,
        _ => atom,
    };
    if let TermData::App(sym, args) = terms.get(inner) {
        let sides: Vec<String> = args
            .iter()
            .take(2)
            .map(|a| {
                format!(
                    "T{} [{}] {}",
                    a.0,
                    head_bucket(terms, *a),
                    short_term(terms, *a)
                )
            })
            .collect();
        format!("atom=T{} ({} ...) sides={:?}", atom.0, sym.name(), sides)
    } else {
        format!("atom=T{} {}", atom.0, short_term(terms, atom))
    }
}

fn describe_result(r: &TheoryResult, terms: &TermStore) {
    match r {
        TheoryResult::NeedExpressionSplit(req) => {
            eprintln!(
                "c reject-instrument   exprsplit {}",
                describe_diseq(terms, req.disequality_term)
            );
        }
        TheoryResult::NeedExpressionSplits(reqs) => {
            eprintln!("c reject-instrument   exprsplits count={}", reqs.len());
            for req in reqs.iter().take(6) {
                eprintln!(
                    "c reject-instrument     {}",
                    describe_diseq(terms, req.disequality_term)
                );
            }
        }
        TheoryResult::NeedSplit(req) => {
            eprintln!(
                "c reject-instrument   split var=T{} [{}] {} floor={} ceil={}",
                req.variable.0,
                head_bucket(terms, req.variable),
                short_term(terms, req.variable),
                req.floor,
                req.ceil
            );
        }
        TheoryResult::NeedLemmas(lemmas) => {
            for (i, lemma) in lemmas.iter().enumerate().take(4) {
                let heads: Vec<&str> = lemma
                    .clause
                    .iter()
                    .map(|l| head_bucket(terms, l.term))
                    .collect();
                eprintln!(
                    "c reject-instrument   lemma[{i}] atoms={} heads={:?}",
                    lemma.clause.len(),
                    heads
                );
                for lit in lemma.clause.iter().take(4) {
                    eprintln!(
                        "c reject-instrument     lit T{} val={} {}",
                        lit.term.0,
                        lit.value,
                        short_term(terms, lit.term)
                    );
                }
            }
        }
        TheoryResult::NeedModelEquality(eq) => {
            eprintln!(
                "c reject-instrument   modeleq lhs=T{} [{}] {} == rhs=T{} [{}] {}",
                eq.lhs.0,
                head_bucket(terms, eq.lhs),
                short_term(terms, eq.lhs),
                eq.rhs.0,
                head_bucket(terms, eq.rhs),
                short_term(terms, eq.rhs)
            );
        }
        TheoryResult::NeedModelEqualities(eqs) => {
            for eq in eqs.iter().take(6) {
                eprintln!(
                    "c reject-instrument   modeleq lhs=T{} [{}] == rhs=T{} [{}]",
                    eq.lhs.0,
                    head_bucket(terms, eq.lhs),
                    eq.rhs.0,
                    head_bucket(terms, eq.rhs)
                );
            }
        }
        _ => {}
    }
}

/// Very short structural sketch of a term (head + arity + child heads).
fn short_term(terms: &TermStore, t: TermId) -> String {
    match terms.get(t) {
        TermData::App(sym, args) => {
            let child_heads: Vec<&str> = args
                .iter()
                .take(3)
                .map(|a| head_bucket(terms, *a))
                .collect();
            format!("({} /{} {:?})", sym.name(), args.len(), child_heads)
        }
        TermData::Not(inner) => format!("(not {})", short_term(terms, *inner)),
        TermData::Const(_) => "const".to_string(),
        TermData::Var(n, _) => format!("var:{n}"),
        TermData::Ite(..) => "ite".to_string(),
        _ => "other".to_string(),
    }
}

fn dump_locked(s: &RejectState, tag: &str) {
    eprintln!("c ======== reject-instrument TABLE ({tag}) ========");
    eprintln!(
        "c candidate_iterations(eager arm only)={}  term_len first={} last={}  growth=+{}",
        s.cand_iters,
        s.first_term_len,
        s.last_term_len,
        s.last_term_len.saturating_sub(s.first_term_len)
    );
    eprintln!(
        "c combiner_calls={}  comb_term_len first={} last={}  growth=+{}",
        s.combiner_calls,
        s.comb_first_term_len,
        s.comb_last_term_len,
        s.comb_last_term_len.saturating_sub(s.comb_first_term_len)
    );
    let total_unsat = s.r_unsat + s.r_unsat_farkas;
    eprintln!(
        "c   Sat={}  Unsat(EUF)={}  UnsatWithFarkas(LIA)={}  Unknown={}",
        s.r_sat, s.r_unsat, s.r_unsat_farkas, s.r_unknown
    );
    eprintln!(
        "c   empty_conflicts: EUF={}  FARKAS={}  (empty => non-blocking, cannot learn)",
        s.empty_unsat, s.empty_farkas
    );
    let avg_sz = if total_unsat > 0 {
        s.unsat_size_sum as f64 / total_unsat as f64
    } else {
        0.0
    };
    eprintln!(
        "c   ALL-UNSAT distinct_conflicts={}  total={}  avg_conflict_size={:.2}  => {}",
        s.unsat_distinct.len(),
        total_unsat,
        avg_sz,
        if total_unsat > 100 && (s.unsat_distinct.len() as f64) < 0.1 * (total_unsat as f64) {
            "CYCLING (conflicts regenerated)"
        } else {
            "PROGRESS (distinct conflicts)"
        }
    );
    // INTERFACE-DIET C5/R4: shared-equality interface size + per-kind conflict
    // length histograms (Farkas shrinkage vs EUF-migration diagnosis).
    let avg_sh = if s.combiner_calls > 0 {
        s.shared_eq_len_sum as f64 / s.combiner_calls as f64
    } else {
        0.0
    };
    eprintln!(
        "c   shared_equalities_len@result: avg={avg_sh:.1}  max={}  last={}",
        s.shared_eq_len_max, s.shared_eq_len_last
    );
    let euf_avg = if s.r_unsat > 0 {
        s.euf_size_sum as f64 / s.r_unsat as f64
    } else {
        0.0
    };
    let farkas_avg = if s.r_unsat_farkas > 0 {
        s.farkas_size_sum as f64 / s.r_unsat_farkas as f64
    } else {
        0.0
    };
    eprint!("c   EUF-conflict-length hist (avg={euf_avg:.1}):");
    for (i, name) in LEN_BUCKET_NAMES.iter().enumerate() {
        if s.euf_len_hist[i] > 0 {
            eprint!(" {name}={}", s.euf_len_hist[i]);
        }
    }
    eprintln!();
    eprint!("c   FARKAS-conflict-length hist (avg={farkas_avg:.1}):");
    for (i, name) in LEN_BUCKET_NAMES.iter().enumerate() {
        if s.farkas_len_hist[i] > 0 {
            eprint!(" {name}={}", s.farkas_len_hist[i]);
        }
    }
    eprintln!();
    eprintln!("c   unsat_conflict_side_head_hist:");
    for (i, name) in BUCKET_NAMES.iter().enumerate() {
        if s.unsat_side_bucket[i] > 0 {
            eprintln!("c     {name}={}", s.unsat_side_bucket[i]);
        }
    }
    eprintln!(
        "c   NeedSplit={}  NeedDiseqSplit={}  NeedExprSplit={}  NeedExprSplits={}",
        s.r_need_split, s.r_need_diseq_split, s.r_need_expr_split, s.r_need_expr_splits
    );
    eprintln!(
        "c   NeedLemmas={}  NeedModelEquality={}  NeedModelEqualities={}  NeedStringLemma={}",
        s.r_need_lemmas, s.r_need_model_eq, s.r_need_model_eqs, s.r_need_string_lemma
    );
    // dominant rejector
    let cands: [(&str, u64); 10] = [
        ("Unsat(EUF-conflict)", s.r_unsat),
        ("UnsatWithFarkas(LIA-conflict)", s.r_unsat_farkas),
        ("NeedLemmas", s.r_need_lemmas),
        ("NeedModelEquality", s.r_need_model_eq),
        ("NeedModelEqualities", s.r_need_model_eqs),
        ("NeedSplit", s.r_need_split),
        ("NeedDisequalitySplit", s.r_need_diseq_split),
        ("NeedExpressionSplit", s.r_need_expr_split),
        ("NeedExpressionSplits", s.r_need_expr_splits),
        ("NeedStringLemma", s.r_need_string_lemma),
    ];
    if let Some((name, n)) = cands.iter().copied().max_by_key(|(_, n)| *n) {
        eprintln!("c   DOMINANT_REJECTOR={name} count={n}");
    }
    // progress-vs-cycling: how many DISTINCT rejector atoms/pairs (bounded set,
    // revisited = progress-capable; unbounded fresh = cycling matching loop)
    eprintln!(
        "c   distinct_exprsplit_atoms={}  distinct_modeleq_pairs={}",
        s.exprsplit_distinct_atoms.len(),
        s.modeleq_distinct_atoms.len()
    );
    eprintln!("c   lemma_head_hist:");
    for (i, name) in BUCKET_NAMES.iter().enumerate() {
        if s.lemma_bucket[i] > 0 {
            eprintln!("c     {name}={}", s.lemma_bucket[i]);
        }
    }
    eprintln!("c   modeleq_head_hist:");
    for (i, name) in BUCKET_NAMES.iter().enumerate() {
        if s.modeleq_bucket[i] > 0 {
            eprintln!("c     {name}={}", s.modeleq_bucket[i]);
        }
    }
    eprintln!("c   exprsplit_side_head_hist:");
    for (i, name) in BUCKET_NAMES.iter().enumerate() {
        if s.exprsplit_side_bucket[i] > 0 {
            eprintln!("c     {name}={}", s.exprsplit_side_bucket[i]);
        }
    }
    eprintln!("c   growth_curve (iter -> term_len):");
    for (it, tl) in &s.growth_samples {
        eprintln!("c     {it} -> {tl}");
    }
    eprintln!("c ================================================");
}

/// Explicit end-of-solve dump (best-effort; the diverging solve is usually
/// killed before reaching this, which is why `record_candidate_iteration`
/// also dumps periodically). Retained for manual/terminating-solve use.
#[allow(dead_code)]
pub(crate) fn dump_final() {
    STATE.with(|st| {
        let s = st.borrow();
        if !s.enabled {
            return;
        }
        dump_locked(&s, "final");
    });
}
