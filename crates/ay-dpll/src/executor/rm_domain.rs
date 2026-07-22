// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! FP RoundingMode finite-domain coverage (Pass B of #P0.2 symbolic
//! RoundingMode).
//!
//! `RoundingMode` is `Sort::Uninterpreted("RoundingMode")` in the core term
//! language (see `ay-frontend` elaborate/term.rs — RM literals — and
//! sorts.rs — declared consts), but semantically it is the FIXED 5-element
//! domain {RNE, RNA, RTP, RTN, RTZ}. EUF alone treats it as an unbounded free
//! sort, which produced live wrong verdicts both ways:
//!
//! * `(assert (= roundTowardPositive roundTowardZero))` → `sat` (EUF happily
//!   merges the two nullary constants; truth: `unsat`),
//! * `(distinct a b c d e f)` over six RM consts → `sat` (no pigeonhole over a
//!   free sort; truth: `unsat`).
//!
//! This pass asserts, for an assertion set that mentions RoundingMode in a
//! domain position:
//!
//! 1. `(distinct RNE RNA RTP RTN RTZ)` — the five literal modes are pairwise
//!    distinct, and
//! 2. per non-literal RoundingMode-sorted ground term `t`:
//!    `(or (= t RNE) (= t RNA) (= t RTP) (= t RTN) (= t RTZ))` — domain
//!    coverage.
//!
//! Both are VALID in every model of the FP theory (the RoundingMode domain is
//! exactly the five modes), so adding them removes no models and can never
//! turn `sat` into `unsat`; they only stop EUF from inventing out-of-domain
//! elements or merging distinct modes. This mirrors
//! `add_finite_enum_domain_coverage` (the all-nullary-datatype precedent) with
//! two deliberate differences dictated by the wrong-verdict analysis:
//!
//! * Plain declared `Var` terms ARE covered (the datatype precedent skips
//!   them): for RM the declared consts are exactly the load-bearing pigeonhole
//!   terms — `(distinct a b c d e f)` has no application terms at all.
//! * There is NO silent over-budget skip and NO silent quantifier skip. For
//!   the datatype pass, skipping only costs completeness (a lost `unsat`).
//!   Here an *uncovered* RM term leaves a wrong `sat` reachable (EUF floats it
//!   out of the 5-element domain), so any shape this pass cannot prove fully
//!   covered — an RM mention under a quantifier, or a term count beyond the
//!   budget — must FAIL CLOSED to `unknown` (`RmDomainAxioms::FailClose`),
//!   never proceed uncovered.
//!
//! Trigger discipline (byte-compat with literal-mode FP): the pass is a strict
//! no-op unless the assertion DAG mentions RoundingMode OUTSIDE the
//! rounding-mode operand slot of an FP operation. Literal-mode FP corpora
//! (`(fp.add RNE x y)` …) therefore see zero new assertions and an unchanged
//! CNF. Callers place the returned axioms scope-transiently (check_sat's
//! in-place preprocessing with `scope_tracked_assertions` restore; the
//! check-sat-assuming wrapper's truncate) so nothing persists across solves.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::{Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};
use ay_fp::RoundingMode;

use super::Executor;

/// The five IEEE 754 / SMT-LIB rounding modes, in canonical order.
pub(in crate::executor) const RM_MODES: [RoundingMode; 5] = [
    RoundingMode::RNE,
    RoundingMode::RNA,
    RoundingMode::RTP,
    RoundingMode::RTN,
    RoundingMode::RTZ,
];

/// Budget for coverage terms. Exceeding it FAILS CLOSED (never a silent,
/// uncovered proceed — see module docs). 256 matches the datatype precedent;
/// real RM problems have a handful of mode terms.
const RM_COVERAGE_MAX_TERMS: usize = 256;

/// The RoundingMode sort as stored in the core term language.
pub(in crate::executor) fn rm_sort() -> Sort {
    Sort::Uninterpreted("RoundingMode".to_string())
}

/// Whether `sort` is the RoundingMode sort.
pub(in crate::executor) fn is_rm_sort(sort: &Sort) -> bool {
    matches!(sort, Sort::Uninterpreted(name) if name == "RoundingMode")
}

/// Whether `term` is a *literal* rounding mode: a nullary application or a
/// variable whose name resolves via `RoundingMode::from_name` (mirrors
/// `theories/fp/support.rs::is_literal_rounding_mode`; the Var arm only
/// matters for embedder-built terms — the frontend seals the ten names).
pub(in crate::executor) fn is_rm_literal(terms: &TermStore, term: TermId) -> bool {
    rm_literal_mode(terms, term).is_some()
}

/// The concrete mode of a literal rounding-mode term, if it is one.
pub(in crate::executor) fn rm_literal_mode(
    terms: &TermStore,
    term: TermId,
) -> Option<RoundingMode> {
    match terms.get(term) {
        TermData::App(sym, args) if args.is_empty() => RoundingMode::from_name(sym.name()),
        TermData::Var(name, _) => RoundingMode::from_name(name),
        _ => None,
    }
}

/// Intern the literal term for `mode`, exactly as the frontend elaborates RM
/// literals (`mk_app(short_name, [], RoundingMode)`) so hash-consing merges it
/// with parsed literals and EUF sees ONE constant per mode.
pub(in crate::executor) fn rm_literal_term(terms: &mut TermStore, mode: RoundingMode) -> TermId {
    terms.mk_app(Symbol::named(mode.name()), vec![], rm_sort())
}

/// SMT-LIB long name for a mode (`roundTowardZero` …) — the spelling z3
/// prints in models.
pub(in crate::executor) fn rm_long_name(mode: RoundingMode) -> &'static str {
    match mode {
        RoundingMode::RNE => "roundNearestTiesToEven",
        RoundingMode::RNA => "roundNearestTiesToAway",
        RoundingMode::RTP => "roundTowardPositive",
        RoundingMode::RTN => "roundTowardNegative",
        RoundingMode::RTZ => "roundTowardZero",
    }
}

/// The rounding-mode operand slot of an FP application, if it has one.
/// Mirrors `theories/fp/support.rs::rounding_mode_operand`.
fn fp_rounding_mode_operand(name: &str, args: &[TermId]) -> Option<TermId> {
    match name {
        "fp.add" | "fp.sub" | "fp.mul" | "fp.div" | "fp.sqrt" | "fp.fma" | "fp.roundToIntegral" => {
            args.first().copied()
        }
        "to_fp" | "to_fp_unsigned" | "fp.to_ubv" | "fp.to_sbv" if args.len() == 2 => Some(args[0]),
        _ => None,
    }
}

/// Outcome of the RM domain-coverage scan.
pub(in crate::executor) enum RmDomainAxioms {
    /// No RoundingMode domain mention: strict no-op (byte-compat path).
    NoMention,
    /// The domain axioms to assert (distinct-5 first, then per-term coverage,
    /// in deterministic first-visit order).
    Axioms(Vec<TermId>),
    /// A RoundingMode mention this pass cannot prove covered (an RM-sort
    /// mention under a quantifier, or over budget). The caller MUST fail the
    /// solve closed to `unknown` — an uncovered RM term leaves a wrong `sat`
    /// reachable.
    FailClose,
}

impl Executor {
    /// Scan `roots` (assertions plus any assumptions) and produce the RM
    /// finite-domain axioms, `NoMention` when RoundingMode does not occur in a
    /// domain position, or `FailClose` when full coverage cannot be proven.
    pub(in crate::executor) fn rm_domain_axioms(&mut self, roots: &[TermId]) -> RmDomainAxioms {
        // ---- Collection walk (immutable) ----
        let terms = &self.ctx.terms;
        let mut seen: HashSet<TermId> = HashSet::default();
        // Non-literal RM-sorted ground terms, in deterministic DFS order.
        let mut needs_coverage: Vec<TermId> = Vec::new();
        let mut coverage_set: HashSet<TermId> = HashSet::default();
        // An RM literal occurred OUTSIDE an FP rounding-op mode slot
        // (equality/distinct/ite/UF argument…): the distinct-5 axiom is then
        // load-bearing even with no non-literal term (`(= RTP RTZ)`).
        let mut literal_domain_mention = false;

        let mut stack: Vec<TermId> = roots.to_vec();
        // Roots are formulas (Bool-sorted); an RM literal can only be *seen*
        // through a parent, so parent-side classification below is exhaustive.
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            // Any non-literal term whose OWN sort is RoundingMode needs
            // coverage — Vars included (see module docs), UF applications,
            // ites, whatever shape: the coverage disjunction is valid for any
            // ground RM-sorted term.
            if is_rm_sort(terms.sort(t)) && !is_rm_literal(terms, t) && coverage_set.insert(t) {
                needs_coverage.push(t);
            }
            match terms.get(t) {
                TermData::App(sym, args) => {
                    let mode_slot = fp_rounding_mode_operand(sym.name(), args);
                    for (i, &a) in args.iter().enumerate() {
                        // A literal in the rounding-op mode slot (arg 0) is the
                        // byte-compat literal-mode FP case: no domain mention.
                        let in_mode_slot = i == 0 && mode_slot == Some(a);
                        if !in_mode_slot && is_rm_literal(terms, a) {
                            literal_domain_mention = true;
                        }
                        stack.push(a);
                    }
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, th, el) => {
                    for &x in &[*c, *th, *el] {
                        if is_rm_literal(terms, x) {
                            literal_domain_mention = true;
                        }
                        stack.push(x);
                    }
                }
                TermData::Let(bindings, body) => {
                    for (_, v) in bindings {
                        if is_rm_literal(terms, *v) {
                            literal_domain_mention = true;
                        }
                        stack.push(*v);
                    }
                    stack.push(*body);
                }
                TermData::Forall(vars, body, _) | TermData::Exists(vars, body, _) => {
                    // RoundingMode under a binder needs its own discipline
                    // (ground coverage cannot reach bound-variable-carrying
                    // terms, and instantiation could mint RM terms after this
                    // pass ran). `walk_quantifier_body` covers what is
                    // provably ground (global RM consts), ignores benign
                    // literal mode operands (`fp.add RNE …` under a `forall`
                    // is the standard quantified-FP pattern and must NOT
                    // degrade), flags literal domain mentions, and FAILS
                    // CLOSED on everything else: RM-sorted binders, RM-valued
                    // applications/ites (may carry bound variables), and any
                    // `let` that mentions the sort.
                    if vars.iter().any(|(_, s)| is_rm_sort(s))
                        || !walk_quantifier_body(
                            terms,
                            *body,
                            &mut vars.iter().map(|(n, _)| n.clone()).collect(),
                            &mut needs_coverage,
                            &mut coverage_set,
                            &mut literal_domain_mention,
                        )
                    {
                        return RmDomainAxioms::FailClose;
                    }
                }
                _ => {}
            }
        }

        if needs_coverage.is_empty() && !literal_domain_mention {
            return RmDomainAxioms::NoMention;
        }
        if needs_coverage.len() > RM_COVERAGE_MAX_TERMS {
            // NEVER proceed uncovered (a wrong `sat` would be reachable).
            return RmDomainAxioms::FailClose;
        }

        // ---- Axiom construction (mutable) ----
        let terms = &mut self.ctx.terms;
        let lits: Vec<TermId> = RM_MODES
            .iter()
            .map(|&m| rm_literal_term(terms, m))
            .collect();
        let mut axioms: Vec<TermId> = Vec::with_capacity(1 + needs_coverage.len());
        // `mk_distinct` expands ≥3-ary distinct to pairwise disequalities, so
        // every theory lane sees plain `not (= …)` atoms.
        axioms.push(terms.mk_distinct(lits.clone()));
        for t in needs_coverage {
            let eqs: Vec<TermId> = lits.iter().map(|&l| terms.mk_eq(t, l)).collect();
            axioms.push(terms.mk_or(eqs));
        }
        RmDomainAxioms::Axioms(axioms)
    }
}

/// Walk a quantifier body classifying its RoundingMode mentions.
///
/// Returns `true` when every RM mention is handled soundly:
/// * an RM literal in an FP rounding-op mode slot — benign, ignored (this is
///   the standard quantified-FP pattern, e.g. `forall i. … (fp.add RNE …)`);
/// * an RM literal in a domain position — sets `literal_domain_mention` so
///   the distinct-5 axiom (ground, valid) constrains every instantiation;
/// * a plain RM-sorted `Var` that is NOT a bound variable of any enclosing
///   binder — a GLOBAL constant (bound-variable-carrying terms are never
///   plain global Vars), so the ground coverage disjunction reaches it:
///   collected into `needs_coverage`.
///
/// Returns `false` (caller MUST fail closed) for every other shape: an
/// RM-sorted binder of a nested quantifier, an RM-sorted Var that shadows an
/// enclosing binder name, any RM-sorted application/ite (it may carry bound
/// variables — asserting ground coverage over it would be ill-formed), and
/// any `let` whose subtree mentions the sort (binding structure makes
/// groundness analysis unreliable; rare, conservative).
fn walk_quantifier_body(
    terms: &TermStore,
    body: TermId,
    binder_names: &mut Vec<String>,
    needs_coverage: &mut Vec<TermId>,
    coverage_set: &mut HashSet<TermId>,
    literal_domain_mention: &mut bool,
) -> bool {
    // No cross-call seen-set: the binder-name context matters, and quantifier
    // bodies are small relative to the ground DAG.
    let data = terms.get(body).clone();
    if is_rm_sort(terms.sort(body)) && !is_rm_literal(terms, body) {
        match &data {
            TermData::Var(name, _) => {
                if binder_names.iter().any(|b| b == name) {
                    return false; // bound RM var (or shadowing) — fail closed
                }
                if coverage_set.insert(body) {
                    needs_coverage.push(body);
                }
            }
            _ => return false, // RM-valued app/ite/let under a binder
        }
    }
    match data {
        TermData::App(sym, args) => {
            let mode_slot = fp_rounding_mode_operand(sym.name(), &args);
            for (i, &a) in args.iter().enumerate() {
                let in_mode_slot = i == 0 && mode_slot == Some(a);
                if is_rm_literal(terms, a) {
                    if !in_mode_slot {
                        *literal_domain_mention = true;
                    }
                    continue;
                }
                if !walk_quantifier_body(
                    terms,
                    a,
                    binder_names,
                    needs_coverage,
                    coverage_set,
                    literal_domain_mention,
                ) {
                    return false;
                }
            }
            true
        }
        TermData::Not(inner) => walk_quantifier_body(
            terms,
            inner,
            binder_names,
            needs_coverage,
            coverage_set,
            literal_domain_mention,
        ),
        TermData::Ite(c, th, el) => [c, th, el].into_iter().all(|x| {
            if is_rm_literal(terms, x) {
                *literal_domain_mention = true;
                return true;
            }
            walk_quantifier_body(
                terms,
                x,
                binder_names,
                needs_coverage,
                coverage_set,
                literal_domain_mention,
            )
        }),
        // `let` under a binder: fail closed iff its subtree mentions RM at
        // all (conservative — see doc comment).
        TermData::Let(..) => !subtree_mentions_rm_sort(terms, body),
        TermData::Forall(vars, b, _) | TermData::Exists(vars, b, _) => {
            if vars.iter().any(|(_, s)| is_rm_sort(s)) {
                return false;
            }
            let added = vars.len();
            binder_names.extend(vars.iter().map(|(n, _)| n.clone()));
            let ok = walk_quantifier_body(
                terms,
                b,
                binder_names,
                needs_coverage,
                coverage_set,
                literal_domain_mention,
            );
            binder_names.truncate(binder_names.len() - added);
            ok
        }
        // Constants and non-RM vars carry no RM structure.
        _ => true,
    }
}

/// Whether any subterm (incl. binder sorts and literals) mentions the
/// RoundingMode sort.
fn subtree_mentions_rm_sort(terms: &TermStore, root: TermId) -> bool {
    let mut seen: HashSet<TermId> = HashSet::default();
    let mut stack = vec![root];
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        if is_rm_sort(terms.sort(t)) {
            return true;
        }
        match terms.get(t) {
            TermData::App(_, args) => stack.extend_from_slice(args),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, th, el) => {
                stack.push(*c);
                stack.push(*th);
                stack.push(*el);
            }
            TermData::Let(bindings, b) => {
                for (_, v) in bindings {
                    stack.push(*v);
                }
                stack.push(*b);
            }
            TermData::Forall(vars, b, _) | TermData::Exists(vars, b, _) => {
                if vars.iter().any(|(_, s)| is_rm_sort(s)) {
                    return true;
                }
                stack.push(*b);
            }
            _ => {}
        }
    }
    false
}
