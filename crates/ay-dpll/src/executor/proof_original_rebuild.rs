// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Rebuild a trust-bearing exported proof from the ORIGINAL problem
//! assertions.
//!
//! Preprocessing substitution (constant/definition propagation) rewrites the
//! assertion stack before the SAT layer clausifies it. The exported proof
//! then references the SUBSTITUTED assertion forms as leaves — terms that are
//! no longer problem assertions — and the demotion pass turns those `assume`
//! leaves into premiseless `:rule trust` steps (the "SAT layer materializes
//! input clauses as trust leaves" class), which no external checker accepts.
//!
//! Rather than trying to re-derive the substituted forms literal-by-literal
//! (substitution composes with arithmetic normalization, so the substituted
//! term is not recoverable by syntactic replay), this pass re-proves the
//! contradiction directly from the ORIGINAL problem assertions:
//!
//! 1. Find an original assertion `(or D1 .. Dn)` whose disjuncts are all
//!    linear-arithmetic literals, plus original assertions that are
//!    themselves linear literals (the "bounds", equalities included). The
//!    conjuncts of an original `(and C1 .. Cn)` are bounds too: each unit is
//!    DERIVED from the root's `assume` by strictly-validated `and_pos` +
//!    resolution steps, so no trust enters the proof (the multi-equality
//!    substitution class, e.g. `x = N ∧ y = 0` substituted into `N < x + y`
//!    leaves only the trust leaf `x < x`).
//! 2. Refute every disjunct `Di` against the bounds with a fresh LRA solver,
//!    demanding a Farkas certificate, and re-verify each certificate with the
//!    independent `verify_farkas_conflict_lits_full` checker (fail-closed).
//! 3. Emit `assume` steps for exactly the originals used, one certified
//!    `la_generic` theory lemma per refuted disjunct, the `or` decomposition,
//!    and a binary resolution chain to the empty clause.
//!
//! When there is no disjunction and no disequality to split on, the bounds
//! ALONE may be jointly infeasible (`try_rebuild_with_pure_bounds`): one
//! certified, independently re-verified Farkas lemma over the original
//! bounds closes the proof, gated by a whole-proof `check_proof_strict`
//! revert check with `trust_count == 0`.
//!
//! The pass runs at the very end of proof export and ONLY when the exported
//! derivation is defective: a `trust` step (or trust-kind theory lemma), an
//! `assume` of a non-original term, or an `assume` of an original whose
//! canonical form prints unlike the problem file with no surface override to
//! fix it (the trust-free normalized-assume class), REACHABLE from an
//! empty-clause step.
//! Proofs that are already fully derived from the original assertions are
//! untouched (byte-stability). If any part of the reconstruction
//! fails, the original proof is kept unchanged (fail-closed: the output is
//! never worse, and never a wrong proof step).

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{
    AletheRule, Constant, FarkasAnnotation, Proof, ProofId, ProofStep, Sort, Symbol, TermId,
    TermStore, TheoryLemmaKind, TheoryLit, TheoryResult, TheorySolver,
};
use ay_frontend::command::Term as FrontendTerm;
use num_bigint::BigInt;

use super::proof_surface_syntax::{
    collect_surface_term_overrides, strip_frontend_annotations, surface_override_map_is_bounded,
    surface_override_roots_have_bounded_work,
};
use super::proof_trust_surgery_provenance::OriginalSourceIndex;
use super::Executor;

fn collect_bounded_bv_lia_roots(
    terms: &TermStore,
    authored_roots: &[TermId],
) -> Option<Vec<TermId>> {
    let mut seen = HashSet::default();
    let mut roots = Vec::new();
    for &root in authored_roots {
        if terms.entry_stamp(root).is_none() || terms.sort(root) != &Sort::Bool {
            return None;
        }
        if matches!(terms.get(root), TermData::Const(Constant::Bool(true))) || !seen.insert(root) {
            continue;
        }
        if roots.len() == ay_proof::MAX_BV_LIA_QUERY_ROOTS {
            return None;
        }
        roots.push(root);
    }
    Some(roots)
}

/// How a single disjunct of the original disjunction gets eliminated.
enum DisjunctElimination {
    /// A bound assertion is the exact complementary literal of the disjunct:
    /// resolve the disjunct directly against that bound's `assume`.
    Unit { bound_idx: usize },
    /// A theory refutation: `Di ∧ bounds` is LRA/LIA-infeasible with a
    /// re-verified Farkas certificate. `blocking_clause` is the negation of
    /// the conflict literals: `¬Di` plus, for each bound the certificate
    /// uses, the complement of that bound (resolved away against the bound's
    /// `assume`).
    Lemma {
        blocking_clause: Vec<TermId>,
        farkas: FarkasAnnotation,
    },
}

/// An original problem assertion that is a linear-arithmetic DISEQUALITY —
/// canonical `(not (= s t))` over `Int`/`Real` — usable as the backbone of a
/// rebuilt proof via a synthesized `la_disequality` case split:
/// `(or (= s t) (not (<= s t)) (not (<= t s)))`. Covers both surface
/// `(not (= s t))` and binary `(distinct s t)` sugar (the latter needs a
/// `distinct_elim` + `equiv_pos1/2` bridge from the printed assume to the
/// canonical disequality literal).
struct DiseqCandidate {
    /// Index into `originals`.
    original_idx: usize,
    /// The canonical positive equality `(= s t)` under the negation.
    eq_term: TermId,
    /// Left operand of the equality (canonical order).
    lhs: TermId,
    /// Right operand of the equality (canonical order).
    rhs: TermId,
    /// The problem file spells the assertion `(distinct s t)` rather than
    /// `(not (= s t))`.
    surface_is_distinct: bool,
}

/// An original problem assertion usable as the disjunction backbone of the
/// rebuilt proof.
struct DisjunctionCandidate {
    /// Index into `originals`.
    original_idx: usize,
    /// Clause literals of the decomposition step (canonical or-disjuncts).
    disjuncts: Vec<TermId>,
    /// `or` for a surface `(or ...)`, `not_and` for a surface
    /// `(not (and ...))` whose canonical form is the De Morgan `or`.
    decomposition_rule: AletheRule,
    /// Surface form of each clause literal, aligned with `disjuncts`
    /// (re-elaboration-verified), for print overrides.
    surface_literals: Vec<FrontendTerm>,
}

/// Exact proof plan for the native-API sequence push-back ROW1 obligation.
///
/// The sequence encoder lowers
///
/// ```text
/// len = 0
/// not (value = select(store(array, read_index + len, value), read_index))
/// ```
///
/// to ordinary Int/array terms.  The sequence operator itself is no longer in
/// the load-bearing claim: a certified LIA implication first proves the two
/// indices equal, then the primitive guarded ROW1 axiom proves the selected
/// value.  Both assumptions are exact immutable authored roots.
struct AuthoredSeqPushBackRow1Plan {
    arithmetic_roots: Vec<TermId>,
    goal_negated: TermId,
    len_zero: TermId,
    len_chain_clause: Option<Vec<TermId>>,
    read_refl: TermId,
    add_eq: TermId,
    congruence_clause: Vec<TermId>,
    add_zero_eq: TermId,
    index_eq: TermId,
    index_chain_clause: Vec<TermId>,
    row_eq: TermId,
    row_clause: Vec<TermId>,
}

/// A linear-arithmetic bound usable by the rebuild backbones, together with
/// how its unit clause `(cl <literal>)` is DERIVED from an original problem
/// assertion.
struct BoundSpec {
    /// Index into `originals` of the assertion this bound comes from.
    original_idx: usize,
    /// The canonical bound literal.
    term: TermId,
    /// Positional path through the original's canonical `and`-tree down to
    /// the literal. Empty = the original IS the literal (assumed directly);
    /// non-empty = the unit is derived from the root's `assume` by one
    /// strictly-validated `and_pos` + resolution step per level.
    path: Vec<u32>,
    /// Surface form of the bound literal itself (the conjunct operand for a
    /// conjunct bound; the whole parsed assertion for a direct bound).
    surface: FrontendTerm,
    /// `Some((s, t))` when the problem file spells this bound
    /// `(distinct s t)` (canonical `(not (= s t))`): the disjunction backbone
    /// assumes the raw `distinct` application and bridges it via
    /// `distinct_elim` + `equiv_pos2`.
    distinct: Option<(TermId, TermId)>,
}

/// How the `la_disequality` path derives a bound's canonical unit WITHOUT
/// surface overrides (see the printing note in
/// `try_rebuild_with_diseq_split`).
enum DiseqBoundPlan {
    /// Assume `raw` (spelled exactly like the problem file). `bridge_atom` is
    /// `None` when `raw` IS the canonical literal, `Some(atom)` for an
    /// orientation flip bridged by a certified 2-literal `la_generic` lemma.
    Direct {
        raw: TermId,
        bridge_atom: Option<TermId>,
    },
    /// Assume the (fully surface-faithful) conjunction root and derive the
    /// literal with an `and_pos` + resolution chain.
    Conjunct,
}

/// Total `plan_eq` nodes one predicate bridge may explore.
///
/// The search is a fail-closed planner: exhausting the budget abandons the
/// rebuild and keeps the original proof, so this only trades recoverable
/// proofs for bounded planning time — never correctness. Sized to clear the
/// longest store-flat chains in the QF_AX division (60 links, each costing a
/// `trans` node plus a 3-argument congruence node) with a wide margin.
const EQ_PLAN_BUDGET: u32 = 200_000;

fn atom_of(terms: &TermStore, lit: TermId) -> TermId {
    match terms.get(lit) {
        TermData::Not(inner) => *inner,
        _ => lit,
    }
}

/// A (possibly negated) binary linear-arithmetic atom (`<,<=,>,>=,=`).
fn is_linear_literal(terms: &TermStore, lit: TermId) -> bool {
    let atom = atom_of(terms, lit);
    matches!(
        terms.get(atom),
        TermData::App(Symbol::Named(name), args)
            if args.len() == 2 && matches!(name.as_str(), "<" | "<=" | ">" | ">=" | "=")
    )
}

/// A Boolean variable, optionally negated. These literals need no theory
/// certificate: the disjunction rebuild may eliminate one directly against an
/// exact complementary authored unit.
fn is_boolean_atom_literal(terms: &TermStore, lit: TermId) -> bool {
    let atom = atom_of(terms, lit);
    matches!(terms.get(atom), TermData::Var(..)) && matches!(terms.sort(atom), Sort::Bool)
}

/// Head operator of a parsed assertion, for print-shape gating: the proof's
/// `assume` steps print with the problem file's surface syntax, so a bound
/// whose surface form is sugar the resolution chain cannot see through
/// (e.g. `(distinct x 1)` for the canonical `(not (= x 1))`) must be
/// rejected — the checker would fail to match the printed literals.
fn parsed_head(parsed: &FrontendTerm) -> Option<&str> {
    match strip_frontend_annotations(parsed) {
        FrontendTerm::App(name, _) => Some(name.as_str()),
        _ => None,
    }
}

/// The parsed-form sentinel the native API records for native assertions
/// (`api/solving/assertions.rs`): the assertion has NO surface syntax. The
/// rebuild then works from the assertion-stack term itself — the exact term
/// the proof bundle exports as the obligation — and skips every
/// surface-fidelity concern: there is no problem file to print-match, so the
/// canonical rendering IS the surface, and no overrides may be registered
/// (an override would print the sentinel string).
pub(in crate::executor) fn is_api_placeholder(parsed: &FrontendTerm) -> bool {
    matches!(
        strip_frontend_annotations(parsed),
        FrontendTerm::Symbol(name) if name == super::NATIVE_API_ASSERTION_PLACEHOLDER
    )
}

/// Head operator of a CANONICAL term — the placeholder-surface analogue of
/// [`parsed_head`] (`Not` prints as `not`).
fn canonical_head(terms: &TermStore, term: TermId) -> Option<String> {
    match terms.get(term) {
        TermData::Not(_) => Some("not".to_string()),
        TermData::App(Symbol::Named(name), _) => Some(name.clone()),
        _ => None,
    }
}

impl Executor {
    /// See the module docs. Runs after all other export passes; replaces the
    /// proof only when a fully-certified reconstruction from the original
    /// problem assertions succeeds.
    pub(super) fn rebuild_trust_leaf_proof_from_original_assertions(&mut self, proof: &mut Proof) {
        // (1) Re-elaborate the parsed assertion stack to recover the ORIGINAL
        // canonical assertion terms (the assertion stack itself may hold
        // substituted forms). Fail-closed on any assertion that does not
        // re-elaborate.
        let parsed_stack = self.ctx.assertions_parsed();
        // Three passes: this audit, the deep clone below, and re-elaboration.
        if !self.proof_source_work.spend(
            super::proof_trust_surgery_surface_audit::ProofSourcePass::OriginalAssertionRebuild,
            parsed_stack,
        ) {
            return;
        }
        let parsed_assertions: Vec<FrontendTerm> = parsed_stack.to_vec();
        if parsed_assertions.is_empty() {
            return;
        }
        // The provenance-aware ORIGINAL assertion stack, index-aligned with
        // `assertions_parsed` — preprocessing may rewrite `ctx.assertions` in
        // place (e.g. substitute-and-simplify to `true`), so the raw stack is
        // NOT a usable original source for surface-less assertions.
        let original_stack = self.proof_original_problem_assertions();
        // Keep an exact, index-aligned view of the immutable authored roots
        // for repairs that can reason directly over their syntax. In
        // particular, the complementary-literal repair must assume these
        // terms, not a comparison-normalized re-elaboration of the parsed
        // surface. A length mismatch is a provenance failure: leave this view
        // empty so that repair fails closed.
        let authored_originals: Vec<(TermId, FrontendTerm)> =
            if original_stack.len() == parsed_assertions.len() {
                original_stack
                    .iter()
                    .copied()
                    .zip(parsed_assertions.iter().cloned())
                    .collect()
            } else {
                Vec::new()
            };
        let mut originals: Vec<(TermId, FrontendTerm)> =
            Vec::with_capacity(parsed_assertions.len());
        for (idx, parsed) in parsed_assertions.iter().enumerate() {
            if is_api_placeholder(parsed) {
                // Native-API assertion: there is no surface form to
                // re-elaborate. The provenance-tracked original stack entry
                // is the term the caller asserted — the obligation this proof
                // must derive from. Fail-closed on any misalignment.
                let Some(&canonical) = original_stack.get(idx) else {
                    return;
                };
                originals.push((canonical, parsed.clone()));
                continue;
            }
            let stripped = strip_frontend_annotations(parsed);
            let Some(canonical) = self.ctx.elaborate_surface_subterm(stripped) else {
                return;
            };
            originals.push((canonical, parsed.clone()));
        }

        // Capture the re-elaborated original terms for the leak-2 provenance
        // gate (`proof_legit_assume_set`). Re-elaborating a `forall` surface
        // mints fresh binder terms, so the surgery-inserted `assume` steps
        // carry THESE canonical ids — not `ctx.assertions` / `rec.original` —
        // and the gate must accept them. Captured once here (stable within the
        // solve); the trust surgery below reuses this exact `originals` list.
        self.last_proof_rebuild_originals = originals.iter().map(|(c, _)| *c).collect();

        // Also capture the recursively RAW re-interned form of each parsed
        // original. The fold-to-`false` reconstructions assume exact source
        // syntax, not a shallow top-level app whose children have already
        // folded (which could silently authorize `(distinct x y z)` for the
        // actual source `(distinct (ite true x w) y z)`). A foreign injected
        // axiom is never a parsed assertion, so it is never added here.
        //
        // #raw-intern-head-cliff — this used to run only for a hand-maintained
        // list of ten top-level heads (`and or not => distinct = < <= > >=`).
        // That list carried NO safety and was a pure coverage cliff:
        // `raw_intern_surface` recurses through EVERY child with
        // `raw_intern_surface` itself and fails closed per node (`?` on any
        // shape it cannot rebuild), so the "shallow top-level app whose
        // children have already folded" hazard the comment above describes is
        // not reachable — the children are raw by construction, never folded.
        //
        // What the list did instead was silently drop the grant for any
        // authored assertion with another head. `(assert (ite ...))`,
        // `(assert (bvult ...))`, `(assert (xor ...))` and every other theory
        // predicate therefore lost `assume` authority, and the mandatory strict
        // certification rejected the whole refutation as an unauthorized
        // assumption — turning a CORRECT `unsat` into `unknown`.
        //
        // Decisive lever on a 4-assertion QF_UFBV file that is plainly unsat
        // (`(assert (ite b (= x #x01) (= x #x02)))` + `(assert (bvult x #x01))`
        // + two more): as written it reports
        //   "step t2 assumes term t40 outside the supplied problem obligation"
        //   -> unknown
        // Wrapping every non-listed assertion as `(or <orig> false)` — which the
        // elaborator folds straight back, so the canonical terms are unchanged
        // and only the PARSED head differs — reports `unsat`.
        //
        // The grant is unchanged in kind: it authorizes the raw re-intern of an
        // assertion THE AUTHOR WROTE, and a foreign injected axiom is never a
        // parsed assertion so it is still never added here.
        for (_, parsed) in &originals {
            if !matches!(strip_frontend_annotations(parsed), FrontendTerm::App(_, _)) {
                continue;
            }
            if let Some(raw) = self.raw_intern_surface(parsed) {
                self.last_proof_rebuild_originals.push(raw);
            }
        }

        // Preprocessor fold-to-`false` collapse (`(distinct x x)`, `(= 1 2)`,
        // `(and p (not p))`): the degenerate `:rule false` export is replaced
        // by a certified derivation rebuilt from the parsed original
        // assertion's shape. Runs before the trust triggers below — the
        // collapse shape carries no trust step, only the misused `false`
        // rule. Fail-closed (whole-proof shape gated); see
        // `try_rebuild_false_collapse`.
        if self.try_rebuild_false_collapse(proof, &originals, &authored_originals, false) {
            return;
        }

        // (0) Only proofs whose EXPORTED derivation is defective are
        // candidates: a `trust` step, a trust-kind theory lemma, or an
        // `assume` of a term that is NOT an original problem assertion
        // (preprocessing-substituted forms no external checker can match to
        // the problem's premises) must be REACHABLE from an empty-clause step
        // (dead steps are not printed). Anything already fully derived from
        // the original assertions is left byte-identical.
        let trust_report = ay_proof::terminal_trust_report(proof);
        let has_reachable_trust =
            trust_report.trust_rule_on_path > 0 || trust_report.trust_theory_lemma_on_path > 0;
        if !has_reachable_trust
            && !Self::reachable_non_original_assume(proof, &originals)
            && !self.reachable_normalized_assume(proof, &originals)
        {
            return;
        }

        // A syntactic contradiction between exact authored roots is already a
        // complete strict proof.  Prefer that proof before any partial
        // trust-surgery route can claim the input and return a proof that only
        // a later promotion *might* finish.  The public UNSAT boundary now
        // requires a fully strict certificate, so letting a partial route mask
        // this exact propositional closure incorrectly downgrades a certifiable
        // UNSAT to `unknown`.
        if !authored_originals.is_empty()
            && self.try_rebuild_with_complementary_literals(proof, &authored_originals)
        {
            return;
        }

        // Native sequence push-back ROW1 closure.  The preceding solver proof
        // can end in a Generic fallback that negates every generated array
        // theorem, even though the ORIGINAL VC has a tiny strict derivation:
        // an authored `len = 0` makes the store/read indices equal, guarded
        // ROW1 yields the selected value, and the authored disequality closes.
        // Consume only the immutable, index-aligned authored roots assembled
        // above; a preprocessed/injected equality is never eligible.
        let authenticated_terms: Vec<TermId> =
            authored_originals.iter().map(|(term, _)| *term).collect();
        if !authenticated_terms.is_empty()
            && self.try_rebuild_authenticated_seq_push_back_row1(proof, &authenticated_terms)
        {
            return;
        }

        // (2) Classify the originals: candidate disjunctions and unit bounds.
        // Every candidate carries the surface form of each of its clause
        // literals, so the printed proof matches the problem file exactly.
        // A bound's surface head must be a plain literal shape (`not` or a
        // binary comparison) so the printed `assume` matches the literals the
        // lemma/resolution steps use (e.g. `(distinct x 1)` sugar is
        // rejected — its printed form would not resolve against `(= x 1)`).
        let mut disjunctions: Vec<DisjunctionCandidate> = Vec::new();
        let mut bound_specs: Vec<BoundSpec> = Vec::new();
        let mut diseqs: Vec<DiseqCandidate> = Vec::new();
        // Original indices whose surface is an `(and ...)` tree of usable
        // linear literals ALL of which re-intern raw-faithfully — the
        // precondition for the override-free `la_disequality` path to assume
        // the root (its print must match the problem file byte-for-byte).
        let mut conjunct_root_faithful: HashMap<usize, bool> = HashMap::default();
        for (idx, (canonical, parsed)) in originals.iter().enumerate() {
            // Placeholder (native-API) assertions have no surface head; gate
            // on the canonical term's own head instead.
            let head: Option<String> = if is_api_placeholder(parsed) {
                canonical_head(&self.ctx.terms, *canonical)
            } else {
                parsed_head(parsed).map(str::to_string)
            };
            let Some(head) = head else {
                continue;
            };
            let head = head.as_str();
            if let Some(cand) = self.recognize_diseq_candidate(idx, *canonical, parsed, head) {
                if cand.surface_is_distinct {
                    // A binary `(distinct s t)` bound is usable by the
                    // disjunction rebuild too: it is assumed as the raw
                    // `distinct` application (printed exactly like the
                    // problem file) and bridged to the canonical
                    // `(not (= s t))` literal via `distinct_elim` +
                    // `equiv_pos2` (its printed sugar cannot resolve against
                    // `(= s t)` directly).
                    bound_specs.push(BoundSpec {
                        original_idx: idx,
                        term: *canonical,
                        path: Vec::new(),
                        surface: parsed.clone(),
                        distinct: Some((cand.lhs, cand.rhs)),
                    });
                }
                diseqs.push(cand);
            }
            if (is_linear_literal(&self.ctx.terms, *canonical)
                || is_boolean_atom_literal(&self.ctx.terms, *canonical))
                && matches!(head, "not" | "<" | "<=" | ">" | ">=" | "=")
            {
                bound_specs.push(BoundSpec {
                    original_idx: idx,
                    term: *canonical,
                    path: Vec::new(),
                    surface: parsed.clone(),
                    distinct: None,
                });
                continue;
            }
            if head == "and" {
                // The conjuncts of an original `(and ...)` are bounds too
                // (the multi-equality substitution class): each unit is
                // DERIVED from the root's assume by strictly-validated
                // `and_pos` + resolution steps — no trust enters the proof.
                // A placeholder (native-API) root has no surface to align:
                // its canonical structure is walked directly, and it is
                // trivially print-faithful (canonical rendering IS its only
                // spelling).
                let (specs, fully_faithful) = if is_api_placeholder(parsed) {
                    self.collect_conjunct_bound_specs_canonical(idx, *canonical, parsed)
                } else {
                    self.collect_conjunct_bound_specs(idx, *canonical, parsed)
                };
                if !specs.is_empty() {
                    conjunct_root_faithful.insert(idx, fully_faithful);
                    bound_specs.extend(specs);
                }
                continue;
            }
            let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(*canonical) else {
                continue;
            };
            if name != "or" || args.len() < 2 {
                continue;
            }
            let disjuncts = args.clone();
            if !disjuncts.iter().all(|&d| {
                is_linear_literal(&self.ctx.terms, d) || is_boolean_atom_literal(&self.ctx.terms, d)
            }) {
                continue;
            }
            // Distinct pivot atoms keep the resolution chain unambiguous (a
            // duplicated/complementary atom would make the per-disjunct pivot
            // elimination remove the wrong number of literals).
            let mut atoms: Vec<TermId> = disjuncts
                .iter()
                .map(|&d| atom_of(&self.ctx.terms, d))
                .collect();
            atoms.sort_unstable();
            atoms.dedup();
            if atoms.len() != disjuncts.len() {
                continue;
            }
            // A placeholder (native-API) disjunction has no surface: it
            // decomposes with the plain `or` rule and registers no literal
            // overrides (everything prints canonically).
            if is_api_placeholder(parsed) {
                disjunctions.push(DisjunctionCandidate {
                    original_idx: idx,
                    disjuncts,
                    decomposition_rule: AletheRule::Or,
                    surface_literals: Vec::new(),
                });
                continue;
            }
            // Match the canonical `or` against the SURFACE shape: a literal
            // `(or ...)` decomposes with the Alethe `or` rule; a De
            // Morgan-canonicalized `(not (and A1 .. An))` decomposes with
            // `not_and` (clause literal i = `(not Ai)`). Each surface literal
            // must re-elaborate to exactly the corresponding canonical
            // disjunct, so the printed step literals are byte-faithful to the
            // problem file.
            let stripped = strip_frontend_annotations(parsed);
            let surface_literals: Vec<FrontendTerm> = match stripped {
                FrontendTerm::App(op, operands) if op == "or" => operands.clone(),
                FrontendTerm::App(op, operands) if op == "not" && operands.len() == 1 => {
                    match strip_frontend_annotations(&operands[0]) {
                        FrontendTerm::App(inner_op, conj) if inner_op == "and" => conj
                            .iter()
                            .map(|c| FrontendTerm::App("not".to_string(), vec![c.clone()]))
                            .collect(),
                        _ => continue,
                    }
                }
                _ => continue,
            };
            if surface_literals.len() != disjuncts.len() {
                continue;
            }
            let mut aligned = true;
            for (surface, &canonical_lit) in surface_literals.iter().zip(disjuncts.iter()) {
                if self.ctx.elaborate_surface_subterm(surface) != Some(canonical_lit) {
                    aligned = false;
                    break;
                }
            }
            if !aligned {
                continue;
            }
            // The decomposition rule must describe the PREMISE this step is
            // actually given, and that premise is the CANONICAL assertion term
            // (`originals[idx].0`, assumed at `try_rebuild_with_disjunction`),
            // which the guard above has already forced to be `App("or", ..)`.
            //
            // Selecting `not_and` from the SURFACE shape made the step
            // self-inconsistent: `validate_not_and` requires a `(not (and ..))`
            // premise and the premise is an `or`, so every De Morgan-canonicalized
            // assertion produced an unusable step ("premise must be (not (and
            // ...))"). Surface fidelity is carried by `surface_literals`, which
            // is what re-prints the literals byte-faithfully; it does not change
            // which term the premise holds.
            let decomposition_rule = AletheRule::Or;
            disjunctions.push(DisjunctionCandidate {
                original_idx: idx,
                disjuncts,
                decomposition_rule,
                surface_literals,
            });
        }

        for candidate in &disjunctions {
            if self.try_rebuild_with_disjunction(proof, &originals, candidate, &bound_specs) {
                return;
            }
        }

        // No explicit disjunction backbone: try a SYNTHESIZED case split on an
        // original linear disequality via `la_disequality` (the
        // disequality-bound refutation class: `x ≠ k ∧ k ≤ x ≤ k → ⊥` cannot
        // be expressed by a single Farkas combination, but splits into
        // `(= s t) ∨ ¬(s ≤ t) ∨ ¬(t ≤ s)`, each disjunct refuted against the
        // bounds by its own certified `la_generic` lemma).
        for candidate in &diseqs {
            if self.try_rebuild_with_diseq_split(
                proof,
                &originals,
                candidate,
                &bound_specs,
                &conjunct_root_faithful,
            ) {
                return;
            }
        }

        // Multi-equality Farkas class: the bounds ALONE may be
        // jointly infeasible — preprocessing substituted the equalities into
        // the remaining assertion and collapsed the whole contradiction into
        // a premiseless trust leaf. One certified,
        // independently re-verified Farkas lemma over the original bounds
        // closes the proof. Try this complete strict reconstruction before the
        // partial skeleton surgery below: a partial rewrite can retain a
        // Generic leaf for a later promotion and must not mask a certificate
        // that is already complete at this point.
        if self.try_rebuild_with_pure_bounds(proof, &originals, &bound_specs) {
            return;
        }

        // No full-rebuild backbone applies: the exported RESOLUTION skeleton
        // may still be sound with only local defects (n-ary distinct assumes,
        // normalized-bounds assumes, Int trichotomy trust lemmas). Try the
        // insert-and-remap surgery, which keeps the skeleton and replaces
        // each defective site with a certified derivation (fail-closed).
        if self.try_rebuild_with_trust_surgery(proof, &originals) {
            return;
        }

        // Truly-final resort (complementary-literal propositional closure —
        // the level-0 EUF/interned-enum root-conflict class): the assertions
        // contradict SYNTACTICALLY, e.g. `(and .. (= tee c) ..)` against
        // `(and (not (= tee c)) ..)` (an inductive-invariant initiation over
        // an int-coded string enum), where ay-dpll's preprocessor found the
        // complementary pair at level 0 and certified `⊥` with a terminal
        // trust fallback no Farkas backbone can replace (a disequality is not
        // a Farkas premise). The closure is purely propositional — `assume` +
        // `and_pos`/`or` extraction + `resolution`, every rule already
        // strictly validated — so it is theory-independent and cannot mint a
        // false proof: it only exists when the complementary pair is really
        // asserted. Runs dead last so every previously-working backbone keeps
        // producing byte-identical output.
        if !authored_originals.is_empty()
            && self.try_rebuild_with_complementary_literals(proof, &authored_originals)
        {
            return;
        }

        // THEORY-AGNOSTIC last pass (the substitution-derived `assume` class):
        // every backbone above re-proves the contradiction with an ARITHMETIC
        // certificate, so a non-arithmetic refutation whose only defect is a
        // preprocessing-substituted `assume` leaf (the whole QF_S "sink"
        // family: `(str.in_re literal_5 R)` exported as
        // `(str.in_re "/mod/forum/" R)` after constant propagation) reaches
        // here untouched. Keep the exported resolution SKELETON and replace
        // just those leaves with an `eq_congruent_pred` bridge from the
        // AUTHORED assertion plus the defining equalities. Fail-closed.
        self.try_rebuild_with_substitution_bridge(proof, &originals);

        // A premise-bound trust step is useful only when every checkable
        // reconstruction in this pass has declined. In particular, committing
        // that fallback before the arithmetic planners masks the externally
        // checkable `la_disequality` proof for a conjoined-equalities collapse.
        // The later authored cascade may still replace this honest fallback;
        // the internal BV/LIA fallback runs after that cascade.
        let _ = self.try_rebuild_false_collapse(proof, &originals, &authored_originals, true);

        // NOTE: the internal-certificate BV/LIA fallback deliberately does NOT
        // run here. This function executes EARLY in proof publication (from
        // `apply_input_syntax_rewrites_to_proof`), before the authored
        // replacement cascade — which includes
        // `replace_with_exact_authored_bv_refutation`, the pass that emits a
        // REAL, externally surfaceable `bv_bitblast` certificate. Running the
        // internal fallback here once silently downgraded a pure QF_BV
        // commutativity refutation from a strict `BvBitBlast` lemma to a
        // `BvLiaTautology` step that renders as an honest `hole` on the Alethe
        // wire (the cascade's strict gate then saw a valid proof and declined
        // to touch it). The fallback is invoked as the TRUE last resort in
        // `build_unsat_proof`, after `run_authored_replacement_cascade`; see
        // `rebuild_authenticated_bv_lia_internal_certificate_last_resort`.
    }

    /// Final internal-certificate fallback for exact mixed Bool/Int/BV source
    /// queries — the TRUE last resort of proof publication.
    ///
    /// Runs only after every ordinary Alethe reconstruction (including the
    /// authored replacement cascade) has had first refusal: the pinned
    /// external checker cannot parse `bv2nat`, while AY's bounded source
    /// interpreter can independently re-decide a narrow finite query. The
    /// candidate is still an ordinary assume + tautology + resolution proof,
    /// and both its premise scope and every step are replayed before
    /// replacement; a proof that is already strict-complete over the authored
    /// scope is preserved byte-identically.
    pub(super) fn rebuild_authenticated_bv_lia_internal_certificate_last_resort(
        &mut self,
        proof: &mut Proof,
    ) {
        let authenticated_terms = self.authenticated_authored_roots_for_internal_certificate();
        if !authenticated_terms.is_empty() {
            self.try_rebuild_authenticated_bv_lia_refutation(proof, &authenticated_terms);
        }
    }

    /// Replace a still-defective proof with a bounded semantic tautology over
    /// exact immutable authored roots.
    fn try_rebuild_authenticated_bv_lia_refutation(
        &mut self,
        proof: &mut Proof,
        authenticated_authored_roots: &[TermId],
    ) -> bool {
        // Preserve a proof that an earlier, externally surfaceable rebuild has
        // already completed. Scope validation is separate from rule replay:
        // a syntactically valid proof with a foreign assume is not
        // authoritative — but "not foreign" is exactly what the leak-2
        // provenance authority `proof_legit_assume_set` decides (canonical
        // originals, and-conjuncts, the re-elaborated/raw-re-interned grants in
        // `last_proof_rebuild_originals`, quantifier-expansion premises), and
        // the strict authority for the existing proof is the datatype-aware
        // checker the publication gates themselves consult. Checking a
        // NARROWER scope or the datatype-blind checker here once replaced
        // strict `BvBitBlast` certificates from `promote_bv_identity_collapse`
        // and `DatatypeSelectorProject` lemmas with internal `BvLiaTautology`
        // steps that render as holes on the Alethe wire. The wider scope can
        // only ever DECLINE a replacement, never authorize one: the candidate
        // built below remains authorized against the narrow
        // `authenticated_authored_roots` slice alone.
        let preservation_scope: Vec<TermId> = self.proof_legit_assume_set().into_iter().collect();
        if ay_proof::validate_reachable_assumes_in_problem_scope(proof, &preservation_scope).is_ok()
            && self
                .check_proof_strict_with_datatypes(proof)
                .is_ok_and(|quality| quality.is_complete())
            && Self::proof_derives_empty_clause(proof)
        {
            return false;
        }

        // `true` contributes nothing to a conjunction and creates an awkward
        // constant pivot. Deduplicate exact TermIds in linear time and stop as
        // soon as the independent checker's root bound is exceeded. No
        // rewritten/generated root is admitted.
        let Some(mut roots) =
            collect_bounded_bv_lia_roots(&self.ctx.terms, authenticated_authored_roots)
        else {
            return false;
        };
        if roots.is_empty() {
            return false;
        }
        let kind = match ay_proof::authenticate_bv_lia_unsat_query(&self.ctx.terms, &roots, None) {
            Ok(_) => TheoryLemmaKind::BvLiaTautology,
            Err(error) if error.is_capability_decline() => {
                let Some(subset) = ay_proof::recognize_seq_extensional_companion_contradiction(
                    &self.ctx.terms,
                    &roots,
                ) else {
                    return false;
                };
                roots = subset.into();
                TheoryLemmaKind::SeqExtensionalCompanionContradiction
            }
            Err(_) => return false,
        };

        let Some(candidate) =
            self.build_authenticated_bv_lia_refutation(&roots, kind, authenticated_authored_roots)
        else {
            return false;
        };

        *proof = candidate;
        true
    }

    /// Build and independently replay the exact internal certificate used by
    /// the last-resort BV/LIA and sequence-extensionality lanes.
    ///
    /// `authenticated_scope` is the complete immutable public query, while
    /// `roots` is the independently recognized, load-bearing theorem subset.
    /// Requiring every selected root to remain reachable prevents a recognizer
    /// bug from silently authorizing a proof over a weaker subset.
    fn build_authenticated_bv_lia_refutation(
        &mut self,
        roots: &[TermId],
        kind: TheoryLemmaKind,
        authenticated_scope: &[TermId],
    ) -> Option<Proof> {
        if roots.is_empty() {
            return None;
        }
        let mut candidate = Proof::new();
        let assumes: Vec<ProofId> = roots
            .iter()
            .map(|&root| candidate.add_assume(root, None))
            .collect();
        let mut residual: Vec<TermId> = roots
            .iter()
            .map(|&root| self.ctx.terms.mk_not_raw(root))
            .collect();
        let mut current = candidate.add_step(ProofStep::TheoryLemma {
            theory: "BV_LIA".to_string(),
            clause: residual.clone(),
            farkas: None,
            kind,
            lia: None,
        });
        for (&root, &assume) in roots.iter().zip(assumes.iter()) {
            let complement = self.ctx.terms.mk_not_raw(root);
            let before = residual.len();
            residual.retain(|&literal| literal != complement);
            if residual.len() + 1 != before {
                return None;
            }
            current = candidate.add_resolution(residual.clone(), root, current, assume);
        }
        if !residual.is_empty() {
            return None;
        }

        if ay_proof::validate_reachable_assumes_in_problem_scope(&candidate, authenticated_scope)
            .is_err()
        {
            return None;
        }
        // Scope validation above rejects foreign leaves. Removing each
        // selected root in turn proves the converse: every selected theorem
        // premise is reachable from the empty clause and therefore
        // load-bearing in this exact candidate.
        for omitted in 0..roots.len() {
            let reduced: Vec<TermId> = roots
                .iter()
                .enumerate()
                .filter_map(|(index, &root)| (index != omitted).then_some(root))
                .collect();
            if ay_proof::validate_reachable_assumes_in_problem_scope(&candidate, &reduced).is_ok() {
                return None;
            }
        }
        let Ok(quality) = ay_proof::check_proof_strict(&candidate, &self.ctx.terms) else {
            return None;
        };
        if !quality.is_complete() || !Self::proof_derives_empty_clause(&candidate) {
            return None;
        }
        Some(candidate)
    }

    /// Replace a trust-bearing sequence push-back proof with the exact
    /// LIA+ROW1 derivation described by [`AuthoredSeqPushBackRow1Plan`].
    ///
    /// Authority is deliberately an argument, not the live assertion stack:
    /// the sole production caller supplies the immutable, provenance-aligned
    /// authored roots.  Every reachable `Assume` is checked against that exact
    /// slice again before the candidate is committed.
    fn try_rebuild_authenticated_seq_push_back_row1(
        &mut self,
        proof: &mut Proof,
        authenticated_authored_roots: &[TermId],
    ) -> bool {
        let Some(plan) = self.plan_authenticated_seq_push_back_row1(authenticated_authored_roots)
        else {
            return false;
        };

        let mut candidate = Proof::new();
        let arithmetic_assumes: Vec<ProofId> = plan
            .arithmetic_roots
            .iter()
            .map(|&root| candidate.add_assume(root, None))
            .collect();
        let goal_assume = candidate.add_assume(plan.goal_negated, None);

        // First compose the exact authored length equalities with ordinary
        // EUF transitivity. A direct authored `len = 0` is already the unit;
        // the TrustWP shape uses two roots (`seed = 0`, `seed = len`).
        let len_zero_unit = if let Some(len_chain_clause) = &plan.len_chain_clause {
            let mut residual = len_chain_clause.clone();
            let mut current = candidate.add_rule_step(
                AletheRule::EqTransitive,
                residual.clone(),
                Vec::new(),
                Vec::new(),
            );
            for (&root, &assume) in plan.arithmetic_roots.iter().zip(arithmetic_assumes.iter()) {
                let negated = self.ctx.terms.mk_not_raw(root);
                residual.retain(|&literal| literal != negated);
                current = candidate.add_resolution(residual.clone(), root, assume, current);
            }
            if residual != [plan.len_zero] {
                return false;
            }
            current
        } else {
            if plan.arithmetic_roots.len() != 1 || plan.arithmetic_roots[0] != plan.len_zero {
                return false;
            }
            arithmetic_assumes[0]
        };

        // Transport `len = 0` through the second argument of `+`. Strict
        // eq_congruent requires an explicit equality for every position, so
        // the unchanged read-index argument has its own raw reflexive proof.
        let refl_unit = candidate.add_rule_step(
            AletheRule::EqReflexive,
            vec![plan.read_refl],
            Vec::new(),
            Vec::new(),
        );
        let congruence = candidate.add_rule_step(
            AletheRule::EqCongruent,
            plan.congruence_clause.clone(),
            Vec::new(),
            Vec::new(),
        );
        let not_read_refl = self.ctx.terms.mk_not_raw(plan.read_refl);
        let mut congruence_residual = plan.congruence_clause.clone();
        congruence_residual.retain(|&literal| literal != not_read_refl);
        let congruence_no_refl = candidate.add_resolution(
            congruence_residual.clone(),
            plan.read_refl,
            refl_unit,
            congruence,
        );
        let not_len_zero = self.ctx.terms.mk_not_raw(plan.len_zero);
        congruence_residual.retain(|&literal| literal != not_len_zero);
        let add_eq_unit = candidate.add_resolution(
            congruence_residual.clone(),
            plan.len_zero,
            len_zero_unit,
            congruence_no_refl,
        );
        if congruence_residual != [plan.add_eq] {
            return false;
        }

        // `read_index + 0 = read_index` is a checked linear identity. EUF
        // transitivity then combines it with congruence to derive the exact
        // equality used as ROW1's guard.
        let add_zero_unit = candidate.add_step(ProofStep::TheoryLemma {
            theory: "LIA".to_string(),
            clause: vec![plan.add_zero_eq],
            farkas: Some(FarkasAnnotation::from_ints(&[1])),
            kind: TheoryLemmaKind::LiaGeneric,
            lia: Some(ay_core::LiaAnnotation::LinearIdentity),
        });
        let mut index_residual = plan.index_chain_clause.clone();
        let mut index_unit = candidate.add_rule_step(
            AletheRule::EqTransitive,
            index_residual.clone(),
            Vec::new(),
            Vec::new(),
        );
        for (edge, unit) in [
            (plan.add_eq, add_eq_unit),
            (plan.add_zero_eq, add_zero_unit),
        ] {
            let negated = self.ctx.terms.mk_not_raw(edge);
            index_residual.retain(|&literal| literal != negated);
            index_unit = candidate.add_resolution(index_residual.clone(), edge, unit, index_unit);
        }
        if index_residual != [plan.index_eq] {
            return false;
        }

        // Only after the index equality has been derived do we instantiate
        // guarded ROW1.  Resolving its exact guard produces the equality that
        // is complementary to the authored proof-assert goal.
        let row_lemma = candidate.add_step(ProofStep::TheoryLemma {
            theory: "array".to_string(),
            clause: plan.row_clause.clone(),
            farkas: None,
            kind: TheoryLemmaKind::ArraySelectStore { index_eq: true },
            lia: None,
        });
        let row_unit =
            candidate.add_resolution(vec![plan.row_eq], plan.index_eq, index_unit, row_lemma);
        candidate.add_resolution(Vec::new(), plan.row_eq, row_unit, goal_assume);

        // Two independent gates: exact premise authorization, then semantic
        // replay of every proof step.  A future recognizer/checker mismatch or
        // an accidentally broadened scan leaves the old trust proof visible.
        if ay_proof::validate_reachable_assumes_in_problem_scope(
            &candidate,
            authenticated_authored_roots,
        )
        .is_err()
        {
            return false;
        }
        let Ok(quality) = ay_proof::check_proof_strict(&candidate, &self.ctx.terms) else {
            return false;
        };
        if !quality.is_complete() || !Self::proof_derives_empty_clause(&candidate) {
            return false;
        }

        *proof = candidate;
        true
    }

    /// Recognize the narrow authored sequence/array obligation and construct
    /// its independently checkable arithmetic and ROW1 lemmas.
    fn plan_authenticated_seq_push_back_row1(
        &mut self,
        authenticated_authored_roots: &[TermId],
    ) -> Option<AuthoredSeqPushBackRow1Plan> {
        for &goal_negated in authenticated_authored_roots {
            let TermData::Not(row_eq) = self.ctx.terms.get(goal_negated).clone() else {
                continue;
            };
            let TermData::App(Symbol::Named(eq_name), eq_args) = self.ctx.terms.get(row_eq).clone()
            else {
                continue;
            };
            if eq_name != "=" || eq_args.len() != 2 {
                continue;
            }

            // Accept either equality orientation, but require the selected
            // array to be the exact depth-one store and the other endpoint to
            // be the exact stored value.
            for (select_term, value) in [(eq_args[0], eq_args[1]), (eq_args[1], eq_args[0])] {
                let TermData::App(Symbol::Named(select_name), select_args) =
                    self.ctx.terms.get(select_term).clone()
                else {
                    continue;
                };
                if select_name != "select" || select_args.len() != 2 {
                    continue;
                }
                let stored_array = select_args[0];
                let read_index = select_args[1];
                let TermData::App(Symbol::Named(store_name), store_args) =
                    self.ctx.terms.get(stored_array).clone()
                else {
                    continue;
                };
                if store_name != "store" || store_args.len() != 3 || store_args[2] != value {
                    continue;
                }
                let store_index = store_args[1];
                if store_index == read_index
                    || !matches!(self.ctx.terms.sort(store_index), Sort::Int)
                    || !matches!(self.ctx.terms.sort(read_index), Sort::Int)
                {
                    continue;
                }

                // The supported lowering is exactly `read_index + len` (in
                // either commutative operand order).  Wider index expressions
                // remain outside this lane even if an arithmetic solver could
                // happen to prove them.
                let TermData::App(Symbol::Named(add_name), add_args) =
                    self.ctx.terms.get(store_index).clone()
                else {
                    continue;
                };
                if add_name != "+" || add_args.len() != 2 {
                    continue;
                }
                let len = if add_args[0] == read_index {
                    add_args[1]
                } else if add_args[1] == read_index {
                    add_args[0]
                } else {
                    continue;
                };
                if !matches!(self.ctx.terms.sort(len), Sort::Int) {
                    continue;
                }

                // Candidate exact authored arithmetic subsets.  The direct
                // form is `len = 0`.  The two-link form is `seed = 0` plus
                // `seed = len` (all orientations accepted).  This is the
                // actual TrustWP VC shape (`len17 = 0`, `len17 = len21`).
                // Nothing from the preprocessed assertion stack participates.
                let zero_matches = |terms: &TermStore, term: TermId| {
                    matches!(
                        terms.get(term),
                        TermData::Const(Constant::Int(value)) if value == &BigInt::from(0_u8)
                    )
                };
                let mut zero_seeds: Vec<(TermId, TermId, TermId)> = Vec::new();
                for &root in authenticated_authored_roots {
                    let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(root).clone()
                    else {
                        continue;
                    };
                    if name != "=" || args.len() != 2 {
                        continue;
                    }
                    if zero_matches(&self.ctx.terms, args[0])
                        && matches!(self.ctx.terms.sort(args[1]), Sort::Int)
                    {
                        zero_seeds.push((root, args[1], args[0]));
                    } else if zero_matches(&self.ctx.terms, args[1])
                        && matches!(self.ctx.terms.sort(args[0]), Sort::Int)
                    {
                        zero_seeds.push((root, args[0], args[1]));
                    }
                }
                let mut arithmetic_root_sets: Vec<(
                    Vec<TermId>,
                    TermId,
                    TermId,
                    Option<Vec<TermId>>,
                )> = Vec::new();
                for &(zero_root, seed, zero) in &zero_seeds {
                    if seed == len {
                        arithmetic_root_sets.push((vec![zero_root], zero, zero_root, None));
                        continue;
                    }
                    for &link_root in authenticated_authored_roots {
                        if link_root == zero_root {
                            continue;
                        }
                        let TermData::App(Symbol::Named(link_name), link_args) =
                            self.ctx.terms.get(link_root).clone()
                        else {
                            continue;
                        };
                        if link_name == "="
                            && link_args.len() == 2
                            && ((link_args[0] == seed && link_args[1] == len)
                                || (link_args[1] == seed && link_args[0] == len))
                        {
                            let len_zero =
                                self.ctx
                                    .terms
                                    .mk_app(Symbol::named("="), [len, zero], Sort::Bool);
                            let len_chain_clause = vec![
                                self.ctx.terms.mk_not_raw(zero_root),
                                self.ctx.terms.mk_not_raw(link_root),
                                len_zero,
                            ];
                            arithmetic_root_sets.push((
                                vec![zero_root, link_root],
                                zero,
                                len_zero,
                                Some(len_chain_clause),
                            ));
                        }
                    }
                }

                let index_eq = self.ctx.terms.mk_app(
                    Symbol::named("="),
                    [store_index, read_index],
                    Sort::Bool,
                );
                for (arithmetic_roots, zero, len_zero, len_chain_clause) in arithmetic_root_sets {
                    // Replace the exact `len` argument with the authenticated
                    // zero term while preserving the original `+` argument
                    // order.  Congruence premises are emitted in that same
                    // positional order.
                    let mut zero_add_args = add_args.clone();
                    let Some(len_position) = zero_add_args.iter().position(|&arg| arg == len)
                    else {
                        continue;
                    };
                    if len == read_index {
                        continue;
                    }
                    zero_add_args[len_position] = zero;
                    let add_zero =
                        self.ctx
                            .terms
                            .mk_app(Symbol::named("+"), zero_add_args.clone(), Sort::Int);
                    let add_eq = self.ctx.terms.mk_app(
                        Symbol::named("="),
                        [store_index, add_zero],
                        Sort::Bool,
                    );
                    let read_refl = self.ctx.terms.mk_app(
                        Symbol::named("="),
                        [read_index, read_index],
                        Sort::Bool,
                    );
                    let mut congruence_clause: Vec<TermId> = Vec::with_capacity(3);
                    for position in 0..add_args.len() {
                        let premise = if position == len_position {
                            len_zero
                        } else if add_args[position] == read_index
                            && zero_add_args[position] == read_index
                        {
                            read_refl
                        } else {
                            congruence_clause.clear();
                            break;
                        };
                        congruence_clause.push(self.ctx.terms.mk_not_raw(premise));
                    }
                    if congruence_clause.len() != add_args.len() {
                        continue;
                    }
                    congruence_clause.push(add_eq);

                    let add_zero_eq = self.ctx.terms.mk_app(
                        Symbol::named("="),
                        [add_zero, read_index],
                        Sort::Bool,
                    );
                    if !ay_core::proof_validation::recognize_lia_linear_identity(
                        &self.ctx.terms,
                        &[add_zero_eq],
                    ) {
                        continue;
                    }
                    let index_chain_clause = vec![
                        self.ctx.terms.mk_not_raw(add_eq),
                        self.ctx.terms.mk_not_raw(add_zero_eq),
                        index_eq,
                    ];

                    let not_index_eq = self.ctx.terms.mk_not_raw(index_eq);
                    let row_clause = vec![not_index_eq, row_eq];
                    if ay_proof::recognize_array_select_store(&self.ctx.terms, &row_clause)
                        != Some(true)
                    {
                        continue;
                    }

                    return Some(AuthoredSeqPushBackRow1Plan {
                        arithmetic_roots,
                        goal_negated,
                        len_zero,
                        len_chain_clause,
                        read_refl,
                        add_eq,
                        congruence_clause,
                        add_zero_eq,
                        index_eq,
                        index_chain_clause,
                        row_eq,
                        row_clause,
                    });
                }
            }
        }
        None
    }

    /// Recognize an original assertion as a linear-arithmetic disequality
    /// usable as an `la_disequality` case-split backbone. The surface form
    /// must be either `(not (= s t))` or binary `(distinct s t)` sugar, with
    /// operands elaborating POSITIONALLY to the canonical equality's operands
    /// (so every printed occurrence of `s`, `t`, and the equality matches the
    /// problem file and the synthesized `(<= s t)`/`(<= t s)` literals are
    /// order-consistent with the printed equality). Fail-closed otherwise.
    fn recognize_diseq_candidate(
        &mut self,
        idx: usize,
        canonical: TermId,
        parsed: &FrontendTerm,
        head: &str,
    ) -> Option<DiseqCandidate> {
        let TermData::Not(inner) = self.ctx.terms.get(canonical) else {
            return None;
        };
        let eq_term = *inner;
        let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(eq_term) else {
            return None;
        };
        if name != "=" || args.len() != 2 {
            return None;
        }
        let (lhs, rhs) = (args[0], args[1]);
        if !matches!(self.ctx.terms.sort(lhs), Sort::Int | Sort::Real)
            || self.ctx.terms.sort(lhs) != self.ctx.terms.sort(rhs)
        {
            return None;
        }
        // A placeholder (native-API) disequality has no surface spelling:
        // the canonical `(not (= s t))` shape above is all there is, and the
        // synthesized split literals are positionally consistent with it by
        // construction.
        if is_api_placeholder(parsed) {
            return Some(DiseqCandidate {
                original_idx: idx,
                eq_term,
                lhs,
                rhs,
                surface_is_distinct: false,
            });
        }
        let surface_operands: Vec<&FrontendTerm> = match strip_frontend_annotations(parsed) {
            FrontendTerm::App(op, operands)
                if op == "not" && operands.len() == 1 && head == "not" =>
            {
                match strip_frontend_annotations(&operands[0]) {
                    FrontendTerm::App(inner_op, eq_operands)
                        if inner_op == "=" && eq_operands.len() == 2 =>
                    {
                        eq_operands.iter().collect()
                    }
                    _ => return None,
                }
            }
            FrontendTerm::App(op, operands) if op == "distinct" && operands.len() == 2 => {
                operands.iter().collect()
            }
            _ => return None,
        };
        // Positional alignment: printed operand order must match the
        // canonical equality's operand order exactly.
        if self.ctx.elaborate_surface_subterm(surface_operands[0]) != Some(lhs)
            || self.ctx.elaborate_surface_subterm(surface_operands[1]) != Some(rhs)
        {
            return None;
        }
        Some(DiseqCandidate {
            original_idx: idx,
            eq_term,
            lhs,
            rhs,
            surface_is_distinct: head == "distinct",
        })
    }

    /// Whether any `Assume` leaf reachable from an empty-clause step carries
    /// a term that is not one of the (re-elaborated) original problem
    /// assertions. Such an assume cannot be matched to the problem's premises
    /// by an external checker.
    fn reachable_non_original_assume(proof: &Proof, originals: &[(TermId, FrontendTerm)]) -> bool {
        let source_index = OriginalSourceIndex::new(originals);
        if !source_index.is_valid() {
            return true;
        }
        let n = proof.steps.len();
        let mut on_path = vec![false; n];
        let mut stack: Vec<usize> = Vec::new();
        for (idx, step) in proof.steps.iter().enumerate() {
            let empty = match step {
                ProofStep::Step { clause, .. }
                | ProofStep::Resolution { clause, .. }
                | ProofStep::TheoryLemma { clause, .. } => clause.is_empty(),
                _ => false,
            };
            if empty && !on_path[idx] {
                on_path[idx] = true;
                stack.push(idx);
            }
        }
        let push = |id: ProofId, on_path: &mut Vec<bool>, stack: &mut Vec<usize>| {
            let i = id.0 as usize;
            if i < n && !on_path[i] {
                on_path[i] = true;
                stack.push(i);
            }
        };
        while let Some(idx) = stack.pop() {
            match &proof.steps[idx] {
                ProofStep::Step { premises, .. } => {
                    for &p in premises {
                        push(p, &mut on_path, &mut stack);
                    }
                }
                ProofStep::Resolution {
                    clause1, clause2, ..
                } => {
                    push(*clause1, &mut on_path, &mut stack);
                    push(*clause2, &mut on_path, &mut stack);
                }
                ProofStep::Assume(term) => {
                    if !source_index.contains(*term) {
                        return true;
                    }
                }
                _ => {}
            }
        }
        false
    }

    fn try_rebuild_with_disjunction(
        &mut self,
        proof: &mut Proof,
        originals: &[(TermId, FrontendTerm)],
        candidate: &DisjunctionCandidate,
        bound_specs: &[BoundSpec],
    ) -> bool {
        let disj_idx = candidate.original_idx;
        let disj_term = originals[disj_idx].0;
        let disjuncts = candidate.disjuncts.clone();
        let decomposition_rule = candidate.decomposition_rule.clone();
        let bound_terms: Vec<TermId> = bound_specs.iter().map(|s| s.term).collect();

        // (3) Eliminate every disjunct: directly by a complementary bound
        // when one exists, otherwise by a re-verified theory refutation of
        // `Di ∧ bounds`.
        let mut eliminations: Vec<DisjunctElimination> = Vec::with_capacity(disjuncts.len());
        for &di in &disjuncts {
            if let Some(pos) = bound_terms.iter().position(|&b| {
                let complementary = match (self.ctx.terms.get(di), self.ctx.terms.get(b)) {
                    (TermData::Not(inner), _) => *inner == b,
                    (_, TermData::Not(inner)) => *inner == di,
                    _ => false,
                };
                complementary
            }) {
                eliminations.push(DisjunctElimination::Unit { bound_idx: pos });
                continue;
            }

            let Some(elim) = self.refute_disjunct_against_bounds(di, &bound_terms) else {
                return false;
            };
            eliminations.push(elim);
        }

        // (4) Determine which bounds are actually used, in assertion order.
        let mut used_bound: Vec<bool> = vec![false; bound_terms.len()];
        for (di_idx, elim) in eliminations.iter().enumerate() {
            match elim {
                DisjunctElimination::Unit { bound_idx } => used_bound[*bound_idx] = true,
                DisjunctElimination::Lemma {
                    blocking_clause, ..
                } => {
                    let di_atom = atom_of(&self.ctx.terms, disjuncts[di_idx]);
                    for &lit in blocking_clause {
                        if atom_of(&self.ctx.terms, lit) == di_atom {
                            continue;
                        }
                        // Each non-disjunct blocking literal must be the
                        // complement of a bound (its unit resolvent).
                        let complement = match self.ctx.terms.get(lit) {
                            TermData::Not(inner) => *inner,
                            _ => match bound_terms.iter().position(|&b| {
                                matches!(self.ctx.terms.get(b), TermData::Not(inner) if *inner == lit)
                            }) {
                                Some(pos) => {
                                    used_bound[pos] = true;
                                    continue;
                                }
                                None => return false,
                            },
                        };
                        match bound_terms.iter().position(|&b| b == complement) {
                            Some(pos) => used_bound[pos] = true,
                            None => return false,
                        }
                    }
                }
            }
        }

        // (5) Assemble the replacement proof: assumes first (Alethe ordering),
        // then lemmas, the `or` decomposition, and the resolution chain.
        let mut new_proof = Proof::new();
        let disj_assume = new_proof.add_assume(disj_term, None);
        // `bound_assume` maps each used CANONICAL bound term to a proof of
        // it: the assume itself; for a `(distinct s t)` surface bound, whose
        // printed sugar cannot resolve against `(= s t)`, the raw `distinct`
        // application assume bridged through `distinct_elim` + `equiv_pos2`
        // down to the canonical `(not (= s t))` literal; for a conjunct
        // bound, the root's assume chained through strictly-validated
        // `and_pos` + resolution steps.
        let mut bound_assume: HashMap<TermId, ProofId> = HashMap::default();
        let mut root_assumes: HashMap<TermId, ProofId> = HashMap::default();
        let mut distinct_bridges: Vec<(TermId, TermId, ProofId)> = Vec::new();
        // (spec index, root assume) pairs whose `and_pos` chains are emitted
        // after ALL assumes.
        let mut conjunct_chains: Vec<(usize, ProofId)> = Vec::new();
        for (idx, spec) in bound_specs.iter().enumerate() {
            if !used_bound[idx] || bound_assume.contains_key(&spec.term) {
                continue;
            }
            if let Some((s, t)) = spec.distinct {
                let dist = self
                    .ctx
                    .terms
                    .mk_app(Symbol::named("distinct"), [s, t], Sort::Bool);
                let id = new_proof.add_assume(dist, None);
                distinct_bridges.push((spec.term, dist, id));
            } else if spec.path.is_empty() {
                let id = new_proof.add_assume(spec.term, None);
                bound_assume.insert(spec.term, id);
            } else {
                let root = originals[spec.original_idx].0;
                let id = *root_assumes
                    .entry(root)
                    .or_insert_with(|| new_proof.add_assume(root, None));
                conjunct_chains.push((idx, id));
            }
        }
        for &(spec_idx, root_assume) in &conjunct_chains {
            let spec = &bound_specs[spec_idx];
            if bound_assume.contains_key(&spec.term) {
                continue;
            }
            let root = originals[spec.original_idx].0;
            let Some(unit) = Self::emit_and_pos_chain(
                &mut self.ctx.terms,
                &mut new_proof,
                root_assume,
                root,
                &spec.path,
                spec.term,
            ) else {
                return false;
            };
            bound_assume.insert(spec.term, unit);
        }
        for &(b, dist, assume_id) in &distinct_bridges {
            let equiv = self
                .ctx
                .terms
                .mk_app(Symbol::named("="), [dist, b], Sort::Bool);
            let not_equiv = self.ctx.terms.mk_not_raw(equiv);
            let not_dist = self.ctx.terms.mk_not_raw(dist);
            let de = new_proof.add_rule_step(
                AletheRule::DistinctElim,
                vec![equiv],
                Vec::new(),
                Vec::new(),
            );
            let ep = new_proof.add_rule_step(
                AletheRule::EquivPos2,
                vec![not_equiv, not_dist, b],
                Vec::new(),
                Vec::new(),
            );
            let r1 = new_proof.add_resolution(vec![not_dist, b], equiv, ep, de);
            let unit = new_proof.add_resolution(vec![b], dist, r1, assume_id);
            bound_assume.insert(b, unit);
        }

        let or_step = new_proof.add_rule_step(
            decomposition_rule,
            disjuncts.clone(),
            vec![disj_assume],
            Vec::new(),
        );

        let mut current_clause = disjuncts.clone();
        let mut current_proof = or_step;
        for (di_idx, elim) in eliminations.iter().enumerate() {
            let di = disjuncts[di_idx];
            let di_atom = atom_of(&self.ctx.terms, di);
            let unit_proof = match elim {
                DisjunctElimination::Unit { bound_idx } => {
                    let b = bound_terms[*bound_idx];
                    match bound_assume.get(&b) {
                        Some(&id) => id,
                        None => return false,
                    }
                }
                DisjunctElimination::Lemma {
                    blocking_clause,
                    farkas,
                } => {
                    let lemma_id = new_proof.add_step(ProofStep::TheoryLemma {
                        theory: "LRA".to_string(),
                        clause: blocking_clause.clone(),
                        farkas: Some(farkas.clone()),
                        kind: TheoryLemmaKind::LraFarkas,
                        lia: None,
                    });
                    // Resolve the lemma's bound literals away, leaving the
                    // unit `¬Di`.
                    let mut lemma_clause = blocking_clause.clone();
                    let mut lemma_proof = lemma_id;
                    let bound_lits: Vec<TermId> = lemma_clause
                        .iter()
                        .copied()
                        .filter(|&l| atom_of(&self.ctx.terms, l) != di_atom)
                        .collect();
                    for blit in bound_lits {
                        let pivot = atom_of(&self.ctx.terms, blit);
                        // The bound is the complement of the blocking literal.
                        let bound = if matches!(self.ctx.terms.get(blit), TermData::Not(_)) {
                            pivot
                        } else {
                            match bound_terms.iter().copied().find(|&b| {
                                matches!(self.ctx.terms.get(b), TermData::Not(inner) if *inner == blit)
                            }) {
                                Some(b) => b,
                                None => return false,
                            }
                        };
                        let Some(&unit_id) = bound_assume.get(&bound) else {
                            return false;
                        };
                        let resolvent: Vec<TermId> = lemma_clause
                            .iter()
                            .copied()
                            .filter(|&l| l != blit)
                            .collect();
                        lemma_proof = new_proof.add_resolution(
                            resolvent.clone(),
                            pivot,
                            lemma_proof,
                            unit_id,
                        );
                        lemma_clause = resolvent;
                    }
                    // The remaining lemma clause must be exactly the
                    // complementary unit of `Di`.
                    if lemma_clause.len() != 1
                        || atom_of(&self.ctx.terms, lemma_clause[0]) != di_atom
                        || lemma_clause[0] == di
                    {
                        return false;
                    }
                    lemma_proof
                }
            };
            let resolvent: Vec<TermId> = current_clause
                .iter()
                .copied()
                .filter(|&l| l != di)
                .collect();
            current_proof =
                new_proof.add_resolution(resolvent.clone(), di_atom, current_proof, unit_proof);
            current_clause = resolvent;
        }

        if !current_clause.is_empty() {
            return false;
        }

        // (6) Success: swap the proof and register surface-syntax overrides
        // for the originals we now assume — and for each clause literal of
        // the decomposition (a De Morgan-canonicalized `(not (and ...))`
        // stores its literals as or-disjuncts whose surface form is
        // `(not Ai)`) — so everything prints with the problem file's own
        // syntax and the checker can match the premises.
        let mut pairs: Vec<(TermId, FrontendTerm)> =
            vec![(originals[disj_idx].0, originals[disj_idx].1.clone())];
        let mut suppressed = Vec::new();
        for (&canonical_lit, surface) in disjuncts.iter().zip(candidate.surface_literals.iter()) {
            pairs.push((canonical_lit, surface.clone()));
        }
        for (idx, used) in used_bound.iter().enumerate() {
            if !*used {
                continue;
            }
            let spec = &bound_specs[idx];
            // A `(distinct s t)` bound is assumed as the raw `distinct`
            // application, which already prints exactly like the problem
            // file; an override on its CANONICAL `(not (= s t))` term —
            // including any STALE one collected during the ordinary
            // export the rebuild replaces — would corrupt the bridge and
            // resolution literal prints.
            if spec.distinct.is_some() {
                suppressed.push(spec.term);
                continue;
            }
            // A conjunct bound registers its ROOT's surface: the assume is
            // the root, and `collect_surface_term_overrides` descends to the
            // extracted literals. Direct bounds register themselves (root ==
            // literal).
            pairs.push((
                originals[spec.original_idx].0,
                originals[spec.original_idx].1.clone(),
            ));
        }
        if !surface_override_roots_have_bounded_work(
            &self.ctx.terms,
            pairs.iter().map(|(canonical, _)| *canonical),
        ) {
            return false;
        }
        if self
            .last_proof_term_overrides
            .as_ref()
            .is_some_and(|overrides| !surface_override_map_is_bounded(overrides))
        {
            return false;
        }
        let mut overrides = self.last_proof_term_overrides.clone().unwrap_or_default();
        for term in suppressed {
            overrides.remove(&term);
        }
        for (canonical, parsed) in &pairs {
            // Placeholder (native-API) surfaces register NO override: the
            // sentinel string is not a printable spelling — the canonical
            // rendering already is.
            if is_api_placeholder(parsed) {
                continue;
            }
            if !collect_surface_term_overrides(&mut self.ctx, *canonical, parsed, &mut overrides)
                || !surface_override_map_is_bounded(&overrides)
            {
                return false;
            }
        }
        *proof = new_proof;
        self.last_proof_term_overrides = Some(overrides);
        if ay_core::misc_cli_flags().debug_cert {
            ay_core::safe_eprintln!("c !! substitution-bridge SUCCEEDED (override path)");
        }
        true
    }

    /// Rebuild the proof around a SYNTHESIZED `la_disequality` case split on
    /// an original linear disequality `(not (= s t))` (or binary
    /// `(distinct s t)` sugar):
    ///
    /// 1. `la_disequality` ⊢ `(or (= s t) (not (<= s t)) (not (<= t s)))`,
    ///    split by the `or` rule.
    /// 2. The `(= s t)` disjunct resolves against the disequality assume
    ///    (through a `distinct_elim` + `equiv_pos2` bridge when the problem
    ///    file spells it `(distinct s t)`).
    /// 3. Each inequality disjunct is refuted against the remaining bound
    ///    assertions by a certified, independently re-verified `la_generic`
    ///    lemma (or a direct complementary bound), exactly as in
    ///    `try_rebuild_with_disjunction`.
    ///
    /// Fail-closed: returns `false` (proof untouched) on any gap.
    fn try_rebuild_with_diseq_split(
        &mut self,
        proof: &mut Proof,
        originals: &[(TermId, FrontendTerm)],
        candidate: &DiseqCandidate,
        bound_specs: &[BoundSpec],
        conjunct_root_faithful: &HashMap<usize, bool>,
    ) -> bool {
        let diseq_idx = candidate.original_idx;
        let neq_term = originals[diseq_idx].0;
        let (eq, s, t) = (candidate.eq_term, candidate.lhs, candidate.rhs);

        // Synthesized split literals. `mk_app` raw-interns, so the printed
        // operand order is exactly `(<= s t)` / `(<= t s)` as `la_disequality`
        // requires; still fail-closed on any constant-fold surprise.
        let le_st = self
            .ctx
            .terms
            .mk_app(Symbol::named("<="), [s, t], Sort::Bool);
        let le_ts = self
            .ctx
            .terms
            .mk_app(Symbol::named("<="), [t, s], Sort::Bool);
        let le_shape_ok = |terms: &TermStore, le: TermId| {
            matches!(
                terms.get(le),
                TermData::App(Symbol::Named(name), args) if name == "<=" && args.len() == 2
            )
        };
        if !le_shape_ok(&self.ctx.terms, le_st) || !le_shape_ok(&self.ctx.terms, le_ts) {
            return false;
        }
        let not_le_st = self.ctx.terms.mk_not_raw(le_st);
        let not_le_ts = self.ctx.terms.mk_not_raw(le_ts);
        let or_term =
            self.ctx
                .terms
                .mk_app(Symbol::named("or"), [eq, not_le_st, not_le_ts], Sort::Bool);

        // Bounds exclude the disequality itself. `bound_pairs.0` indexes into
        // `bound_specs`.
        let bound_pairs: Vec<(usize, TermId)> = bound_specs
            .iter()
            .enumerate()
            .filter(|(_, s)| s.original_idx != diseq_idx)
            .map(|(i, s)| (i, s.term))
            .collect();
        let bound_terms: Vec<TermId> = bound_pairs.iter().map(|&(_, b)| b).collect();

        // (a) Eliminate both inequality disjuncts.
        let split_disjuncts = [not_le_st, not_le_ts];
        let mut eliminations: Vec<DisjunctElimination> = Vec::with_capacity(2);
        for &di in &split_disjuncts {
            let di_atom = atom_of(&self.ctx.terms, di);
            if let Some(pos) = bound_terms.iter().position(|&b| b == di_atom) {
                eliminations.push(DisjunctElimination::Unit { bound_idx: pos });
                continue;
            }
            let Some(elim) = self.refute_disjunct_against_bounds(di, &bound_terms) else {
                return false;
            };
            eliminations.push(elim);
        }

        // (b) Which bounds are actually used (mirrors
        // `try_rebuild_with_disjunction` step 4).
        let mut used_bound: Vec<bool> = vec![false; bound_terms.len()];
        for (di_idx, elim) in eliminations.iter().enumerate() {
            match elim {
                DisjunctElimination::Unit { bound_idx } => used_bound[*bound_idx] = true,
                DisjunctElimination::Lemma {
                    blocking_clause, ..
                } => {
                    let di_atom = atom_of(&self.ctx.terms, split_disjuncts[di_idx]);
                    for &lit in blocking_clause {
                        if atom_of(&self.ctx.terms, lit) == di_atom {
                            continue;
                        }
                        let complement = match self.ctx.terms.get(lit) {
                            TermData::Not(inner) => *inner,
                            _ => match bound_terms.iter().position(|&b| {
                                matches!(self.ctx.terms.get(b), TermData::Not(inner) if *inner == lit)
                            }) {
                                Some(pos) => {
                                    used_bound[pos] = true;
                                    continue;
                                }
                                None => return false,
                            },
                        };
                        match bound_terms.iter().position(|&b| b == complement) {
                            Some(pos) => used_bound[pos] = true,
                            None => return false,
                        }
                    }
                }
            }
        }

        // (c) Assemble: assumes first, then the (optional) distinct bridge,
        // per-bound orientation bridges, the la_disequality split, and the
        // resolution chain.
        //
        // Printing note: the proof's term-surface overrides are GLOBAL per
        // TermId, and the canonical form of a bound like `(>= x 1)` is
        // exactly the `(<= 1 x)` literal that `la_disequality` must print —
        // an override would corrupt the rule's rigid shape. So this path
        // registers NO orientation overrides: each bound is assumed as a
        // raw surface-spelled term (its own TermId) and bridged to the
        // canonical literal by a certified 2-literal `la_generic` lemma.
        let mut plans: Vec<Option<DiseqBoundPlan>> = Vec::with_capacity(bound_pairs.len());
        for &(spec_idx, b) in &bound_pairs {
            let spec = &bound_specs[spec_idx];
            let plan = if spec.distinct.is_some() {
                // `(distinct s t)` sugar cannot resolve against the split
                // literals without a `distinct_elim` bridge, whose printed
                // shape this override-free path does not manage. Fail-closed.
                None
            } else if spec.path.is_empty() {
                if is_api_placeholder(&spec.surface) {
                    // No surface: the canonical literal is its own spelling.
                    Some(DiseqBoundPlan::Direct {
                        raw: b,
                        bridge_atom: None,
                    })
                } else {
                    self.surface_bound_raw_term(&spec.surface, b)
                        .map(|(raw, bridge_atom)| DiseqBoundPlan::Direct { raw, bridge_atom })
                }
            } else if conjunct_root_faithful
                .get(&spec.original_idx)
                .copied()
                .unwrap_or(false)
            {
                // EVERY leaf of the root re-interns raw-faithfully, so the
                // root's assume prints byte-identically to the problem file
                // with no overrides; the literal is extracted by `and_pos`.
                Some(DiseqBoundPlan::Conjunct)
            } else {
                None
            };
            plans.push(plan);
        }
        for (idx, plan) in plans.iter().enumerate() {
            if used_bound[idx] && plan.is_none() {
                // A needed bound has an unprintable/unbridgeable surface form.
                return false;
            }
        }

        let mut new_proof = Proof::new();
        let (diseq_assume_term, dist_term) = if candidate.surface_is_distinct {
            let dist = self
                .ctx
                .terms
                .mk_app(Symbol::named("distinct"), [s, t], Sort::Bool);
            (dist, Some(dist))
        } else {
            (neq_term, None)
        };
        let diseq_assume = new_proof.add_assume(diseq_assume_term, None);
        let mut bound_assume_raw: HashMap<TermId, ProofId> = HashMap::default();
        let mut root_assumes: HashMap<TermId, ProofId> = HashMap::default();
        for (idx, &b) in bound_terms.iter().enumerate() {
            if !used_bound[idx] || bound_assume_raw.contains_key(&b) {
                continue;
            }
            match &plans[idx] {
                Some(DiseqBoundPlan::Direct { raw, .. }) => {
                    let id = new_proof.add_assume(*raw, None);
                    bound_assume_raw.insert(b, id);
                }
                Some(DiseqBoundPlan::Conjunct) => {
                    let root = originals[bound_specs[bound_pairs[idx].0].original_idx].0;
                    let id = *root_assumes
                        .entry(root)
                        .or_insert_with(|| new_proof.add_assume(root, None));
                    bound_assume_raw.insert(b, id);
                }
                None => return false,
            }
        }
        // Bridge each bound assume down to the CANONICAL bound literal:
        // an orientation flip via certified la_generic `(cl <canonical>
        // <complement of raw>)` resolved against the raw assume; a conjunct
        // via the strictly-validated `and_pos` + resolution chain from its
        // root's assume. `bound_assume` maps the canonical bound term to a
        // proof of it.
        let mut bound_assume: HashMap<TermId, ProofId> = HashMap::default();
        for (idx, &b) in bound_terms.iter().enumerate() {
            if !used_bound[idx] || bound_assume.contains_key(&b) {
                continue;
            }
            let &raw_assume = match bound_assume_raw.get(&b) {
                Some(id) => id,
                None => return false,
            };
            let (raw, atom) = match &plans[idx] {
                Some(DiseqBoundPlan::Conjunct) => {
                    let spec = &bound_specs[bound_pairs[idx].0];
                    let root = originals[spec.original_idx].0;
                    let Some(unit) = Self::emit_and_pos_chain(
                        &mut self.ctx.terms,
                        &mut new_proof,
                        raw_assume,
                        root,
                        &spec.path,
                        b,
                    ) else {
                        return false;
                    };
                    bound_assume.insert(b, unit);
                    continue;
                }
                Some(DiseqBoundPlan::Direct {
                    bridge_atom: None, ..
                }) => {
                    // Raw form IS the canonical term: no bridge needed.
                    bound_assume.insert(b, raw_assume);
                    continue;
                }
                Some(DiseqBoundPlan::Direct {
                    raw,
                    bridge_atom: Some(atom),
                }) => (*raw, *atom),
                None => return false,
            };
            // Complement of the raw literal, avoiding double negation.
            let raw_complement = if raw == atom {
                self.ctx.terms.mk_not_raw(atom)
            } else {
                atom
            };
            let bridge_clause = vec![b, raw_complement];
            // Independent verification of the [1, 1] Farkas certificate for
            // the orientation-flip lemma (fail-closed).
            let farkas = FarkasAnnotation::from_ints(&[1, 1]);
            let lits: Vec<TheoryLit> = bridge_clause
                .iter()
                .map(|&l| match self.ctx.terms.get(l) {
                    TermData::Not(inner) => TheoryLit::new(*inner, true),
                    _ => TheoryLit::new(l, false),
                })
                .collect();
            if ay_core::proof_validation::verify_farkas_conflict_lits_full(
                &self.ctx.terms,
                &lits,
                &farkas,
            )
            .is_err()
            {
                return false;
            }
            let lemma_id = new_proof.add_step(ProofStep::TheoryLemma {
                theory: "LRA".to_string(),
                clause: bridge_clause,
                farkas: Some(farkas),
                kind: TheoryLemmaKind::LraFarkas,
                lia: None,
            });
            let unit = new_proof.add_resolution(vec![b], atom, lemma_id, raw_assume);
            bound_assume.insert(b, unit);
        }

        // Unit `(not (= s t))`: the assume itself, or the distinct bridge
        //   distinct_elim ⊢ (= (distinct s t) (not (= s t)))
        //   equiv_pos2    ⊢ (cl (not (= φ1 φ2)) (not φ1) φ2)
        // resolved with the assume down to the canonical literal.
        let neq_unit = match dist_term {
            None => diseq_assume,
            Some(dist) => {
                let equiv = self
                    .ctx
                    .terms
                    .mk_app(Symbol::named("="), [dist, neq_term], Sort::Bool);
                let not_equiv = self.ctx.terms.mk_not_raw(equiv);
                let not_dist = self.ctx.terms.mk_not_raw(dist);
                let de = new_proof.add_rule_step(
                    AletheRule::DistinctElim,
                    vec![equiv],
                    Vec::new(),
                    Vec::new(),
                );
                let ep = new_proof.add_rule_step(
                    AletheRule::EquivPos2,
                    vec![not_equiv, not_dist, neq_term],
                    Vec::new(),
                    Vec::new(),
                );
                let r1 = new_proof.add_resolution(vec![not_dist, neq_term], equiv, ep, de);
                new_proof.add_resolution(vec![neq_term], dist, r1, diseq_assume)
            }
        };

        let la_step = new_proof.add_rule_step(
            AletheRule::LaDisequality,
            vec![or_term],
            Vec::new(),
            Vec::new(),
        );
        let or_step = new_proof.add_rule_step(
            AletheRule::Or,
            vec![eq, not_le_st, not_le_ts],
            vec![la_step],
            Vec::new(),
        );

        let mut current_clause = vec![not_le_st, not_le_ts];
        let mut current_proof =
            new_proof.add_resolution(current_clause.clone(), eq, or_step, neq_unit);

        for (di_idx, elim) in eliminations.iter().enumerate() {
            let di = split_disjuncts[di_idx];
            let di_atom = atom_of(&self.ctx.terms, di);
            let unit_proof = match elim {
                DisjunctElimination::Unit { bound_idx } => {
                    let b = bound_terms[*bound_idx];
                    match bound_assume.get(&b) {
                        Some(&id) => id,
                        None => return false,
                    }
                }
                DisjunctElimination::Lemma {
                    blocking_clause,
                    farkas,
                } => {
                    let lemma_id = new_proof.add_step(ProofStep::TheoryLemma {
                        theory: "LRA".to_string(),
                        clause: blocking_clause.clone(),
                        farkas: Some(farkas.clone()),
                        kind: TheoryLemmaKind::LraFarkas,
                        lia: None,
                    });
                    let mut lemma_clause = blocking_clause.clone();
                    let mut lemma_proof = lemma_id;
                    let bound_lits: Vec<TermId> = lemma_clause
                        .iter()
                        .copied()
                        .filter(|&l| atom_of(&self.ctx.terms, l) != di_atom)
                        .collect();
                    for blit in bound_lits {
                        let pivot = atom_of(&self.ctx.terms, blit);
                        let bound = if matches!(self.ctx.terms.get(blit), TermData::Not(_)) {
                            pivot
                        } else {
                            match bound_terms.iter().copied().find(|&b| {
                                matches!(self.ctx.terms.get(b), TermData::Not(inner) if *inner == blit)
                            }) {
                                Some(b) => b,
                                None => return false,
                            }
                        };
                        let Some(&unit_id) = bound_assume.get(&bound) else {
                            return false;
                        };
                        let resolvent: Vec<TermId> = lemma_clause
                            .iter()
                            .copied()
                            .filter(|&l| l != blit)
                            .collect();
                        lemma_proof = new_proof.add_resolution(
                            resolvent.clone(),
                            pivot,
                            lemma_proof,
                            unit_id,
                        );
                        lemma_clause = resolvent;
                    }
                    if lemma_clause.len() != 1
                        || atom_of(&self.ctx.terms, lemma_clause[0]) != di_atom
                        || lemma_clause[0] == di
                    {
                        return false;
                    }
                    lemma_proof
                }
            };
            let resolvent: Vec<TermId> = current_clause
                .iter()
                .copied()
                .filter(|&l| l != di)
                .collect();
            current_proof =
                new_proof.add_resolution(resolvent.clone(), di_atom, current_proof, unit_proof);
            current_clause = resolvent;
        }

        if !current_clause.is_empty() {
            return false;
        }

        // (d) Success: swap the proof. NO surface overrides are registered in
        // this path (see the printing note above): every assumed term is
        // already spelled with the problem file's own surface syntax (raw
        // interned apps / the canonical disequality), and a global override
        // would corrupt the rigid `la_disequality` literal shapes.
        *proof = new_proof;
        self.last_proof_term_overrides = None;
        true
    }

    /// Map a bound assertion's SURFACE form to a raw printable term.
    ///
    /// Returns `Some((raw_term, bridge_atom))` where `raw_term` is the term
    /// the `assume` step carries (spelled exactly like the problem file) and
    /// `bridge_atom` is `None` when `raw_term` IS the canonical bound term
    /// (no bridge needed) or `Some(atom)` — the raw literal's atom — when the
    /// surface is an orientation flip (`(>= a b)` for canonical `(<= b a)`,
    /// `(> a b)` for `(< b a)`, possibly under `not`) that must be bridged by
    /// an `la_generic` lemma. Returns `None` for any other surface shape
    /// (fail-closed: the caller rejects the rebuild if that bound is needed).
    pub(super) fn surface_bound_raw_term(
        &mut self,
        parsed: &FrontendTerm,
        canonical: TermId,
    ) -> Option<(TermId, Option<TermId>)> {
        fn flipped_head(head: &str) -> Option<&'static str> {
            match head {
                ">=" => Some("<="),
                ">" => Some("<"),
                _ => None,
            }
        }
        let stripped = strip_frontend_annotations(parsed);
        // Optional `not` wrapper.
        let (inner_surface, negated) = match stripped {
            FrontendTerm::App(op, operands) if op == "not" && operands.len() == 1 => {
                (strip_frontend_annotations(&operands[0]), true)
            }
            _ => (stripped, false),
        };
        let FrontendTerm::App(head, operands) = inner_surface else {
            return None;
        };
        if operands.len() != 2 || !matches!(head.as_str(), "<=" | "<" | ">=" | ">" | "=") {
            return None;
        }
        let a = self.ctx.elaborate_surface_subterm(&operands[0])?;
        let b = self.ctx.elaborate_surface_subterm(&operands[1])?;
        let raw_atom = self
            .ctx
            .terms
            .mk_app(Symbol::named(head.as_str()), [a, b], Sort::Bool);
        let raw_term = if negated {
            self.ctx.terms.mk_not_raw(raw_atom)
        } else {
            raw_atom
        };
        if raw_term == canonical {
            return Some((raw_term, None));
        }
        // Orientation flip: canonical must be exactly the argument-swapped
        // comparison (same polarity).
        let flip = flipped_head(head.as_str())?;
        let flip_atom = self
            .ctx
            .terms
            .mk_app(Symbol::named(flip), [b, a], Sort::Bool);
        let flip_term = if negated {
            self.ctx.terms.mk_not_raw(flip_atom)
        } else {
            flip_atom
        };
        if flip_term != canonical {
            return None;
        }
        Some((raw_term, Some(raw_atom)))
    }

    /// Refute `Di ∧ bounds` with a fresh LRA solver and return the blocking
    /// clause + Farkas certificate, RE-VERIFIED by the independent checker
    /// (`verify_farkas_conflict_lits_full`) and required to be
    /// sign-resolvable for Alethe printing
    /// (`resolve_equality_coefficient_signs`). Fail-closed on any gap.
    fn refute_disjunct_against_bounds(
        &mut self,
        di: TermId,
        bound_terms: &[TermId],
    ) -> Option<DisjunctElimination> {
        if !is_linear_literal(&self.ctx.terms, di) {
            return None;
        }
        let (di_atom, di_val) = match self.ctx.terms.get(di) {
            TermData::Not(inner) => (*inner, false),
            _ => (di, true),
        };
        let linear_bounds: Vec<TermId> = bound_terms
            .iter()
            .copied()
            .filter(|&bound| is_linear_literal(&self.ctx.terms, bound))
            .collect();
        let mut lra = ay_lra::LraSolver::new(&self.ctx.terms);
        lra.set_combined_theory_mode(true);
        TheorySolver::register_atom(&mut lra, di_atom);
        for &b in &linear_bounds {
            TheorySolver::register_atom(&mut lra, atom_of(&self.ctx.terms, b));
        }
        TheorySolver::assert_literal(&mut lra, di_atom, di_val);
        for &b in &linear_bounds {
            let (atom, val) = match self.ctx.terms.get(b) {
                TermData::Not(inner) => (*inner, false),
                _ => (b, true),
            };
            TheorySolver::assert_literal(&mut lra, atom, val);
        }
        let TheoryResult::UnsatWithFarkas(conflict) = TheorySolver::check(&mut lra) else {
            return None;
        };
        let farkas = conflict.farkas?;
        if farkas.coefficients.len() != conflict.literals.len() || conflict.literals.is_empty() {
            return None;
        }
        // The refutation must actually name this disjunct.
        if !conflict.literals.iter().any(|l| l.term == di_atom) {
            return None;
        }
        // Independent semantic re-verification (never trust the solver's
        // certificate blindly), plus a sign-resolution dry run so we know the
        // printed `la_generic` args will be exact.
        let lits: Vec<TheoryLit> = conflict.literals.clone();
        if ay_core::proof_validation::verify_farkas_conflict_lits_full(
            &self.ctx.terms,
            &lits,
            &farkas,
        )
        .is_err()
        {
            return None;
        }
        ay_core::proof_validation::resolve_equality_coefficient_signs(
            &self.ctx.terms,
            &lits,
            &farkas,
        )?;

        let mut blocking_clause = Vec::with_capacity(conflict.literals.len());
        for lit in &conflict.literals {
            let t = if lit.value {
                self.ctx.terms.mk_not_raw(lit.term)
            } else {
                lit.term
            };
            blocking_clause.push(t);
        }
        Some(DisjunctElimination::Lemma {
            blocking_clause,
            farkas,
        })
    }

    /// Collect usable linear bounds from the conjuncts of an original
    /// `(and ...)` assertion (nested `and` trees included).
    ///
    /// Surface/canonical LOCKSTEP: at every `and` node the parsed operator,
    /// the canonical operator, and the operand count must agree, and every
    /// surface operand must re-elaborate to exactly the corresponding
    /// canonical child — a misaligned child contributes nothing (fail-closed:
    /// a literal we cannot surface-align could not be matched to the problem
    /// file by an external checker). A leaf becomes a bound when it is a
    /// (possibly negated) binary linear comparison with a plain surface head,
    /// mirroring the direct-bound gate.
    ///
    /// The second return is `true` when EVERY leaf of the tree is such a
    /// bound AND re-interns raw-faithfully (its surface rebuilds to exactly
    /// the canonical term id, so the root prints byte-identically to the
    /// problem file with NO overrides) — the precondition for the
    /// override-free `la_disequality` path to assume the root.
    fn collect_conjunct_bound_specs(
        &mut self,
        original_idx: usize,
        canonical: TermId,
        parsed: &FrontendTerm,
    ) -> (Vec<BoundSpec>, bool) {
        let mut specs = Vec::new();
        let mut fully_faithful = true;
        let mut path = Vec::new();
        self.walk_conjunct_bounds(
            original_idx,
            canonical,
            parsed,
            &mut path,
            &mut specs,
            &mut fully_faithful,
        );
        (specs, fully_faithful)
    }

    /// Placeholder (native-API) variant of [`collect_conjunct_bound_specs`]:
    /// walk the CANONICAL `and`-tree directly — there is no surface to align,
    /// so alignment is definitional and the root is trivially print-faithful
    /// (its canonical rendering is its only spelling). Each collected spec
    /// carries the placeholder as its (unused) surface; every surface-fidelity
    /// consumer branches on `is_api_placeholder` before touching it. The
    /// second return mirrors `collect_conjunct_bound_specs`: `true` iff EVERY
    /// leaf is a usable linear bound.
    fn collect_conjunct_bound_specs_canonical(
        &mut self,
        original_idx: usize,
        canonical: TermId,
        placeholder: &FrontendTerm,
    ) -> (Vec<BoundSpec>, bool) {
        let mut specs = Vec::new();
        let mut fully_linear = true;
        // (term, path) worklist over the and-tree.
        let mut stack: Vec<(TermId, Vec<u32>)> = vec![(canonical, Vec::new())];
        while let Some((term, path)) = stack.pop() {
            if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(term) {
                if name == "and" {
                    let args = args.clone();
                    for (i, &child) in args.iter().enumerate() {
                        let Ok(pos) = u32::try_from(i) else {
                            fully_linear = false;
                            continue;
                        };
                        let mut child_path = path.clone();
                        child_path.push(pos);
                        stack.push((child, child_path));
                    }
                    continue;
                }
            }
            if path.is_empty() {
                // The original itself is not an `and`: no conjunct bounds.
                return (Vec::new(), false);
            }
            if !is_linear_literal(&self.ctx.terms, term) {
                fully_linear = false;
                continue;
            }
            specs.push(BoundSpec {
                original_idx,
                term,
                path,
                surface: placeholder.clone(),
                distinct: None,
            });
        }
        (specs, fully_linear)
    }

    fn walk_conjunct_bounds(
        &mut self,
        original_idx: usize,
        canonical: TermId,
        surface: &FrontendTerm,
        path: &mut Vec<u32>,
        specs: &mut Vec<BoundSpec>,
        fully_faithful: &mut bool,
    ) {
        // An `and` node: descend surface/canonical in LOCKSTEP.
        if let FrontendTerm::App(op, operands) = strip_frontend_annotations(surface) {
            if op == "and" {
                let args = match self.ctx.terms.get(canonical) {
                    TermData::App(Symbol::Named(name), args)
                        if name == "and" && args.len() == operands.len() =>
                    {
                        args.clone()
                    }
                    _ => {
                        // Surface/canonical shape drift (e.g. elaboration
                        // flattening): the whole subtree is unusable.
                        *fully_faithful = false;
                        return;
                    }
                };
                for (i, (child, child_surface)) in args.iter().zip(operands.iter()).enumerate() {
                    let Ok(pos) = u32::try_from(i) else {
                        *fully_faithful = false;
                        continue;
                    };
                    if self.ctx.elaborate_surface_subterm(child_surface) != Some(*child) {
                        // Misaligned conjunct: skip its subtree (fail-closed).
                        *fully_faithful = false;
                        continue;
                    }
                    path.push(pos);
                    self.walk_conjunct_bounds(
                        original_idx,
                        *child,
                        child_surface,
                        path,
                        specs,
                        fully_faithful,
                    );
                    path.pop();
                }
                return;
            }
        }
        // A leaf. The original itself not being an `and` yields no conjunct
        // bounds at all.
        if path.is_empty() {
            *fully_faithful = false;
            return;
        }
        let head_ok = matches!(
            parsed_head(surface),
            Some("not" | "<" | "<=" | ">" | ">=" | "=")
        );
        if !head_ok || !is_linear_literal(&self.ctx.terms, canonical) {
            *fully_faithful = false;
            return;
        }
        // Raw-faithfulness (the surface re-interns to EXACTLY the canonical
        // term id) is what the override-free `la_disequality` path needs to
        // print the root assume byte-identically to the problem file.
        match self.surface_bound_raw_term(surface, canonical) {
            Some((raw, None)) if raw == canonical => {}
            _ => *fully_faithful = false,
        }
        specs.push(BoundSpec {
            original_idx,
            term: canonical,
            path: path.clone(),
            surface: surface.clone(),
            distinct: None,
        });
    }

    /// Emit the strictly-validated `and_pos` + resolution chain deriving the
    /// conjunct at `path` inside `root` from `root_assume : (cl root)`:
    /// per level, `and_pos(i)` gives the Alethe tautology
    /// `(cl (not parent) child_i)` (args = [parent]; validated STRUCTURALLY
    /// by the strict checker), resolved against `(cl parent)` on pivot
    /// `parent` to the unit `(cl child_i)`.
    ///
    /// Returns the unit's proof id only when the path walks `and`
    /// applications down to exactly `expected`; `None` abandons the rebuild
    /// (fail-closed — the partially-emitted steps die with the discarded
    /// proof).
    pub(super) fn emit_and_pos_chain(
        terms: &mut TermStore,
        new_proof: &mut Proof,
        root_assume: ProofId,
        root: TermId,
        path: &[u32],
        expected: TermId,
    ) -> Option<ProofId> {
        let mut current_id = root_assume;
        let mut current_term = root;
        for &pos in path {
            let child = match terms.get(current_term) {
                TermData::App(Symbol::Named(name), args) if name == "and" => {
                    *args.get(pos as usize)?
                }
                _ => return None,
            };
            let not_parent = terms.mk_not_raw(current_term);
            let and_pos = new_proof.add_rule_step(
                AletheRule::AndPos(pos),
                vec![not_parent, child],
                Vec::new(),
                vec![current_term],
            );
            current_id = new_proof.add_resolution(vec![child], current_term, and_pos, current_id);
            current_term = child;
        }
        (current_term == expected).then_some(current_id)
    }

    /// Rebuild the proof as ONE certified Farkas lemma over the original
    /// bound assertions themselves — the "conjunction of linear facts is
    /// jointly infeasible" class (e.g. `x = N ∧ y = 0 ∧ N < x + y`), where
    /// preprocessing substituted the equalities into the remaining assertion
    /// and collapsed the whole contradiction into a premiseless trust leaf,
    /// and no disjunction/disequality backbone applies.
    ///
    /// 1. Refute the conjunction of ALL usable bounds (conjunct bounds
    ///    included; `(distinct ..)`-sugared bounds excluded — their
    ///    `distinct_elim` bridge is not strictly validated) with a fresh
    ///    LRA/LIA solver, demanding a Farkas certificate over a subset of
    ///    the asserted bounds.
    /// 2. RE-VERIFY the certificate with the independent
    ///    `verify_farkas_conflict_lits_full` checker and dry-run
    ///    `resolve_equality_coefficient_signs` (so the printed `la_generic`
    ///    args are exact) — both fail-closed, exactly as
    ///    `refute_disjunct_against_bounds` does. The solver's certificate is
    ///    never trusted on its own.
    /// 3. Emit `assume` steps for exactly the originals used (a conjunct
    ///    bound derives its unit from its root's assume via strictly
    ///    validated `and_pos` + resolution), ONE `la_generic` theory lemma
    ///    whose clause negates the conflict literals, and a binary
    ///    resolution chain to the empty clause.
    /// 4. WHOLE-PROOF revert gate (mirroring `promote_nia_pin_substitution`):
    ///    the rebuilt proof replaces the original only if the UNCHANGED
    ///    strict checker accepts it with `trust_count == 0`. The checker
    ///    re-verifies the linear combination SEMANTICALLY (Σλᵢ·cᵢ must
    ///    cancel every variable and contradict the constant under the
    ///    strict/nonstrict rules, equalities searched in both orientations,
    ///    Int tightening only where provably integer-valued) — annotation
    ///    presence alone proves nothing. Any gap keeps the existing proof.
    fn try_rebuild_with_pure_bounds(
        &mut self,
        proof: &mut Proof,
        originals: &[(TermId, FrontendTerm)],
        bound_specs: &[BoundSpec],
    ) -> bool {
        let usable: Vec<usize> = (0..bound_specs.len())
            .filter(|&i| bound_specs[i].distinct.is_none())
            .collect();
        if usable.is_empty() {
            return false;
        }

        // (1) Refute the bounds' conjunction with a fresh solver.
        let mut lra = ay_lra::LraSolver::new(&self.ctx.terms);
        lra.set_combined_theory_mode(true);
        for &si in &usable {
            TheorySolver::register_atom(&mut lra, atom_of(&self.ctx.terms, bound_specs[si].term));
        }
        for &si in &usable {
            let (atom, val) = match self.ctx.terms.get(bound_specs[si].term) {
                TermData::Not(inner) => (*inner, false),
                _ => (bound_specs[si].term, true),
            };
            TheorySolver::assert_literal(&mut lra, atom, val);
        }
        let TheoryResult::UnsatWithFarkas(conflict) = TheorySolver::check(&mut lra) else {
            return false;
        };
        let Some(farkas) = conflict.farkas.clone() else {
            return false;
        };
        if farkas.coefficients.len() != conflict.literals.len() || conflict.literals.is_empty() {
            return false;
        }
        // (2) Independent semantic re-verification + sign-resolution dry run.
        if ay_core::proof_validation::verify_farkas_conflict_lits_full(
            &self.ctx.terms,
            &conflict.literals,
            &farkas,
        )
        .is_err()
        {
            return false;
        }
        if ay_core::proof_validation::resolve_equality_coefficient_signs(
            &self.ctx.terms,
            &conflict.literals,
            &farkas,
        )
        .is_none()
        {
            return false;
        }

        // Map every conflict literal to the bound spec that asserted it
        // (same atom, same polarity), and build the blocking clause (the
        // conflict's negation).
        let mut lit_specs: Vec<usize> = Vec::with_capacity(conflict.literals.len());
        let mut blocking_clause: Vec<TermId> = Vec::with_capacity(conflict.literals.len());
        for lit in &conflict.literals {
            let pos = usable.iter().copied().find(|&si| {
                let spec = &bound_specs[si];
                let (atom, val) = match self.ctx.terms.get(spec.term) {
                    TermData::Not(inner) => (*inner, false),
                    _ => (spec.term, true),
                };
                atom == lit.term && val == lit.value
            });
            let Some(si) = pos else {
                return false;
            };
            lit_specs.push(si);
            blocking_clause.push(if lit.value {
                self.ctx.terms.mk_not_raw(lit.term)
            } else {
                lit.term
            });
        }

        // (3) Assemble: assumes first (Alethe ordering), then the `and_pos`
        // chains, the lemma, and the resolution chain to the empty clause.
        let mut new_proof = Proof::new();
        let mut bound_assume: HashMap<TermId, ProofId> = HashMap::default();
        let mut root_assumes: HashMap<TermId, ProofId> = HashMap::default();
        let mut conjunct_chains: Vec<(usize, ProofId)> = Vec::new();
        for &si in &lit_specs {
            let spec = &bound_specs[si];
            if bound_assume.contains_key(&spec.term) {
                continue;
            }
            if spec.path.is_empty() {
                let id = new_proof.add_assume(spec.term, None);
                bound_assume.insert(spec.term, id);
            } else {
                let root = originals[spec.original_idx].0;
                let id = *root_assumes
                    .entry(root)
                    .or_insert_with(|| new_proof.add_assume(root, None));
                conjunct_chains.push((si, id));
            }
        }
        for &(si, root_assume) in &conjunct_chains {
            let spec = &bound_specs[si];
            if bound_assume.contains_key(&spec.term) {
                continue;
            }
            let root = originals[spec.original_idx].0;
            let Some(unit) = Self::emit_and_pos_chain(
                &mut self.ctx.terms,
                &mut new_proof,
                root_assume,
                root,
                &spec.path,
                spec.term,
            ) else {
                return false;
            };
            bound_assume.insert(spec.term, unit);
        }

        let lemma_id = new_proof.add_step(ProofStep::TheoryLemma {
            theory: "LRA".to_string(),
            clause: blocking_clause.clone(),
            farkas: Some(farkas),
            kind: TheoryLemmaKind::LraFarkas,
            lia: None,
        });
        let mut current_clause = blocking_clause.clone();
        let mut current_proof = lemma_id;
        for (blit_idx, &blit) in blocking_clause.iter().enumerate() {
            if !current_clause.contains(&blit) {
                // A duplicated conflict literal was already resolved away.
                return false;
            }
            let pivot = atom_of(&self.ctx.terms, blit);
            let Some(&unit_id) = bound_assume.get(&bound_specs[lit_specs[blit_idx]].term) else {
                return false;
            };
            let resolvent: Vec<TermId> = current_clause
                .iter()
                .copied()
                .filter(|&l| l != blit)
                .collect();
            current_proof =
                new_proof.add_resolution(resolvent.clone(), pivot, current_proof, unit_id);
            current_clause = resolvent;
        }
        if !current_clause.is_empty() {
            return false;
        }

        // (4) Whole-proof revert gate: keep the rebuild ONLY if the strict
        // checker (unchanged — it re-verifies the Farkas combination
        // semantically) accepts it with zero trust steps.
        match ay_proof::check_proof_strict(&new_proof, &self.ctx.terms) {
            Ok(q) if q.trust_count == 0 => {}
            _ => return false,
        }

        // Success: swap the proof and register surface overrides for the
        // assumed originals, so the assumes — and the literals the chains
        // extract from them — print with the problem file's own syntax.
        if !surface_override_roots_have_bounded_work(
            &self.ctx.terms,
            lit_specs
                .iter()
                .map(|&spec| originals[bound_specs[spec].original_idx].0),
        ) {
            return false;
        }
        if self
            .last_proof_term_overrides
            .as_ref()
            .is_some_and(|overrides| !surface_override_map_is_bounded(overrides))
        {
            return false;
        }
        let mut overrides = self.last_proof_term_overrides.clone().unwrap_or_default();
        let mut registered: Vec<usize> = Vec::new();
        for &si in &lit_specs {
            let orig_idx = bound_specs[si].original_idx;
            if registered.contains(&orig_idx) {
                continue;
            }
            registered.push(orig_idx);
            let (canonical, parsed) = (originals[orig_idx].0, originals[orig_idx].1.clone());
            // Placeholder (native-API) surfaces register NO override — the
            // sentinel string is not a printable spelling.
            if is_api_placeholder(&parsed) {
                continue;
            }
            if !collect_surface_term_overrides(&mut self.ctx, canonical, &parsed, &mut overrides)
                || !surface_override_map_is_bounded(&overrides)
            {
                return false;
            }
        }
        *proof = new_proof;
        self.last_proof_term_overrides = Some(overrides);
        true
    }

    /// Collect every UNIT SOURCE reachable from the original assertions: an
    /// original that IS a (non-`and`) Bool-sorted literal (empty path), or a
    /// leaf of an original's canonical `and`-tree (derivable from the root's
    /// `assume` by strictly-validated `and_pos` + resolution steps —
    /// `emit_and_pos_chain`). Deliberately NO linearity gate: the
    /// complementary closure below is purely propositional, so any Bool
    /// literal qualifies (int-coded enum equalities, EUF atoms, plain
    /// Booleans alike). Returned in deterministic walk order (assertion
    /// order, then left-to-right through each `and`-tree); first source per
    /// term wins.
    fn collect_complementary_unit_sources(
        &self,
        originals: &[(TermId, FrontendTerm)],
    ) -> Vec<(TermId, usize, Vec<u32>)> {
        let mut order: Vec<(TermId, usize, Vec<u32>)> = Vec::new();
        let mut seen: HashMap<TermId, ()> = HashMap::default();
        for (idx, (canonical, _)) in originals.iter().enumerate() {
            let mut stack: Vec<(TermId, Vec<u32>)> = vec![(*canonical, Vec::new())];
            while let Some((term, path)) = stack.pop() {
                if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(term) {
                    if name == "and" && !args.is_empty() {
                        let args = args.clone();
                        // Reverse push keeps the pop order left-to-right.
                        for (i, &child) in args.iter().enumerate().rev() {
                            let Ok(pos) = u32::try_from(i) else { continue };
                            let mut child_path = path.clone();
                            child_path.push(pos);
                            stack.push((child, child_path));
                        }
                        continue;
                    }
                }
                if !matches!(self.ctx.terms.sort(term), Sort::Bool) {
                    continue;
                }
                if seen.insert(term, ()).is_none() {
                    order.push((term, idx, path));
                }
            }
        }
        order
    }

    /// Derive `(cl ¬node)` for an `and`-tree disjunct `node` from the proof
    /// of the COMPLEMENT of the leaf at `path`: per level, the premiseless
    /// tautology `and_pos(i) : (cl ¬parent child_i)` (strictly validated) is
    /// resolved — at the bottom against the leaf's complement unit, above
    /// against the level below's `(cl ¬child)` — leaving `(cl ¬parent)`.
    fn emit_neg_and_chain(
        terms: &mut TermStore,
        new_proof: &mut Proof,
        node: TermId,
        path: &[u32],
        leaf: TermId,
        leaf_complement_unit: ProofId,
    ) -> Option<ProofId> {
        let mut levels: Vec<(TermId, u32, TermId)> = Vec::with_capacity(path.len());
        let mut current = node;
        for &pos in path {
            let child = match terms.get(current) {
                TermData::App(Symbol::Named(name), args) if name == "and" => {
                    *args.get(pos as usize)?
                }
                _ => return None,
            };
            levels.push((current, pos, child));
            current = child;
        }
        if current != leaf || levels.is_empty() {
            return None;
        }
        let mut neg_child_proof: Option<ProofId> = None;
        for (depth, &(parent, pos, child)) in levels.iter().enumerate().rev() {
            let not_parent = terms.mk_not_raw(parent);
            let ap = new_proof.add_rule_step(
                AletheRule::AndPos(pos),
                vec![not_parent, child],
                Vec::new(),
                vec![parent],
            );
            let (elim, pivot) = if depth == levels.len() - 1 {
                // Bottom: resolve the leaf against its complement unit on the
                // leaf's ATOM (handles both `p`/`(not p)` orientations).
                (leaf_complement_unit, atom_of(terms, child))
            } else {
                // Above: resolve the (positive) `and` child against the level
                // below's `(cl ¬child)`.
                (neg_child_proof?, child)
            };
            neg_child_proof = Some(new_proof.add_resolution(vec![not_parent], pivot, ap, elim));
        }
        neg_child_proof
    }

    /// Complementary-literal propositional closure over the ORIGINAL
    /// assertions — the rebuild for ay-dpll's level-0 preprocessing
    /// collapses on syntactically contradictory assertion sets (the
    /// int-coded string-enum inductive-invariant class: `Init` pins
    /// `(= tee c)` while `¬J` conjoins `(not (= tee c))`), whose exported
    /// proof is a terminal trust-⊥ no Farkas backbone can replace (a
    /// disequality is not a Farkas premise).
    ///
    /// Two sub-shapes, both closed with ONLY strictly-validated rules
    /// (`assume`, `and_pos`, `or`, `resolution`) and gated by a whole-proof
    /// `check_proof_strict` revert check:
    ///
    /// 1. **Unit/unit**: two unit sources are syntactic complements `p` /
    ///    `(not p)` — two `and_pos` chains + one resolution derive `∅`.
    /// 2. **Disjunction/units**: an original `(or D1 .. Dn)` where EVERY
    ///    disjunct is refuted by the available units — either `Di`'s own
    ///    complement is a unit, or `Di` is an `and`-tree with a conjunct
    ///    whose complement is a unit (`(cl ¬Di)` via `emit_neg_and_chain`).
    ///    Covers the enum consecution shape (`Next = or-of-actions`, each
    ///    action pinning the enum var against a `¬J'` conjunct) and the
    ///    safety shape (`J = or-of-equalities` against the `¬J`
    ///    conjunction).
    ///
    /// Sound by construction: the rebuilt proof's axioms are original
    /// assertions and every inference is checker-validated — it cannot exist
    /// unless the asserted contradiction is real. Fail-closed: any miss
    /// keeps the existing (honestly defective) proof.
    fn try_rebuild_with_complementary_literals(
        &mut self,
        proof: &mut Proof,
        originals: &[(TermId, FrontendTerm)],
    ) -> bool {
        let unit_sources = self.collect_complementary_unit_sources(originals);
        let mut unit_index: HashMap<TermId, usize> = HashMap::default();
        for (i, (term, _, _)) in unit_sources.iter().enumerate() {
            unit_index.entry(*term).or_insert(i);
        }

        // ---- Shape 1: a complementary unit pair. ----
        for (term, _, _) in &unit_sources {
            let TermData::Not(inner) = self.ctx.terms.get(*term) else {
                continue;
            };
            let (neg_term, pos_term) = (*term, *inner);
            let Some(&pos_i) = unit_index.get(&pos_term) else {
                continue;
            };
            let neg_i = unit_index[&neg_term];
            let (_, pos_orig, pos_path) = &unit_sources[pos_i];
            let (_, neg_orig, neg_path) = &unit_sources[neg_i];

            let mut new_proof = Proof::new();
            let mut root_assumes: HashMap<TermId, ProofId> = HashMap::default();
            let pos_root = originals[*pos_orig].0;
            let neg_root = originals[*neg_orig].0;
            let pos_assume = *root_assumes
                .entry(pos_root)
                .or_insert_with(|| new_proof.add_assume(pos_root, None));
            let neg_assume = *root_assumes
                .entry(neg_root)
                .or_insert_with(|| new_proof.add_assume(neg_root, None));
            let (Some(pos_unit), Some(neg_unit)) = (
                Self::emit_and_pos_chain(
                    &mut self.ctx.terms,
                    &mut new_proof,
                    pos_assume,
                    pos_root,
                    pos_path,
                    pos_term,
                ),
                Self::emit_and_pos_chain(
                    &mut self.ctx.terms,
                    &mut new_proof,
                    neg_assume,
                    neg_root,
                    neg_path,
                    neg_term,
                ),
            ) else {
                continue;
            };
            new_proof.add_resolution(Vec::new(), pos_term, neg_unit, pos_unit);
            if self.accept_complementary_rebuild(
                proof,
                new_proof,
                originals,
                &[*pos_orig, *neg_orig],
            ) {
                return true;
            }
        }

        // ---- Shape 2: an original disjunction, every disjunct refuted by a
        // complementary unit (directly or through one of its conjuncts). ----
        'roots: for (disj_idx, (or_root, parsed)) in originals.iter().enumerate() {
            let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(*or_root) else {
                continue;
            };
            if name != "or" || args.len() < 2 {
                continue;
            }
            let disjuncts = args.clone();
            // Distinct pivot atoms keep the per-disjunct elimination exact.
            let mut atoms: Vec<TermId> = disjuncts
                .iter()
                .map(|&d| atom_of(&self.ctx.terms, d))
                .collect();
            atoms.sort_unstable();
            atoms.dedup();
            if atoms.len() != disjuncts.len() {
                continue;
            }
            // Surface fidelity: a non-placeholder root must be a literal
            // `(or ...)` whose operands re-elaborate to exactly the canonical
            // disjuncts (the printed step literals must match the problem
            // file). Placeholder (native-API) roots have no surface to align.
            if !is_api_placeholder(parsed) {
                let FrontendTerm::App(op, operands) = strip_frontend_annotations(parsed) else {
                    continue;
                };
                if op != "or" || operands.len() != disjuncts.len() {
                    continue;
                }
                let operands = operands.clone();
                for (surface, &canonical_lit) in operands.iter().zip(disjuncts.iter()) {
                    if self.ctx.elaborate_surface_subterm(surface) != Some(canonical_lit) {
                        continue 'roots;
                    }
                }
            }

            // Plan the elimination of every disjunct. `(leaf, path-in-Di,
            // unit index)`: an empty path means the disjunct ITSELF resolves
            // against the unit; a non-empty path derives `(cl ¬Di)` first.
            let mut plans: Vec<(TermId, Vec<u32>, usize)> = Vec::with_capacity(disjuncts.len());
            for &di in &disjuncts {
                let Some(plan) = self.plan_disjunct_complement(di, disj_idx, &unit_sources) else {
                    continue 'roots;
                };
                plans.push(plan);
            }

            // Assemble: assumes first (Alethe ordering), then unit chains,
            // the `or` decomposition, and the elimination resolutions.
            let mut new_proof = Proof::new();
            let mut root_assumes: HashMap<TermId, ProofId> = HashMap::default();
            let disj_assume = *root_assumes
                .entry(*or_root)
                .or_insert_with(|| new_proof.add_assume(*or_root, None));
            let mut used_originals: Vec<usize> = vec![disj_idx];
            for &(_, _, ui) in &plans {
                let (_, orig_idx, _) = &unit_sources[ui];
                let root = originals[*orig_idx].0;
                root_assumes
                    .entry(root)
                    .or_insert_with(|| new_proof.add_assume(root, None));
                if !used_originals.contains(orig_idx) {
                    used_originals.push(*orig_idx);
                }
            }
            let mut unit_proofs: HashMap<TermId, ProofId> = HashMap::default();
            for &(_, _, ui) in &plans {
                let (unit_term, orig_idx, unit_path) = &unit_sources[ui];
                if unit_proofs.contains_key(unit_term) {
                    continue;
                }
                let root = originals[*orig_idx].0;
                let root_assume = root_assumes[&root];
                let Some(unit) = Self::emit_and_pos_chain(
                    &mut self.ctx.terms,
                    &mut new_proof,
                    root_assume,
                    root,
                    unit_path,
                    *unit_term,
                ) else {
                    continue 'roots;
                };
                unit_proofs.insert(*unit_term, unit);
            }

            let or_step = new_proof.add_rule_step(
                AletheRule::Or,
                disjuncts.clone(),
                vec![disj_assume],
                Vec::new(),
            );

            let mut current_clause = disjuncts.clone();
            let mut current_proof = or_step;
            for (di_idx, &(leaf, ref leaf_path, ui)) in plans.iter().enumerate() {
                let di = disjuncts[di_idx];
                let unit_term = unit_sources[ui].0;
                let unit_proof = unit_proofs[&unit_term];
                let (elim_proof, pivot) = if leaf_path.is_empty() {
                    // The unit IS the disjunct's complement.
                    (unit_proof, atom_of(&self.ctx.terms, di))
                } else {
                    // Derive `(cl ¬Di)` from the conjunct's complement.
                    let Some(neg_di) = Self::emit_neg_and_chain(
                        &mut self.ctx.terms,
                        &mut new_proof,
                        di,
                        leaf_path,
                        leaf,
                        unit_proof,
                    ) else {
                        continue 'roots;
                    };
                    (neg_di, di)
                };
                let resolvent: Vec<TermId> = current_clause
                    .iter()
                    .copied()
                    .filter(|&l| l != di)
                    .collect();
                current_proof =
                    new_proof.add_resolution(resolvent.clone(), pivot, current_proof, elim_proof);
                current_clause = resolvent;
            }
            if !current_clause.is_empty() {
                continue;
            }
            if self.accept_complementary_rebuild(proof, new_proof, originals, &used_originals) {
                return true;
            }
        }
        false
    }

    /// Find the complement plan for one disjunct: `(leaf, path-in-disjunct,
    /// unit index)` — empty path when the disjunct's own complement is a
    /// unit, else the first (left-to-right) conjunct of the disjunct's
    /// `and`-tree whose complement is a unit. Units sourced from the
    /// disjunction original itself are skipped (its walk only yields the
    /// whole root, which cannot refute its own disjunct).
    fn plan_disjunct_complement(
        &mut self,
        di: TermId,
        disj_idx: usize,
        unit_sources: &[(TermId, usize, Vec<u32>)],
    ) -> Option<(TermId, Vec<u32>, usize)> {
        let complement_unit = |me: &mut Self, lit: TermId| -> Option<usize> {
            let comp = match me.ctx.terms.get(lit) {
                TermData::Not(inner) => *inner,
                _ => me.ctx.terms.mk_not_raw(lit),
            };
            unit_sources
                .iter()
                .position(|&(t, orig, _)| t == comp && orig != disj_idx)
        };
        if let Some(ui) = complement_unit(self, di) {
            return Some((di, Vec::new(), ui));
        }
        // Left-to-right walk of the disjunct's `and`-tree.
        let mut stack: Vec<(TermId, Vec<u32>)> = Vec::new();
        if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(di) {
            if name == "and" && !args.is_empty() {
                let args = args.clone();
                for (i, &child) in args.iter().enumerate().rev() {
                    let Ok(pos) = u32::try_from(i) else { continue };
                    stack.push((child, vec![pos]));
                }
            }
        }
        while let Some((term, path)) = stack.pop() {
            if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(term) {
                if name == "and" && !args.is_empty() {
                    let args = args.clone();
                    for (i, &child) in args.iter().enumerate().rev() {
                        let Ok(pos) = u32::try_from(i) else { continue };
                        let mut child_path = path.clone();
                        child_path.push(pos);
                        stack.push((child, child_path));
                    }
                    continue;
                }
            }
            if let Some(ui) = complement_unit(self, term) {
                return Some((term, path, ui));
            }
        }
        None
    }

    /// Whole-proof revert gate + swap + surface overrides for the
    /// complementary-literal rebuild (mirrors `try_rebuild_with_pure_bounds`
    /// step 4): the rebuilt proof replaces the original ONLY if the
    /// UNCHANGED strict checker accepts it with zero trust steps.
    fn accept_complementary_rebuild(
        &mut self,
        proof: &mut Proof,
        new_proof: Proof,
        originals: &[(TermId, FrontendTerm)],
        used_originals: &[usize],
    ) -> bool {
        match ay_proof::check_proof_strict(&new_proof, &self.ctx.terms) {
            Ok(q) if q.trust_count == 0 => {}
            _ => return false,
        }
        if !surface_override_roots_have_bounded_work(
            &self.ctx.terms,
            used_originals.iter().map(|&index| originals[index].0),
        ) {
            return false;
        }
        if self
            .last_proof_term_overrides
            .as_ref()
            .is_some_and(|overrides| !surface_override_map_is_bounded(overrides))
        {
            return false;
        }
        let mut overrides = self.last_proof_term_overrides.clone().unwrap_or_default();
        let mut registered: Vec<usize> = Vec::new();
        for &orig_idx in used_originals {
            if registered.contains(&orig_idx) {
                continue;
            }
            registered.push(orig_idx);
            let (canonical, parsed) = (originals[orig_idx].0, originals[orig_idx].1.clone());
            // Placeholder (native-API) surfaces register NO override — the
            // sentinel string is not a printable spelling.
            if is_api_placeholder(&parsed) {
                continue;
            }
            if !collect_surface_term_overrides(&mut self.ctx, canonical, &parsed, &mut overrides)
                || !surface_override_map_is_bounded(&overrides)
            {
                return false;
            }
        }
        *proof = new_proof;
        self.last_proof_term_overrides = Some(overrides);
        true
    }

    // -----------------------------------------------------------------------
    // Substitution-derived `assume` bridge (theory-agnostic).
    // -----------------------------------------------------------------------

    /// Replace every preprocessing-substituted `assume` leaf with a certified
    /// derivation from the AUTHORED assertion it came from, keeping the rest
    /// of the exported proof byte-identical in structure.
    ///
    /// Constant/definition propagation rewrites `(str.in_re literal_5 R)` into
    /// `(str.in_re "/mod/forum/" R)` before clausification, so the exported
    /// proof assumes a formula that is NOT a problem premise — the Alethe
    /// printer refuses it (`NonProblemAssume`) and `--self-check` degrades the
    /// UNSAT to `unknown`. The link back to the problem is exactly the
    /// congruence axiom: from the authored predicate `P(a1..an)` and the
    /// authored defining equalities `(= ai bi)`, `eq_congruent_pred` yields
    /// `P(b1..bn)`.
    ///
    /// This pass is deliberately THEORY-AGNOSTIC: it never inspects the
    /// predicate's theory, only its congruence structure, so it repairs the
    /// same defect for strings, EUF, datatypes, or anything else. Every rule
    /// it emits (`refl`, `symm`, `eq_congruent`, `eq_congruent_pred`,
    /// `th_resolution`) is validated by the UNCHANGED strict checker, and the
    /// whole rebuilt proof must pass `check_proof_collecting_trust` carrying
    /// NO trust obligation the proof it replaces did not already carry — so
    /// this can only make MORE proofs genuinely checkable, never fewer.
    ///
    /// Fail-closed: any leaf that cannot be derived, any dangling premise, or
    /// a rebuilt proof the checker likes less than the original leaves the
    /// proof untouched.
    fn try_rebuild_with_substitution_bridge(
        &mut self,
        proof: &mut Proof,
        originals: &[(TermId, FrontendTerm)],
    ) -> bool {
        let original_terms: Vec<TermId> = originals.iter().map(|(c, _)| *c).collect();

        // (1) Which generated leaves are defective?
        //
        // Only leaves REACHABLE from an empty-clause step matter: the #8821
        // authority gate (`validate_reachable_assumes_in_problem_scope`) walks
        // the dependency cone of the empty clause and ignores everything
        // outside it. A defective leaf on a dead branch (e.g. an abandoned
        // extensionality split whose
        // `__ay_ext_diff_*` witness assumes survive in the step list) therefore
        // carries NO authority claim, and must not veto repairing the leaves
        // that do. Unreachable steps are omitted from the rebuilt proof: an
        // external checker validates every serialized command, not only the
        // final empty clause's dependency cone.
        let reachable = Self::reachable_step_mask(proof);
        let mut defective: Vec<TermId> = Vec::new();
        for (idx, step) in proof.steps.iter().enumerate() {
            let term = match step {
                ProofStep::Assume(term) => Some(*term),
                // The provenance demotion pass runs before this final repair
                // and converts a generated Assume into an explicit unit
                // `trust`. It is still repairable only when the same
                // substitution planner derives that exact unit from authored
                // premises; arbitrary trust clauses remain untouched.
                ProofStep::Step {
                    rule: AletheRule::Trust,
                    clause,
                    premises,
                    ..
                } if premises.is_empty() && clause.len() == 1 => Some(clause[0]),
                // A GENERIC-kind unit theory lemma is the same defect in a
                // different coat: an unpedigreed leaf the strict checker
                // rejects by kind. The DT lazy lane's indexed-authority
                // recording (2026-08-20) moved its propagated
                // selector-through-equality leaves from unit `trust` steps to
                // exactly this shape, which silently disengaged the bridge —
                // the leaf is unchanged, only its spelling moved. Same repair
                // contract: derivable from authored premises or left as-is.
                ProofStep::TheoryLemma {
                    kind: TheoryLemmaKind::Generic,
                    clause,
                    ..
                } if clause.len() == 1 => Some(clause[0]),
                _ => None,
            };
            let Some(term) = term else {
                continue;
            };
            if !reachable[idx] || original_terms.contains(&term) {
                continue;
            }
            if !defective.contains(&term) {
                defective.push(term);
            }
        }
        if defective.is_empty() {
            return false;
        }
        if ay_core::misc_cli_flags().debug_cert {
            ay_core::safe_eprintln!(
                "c !! substitution-bridge entered: {} defective leaf(s)",
                defective.len()
            );
        }

        // (2) Plan a congruence bridge for each defective leaf. Planning is
        // pure w.r.t. the proof (it only interns the equality/lemma terms the
        // emission will need), so a failure costs nothing.
        let mut plans: Vec<BridgePlan> = Vec::with_capacity(defective.len());
        // A defective leaf that is a STANDALONE checkable tautology needs no
        // bridge from an authored source at all — validity is intrinsic. The
        // canonical instance is definition substitution rewriting an
        // ite/store clausification unit into
        // `(or (= 42 (select a (+ i 1))) (not (= i (+ i 1))))`, which no
        // congruence bridge can reach (there is no single authored source)
        // but the arithmetic refuter re-derives outright. Both recognizers
        // ARE their strict validators, and the whole-proof gate below
        // re-checks every emitted lemma, so nothing unproven is admitted.
        let mut tautology_leaves: Vec<(TermId, TheoryLemmaKind)> = Vec::new();
        for &goal in &defective {
            if ay_proof::recognize_bool_tautology(&self.ctx.terms, &[goal]) {
                tautology_leaves.push((goal, TheoryLemmaKind::BoolTautology));
            } else if ay_proof::recognize_arith_clause_tautology(&self.ctx.terms, &[goal]) {
                tautology_leaves.push((goal, TheoryLemmaKind::ArithClauseTautology));
            } else if ay_proof::recognize_euf_transitive(&self.ctx.terms, &[goal]) {
                // Or-packed EUF transitivity chain (the validator flattens the
                // packed unit): `¬(a=b) ∨ ¬(c=a) ∨ (c=b)` — intrinsically
                // valid, produced by congruence-closure explanation recording.
                tautology_leaves.push((goal, TheoryLemmaKind::EufTransitive));
            } else if ay_proof::recognize_euf_congruent(&self.ctx.terms, &[goal]) {
                // Its congruence sibling: `¬(a=b) ∨ (f a c) = (f b c)` — the
                // extensionality-instance shape array preprocessing emits.
                tautology_leaves.push((goal, TheoryLemmaKind::EufCongruent));
            } else if ay_proof::recognize_ite_branch_projection(&self.ctx.terms, &[goal]) {
                tautology_leaves.push((goal, TheoryLemmaKind::IteBranchProjection));
            } else if ay_proof::recognize_array_guarded_row_expansion(&self.ctx.terms, &[goal]) {
                tautology_leaves.push((goal, TheoryLemmaKind::ArrayGuardedRowExpansion));
            } else if {
                let decls = self.datatype_decls_for_strict_proof();
                let selectors = self.ctor_selector_decls_for_strict_proof();
                !decls.is_empty()
                    && ay_proof::recognize_datatype_tester_eval_with_selectors(
                        &self.ctx.terms,
                        &[goal],
                        &decls,
                        &selectors,
                    )
            } {
                // Tester evaluation over a constructor application
                // (`((_ is B) B)`), registry-validated.
                tautology_leaves.push((goal, TheoryLemmaKind::DatatypeTesterEval));
            } else if ay_proof::recognize_array_finite_select_expansion(&self.ctx.terms, &[goal]) {
                // The Bool/finite-carrier symbolic-select expansion axiom the
                // array solver injects (`(ite p (= (select A true) (select A p))
                // (= (select A false) (select A p)))`) — an intrinsic
                // array-theory tautology whose exhaustiveness the typed
                // validator re-derives point by point.
                tautology_leaves.push((goal, TheoryLemmaKind::ArrayFiniteSelectExpansion));
            }
        }
        // A POSITIVE-EQUALITY leaf may be derivable outright by the equality
        // planner (refl / authored / symm / cong / trans-through-definition /
        // ground-eval / selector-chase legs), with no predicate-congruence
        // bridge from a single source at all. The datatype selector
        // propagation leaf `(= a (top x))` under `x ~ y ~ stack(a, empty)`
        // is the canonical case: its derivation is projection + congruence +
        // transitivity across TWO authored equalities.
        let mut eq_planned_leaves: Vec<(TermId, EqPlan)> = Vec::new();
        // DERIVED TESTER facts: `((_ is C) t)` (either polarity) where `t` is
        // derivably equal to a candidate `k` on which the same-polarity
        // tester fact is a registry-validated `DatatypeTesterEval` tautology
        // (`is-stack(s1)` under `s1 ~ s0 ~ stack(..)`). Assembled below as
        // eq_congruent_pred over the unary tester predicate, resolved with
        // the eq-plan unit and the tester-eval lemma.
        let mut tester_leaves: Vec<DerivedTesterLeaf> = Vec::new();
        for &goal in &defective {
            if tautology_leaves.iter().any(|&(term, _)| term == goal) {
                continue;
            }
            if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(goal) {
                if name == "=" && args.len() == 2 {
                    let (lhs, rhs) = (args[0], args[1]);
                    let mut budget = EQ_PLAN_BUDGET;
                    if let Some(plan) = self.plan_eq(lhs, rhs, &original_terms, 0, &mut budget) {
                        eq_planned_leaves.push((goal, plan));
                        continue;
                    }
                }
            }
            if let Some(leaf) = self.plan_derived_tester_leaf(goal, &original_terms) {
                tester_leaves.push(leaf);
                continue;
            }
            let Some(plan) = self.plan_substitution_bridge(goal, &original_terms) else {
                // Which leaf the repair gave up on is the one fact a
                // strict-decline triage needs (same disclosure rationale as
                // `TRUST step rejected` in the checker). Typed carrier only.
                if ay_core::misc_cli_flags().debug_cert {
                    ay_core::safe_eprintln!(
                        "c !! substitution-bridge plan FAILED for defective leaf {goal:?}: {}",
                        ay_proof::render_term_canonical(&self.ctx.terms, goal)
                    );
                }
                return false;
            };
            plans.push(plan);
        }
        let self_contained_surface = plans.iter().any(BridgePlan::uses_ground_evaluate);

        // (3) Originals the rebuilt proof will assume: the ones the surviving
        // skeleton already assumed, plus every premise the bridges need.
        let mut needed: Vec<TermId> = Vec::new();
        let push_needed = |t: TermId, needed: &mut Vec<TermId>| {
            if !needed.contains(&t) {
                needed.push(t);
            }
        };
        for (idx, step) in proof.steps.iter().enumerate() {
            if !reachable[idx] {
                continue;
            }
            if let ProofStep::Assume(term) = step {
                if original_terms.contains(term) {
                    push_needed(*term, &mut needed);
                }
            }
        }
        for plan in &plans {
            push_needed(plan.source, &mut needed);
            for kid in &plan.kids {
                kid.collect_assumed(&mut needed);
            }
        }
        for (_, plan) in &eq_planned_leaves {
            let mut assumed = Vec::new();
            plan.collect_assumed(&mut assumed);
            for term in assumed {
                push_needed(term, &mut needed);
            }
        }
        for leaf in &tester_leaves {
            let mut assumed = Vec::new();
            leaf.eq_plan.collect_assumed(&mut assumed);
            for term in assumed {
                push_needed(term, &mut needed);
            }
        }
        // Every assumed term must genuinely be an original premise.
        if needed.iter().any(|t| !original_terms.contains(t)) {
            if ay_core::misc_cli_flags().debug_cert {
                for t in needed.iter().filter(|t| !original_terms.contains(t)) {
                    ay_core::safe_eprintln!(
                        "c !! substitution-bridge refused: needed premise is not authored: {}",
                        ay_proof::render_term_canonical(&self.ctx.terms, *t)
                    );
                }
            }
            return false;
        }

        // (4) Assemble: assumes first (Alethe ordering), then the bridge
        // derivations, then the surviving skeleton with premises remapped.
        let mut new_proof = Proof::new();
        let mut assume_ids: HashMap<TermId, ProofId> = HashMap::default();
        let mut raw_authored_to_record: Vec<TermId> = Vec::new();
        if self_contained_surface {
            // A surface override changes printing only; internally-generated
            // congruence terms still reference the canonical ids. That is not
            // enough when a nested ground concat was folded during
            // elaboration: the serialized source and conclusion cease to be
            // syntactically linked. Reconstruct every needed authored premise
            // recursively, assume that exact raw term, and explicitly derive
            // its canonical form before using the ordinary substitution plan.
            let mut surface_plans: Vec<SurfaceAssumePlan> = Vec::with_capacity(needed.len());
            for &canonical in &needed {
                let Some(idx) = original_terms
                    .iter()
                    .position(|&original| original == canonical)
                else {
                    return false;
                };
                let parsed = originals[idx].1.clone();
                let raw = if is_api_placeholder(&parsed) {
                    canonical
                } else {
                    let Some(raw) = self.raw_intern_surface(&parsed) else {
                        return false;
                    };
                    raw
                };
                if !raw_authored_to_record.contains(&raw) {
                    raw_authored_to_record.push(raw);
                }

                let canonicalization = if raw == canonical {
                    SurfaceCanonicalization::Direct
                } else if matches!(parsed_head(&parsed), Some("distinct")) {
                    if !Self::is_matching_binary_distinct(&self.ctx.terms, canonical, raw) {
                        return false;
                    }
                    SurfaceCanonicalization::Distinct
                } else {
                    let mut budget = EQ_PLAN_BUDGET;
                    let Some(plan) = self.plan_substitution_bridge_from_source_with_budget(
                        canonical,
                        raw,
                        &original_terms,
                        &mut budget,
                    ) else {
                        return false;
                    };
                    SurfaceCanonicalization::Bridge(plan)
                };
                surface_plans.push(SurfaceAssumePlan {
                    canonical,
                    raw,
                    canonicalization,
                });
            }

            let mut distinct_assumes: Vec<(TermId, TermId, ProofId)> = Vec::new();
            let mut pending_surface_bridges: Vec<BridgePlan> = Vec::new();
            for surface in surface_plans {
                let assume_id = if let Some(&existing) = assume_ids.get(&surface.raw) {
                    existing
                } else {
                    let id = new_proof.add_assume(surface.raw, None);
                    assume_ids.insert(surface.raw, id);
                    id
                };
                match surface.canonicalization {
                    SurfaceCanonicalization::Direct => {
                        assume_ids.insert(surface.canonical, assume_id);
                    }
                    SurfaceCanonicalization::Distinct => {
                        distinct_assumes.push((surface.canonical, surface.raw, assume_id));
                    }
                    SurfaceCanonicalization::Bridge(plan) => {
                        pending_surface_bridges.push(plan);
                    }
                }
            }
            for (diseq, distinct, assume_id) in distinct_assumes {
                let Some(unit) = Self::emit_binary_distinct_bridge(
                    &mut self.ctx.terms,
                    &mut new_proof,
                    diseq,
                    distinct,
                    assume_id,
                ) else {
                    return false;
                };
                assume_ids.insert(diseq, unit);
            }
            // A raw premise's canonicalization can depend on another
            // canonical authored equality. Emit in dependency order and fail
            // closed on a cycle or missing source.
            while !pending_surface_bridges.is_empty() {
                let ready = pending_surface_bridges.iter().position(|plan| {
                    let mut assumed = Vec::new();
                    for kid in &plan.kids {
                        kid.collect_assumed(&mut assumed);
                    }
                    assumed.iter().all(|term| assume_ids.contains_key(term))
                });
                let Some(ready) = ready else {
                    return false;
                };
                let plan = pending_surface_bridges.remove(ready);
                let Some(unit) = Self::emit_substitution_bridge(
                    &mut self.ctx.terms,
                    &mut new_proof,
                    &plan,
                    &assume_ids,
                ) else {
                    return false;
                };
                assume_ids.insert(plan.goal, unit);
            }
        } else {
            let mut distinct_assumes: Vec<(TermId, TermId, ProofId)> = Vec::new();
            for &term in &needed {
                let Some(idx) = original_terms.iter().position(|&original| original == term) else {
                    return false;
                };
                let parsed = &originals[idx].1;
                if matches!(parsed_head(parsed), Some("distinct")) {
                    // Binary `distinct` elaborates to `(not (= s t))`, but an
                    // Alethe `assume` must retain the problem's actual surface
                    // term. Derive the canonical disequality through
                    // `distinct_elim` + `equiv_pos2`.
                    let TermData::Not(eq) = self.ctx.terms.get(term) else {
                        return false;
                    };
                    let eq = *eq;
                    let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(eq) else {
                        return false;
                    };
                    if name != "=" || args.len() != 2 {
                        return false;
                    }
                    let args = args.clone();
                    let FrontendTerm::App(surface_name, surface_args) =
                        strip_frontend_annotations(parsed)
                    else {
                        return false;
                    };
                    if surface_name != "distinct" || surface_args.len() != 2 {
                        return false;
                    }
                    let Some(raw_args) = surface_args
                        .iter()
                        .map(|arg| self.raw_intern_surface(arg))
                        .collect::<Option<Vec<_>>>()
                    else {
                        return false;
                    };
                    if raw_args.as_slice() != args.as_slice() {
                        // `distinct_elim` below proves the canonical
                        // disequality only for these exact operands. A nested
                        // source fold needs its own explicit bridge; treating
                        // the shallow canonical pair as authored would grant
                        // authority to a term absent from the problem.
                        return false;
                    }
                    let distinct =
                        self.ctx
                            .terms
                            .mk_app(Symbol::named("distinct"), raw_args, Sort::Bool);
                    if !Self::is_matching_binary_distinct(&self.ctx.terms, term, distinct) {
                        return false;
                    }
                    let id = new_proof.add_assume(distinct, None);
                    distinct_assumes.push((term, distinct, id));
                } else {
                    let id = new_proof.add_assume(term, None);
                    assume_ids.insert(term, id);
                }
            }
            for (diseq, distinct, assume_id) in distinct_assumes {
                let Some(unit) = Self::emit_binary_distinct_bridge(
                    &mut self.ctx.terms,
                    &mut new_proof,
                    diseq,
                    distinct,
                    assume_id,
                ) else {
                    return false;
                };
                assume_ids.insert(diseq, unit);
            }
        }

        let mut bridge_unit: HashMap<TermId, ProofId> = HashMap::default();
        for &(term, kind) in &tautology_leaves {
            let theory = match kind {
                TheoryLemmaKind::ArithClauseTautology => "arith",
                TheoryLemmaKind::ArrayFiniteSelectExpansion
                | TheoryLemmaKind::ArrayGuardedRowExpansion => "array",
                TheoryLemmaKind::EufTransitive | TheoryLemmaKind::EufCongruent => "EUF",
                TheoryLemmaKind::DatatypeTesterEval => "DT",
                TheoryLemmaKind::IteBranchProjection => "ite",
                _ => "bool",
            };
            let unit = new_proof.add_step(ProofStep::TheoryLemma {
                theory: theory.to_string(),
                clause: vec![term],
                farkas: None,
                kind,
                lia: None,
            });
            bridge_unit.insert(term, unit);
        }
        for (term, plan) in &eq_planned_leaves {
            let Some(unit) = Self::emit_eq_plan(&mut new_proof, plan, &assume_ids) else {
                if ay_core::misc_cli_flags().debug_cert {
                    ay_core::safe_eprintln!(
                        "c !! substitution-bridge refused: eq-plan emission failed for {}",
                        ay_proof::render_term_canonical(&self.ctx.terms, *term)
                    );
                }
                return false;
            };
            bridge_unit.insert(*term, unit);
        }
        for leaf in &tester_leaves {
            let Some(unit) = self.emit_derived_tester_leaf(&mut new_proof, leaf, &assume_ids)
            else {
                if ay_core::misc_cli_flags().debug_cert {
                    ay_core::safe_eprintln!(
                        "c !! substitution-bridge refused: derived-tester emission failed for {}",
                        ay_proof::render_term_canonical(&self.ctx.terms, leaf.goal)
                    );
                }
                return false;
            };
            bridge_unit.insert(leaf.goal, unit);
        }
        for plan in &plans {
            let Some(unit) = Self::emit_substitution_bridge(
                &mut self.ctx.terms,
                &mut new_proof,
                plan,
                &assume_ids,
            ) else {
                return false;
            };
            bridge_unit.insert(plan.goal, unit);
        }

        let mut remap: Vec<Option<ProofId>> = vec![None; proof.steps.len()];
        for (idx, step) in proof.steps.iter().enumerate() {
            if !reachable[idx] {
                continue;
            }
            let new_id = match step {
                ProofStep::Assume(term) => match assume_ids.get(term) {
                    Some(&id) => id,
                    None => match bridge_unit.get(term) {
                        Some(&id) => id,
                        None => return false,
                    },
                },
                ProofStep::Resolution {
                    clause,
                    pivot,
                    clause1,
                    clause2,
                } => {
                    let (Some(c1), Some(c2)) = (
                        remap.get(clause1.0 as usize).copied().flatten(),
                        remap.get(clause2.0 as usize).copied().flatten(),
                    ) else {
                        return false;
                    };
                    new_proof.add_resolution(clause.clone(), *pivot, c1, c2)
                }
                ProofStep::TheoryLemma {
                    theory,
                    clause,
                    farkas,
                    kind,
                    lia,
                } => {
                    // The Generic-coat defective leaf (see the collector):
                    // swap in the derived bridge unit exactly like a repaired
                    // unit `trust` step.
                    if matches!(kind, TheoryLemmaKind::Generic) && clause.len() == 1 {
                        if let Some(&id) = bridge_unit.get(&clause[0]) {
                            remap[idx] = Some(id);
                            continue;
                        }
                    }
                    new_proof.add_step(ProofStep::TheoryLemma {
                        theory: theory.clone(),
                        clause: clause.clone(),
                        farkas: farkas.clone(),
                        kind: *kind,
                        lia: lia.clone(),
                    })
                }
                ProofStep::Step {
                    rule,
                    clause,
                    premises,
                    args,
                } => {
                    if matches!(rule, AletheRule::Trust) && premises.is_empty() && clause.len() == 1
                    {
                        if let Some(&id) = bridge_unit.get(&clause[0]) {
                            remap[idx] = Some(id);
                            continue;
                        }
                    }
                    let mut mapped = Vec::with_capacity(premises.len());
                    for p in premises {
                        match remap.get(p.0 as usize).copied().flatten() {
                            Some(id) => mapped.push(id),
                            None => return false,
                        }
                    }
                    new_proof.add_rule_step(rule.clone(), clause.clone(), mapped, args.clone())
                }
                // Anchors and any other step shape carry scoped structure this
                // pass does not model; refuse rather than reorder them.
                _ => return false,
            };
            remap[idx] = Some(new_id);
        }

        // (5) Whole-proof gate: the rebuilt derivation must be at least as
        // checkable as the one it replaces. DEFERRED-trust mode is the right
        // yardstick here — this pass runs BEFORE the Generic-lemma promotion
        // passes, so the surviving skeleton legitimately still carries
        // trust-kind lemmas that a later pass promotes (the string
        // ground-evaluation lemma is exactly one). Every OTHER step, including
        // every step this pass emits, must validate strictly, and the rebuilt
        // proof must not introduce a trust obligation the original did not
        // already carry.
        // The gate runs with the executor's own datatype context when the
        // exact member signatures exist: the selector-chase leg emits
        // registry-gated `DatatypeSelectorProject` lemmas which the plain
        // context-free checker rejects fail-closed by design. Problems with
        // no datatypes carry empty registries and behave exactly as before.
        let decls = self.datatype_decls_for_strict_proof();
        let selectors = self.ctor_selector_decls_for_strict_proof();
        let member_signatures = self.datatype_member_signatures_for_strict_proof();
        let gate = |target: &Proof| -> Result<Vec<Vec<TermId>>, ()> {
            let collected = match member_signatures.as_ref() {
                Some(signatures) => ay_proof::check_proof_collecting_trust_with_typed_context(
                    target,
                    &self.ctx.terms,
                    (!decls.is_empty()).then_some(decls.as_slice()),
                    (!selectors.is_empty()).then_some(selectors.as_slice()),
                    signatures.as_slice(),
                    None,
                ),
                None => ay_proof::check_proof_collecting_trust(target, &self.ctx.terms),
            }
            .map_err(|_| ())?;
            Ok(collected.into_iter().map(|(_, clause)| clause).collect())
        };
        let before = gate(proof).ok();
        let after: Vec<Vec<TermId>> = match gate(&new_proof) {
            Ok(collected) => collected,
            Err(()) => return false,
        };
        let Some(before) = before else {
            // The original did not even pass deferred-trust validation; this
            // pass is not the one to reason about what it was doing.
            return false;
        };
        if after.len() > before.len() || after.iter().any(|clause| !before.contains(clause)) {
            if ay_core::misc_cli_flags().debug_cert {
                ay_core::safe_eprintln!(
                    "c !! substitution-bridge refused: rebuilt proof defers {} clause(s), original {}",
                    after.len(),
                    before.len()
                );
            }
            return false;
        }

        if self_contained_surface {
            *proof = new_proof;
            if ay_core::misc_cli_flags().debug_cert {
                ay_core::safe_eprintln!("c !! substitution-bridge SUCCEEDED (self-contained path)");
            }
            for raw in raw_authored_to_record {
                self.record_rebuilt_authored_proof_premise(raw);
            }
            // Every authored premise is now represented by its own raw term,
            // with explicit proof steps to the canonical ids. Keeping any
            // printer override would collapse those distinct terms again.
            self.last_proof_term_overrides = None;
            return true;
        }
        if !surface_override_roots_have_bounded_work(&self.ctx.terms, needed.iter().copied()) {
            if ay_core::misc_cli_flags().debug_cert {
                ay_core::safe_eprintln!(
                    "c !! substitution-bridge refused: override roots exceed bounded work"
                );
            }
            return false;
        }
        if self
            .last_proof_term_overrides
            .as_ref()
            .is_some_and(|overrides| !surface_override_map_is_bounded(overrides))
        {
            if ay_core::misc_cli_flags().debug_cert {
                ay_core::safe_eprintln!(
                    "c !! substitution-bridge refused: unbounded surface-override map"
                );
            }
            return false;
        }
        let mut overrides = self.last_proof_term_overrides.clone().unwrap_or_default();
        // A substituted leaf carries a STALE surface override: the ordinary
        // export registered "print the substituted form the way the AUTHORED
        // assertion is spelled" so the (indefensible) `assume` at least looked
        // like a premise. Now that the leaf is DERIVED, that override would
        // print the derived term and its source identically — collapsing the
        // `eq_congruent_pred` conclusion onto its own premise and producing a
        // certificate no external checker can follow. Drop it.
        for plan in &plans {
            overrides.remove(&plan.goal);
            let (atom, _) = strip_not_polarity(&self.ctx.terms, plan.goal);
            overrides.remove(&atom);
        }
        let mut registered: Vec<TermId> = Vec::new();
        for &term in &needed {
            if registered.contains(&term) {
                continue;
            }
            registered.push(term);
            let Some(idx) = original_terms.iter().position(|&t| t == term) else {
                continue;
            };
            let parsed = originals[idx].1.clone();
            // Placeholder (native-API) surfaces register NO override — the
            // sentinel string is not a printable spelling.
            if is_api_placeholder(&parsed) {
                continue;
            }
            // The raw binary-distinct assume above already carries the exact
            // source spelling. Overriding its derived canonical `(not (= ...))`
            // back to `distinct` would make the `equiv_pos2`/resolution bridge
            // syntactically invalid in the emitted Alethe certificate.
            if matches!(parsed_head(&parsed), Some("distinct")) {
                overrides.remove(&term);
                continue;
            }
            if !collect_surface_term_overrides(&mut self.ctx, term, &parsed, &mut overrides)
                || !surface_override_map_is_bounded(&overrides)
            {
                if ay_core::misc_cli_flags().debug_cert {
                    ay_core::safe_eprintln!(
                        "c !! substitution-bridge refused: surface override collection failed for {}",
                        ay_proof::render_term_canonical(&self.ctx.terms, term)
                    );
                }
                return false;
            }
        }
        *proof = new_proof;
        self.last_proof_term_overrides = Some(overrides);
        true
    }

    /// Mark every step in the dependency cone of an empty-clause step.
    ///
    /// This mirrors `ay_proof::validate_reachable_assumes_in_problem_scope`
    /// exactly — it is the same cone the #8821 authority gate inspects — so a
    /// leaf this mask reports as unreachable provably cannot be the leaf that
    /// gate rejects.
    fn reachable_step_mask(proof: &Proof) -> Vec<bool> {
        let mut reachable = vec![false; proof.steps.len()];
        let mut stack: Vec<usize> = Vec::new();
        for (index, step) in proof.steps.iter().enumerate() {
            let derives_empty = match step {
                ProofStep::Step { clause, .. }
                | ProofStep::Resolution { clause, .. }
                | ProofStep::TheoryLemma { clause, .. } => clause.is_empty(),
                _ => false,
            };
            if derives_empty {
                reachable[index] = true;
                stack.push(index);
            }
        }
        while let Some(index) = stack.pop() {
            let push = |premise: ProofId, reachable: &mut Vec<bool>, stack: &mut Vec<usize>| {
                let premise = premise.0 as usize;
                if premise < reachable.len() && !reachable[premise] {
                    reachable[premise] = true;
                    stack.push(premise);
                }
            };
            match &proof.steps[index] {
                ProofStep::Step { premises, .. } => {
                    for &premise in premises {
                        push(premise, &mut reachable, &mut stack);
                    }
                }
                ProofStep::Resolution {
                    clause1, clause2, ..
                } => {
                    push(*clause1, &mut reachable, &mut stack);
                    push(*clause2, &mut reachable, &mut stack);
                }
                _ => {}
            }
        }
        reachable
    }

    /// Plan the congruence bridge deriving the substituted leaf `goal` from an
    /// authored predicate assertion plus authored defining equalities, or
    /// `None` when no such derivation exists.
    fn plan_substitution_bridge(
        &mut self,
        goal: TermId,
        original_terms: &[TermId],
    ) -> Option<BridgePlan> {
        let mut budget = EQ_PLAN_BUDGET;
        self.plan_substitution_bridge_with_budget(goal, original_terms, &mut budget)
    }

    /// Budget-injectable implementation used by the adversarial unit tests.
    /// One shared counter covers every same-head source candidate and every
    /// argument of this goal; a large assertion set cannot reset the bound by
    /// making an earlier candidate fail.
    fn plan_substitution_bridge_with_budget(
        &mut self,
        goal: TermId,
        original_terms: &[TermId],
        budget: &mut u32,
    ) -> Option<BridgePlan> {
        for &source in original_terms {
            if let Some(plan) = self.plan_substitution_bridge_from_source_with_budget(
                goal,
                source,
                original_terms,
                budget,
            ) {
                return Some(plan);
            }
        }
        None
    }

    /// Plan one bridge from the exact authored `source` spelling to `goal`.
    ///
    /// The ordinary path searches canonical originals for a source. The
    /// self-contained surface path already reconstructed the exact raw source,
    /// so it calls this helper directly and still limits all equality premises
    /// to `original_terms`.
    fn plan_substitution_bridge_from_source_with_budget(
        &mut self,
        goal: TermId,
        source: TermId,
        original_terms: &[TermId],
        budget: &mut u32,
    ) -> Option<BridgePlan> {
        let (goal_atom, goal_negated) = strip_not_polarity(&self.ctx.terms, goal);
        let TermData::App(goal_sym, goal_args) = self.ctx.terms.get(goal_atom) else {
            return None;
        };
        let (goal_sym, goal_args) = (goal_sym.clone(), goal_args.clone());
        if goal_args.is_empty() {
            return None;
        }

        let (src_atom, src_negated) = strip_not_polarity(&self.ctx.terms, source);
        if src_negated != goal_negated || src_atom == goal_atom {
            return None;
        }
        let TermData::App(src_sym, src_args) = self.ctx.terms.get(src_atom) else {
            return None;
        };
        if *src_sym != goal_sym || src_args.len() != goal_args.len() {
            return None;
        }
        let src_args = src_args.clone();
        let mut kids: Vec<EqPlan> = Vec::with_capacity(src_args.len());
        let mut effective_src_atom = src_atom;
        let mut source_via_symm = false;
        let mut direct_failed = false;
        for (&a, &b) in src_args.iter().zip(goal_args.iter()) {
            match self.plan_eq(a, b, original_terms, 0, budget) {
                Some(kid) => kids.push(kid),
                None => {
                    direct_failed = true;
                    break;
                }
            }
        }
        if direct_failed {
            // Symmetric retry, POSITIVE binary `=` leaves only. Preprocessing
            // substitution can reorient an authored equality (`(= S 42)`
            // recorded as `(= 42 S')`), and positional pairing then asks for
            // `S = 42` — underivable — instead of the two argument equalities
            // that actually hold. Pair against the SWAPPED source arguments
            // and run the congruence from `(= b a)`, which the emitter first
            // derives from the authored assume by one strict `symm` step. The
            // negated case would need `not_symm`, which this pass does not
            // model; it stays fail-closed.
            if goal_negated
                || src_args.len() != 2
                || !matches!(&goal_sym, Symbol::Named(name) if name == "=")
            {
                return None;
            }
            kids.clear();
            for (&a, &b) in [src_args[1], src_args[0]].iter().zip(goal_args.iter()) {
                kids.push(self.plan_eq(a, b, original_terms, 0, budget)?);
            }
            let swapped =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("="), [src_args[1], src_args[0]], Sort::Bool);
            // `mk_app` raw-interns, but a folding surprise would break the
            // rigid `symm`/`eq_congruent_pred` shapes; fail closed on one.
            if !matches!(
                self.ctx.terms.get(swapped),
                TermData::App(Symbol::Named(name), args)
                    if name == "=" && args.as_slice() == [src_args[1], src_args[0]]
            ) {
                return None;
            }
            effective_src_atom = swapped;
            source_via_symm = true;
        }
        // `eq_congruent_pred ⊢ (cl ¬(= a1 b1) .. ¬(= an bn) ¬P(a..) P(b..))`.
        // For a NEGATED leaf the roles swap: the derivation runs from the
        // asserted `(not P(a..))` to `(not P(b..))`, which is the same
        // rule with `P(b..)` in the negated slot. The strict checker accepts
        // either premise orientation at each argument position, so the SAME
        // equality terms serve both directions.
        let mut lemma: Vec<TermId> = kids.iter().map(|k| k.neg_eq).collect();
        if goal_negated {
            lemma.push(self.ctx.terms.mk_not_raw(goal_atom));
            lemma.push(effective_src_atom);
        } else {
            lemma.push(self.ctx.terms.mk_not_raw(effective_src_atom));
            lemma.push(goal_atom);
        }
        Some(BridgePlan {
            goal,
            goal_negated,
            source,
            source_atom: effective_src_atom,
            source_via_symm,
            lemma,
            kids,
        })
    }

    /// Plan a derivation of `(= a b)` from the original assertions:
    /// reflexivity, an authored equality (either orientation, bridged by
    /// `symm`), congruence over a shared function symbol, or transitivity
    /// through an authored DEFINING equality for `a`.
    ///
    /// The transitivity leg is what covers eliminated definitions. A
    /// definition-substituting preprocessing pass (the QF_AX store-flat
    /// pass `substitute_store_flat_equalities` is the canonical case) replaces
    /// a defined symbol by its definition EVERYWHERE and then drops the now
    /// tautological defining equality from the assertion stack, so the leaf
    /// the proof assumes mentions the fully expanded term while the authored
    /// assertion mentions the name. The defining equalities are not lost —
    /// they are still authored assertions, recovered here from the
    /// re-elaborated parse — but the expansion is a FIXPOINT: authored
    /// `(= a3 (store a2 i e))` relates `a3` to a one-level store, while the
    /// leaf holds the fully nested chain. Congruence alone cannot cross that
    /// gap (`a3` is a variable, not an application); `trans` through the
    /// authored definition followed by congruence on the store's array
    /// argument walks the chain one link at a time, bottoming out at whichever
    /// link the substitution left alone.
    fn plan_eq(
        &mut self,
        a: TermId,
        b: TermId,
        original_terms: &[TermId],
        depth: u32,
        budget: &mut u32,
    ) -> Option<EqPlan> {
        // Chains are walked one definition per level, so the depth bound must
        // admit `2 * chain_length` (a `trans` level plus a `cong` level per
        // link). `EQ_PLAN_BUDGET` is the real terminator; `MAX_DEPTH` only
        // caps native stack use.
        const MAX_DEPTH: u32 = 512;
        if depth > MAX_DEPTH {
            return None;
        }
        if *budget == 0 {
            return None;
        }
        *budget -= 1;
        let eq = self
            .ctx
            .terms
            .mk_app(Symbol::named("="), [a, b], Sort::Bool);
        // `mk_app` raw-interns, but a constant-folding surprise would break
        // the rigid `refl`/`eq_congruent` shapes; fail closed on one.
        if !matches!(
            self.ctx.terms.get(eq),
            TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2
        ) {
            return None;
        }
        let neg_eq = self.ctx.terms.mk_not_raw(eq);
        if a == b {
            return Some(EqPlan {
                eq,
                neg_eq,
                kind: EqPlanKind::Refl,
            });
        }
        if original_terms.contains(&eq) {
            return Some(EqPlan {
                eq,
                neg_eq,
                kind: EqPlanKind::Assumed,
            });
        }
        let flipped = self
            .ctx
            .terms
            .mk_app(Symbol::named("="), [b, a], Sort::Bool);
        if original_terms.contains(&flipped) {
            return Some(EqPlan {
                eq,
                neg_eq,
                kind: EqPlanKind::Symm { assumed: flipped },
            });
        }
        // Constant-folded concat: preprocessing can turn
        // `concat(op, concat(lhs, rhs))` into one BV literal after `op/lhs/rhs`
        // are pinned. Pure EUF congruence cannot relate an application to that
        // literal, so split the literal according to the concat operand widths:
        //
        //   authored pins + eq_congruent  |- a = concat(hi, lo)
        //   exact ground evaluate         |- concat(hi, lo) = b
        //   trans                         |- a = b
        //
        // The second leg is admitted only when ay-proof's deliberately narrow
        // strict `evaluate` recognizer independently checks the closed concat.
        // A missing pin, malformed width, unsupported ground operation, false
        // fold, or width above 64 therefore fails closed.
        if let Some(plan) =
            self.plan_concat_eq_to_constant(a, b, eq, neg_eq, original_terms, depth, budget)
        {
            return Some(plan);
        }
        // Ground SEQUENCE identity: elaboration folds `seq.++`/`seq.empty`
        // trees (e.g. `(seq.++ seq.empty (seq.unit 1))` → `(seq.unit 1)`), so
        // the authored side and the solver-visible side of an assertion cease
        // to be syntactically linked and pure EUF congruence cannot cross the
        // gap — the assume was then provenance-demoted to a trust unit and
        // mandatory certification demoted a correct seq `unsat` to `unknown`
        // (deductive-checks calc_basic, 2026-08-19). The recognizer IS the strict
        // validator (`SeqGroundEval` shape B), so this leg is exactly as
        // fail-closed as the BV `evaluate` leg above.
        if ay_proof::recognize_seq_ground_eval(&self.ctx.terms, &[eq]) {
            return Some(EqPlan {
                eq,
                neg_eq,
                kind: EqPlanKind::SeqGroundEvaluate,
            });
        }
        // DIRECT datatype selector projection: the goal equality itself is
        // `(= (sel (C ..)) arg_i)` (either orientation) — a registry-gated
        // datatype tautology (`(= B (top (stack B ..)))`, the ground-tower
        // leaves). Registry fetch is gated on a cheap selector-application
        // shape probe so non-datatype problems never pay for it.
        if self.eq_sides_have_selector_application(a, b) {
            let ctor_selectors = self.ctor_selector_decls_for_strict_proof();
            if !ctor_selectors.is_empty()
                && ay_proof::recognize_datatype_selector_project(
                    &self.ctx.terms,
                    &[eq],
                    &ctor_selectors,
                )
            {
                return Some(EqPlan {
                    eq,
                    neg_eq,
                    kind: EqPlanKind::DatatypeSelectorProjectEval,
                });
            }
        }
        // Congruence: `a` and `b` are the same function applied to pairwise
        // derivably-equal arguments.
        let congruence = (|| {
            let TermData::App(a_sym, a_args) = self.ctx.terms.get(a) else {
                return None;
            };
            let (a_sym, a_args) = (a_sym.clone(), a_args.clone());
            let TermData::App(b_sym, b_args) = self.ctx.terms.get(b) else {
                return None;
            };
            if *b_sym != a_sym || b_args.len() != a_args.len() || a_args.is_empty() {
                return None;
            }
            let b_args = b_args.clone();
            let mut kids = Vec::with_capacity(a_args.len());
            for (&x, &y) in a_args.iter().zip(b_args.iter()) {
                kids.push(self.plan_eq(x, y, original_terms, depth + 1, budget)?);
            }
            // `eq_congruent ⊢ (cl ¬(= a1 b1) .. ¬(= an bn) (= f(a..) f(b..)))`.
            let mut lemma: Vec<TermId> = kids.iter().map(|k| k.neg_eq).collect();
            lemma.push(eq);
            Some(EqPlanKind::Cong { lemma, kids })
        })();
        if let Some(kind) = congruence {
            return Some(EqPlan { eq, neg_eq, kind });
        }

        // Transitivity through an authored DEFINING equality for `a`: some
        // original asserts `(= a mid)` (either orientation), and `(= mid b)`
        // is itself derivable. `trans` chains the two unit equalities into
        // `(= a b)`.
        //
        // Only `a` — the side that comes from the AUTHORED assertion — is
        // expanded. `b` is the preprocessing-substituted side; walking it
        // would be searching for a way to make the substituted form match
        // something, which is exactly the direction that could launder a
        // formula the problem never asserted.
        if let Some(plan) =
            self.plan_eq_via_definition(a, b, eq, neg_eq, original_terms, depth, budget)
        {
            return Some(plan);
        }

        if let Some(plan) = self.plan_eq_via_constructor_injectivity(
            a,
            b,
            eq,
            neg_eq,
            original_terms,
            depth,
            budget,
        ) {
            return Some(plan);
        }

        // SELECTOR CHASE: `(= a (sel u))` (either orientation) where `u` is
        // derivably equal to a registered constructor application `C(..)`
        // owning `sel`. Datatype selector propagation records exactly this
        // shape as a trust unit — `x ~ stack(a, empty)` forcing
        // `(= a (top x))` — and no purely syntactic leg can cross it: the
        // projection is a THEORY fact. Compose
        //   a = sel(C(..))   [DatatypeSelectorProject, registry-validated]
        //   sel(C(..)) = sel(u)   [cong over `sel` from plan_eq(C(..), u)]
        // via trans. Candidate constructor terms are drawn from the authored
        // assertion sides only (the same non-laundering rule as the
        // definition leg above), and the projection clause is verified by
        // the strict validator's own recognizer at plan time.
        self.plan_eq_via_selector_chase(a, b, eq, neg_eq, original_terms, depth, budget)
    }

    /// Plan a [`DerivedTesterLeaf`]; see the collection-site comment.
    fn plan_derived_tester_leaf(
        &mut self,
        goal: TermId,
        original_terms: &[TermId],
    ) -> Option<DerivedTesterLeaf> {
        let decls = self.datatype_decls_for_strict_proof();
        let selectors = self.ctor_selector_decls_for_strict_proof();
        if decls.is_empty() {
            return None;
        }
        let (subject_atom, negated) = strip_not_polarity(&self.ctx.terms, goal);
        let TermData::App(tester_symbol, tester_args) = self.ctx.terms.get(subject_atom) else {
            return None;
        };
        if tester_args.len() != 1 {
            return None;
        }
        let (tester_symbol, subject) = (tester_symbol.clone(), tester_args[0]);
        // Candidates: authored equality sides, same sort as the subject.
        let mut candidates: Vec<TermId> = Vec::new();
        for &original in original_terms {
            let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(original) else {
                continue;
            };
            if name != "=" || args.len() != 2 {
                continue;
            }
            for &side in args.as_slice() {
                if side != subject
                    && self.ctx.terms.sort(side) == self.ctx.terms.sort(subject)
                    && !candidates.contains(&side)
                {
                    candidates.push(side);
                }
            }
        }
        for candidate in candidates {
            let sort = self.ctx.terms.sort(subject_atom).clone();
            let candidate_atom = self
                .ctx
                .terms
                .mk_app(tester_symbol.clone(), [candidate], sort);
            let tester_clause = if negated {
                self.ctx.terms.mk_not_raw(candidate_atom)
            } else {
                candidate_atom
            };
            // The same-polarity tester fact on the candidate must be a
            // registry-validated tautology (the recognizer IS the strict
            // validator with the same registries).
            if !ay_proof::recognize_datatype_tester_eval_with_selectors(
                &self.ctx.terms,
                &[tester_clause],
                &decls,
                &selectors,
            ) {
                continue;
            }
            let mut budget = EQ_PLAN_BUDGET;
            let Some(eq_plan) = self.plan_eq(candidate, subject, original_terms, 0, &mut budget)
            else {
                continue;
            };
            return Some(DerivedTesterLeaf {
                goal,
                negated,
                subject_atom,
                candidate_atom,
                tester_clause,
                eq_plan,
            });
        }
        None
    }

    /// Emit a planned [`DerivedTesterLeaf`], returning the unit `(cl goal)`:
    ///
    /// ```text
    /// eq_congruent_pred ⊢ (cl ¬(= k t) ¬P(k) P(t))     [pos]  (dually for neg)
    ///   ⊗ (cl (= k t))    [the eq plan]
    ///   ⊗ (cl P(k))       [DatatypeTesterEval lemma]
    ///   = (cl P(t))
    /// ```
    fn emit_derived_tester_leaf(
        &mut self,
        proof: &mut Proof,
        leaf: &DerivedTesterLeaf,
        assume_ids: &HashMap<TermId, ProofId>,
    ) -> Option<ProofId> {
        let eq_unit = Self::emit_eq_plan(proof, &leaf.eq_plan, assume_ids)?;
        let tester_unit = proof.add_step(ProofStep::TheoryLemma {
            theory: "DT".to_string(),
            clause: vec![leaf.tester_clause],
            farkas: None,
            kind: TheoryLemmaKind::DatatypeTesterEval,
            lia: None,
        });
        let not_eq = leaf.eq_plan.neg_eq;
        // For a NEGATED goal the roles swap (same convention as the source
        // bridges): the derivation runs from `(not P(k))` to `(not P(t))`,
        // which is the same eq_congruent_pred with `P(t)` in the negated slot.
        let (lemma, tester_pivot) = if leaf.negated {
            (
                vec![
                    not_eq,
                    self.ctx.terms.mk_not_raw(leaf.subject_atom),
                    leaf.candidate_atom,
                ],
                leaf.candidate_atom,
            )
        } else {
            (
                vec![
                    not_eq,
                    self.ctx.terms.mk_not_raw(leaf.candidate_atom),
                    leaf.subject_atom,
                ],
                leaf.candidate_atom,
            )
        };
        let lemma_step = proof.add_step(ProofStep::TheoryLemma {
            theory: "EUF".to_string(),
            clause: lemma.clone(),
            farkas: None,
            kind: TheoryLemmaKind::EufCongruentPred,
            lia: None,
        });
        // Resolve away the equality premise.
        let after_eq: Vec<TermId> = lemma.iter().copied().filter(|&l| l != not_eq).collect();
        let step_eq = proof.add_resolution(after_eq.clone(), leaf.eq_plan.eq, lemma_step, eq_unit);
        // Resolve away the candidate tester literal against the lemma unit.
        let goal_lit = if leaf.negated {
            self.ctx.terms.mk_not_raw(leaf.subject_atom)
        } else {
            leaf.subject_atom
        };
        let final_clause = vec![goal_lit];
        // Resolution operand order follows the checker's convention: the
        // clause holding the NEGATED pivot comes first. Positive goals leave
        // `¬P(k)` in the congruence residue; negated goals leave `P(k)` there
        // and the negation in the tester-eval unit.
        let step_final = if leaf.negated {
            proof.add_resolution(final_clause.clone(), tester_pivot, tester_unit, step_eq)
        } else {
            proof.add_resolution(final_clause.clone(), tester_pivot, step_eq, tester_unit)
        };
        (final_clause == vec![leaf.goal]).then_some(step_final)
    }

    /// Cheap shape probe: is either equality side a unary application whose

    /// head COULD be a selector? Gates the registry fetch in `plan_eq`'s
    /// direct-projection leg.
    fn eq_sides_have_selector_application(&self, a: TermId, b: TermId) -> bool {
        [a, b].iter().any(|&side| {
            matches!(
                self.ctx.terms.get(side),
                TermData::App(Symbol::Named(_), args) if args.len() == 1
            )
        })
    }

    /// Constructor injectivity through selectors: goal `(= x y)` where some
    /// pair of same-constructor applications `C(.., x, ..)` / `C(.., y, ..)`
    /// (same argument position, drawn from authored equality sides) is itself
    /// derivably equal. Then, with `sel_i` the registered position-`i`
    /// selector,
    ///   x = sel_i(C(..x..))          [projection]
    ///     = sel_i(C(..y..))          [cong over sel_i from the planned pair]
    ///     = y                        [projection]
    /// — every leaf registry-validated, no injectivity axiom needed. This is
    /// how a proof leaf like `(= (stack B ..) (stack C ..))` obtained from
    /// `stack(A, X) ~chain~ stack(A, Y)` becomes derivable.
    #[allow(clippy::too_many_arguments)]
    fn plan_eq_via_constructor_injectivity(
        &mut self,
        a: TermId,
        b: TermId,
        eq: TermId,
        neg_eq: TermId,
        original_terms: &[TermId],
        depth: u32,
        budget: &mut u32,
    ) -> Option<EqPlan> {
        let ctor_selectors = self.ctor_selector_decls_for_strict_proof();
        if ctor_selectors.is_empty() {
            return None;
        }
        // Constructor applications among authored equality sides that carry
        // `a` (resp. `b`) as a direct argument.
        let mut holders_a: Vec<(TermId, String, usize)> = Vec::new();
        let mut holders_b: Vec<(TermId, String, usize)> = Vec::new();
        for &original in original_terms {
            let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(original) else {
                continue;
            };
            if name != "=" || args.len() != 2 {
                continue;
            }
            for &side in args.clone().as_slice() {
                let TermData::App(Symbol::Named(head), head_args) = self.ctx.terms.get(side) else {
                    continue;
                };
                let head = head.clone();
                if !ctor_selectors.iter().any(|(ctor, _)| ctor == &head) {
                    continue;
                }
                for (index, &argument) in head_args.clone().iter().enumerate() {
                    if argument == a && !holders_a.iter().any(|&(t, _, _)| t == side) {
                        holders_a.push((side, head.clone(), index));
                    }
                    if argument == b && !holders_b.iter().any(|&(t, _, _)| t == side) {
                        holders_b.push((side, head.clone(), index));
                    }
                }
            }
        }
        for &(pa, ref ctor_a, index_a) in &holders_a {
            for &(pb, ref ctor_b, index_b) in &holders_b {
                if ctor_a != ctor_b || index_a != index_b || pa == pb {
                    continue;
                }
                let Some((_, selectors)) = ctor_selectors.iter().find(|(ctor, _)| ctor == ctor_a)
                else {
                    continue;
                };
                let Some(selector) = selectors.get(index_a) else {
                    continue;
                };
                // Projections at both ends, recognizer-verified.
                let sort_a = self.ctx.terms.sort(a).clone();
                let sel_pa =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named(selector.clone()), [pa], sort_a.clone());
                let sel_pb = self
                    .ctx
                    .terms
                    .mk_app(Symbol::named(selector.clone()), [pb], sort_a);
                let proj_a = self
                    .ctx
                    .terms
                    .mk_app(Symbol::named("="), [a, sel_pa], Sort::Bool);
                let proj_b = self
                    .ctx
                    .terms
                    .mk_app(Symbol::named("="), [sel_pb, b], Sort::Bool);
                if !ay_proof::recognize_datatype_selector_project(
                    &self.ctx.terms,
                    &[proj_a],
                    &ctor_selectors,
                ) || !ay_proof::recognize_datatype_selector_project(
                    &self.ctx.terms,
                    &[proj_b],
                    &ctor_selectors,
                ) {
                    continue;
                }
                // The constructor-application pair must itself be derivable.
                let pair_kid = self.plan_eq(pa, pb, original_terms, depth + 1, budget)?;
                let cong_eq =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("="), [sel_pa, sel_pb], Sort::Bool);
                let cong = EqPlan {
                    eq: cong_eq,
                    neg_eq: self.ctx.terms.mk_not_raw(cong_eq),
                    kind: EqPlanKind::Cong {
                        lemma: vec![pair_kid.neg_eq, cong_eq],
                        kids: vec![pair_kid],
                    },
                };
                let left = EqPlan {
                    eq: proj_a,
                    neg_eq: self.ctx.terms.mk_not_raw(proj_a),
                    kind: EqPlanKind::DatatypeSelectorProjectEval,
                };
                let right_tail = EqPlan {
                    eq: proj_b,
                    neg_eq: self.ctx.terms.mk_not_raw(proj_b),
                    kind: EqPlanKind::DatatypeSelectorProjectEval,
                };
                let mid_eq = self
                    .ctx
                    .terms
                    .mk_app(Symbol::named("="), [sel_pa, b], Sort::Bool);
                let mid = EqPlan {
                    eq: mid_eq,
                    neg_eq: self.ctx.terms.mk_not_raw(mid_eq),
                    kind: EqPlanKind::Trans {
                        left: Box::new(cong),
                        right: Box::new(right_tail),
                    },
                };
                return Some(EqPlan {
                    eq,
                    neg_eq,
                    kind: EqPlanKind::Trans {
                        left: Box::new(left),
                        right: Box::new(mid),
                    },
                });
            }
        }
        None
    }

    /// The selector-chase leg of [`Self::plan_eq`]; see the call site.
    #[allow(clippy::too_many_arguments)]
    fn plan_eq_via_selector_chase(
        &mut self,
        a: TermId,
        b: TermId,
        eq: TermId,
        neg_eq: TermId,
        original_terms: &[TermId],
        depth: u32,
        budget: &mut u32,
    ) -> Option<EqPlan> {
        let ctor_selectors = self.ctor_selector_decls_for_strict_proof();
        if ctor_selectors.is_empty() {
            return None;
        }
        // Which side is the selector application? Try both orientations.
        for (target, sel_app) in [(a, b), (b, a)] {
            let TermData::App(Symbol::Named(sel_name), sel_args) = self.ctx.terms.get(sel_app)
            else {
                continue;
            };
            if sel_args.len() != 1 {
                continue;
            }
            let sel_name = sel_name.clone();
            let subject = sel_args[0];
            if !ctor_selectors
                .iter()
                .any(|(_, selectors)| selectors.iter().any(|s| s == &sel_name))
            {
                continue;
            }
            // Candidate constructor terms: authored assertion equality sides.
            let mut candidates: Vec<TermId> = Vec::new();
            for &original in original_terms {
                let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(original) else {
                    continue;
                };
                if name != "=" || args.len() != 2 {
                    continue;
                }
                for &side in args.as_slice() {
                    if side != subject && !candidates.contains(&side) {
                        candidates.push(side);
                    }
                }
            }
            for candidate in candidates {
                if self.ctx.terms.sort(candidate) != self.ctx.terms.sort(subject) {
                    continue;
                }
                // The projection clause the strict validator must accept:
                // `(= target (sel candidate))` in the goal's own orientation,
                // recognizer-verified (fail-closed on shape or registry).
                let projected = self.ctx.terms.mk_app(
                    Symbol::named(sel_name.clone()),
                    [candidate],
                    self.ctx.terms.sort(sel_app).clone(),
                );
                let projection_eq =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("="), [target, projected], Sort::Bool);
                if !ay_proof::recognize_datatype_selector_project(
                    &self.ctx.terms,
                    &[projection_eq],
                    &ctor_selectors,
                ) {
                    continue;
                }
                // `sel(candidate) = sel(subject)` by congruence over `sel`.
                let cong_kid =
                    self.plan_eq(candidate, subject, original_terms, depth + 1, budget)?;
                let cong_eq =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("="), [projected, sel_app], Sort::Bool);
                // `eq_congruent ⊢ (cl ¬(= x y) (= (sel x) (sel y)))`.
                let cong_lemma = vec![cong_kid.neg_eq];
                // Assemble `(= target sel_app)`; flip to the requested
                // orientation with the trans machinery's own handling by
                // planning in the goal's orientation directly.
                let left = EqPlan {
                    eq: projection_eq,
                    neg_eq: self.ctx.terms.mk_not_raw(projection_eq),
                    kind: EqPlanKind::DatatypeSelectorProjectEval,
                };
                let right = EqPlan {
                    eq: cong_eq,
                    neg_eq: self.ctx.terms.mk_not_raw(cong_eq),
                    kind: EqPlanKind::Cong {
                        lemma: {
                            let mut lemma = cong_lemma;
                            lemma.push(cong_eq);
                            lemma
                        },
                        kids: vec![cong_kid],
                    },
                };
                let assembled_eq =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("="), [target, sel_app], Sort::Bool);
                let assembled = EqPlan {
                    eq: assembled_eq,
                    neg_eq: self.ctx.terms.mk_not_raw(assembled_eq),
                    kind: EqPlanKind::Trans {
                        left: Box::new(left),
                        right: Box::new(right),
                    },
                };
                if assembled_eq == eq {
                    return Some(EqPlan {
                        eq,
                        neg_eq,
                        kind: assembled.kind,
                    });
                }
                // Goal is the flipped orientation `(= sel_app target)`.
                return Some(EqPlan {
                    eq,
                    neg_eq,
                    kind: EqPlanKind::SymmOfPlan {
                        inner: Box::new(assembled),
                    },
                });
            }
        }
        None
    }

    /// Plan a certified equality from a symbolic binary `concat` to its folded
    /// BV literal. See the call-site comment in [`Self::plan_eq`].
    #[allow(clippy::too_many_arguments)]
    fn plan_concat_eq_to_constant(
        &mut self,
        a: TermId,
        b: TermId,
        eq: TermId,
        neg_eq: TermId,
        original_terms: &[TermId],
        depth: u32,
        budget: &mut u32,
    ) -> Option<EqPlan> {
        let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(a) else {
            return None;
        };
        if name != "concat" || args.len() != 2 {
            return None;
        }
        let args = args.clone();
        let TermData::Const(Constant::BitVec { value, width }) = self.ctx.terms.get(b).clone()
        else {
            return None;
        };
        // A surface-faithful source can already be a fully ground concat tree.
        // In that case `eq` itself is the exact checked evaluation theorem.
        // Splitting it and adding `trans(eq, ...)` would make one premise equal
        // to the conclusion, which both Alethe and our strict checker reject as
        // redundant. Prefer the direct, independently recognized theorem.
        if ay_proof::recognize_bv_ground_evaluate(&self.ctx.terms, &[eq]) {
            return Some(EqPlan {
                eq,
                neg_eq,
                kind: EqPlanKind::BvGroundEvaluate,
            });
        }
        let (Sort::BitVec(high_sort), Sort::BitVec(low_sort)) = (
            self.ctx.terms.sort(args[0]).clone(),
            self.ctx.terms.sort(args[1]).clone(),
        ) else {
            return None;
        };
        if high_sort.width == 0
            || low_sort.width == 0
            || width > u64::BITS
            || high_sort.width > u64::BITS
            || low_sort.width > u64::BITS
            || high_sort.width.checked_add(low_sort.width) != Some(width)
        {
            return None;
        }

        let low_mask = (BigInt::from(1_u8) << low_sort.width) - BigInt::from(1_u8);
        let low_value = &value & low_mask;
        let high_value = value >> low_sort.width;
        let high = self.ctx.terms.mk_bitvec(high_value, high_sort.width);
        let low = self.ctx.terms.mk_bitvec(low_value, low_sort.width);

        let high_plan = self.plan_eq(args[0], high, original_terms, depth + 1, budget)?;
        let low_plan = self.plan_eq(args[1], low, original_terms, depth + 1, budget)?;

        // `mk_app` deliberately preserves the raw application. The folded
        // literal is `b`; keeping this intermediate raw is what gives
        // `eq_congruent` a matching function head on both sides.
        let raw_ground =
            self.ctx
                .terms
                .mk_app(Symbol::named("concat"), [high, low], Sort::bitvec(width));
        if !matches!(
            self.ctx.terms.get(raw_ground),
            TermData::App(Symbol::Named(n), raw_args)
                if n == "concat" && raw_args.as_slice() == [high, low]
        ) {
            return None;
        }
        let congruent_eq = self
            .ctx
            .terms
            .mk_app(Symbol::named("="), [a, raw_ground], Sort::Bool);
        let congruent_neg = self.ctx.terms.mk_not_raw(congruent_eq);
        let congruent = EqPlan {
            eq: congruent_eq,
            neg_eq: congruent_neg,
            kind: EqPlanKind::Cong {
                lemma: vec![high_plan.neg_eq, low_plan.neg_eq, congruent_eq],
                kids: vec![high_plan, low_plan],
            },
        };

        let ground_eq = self
            .ctx
            .terms
            .mk_app(Symbol::named("="), [raw_ground, b], Sort::Bool);
        if !ay_proof::recognize_bv_ground_evaluate(&self.ctx.terms, &[ground_eq]) {
            return None;
        }
        let ground = EqPlan {
            eq: ground_eq,
            neg_eq: self.ctx.terms.mk_not_raw(ground_eq),
            kind: EqPlanKind::BvGroundEvaluate,
        };
        Some(EqPlan {
            eq,
            neg_eq,
            kind: EqPlanKind::Trans {
                left: Box::new(congruent),
                right: Box::new(ground),
            },
        })
    }

    /// The `trans`-through-a-definition leg of [`Self::plan_eq`].
    ///
    /// Every `mid` considered comes from an assertion the problem AUTHORED, and
    /// the emitted `trans` step is validated by the unchanged strict checker
    /// (which re-derives the `a — mid — b` chain itself and rejects redundant
    /// premises), so a definition the problem does not contain cannot be
    /// fabricated here: there is simply no original to read it from.
    #[allow(clippy::too_many_arguments)]
    fn plan_eq_via_definition(
        &mut self,
        a: TermId,
        b: TermId,
        eq: TermId,
        neg_eq: TermId,
        original_terms: &[TermId],
        depth: u32,
        budget: &mut u32,
    ) -> Option<EqPlan> {
        for &original in original_terms {
            let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(original) else {
                continue;
            };
            if name != "=" || args.len() != 2 {
                continue;
            }
            let (lhs, rhs) = (args[0], args[1]);
            // `mid` is the OTHER side of an authored equality one of whose
            // sides is syntactically `a`.
            let (mid, flipped) = if lhs == a {
                (rhs, false)
            } else if rhs == a {
                (lhs, true)
            } else {
                continue;
            };
            // `mid == b` is already covered by the Assumed/Symm cases above,
            // and `mid == a` is a degenerate self-definition: neither yields a
            // well-formed two-edge `trans` chain.
            if mid == b || mid == a {
                continue;
            }
            let Some(right) = self.plan_eq(mid, b, original_terms, depth + 1, budget) else {
                continue;
            };
            // The left leg proves `(= a mid)`. When the problem spelled the
            // definition the other way round (`(= mid a)`), `symm` reorients
            // it, and the leg's conclusion is the separately interned
            // `(= a mid)` — NOT the authored term — so emission resolves
            // against the right id.
            let left = if flipped {
                let oriented = self
                    .ctx
                    .terms
                    .mk_app(Symbol::named("="), [a, mid], Sort::Bool);
                // `mk_app` raw-interns, but a constant-folding surprise would
                // break the rigid `symm` / `trans` clause shapes.
                if !matches!(
                    self.ctx.terms.get(oriented),
                    TermData::App(Symbol::Named(n), ar) if n == "=" && ar.len() == 2
                ) {
                    continue;
                }
                EqPlan {
                    eq: oriented,
                    neg_eq: self.ctx.terms.mk_not_raw(oriented),
                    kind: EqPlanKind::Symm { assumed: original },
                }
            } else {
                EqPlan {
                    eq: original,
                    neg_eq: self.ctx.terms.mk_not_raw(original),
                    kind: EqPlanKind::Assumed,
                }
            };
            return Some(EqPlan {
                eq,
                neg_eq,
                kind: EqPlanKind::Trans {
                    left: Box::new(left),
                    right: Box::new(right),
                },
            });
        }
        None
    }

    fn is_matching_binary_distinct(terms: &TermStore, diseq: TermId, distinct: TermId) -> bool {
        let TermData::Not(eq) = terms.get(diseq) else {
            return false;
        };
        let TermData::App(Symbol::Named(eq_name), eq_args) = terms.get(*eq) else {
            return false;
        };
        let TermData::App(Symbol::Named(distinct_name), distinct_args) = terms.get(distinct) else {
            return false;
        };
        eq_name == "="
            && eq_args.len() == 2
            && distinct_name == "distinct"
            && distinct_args.as_slice() == eq_args.as_slice()
            && terms.sort(diseq) == &Sort::Bool
            && terms.sort(distinct) == &Sort::Bool
    }

    /// Derive canonical `(not (= a b))` from the exact authored
    /// `(distinct a b)` premise.
    fn emit_binary_distinct_bridge(
        terms: &mut TermStore,
        proof: &mut Proof,
        diseq: TermId,
        distinct: TermId,
        assume_id: ProofId,
    ) -> Option<ProofId> {
        if !Self::is_matching_binary_distinct(terms, diseq, distinct) {
            return None;
        }
        let equiv = terms.mk_app(Symbol::named("="), [distinct, diseq], Sort::Bool);
        let not_equiv = terms.mk_not_raw(equiv);
        let not_distinct = terms.mk_not_raw(distinct);
        let de = proof.add_rule_step(
            AletheRule::DistinctElim,
            vec![equiv],
            Vec::new(),
            Vec::new(),
        );
        let ep = proof.add_rule_step(
            AletheRule::EquivPos2,
            vec![not_equiv, not_distinct, diseq],
            Vec::new(),
            Vec::new(),
        );
        let r1 = proof.add_resolution(vec![not_distinct, diseq], equiv, ep, de);
        Some(proof.add_resolution(vec![diseq], distinct, r1, assume_id))
    }

    /// Emit a planned bridge, returning the id of the unit `(cl goal)` step.
    fn emit_substitution_bridge(
        terms: &mut TermStore,
        proof: &mut Proof,
        plan: &BridgePlan,
        assume_ids: &HashMap<TermId, ProofId>,
    ) -> Option<ProofId> {
        let mut kid_units: Vec<(TermId, TermId, ProofId)> = Vec::with_capacity(plan.kids.len());
        for kid in &plan.kids {
            let id = Self::emit_eq_plan(proof, kid, assume_ids)?;
            kid_units.push((kid.eq, kid.neg_eq, id));
        }
        let mut clause = plan.lemma.clone();
        let mut current = proof.add_step(ProofStep::TheoryLemma {
            theory: "EUF".to_string(),
            clause: clause.clone(),
            farkas: None,
            kind: TheoryLemmaKind::EufCongruentPred,
            lia: None,
        });
        for (eq, neg_eq, unit) in &kid_units {
            let resolvent: Vec<TermId> = clause.iter().copied().filter(|&l| l != *neg_eq).collect();
            if resolvent.len() == clause.len() {
                return None;
            }
            current = proof.add_resolution(resolvent.clone(), *eq, current, *unit);
            clause = resolvent;
        }
        // A kid whose equality IS the source assertion shares its `neg_eq`
        // with the source literal, so the kid resolution above already
        // eliminated both copies and the clause is the unit goal. A further
        // resolution against the source assume would have no pivot literal
        // left and be rejected by the checker; the derivation is complete.
        if clause.as_slice() == [plan.goal] {
            return Some(current);
        }
        // Resolve the asserted predicate away, leaving the unit `(cl goal)`.
        let (source_lit, pivot) = if plan.goal_negated {
            (plan.source_atom, plan.source_atom)
        } else {
            (terms.mk_not_raw(plan.source_atom), plan.source_atom)
        };
        let resolvent: Vec<TermId> = clause
            .iter()
            .copied()
            .filter(|&l| l != source_lit)
            .collect();
        if resolvent.len() != 1 || resolvent[0] != plan.goal {
            return None;
        }
        let &source_assume = assume_ids.get(&plan.source)?;
        let source_step = if plan.source_via_symm {
            // `symm`: unit `(cl (= b a))` from the authored `(cl (= a b))`.
            // Only planned for positive leaves, so the assume IS the equality.
            proof.add_rule_step(
                AletheRule::Symm,
                vec![plan.source_atom],
                vec![source_assume],
                Vec::new(),
            )
        } else {
            source_assume
        };
        Some(proof.add_resolution(resolvent, pivot, current, source_step))
    }

    /// Emit a planned equality derivation, returning the id of the unit
    /// `(cl (= a b))` step.
    fn emit_eq_plan(
        proof: &mut Proof,
        plan: &EqPlan,
        assume_ids: &HashMap<TermId, ProofId>,
    ) -> Option<ProofId> {
        match &plan.kind {
            EqPlanKind::Refl => {
                Some(proof.add_rule_step(AletheRule::Refl, vec![plan.eq], Vec::new(), Vec::new()))
            }
            EqPlanKind::Assumed => {
                let unit = assume_ids.get(&plan.eq).copied();
                if unit.is_none() && ay_core::misc_cli_flags().debug_cert {
                    ay_core::safe_eprintln!(
                        "c !! emit_eq_plan: Assumed eq {:?} has no assume id",
                        plan.eq
                    );
                }
                unit
            }
            EqPlanKind::Symm { assumed } => {
                let premise = match assume_ids.get(assumed) {
                    Some(&id) => id,
                    None => {
                        if ay_core::misc_cli_flags().debug_cert {
                            ay_core::safe_eprintln!(
                                "c !! emit_eq_plan: Symm premise {assumed:?} has no assume id"
                            );
                        }
                        return None;
                    }
                };
                Some(proof.add_rule_step(
                    AletheRule::Symm,
                    vec![plan.eq],
                    vec![premise],
                    Vec::new(),
                ))
            }
            EqPlanKind::BvGroundEvaluate => Some(proof.add_rule_step(
                AletheRule::Evaluate,
                vec![plan.eq],
                Vec::new(),
                Vec::new(),
            )),
            EqPlanKind::SeqGroundEvaluate => Some(proof.add_step(ProofStep::TheoryLemma {
                theory: "seq".to_string(),
                clause: vec![plan.eq],
                farkas: None,
                kind: TheoryLemmaKind::SeqGroundEval,
                lia: None,
            })),
            EqPlanKind::DatatypeSelectorProjectEval => {
                Some(proof.add_step(ProofStep::TheoryLemma {
                    theory: "DT".to_string(),
                    clause: vec![plan.eq],
                    farkas: None,
                    kind: TheoryLemmaKind::DatatypeSelectorProject,
                    lia: None,
                }))
            }
            EqPlanKind::SymmOfPlan { inner } => {
                let premise = Self::emit_eq_plan(proof, inner, assume_ids)?;
                Some(proof.add_rule_step(
                    AletheRule::Symm,
                    vec![plan.eq],
                    vec![premise],
                    Vec::new(),
                ))
            }
            EqPlanKind::Cong { lemma, kids } => {
                let mut kid_units: Vec<(TermId, TermId, ProofId)> = Vec::with_capacity(kids.len());
                for kid in kids {
                    let id = Self::emit_eq_plan(proof, kid, assume_ids)?;
                    kid_units.push((kid.eq, kid.neg_eq, id));
                }
                let mut clause = lemma.clone();
                let mut current = proof.add_step(ProofStep::TheoryLemma {
                    theory: "EUF".to_string(),
                    clause: clause.clone(),
                    farkas: None,
                    kind: TheoryLemmaKind::EufCongruent,
                    lia: None,
                });
                for (kid_eq, kid_neg, unit) in &kid_units {
                    let resolvent: Vec<TermId> =
                        clause.iter().copied().filter(|&l| l != *kid_neg).collect();
                    if resolvent.len() == clause.len() {
                        if ay_core::misc_cli_flags().debug_cert {
                            ay_core::safe_eprintln!(
                                "c !! emit_eq_plan: Cong kid neg_eq {kid_neg:?} absent from lemma {clause:?}"
                            );
                        }
                        return None;
                    }
                    current = proof.add_resolution(resolvent.clone(), *kid_eq, current, *unit);
                    clause = resolvent;
                }
                if clause.len() != 1 || clause[0] != plan.eq {
                    if ay_core::misc_cli_flags().debug_cert {
                        ay_core::safe_eprintln!(
                            "c !! emit_eq_plan: Cong residue {clause:?} != goal {:?}",
                            plan.eq
                        );
                    }
                    return None;
                }
                Some(current)
            }
            EqPlanKind::Trans { left, right } => {
                let left_id = Self::emit_eq_plan(proof, left, assume_ids)?;
                let right_id = Self::emit_eq_plan(proof, right, assume_ids)?;
                // `trans` takes the two unit equalities as PREMISES; the
                // strict checker re-derives the `a — mid — b` chain from them
                // and rejects any premise it cannot place on that path.
                Some(proof.add_rule_step(
                    AletheRule::Trans,
                    vec![plan.eq],
                    vec![left_id, right_id],
                    Vec::new(),
                ))
            }
        }
    }
}

/// Split a literal into its atom and polarity (a doubly-negated literal is
/// normalized, matching the strict checker's `strip_not`).
fn strip_not_polarity(terms: &TermStore, mut lit: TermId) -> (TermId, bool) {
    let mut negated = false;
    while let TermData::Not(inner) = terms.get(lit) {
        lit = *inner;
        negated = !negated;
    }
    (lit, negated)
}

/// A derived tester leaf: `((_ is C) t)` (either polarity) justified by the
/// same-polarity registry-validated tester fact on a derivably-equal `k`.
struct DerivedTesterLeaf {
    /// The defective leaf exactly as the proof states it.
    goal: TermId,
    /// True when `goal` is `(not ((_ is C) t))`.
    negated: bool,
    /// The tester ATOM on the subject: `((_ is C) t)`.
    subject_atom: TermId,
    /// The tester ATOM on the candidate: `((_ is C) k)`.
    candidate_atom: TermId,
    /// The tester-eval LEMMA clause: `[((_ is C) k)]` or `[(not ((_ is C) k))]`.
    tester_clause: TermId,
    /// Derivation of `(= k t)`.
    eq_plan: EqPlan,
}

/// A planned derivation of `(= a b)` from the original problem assertions.
///
/// `eq` is the goal equality and `neg_eq` its negation — both interned during
/// planning, so emission needs no fresh terms and cannot surprise the rigid
/// `refl` / `eq_congruent` clause shapes.
struct EqPlan {
    eq: TermId,
    neg_eq: TermId,
    kind: EqPlanKind,
}

enum EqPlanKind {
    /// `refl ⊢ (cl (= a a))`.
    Refl,
    /// The equality IS an original assertion: `assume`.
    Assumed,
    /// The FLIPPED equality is an original assertion; `symm` reorients it.
    Symm { assumed: TermId },
    /// Closed concat evaluation accepted by the strict `evaluate` recognizer.
    BvGroundEvaluate,
    /// Ground sequence identity (`seq.empty`/`seq.unit`-of-constant/`seq.++`
    /// on both sides, elementwise-identical normal forms) accepted by the
    /// strict `SeqGroundEval` recognizer. Covers elaboration-folded seq
    /// concats the same way `BvGroundEvaluate` covers folded BV concats.
    SeqGroundEvaluate,
    /// Datatype selector projection `(= t (sel C(..t..)))` accepted by the
    /// registry-gated `DatatypeSelectorProject` recognizer at plan time.
    /// Emitted as the corresponding theory lemma; the whole-proof gate
    /// re-validates it with the executor's own registries.
    DatatypeSelectorProjectEval,
    /// The flipped orientation of a fully planned equality: emit `inner`'s
    /// unit `(cl (= a b))`, then one strict `symm` step to `(cl (= b a))`.
    SymmOfPlan { inner: Box<EqPlan> },
    /// `eq_congruent` over a shared function symbol.
    Cong {
        lemma: Vec<TermId>,
        kids: Vec<EqPlan>,
    },
    /// `trans` over an authored defining equality `(= a mid)` (`left`) and a
    /// derivation of `(= mid b)` (`right`).
    Trans {
        left: Box<EqPlan>,
        right: Box<EqPlan>,
    },
}

impl EqPlan {
    fn collect_assumed(&self, out: &mut Vec<TermId>) {
        match &self.kind {
            EqPlanKind::Refl
            | EqPlanKind::BvGroundEvaluate
            | EqPlanKind::SeqGroundEvaluate
            | EqPlanKind::DatatypeSelectorProjectEval => {}
            EqPlanKind::SymmOfPlan { inner } => inner.collect_assumed(out),
            EqPlanKind::Assumed => {
                if !out.contains(&self.eq) {
                    out.push(self.eq);
                }
            }
            EqPlanKind::Symm { assumed } => {
                if !out.contains(assumed) {
                    out.push(*assumed);
                }
            }
            EqPlanKind::Cong { kids, .. } => {
                for kid in kids {
                    kid.collect_assumed(out);
                }
            }
            EqPlanKind::Trans { left, right } => {
                left.collect_assumed(out);
                right.collect_assumed(out);
            }
        }
    }

    fn uses_ground_evaluate(&self) -> bool {
        match &self.kind {
            EqPlanKind::BvGroundEvaluate
            | EqPlanKind::SeqGroundEvaluate
            | EqPlanKind::DatatypeSelectorProjectEval => true,
            EqPlanKind::SymmOfPlan { inner } => inner.uses_ground_evaluate(),
            EqPlanKind::Cong { kids, .. } => kids.iter().any(Self::uses_ground_evaluate),
            EqPlanKind::Trans { left, right } => {
                left.uses_ground_evaluate() || right.uses_ground_evaluate()
            }
            EqPlanKind::Refl | EqPlanKind::Assumed | EqPlanKind::Symm { .. } => false,
        }
    }
}

/// A planned bridge from an authored predicate assertion to the
/// preprocessing-substituted form the exported proof assumed.
struct BridgePlan {
    /// The substituted leaf to derive (possibly negated).
    goal: TermId,
    /// Whether `goal` is the negated form.
    goal_negated: bool,
    /// The authored assertion the leaf came from (same polarity as `goal`).
    source: TermId,
    /// `source` with its `not` wrapper stripped — or, when
    /// `source_via_symm` is set, the SWAPPED orientation of that equality.
    source_atom: TermId,
    /// Derive `source_atom` from the authored assume by one strict `symm`
    /// step before the final resolution (positive binary `=` sources only).
    source_via_symm: bool,
    /// The `eq_congruent_pred` clause.
    lemma: Vec<TermId>,
    /// Per-argument equality derivations, aligned with the predicate's args.
    kids: Vec<EqPlan>,
}

impl BridgePlan {
    fn uses_ground_evaluate(&self) -> bool {
        self.kids.iter().any(EqPlan::uses_ground_evaluate)
    }
}

struct SurfaceAssumePlan {
    canonical: TermId,
    raw: TermId,
    canonicalization: SurfaceCanonicalization,
}

enum SurfaceCanonicalization {
    Direct,
    Distinct,
    Bridge(BridgePlan),
}

#[cfg(test)]
#[path = "proof_original_rebuild_tests.rs"]
mod proof_original_rebuild_tests;

#[path = "proof_original_rebuild_bv_lia_scope.rs"]
mod proof_original_rebuild_bv_lia_scope;
#[cfg(test)]
#[path = "proof_original_rebuild_bv_lia_tests.rs"]
mod proof_original_rebuild_bv_lia_tests;
