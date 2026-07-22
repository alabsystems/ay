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

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::TermData;
use ay_core::{
    AletheRule, FarkasAnnotation, Proof, ProofId, ProofStep, Sort, Symbol, TermId, TermStore,
    TheoryLemmaKind, TheoryLit, TheoryResult, TheorySolver,
};
use ay_frontend::command::Term as FrontendTerm;

use super::proof_surface_syntax::{collect_surface_term_overrides, strip_frontend_annotations};
use super::Executor;

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

/// The parsed-form sentinel the native API records for `assert_term`
/// (`api/solving/assertions.rs`): the assertion has NO surface syntax. The
/// rebuild then works from the assertion-stack term itself — the exact term
/// the proof bundle exports as the obligation — and skips every
/// surface-fidelity concern: there is no problem file to print-match, so the
/// canonical rendering IS the surface, and no overrides may be registered
/// (an override would print the sentinel string).
const API_ASSERTION_PLACEHOLDER: &str = "__ay_api_assertion__";

fn is_api_placeholder(parsed: &FrontendTerm) -> bool {
    matches!(
        strip_frontend_annotations(parsed),
        FrontendTerm::Symbol(name) if name == API_ASSERTION_PLACEHOLDER
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
        let parsed_assertions: Vec<FrontendTerm> = self.ctx.assertions_parsed().to_vec();
        if parsed_assertions.is_empty() {
            return;
        }
        // The provenance-aware ORIGINAL assertion stack, index-aligned with
        // `assertions_parsed` — preprocessing may rewrite `ctx.assertions` in
        // place (e.g. substitute-and-simplify to `true`), so the raw stack is
        // NOT a usable original source for surface-less assertions.
        let original_stack = self.proof_original_problem_assertions();
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
            let stripped = strip_frontend_annotations(parsed).clone();
            let Some(canonical) = self.ctx.elaborate_surface_subterm(&stripped) else {
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

        // Also capture the RAW top-level re-interned form of each parsed
        // original. The fold-to-`false` reconstruction re-interns a folded
        // assertion RAW so the rebuilt `assume` prints like the problem file:
        // e.g. `(and b0 (not b0))` elaborates (folds) to `false`, but
        // `rebuild_complementary_and_collapse` assumes `mk_app("and",
        // [elaborate(b0), elaborate(not b0)], Bool)` — a distinct id the folded
        // `canonical` above does NOT cover. Rebuild the same raw top-level app
        // here (hash-consed identical to what the collapse builds) for the Bool
        // connective/relation heads those reconstructions use, so the leak-2
        // gate accepts these genuine premises. A foreign injected axiom is
        // never a parsed assertion, so it is never added by this loop.
        let parsed_forms: Vec<FrontendTerm> = originals.iter().map(|(_, p)| p.clone()).collect();
        for parsed in &parsed_forms {
            let FrontendTerm::App(head, operands) = strip_frontend_annotations(parsed) else {
                continue;
            };
            let head = head.clone();
            if !matches!(
                head.as_str(),
                "and" | "or" | "not" | "=>" | "distinct" | "=" | "<" | "<=" | ">" | ">="
            ) {
                continue;
            }
            let operands = operands.clone();
            let mut elaborated = Vec::with_capacity(operands.len());
            let mut ok = true;
            for op in &operands {
                let stripped = strip_frontend_annotations(op).clone();
                match self.ctx.elaborate_surface_subterm(&stripped) {
                    Some(t) => elaborated.push(t),
                    None => {
                        ok = false;
                        break;
                    }
                }
            }
            if !ok {
                continue;
            }
            let raw = if head == "not" && elaborated.len() == 1 {
                self.ctx.terms.mk_not_raw(elaborated[0])
            } else {
                self.ctx
                    .terms
                    .mk_app(Symbol::named(&head), &elaborated, Sort::Bool)
            };
            self.last_proof_rebuild_originals.push(raw);
        }

        // Preprocessor fold-to-`false` collapse (`(distinct x x)`, `(= 1 2)`,
        // `(and p (not p))`): the degenerate `:rule false` export is replaced
        // by a certified derivation rebuilt from the parsed original
        // assertion's shape. Runs before the trust triggers below — the
        // collapse shape carries no trust step, only the misused `false`
        // rule. Fail-closed (whole-proof shape gated); see
        // `try_rebuild_false_collapse`.
        if self.try_rebuild_false_collapse(proof, &originals) {
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
            if is_linear_literal(&self.ctx.terms, *canonical)
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
            if !disjuncts
                .iter()
                .all(|&d| is_linear_literal(&self.ctx.terms, d))
            {
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
            let decomposition_rule = match stripped {
                FrontendTerm::App(op, _) if op == "or" => AletheRule::Or,
                _ => AletheRule::NotAnd,
            };
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

        // No full-rebuild backbone applies: the exported RESOLUTION skeleton
        // may still be sound with only local defects (n-ary distinct assumes,
        // normalized-bounds assumes, Int trichotomy trust lemmas). Try the
        // insert-and-remap surgery, which keeps the skeleton and replaces
        // each defective site with a certified derivation (fail-closed).
        if self.try_rebuild_with_trust_surgery(proof, &originals) {
            return;
        }

        // Last resort (multi-equality Farkas class): the bounds ALONE may be
        // jointly infeasible — preprocessing substituted the equalities into
        // the remaining assertion and collapsed the whole contradiction into
        // a premiseless trust leaf no backbone above can reach (there is no
        // disjunction and no disequality to split on). One certified,
        // independently re-verified Farkas lemma over the original bounds
        // closes the proof; a whole-proof `check_proof_strict` gate keeps
        // the original on any miss.
        if self.try_rebuild_with_pure_bounds(proof, &originals, &bound_specs) {
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
        if self.try_rebuild_with_complementary_literals(proof, &originals) {
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
                    if !originals.iter().any(|(c, _)| c == term) {
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
        *proof = new_proof;
        let mut overrides = self.last_proof_term_overrides.take().unwrap_or_default();
        let mut pairs: Vec<(TermId, FrontendTerm)> =
            vec![(originals[disj_idx].0, originals[disj_idx].1.clone())];
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
                overrides.remove(&spec.term);
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
        for (canonical, parsed) in &pairs {
            // Placeholder (native-API) surfaces register NO override: the
            // sentinel string is not a printable spelling — the canonical
            // rendering already is.
            if is_api_placeholder(parsed) {
                continue;
            }
            collect_surface_term_overrides(&mut self.ctx, *canonical, parsed, &mut overrides);
        }
        self.last_proof_term_overrides = Some(overrides);
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
        let (di_atom, di_val) = match self.ctx.terms.get(di) {
            TermData::Not(inner) => (*inner, false),
            _ => (di, true),
        };
        let mut lra = ay_lra::LraSolver::new(&self.ctx.terms);
        lra.set_combined_theory_mode(true);
        TheorySolver::register_atom(&mut lra, di_atom);
        for &b in bound_terms {
            TheorySolver::register_atom(&mut lra, atom_of(&self.ctx.terms, b));
        }
        TheorySolver::assert_literal(&mut lra, di_atom, di_val);
        for &b in bound_terms {
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
        *proof = new_proof;
        let mut overrides = self.last_proof_term_overrides.take().unwrap_or_default();
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
            collect_surface_term_overrides(&mut self.ctx, canonical, &parsed, &mut overrides);
        }
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
        *proof = new_proof;
        let mut overrides = self.last_proof_term_overrides.take().unwrap_or_default();
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
            collect_surface_term_overrides(&mut self.ctx, canonical, &parsed, &mut overrides);
        }
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

        // (1) Which assume leaves are defective?
        //
        // Only leaves REACHABLE from an empty-clause step matter: the #8821
        // authority gate (`validate_reachable_assumes_in_problem_scope`) walks
        // the dependency cone of the empty clause and ignores everything
        // outside it, and dead steps are never printed. A defective leaf on a
        // dead branch (e.g. an abandoned extensionality split whose
        // `__ext_diff_*` witness assumes survive in the step list) therefore
        // carries NO authority claim, and must not veto repairing the leaves
        // that do. Those leaves are copied through verbatim — this pass never
        // invents a derivation for them.
        let reachable = Self::reachable_step_mask(proof);
        let mut defective: Vec<TermId> = Vec::new();
        let mut dead_defective: Vec<TermId> = Vec::new();
        for (idx, step) in proof.steps.iter().enumerate() {
            if let ProofStep::Assume(term) = step {
                if original_terms.contains(term) {
                    continue;
                }
                if reachable[idx] {
                    if !defective.contains(term) {
                        defective.push(*term);
                    }
                } else if !dead_defective.contains(term) {
                    dead_defective.push(*term);
                }
            }
        }
        // A term assumed on BOTH a live and a dead branch is repaired once and
        // remapped everywhere; it is not a pass-through.
        dead_defective.retain(|t| !defective.contains(t));
        if defective.is_empty() {
            return false;
        }

        // (2) Plan a congruence bridge for each defective leaf. Planning is
        // pure w.r.t. the proof (it only interns the equality/lemma terms the
        // emission will need), so a failure costs nothing.
        let mut plans: Vec<BridgePlan> = Vec::with_capacity(defective.len());
        for &goal in &defective {
            let Some(plan) = self.plan_substitution_bridge(goal, &original_terms) else {
                return false;
            };
            plans.push(plan);
        }

        // (3) Originals the rebuilt proof will assume: the ones the surviving
        // skeleton already assumed, plus every premise the bridges need.
        let mut needed: Vec<TermId> = Vec::new();
        let push_needed = |t: TermId, needed: &mut Vec<TermId>| {
            if !needed.contains(&t) {
                needed.push(t);
            }
        };
        for step in &proof.steps {
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
        // Every assumed term must genuinely be an original premise.
        if needed.iter().any(|t| !original_terms.contains(t)) {
            return false;
        }

        // (4) Assemble: assumes first (Alethe ordering), then the bridge
        // derivations, then the surviving skeleton with premises remapped.
        let mut new_proof = Proof::new();
        let mut assume_ids: HashMap<TermId, ProofId> = HashMap::default();
        for &term in &needed {
            let id = new_proof.add_assume(term, None);
            assume_ids.insert(term, id);
        }
        // Dead-branch defective leaves are re-emitted UNCHANGED, exactly as
        // the proof already had them. They stay outside the empty clause's
        // cone, so they are neither printed nor claimed as authority; keeping
        // them merely preserves the skeleton this pass promised not to
        // restructure.
        let mut passthrough_ids: HashMap<TermId, ProofId> = HashMap::default();
        for &term in &dead_defective {
            let id = new_proof.add_assume(term, None);
            passthrough_ids.insert(term, id);
        }

        let mut bridge_unit: HashMap<TermId, ProofId> = HashMap::default();
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
            let new_id = match step {
                ProofStep::Assume(term) => match assume_ids.get(term) {
                    Some(&id) => id,
                    None => match bridge_unit.get(term).or_else(|| passthrough_ids.get(term)) {
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
                } => new_proof.add_step(ProofStep::TheoryLemma {
                    theory: theory.clone(),
                    clause: clause.clone(),
                    farkas: farkas.clone(),
                    kind: *kind,
                    lia: lia.clone(),
                }),
                ProofStep::Step {
                    rule,
                    clause,
                    premises,
                    args,
                } => {
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
        let before = ay_proof::check_proof_collecting_trust(proof, &self.ctx.terms)
            .ok()
            .map(|collected| {
                collected
                    .into_iter()
                    .map(|(_, clause)| clause)
                    .collect::<Vec<_>>()
            });
        let after: Vec<Vec<TermId>> =
            match ay_proof::check_proof_collecting_trust(&new_proof, &self.ctx.terms) {
                Ok(collected) => collected.into_iter().map(|(_, clause)| clause).collect(),
                Err(_) => return false,
            };
        let Some(before) = before else {
            // The original did not even pass deferred-trust validation; this
            // pass is not the one to reason about what it was doing.
            return false;
        };
        if after.len() > before.len() || after.iter().any(|clause| !before.contains(clause)) {
            return false;
        }

        *proof = new_proof;
        let mut overrides = self.last_proof_term_overrides.take().unwrap_or_default();
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
            collect_surface_term_overrides(&mut self.ctx, term, &parsed, &mut overrides);
        }
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
        let (goal_atom, goal_negated) = strip_not_polarity(&self.ctx.terms, goal);
        let TermData::App(goal_sym, goal_args) = self.ctx.terms.get(goal_atom) else {
            return None;
        };
        let (goal_sym, goal_args) = (goal_sym.clone(), goal_args.clone());
        if goal_args.is_empty() {
            return None;
        }

        for &source in original_terms {
            let (src_atom, src_negated) = strip_not_polarity(&self.ctx.terms, source);
            if src_negated != goal_negated || src_atom == goal_atom {
                continue;
            }
            let TermData::App(src_sym, src_args) = self.ctx.terms.get(src_atom) else {
                continue;
            };
            if *src_sym != goal_sym || src_args.len() != goal_args.len() {
                continue;
            }
            let src_args = src_args.clone();
            let mut kids: Vec<EqPlan> = Vec::with_capacity(src_args.len());
            let mut ok = true;
            // One shared budget across the whole predicate: a pathological
            // original set can offer many defining equalities per variable,
            // and search is bounded so planning stays linear-ish in practice
            // and always terminates.
            let mut budget = EQ_PLAN_BUDGET;
            for (&a, &b) in src_args.iter().zip(goal_args.iter()) {
                match self.plan_eq(a, b, original_terms, 0, &mut budget) {
                    Some(plan) => kids.push(plan),
                    None => {
                        ok = false;
                        break;
                    }
                }
            }
            if !ok {
                continue;
            }
            // `eq_congruent_pred ⊢ (cl ¬(= a1 b1) .. ¬(= an bn) ¬P(a..) P(b..))`.
            // For a NEGATED leaf the roles swap: the derivation runs from the
            // asserted `(not P(a..))` to `(not P(b..))`, which is the same
            // rule with `P(b..)` in the negated slot. The strict checker
            // accepts either premise orientation at each argument position, so
            // the SAME equality terms serve both directions.
            let mut lemma: Vec<TermId> = kids.iter().map(|k| k.neg_eq).collect();
            if goal_negated {
                lemma.push(self.ctx.terms.mk_not_raw(goal_atom));
                lemma.push(src_atom);
            } else {
                lemma.push(self.ctx.terms.mk_not_raw(src_atom));
                lemma.push(goal_atom);
            }
            return Some(BridgePlan {
                goal,
                goal_negated,
                source,
                source_atom: src_atom,
                lemma,
                kids,
            });
        }
        None
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
        self.plan_eq_via_definition(a, b, eq, neg_eq, original_terms, depth, budget)
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
        Some(proof.add_resolution(resolvent, pivot, current, source_assume))
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
            EqPlanKind::Assumed => assume_ids.get(&plan.eq).copied(),
            EqPlanKind::Symm { assumed } => {
                let &premise = assume_ids.get(assumed)?;
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
                        return None;
                    }
                    current = proof.add_resolution(resolvent.clone(), *kid_eq, current, *unit);
                    clause = resolvent;
                }
                if clause.len() != 1 || clause[0] != plan.eq {
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
            EqPlanKind::Refl => {}
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
    /// `source` with its `not` wrapper stripped.
    source_atom: TermId,
    /// The `eq_congruent_pred` clause.
    lemma: Vec<TermId>,
    /// Per-argument equality derivations, aligned with the predicate's args.
    kids: Vec<EqPlan>,
}

#[cfg(test)]
#[path = "proof_original_rebuild_tests.rs"]
mod proof_original_rebuild_tests;
