// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Quantifier preprocessing helpers for `process_quantifiers`.
//!
//! Contains finite-domain expansion, Skolemization, E-matching rounds,
//! instance filtering, promote-unsat, CEGQI setup, and assertion flattening.
//! These are private `impl Executor` methods called from the orchestrator
//! in `mod.rs`.

// #8529: Use deterministic hash sets in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, Symbol};
use ay_core::{FarkasAnnotation, Sort, TermData, TermId, TermStore, TheoryLemmaKind, TheoryLit};

use super::super::model::EvalValue;
use super::super::Executor;
use super::collect_and_conjuncts;
use crate::cegqi::{is_cegqi_candidate, CegqiInstantiator};
use crate::ematching::{
    collect_ground_terms_by_sort, contains_quantifier, enumerative_instantiation, subst_vars,
};
use crate::preprocess::{FlattenAnd, PreprocessingPass};
use crate::quantifier_manager::QuantifierManager;

// MAX_EMATCHING_ROUNDS is now accessed via self.ematching_round_limit() (#7893)

/// Red zone / segment size for `stacker::maybe_grow` while rewriting deeply
/// nested ground terms in [`tighten_int_strict_term`] (mirrors skolemize.rs).
const TIGHTEN_STACK_RED_ZONE: usize = 32 * 1024;
const TIGHTEN_STACK_SIZE: usize = 1024 * 1024;

/// Rewrite GROUND integer STRICT order atoms — in every syntactic form the
/// skolemizer / arithmetic normalizer emits — to the equivalent POSITIVE
/// NON-STRICT `(<= _ _)` bound, recursing through Boolean / function structure
/// but NOT into `forall`/`exists` bodies.
///
/// Over `Int`, all of these are exact equivalences (true in every model, so safe
/// in any polarity):
///   * `(< a b)`        ⇒ `(<= a (- b 1))`           (a < b   ⇔ a ≤ b-1)
///   * `(not (<= a b))` ⇒ `(<= (+ b 1) a)`           (a > b   ⇔ a ≥ b+1)
///   * `(not (< a b))`  ⇒ `(<= b a)`                 (a ≥ b   ⇔ b ≤ a)
///
/// The skolemized negation of a per-element GOAL `(forall i. (and (<= lo i)
/// (< i hi)) ⇒ P)` surfaces its boundary bounds as the *negated* atoms
/// `(not (<= k (- len 1)))` (k ≥ len) and `(not (<= (+ len 1) k))` (k ≤ len) —
/// strict bounds in disguise. ay-lia only EXPORTS an implied equality from
/// POSITIVE non-strict two-sided bounds, so without this normalization the
/// boundary index `k` is never pinned to `len` and the goal stays Unknown/Sat.
/// Normalizing every strict form to a positive `<=` feeds the existing
/// (sound) export, letting `k ≥ len ∧ k ≤ len ⇒ k = len` propagate to the
/// congruence closure so the just-pushed element closes the new-element case.
///
/// See [`Executor::tighten_ground_int_strict_bounds`] for the full rationale.
/// `cache` memoizes on the original (pre-rewrite) `TermId`; existing terms are
/// never mutated (only fresh terms interned), so cached ids stay valid.
/// Real-sorted comparisons are left untouched (strict ≠ non-strict over `Real`).
///
/// `subst` folds asserted GROUND integer equalities `v = <expr>` (keyed on the
/// `Var` `TermId` of `v`, value the integer-equal `<expr>`) into the OPERANDS of
/// the integer order atoms it tightens — and ONLY there. A boundary bound
/// written against a SEPARATE upper-bound variable — e.g. `(< k new_len)` with
/// `(= new_len (+ len 1))` asserted — then resolves to the SAME concrete
/// `(<= k (- (+ len 1) 1))` the inline `(< k (+ len 1))` form already produces,
/// which ay-lia simplifies to `(<= k len)` and pins `k = len`. Confining the
/// fold to order-atom operands (rather than substituting every `Var` leaf) keeps
/// the blast radius minimal: the asserted defining equation and all non-order
/// atoms are left byte-identical, so E-matching / array reasoning are
/// unperturbed. The map values are pre-filtered (see
/// [`Executor::collect_ground_int_eq_subst`]) to contain no key `Var`. Folding an
/// ASSERTED equality is an exact integer-equivalence substitution, so it cannot
/// turn an invalid goal `unsat` — only normalize the boundary atom so the
/// existing (sound) implied-equality export can fire.
fn tighten_int_strict_term(
    terms: &mut TermStore,
    term: TermId,
    subst: &HashMap<TermId, TermId>,
    cache: &mut HashMap<TermId, TermId>,
) -> TermId {
    if let Some(&cached) = cache.get(&term) {
        return cached;
    }
    let result = stacker::maybe_grow(TIGHTEN_STACK_RED_ZONE, TIGHTEN_STACK_SIZE, || {
        match terms.get(term).clone() {
            TermData::App(sym, args) => {
                let new_args: Vec<TermId> = args
                    .iter()
                    .map(|&a| tighten_int_strict_term(terms, a, subst, cache))
                    .collect();
                // Integer strict less-than: `(< a b)` ⇒ `(<= a (- b 1))`. `>`/`>=`
                // are already normalized to `<`/`<=` at construction (mk_gt/mk_ge),
                // and `<=` needs no change. Real-sorted `<` is left untouched
                // (strict ≠ non-strict over the reals).
                if sym.name() == "<"
                    && new_args.len() == 2
                    && matches!(terms.sort(new_args[0]), Sort::Int)
                {
                    // Ground-equality fold (#ground-length-equation): resolve any
                    // asserted `v = <expr>` in the boundary operands so a strict
                    // bound against a separate length variable becomes pinnable.
                    let lhs = subst_ground_int_vars(terms, new_args[0], subst);
                    let rhs = subst_ground_int_vars(terms, new_args[1], subst);
                    let one = terms.mk_int(num_bigint::BigInt::from(1));
                    let t_minus_1 = terms.mk_sub(vec![rhs, one]);
                    terms.mk_le(lhs, t_minus_1)
                } else if new_args == args {
                    term
                } else {
                    let sort = terms.sort(term).clone();
                    terms.mk_app(sym, new_args, sort)
                }
            }
            TermData::Not(inner) => {
                // Normalize a NEGATED integer order atom into a positive `<=`.
                if let TermData::App(isym, iargs) = terms.get(inner).clone() {
                    if iargs.len() == 2 && matches!(terms.sort(iargs[0]), Sort::Int) {
                        let a0 = tighten_int_strict_term(terms, iargs[0], subst, cache);
                        let b0 = tighten_int_strict_term(terms, iargs[1], subst, cache);
                        // Ground-equality fold into the (negated) boundary operands.
                        let a = subst_ground_int_vars(terms, a0, subst);
                        let b = subst_ground_int_vars(terms, b0, subst);
                        match isym.name() {
                            // ¬(a ≤ b) ⇔ a ≥ b+1 ⇔ (b+1) ≤ a
                            "<=" => {
                                let one = terms.mk_int(num_bigint::BigInt::from(1));
                                let b_plus_1 = terms.mk_add(vec![b, one]);
                                return terms.mk_le(b_plus_1, a);
                            }
                            // ¬(a < b) ⇔ a ≥ b ⇔ b ≤ a
                            "<" => {
                                return terms.mk_le(b, a);
                            }
                            _ => {}
                        }
                    }
                }
                let ni = tighten_int_strict_term(terms, inner, subst, cache);
                if ni == inner {
                    term
                } else {
                    terms.mk_not(ni)
                }
            }
            TermData::Ite(c, t, e) => {
                let nc = tighten_int_strict_term(terms, c, subst, cache);
                let nt = tighten_int_strict_term(terms, t, subst, cache);
                let ne = tighten_int_strict_term(terms, e, subst, cache);
                if nc == c && nt == t && ne == e {
                    term
                } else {
                    terms.mk_ite(nc, nt, ne)
                }
            }
            TermData::Let(bindings, body) => {
                let new_bindings: Vec<(String, TermId)> = bindings
                    .iter()
                    .map(|(n, v)| (n.clone(), tighten_int_strict_term(terms, *v, subst, cache)))
                    .collect();
                let nb = tighten_int_strict_term(terms, body, subst, cache);
                if nb == body && new_bindings == bindings {
                    term
                } else {
                    terms.mk_let(new_bindings, nb)
                }
            }
            // Surviving quantifier bodies are deliberately opaque: tightening only
            // the GROUND atoms keeps E-matching / trigger selection unperturbed.
            // Leaves (Const, Var) and Forall/Exists return unchanged.
            _ => term,
        }
    });
    cache.insert(term, result);
    result
}

/// Replace asserted ground-equality variables (`subst` keys) inside an INTEGER
/// arithmetic operand of an order atom, rebuilding the term around the
/// replacements. `subst` values are key-free (collection-time filter), so a
/// single non-recursive replacement per `Var` leaf is exact and terminating.
///
/// This is the ONLY place the ground-equality fold rewrites terms: it touches
/// just the operands of the strict / negated order atoms
/// [`tighten_int_strict_term`] already normalizes, leaving the asserted defining
/// equation and every other atom untouched. No descent into `Forall`/`Exists`
/// bodies (ground order-atom operands never contain them; guarded for safety).
fn subst_ground_int_vars(
    terms: &mut TermStore,
    term: TermId,
    subst: &HashMap<TermId, TermId>,
) -> TermId {
    if subst.is_empty() {
        return term;
    }
    stacker::maybe_grow(TIGHTEN_STACK_RED_ZONE, TIGHTEN_STACK_SIZE, || {
        match terms.get(term).clone() {
            TermData::Var(..) => subst.get(&term).copied().unwrap_or(term),
            TermData::App(sym, args) => {
                let new_args: Vec<TermId> = args
                    .iter()
                    .map(|&a| subst_ground_int_vars(terms, a, subst))
                    .collect();
                if new_args == args {
                    term
                } else {
                    let sort = terms.sort(term).clone();
                    terms.mk_app(sym, new_args, sort)
                }
            }
            TermData::Ite(c, t, e) => {
                let nc = subst_ground_int_vars(terms, c, subst);
                let nt = subst_ground_int_vars(terms, t, subst);
                let ne = subst_ground_int_vars(terms, e, subst);
                if nc == c && nt == t && ne == e {
                    term
                } else {
                    terms.mk_ite(nc, nt, ne)
                }
            }
            // Const leaves and (defensively) any Forall/Exists/Not/Let return
            // unchanged: an integer order-atom operand is ground arithmetic.
            _ => term,
        }
    })
}

/// Does any `Var` whose `TermId` is in `targets` occur anywhere in `term`?
///
/// Iterative (heap stack) so deeply nested ground terms cannot overflow.
/// Descends into EVERY structural position — including quantifier bodies — so
/// the acyclicity / self-reference checks for the ground-equality fold are
/// conservative (a candidate is rejected if its right-hand side mentions any
/// substituted variable *anywhere*).
fn term_mentions_any_var(terms: &TermStore, term: TermId, targets: &HashSet<TermId>) -> bool {
    let mut stack = vec![term];
    let mut seen: HashSet<TermId> = HashSet::default();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        // `targets` holds only `Var` ids; reaching one means the var occurs.
        if targets.contains(&t) {
            return true;
        }
        match terms.get(t) {
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(i) => stack.push(*i),
            TermData::Ite(c, th, e) => {
                stack.push(*c);
                stack.push(*th);
                stack.push(*e);
            }
            TermData::Let(binds, b) => {
                for (_, v) in binds {
                    stack.push(*v);
                }
                stack.push(*b);
            }
            TermData::Forall(_, b, _) | TermData::Exists(_, b, _) => stack.push(*b),
            _ => {}
        }
    }
    false
}

/// Validate the two-literal arithmetic tautology `(cl a b)` with an explicit
/// `[1, 1]` Farkas certificate.  Clause literals are converted to the conflict
/// polarity expected by the shared proof validator exactly as the final
/// `la_generic` checker does.  This is the admission gate for affine-bound
/// bridges: failure means no clause is injected.
fn farkas_pair_clause_valid(terms: &TermStore, a: TermId, b: TermId) -> bool {
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    let lits: Vec<TheoryLit> = [a, b]
        .iter()
        .map(|&literal| match terms.get(literal) {
            TermData::Not(inner) => TheoryLit::new(*inner, true),
            _ => TheoryLit::new(literal, false),
        })
        .collect();
    ay_core::proof_validation::verify_farkas_conflict_lits_full(terms, &lits, &farkas).is_ok()
}

/// Insert every `Var` `TermId` reachable from `root` into `out`.
fn collect_all_var_ids(terms: &TermStore, root: TermId, out: &mut HashSet<TermId>) {
    let mut stack = vec![root];
    let mut seen: HashSet<TermId> = HashSet::default();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match terms.get(t) {
            TermData::Var(..) => {
                out.insert(t);
            }
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(i) => stack.push(*i),
            TermData::Ite(c, th, e) => {
                stack.push(*c);
                stack.push(*th);
                stack.push(*e);
            }
            TermData::Let(binds, b) => {
                for (_, v) in binds {
                    stack.push(*v);
                }
                stack.push(*b);
            }
            TermData::Forall(_, b, _) | TermData::Exists(_, b, _) => stack.push(*b),
            _ => {}
        }
    }
}

/// Insert the `Var` `TermId`s that occur inside ANY quantifier body reachable
/// from `root` into `out` (the body subtree's full var set, nested quantifiers
/// included).
///
/// Variables that appear under a surviving `Forall`/`Exists` are excluded from
/// the ground-equality fold so E-matching / trigger alignment stays byte
/// identical: the fold rewrites only GROUND atoms, never quantifier bodies, so
/// folding a variable that ALSO occurs in a body would desync the ground atom
/// from the matching instantiation (e.g. a ground `(+ bit0 bit1)` rewritten to
/// `(+ 0 1)` while the live `forall` body keeps `(+ bit0 bit1)`), dropping the
/// syntactic conflict E-matching relies on.
fn collect_vars_under_quantifiers(terms: &TermStore, root: TermId, out: &mut HashSet<TermId>) {
    let mut stack = vec![root];
    let mut seen: HashSet<TermId> = HashSet::default();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match terms.get(t) {
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                collect_all_var_ids(terms, *body, out);
            }
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(i) => stack.push(*i),
            TermData::Ite(c, th, e) => {
                stack.push(*c);
                stack.push(*th);
                stack.push(*e);
            }
            TermData::Let(binds, b) => {
                for (_, v) in binds {
                    stack.push(*v);
                }
                stack.push(*b);
            }
            _ => {}
        }
    }
}

/// Recursively fold datatype selector-over-constructor applications
/// `sel_i(C(t0..tn)) -> t_i` throughout `term`, re-interning the result. This is
/// the exact SMT-LIB datatype selector axiom applied as a semantics-preserving
/// rewrite — the same fold the elaborator performs (`elaborate_app`). Only fires
/// when the selector provably OWNS the applied constructor (looked up in
/// `ctor_sels`, the constructor -> ordered-selector-name map); a selector over a
/// foreign constructor is left opaque for the existing selector-axiom path.
/// `memo` shares folded subterms across the whole assertion DAG so shared
/// structure is rewritten once (no exponential blowup). Descends `App`/`Not`/
/// `Ite`; E-matching instances are quantifier-free ground bodies, so any residual
/// binder/let (never produced by `instantiate_body`) is returned unchanged.
fn reduce_selectors_rec(
    terms: &mut TermStore,
    ctor_sels: &HashMap<String, Vec<String>>,
    term: TermId,
    memo: &mut HashMap<TermId, TermId>,
) -> TermId {
    if let Some(&cached) = memo.get(&term) {
        return cached;
    }
    let result = match terms.get(term).clone() {
        TermData::App(sym, args) => {
            let rargs: Vec<TermId> = args
                .iter()
                .map(|&a| reduce_selectors_rec(terms, ctor_sels, a, memo))
                .collect();
            // Datatype folds when the (already-reduced) single argument is a
            // constructor application `C(f0..fn)`:
            //   * selector:  `sel_i(C(f..)) -> f_i` (the field, already reduced)
            //   * tester:    `is-D(C(..))  -> (D == C)` as `true`/`false`
            // Both are exact SMT-LIB datatype axioms. The tester name is
            // `is-<constructor>` (elaborator convention, `datatypes.rs`); it is a
            // genuine tester only when the stripped name is itself a constructor,
            // and the fold to a Boolean constant is sound only when the argument is
            // KNOWN to be a constructor of the same datatype — guaranteed here
            // because a well-sorted tester is applied to a term of its datatype and
            // `C` is that term's actual head constructor.
            let mut folded = None;
            if let (Symbol::Named(name), [only]) = (&sym, rargs.as_slice()) {
                if let TermData::App(Symbol::Named(ctor), cargs) = terms.get(*only).clone() {
                    if let Some(sels) = ctor_sels.get(&ctor) {
                        if let Some(idx) = sels.iter().position(|s| s == name) {
                            folded = cargs.get(idx).copied();
                        }
                    }
                    if folded.is_none() {
                        if let Some(tested) = name.strip_prefix("is-") {
                            if ctor_sels.contains_key(tested) && ctor_sels.contains_key(&ctor) {
                                folded = Some(if tested == ctor {
                                    terms.true_term()
                                } else {
                                    terms.false_term()
                                });
                            }
                        }
                    }
                }
            }
            match folded {
                Some(field) => field,
                None => {
                    let sort = terms.sort(term).clone();
                    terms.mk_app(sym, rargs, sort)
                }
            }
        }
        TermData::Not(x) => {
            let rx = reduce_selectors_rec(terms, ctor_sels, x, memo);
            terms.mk_not(rx)
        }
        TermData::Ite(c, t, e) => {
            let rc = reduce_selectors_rec(terms, ctor_sels, c, memo);
            let rt = reduce_selectors_rec(terms, ctor_sels, t, memo);
            let re = reduce_selectors_rec(terms, ctor_sels, e, memo);
            terms.mk_ite(rc, rt, re)
        }
        _ => term,
    };
    memo.insert(term, result);
    result
}

/// Intermediate results from the E-matching phase.
pub(super) struct EmatchingSummary {
    pub instantiations: Vec<TermId>,
    /// Union of exact quantifier roots that E-matching processed across rounds.
    pub instantiated_quantifiers: HashSet<TermId>,
    /// Exact source/binding records for proof-producing instances of
    /// unconditionally asserted foralls.
    pub unconditional_forall_instantiations: Vec<crate::ematching::ForallInstantiationProvenance>,
    pub has_uninstantiated: bool,
    pub uninstantiated_quantifiers: HashSet<TermId>,
    pub reached_limit: bool,
    /// Number of E-matching rounds actually executed (#8614).
    pub rounds_completed: u64,
    /// Total instances created across all rounds (#8614).
    pub instances_created: u64,
    /// Union (across all rounds) of ground-instance roots that are instances of
    /// UNCONDITIONALLY-asserted Foralls — the SOUND conflict-verification
    /// support subset (see [`crate::ematching::collect_unconditional_foralls`]).
    pub unconditional_forall_roots: HashSet<TermId>,
}

fn classify_ematching_proof_sources(
    provenance: &super::super::theories::solve_harness::ProofProblemAssertionProvenance,
) -> (HashSet<TermId>, HashMap<TermId, TermId>) {
    let direct: HashSet<TermId> = provenance
        .original_problem_assertions
        .iter()
        .copied()
        .collect();
    let normalized = provenance
        .assertion_sources
        .iter()
        .filter_map(|(&derived, source_sets)| {
            // Require one unambiguous singleton source rooted in the immutable
            // authored assertion set. Duplicate and multi-source mappings fail
            // closed and cannot reach the proof tracker.
            let [source_set] = source_sets.as_slice() else {
                return None;
            };
            let [source] = source_set.as_slice() else {
                return None;
            };
            (!direct.contains(&derived) && direct.contains(source)).then_some((derived, *source))
        })
        .collect();
    (direct, normalized)
}

/// Intermediate results from CEGQI setup.
pub(super) struct CegqiPreparation {
    pub cegqi_has_forall: bool,
    pub cegqi_has_exists: bool,
    pub cegqi_ce_lemma_ids: Vec<TermId>,
    /// Per-universal CE-conjunct groups (#cegqi-per-universal): for each
    /// CEGQI-handled quantifier, the surviving AND-conjuncts of ITS CE lemma.
    pub cegqi_ce_lemma_groups: Vec<(TermId, Vec<TermId>)>,
    pub has_completely_unhandled_quantifiers: bool,
    pub unhandled_quantifiers: Vec<TermId>,
    pub cegqi_state: Vec<(TermId, CegqiInstantiator)>,
}

/// (#p2-diag-position) Collect, in deterministic assertion order, the universal
/// quantifiers that are ENTAILED as NNF CONJUNCTS of `term` under the given
/// `positive` polarity — the SOUND candidate set for
/// [`Executor::add_diagonal_forall_instances`], whose instances are asserted as
/// top-level conjuncts.
///
/// This is a thin alias for the CANONICAL predicate
/// [`crate::ematching::collect_entailed_foralls`]. It used to be a second,
/// byte-identical copy; the two were merged when the same entailment condition
/// became the soundness gate for the E-matching / enumerative / MBQI
/// instantiation lanes as well (#auflia-disjunct-forall-false-unsat). Keep ONE
/// implementation: a divergence between "entailed enough for the diagonal pass"
/// and "entailed enough to instantiate" would be a silent soundness hole.
pub(super) fn collect_entailed_foralls(
    terms: &mut TermStore,
    term: TermId,
    positive: bool,
    out: &mut Vec<TermId>,
) {
    crate::ematching::collect_entailed_foralls(terms, term, positive, out);
}

impl Executor {
    /// Freeze the immutable user-assertion scope before preprocessing creates
    /// solver-visible replacements or theory axioms.
    ///
    /// With this provenance active, proof bootstrap may still *see* temporary
    /// assertions, but they are not authorized as problem Assumes. A producer
    /// must derive them from these original roots (as the certified
    /// single-forall Skolem lane below does) or proof export fails closed.
    pub(in crate::executor) fn install_proof_source_provenance(
        &mut self,
        original_assertions: &[TermId],
    ) {
        if !self.produce_proofs_enabled() || self.proof_problem_assertion_provenance.is_some() {
            return;
        }
        let mut assertion_sources = HashMap::default();
        for &source in original_assertions {
            assertion_sources.insert(source, vec![vec![source]]);
        }
        self.proof_problem_assertion_provenance = Some(
            super::super::theories::solve_harness::ProofProblemAssertionProvenance {
                original_problem_assertions: original_assertions.to_vec(),
                problem_assertions: original_assertions.to_vec(),
                assertion_sources,
            },
        );
    }

    /// Register strict proof derivations for exact E-matching instances whose
    /// source is itself a direct authenticated problem assertion.
    ///
    /// `collect_unconditional_foralls` also recognizes foralls nested under a
    /// top-level conjunction. Those instances are semantically sound, but this
    /// narrow proof lane does not yet derive the conjunction projection, so it
    /// refuses them here rather than introducing the nested forall as a free
    /// Assume. The tracker independently recomputes every substitution.
    pub(super) fn register_ematching_proof_provenance(
        &mut self,
        records: &[crate::ematching::ForallInstantiationProvenance],
    ) {
        if !self.produce_proofs_enabled() || records.is_empty() {
            return;
        }
        let (direct_sources, normalized_sources) = self
            .proof_problem_assertion_provenance
            .as_ref()
            .map(classify_ematching_proof_sources)
            .unwrap_or_default();
        let direct_indices: HashMap<TermId, usize> = self
            .proof_problem_assertion_provenance
            .as_ref()
            .map(|provenance| {
                provenance
                    .original_problem_assertions
                    .iter()
                    .copied()
                    .enumerate()
                    .map(|(index, term)| (term, index))
                    .collect()
            })
            .unwrap_or_default();
        for record in records {
            if direct_sources.contains(&record.quantifier) {
                let registered = self.proof_tracker.add_forall_instantiated_assertion(
                    &mut self.ctx.terms,
                    record.quantifier,
                    &record.binding,
                    record.instance,
                );
                if registered.is_some() {
                    if let Some(&assertion_index) = direct_indices.get(&record.quantifier) {
                        let proof_record = super::super::EmatchingProofRecord {
                            assertion_index,
                            quantifier: record.quantifier,
                            binding: record.binding.clone(),
                            instance: record.instance,
                        };
                        if !self.ematching_proof_records.contains(&proof_record) {
                            self.ematching_proof_records.push(proof_record);
                        }
                    }
                }
            } else if let Some(&source) = normalized_sources.get(&record.quantifier) {
                let _ = self
                    .proof_tracker
                    .add_normalized_forall_instantiated_assertion(
                        &mut self.ctx.terms,
                        source,
                        record.quantifier,
                        &record.binding,
                        record.instance,
                    );
            }
        }
    }

    /// Expand finite-domain quantifiers (Bool, small BV) into ground conjunctions/disjunctions.
    ///
    /// For `(forall ((b Bool)) (P b))` → `(and (P true) (P false))`.
    /// For `(exists ((b Bool)) (P b))` → `(or (P true) (P false))`.
    /// Runs BEFORE Skolemization so finite-domain existentials get ground expansion
    /// instead of Skolem constants. Up to 256 combinations per quantifier. (#5848)
    /// (#quant-diagonal) Add the all-bound-vars-EQUAL ("diagonal") instances of each
    /// universal over >=2 same-sort bound variables, over the ground constants of that
    /// sort. Trigger-based e-matching only instantiates at ground TUPLES already
    /// present, so a refutation needing the diagonal self-pair — e.g. `(X0:=d, X1:=d)`
    /// when only `(s d b)` is present — is missed and AY wrongly answers SAT for an
    /// unsat EPR/UF formula (fuzzer Class B). Cheap: `k` instances per forall (k =
    /// #constants), NOT `k^n`.
    ///
    /// # SOUNDNESS CONTRACT (#p2-diag-position wrong-UNSAT repair)
    ///
    /// The diagonal instance is asserted as a TOP-LEVEL CONJUNCT, so it is sound
    /// ONLY for a universal that is itself ENTAILED by the assertion set — i.e.
    /// an NNF conjunct (top-level forall, forall under `and`, negated exists,
    /// negated implication conclusion, …). A forall that is merely a DISJUNCT
    /// (`(or c (forall x y. p x y))`) or an `ite` branch is NOT entailed; conjoining
    /// its diagonal instance manufactures `p(0,0)` out of thin air and turned
    /// trivially-SAT formulas into wrong `unsat` (probes a12/t1–t3/u2/x4). The
    /// caller MUST therefore collect candidates with
    /// [`collect_entailed_foralls`] — polarity-tracking, stops at every
    /// non-entailing connective — and NEVER with
    /// [`crate::ematching::collect_quantifiers`], which flattens through
    /// `or`/`ite` without polarity and surfaces non-entailed foralls.
    pub(super) fn add_diagonal_forall_instances(&mut self, quantifiers: &[TermId]) {
        let seed = self.ctx.assertions.clone();
        let by_sort = collect_ground_terms_by_sort(&self.ctx.terms, &seed);
        let mut to_add: Vec<TermId> = Vec::new();
        for &quant in quantifiers {
            // A no_mbqi ("E-matching only") quantifier — the Hilbert-`choose`
            // combined axiom `forall i,j. P(i,j) => P(chosen)` — must NOT receive
            // diagonal self-pair instances. Over a TRANSPARENT predicate the
            // diagonal `P(c,c)` is trivially true (e.g. reflexivity of `<=`), so
            // the instance `P(c,c) => P(chosen)` discharges the choose existential
            // with NO genuine ground witness — proving `P(chosen)` where Verus
            // (trigger-only, no synthesis) does not. Skip it; the choose axiom is
            // then discharged solely by E-matching a real program-level witness.
            // Sound (this pass only ADDS logical consequences, so dropping some
            // can never cause a wrong-UNSAT).
            if self.ctx.terms.is_no_mbqi(quant) {
                continue;
            }
            let (vars, body) = match self.ctx.terms.get(quant) {
                TermData::Forall(v, b, _) => (v.clone(), *b),
                _ => continue,
            };
            if vars.len() < 2 {
                continue; // diagonal only matters for >=2 vars
            }
            let sort0 = vars[0].1.clone();
            if !vars.iter().all(|(_, s)| *s == sort0) {
                continue; // all bound vars must share a sort
            }
            let Some(consts) = by_sort.get(&sort0) else {
                continue;
            };
            if consts.is_empty() || consts.len() > 64 {
                continue; // bound the linear blowup
            }
            let names: Vec<String> = vars.iter().map(|(n, _)| n.clone()).collect();
            for &c in &consts.clone() {
                let mut subst: HashMap<String, TermId> = HashMap::default();
                for n in &names {
                    subst.insert(n.clone(), c);
                }
                to_add.push(subst_vars(&mut self.ctx.terms, body, &subst));
            }
        }
        if !to_add.is_empty() {
            let mut seen: HashSet<TermId> = self.ctx.assertions.iter().copied().collect();
            self.ctx
                .assertions
                .extend(to_add.into_iter().filter(|t| seen.insert(*t)));
        }
    }

    pub(super) fn expand_finite_domains(&mut self) {
        // #bool-ground-inst: Bool binders are finite-domain-expanded at
        // {true, false}, which DESTROYS the quantifier (and with it any
        // trigger), so an opaque Bool term `c` buried in a UF argument
        // position never receives an instantiation: `f(c)` floats free of the
        // expanded `f(true)`/`f(false)` and the ground solver cannot relate
        // them (the SAT layer never branches on `c`, so EUF never merges it
        // with the true/false class — #bool-arg-congruence; the eager
        // congruence lemma is single-shot-only, see executor/theories/euf.rs).
        // Fix: instantiate Bool binders ALSO at the assertion set's ground
        // Bool UF-argument terms. This is EQUIVALENCE-preserving — every model
        // interprets ground `c:Bool` as true or false, so `P(c)` is redundant
        // given `P(true) /\ P(false)` — hence sound at any polarity and for
        // exists as well. Scoped exactly around this expansion run (mirrors
        // `set_derived_consts`); capped to keep the combo blowup bounded.
        const MAX_BOOL_GROUND_CANDIDATES: usize = 16;
        let mut bool_candidates =
            crate::ematching::collect_bool_uf_arg_terms(&self.ctx.terms, &self.ctx.assertions);
        bool_candidates.truncate(MAX_BOOL_GROUND_CANDIDATES);
        crate::skolemize::set_bool_ground_instantiation_candidates(bool_candidates);
        let mut expanded = Vec::new();
        for i in 0..self.ctx.assertions.len() {
            let a = self.ctx.assertions[i];
            // Recurse into the whole assertion (not just a top-level quantifier) so a
            // bounded quantifier NESTED under `(not ...)` / `(and ...)` / `(or ...)` is
            // also expanded. `(not (exists X. (and (<= 0 X)(<= X 4) p)))` was NOT a
            // top-level quantifier, so the old top-level-only `finite_domain_expand`
            // skipped it; the residue `p` was then dropped downstream → false-UNSAT
            // (= (not p), trivially sat). The recursive expander turns it into
            // `(not (or p..p))` = `(not p)`. Sound (finite expansion); the bounds
            // checks inside still gate large domains to E-matching.
            let ground = crate::skolemize::expand_finite_domain_subterms(&mut self.ctx.terms, a);
            if ground != a {
                expanded.push((i, ground));
            }
        }
        for (idx, ground) in expanded {
            // (#quant-expansion-proof) Record provenance when a TOP-LEVEL
            // `forall` assertion is replaced in place by its ground instance
            // conjunction, so the proof exporter can re-derive the consumed
            // conjuncts from the original premise via `forall_inst` instead
            // of assuming the merged expansion (which no external checker can
            // match to a problem premise). Gated on the recording expansion
            // reproducing the exact replacement term (fail-closed: a
            // miniscoped/folded route records nothing and the exporter keeps
            // its current behavior). Purely observational — the replacement
            // itself is byte-identical either way.
            let a = self.ctx.assertions[idx];
            if matches!(self.ctx.terms.get(a), TermData::Forall(..)) {
                if let Some((recorded_ground, instances)) =
                    crate::skolemize::finite_domain_expand_with_instances(&mut self.ctx.terms, a)
                {
                    if recorded_ground == ground {
                        // Normalize each instance with the SIMPLIFYING
                        // constructors (the substitution builds `or`/`and`
                        // connectives raw, so a discharged guard leaves
                        // `(or c false ..)` unfolded): the later ground
                        // preprocessing folds the merged conjuncts the same
                        // way, and the exporter matches the folded forms.
                        // Instances folding to a constant carry no derivable
                        // content and are dropped.
                        let mut folded_instances: Vec<(Vec<TermId>, TermId)> =
                            Vec::with_capacity(instances.len());
                        for (vals, inst) in instances {
                            let folded = match self.ctx.terms.get(inst).clone() {
                                TermData::App(sym, args) if sym.name() == "or" => {
                                    self.ctx.terms.mk_or(args)
                                }
                                TermData::App(sym, args) if sym.name() == "and" => {
                                    self.ctx.terms.mk_and(args)
                                }
                                _ => inst,
                            };
                            if !matches!(self.ctx.terms.get(folded), TermData::Const(_)) {
                                folded_instances.push((vals, folded));
                            }
                        }
                        // (#bv-forall-const-expansion) The record is pushed even
                        // when EVERY instance folded away. Two different things
                        // live in this struct and they must not be conflated:
                        //
                        //   * `instances` is proof-export PAYLOAD — the conjuncts
                        //     a `forall_inst` derivation can re-derive. A constant
                        //     instance has nothing to derive, so dropping it is
                        //     right (and `plan_quant_consequence` skips `Const`
                        //     instances again on its own side).
                        //   * the record's EXISTENCE is the authenticated fact
                        //     that this exact authored `forall` was replaced in
                        //     place by the canonical finite-domain expansion.
                        //     `result_mapping`'s BV full-domain recognizer reads
                        //     precisely that fact ("capability is not evidence")
                        //     before granting `bv_quantifier_full_domain_proof`.
                        //
                        // Gating the record on a non-empty payload silently
                        // withdrew the authentication for exactly the expansions
                        // that discharged the quantifier COMPLETELY. Measured at
                        // cbb3157aeb with the release binary:
                        //
                        //   ∀x:BV8. (0 <u x ∨ f(x) = 0)  -> sat      (z3: sat)
                        //   ∀x:BV8. (0 <u x ∨ x = 0)     -> unknown  (z3: sat)
                        //
                        // Same guard, same expansion range `[0,0]`, same solver
                        // route; the only difference is that the second one's
                        // single instance `(= #x00 #x00)` constant-folds to
                        // `true`, so the payload emptied and the record vanished.
                        // The guard-range early return (`hi < lo`, folded to
                        // `true` with no recorded instance at all) lost it the
                        // same way.
                        //
                        // Restoring the record cannot loosen the SAT certificate:
                        // the recognizer independently re-runs the canonical
                        // expander on the authored assertion and additionally
                        // requires a non-nested all-BV-binder `forall` plus full
                        // E-matching coverage, and this site still requires
                        // `recorded_ground == ground` (the recording expansion
                        // reproduced the exact replacement term). It only stops
                        // discarding evidence the pass already produced.
                        self.quant_expansion_records
                            .push(crate::executor::QuantExpansionRecord {
                                original: a,
                                assertion_index: idx,
                                expanded: ground,
                                instances: folded_instances,
                            });
                    }
                }
            }
            self.ctx.assertions[idx] = ground;
        }
        // #bool-ground-inst: clear the scoped candidate set (mirrors the
        // `set_derived_consts` discipline — never visible to a nested
        // sub-solve, which must re-derive candidates from ITS assertions).
        crate::skolemize::set_bool_ground_instantiation_candidates(Vec::new());
    }

    /// Skolemize existential quantifiers via polarity-aware deep walk.
    ///
    /// - Positive Exists(vars, body) → body[vars := fresh_constants]
    /// - Negative Forall(vars, body) → (¬body)[vars := fresh_constants]
    ///
    /// Handles existentials nested inside conjunctions/disjunctions, matching
    /// Z3's NNF Skolemizer (reference/z3/src/ast/normal_forms/nnf.cpp:407).
    /// Runs after finite domain expansion so only non-finite-domain existentials
    /// are Skolemized. (#5840)
    pub(super) fn skolemize_existentials(&mut self) {
        let mut skolemized = Vec::new();
        for i in 0..self.ctx.assertions.len() {
            let a = self.ctx.assertions[i];
            let (body, provenance) =
                crate::skolemize::skolemize_deep_with_provenance(&mut self.ctx.terms, a, true);
            if let Some(body) = body {
                skolemized.push((i, a, body, provenance));
            }
        }
        for (idx, original, body, provenance) in skolemized {
            let body = self.add_enum_skolem_coverage(body);
            if self.produce_proofs_enabled() {
                if let TermData::Not(quantified) = self.ctx.terms.get(original) {
                    if let Some(record) = provenance
                        .iter()
                        .find(|record| record.quantified == *quantified)
                    {
                        let _ = self.proof_tracker.add_single_forall_skolemized_assertion(
                            &mut self.ctx.terms,
                            original,
                            record.quantified,
                            record.instance,
                            record.witness,
                            body,
                        );
                    }
                }
            }
            self.ctx.assertions[idx] = body;
        }
    }

    /// Tighten GROUND integer strict less-than atoms `(< s t)` to the equivalent
    /// non-strict `(<= s (- t 1))`, leaving surviving quantifier bodies untouched.
    ///
    /// # Why (#forall-goal-boundary)
    ///
    /// Discharging a universal GOAL `(forall i. (and (<= lo i) (< i hi)) ⇒ P)`
    /// skolemizes its negation `(not goal)` ≡ `(exists i. ...)` to a fresh ground
    /// witness `k` carrying the boundary atom `(< k hi)`. When `hi = (+ len 1)`
    /// (the index just past the last element — the slot of a just-pushed element)
    /// the refutation needs `k = len` on the branch where `k >= len`. Over the
    /// integers `(< k (+ len 1))` is `(<= k len)`, which combined with `k >= len`
    /// forces `k = len`; the LIA solver then EXPORTS that implied equality to the
    /// congruence closure so `read(arr, k) ≡ read(arr, len)` and the per-element
    /// predicate at the new element closes the case. But ay-lia only exports an
    /// implied equality from a *non-strict* two-sided bound (`a<=b ∧ b<=a ⇒ a=b`),
    /// not from the rational-shaped strict form `b < a+1` — so the boundary index
    /// was never pinned and the goal stayed Unknown/Sat. Normalizing the strict
    /// atom to its non-strict integer equivalent feeds the existing export path.
    ///
    /// # Soundness
    ///
    /// `(< s t) ≡ (<= s (t-1))` is an exact equivalence over `Int` for BOTH
    /// polarities (`¬(s<t) ≡ s≥t ≡ ¬(s≤t-1)`), so the set of models is unchanged.
    /// This therefore cannot flip any verdict: a valid goal stays Unsat, an invalid
    /// one stays Sat, and no false equality (hence no false Unsat) can be created.
    /// It is purely a syntactic normalization that *enables* the already-sound
    /// non-strict implied-equality export. Real-sorted `<` is left alone (strict and
    /// non-strict differ over the reals). Quantifier bodies are skipped, so trigger
    /// selection / E-matching of the assumed invariant are unaffected — only ground
    /// atoms (including the skolemized goal bound) are rewritten.
    ///
    /// # Ground-equality fold (#ground-length-equation)
    ///
    /// When the upper bound is a SEPARATE variable pinned by an asserted ground
    /// equation — `(< k new_len)` with `(= new_len (+ len 1))` — tightening alone
    /// yields `(<= k (- new_len 1))`, which never reduces to `(<= k len)` because
    /// `new_len` is opaque, so `k` is never pinned and the goal stays Sat. This
    /// pass first collects the asserted ground integer equalities
    /// (`collect_ground_int_eq_subst`) and folds them into the strict-bound
    /// tightening: the `new_len` leaf is replaced by `(+ len 1)`, reproducing the
    /// inline `(<= k (- (+ len 1) 1))` ≡ `(<= k len)` form the existing export
    /// already pins. Substituting an ASSERTED equality is an exact integer
    /// equivalence (same soundness guarantee as the strict-bound rewrite above):
    /// it can only turn a previously-unrefuted VALID goal `unsat`, never make an
    /// INVALID goal wrongly `unsat`.
    pub(super) fn tighten_ground_int_strict_bounds(&mut self) {
        let subst = self.collect_ground_int_eq_subst();
        let authored_equalities: Vec<TermId> = if self.produce_proofs_enabled() {
            self.proof_original_problem_assertions()
                .into_iter()
                .filter(|&assertion| {
                    matches!(
                        self.ctx.terms.get(assertion),
                        TermData::App(Symbol::Named(name), args)
                            if name == "=" && args.len() == 2
                                && matches!(self.ctx.terms.sort(args[0]), Sort::Int)
                                && matches!(self.ctx.terms.sort(args[1]), Sort::Int)
                    )
                })
                .collect()
        } else {
            Vec::new()
        };
        let mut cache: HashMap<TermId, TermId> = HashMap::default();
        for i in 0..self.ctx.assertions.len() {
            let a = self.ctx.assertions[i];
            let rewritten = tighten_int_strict_term(&mut self.ctx.terms, a, &subst, &mut cache);
            if rewritten != a {
                if self.produce_proofs_enabled() {
                    let _ = self.proof_tracker.add_certified_int_rewrite_assertion(
                        &mut self.ctx.terms,
                        a,
                        rewritten,
                        &authored_equalities,
                    );
                }
                self.ctx.assertions[i] = rewritten;
            }
        }
        // (#quant-expansion-proof) Keep the quantifier-expansion provenance in
        // sync with the in-place rewrite above: the exported `assume` carries
        // the TIGHTENED assertion, so both the recorded replacement term and
        // its per-instance conjuncts must be tightened with the SAME
        // substitution and cache to stay exactly matchable at proof export.
        let mut records = std::mem::take(&mut self.quant_expansion_records);
        for rec in &mut records {
            rec.expanded =
                tighten_int_strict_term(&mut self.ctx.terms, rec.expanded, &subst, &mut cache);
            for (_, inst) in &mut rec.instances {
                *inst = tighten_int_strict_term(&mut self.ctx.terms, *inst, &subst, &mut cache);
            }
        }
        self.quant_expansion_records = records;

        // #forall-goal-boundary-proof: the proof-producing SeqLIA pipeline is
        // intentionally more conservative than the ordinary search. In
        // particular, it does not always export the equality implied by two
        // opposite non-strict bounds to EUF. That left the proof corroboration
        // of a genuine non-string-Seq UNSAT at a spurious Sat:
        //
        //     len <= sk!i  /\  sk!i <= len
        //     entailed(seq.nth(db, len))
        //     !entailed(seq.nth(db, sk!i))
        //
        // The tightening above has normalized the integer boundary to two
        // semantically opposite bounds.  Its negated-`<=` lane deliberately
        // preserves a common affine translation, so the concrete pair can be
        //
        //     len <= sk!i  /\  sk!i + 1 <= len + 1
        //
        // rather than two syntactically reversed atoms. Add two independently
        // checkable tautologies:
        //
        //     !((sk!i + 1) <= (len + 1)) \/ sk!i <= len
        //
        //     !(len <= sk!i) \/ !(sk!i <= len) \/ len = sk!i
        //
        // The first is admitted only after AY's independent Farkas verifier
        // accepts its `[1, 1]` certificate, then recorded as `la_generic`. The
        // second is the rigid Alethe `la_disequality` shape, independently
        // re-validated by the strict proof checker. Boolean propagation derives
        // the canonical reverse bound and then the equality, so EUF sees the
        // same boundary pin without relying on the missing cross-theory export.
        // Crucially, neither the canonical bound nor the equality is appended as
        // an input assertion: only the two tautological clauses enter SAT, and
        // both are tracked proof steps. Scope this to a registered Skolem
        // CONSTANT: it is precisely the witness minted for a negated forall,
        // excludes arbitrary user-variable preprocessing, and leaves the
        // ordinary no-proof search (including the seed-69 soundness
        // corroboration target) byte-identical.
        //
        // SOUNDNESS: the three-way split is a tautology over Int (indeed over
        // every linear order), and the strict proof checker verifies its exact
        // equality/opposite-bound shape. Adding a tautology preserves the model
        // set; it cannot turn a satisfiable false control into UNSAT.
        if self.produce_proofs_enabled() {
            self.add_tight_skolem_antisymmetry_lemmas();
        }
    }

    /// Add a certified affine bridge followed by the exact tracked tautology
    /// `!(sk <= t) \/ !(t <= sk) \/ sk = t` when proof mode sees two
    /// unconditionally asserted bounds that force a Skolem boundary pin.
    ///
    /// Skolem provenance comes from `TermStore`'s exact registry rather than a
    /// name-prefix guess. Skolem *function* applications are deliberately out
    /// of scope: this repair is for the fresh ground witness of a negated
    /// single-level forall, and widening it is unnecessary.
    fn add_tight_skolem_antisymmetry_lemmas(&mut self) {
        let mut conjuncts: Vec<TermId> = Vec::new();
        for &a in &self.ctx.assertions {
            conjuncts.push(a);
            collect_and_conjuncts(&self.ctx.terms, a, &mut conjuncts);
        }

        let mut bounds: Vec<(TermId, TermId, TermId)> = Vec::new();
        let mut seen_bounds: HashSet<TermId> = HashSet::default();
        for conjunct in conjuncts {
            let TermData::App(sym, args) = self.ctx.terms.get(conjunct) else {
                continue;
            };
            if sym.name() != "<="
                || args.len() != 2
                || !matches!(self.ctx.terms.sort(args[0]), Sort::Int)
                || !matches!(self.ctx.terms.sort(args[1]), Sort::Int)
            {
                continue;
            }
            if seen_bounds.insert(conjunct) {
                bounds.push((args[0], args[1], conjunct));
            }
        }

        let is_skolem_const = |terms: &TermStore, term: TermId| match terms.get(term) {
            TermData::Var(name, _) => terms.is_skolem_symbol(name),
            _ => false,
        };
        let mut present: HashSet<TermId> = self.ctx.assertions.iter().copied().collect();
        let mut derived: Vec<TermId> = Vec::new();
        let mut seen_pairs: HashSet<(TermId, TermId)> = HashSet::default();
        for &(lhs, rhs, lhs_le_rhs) in &bounds {
            let skolem = match (
                is_skolem_const(&self.ctx.terms, lhs),
                is_skolem_const(&self.ctx.terms, rhs),
            ) {
                (true, false) => lhs,
                (false, true) => rhs,
                _ => continue,
            };
            let canonical_pair = if lhs < rhs { (lhs, rhs) } else { (rhs, lhs) };
            if lhs == rhs || seen_pairs.contains(&canonical_pair) {
                continue;
            }

            // Keep the semantic search narrow: the companion must itself
            // mention this exact registered Skolem. Its implication to the
            // canonical reverse bound is then proved, never guessed.
            let mut skolem_target: HashSet<TermId> = HashSet::default();
            skolem_target.insert(skolem);
            let rhs_le_lhs = self
                .ctx
                .terms
                .mk_app(Symbol::named("<="), [rhs, lhs], Sort::Bool);
            let companion = bounds.iter().find_map(|&(_, _, candidate)| {
                if candidate == lhs_le_rhs
                    || !term_mentions_any_var(&self.ctx.terms, candidate, &skolem_target)
                {
                    return None;
                }
                let not_candidate = self.ctx.terms.mk_not_raw(candidate);
                farkas_pair_clause_valid(&self.ctx.terms, not_candidate, rhs_le_lhs)
                    .then_some((candidate, not_candidate))
            });
            let Some((companion, not_companion)) = companion else {
                continue;
            };
            seen_pairs.insert(canonical_pair);

            // Fact 1: the affine companion implies the canonical reverse
            // bound. This is a flat `[1,1]` Farkas lemma, not an assumption.
            if companion != rhs_le_lhs {
                let bridge = self.ctx.terms.mk_app(
                    Symbol::named("or"),
                    [not_companion, rhs_le_lhs],
                    Sort::Bool,
                );
                if present.insert(bridge) {
                    derived.push(bridge);
                    let _ = self.proof_tracker.add_packed_farkas_lemma(
                        &mut self.ctx.terms,
                        bridge,
                        vec![not_companion, rhs_le_lhs],
                        FarkasAnnotation::from_ints(&[1, 1]),
                        TheoryLemmaKind::LraFarkas,
                    );
                }
            }

            // Fact 2: exact linear-order antisymmetry. The tracker records
            // `la_disequality` and its `or` decomposition so SAT reconstruction
            // reuses the flat clause instead of manufacturing an Assume.
            let equality = self.ctx.terms.mk_eq(lhs, rhs);
            let not_lhs_le_rhs = self.ctx.terms.mk_not_raw(lhs_le_rhs);
            let not_rhs_le_lhs = self.ctx.terms.mk_not_raw(rhs_le_lhs);
            let split = self.ctx.terms.mk_app(
                Symbol::named("or"),
                [equality, not_lhs_le_rhs, not_rhs_le_lhs],
                Sort::Bool,
            );
            if present.insert(split) {
                derived.push(split);
                let _ = self.proof_tracker.add_la_disequality_lemma(
                    split,
                    vec![equality, not_lhs_le_rhs, not_rhs_le_lhs],
                );
            }
        }
        self.ctx.assertions.extend(derived);
    }

    /// Collect asserted GROUND integer equalities `v = <expr>` as a substitution
    /// map (keyed on the `Var` `TermId` of `v`, value the integer-equal `<expr>`)
    /// for the ground-length-equation fold in `tighten_ground_int_strict_bounds`.
    ///
    /// Scans the top-level assertions and their AND-conjuncts for `(= x y)` over
    /// `Int` where exactly one side is an atomic `Var` `v`, the other side `<expr>`
    /// is a NON-`Var` (compound/constant) integer term, and `v` does not occur in
    /// `<expr>` (no self reference). To keep the fold an exact, terminating,
    /// single-pass substitution, candidates whose `<expr>` mentions ANY collected
    /// key variable are dropped: every retained value is then key-free, so
    /// re-tightening a replacement cannot loop and chains/cycles are sidestepped
    /// (a dropped chain link is a completeness, never a soundness, concession).
    ///
    /// # Soundness
    ///
    /// Only GENUINELY asserted equalities are collected (no heuristic guessing);
    /// substituting `v` by an integer-equal `<expr>` is an exact equivalence, so a
    /// SAT problem stays SAT and an UNSAT one stays UNSAT — it can only let the
    /// existing implied-equality export pin a boundary index, never manufacture a
    /// false equality or a false UNSAT. Int-gated; quantifier bodies are never
    /// descended into during the fold itself (`tighten_int_strict_term`), so
    /// E-matching / trigger selection are unperturbed.
    fn collect_ground_int_eq_subst(&self) -> HashMap<TermId, TermId> {
        // 1. Gather every asserted conjunct (top-level assertions + AND-conjuncts).
        let mut conjuncts: Vec<TermId> = Vec::new();
        for &a in &self.ctx.assertions {
            conjuncts.push(a);
            collect_and_conjuncts(&self.ctx.terms, a, &mut conjuncts);
        }

        // 2. Extract oriented candidates `(v, expr)` and the set of all key vars.
        let mut candidates: Vec<(TermId, TermId)> = Vec::new();
        let mut keys: HashSet<TermId> = HashSet::default();
        for &c in &conjuncts {
            let TermData::App(sym, args) = self.ctx.terms.get(c) else {
                continue;
            };
            if sym.name() != "=" || args.len() != 2 {
                continue;
            }
            let (x, y) = (args[0], args[1]);
            // Equality operands share a sort; gate the fold to Int.
            if !matches!(self.ctx.terms.sort(x), Sort::Int) {
                continue;
            }
            let x_is_var = matches!(self.ctx.terms.get(x), TermData::Var(..));
            let y_is_var = matches!(self.ctx.terms.get(y), TermData::Var(..));
            let mut singleton: HashSet<TermId> = HashSet::default();
            let cand = if x_is_var && !y_is_var {
                singleton.insert(x);
                (!term_mentions_any_var(&self.ctx.terms, y, &singleton)).then_some((x, y))
            } else if y_is_var && !x_is_var {
                singleton.insert(y);
                (!term_mentions_any_var(&self.ctx.terms, x, &singleton)).then_some((y, x))
            } else {
                // var = var (skip: avoids orientation ambiguity / cycles) or
                // expr = expr (no atomic substitutable side).
                None
            };
            if let Some((v, e)) = cand {
                keys.insert(v);
                candidates.push((v, e));
            }
        }

        // 3. Exclude any variable that occurs inside a SURVIVING quantifier body:
        //    the fold rewrites only ground atoms, so folding such a variable would
        //    desync the ground atom from its E-matching instantiation (#8961).
        let mut vars_under_quant: HashSet<TermId> = HashSet::default();
        for &a in &self.ctx.assertions {
            collect_vars_under_quantifiers(&self.ctx.terms, a, &mut vars_under_quant);
        }

        // 4. Retain only candidates whose RHS mentions no key var (key-free values
        //    ⇒ exact, terminating, single-pass fold) and whose key is purely
        //    ground. First mapping per var wins.
        let mut subst: HashMap<TermId, TermId> = HashMap::default();
        for (v, e) in candidates {
            if subst.contains_key(&v) || vars_under_quant.contains(&v) {
                continue;
            }
            if !term_mentions_any_var(&self.ctx.terms, e, &keys) {
                subst.insert(v, e);
            }
        }
        subst
    }

    /// F6 (bv2nat/int2bv bridge value propagation + evaluation): propagate
    /// asserted ground CONSTANT pins across the `bv2nat`/`int2bv` boundary so a
    /// fixed sequence length threaded through the bridge collapses to a concrete
    /// bitvector, unblocking the seq-concat / frame array-`forall` reasoning that
    /// otherwise stalls at Unknown (probe M1/M1d).
    ///
    /// # Phase 1 — ground fold
    /// [`Self::collect_ground_const_subst`] gathers every asserted `v = <const>`
    /// (Int and BitVec `v`) whose `v` occurs in NO surviving quantifier body, and
    /// [`PropagateValues::fold_with_substitution`] rewrites each assertion under
    /// that map through the canonical folding constructors — INCLUDING `bv2nat` /
    /// `int2bv` (added for F6). A pinned `int2bv_w(len)` over a now-constant `len`
    /// folds to its bitvector, a `bv2nat(k)` over a now-constant `k` folds to its
    /// Int, and a pure-Int goal disjunct such as `(= 2 (+ len_b len_c))` collapses
    /// to `true`/`false` — so the mixed goal reduces to the pure array/BV shape the
    /// decision procedure already refutes. No descent into `forall`/`exists`
    /// bodies (`fold_with_substitution` passes binders through), so triggers / the
    /// e-matching of the assumed invariants are byte-identical.
    ///
    /// # Phase 2 — bv2nat inversion
    /// [`Self::add_ground_bv2nat_inversion_pins`] scans the (folded) ground
    /// conjuncts for a `bv2nat(x) = n` pin with `0 <= n < 2^w` and ADDS the
    /// entailed identity `x = int2bv_w(n)` (a concrete bitvector). `bv2nat` is a
    /// bijection onto `[0, 2^w)` with modular left-inverse `int2bv_w`, so this is
    /// the unique BV witness — the EUF pin the array-`forall` bound needs when the
    /// length-index BV var is itself under a quantifier and cannot be folded in
    /// place.
    ///
    /// # Soundness
    /// Phase 1 substitutes only GENUINELY ASSERTED `v = const` equalities — an
    /// exact equivalence (SAT stays SAT, UNSAT stays sound) via folding
    /// constructors that produce definitionally-equal terms. Phase 2 adds only
    /// TAUTOLOGIES of mixed BV/Int semantics (`bv2nat(x)=n ⇒ x=int2bv_w(n)`),
    /// which remove no model. Neither can turn an invalid goal `unsat`; both only
    /// let the existing sound array/BV reasoning fire. Gated to bridge-bearing
    /// problems ([`Self::assertions_contain_bridge_term`]) — zero blast radius
    /// elsewhere.
    pub(super) fn propagate_bridge_ground_values(&mut self) {
        let dbg = std::env::var_os("AY_DEBUG_CERT").is_some();
        if !self.assertions_contain_bridge_term() {
            if dbg {
                eprintln!("F6/bridge-fold: no bridge term, skip");
            }
            return;
        }
        // Phase 1: fold ground const pins (incl. bv2nat/int2bv) through the
        // ground positions of every assertion.
        let subst = self.collect_ground_const_subst();
        if dbg {
            eprintln!("F6/bridge-fold: subst_size={}", subst.len());
        }
        if !subst.is_empty() {
            let mut pv = crate::preprocess::PropagateValues::new();
            pv.seed_substitution(&subst);
            let mut changed = 0usize;
            for i in 0..self.ctx.assertions.len() {
                let a = self.ctx.assertions[i];
                let rewritten = pv.rewrite_seeded(&mut self.ctx.terms, a);
                if rewritten != a {
                    self.ctx.assertions[i] = rewritten;
                    changed += 1;
                }
            }
            if dbg {
                eprintln!("F6/bridge-fold: rewrote {changed} assertions");
            }
        }
        // Phase 2: bv2nat inversion — COMPUTE the entailed BV identity pins
        // `x = int2bv_w(n)` for every ground `bv2nat(x) = n` (no assertions added
        // yet; see the ordering note below).
        let inversion = self.collect_bv2nat_inversion_pins();
        if dbg {
            eprintln!("F6/bridge-fold: {} inversion pins", inversion.len());
        }
        if !inversion.is_empty() {
            // Phase 3: fold the ground `bv2nat(x)` atoms (and any other ground `x`
            // occurrence) through the `x = <bvconst>` pins, so a residual
            // `(= n (bv2nat x))` collapses to `true` and stops keeping the query
            // in the mixed BV+Int fragment. `rewrite_seeded` skips binder bodies,
            // so a length-index still ranging under a `forall` keeps its symbolic
            // occurrence there while its GROUND occurrences fold.
            let mut inv_subst: HashMap<TermId, TermId> = HashMap::default();
            for &(x, bvconst) in &inversion {
                inv_subst.entry(x).or_insert(bvconst);
            }
            let mut pv = crate::preprocess::PropagateValues::new();
            pv.seed_substitution(&inv_subst);
            let mut changed = 0usize;
            for i in 0..self.ctx.assertions.len() {
                let a = self.ctx.assertions[i];
                let rewritten = pv.rewrite_seeded(&mut self.ctx.terms, a);
                if rewritten != a {
                    self.ctx.assertions[i] = rewritten;
                    changed += 1;
                }
            }
            if dbg {
                eprintln!("F6/bridge-fold: phase-3 rewrote {changed} assertions");
            }
            // Phase 4: NOW add the `x = <bvconst>` pins — AFTER the Phase-3 fold,
            // so the fold cannot collapse the pin into `(= <bvconst> <bvconst>)` =
            // `true` and erase the very EUF fact a symbolic length-index under a
            // surviving `forall` needs. Sound: each is a mixed BV/Int tautology
            // (`bv2nat(x)=n ⇒ x=int2bv_w(n)`), removing no model.
            let mut added = 0usize;
            for &(x, bvconst) in &inversion {
                let eq = self.ctx.terms.mk_eq(x, bvconst);
                if !self.ctx.assertions.contains(&eq) {
                    self.ctx.assertions.push(eq);
                    added += 1;
                }
            }
            if dbg {
                eprintln!("F6/bridge-fold: added {added} inversion-pin assertions");
            }
        }
    }

    /// Does any reachable term use the `bv2nat` / `int2bv` BV↔Int bridge?
    /// The gate for [`Self::propagate_bridge_ground_values`].
    fn assertions_contain_bridge_term(&self) -> bool {
        fn visit(terms: &TermStore, term: TermId, seen: &mut HashSet<TermId>) -> bool {
            if !seen.insert(term) {
                return false;
            }
            match terms.get(term) {
                TermData::App(sym, args) => {
                    matches!(sym.name(), "bv2nat" | "int2bv")
                        || args.iter().any(|&a| visit(terms, a, seen))
                }
                TermData::Not(inner) => visit(terms, *inner, seen),
                TermData::Ite(c, t, e) => {
                    visit(terms, *c, seen) || visit(terms, *t, seen) || visit(terms, *e, seen)
                }
                TermData::Let(bindings, body) => {
                    bindings.iter().any(|(_, v)| visit(terms, *v, seen))
                        || visit(terms, *body, seen)
                }
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                    visit(terms, *body, seen)
                }
                _ => false,
            }
        }
        let mut seen = HashSet::default();
        self.ctx
            .assertions
            .iter()
            .any(|&a| visit(&self.ctx.terms, a, &mut seen))
    }

    /// Collect asserted ground `v = <const>` pins (Int and BitVec `v`) as a
    /// substitution map for the Phase-1 fold. Mirrors
    /// [`Self::collect_ground_int_eq_subst`] but (a) accepts BitVec as well as Int
    /// vars, and (b) requires the RHS to be a concrete CONSTANT (strictly
    /// reducing, clearly folding). Variables occurring under any SURVIVING
    /// quantifier body are excluded, so the fold never desyncs a trigger.
    fn collect_ground_const_subst(&self) -> HashMap<TermId, TermId> {
        let mut conjuncts: Vec<TermId> = Vec::new();
        for &a in &self.ctx.assertions {
            conjuncts.push(a);
            collect_and_conjuncts(&self.ctx.terms, a, &mut conjuncts);
        }
        let mut vars_under_quant: HashSet<TermId> = HashSet::default();
        for &a in &self.ctx.assertions {
            collect_vars_under_quantifiers(&self.ctx.terms, a, &mut vars_under_quant);
        }
        let mut subst: HashMap<TermId, TermId> = HashMap::default();
        for &c in &conjuncts {
            let TermData::App(sym, args) = self.ctx.terms.get(c) else {
                continue;
            };
            if sym.name() != "=" || args.len() != 2 {
                continue;
            }
            let (x, y) = (args[0], args[1]);
            // Orient to `var = const`.
            let candidate = if matches!(self.ctx.terms.get(x), TermData::Var(..))
                && matches!(self.ctx.terms.get(y), TermData::Const(_))
            {
                Some((x, y))
            } else if matches!(self.ctx.terms.get(y), TermData::Var(..))
                && matches!(self.ctx.terms.get(x), TermData::Const(_))
            {
                Some((y, x))
            } else {
                None
            };
            if let Some((v, k)) = candidate {
                if !vars_under_quant.contains(&v) {
                    subst.entry(v).or_insert(k);
                }
            }
        }
        subst
    }

    /// Phase 2 of [`Self::propagate_bridge_ground_values`]: for each ground
    /// `bv2nat(x) = n` pin with `0 <= n < 2^w`, COMPUTE the entailed BV identity
    /// `x = int2bv_w(n)` and return the `(x, <bvconst>)` pairs. `bv2nat` is a
    /// bijection onto `[0, 2^w)` (modular left-inverse `int2bv_w`), so
    /// `int2bv_w(n)` is the UNIQUE preimage — the pin is a tautology and removes
    /// no model. No assertion is added here: the caller folds ground `bv2nat(x)`
    /// atoms through these pins FIRST, then adds `(= x <bvconst>)` so the fold
    /// cannot erase the freshly-added pin (Phase 4).
    fn collect_bv2nat_inversion_pins(&mut self) -> Vec<(TermId, TermId)> {
        let mut conjuncts: Vec<TermId> = Vec::new();
        for &a in &self.ctx.assertions {
            conjuncts.push(a);
            collect_and_conjuncts(&self.ctx.terms, a, &mut conjuncts);
        }
        // Gather `(x, n)` inversion candidates from `(= n (bv2nat x))` conjuncts.
        let mut candidates: Vec<(TermId, num_bigint::BigInt)> = Vec::new();
        for &c in &conjuncts {
            let TermData::App(sym, args) = self.ctx.terms.get(c) else {
                continue;
            };
            if sym.name() != "=" || args.len() != 2 {
                continue;
            }
            let sides = [(args[0], args[1]), (args[1], args[0])];
            for (nside, bside) in sides {
                let TermData::Const(Constant::Int(n)) = self.ctx.terms.get(nside) else {
                    continue;
                };
                let n = n.clone();
                let TermData::App(bsym, bargs) = self.ctx.terms.get(bside) else {
                    continue;
                };
                if bsym.name() == "bv2nat" && bargs.len() == 1 {
                    candidates.push((bargs[0], n));
                    break;
                }
            }
        }
        // Compute the `(x, <bvconst>)` pin for each in-range candidate. Assertions
        // are added by the caller AFTER the Phase-3 fold (see Phase 4).
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut pins: Vec<(TermId, TermId)> = Vec::new();
        for (x, n) in candidates {
            if matches!(self.ctx.terms.get(x), TermData::Const(_)) {
                continue;
            }
            let Sort::BitVec(bv) = self.ctx.terms.sort(x).clone() else {
                continue;
            };
            let width = bv.width;
            if width == 0 {
                continue;
            }
            let modulus = num_bigint::BigInt::from(1) << width as usize;
            if n < num_bigint::BigInt::from(0) || n >= modulus {
                continue;
            }
            let n_term = self.ctx.terms.mk_int(n);
            let bvconst = self.ctx.terms.mk_int2bv(width, n_term);
            if !matches!(self.ctx.terms.get(bvconst), TermData::Const(_)) {
                continue;
            }
            if seen.insert(x) {
                pins.push((x, bvconst));
            }
        }
        pins
    }

    /// Conjoin finite-ENUM-datatype domain-coverage onto a skolemized assertion.
    ///
    /// A fresh Skolem CONSTANT (`sk!…`) over a finite enum datatype `D = {c0..cn}`
    /// — created when a negated-`forall` / positive-`exists` over `D` is
    /// Skolemized — must equal one of the constructors, but the bare fresh `Var`
    /// floats free of `D`'s finite domain. Without coverage, e.g.
    /// `(not (forall ((v D)) (p v))) ∧ (p c0) ∧ … ∧ (p cn)` was wrongly SAT (the
    /// witness `¬p(sk)` never collided with the only inhabitants). We add
    /// `(or (= sk c0) … (= sk cn))` per such Skolem. Sound: a datatype value IS one
    /// of its constructors, so the disjunction holds in every model — it only prunes
    /// spurious ones. Enum (nullary-only) datatypes only; field-carrying/recursive
    /// datatypes need a constructor-with-witness-fields axiom and are left as-is.
    fn add_enum_skolem_coverage(&mut self, body: TermId) -> TermId {
        // Owned map: enum datatype name -> its (nullary) constructor names.
        let dt_list: Vec<(String, Vec<String>)> = self
            .ctx
            .datatype_iter()
            .map(|(n, c)| (n.to_string(), c.iter().map(String::clone).collect()))
            .collect();
        let mut enums: std::collections::HashMap<String, Vec<String>> = Default::default();
        for (name, ctors) in dt_list {
            let all_nullary = ctors.iter().all(|c| {
                self.ctx
                    .constructor_selector_info(c)
                    .map_or(true, |f| f.is_empty())
            });
            if all_nullary && !ctors.is_empty() {
                enums.insert(name, ctors);
            }
        }
        if enums.is_empty() {
            return body;
        }

        // Collect distinct fresh Skolem-constant Vars of an enum-datatype sort.
        let mut sk_vars: Vec<(TermId, String)> = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut stack = vec![body];
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t).clone() {
                TermData::Var(name, _) => {
                    if name.starts_with("sk!") {
                        if let Sort::Uninterpreted(dt) = self.ctx.terms.sort(t).clone() {
                            if enums.contains_key(&dt) && !sk_vars.iter().any(|(v, _)| *v == t) {
                                sk_vars.push((t, dt));
                            }
                        }
                    }
                }
                TermData::App(_, args) => stack.extend(args),
                TermData::Not(i) => stack.push(i),
                TermData::Ite(c, th, e) => {
                    stack.push(c);
                    stack.push(th);
                    stack.push(e);
                }
                TermData::Let(binds, b) => {
                    for (_, v) in binds {
                        stack.push(v);
                    }
                    stack.push(b);
                }
                TermData::Forall(_, b, _) | TermData::Exists(_, b, _) => stack.push(b),
                _ => {}
            }
        }
        if sk_vars.is_empty() {
            return body;
        }

        let mut parts = vec![body];
        for (var, dt) in sk_vars {
            let sort = self.ctx.terms.sort(var).clone();
            let ctors = enums[&dt].clone();
            let eqs: Vec<TermId> = ctors
                .iter()
                .map(|c| {
                    let ct =
                        self.ctx
                            .terms
                            .mk_app(Symbol::named(c), Vec::<TermId>::new(), sort.clone());
                    self.ctx.terms.mk_eq(var, ct)
                })
                .collect();
            let cov = self.ctx.terms.mk_or(eqs);
            parts.push(cov);
        }
        self.ctx.terms.mk_and(parts)
    }

    /// Run multi-round E-matching, collecting instantiations across rounds.
    ///
    /// Uses the persistent `QuantifierManager` for generation tracking (#573).
    /// Extracts the EUF model from the last solve for congruence-aware matching
    /// (Phase B1b, #3325).
    pub(super) fn run_ematching_rounds(&mut self) -> EmatchingSummary {
        let max_rounds = self.ematching_round_limit();

        // M5 FLIP — demand lane (PRODUCTION-authoritative for classified families):
        // compute the frontier-gated family set BEFORE any long-lived borrow of
        // `self`. Only the M1 self-chaining / bridge-cycle foralls are gated —
        // those are the two geometric minters; every OTHER forall is untouched.
        // `demand_lane_eligible` is `true` on every production path (release AND
        // debug); it is `false` only under the debug-only force-eager differential
        // override, where `gated` stays empty and the lane never arms (byte-
        // identical eager path). Crucially, the lane ARMS below only if `gated` is
        // NON-EMPTY, so a solve with no classified family is byte-identical too —
        // this is what bounds the flip's blast radius to classified-family problems.
        let demand_eligible = self.demand_lane_eligible();
        let gated: HashSet<u32> = if demand_eligible {
            let foralls = self.collect_classifiable_foralls();
            let classes = self.classify_quantifier_families(&foralls);
            classes
                .iter()
                .filter(|(_, c)| {
                    matches!(
                        c,
                        crate::executor::quantifier_loop::family_classifier::FamilyClass::SelfChainingDefinitional
                            | crate::executor::quantifier_loop::family_classifier::FamilyClass::BridgeCycle
                    )
                })
                .map(|(tid, _)| tid.0)
                .collect()
        } else {
            HashSet::default()
        };

        // Capture the deadline/interrupt closure before borrowing the quantifier
        // manager mutably (the closure owns its snapshots, no borrow of `self`).
        let should_stop = self.make_should_stop();
        let euf_model_ref = self.last_model.as_ref().and_then(|m| m.euf_model.as_ref());

        let qm = self
            .quantifier_manager
            .get_or_insert_with(QuantifierManager::new);
        // LI-4: begin a new E-matching epoch. Drains the persistent (quant,binding)
        // instantiation memo back to the scope baseline so any instance produced in
        // a PRIOR check-sat (and since retracted by restore_assertions) is
        // re-instantiable in this check-sat. This is a no-op on the incremental-mode
        // path (where the QM is take()-swapped fresh per check-sat) and essential on
        // the non-incremental reused-QM path. Called ONCE per process_quantifiers;
        // run_post_cegqi_ematching and try_ematching_refinement_round share this
        // epoch's memo (no begin_epoch there).
        qm.begin_epoch();
        // M5 FLIP: arm the demand lane for this solve (LAW #7 parking + LAW #1
        // flush). `begin_epoch` reset it to inert above; arm it ONLY when a
        // classified family is present (`gated` non-empty). This is the family-
        // scoping seam: with an empty `gated` set (no self-chaining/bridge-cycle
        // forall, or the force-eager override) the lane stays inert and every
        // downstream armed-state gate falls through to the eager path byte-
        // identically. The warm-start depth seeds the DT resume depth (LAW #5).
        let gated_debug_len = gated.len();
        if !gated.is_empty() {
            qm.demand_arm(gated, crate::executor::dt_axioms::DT_WARM_START_DEPTH);
        }
        let mut assertions_for_round = self.ctx.assertions.clone();
        let mut seen_instantiations: HashSet<TermId> =
            assertions_for_round.iter().copied().collect();
        let mut all_instantiations = Vec::new();
        let mut all_instantiated_quantifiers = HashSet::default();
        let mut all_unconditional_forall_instantiations = Vec::new();
        let mut seen_forall_instantiations = HashSet::default();
        let mut has_uninstantiated = false;
        let mut uninstantiated_quantifiers = HashSet::default();
        let mut reached_limit = false;
        let mut exhausted_round_budget = false;
        let mut rounds_completed: u64 = 0;
        let mut instances_created: u64 = 0;
        let mut all_unconditional_forall_roots: HashSet<TermId> = HashSet::default();

        for round_idx in 0..max_rounds {
            // Deadline/interrupt guard (#quantifier-deadline): stop entering new
            // E-matching rounds once the budget is spent. Setting `reached_limit`
            // routes any in-progress Sat to Unknown(QuantifierRoundLimit) in
            // classify_quantifier_result; it can never finalize a bogus Sat.
            if should_stop() {
                reached_limit = true;
                break;
            }
            let ematching_result = qm.run_ematching_round(
                &mut self.ctx.terms,
                &assertions_for_round,
                euf_model_ref,
                &should_stop,
            );
            rounds_completed += 1;
            let round_reached_limit = ematching_result.reached_limit;
            let round_has_uninstantiated = ematching_result.has_uninstantiated;
            let round_uninstantiated_quantifiers = ematching_result.uninstantiated_quantifiers;
            all_instantiated_quantifiers.extend(ematching_result.instantiated_quantifiers);
            let round_forall_instantiations = ematching_result.unconditional_forall_instantiations;
            instances_created += ematching_result.instantiations.len() as u64;
            all_unconditional_forall_roots.extend(ematching_result.unconditional_forall_roots);
            let mut round_added = 0usize;

            for inst in ematching_result.instantiations {
                if seen_instantiations.insert(inst) {
                    assertions_for_round.push(inst);
                    all_instantiations.push(inst);
                    round_added += 1;
                }
            }
            // Keep proof provenance independently of instance novelty. The same
            // ground term can be seen first from a nested/non-direct quantifier
            // and only later from an authenticated direct forall. Dropping the
            // latter record would lose a valid certificate (not soundness), so
            // deduplicate by the exact source/binding/instance triple instead.
            for record in round_forall_instantiations {
                if seen_forall_instantiations.insert((
                    record.quantifier,
                    record.binding.clone(),
                    record.instance,
                )) {
                    all_unconditional_forall_instantiations.push(record);
                }
            }

            has_uninstantiated = round_has_uninstantiated;
            uninstantiated_quantifiers = round_uninstantiated_quantifiers;
            reached_limit |= round_reached_limit;

            if round_reached_limit || round_added == 0 {
                break;
            }

            // We still made progress on the last allowed round, so there may be
            // additional instantiations if we continued. Treat this as incomplete.
            if round_idx + 1 == max_rounds {
                exhausted_round_budget = true;
            }
        }

        if exhausted_round_budget {
            reached_limit = true;
        }

        // M5 demand-lane diagnostic (env-gated): report the gated set size + this
        // solve's frontier / parked tally BEFORE the (possibly slow) ground
        // final-solve, so a timed-out run still shows whether the lane armed +
        // parked. Fires only when the lane actually armed (a classified family was
        // present). Pure observation.
        if gated_debug_len > 0 && std::env::var_os("AY_DEMAND_DEBUG").is_some() {
            if let Some(qm) = self.quantifier_manager.as_ref() {
                eprintln!(
                    "c demand-lane batch_instances={} gated_families={} frontier={} has_parked={}",
                    all_instantiations.len(),
                    gated_debug_len,
                    qm.demand_frontier(),
                    qm.demand_has_parked(),
                );
            }
        }

        // Post-loop invariant: all_instantiations is a deduplicated set
        // and its items are a subset of assertions_for_round.
        debug_assert!(
            all_instantiations.len() <= assertions_for_round.len() - self.ctx.assertions.len(),
            "E-matching: more unique instantiations ({}) than new assertions ({})",
            all_instantiations.len(),
            assertions_for_round.len() - self.ctx.assertions.len()
        );

        EmatchingSummary {
            instantiations: all_instantiations,
            instantiated_quantifiers: all_instantiated_quantifiers,
            unconditional_forall_instantiations: all_unconditional_forall_instantiations,
            has_uninstantiated,
            uninstantiated_quantifiers,
            reached_limit,
            rounds_completed,
            instances_created,
            unconditional_forall_roots: all_unconditional_forall_roots,
        }
    }

    /// (#recdt) Fold datatype selector-over-constructor applications in an
    /// [`EmatchingSummary`]'s instances and support-axiom roots.
    ///
    /// `instantiate_body` builds each E-matching instance by raw substitution and
    /// does NOT apply the `sel_i(C(t..)) -> t_i` fold the elaborator applies to
    /// user-written terms. A recursive-datatype defining-axiom instantiated at a
    /// constructor term therefore keeps its selector-over-constructor subterm
    /// unreduced — e.g. `sum(Cons(a,r)) = (hd (Cons a r)) + sum(tl (Cons a r))`
    /// rather than the reduced `sum(Cons(a,r)) = a + sum(r)`. The combined DT+LIA
    /// iterative-deepening final-check (`solve_with_dt_axioms`) unrolls the
    /// recursive selector frontier one level deeper per round on the unreduced
    /// form and diverges to a timeout, even though the reduced instance closes the
    /// goal in milliseconds. Folding here reproduces the parser's ground shape.
    ///
    /// SOUNDNESS: the fold is the SMT-LIB datatype selector axiom
    /// (`sel_i(C(t0..tn)) = t_i`), true in every datatype model, so it removes no
    /// models and adds none. Both the instantiation list and the conflict-
    /// verification support subset are folded with the SAME rewrite: a support
    /// root is entailed by universal instantiation, and its fold is a logically
    /// identical (merely simplified) term, so it remains a sound support axiom and
    /// still references a term that `add_ematching_instances` actually asserts.
    pub(super) fn reduce_dt_selectors_in_ematching(&mut self, ematching: &mut EmatchingSummary) {
        // Owned constructor -> ordered-selectors map so the recursive rewrite can
        // borrow only `self.ctx.terms` mutably. Empty for datatype-free problems,
        // in which case every instance is returned unchanged (zero overhead).
        let ctor_sels: HashMap<String, Vec<String>> = self
            .ctx
            .ctor_selectors_iter()
            .map(|(c, sels)| (c.clone(), sels.clone()))
            .collect();
        if ctor_sels.is_empty() {
            return;
        }
        let mut memo: HashMap<TermId, TermId> = HashMap::default();
        let insts = std::mem::take(&mut ematching.instantiations);
        ematching.instantiations = insts
            .into_iter()
            .map(|i| reduce_selectors_rec(&mut self.ctx.terms, &ctor_sels, i, &mut memo))
            .collect();
        ematching
            .unconditional_forall_instantiations
            .retain(|record| {
                reduce_selectors_rec(&mut self.ctx.terms, &ctor_sels, record.instance, &mut memo)
                    == record.instance
            });
        let roots = std::mem::take(&mut ematching.unconditional_forall_roots);
        ematching.unconditional_forall_roots = roots
            .into_iter()
            .map(|r| reduce_selectors_rec(&mut self.ctx.terms, &ctor_sels, r, &mut memo))
            .collect();
    }

    /// Add E-matching instantiations to assertions, filtering duplicates and
    /// model-satisfied instances (Phase C, #575).
    ///
    /// `unconditional_forall_roots` is the SOUND conflict-verification support
    /// subset: every instance in it that is actually ADDED here (guard (ii):
    /// present in `ctx.assertions`) is recorded into `active_support_axioms`.
    ///
    /// Returns `true` if any new instantiation was added.
    pub(super) fn add_ematching_instances(
        &mut self,
        instantiations: Vec<TermId>,
        unconditional_forall_roots: &HashSet<TermId>,
        suppress_stale_model_filter: bool,
    ) -> bool {
        let existing: HashSet<TermId> = self.ctx.assertions.iter().copied().collect();
        let mut skipped_satisfied = 0usize;
        let mut added_count = 0usize;
        for inst in instantiations {
            if existing.contains(&inst) {
                continue;
            }
            // Phase C (#575): Skip instantiations already satisfied by model.
            //
            // SOUNDNESS-PRESERVING COMPLETENESS (#stale-presolve-frame-skip): the
            // ONLY model available here is the PRE-instantiation presolve model
            // (`solve_bv_lia_bridge` / ground-fragment presolve, run before
            // `process_quantifiers`); it is not a model of the quantified problem
            // and it leaves the universal's not-yet-constrained ground terms at
            // arbitrary default values. When the surviving `forall` is
            // MBQI-unsafe (an array-indexing frame invariant), an instance the
            // presolve model "satisfies" via such a defaulted term
            // (`(or (= (select s_new i) v) (not (bvult i li)))` holding only
            // because the free `(select s_new i)` defaulted to `v`) is exactly
            // the constraint the ground solver needs: dropping it lets the ground
            // solver re-pick that free term to a violating value, yielding a
            // SPURIOUS ground `Sat` that the unsafe-partial soundness gate then
            // degrades to `Unknown` (a decided verdict lost). Adding every
            // E-matched instance is always sound (universal instantiation), so
            // suppressing the presolve-model skip here can only RECOVER a decided
            // verdict, never manufacture a wrong one. Left ON for the common
            // (MBQI-safe) case so those problems keep the byte-identical clause
            // set and its perf.
            if !suppress_stale_model_filter {
                if let Some(ref model) = self.last_model {
                    if matches!(self.evaluate_term(model, inst), EvalValue::Bool(true)) {
                        skipped_satisfied += 1;
                        continue;
                    }
                }
            }
            self.ctx.assertions.push(inst);
            added_count += 1;
            // Record the sound support-axiom subset: `inst` is an instance of an
            // unconditionally-asserted Forall AND is now in ctx.assertions.
            if unconditional_forall_roots.contains(&inst) {
                self.push_active_support_axiom(inst);
            }
        }
        let _ = skipped_satisfied;
        added_count > 0
    }

    /// Append `TheoryLit::new(root, true)` to the accumulated conflict-verification
    /// support set (dedup by term). `root` MUST be a ground instance of an
    /// UNCONDITIONALLY-asserted Forall (top-level conjunct) that is currently in
    /// `ctx.assertions` — callers guarantee both provenance guards. Sound: `root`
    /// is entailed by universal instantiation, hence true in every model of the
    /// problem, so asserting it in the fresh conflict verifier can only confirm a
    /// genuine conflict, never launder a spurious one.
    pub(super) fn push_active_support_axiom(&mut self, root: TermId) {
        if self.active_support_axioms.iter().any(|l| l.term == root) {
            return;
        }
        self.active_support_axioms.push(TheoryLit::new(root, true));
    }

    /// Promote-unsat optimization (Phase D, #557): check deferred instantiations
    /// against the current model and promote conflict-producing ones.
    ///
    /// Returns the number of promoted instantiations.
    pub(super) fn promote_deferred_conflicts(&mut self) -> usize {
        let existing: HashSet<TermId> = self.ctx.assertions.iter().copied().collect();

        let promoted_count = if let Some(ref model) = self.last_model {
            // Phase 1: Extract deferred entries and instantiate terms
            let deferred_with_terms: Vec<_> = {
                let qm = self
                    .quantifier_manager
                    .as_mut()
                    .expect("invariant: quantifier_manager populated by get_or_insert_with above");
                qm.deferred
                    .drain(..)
                    .map(|def| {
                        let inst_term = def.instantiate(&mut self.ctx.terms);
                        (def, inst_term)
                    })
                    .collect()
            };

            // Phase 2: Evaluate each term and decide promote/keep
            let mut promoted = 0usize;
            let mut remaining_deferred = std::collections::VecDeque::new();
            for (def, inst_opt) in deferred_with_terms {
                if let Some(inst_term) = inst_opt {
                    let negated = self.ctx.terms.mk_not(inst_term);
                    match self.evaluate_term(model, negated) {
                        EvalValue::Bool(true) => {
                            if !existing.contains(&inst_term) {
                                self.ctx.assertions.push(inst_term);
                                promoted += 1;
                            }
                        }
                        _ => {
                            remaining_deferred.push_back(def);
                        }
                    }
                } else {
                    remaining_deferred.push_back(def);
                }
            }

            // Phase 3: Put back non-promoted deferred
            if let Some(ref mut qm) = self.quantifier_manager {
                qm.deferred = remaining_deferred;
            }
            promoted
        } else {
            0
        };
        promoted_count
    }

    /// Set up CEGQI for arithmetic quantifiers that E-matching couldn't handle.
    ///
    /// Only applied to quantifiers with no E-matching instantiations (#1939).
    /// Also runs enumerative instantiation for triggerless forall quantifiers
    /// (#3441/#5042). Tracks completely unhandled quantifiers for MBQI (#2865/#5971).
    pub(super) fn setup_cegqi_for_unhandled(
        &mut self,
        quantifiers: &[TermId],
        ematching_has_uninstantiated: bool,
        ematching_uninstantiated_quantifiers: &HashSet<TermId>,
    ) -> CegqiPreparation {
        let mut cegqi_has_forall = false;
        let mut cegqi_has_exists = false;
        let mut raw_ce_lemma_ids: Vec<TermId> = Vec::new();
        // Provenance for the per-universal SAT flip (#cegqi-per-universal):
        // which quantifier each raw CE lemma was created for. Parallel to the
        // `raw_ce_lemma_ids` pushes below.
        let mut raw_ce_lemma_quants: Vec<TermId> = Vec::new();
        let mut cegqi_ce_lemma_ids: Vec<TermId> = Vec::new();
        let mut has_completely_unhandled_quantifiers = false;
        let mut unhandled_quantifier_list: Vec<TermId> = Vec::new();
        let mut cegqi_state: Vec<(TermId, CegqiInstantiator)> = Vec::new();
        // Enumerative instantiation is an incomplete fallback. It should range
        // over ground terms already present in the preprocessed problem, not
        // recursively bootstrap on sibling instantiations added earlier in the
        // same pass. Using the growing assertion set lets later triggerless
        // quantifiers enumerate terms synthesized by earlier ones, creating a
        // one-shot saturation loop on recursive axiom families (#7883).
        let enum_seed_assertions = self.ctx.assertions.clone();

        // (#auflia-disjunct-forall-false-unsat) The universals the CURRENT
        // assertion set actually ENTAILS. Computed over the pre-CEGQI snapshot —
        // i.e. the same set the caller collected `quantifiers` from, and BEFORE
        // `flatten_and_strip_quantifiers` deletes every quantified assertion.
        // Only these may have a ground instance conjoined (see the gate below).
        let entailed_foralls: HashSet<TermId> =
            crate::ematching::entailed_forall_set(&mut self.ctx.terms, &enum_seed_assertions);

        // #forall-bare-bool wrong-SAT: snapshot the genuine (non-CE) assertions
        // that exist BEFORE any CE lemma is pushed below, together with their
        // flattened AND-conjuncts. A CE lemma built by `create_ce_lemma` negates
        // the forall body via De Morgan, so a bare-Bool residual `p` inside the
        // forall yields a `(not p)` CE conjunct that is the HASH-CONSED-IDENTICAL
        // TermId to a genuine user assertion (e.g. an asserted `(not p)`, or the
        // `(not p)` folded from an asserted `p` of opposite sign). Without this
        // snapshot, `flatten_and_strip_quantifiers` captures that aliased TermId
        // into `cegqi_ce_lemma_ids`, and `disambiguate_cegqi_unsat` then DROPS the
        // genuine assertion when it strips CE lemmas — manufacturing a spurious
        // SAT whose model contradicts the dropped constraint. By excluding
        // pre-existing genuine assertions from `cegqi_ce_lemma_ids` we keep
        // `cegqi_ce_lemma_ids` CE-EXCLUSIVE, so the genuine assertion survives the
        // ground re-solve and the result is the correct UNSAT.
        let pre_cegqi_assertions: HashSet<TermId> = {
            let mut acc: Vec<TermId> = Vec::new();
            for &a in &self.ctx.assertions {
                acc.push(a);
                collect_and_conjuncts(&self.ctx.terms, a, &mut acc);
            }
            acc.into_iter().collect()
        };

        for &quant in quantifiers {
            let has_triggers = match self.ctx.terms.get(quant) {
                TermData::Forall(_, _, triggers) | TermData::Exists(_, _, triggers) => {
                    !triggers.is_empty()
                }
                _ => false,
            };

            // #3441/#5042: For triggerless FORALL quantifiers, run enumerative
            // instantiation as a complement to CEGQI.
            let is_forall = matches!(self.ctx.terms.get(quant), TermData::Forall(..));
            let is_triggerless_cegqi_forall =
                !has_triggers && is_forall && is_cegqi_candidate(&self.ctx.terms, quant);
            // (#auflia-disjunct-forall-false-unsat) A `forall` the assertion set
            // does NOT ENTAIL — one reachable only under a positive `or`/`=>` or
            // an `ite` — must not be instantiated here either. `enumerative_
            // instantiation` below pushes `body[t/x]` straight into
            // `ctx.assertions` as a top-level conjunct, and its own doc comment
            // states the false premise ("sound because every instantiation of a
            // universally quantified formula is implied by the formula" — implied
            // by the FORMULA, yes; by the PROBLEM, only when the problem entails
            // the formula). This lane independently reproduced the six
            // 20170829-Rodin false-`unsat`s: gating E-matching alone flipped only
            // 3 of 6, because the enumerative lane re-derived the same fabricated
            // literal from the same disjunct-position `forall`. The excluded
            // quantifier falls through to the fail-closed routing below, which
            // records it as unhandled so no SAT certificate can grant on it
            // either.
            let quant_is_entailed_forall = !is_forall || entailed_foralls.contains(&quant);
            // A `forall` marked "E-matching only" (`mark_no_mbqi`, e.g. the
            // Hilbert-`choose` witness axiom) is EXCLUDED from CEGQI synthesis
            // instantiation, exactly as it is from MBQI. It falls through to the
            // fail-closed routing below, so it is discharged only by E-matching
            // on a ground trigger (an established witness), matching Verus.
            let should_process = !self.ctx.terms.is_no_mbqi(quant)
                && quant_is_entailed_forall
                && (is_triggerless_cegqi_forall
                    || (ematching_has_uninstantiated
                        && ematching_uninstantiated_quantifiers.contains(&quant)));
            if !should_process {
                // #3 (BV/UF forall fail-closed): a forall that is neither a
                // CEGQI candidate nor an E-matching-uninstantiated quantifier
                // (e.g. a pure BitVector-sorted forall whose bound-variable
                // domain exceeds the enumerative instantiation budget) must
                // still be routed to MBQI. Otherwise it is silently dropped and
                // the ground SAT result is returned unverified, producing a
                // wrong SAT on truly-UNSAT problems. Track it here so MBQI can
                // exhaust its budget and fail closed to Unknown.
                if is_forall {
                    unhandled_quantifier_list.push(quant);
                    if !has_triggers {
                        has_completely_unhandled_quantifiers = true;
                    }
                }
                continue;
            }
            if !has_triggers && is_forall {
                let enum_insts = enumerative_instantiation(
                    &mut self.ctx.terms,
                    &enum_seed_assertions,
                    quant,
                    100,
                );
                for inst in enum_insts {
                    self.ctx.assertions.push(inst);
                }
            }

            let mut handled_by_cegqi = false;
            // #6045: Skip CEGQI for trigger-annotated quantifiers.
            if !has_triggers && is_cegqi_candidate(&self.ctx.terms, quant) {
                if let Some(inst) = CegqiInstantiator::new(quant, &mut self.ctx.terms) {
                    if let Some(ce_lemma) = inst.create_ce_lemma(&mut self.ctx.terms) {
                        if inst.is_forall() {
                            cegqi_has_forall = true;
                        } else {
                            cegqi_has_exists = true;
                        }
                        self.ctx.assertions.push(ce_lemma);
                        raw_ce_lemma_ids.push(ce_lemma);
                        raw_ce_lemma_quants.push(quant);
                        handled_by_cegqi = true;
                        cegqi_state.push((quant, inst));
                    }
                }
            }
            if !handled_by_cegqi {
                if is_forall {
                    unhandled_quantifier_list.push(quant);
                }
                if !has_triggers {
                    has_completely_unhandled_quantifiers = true;
                }
            }
        }

        // Flatten, recompute CE lemma IDs, and strip quantifiers.
        let mut cegqi_ce_lemma_groups: Vec<(TermId, Vec<TermId>)> = Vec::new();
        self.flatten_and_strip_quantifiers(
            &raw_ce_lemma_ids,
            &raw_ce_lemma_quants,
            &pre_cegqi_assertions,
            &mut cegqi_ce_lemma_ids,
            &mut cegqi_ce_lemma_groups,
        );

        CegqiPreparation {
            cegqi_has_forall,
            cegqi_has_exists,
            cegqi_ce_lemma_ids,
            cegqi_ce_lemma_groups,
            has_completely_unhandled_quantifiers,
            unhandled_quantifiers: unhandled_quantifier_list,
            cegqi_state,
        }
    }

    /// Flatten top-level AND assertions (#4877), recompute CE lemma IDs after
    /// flattening (#5991), and strip quantified formulas from assertions.
    fn flatten_and_strip_quantifiers(
        &mut self,
        raw_ce_lemma_ids: &[TermId],
        raw_ce_lemma_quants: &[TermId],
        pre_cegqi_assertions: &HashSet<TermId>,
        cegqi_ce_lemma_ids: &mut Vec<TermId>,
        cegqi_ce_lemma_groups: &mut Vec<(TermId, Vec<TermId>)>,
    ) {
        {
            let mut flatten = FlattenAnd::new();
            flatten.apply(&mut self.ctx.terms, &mut self.ctx.assertions);
        }

        if !raw_ce_lemma_ids.is_empty() {
            let mut expanded = Vec::new();
            for &ce_id in raw_ce_lemma_ids {
                expanded.push(ce_id);
                collect_and_conjuncts(&self.ctx.terms, ce_id, &mut expanded);
            }
            let ce_set: HashSet<TermId> = expanded.into_iter().collect();
            // #forall-bare-bool wrong-SAT: keep `cegqi_ce_lemma_ids` CE-EXCLUSIVE.
            // A CE-lemma AND-conjunct can be the hash-consed-identical TermId to a
            // genuine user assertion that pre-existed the CE lemma (a De Morgan
            // `(not p)` from a bare-Bool forall residual aliasing an asserted
            // `(not p)`/`p`). Such a term is already conjoined as a genuine ground
            // assertion, so its CE-lemma role is redundant; treating it as a CE
            // lemma makes `disambiguate_cegqi_unsat` DROP the genuine constraint
            // and report a spurious SAT. Excluding pre-existing genuine assertions
            // guarantees the constraint survives the ground re-solve.
            *cegqi_ce_lemma_ids = self
                .ctx
                .assertions
                .iter()
                .copied()
                .filter(|a| ce_set.contains(a) && !pre_cegqi_assertions.contains(a))
                .collect();
            // Per-universal conjunct groups (#cegqi-per-universal): each raw
            // CE lemma `¬B_q(c⃗)` AND-flattens into conjuncts that lose their
            // provenance in the flat list above. The SAT flip's sound unit of
            // refutation is the whole per-quantifier CONJUNCTION, so record,
            // for every quantifier, exactly its lemma's surviving conjuncts
            // (same live + CE-exclusive filter as the flat list; a conjunct
            // aliasing a genuine assertion participates via the ground core
            // instead). Conjuncts shared between two universals' lemmas by
            // hash-consing appear in both groups — each group is solved
            // independently, so sharing is harmless.
            let live: HashSet<TermId> = self.ctx.assertions.iter().copied().collect();
            *cegqi_ce_lemma_groups = raw_ce_lemma_ids
                .iter()
                .zip(raw_ce_lemma_quants)
                .map(|(&ce_id, &quant)| {
                    let mut conjuncts = vec![ce_id];
                    collect_and_conjuncts(&self.ctx.terms, ce_id, &mut conjuncts);
                    let mut group: Vec<TermId> = Vec::new();
                    for c in conjuncts {
                        if live.contains(&c)
                            && !pre_cegqi_assertions.contains(&c)
                            && !group.contains(&c)
                        {
                            group.push(c);
                        }
                    }
                    (quant, group)
                })
                .collect();
        }

        self.ctx
            .assertions
            .retain(|&a| !contains_quantifier(&self.ctx.terms, a));
    }

    /// Post-CEGQI E-matching pass (#7979): run one E-matching round over the
    /// current (quantifier-stripped) assertions combined with the original
    /// quantifiers from the refinement snapshot.
    ///
    /// Enumerative instantiation and CEGQI may have introduced new ground terms
    /// (e.g., `f(6)` from a triggerless `forall y. y > 5 => f(y) > 0`) that
    /// can trigger patterns in other quantifiers. Without this pass, the
    /// triggered quantifier never sees the ground term and returns Unknown.
    ///
    /// Returns `(added_any, Option<EmatchingSummary>)`.
    pub(super) fn run_post_cegqi_ematching(
        &mut self,
        refinement_assertions: &Option<Vec<TermId>>,
        _prev_uninstantiated: &HashSet<TermId>,
    ) -> (bool, Option<EmatchingSummary>) {
        let Some(ref_assertions) = refinement_assertions else {
            return (false, None);
        };

        // Build combined assertion set: current stripped assertions + quantifiers
        // from the refinement snapshot. This lets E-matching see both the new
        // ground terms from enumerative/CEGQI and the quantifier patterns.
        let mut combined = self.ctx.assertions.clone();
        for &a in ref_assertions {
            if contains_quantifier(&self.ctx.terms, a) && !combined.contains(&a) {
                combined.push(a);
            }
        }

        // Capture the deadline/interrupt closure before borrowing the quantifier
        // manager mutably so the single post-CEGQI round can also be cut short.
        let should_stop = self.make_should_stop();
        let euf_model_ref = self.last_model.as_ref().and_then(|m| m.euf_model.as_ref());
        let qm = self
            .quantifier_manager
            .get_or_insert_with(QuantifierManager::new);
        // Fresh round group: this single post-CEGQI round runs over a re-cloned,
        // quantifier-stripped-then-re-added slice that may not extend the main
        // loop's slice. Reset the index/eqclasses so they are an exact function of
        // `combined` (the seen memo persists across the epoch).
        qm.begin_round_group();

        // `combined` is a NON-monotonically rewritten root set (assertions were
        // flattened + quantifier-stripped, then refinement quantifiers re-added).
        // `begin_round_group` already reset the persisted index/eqclasses to an
        // exact function of `combined`, so no separate cache invalidation is
        // needed here (the incremental match-state design supersedes the old
        // `invalidate_index` cached-TermIndex path).
        let ematching_result =
            qm.run_ematching_round(&mut self.ctx.terms, &combined, euf_model_ref, &should_stop);
        self.register_ematching_proof_provenance(
            &ematching_result.unconditional_forall_instantiations,
        );

        let existing: HashSet<TermId> = self.ctx.assertions.iter().copied().collect();
        let mut added_count = 0usize;

        for &inst in &ematching_result.instantiations {
            if existing.contains(&inst) {
                continue;
            }
            // Skip quantifier-containing terms (they should not be added as ground instances)
            if contains_quantifier(&self.ctx.terms, inst) {
                continue;
            }
            self.ctx.assertions.push(inst);
            added_count += 1;
            // Record the sound support-axiom subset for the just-added instance
            // (present in ctx.assertions ⇒ guard (ii) holds).
            if ematching_result.unconditional_forall_roots.contains(&inst) {
                self.push_active_support_axiom(inst);
            }
        }

        if added_count > 0 {
            let inst_count = ematching_result.instantiations.len() as u64;
            let summary = EmatchingSummary {
                instantiations: ematching_result.instantiations,
                instantiated_quantifiers: ematching_result.instantiated_quantifiers,
                unconditional_forall_instantiations: ematching_result
                    .unconditional_forall_instantiations,
                has_uninstantiated: ematching_result.has_uninstantiated,
                uninstantiated_quantifiers: ematching_result.uninstantiated_quantifiers,
                reached_limit: ematching_result.reached_limit,
                rounds_completed: 1,
                instances_created: inst_count,
                unconditional_forall_roots: ematching_result.unconditional_forall_roots,
            };
            (true, Some(summary))
        } else {
            (false, None)
        }
    }

    /// (#p2-nested-forall) Prenex same-polarity binder-merge prepass.
    ///
    /// Rewrites every DIRECTLY nested same-polarity binder tower
    /// `Forall(vs1, Forall(vs2, B, trigIn), [])` into the single quantifier
    /// `Forall(vs1 ++ vs2', B')` (dually for `Exists`/`Exists`), where `vs2`
    /// is alpha-renamed to fresh names via the capture-avoiding
    /// [`subst_vars`]. The rewrite is a classical logical EQUIVALENCE
    /// (`∀x.∀y.B ⇔ ∀x,y.B` up to renaming), valid in EVERY context and under
    /// every polarity (no nonemptiness assumption is even needed for the
    /// direct-adjacency form), so it is applied uniformly across the whole
    /// term DAG — including towers under `not`, inside `and`/`or`, etc.
    ///
    /// Motivation: the trigger-pattern language cannot express a hole for a
    /// foreign (inner-bound) variable, so an outer `forall` whose body is
    /// another `forall` never receives a trigger and falls through every
    /// instantiation lane straight to `Unknown(QuantifierUnhandled)`
    /// (pattern_helpers.rs `collect_patterns_from_term_with_let_scopes` has no
    /// binder arm). The FLATTENED form is fully handled today (measured:
    /// `a_flat` decides where `g2a` was unknown).
    ///
    /// Deliberately NOT done (fail-safe by omission, each configuration
    /// already decides or stays soundly unknown today):
    ///   - No hoisting of a forall out of `and`/`or`/`=>` bodies: nested
    ///     instantiation rounds already discharge those (the `tw_shadow`
    ///     control), and hoisting would replace a working path with an
    ///     inferred-trigger merged quantifier whose patterns need not cover
    ///     all binders.
    ///   - Outer triggers non-empty: skip (user trigger scope must not be
    ///     silently widened; that configuration already decides — `a_pattern`).
    ///   - `no_mbqi`-marked quantifiers (Hilbert-choose witness axioms): skip —
    ///     their trigger-only discipline must be preserved verbatim.
    ///
    /// Inner triggers are carried onto the merged quantifier ONLY when every
    /// trigger group covers the FULL merged binder set (an E-matcher
    /// substitution built from a group that lacks a binder would be partial —
    /// asserting an instance with a dangling bound var is unsound), otherwise
    /// they are dropped and trigger inference runs on the merged body.
    /// Dropping/keeping triggers is heuristic-only either way: instantiation
    /// at any substitution is universally sound.
    ///
    /// DETECT-BEFORE-MINT: a read-only scan runs first; when no tower exists
    /// anywhere, the pass returns without creating a single term, so
    /// non-tower problems are byte-identical (TermId-stable) to baseline.
    pub(super) fn merge_adjacent_universals(&mut self) {
        let has_tower = self
            .ctx
            .assertions
            .iter()
            .any(|&a| term_has_same_polarity_binder_tower(&self.ctx.terms, a));
        if !has_tower {
            return;
        }
        let assertions = self.ctx.assertions.clone();
        let mut memo: HashMap<TermId, TermId> = HashMap::default();
        let rewritten: Vec<TermId> = assertions
            .iter()
            .map(|&a| self.merge_binder_towers_rewrite(a, &mut memo))
            .collect();
        self.ctx.assertions = rewritten;
    }

    /// Bottom-up, memoized rewrite for [`Self::merge_adjacent_universals`].
    /// Reconstructs a node ONLY when a child changed or a merge fired, so
    /// untouched subtrees keep their TermIds.
    fn merge_binder_towers_rewrite(
        &mut self,
        t: TermId,
        memo: &mut HashMap<TermId, TermId>,
    ) -> TermId {
        if let Some(&r) = memo.get(&t) {
            return r;
        }
        let result = stacker::maybe_grow(TIGHTEN_STACK_RED_ZONE, TIGHTEN_STACK_SIZE, || {
            match self.ctx.terms.get(t).clone() {
                TermData::Const(_) | TermData::Var(_, _) => t,
                TermData::App(sym, args) => {
                    let new_args: Vec<TermId> = args
                        .iter()
                        .map(|&a| self.merge_binder_towers_rewrite(a, memo))
                        .collect();
                    if new_args == args {
                        t
                    } else {
                        let sort = self.ctx.terms.sort(t).clone();
                        self.ctx.terms.mk_app(sym, new_args, sort)
                    }
                }
                TermData::Not(inner) => {
                    let ni = self.merge_binder_towers_rewrite(inner, memo);
                    if ni == inner {
                        t
                    } else {
                        self.ctx.terms.mk_not(ni)
                    }
                }
                TermData::Ite(c, a, b) => {
                    let nc = self.merge_binder_towers_rewrite(c, memo);
                    let na = self.merge_binder_towers_rewrite(a, memo);
                    let nb = self.merge_binder_towers_rewrite(b, memo);
                    if nc == c && na == a && nb == b {
                        t
                    } else {
                        self.ctx.terms.mk_ite(nc, na, nb)
                    }
                }
                // `Let` should not survive to this phase (expanded earlier); if
                // one does, leave it untouched — a tower under an unexpanded
                // `Let` simply stays on today's (sound, fail-closed) path.
                TermData::Let(..) => t,
                TermData::Forall(vars, body, triggers) => {
                    self.merge_binder_tower_node(
                        t, vars, body, triggers, /*forall=*/ true, memo,
                    )
                }
                TermData::Exists(vars, body, triggers) => {
                    self.merge_binder_tower_node(
                        t, vars, body, triggers, /*forall=*/ false, memo,
                    )
                }
                // Future TermData variants: leave unchanged.
                _ => t,
            }
        });
        memo.insert(t, result);
        result
    }

    /// Merge the same-polarity binder chain starting at one quantifier node.
    /// `vars`/`body`/`triggers` are the node's parts; `forall` selects the
    /// polarity (Forall-Forall or Exists-Exists; mixed polarities never merge).
    fn merge_binder_tower_node(
        &mut self,
        t: TermId,
        vars: Vec<(String, Sort)>,
        body: TermId,
        triggers: Vec<Vec<TermId>>,
        forall: bool,
        memo: &mut HashMap<TermId, TermId>,
    ) -> TermId {
        let new_body = self.merge_binder_towers_rewrite(body, memo);
        let mut vars = vars;
        let mut cur_body = new_body;
        let mut cur_trig = triggers;
        let mut merged = false;
        // `no_mbqi` on the OUTER node: preserve the annotated quantifier
        // verbatim (only rebuild if the body itself changed below).
        let outer_no_mbqi = self.ctx.terms.is_no_mbqi(t);
        while cur_trig.is_empty() && !outer_no_mbqi {
            let inner = match self.ctx.terms.get(cur_body).clone() {
                TermData::Forall(iv, ib, it) if forall => Some((iv, ib, it)),
                TermData::Exists(iv, ib, it) if !forall => Some((iv, ib, it)),
                _ => None,
            };
            let Some((ivars, ibody, itrig)) = inner else {
                break;
            };
            if self.ctx.terms.is_no_mbqi(cur_body) {
                break;
            }
            // Alpha-rename every inner binder to a globally fresh name via the
            // capture-avoiding substitution (kills the tw_shadow no-rename
            // weakening: `∀x. q(x) → ∀x. p(x)` must NOT become `∀x. q(x)→p(x)`).
            let mut subst: HashMap<String, TermId> = HashMap::default();
            let mut renamed: Vec<(String, Sort)> = Vec::with_capacity(ivars.len());
            for (name, sort) in &ivars {
                let fresh = self
                    .ctx
                    .terms
                    .mk_fresh_var(&format!("{name}!merge"), sort.clone());
                let TermData::Var(fresh_name, _) = self.ctx.terms.get(fresh).clone() else {
                    // mk_fresh_var always returns a Var; fail safe: no merge.
                    return if cur_body == body && !merged {
                        t
                    } else {
                        self.rebuild_quantifier(vars, cur_body, cur_trig, forall)
                    };
                };
                subst.insert(name.clone(), fresh);
                renamed.push((fresh_name, sort.clone()));
            }
            let nb = subst_vars(&mut self.ctx.terms, ibody, &subst);
            vars.extend(renamed);
            // Inner triggers survive ONLY when every group covers the full
            // merged binder set (after renaming); a group missing a binder
            // would let the matcher build a PARTIAL substitution.
            let renamed_trig: Vec<Vec<TermId>> = itrig
                .iter()
                .map(|group| {
                    group
                        .iter()
                        .map(|&p| subst_vars(&mut self.ctx.terms, p, &subst))
                        .collect()
                })
                .collect();
            let all_names: Vec<&str> = vars.iter().map(|(n, _)| n.as_str()).collect();
            let keep = !renamed_trig.is_empty()
                && renamed_trig
                    .iter()
                    .all(|group| trigger_group_covers_names(&self.ctx.terms, group, &all_names));
            cur_trig = if keep { renamed_trig } else { Vec::new() };
            cur_body = nb;
            merged = true;
        }
        if !merged && cur_body == body {
            t
        } else {
            self.rebuild_quantifier(vars, cur_body, cur_trig, forall)
        }
    }

    fn rebuild_quantifier(
        &mut self,
        vars: Vec<(String, Sort)>,
        body: TermId,
        triggers: Vec<Vec<TermId>>,
        forall: bool,
    ) -> TermId {
        if forall {
            self.ctx.terms.mk_forall_with_triggers(vars, body, triggers)
        } else {
            self.ctx.terms.mk_exists_with_triggers(vars, body, triggers)
        }
    }
}

/// Read-only scan for [`Executor::merge_adjacent_universals`]: does `root`
/// contain a DIRECTLY nested same-polarity binder tower whose outer node has
/// no triggers? (`Forall` whose body is a `Forall`, or `Exists` whose body is
/// an `Exists`.) Never mints a term.
fn term_has_same_polarity_binder_tower(terms: &TermStore, root: TermId) -> bool {
    let mut visited: HashSet<TermId> = HashSet::default();
    let mut stack: Vec<TermId> = vec![root];
    while let Some(t) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        match terms.get(t) {
            TermData::Forall(_, body, trig) => {
                if trig.is_empty() && matches!(terms.get(*body), TermData::Forall(..)) {
                    return true;
                }
                stack.push(*body);
            }
            TermData::Exists(_, body, trig) => {
                if trig.is_empty() && matches!(terms.get(*body), TermData::Exists(..)) {
                    return true;
                }
                stack.push(*body);
            }
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, a, b) => {
                stack.push(*c);
                stack.push(*a);
                stack.push(*b);
            }
            TermData::Let(bindings, body) => {
                for (_, v) in bindings {
                    stack.push(*v);
                }
                stack.push(*body);
            }
            _ => {}
        }
    }
    false
}

/// True iff every merged binder name occurs somewhere in the trigger group's
/// patterns — the coverage requirement for carrying an inner trigger onto a
/// merged quantifier (a non-covering group would yield partial substitutions).
fn trigger_group_covers_names(terms: &TermStore, group: &[TermId], names: &[&str]) -> bool {
    let mut found: HashSet<String> = HashSet::default();
    let mut visited: HashSet<TermId> = HashSet::default();
    let mut stack: Vec<TermId> = group.to_vec();
    while let Some(t) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        match terms.get(t) {
            TermData::Var(name, _) => {
                found.insert(name.clone());
            }
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
    names.iter().all(|n| found.contains(*n))
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::{ProofId, ProofStep, Sort, Symbol, TermData};
    use ay_frontend::parse;
    use num_bigint::BigInt;

    fn raw_nnf_forall_source(
        terms: &mut TermStore,
        prefix: &str,
        predicate: &str,
    ) -> (TermId, String) {
        let binder_name = format!("{prefix}_x");
        let x = terms.mk_var(&binder_name, Sort::Int);
        let upper = terms.mk_var(&format!("{prefix}_upper"), Sort::Int);
        let zero = terms.mk_int(BigInt::from(0));
        let p_x = terms.mk_app(Symbol::named(predicate), [x], Sort::Bool);
        let nonnegative = terms.mk_le(zero, x);
        let below_upper = terms.mk_lt(x, upper);
        let raw_not_nonnegative = terms.mk_not_raw(nonnegative);
        let raw_not_below_upper = terms.mk_not_raw(below_upper);
        let raw_body = terms.mk_app(
            Symbol::named("or"),
            [p_x, raw_not_nonnegative, raw_not_below_upper],
            Sort::Bool,
        );
        (
            terms.mk_forall(vec![(binder_name.clone(), Sort::Int)], raw_body),
            binder_name,
        )
    }

    fn instantiate_forall_body(
        terms: &mut TermStore,
        quantified: TermId,
        binder_name: &str,
        value: TermId,
    ) -> TermId {
        let TermData::Forall(_, body, _) = terms.get(quantified).clone() else {
            panic!("expected forall");
        };
        let mut substitution = HashMap::default();
        substitution.insert(binder_name.to_string(), value);
        subst_vars(terms, body, &substitution)
    }

    #[test]
    fn ambiguous_normalized_forall_source_mapping_fails_closed() {
        let authored_a = TermId(1);
        let authored_b = TermId(2);
        let unique = TermId(3);
        let duplicate = TermId(4);
        let multi_source = TermId(5);
        let unauthored = TermId(6);
        let mut assertion_sources = HashMap::default();
        assertion_sources.insert(unique, vec![vec![authored_a]]);
        assertion_sources.insert(duplicate, vec![vec![authored_a], vec![authored_a]]);
        assertion_sources.insert(multi_source, vec![vec![authored_a, authored_b]]);
        assertion_sources.insert(unauthored, vec![vec![TermId(99)]]);
        let provenance =
            super::super::super::theories::solve_harness::ProofProblemAssertionProvenance {
                original_problem_assertions: vec![authored_a, authored_b],
                problem_assertions: vec![authored_a, authored_b],
                assertion_sources,
            };

        let (direct, normalized) = classify_ematching_proof_sources(&provenance);
        assert_eq!(direct.len(), 2);
        assert_eq!(normalized.get(&unique), Some(&authored_a));
        assert!(
            !normalized.contains_key(&duplicate),
            "duplicate source records must be treated as ambiguous"
        );
        assert!(
            !normalized.contains_key(&multi_source),
            "multi-source provenance must not authorize this narrow lane"
        );
        assert!(
            !normalized.contains_key(&unauthored),
            "a source outside the immutable authored roots must be rejected"
        );
    }

    #[test]
    fn exact_recursive_nnf_forall_provenance_registers_strict_instance() {
        let mut exec = Executor::new();
        exec.set_produce_proofs(true);
        let (authored, binder_name) =
            raw_nnf_forall_source(&mut exec.ctx.terms, "exact_nnf", "exact_nnf_p");
        exec.ctx.assertions.push(authored);
        exec.install_proof_source_provenance(&[authored]);

        exec.fold_quantified_linear_eqs();
        let [normalized] = exec.ctx.assertions.as_slice() else {
            panic!("expected one normalized assertion");
        };
        let normalized = *normalized;
        assert_ne!(normalized, authored);
        let (_, exact_sources) = classify_ematching_proof_sources(
            exec.proof_problem_assertion_provenance
                .as_ref()
                .expect("proof provenance"),
        );
        assert_eq!(
            exact_sources.get(&normalized),
            Some(&authored),
            "recursive NNF must install its exact constructor-minted source edge"
        );

        let value = exec.ctx.terms.mk_var("exact_nnf_k", Sort::Int);
        let instance =
            instantiate_forall_body(&mut exec.ctx.terms, normalized, &binder_name, value);
        exec.register_ematching_proof_provenance(&[
            crate::ematching::ForallInstantiationProvenance {
                quantifier: normalized,
                binding: vec![value],
                instance,
            },
        ]);

        let mut proof = exec.proof_tracker.take_proof();
        let derived = proof
            .steps
            .iter()
            .enumerate()
            .rev()
            .find_map(|(index, step)| {
                matches!(
                    step,
                    ProofStep::Resolution { clause, .. } if clause == &[instance]
                )
                .then(|| ProofId(u32::try_from(index).expect("proof index")))
            })
            .expect("exact recursive provenance must register the instance");
        let not_instance = exec.ctx.terms.mk_not_raw(instance);
        let negated = proof.add_assume(not_instance, None);
        proof.add_resolution(Vec::new(), instance, derived, negated);
        let quality = ay_proof::check_proof_strict_with_context(
            &proof,
            &exec.ctx.terms,
            None,
            None,
            Some(&[authored, not_instance]),
        )
        .expect("recursive NNF instance proof must pass the strict checker");
        assert!(quality.is_complete());
        assert_eq!(quality.trust_count, 0);
    }

    #[test]
    fn absent_exact_nnf_record_never_uses_duplicate_or_same_shape_roots() {
        let mut exec = Executor::new();
        exec.set_produce_proofs(true);
        let (authored_a, binder_name) =
            raw_nnf_forall_source(&mut exec.ctx.terms, "same_shape", "same_shape_a");
        let (authored_b, _) =
            raw_nnf_forall_source(&mut exec.ctx.terms, "same_shape", "same_shape_b");
        exec.ctx.assertions.push(authored_a);
        exec.fold_quantified_linear_eqs();
        let [normalized] = exec.ctx.assertions.as_slice() else {
            panic!("fixture must produce one normalized forall");
        };
        let normalized = *normalized;
        assert_ne!(normalized, authored_a);

        // Freeze the authored roots but deliberately do not install the minted
        // transform record. Identical binder/trigger shapes and a duplicate
        // authored occurrence must not act as an implicit source search.
        exec.ctx.assertions = vec![authored_a, authored_b, authored_a];
        exec.install_proof_source_provenance(&[authored_a, authored_b, authored_a]);
        let value = exec.ctx.terms.mk_var("same_shape_k", Sort::Int);
        let instance =
            instantiate_forall_body(&mut exec.ctx.terms, normalized, &binder_name, value);
        exec.register_ematching_proof_provenance(&[
            crate::ematching::ForallInstantiationProvenance {
                quantifier: normalized,
                binding: vec![value],
                instance,
            },
        ]);
        assert_eq!(
            exec.proof_tracker.num_steps(),
            0,
            "no exact record means no proof authority, regardless of source shape"
        );
    }

    #[test]
    fn recursive_nnf_record_from_nested_nonroot_forall_is_filtered() {
        let mut exec = Executor::new();
        exec.set_produce_proofs(true);
        let (nested, binder_name) =
            raw_nnf_forall_source(&mut exec.ctx.terms, "nested_nnf", "nested_nnf_p");
        let guard = exec.ctx.terms.mk_var("nested_nnf_guard", Sort::Bool);
        let root = exec
            .ctx
            .terms
            .mk_app(Symbol::named("and"), [guard, nested], Sort::Bool);
        exec.ctx.assertions.push(root);
        exec.install_proof_source_provenance(&[root]);

        exec.fold_quantified_linear_eqs();
        let [rewritten_root] = exec.ctx.assertions.as_slice() else {
            panic!("expected one rewritten root");
        };
        let TermData::App(symbol, arguments) = exec.ctx.terms.get(*rewritten_root) else {
            panic!("rewritten root must remain a conjunction");
        };
        assert_eq!(symbol.name(), "and");
        let normalized = arguments
            .iter()
            .copied()
            .find(|&term| matches!(exec.ctx.terms.get(term), TermData::Forall(..)))
            .expect("nested forall must remain present");
        assert_ne!(normalized, nested);
        let (_, exact_sources) = classify_ematching_proof_sources(
            exec.proof_problem_assertion_provenance
                .as_ref()
                .expect("proof provenance"),
        );
        assert!(
            !exact_sources.contains_key(&normalized),
            "a constructor-minted record cannot authorize a non-root source"
        );

        let value = exec.ctx.terms.mk_var("nested_nnf_k", Sort::Int);
        let instance =
            instantiate_forall_body(&mut exec.ctx.terms, normalized, &binder_name, value);
        exec.register_ematching_proof_provenance(&[
            crate::ematching::ForallInstantiationProvenance {
                quantifier: normalized,
                binding: vec![value],
                instance,
            },
        ]);
        assert_eq!(
            exec.proof_tracker.num_steps(),
            0,
            "nested/non-root source must not reach proof registration"
        );
    }

    /// Proof authority is frozen before the binder-tower merge. The merged
    /// assertion is a semantics-preserving solver input, but it is not authored
    /// source text and therefore cannot appear as a problem `Assume` unless a
    /// producer first certifies the rewrite.
    #[test]
    fn nested_forall_merge_is_not_proof_source_authority() {
        let smt = r#"
            (set-logic UFLIA)
            (declare-fun p (Int Int) Bool)
            (declare-fun a () Int)
            (declare-fun b () Int)
            (assert (forall ((x Int)) (forall ((y Int)) (=> (p x y) (< x y)))))
            (assert (p a b))
            (assert (>= a b))
        "#;
        let commands = parse(smt).unwrap();
        let mut exec = Executor::new();
        exec.set_produce_proofs(true);
        for command in &commands {
            assert!(exec.execute(command).unwrap().is_none());
        }

        let source_snapshot = exec.ctx.assertions.clone();
        let quantifier_result = exec.process_quantifiers();
        let merged_snapshot = quantifier_result
            .original_assertions
            .as_ref()
            .expect("quantifier processing must retain its restoration snapshot");
        let merged = merged_snapshot[0];
        assert_ne!(
            merged, source_snapshot[0],
            "the restoration snapshot must contain the merged binder tower"
        );
        let TermData::Forall(vars, _, _) = exec.ctx.terms.get(merged) else {
            panic!("merged restoration term must remain a forall")
        };
        assert_eq!(vars.len(), 2, "the nested binders must have been merged");

        // Exercise a downstream combined-theory provenance installation too.
        // It may narrow the temporary assertion window, but it must preserve
        // the already-frozen authored roots on a definitive result.
        let result = exec.solve_uf_lia().unwrap();
        assert!(result.is_unsat(), "ground UFLIA core must remain UNSAT");

        let authored = exec.proof_original_problem_assertions();
        let [authored_tower, _, _] = authored.as_slice() else {
            panic!(
                "expected the three authored assertions in proof provenance, got {}: {:?}",
                authored.len(),
                authored
                    .iter()
                    .map(|&term| exec.ctx.terms.get(term))
                    .collect::<Vec<_>>()
            )
        };
        let TermData::Forall(_, nested, _) = exec.ctx.terms.get(*authored_tower) else {
            panic!("proof source must retain the authored outer forall")
        };
        assert!(
            matches!(exec.ctx.terms.get(*nested), TermData::Forall(..)),
            "proof source must retain the authored two-level binder tower"
        );

        assert_ne!(merged, *authored_tower);
        assert!(
            !exec.proof_problem_assertions().contains(&merged),
            "the merged solver assertion must not be whitelisted as authored proof authority"
        );

        // Exercise the production problem-scope authority boundary with the
        // exact merged term. A forged proof that assumes it must fail closed.
        let not_merged = exec.ctx.terms.mk_not_raw(merged);
        let mut forged = ay_core::Proof::new();
        let h_merged = forged.add_assume(merged, None);
        let h_not_merged = forged.add_assume(not_merged, None);
        forged.add_resolution(Vec::new(), merged, h_merged, h_not_merged);
        let mut authority_scope = authored;
        authority_scope.push(not_merged);
        let err = ay_proof::try_export_alethe_with_problem_scope_and_overrides(
            &forged,
            &exec.ctx.terms,
            &authority_scope,
            None,
        )
        .expect_err("a merged binder tower must not acquire authored Assume authority");
        assert!(matches!(
            err,
            ay_proof::AlethePrintError::NonProblemAssume { term, .. } if term == merged
        ));
    }

    #[test]
    fn test_triggerless_enumeration_uses_frozen_seed_assertions_7883() {
        let smt = r#"
            (set-logic ALL)
            (declare-sort S 0)
            (declare-fun a () S)
            (declare-fun g (S) S)
            (declare-fun P (S) Bool)
            (assert (P a))
            (assert (forall ((x S)) (P (g x))))
            (assert (forall ((y S)) (=> (P y) false)))
        "#;
        let commands = parse(smt).expect("valid SMT-LIB input");
        let mut exec = Executor::new();
        let outputs = exec.execute_all(&commands).expect("commands execute");
        assert!(
            outputs.is_empty(),
            "setup-only script should not emit output"
        );

        let quantifiers: Vec<TermId> = exec
            .ctx
            .assertions
            .iter()
            .copied()
            .filter(|&a| contains_quantifier(&exec.ctx.terms, a))
            .collect();
        assert_eq!(quantifiers.len(), 2, "expected two triggerless quantifiers");

        let uninstantiated: HashSet<TermId> = quantifiers.iter().copied().collect();

        let ground_assertion = exec.ctx.assertions[0];
        let (p_sym, a_term) = match exec.ctx.terms.get(ground_assertion) {
            TermData::App(sym, args) if args.len() == 1 => (sym.clone(), args[0]),
            other => panic!("expected ground assertion P(a), got {other:?}"),
        };
        let a_sort = exec.ctx.terms.sort(a_term).clone();
        let g_a = exec
            .ctx
            .terms
            .mk_app(Symbol::named("g"), vec![a_term], a_sort);
        let p_g_a = exec.ctx.terms.mk_app(p_sym, vec![g_a], Sort::Bool);
        let not_p_a = exec.ctx.terms.mk_not(ground_assertion);
        let not_p_g_a = exec.ctx.terms.mk_not(p_g_a);

        let _prep = exec.setup_cegqi_for_unhandled(&quantifiers, true, &uninstantiated);

        assert!(
            exec.ctx.assertions.contains(&p_g_a),
            "first quantifier should still enumerate x := a and add P(g(a))"
        );
        assert!(
            exec.ctx.assertions.contains(&not_p_a),
            "second quantifier should still enumerate over the original seed term a"
        );
        assert!(
            !exec.ctx.assertions.contains(&not_p_g_a),
            "second quantifier must not bootstrap on P(g(a)) added earlier in the same pass"
        );
    }
}
