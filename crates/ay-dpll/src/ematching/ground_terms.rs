// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{Sort, TermId, TermStore};
use num_bigint::BigInt;
use num_rational::BigRational;

use super::instantiate_body;
use super::occurrences::GroundOccurrences;

/// Enumerative instantiation fallback for triggerless quantifiers.
///
/// When E-matching auto-pattern extraction and CEGQI both fail (e.g., the quantifier
/// body uses only builtin operators over bound variables mixed with UF), this fallback
/// collects all ground terms of the right sort from the assertion set and instantiates
/// the quantifier body with every combination.
///
/// This is a simplified form of Z3's MBQI: instead of using the model to guide
/// instantiation, we enumerate all available ground terms.
///
/// # CALLER OBLIGATION (#auflia-disjunct-forall-false-unsat)
///
/// The doc here used to claim this is "sound because every instantiation of a
/// universally quantified formula is implied by the formula". Implied by the
/// FORMULA — yes. Implied by the PROBLEM — only when the problem ENTAILS the
/// formula. Every caller conjoins the returned instances into `ctx.assertions`
/// as top-level facts, so calling this on a `forall` that is merely a DISJUNCT
/// (`(or c (forall x. p x))`, a positive `=>` conclusion, an `ite` branch)
/// fabricates a constraint and can refute a satisfiable problem — measured on
/// six `AUFLIA/20170829-Rodin` benchmarks that answered `unsat` against a
/// declared and doubly-oracle-confirmed `sat`.
///
/// This function CANNOT check that itself: it sees one quantifier, not its
/// position. The caller MUST gate on
/// [`crate::ematching::collect_entailed_foralls`] /
/// [`crate::ematching::entailed_forall_set`] first — `setup_cegqi_for_unhandled`
/// does.
///
/// Reference: Z3 smt/smt_model_based_qi.cpp, CVC5 QuantifiersEngine::getTermForType
pub(crate) fn enumerative_instantiation(
    terms: &mut TermStore,
    assertions: &[TermId],
    quantifier: TermId,
    max_instantiations: usize,
    round: &mut GroundTermsRound,
) -> Vec<(Vec<TermId>, TermId)> {
    // A no_mbqi ("E-matching only") quantifier — the Hilbert-`choose` combined
    // axiom — must never be enumeratively (synthesis) instantiated: enumeration
    // builds the cartesian product of ground terms, which reaches the always-true
    // diagonal f2(x,x) and discharges the choose existential with no genuine
    // witness (unfaithful to Verus). Fail closed instead.
    if terms.is_no_mbqi(quantifier) {
        return vec![];
    }
    let (vars, body) = match terms.get(quantifier) {
        TermData::Forall(v, b, _) => (v.clone(), *b),
        TermData::Exists(v, b, _) => (v.clone(), *b),
        _ => return vec![],
    };

    if vars.is_empty() {
        return vec![];
    }

    // Collect ground terms by sort from the assertion set.
    // A ground term is any term that is not under a quantifier binding scope
    // and has no free bound variables.
    let ground_by_sort = round.by_sort(terms, assertions).clone();
    let needs_interpreted_arithmetic_basis = contains_fixed_interpreted_arithmetic(terms, body);

    // For each bound variable, find ground terms of the matching sort.
    let mut candidates_per_var: Vec<Vec<TermId>> = Vec::with_capacity(vars.len());
    for (_name, sort) in &vars {
        let mut candidates = ground_by_sort.get(sort).cloned().unwrap_or_default();
        // Fixed arithmetic conversions and integer division operations have
        // semantic discontinuities that a ground-term-only seed can miss. For
        // example, `forall x:Real. to_int(x) = 0` contains no ground Real term,
        // while `forall x:Int. rem(x, 2) = 0` exposes only the non-refuting
        // points 0 and 2. Add a small, deterministic arithmetic basis exactly
        // for formulas containing those interpreted heads. Every generated
        // instance is still a direct consequence of the entailed universal;
        // in proof mode the caller derives it with `forall_inst` and the strict
        // checker independently evaluates the ground operation.
        if needs_interpreted_arithmetic_basis {
            let mut add = |candidate: TermId| {
                if !candidates.contains(&candidate) {
                    candidates.push(candidate);
                }
            };
            match sort {
                Sort::Int => {
                    add(terms.mk_int(BigInt::from(0)));
                    add(terms.mk_int(BigInt::from(1)));
                    add(terms.mk_int(BigInt::from(-1)));
                }
                Sort::Real => {
                    add(terms.mk_rational(BigRational::from_integer(BigInt::from(0))));
                    add(terms.mk_rational(BigRational::from_integer(BigInt::from(1))));
                    add(terms.mk_rational(BigRational::from_integer(BigInt::from(-1))));
                    add(terms.mk_rational(BigRational::new(BigInt::from(1), BigInt::from(2))));
                    add(terms.mk_rational(BigRational::new(BigInt::from(-1), BigInt::from(2))));
                }
                _ => {}
            }
        }
        if candidates.is_empty() {
            // No ground terms of this sort — can't instantiate this quantifier.
            return vec![];
        }
        candidates_per_var.push(candidates);
    }

    // Generate cartesian product of bindings, up to max_instantiations.
    let var_names: Vec<String> = vars.iter().map(|(n, _)| n.clone()).collect();
    let mut instantiations = Vec::new();
    let mut indices: Vec<usize> = vec![0; vars.len()];

    loop {
        if instantiations.len() >= max_instantiations {
            break;
        }

        // Build binding from current indices
        let binding: Vec<TermId> = indices
            .iter()
            .enumerate()
            .map(|(var_idx, &term_idx)| candidates_per_var[var_idx][term_idx])
            .collect();

        let inst = instantiate_body(terms, body, &var_names, &binding);
        instantiations.push((binding, inst));

        // Advance to next combination (rightmost index increments first)
        let mut carry = true;
        for i in (0..vars.len()).rev() {
            if carry {
                indices[i] += 1;
                if indices[i] < candidates_per_var[i].len() {
                    carry = false;
                } else {
                    indices[i] = 0;
                }
            }
        }
        if carry {
            break; // All combinations exhausted
        }
    }

    instantiations
}

/// Whether `root` contains a fixed-semantics arithmetic operation whose useful
/// counterexample may lie outside the input's existing ground-term set.
///
/// User declarations that reuse `div`/`mod`/`rem` are assigned a private core
/// identity by the frontend, so only the actual interpreted head reaches the
/// exact-name cases below. The explicit shadow flags cover the two conversion
/// names that legacy contexts can redefine without private remapping.
pub(crate) fn contains_fixed_interpreted_arithmetic(terms: &TermStore, root: TermId) -> bool {
    let mut seen: HashSet<TermId> = HashSet::default();
    let mut stack = vec![root];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        match terms.get(term) {
            TermData::App(symbol, arguments) => {
                let fixed = match symbol.name() {
                    "to_real" => !terms.to_real_is_shadowed(),
                    "is_int" => !terms.is_int_is_shadowed(),
                    "to_int" | "div" | "mod" | "rem" => true,
                    _ => false,
                };
                if fixed {
                    return true;
                }
                stack.extend(arguments.iter().copied());
            }
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(condition, then_term, else_term) => {
                stack.push(*condition);
                stack.push(*then_term);
                stack.push(*else_term);
            }
            TermData::Let(bindings, body) => {
                stack.extend(bindings.iter().map(|(_, value)| *value));
                stack.push(*body);
            }
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
            TermData::Const(_) | TermData::Var(..) => {}
            _ => {}
        }
    }
    false
}

/// Collect ground terms from assertions grouped by their sort.
///
/// Walks the assertion DAG, collecting:
/// - Constants (Int, Real, etc.)
/// - Declared variables (constants in SMT-LIB terms)
/// - Function applications that are fully ground
///
/// An asserted occurrence is ground when none of its variables are bound by
/// its enclosing quantifiers. Free subterms inside a quantifier still count;
/// constructing an unasserted quantifier cannot suppress a free occurrence.
/// Public for MBQI (#5971).
pub(crate) fn collect_ground_terms_by_sort(
    terms: &TermStore,
    assertions: &[TermId],
) -> HashMap<Sort, Vec<TermId>> {
    let mut occurrences = GroundOccurrences::default();
    occurrences.visit_assertions(terms, assertions);
    let mut result: HashMap<Sort, Vec<TermId>> = HashMap::default();
    for &id in &occurrences.ground_ids {
        let term = TermId(id);
        if matches!(
            terms.get(term),
            TermData::Const(_) | TermData::Var(_, _) | TermData::App(_, _)
        ) {
            let sort = terms.sort(term);
            if !matches!(sort, Sort::Bool) {
                result.entry(sort.clone()).or_default().push(term);
            }
        }
    }

    // Deduplicate within each sort
    for terms_vec in result.values_mut() {
        terms_vec.sort_unstable_by_key(|t| t.0);
        terms_vec.dedup();
    }

    result
}

/// The ground terms of one enumerative instantiation round's seed, shared
/// across the round's quantifiers.
///
/// A round instantiates every quantifier over the same seed assertion
/// snapshot (#7883), so every quantifier reads the same map; computing it
/// once per round, not once per quantifier, keeps a round from costing
/// (quantifiers x asserted DAG). The map depends only on the seed's roots and
/// the immutable hash-consed terms below them, so a cached map is exactly the
/// one a fresh [`collect_ground_terms_by_sort`] would build. A call with a
/// different seed, or after the store shrank (compaction renumbers terms),
/// recomputes.
#[derive(Default)]
pub(crate) struct GroundTermsRound {
    seed: Vec<TermId>,
    store_len: usize,
    by_sort: Option<HashMap<Sort, Vec<TermId>>>,
}

impl GroundTermsRound {
    /// The ground terms of `assertions`, by sort.
    pub(crate) fn by_sort(
        &mut self,
        terms: &TermStore,
        assertions: &[TermId],
    ) -> &HashMap<Sort, Vec<TermId>> {
        let stale = self.seed.as_slice() != assertions || terms.len() < self.store_len;
        if stale || self.by_sort.is_none() {
            self.seed = assertions.to_vec();
            self.by_sort = None;
        }
        self.store_len = terms.len();
        self.by_sort
            .get_or_insert_with(|| collect_ground_terms_by_sort(terms, assertions))
    }
}

/// Check if a term contains any quantifier-bound variable.
pub(super) fn term_contains_bound_var(
    terms: &TermStore,
    term: TermId,
    bound_var_ids: &HashSet<u32>,
) -> bool {
    match terms.get(term) {
        TermData::Var(_, _) => bound_var_ids.contains(&term.0),
        TermData::Const(_) => false,
        TermData::App(_, args) => args
            .iter()
            .any(|&arg| term_contains_bound_var(terms, arg, bound_var_ids)),
        TermData::Not(inner) => term_contains_bound_var(terms, *inner, bound_var_ids),
        TermData::Ite(c, t, e) => {
            term_contains_bound_var(terms, *c, bound_var_ids)
                || term_contains_bound_var(terms, *t, bound_var_ids)
                || term_contains_bound_var(terms, *e, bound_var_ids)
        }
        TermData::Let(bindings, body) => {
            bindings
                .iter()
                .any(|(_, val)| term_contains_bound_var(terms, *val, bound_var_ids))
                || term_contains_bound_var(terms, *body, bound_var_ids)
        }
        TermData::Forall(..) | TermData::Exists(..) => true, // conservative: assume bound vars inside
        // Future TermData variants: conservatively assume bound vars present.
        _ => true,
    }
}

/// #bool-ground-inst: collect the ground Bool-sorted terms that occur as an
/// ARGUMENT of an UNINTERPRETED function application anywhere in `assertions`.
///
/// These are exactly the terms the two-point Bool finite-domain expansion
/// loses contact with: an opaque Bool term `c` buried in a UF argument
/// position never becomes a SAT atom, so EUF never merges it with the
/// true/false class and `f(c)` floats free of the expanded `f(true)`/`f(false)`
/// instances (#bool-arg-congruence). The finite-domain expander instantiates
/// Bool binders at these terms IN ADDITION to `true`/`false` — an
/// equivalence-preserving augmentation (any ground Bool term denotes `true` or
/// `false`), see `skolemize::finite_domain`.
///
/// Bool literals are excluded (already covered by the base domain), as is any
/// argument occurrence containing an in-scope bound variable (same discipline as
/// [`collect_ground_terms_by_sort`]). Result is sorted/deduped for
/// determinism.
pub(crate) fn collect_bool_uf_arg_terms(terms: &TermStore, assertions: &[TermId]) -> Vec<TermId> {
    let mut occurrences = GroundOccurrences::default();
    occurrences.visit_assertions(terms, assertions);
    let mut out: Vec<TermId> = occurrences.bool_uf_args.into_iter().map(TermId).collect();
    out.sort_unstable_by_key(|t| t.0);
    out
}
