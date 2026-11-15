// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! (#defn-fold-under-forall) Which quantified assertions the aggregate
//! definition fold may rewrite.
//!
//! `fold_ground_definitions_into_universals` replaces a defined Array or
//! Datatype variable by its definition inside a universal so that a binder
//! bound written over the variable, `(bvult i (fld_len v))`, collapses to a
//! literal `expand_finite_domains` can read. That is its only payoff. Its
//! cost is paid by every universal it rewrites: the rewritten term is no
//! longer an authored root, so `register_ematching_proof_record` accepts no
//! E-matching instance of it (neither a direct nor a normalized source),
//! consequence replay finds "no derivable recorded instance (0 records)", and
//! a computed UNSAT that must carry an authored-scope proof is withheld.
//!
//! It also owns the fold's CAPTURE side condition
//! ([`capture_free_definitions`]), which the certificate replay's source fold
//! applies too, so producer and replay fold exactly the same definitions.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{TermData, TermId, TermStore};

use super::term_mentions_any_var;
use crate::ematching::contains_quantifier;
use crate::preprocess::VariableSubstitution;

/// The comparisons a finite-domain bound is written with: the Int and
/// unsigned bit-vector guards `skolemize::finite_domain` reads, plus their
/// mirrored and signed spellings, so a bound in any orientation counts.
const BOUND_ORDER_OPS: [&str; 12] = [
    "<", "<=", ">", ">=", "bvult", "bvule", "bvugt", "bvuge", "bvslt", "bvsle", "bvsgt", "bvsge",
];

/// Whether a binder BOUND of `term` reads a variable in `defined`: an order
/// atom with one side exactly a variable some quantifier of `term` binds and
/// the other side mentioning a defined variable.
///
/// That is the shape the expander reads a bound from (`bounds_from_guard`,
/// `bounds_from_bv_guard`: the binder on one side, the bound on the other),
/// so it is where a fold can turn an unreadable bound into a literal. The
/// nested-Vec replay obligation's `(bvult c (fld_len (select d r)))` over the
/// defined `d` qualifies. A body read does not: `(= (select b i) (select a
/// i))` and `(<= (select b i) (select a i))` expose no bound whatever `b` is,
/// so folding `b := (store a 3 9)` or `b := (store ((as const ..) 0) 3 9)`
/// into them only cost the universal its E-matching provenance.
///
/// Measured on a35bb17fa (5d900fd2f introduced the fold, which rewrote every
/// quantified assertion): `cegqi_ce_strip_identity::{v10,v11,adv2}`, the
/// kill-switch read-over-write fixture, their constant-base twins and the
/// order-body twin answer `unknown` (z3 and the Sep-8 build: `unsat`), and
/// `deductive_checks_set_fold_posture`'s captured obligation (a set defined as
/// `(as const .. false)`, read only in bodies) answers `unknown` at its 180 s
/// wall. Under this gate every one of them decides `unsat` (the obligation in
/// ~40 s), every ay-chc counterexample-replay test that reaches the fold stays
/// green, and every fold whose bound reads a definition is kept. A weaker
/// gate -- any order atom under a binder mentioning a definition -- still
/// folds the order-body twin and leaves it `unknown`.
///
/// Over-approximate by design: a false positive only keeps a fold, which is
/// the pre-gate behaviour. Read-only and linear in the DAG plus one
/// occurrence walk per order atom.
pub(super) fn bound_reads(terms: &TermStore, term: TermId, defined: &HashSet<TermId>) -> bool {
    let mut binders: HashSet<&str> = HashSet::default();
    let mut order_atoms: Vec<(TermId, TermId)> = Vec::new();
    let mut pending = vec![term];
    let mut seen: HashSet<TermId> = HashSet::default();
    while let Some(t) = pending.pop() {
        if !seen.insert(t) {
            continue;
        }
        match terms.get(t) {
            TermData::App(sym, args) => {
                if let [lhs, rhs] = args.as_slice() {
                    if BOUND_ORDER_OPS.contains(&sym.name()) {
                        order_atoms.push((*lhs, *rhs));
                    }
                }
                pending.extend(args.iter().copied());
            }
            TermData::Not(inner) => pending.push(*inner),
            TermData::Ite(cond, then_term, else_term) => {
                pending.extend([*cond, *then_term, *else_term]);
            }
            TermData::Let(bindings, body) => {
                pending.extend(bindings.iter().map(|(_, value)| *value));
                pending.push(*body);
            }
            TermData::Forall(vars, body, _) | TermData::Exists(vars, body, _) => {
                binders.extend(vars.iter().map(|(name, _)| name.as_str()));
                pending.push(*body);
            }
            _ => {}
        }
    }
    let is_binder = |side: TermId| match terms.get(side) {
        TermData::Var(name, _) => binders.contains(name.as_str()),
        _ => false,
    };
    order_atoms.iter().any(|&(lhs, rhs)| {
        (is_binder(lhs) && term_mentions_any_var(terms, rhs, defined))
            || (is_binder(rhs) && term_mentions_any_var(terms, lhs, defined))
    })
}

/// `assertion` with the definitions [`admitted_definitions`] admits folded
/// in; `assertion` itself when it has no quantifier or must stay authored.
pub(super) fn fold(
    terms: &mut TermStore,
    assertion: TermId,
    definitions: &HashMap<TermId, TermId>,
    defined: &HashSet<TermId>,
) -> TermId {
    if !contains_quantifier(terms, assertion) {
        return assertion;
    }
    match admitted_definitions(terms, assertion, definitions, defined) {
        Some(admitted) => {
            VariableSubstitution::from_recorded_map(admitted).apply_to_term(terms, assertion)
        }
        None => assertion,
    }
}

/// The definitions the fold may apply to the quantified `term`, or `None`
/// when `term` must stay authored: only [`capture_free_definitions`], and only
/// while a binder bound still reads one of them ([`bound_reads`]). Refusing
/// every definition a bound reads leaves `term` authored, exactly as if no
/// such definition had been asserted. `defined` is the key set of
/// `definitions`, so the common no-bound case costs one walk.
fn admitted_definitions(
    terms: &TermStore,
    term: TermId,
    definitions: &HashMap<TermId, TermId>,
    defined: &HashSet<TermId>,
) -> Option<HashMap<TermId, TermId>> {
    if !bound_reads(terms, term, defined) {
        return None;
    }
    let admitted = capture_free_definitions(terms, term, definitions);
    if admitted.len() == definitions.len() {
        return Some(admitted);
    }
    let admitted_keys: HashSet<TermId> = admitted.keys().copied().collect();
    bound_reads(terms, term, &admitted_keys).then_some(admitted)
}

/// The definitions `v := t` of `definitions` that can be folded into `term`
/// without capture: those whose value `t` mentions no variable SPELLED like a
/// name `term` binds (#defn-fold-binder-capture).
///
/// `t` comes from outside `term`, so every variable it mentions is free there,
/// and folding it under a binder of the same spelling captures it. The fold
/// itself substitutes by identity, but everything that instantiates the
/// folded universal afterwards replaces a binder BY NAME: the finite-domain
/// expander (`subst_vars`, `is_bound_var`), E-matching and MBQI.
/// `subst_vars` renames an inner binder away from the free names of the
/// value it substitutes for this reason (`capture_avoiding_subst`); this is
/// the same side condition, and a refused definition simply stays unfolded,
/// which is always sound because its defining equality stays asserted.
///
/// The frontend mints each binder a name no declaration holds YET
/// (`mk_fresh_var` does not enter it into the symbol table), but a later
/// `declare-const` (in any `push` scope) can take that spelling for a
/// different variable, and an assertion or a `check-sat-assuming` literal can
/// then define an aggregate over it. Measured on ad60a0707 with `i_2`
/// declared after `(forall ((i Int)) (=> (and (<= 0 i) (< i (select lens
/// 0))) (= i (select w 0))))` (binder minted `i_2`), `lens := (store K 0 2)`
/// and `w := (store K 0 i_2)`: `sat` at every `--rigor` (z3: unsat), sealed by
/// the exact finite-expansion SAT grant; the `distinct` twin answered `unsat`
/// (z3: sat). The same capture happens when the binder is vacuous or the
/// fold erases the binder's own occurrences, since the foreign variable is
/// then the only one so spelled.
///
/// Every binder at any depth and every `let` name counts: each is a spelling
/// some instantiator or `let` expansion substitutes.
pub(in crate::executor::quantifier_loop) fn capture_free_definitions(
    terms: &TermStore,
    term: TermId,
    definitions: &HashMap<TermId, TermId>,
) -> HashMap<TermId, TermId> {
    let bound = bound_names(terms, term);
    definitions
        .iter()
        .filter(|&(_, &value)| bound.is_empty() || !mentions_a_name(terms, value, &bound))
        .map(|(&var, &value)| (var, value))
        .collect()
}

/// Every name `term` binds: quantifier binders at any depth and `let` names.
fn bound_names(terms: &TermStore, term: TermId) -> HashSet<String> {
    let mut names: HashSet<String> = HashSet::default();
    let mut seen: HashSet<TermId> = HashSet::default();
    let mut pending = vec![term];
    while let Some(t) = pending.pop() {
        if !seen.insert(t) {
            continue;
        }
        match terms.get(t) {
            TermData::Forall(vars, _, _) | TermData::Exists(vars, _, _) => {
                names.extend(vars.iter().map(|(name, _)| name.clone()));
            }
            TermData::Let(bindings, _) => {
                names.extend(bindings.iter().map(|(name, _)| name.clone()));
            }
            _ => {}
        }
        pending.extend(terms.children(t));
    }
    names
}

/// Whether `term` mentions a variable spelled like a name in `names`.
fn mentions_a_name(terms: &TermStore, term: TermId, names: &HashSet<String>) -> bool {
    let mut seen: HashSet<TermId> = HashSet::default();
    let mut pending = vec![term];
    while let Some(t) = pending.pop() {
        if !seen.insert(t) {
            continue;
        }
        if matches!(terms.get(t), TermData::Var(name, _) if names.contains(name)) {
            return true;
        }
        pending.extend(terms.children(t));
    }
    false
}

#[cfg(test)]
mod capture_tests;

#[cfg(test)]
mod tests {
    use ay_core::term::Symbol;
    use ay_core::Sort;
    use num_bigint::BigInt;

    use super::*;
    use crate::executor::Executor;

    fn int_array() -> Sort {
        Sort::array(Sort::Int, Sort::Int)
    }

    /// `(= b (store ((as const (Array Int Int)) 0) 3 9))`, `b`, `a`.
    fn store_definition(terms: &mut TermStore) -> (TermId, TermId, TermId) {
        let a = terms.mk_var("a", int_array());
        let b = terms.mk_var("b", int_array());
        let zero = terms.mk_int(BigInt::from(0));
        let three = terms.mk_int(BigInt::from(3));
        let nine = terms.mk_int(BigInt::from(9));
        let base = terms.mk_const_array(Sort::Int, zero);
        let value = terms.mk_store(base, three, nine);
        (terms.mk_eq(b, value), b, a)
    }

    /// `(forall ((i Int)) (or (= 3 i) (<= (select b i) (select a i))))`: the
    /// defined `b` is read only in the body.
    fn body_read_forall(terms: &mut TermStore, b: TermId, a: TermId) -> TermId {
        let i = terms.mk_var("i", Sort::Int);
        let three = terms.mk_int(BigInt::from(3));
        let guard = terms.mk_eq(three, i);
        let b_i = terms.mk_select(b, i);
        let a_i = terms.mk_select(a, i);
        let order_body = terms.mk_le(b_i, a_i);
        let body = terms.mk_or(vec![guard, order_body]);
        terms.mk_forall(vec![("i".to_string(), Sort::Int)], body)
    }

    /// `(forall ((j Int)) (or (< j 0) (<= (select b 3) j) (= (select a j) 0)))`:
    /// the upper bound of `j` is written over the defined `b`.
    fn bound_read_forall(terms: &mut TermStore, b: TermId, a: TermId) -> TermId {
        let j = terms.mk_var("j", Sort::Int);
        let zero = terms.mk_int(BigInt::from(0));
        let three = terms.mk_int(BigInt::from(3));
        let lower = terms.mk_lt(j, zero);
        let b_3 = terms.mk_select(b, three);
        let upper = terms.mk_le(b_3, j);
        let a_j = terms.mk_select(a, j);
        let cell = terms.mk_eq(a_j, zero);
        let body = terms.mk_or(vec![lower, upper, cell]);
        terms.mk_forall(vec![("j".to_string(), Sort::Int)], body)
    }

    #[test]
    fn only_a_binder_bound_over_a_definition_admits_the_fold() {
        let mut terms = TermStore::new();
        let (_, b, a) = store_definition(&mut terms);
        let defined_b: HashSet<TermId> = [b].into_iter().collect();
        let defined_a: HashSet<TermId> = [a].into_iter().collect();

        let body_read = body_read_forall(&mut terms, b, a);
        assert!(
            !bound_reads(&terms, body_read, &defined_b),
            "an order atom over body reads is not a bound"
        );
        let bound_read = bound_read_forall(&mut terms, b, a);
        assert!(bound_reads(&terms, bound_read, &defined_b));
        assert!(
            !bound_reads(&terms, bound_read, &defined_a),
            "`a` is read only in the body of the bounded universal"
        );

        // A comparison under the binder whose bare side is a FREE variable is
        // not a bound of that binder.
        let k = terms.mk_var("k", Sort::Int);
        let zero = terms.mk_int(BigInt::from(0));
        let b_0 = terms.mk_select(b, zero);
        let free_side = terms.mk_lt(k, b_0);
        let i = terms.mk_var("i", Sort::Int);
        let a_i = terms.mk_select(a, i);
        let one = terms.mk_int(BigInt::from(1));
        let cell = terms.mk_eq(a_i, one);
        let body = terms.mk_or(vec![free_side, cell]);
        let free = terms.mk_forall(vec![("i".to_string(), Sort::Int)], body);
        assert!(!bound_reads(&terms, free, &defined_b));
    }

    /// The nested-Vec obligation shape: the INNER binder's bit-vector bound
    /// reads the defined array through the outer binder.
    #[test]
    fn a_nested_bit_vector_bound_over_a_definition_admits_the_fold() {
        let mut terms = TermStore::new();
        let bv = Sort::bitvec(64);
        let d = terms.mk_var("d", Sort::array(bv.clone(), bv.clone()));
        let payload = terms.mk_var("payload", Sort::array(bv.clone(), bv.clone()));
        let r = terms.mk_var("r", bv.clone());
        let c = terms.mk_var("c", bv.clone());
        let d_r = terms.mk_select(d, r);
        let bound = terms.mk_app(Symbol::named("bvult"), vec![c, d_r], Sort::Bool);
        let out_of_range = terms.mk_not(bound);
        let seven = terms.mk_bitvec(BigInt::from(7), 64);
        let payload_c = terms.mk_select(payload, c);
        let cell = terms.mk_eq(payload_c, seven);
        let inner_body = terms.mk_or(vec![out_of_range, cell]);
        let inner = terms.mk_forall(vec![("c".to_string(), bv.clone())], inner_body);
        let outer = terms.mk_forall(vec![("r".to_string(), bv)], inner);

        let defined_d: HashSet<TermId> = [d].into_iter().collect();
        let defined_payload: HashSet<TermId> = [payload].into_iter().collect();
        assert!(bound_reads(&terms, outer, &defined_d));
        assert!(!bound_reads(&terms, outer, &defined_payload));
    }

    /// End to end through the fold: the body-read universal keeps its
    /// authored `TermId`; the bound-read one is rewritten and its bound no
    /// longer names `b`.
    #[test]
    fn the_fold_rewrites_only_universals_whose_bound_reads_a_definition() {
        let mut exec = Executor::new();
        let (definition, b, a) = store_definition(&mut exec.ctx.terms);
        let body_read = body_read_forall(&mut exec.ctx.terms, b, a);
        let bound_read = bound_read_forall(&mut exec.ctx.terms, b, a);
        exec.ctx.assertions = vec![definition, body_read, bound_read];

        exec.fold_ground_definitions_into_universals();

        assert_eq!(exec.ctx.assertions[0], definition);
        assert_eq!(
            exec.ctx.assertions[1], body_read,
            "a universal whose bounds read no definition must stay authored"
        );
        let folded = exec.ctx.assertions[2];
        let defined_b: HashSet<TermId> = [b].into_iter().collect();
        assert_ne!(folded, bound_read);
        assert!(!term_mentions_any_var(&exec.ctx.terms, folded, &defined_b));
    }
}
