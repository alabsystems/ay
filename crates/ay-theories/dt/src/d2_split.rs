// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! D2: datatype splitting on demand (finite / all-nullary sorts).
//!
//! Stage D2 of the development design notes: at the
//! Nelson-Oppen fixpoint (the point the loop would otherwise accept a
//! candidate model), emit an exhaustiveness ("domain closure") clause
//!
//! ```text
//!   (= t C1) ∨ (= t C2) ∨ ... ∨ (= t Ck)
//! ```
//!
//! for each *split base* `t` — a term of an all-nullary (enum) datatype sort —
//! whose e-class is not committed to a constructor and whose candidate
//! assignment satisfies none of the equality atoms. The clause is fed to the
//! SAT core as a permanent clause via `TheoryResult::NeedLemmas` (the same
//! conduit as D0/D1, #6546), turning the constructor choice into an ordinary
//! SAT decision: splitting on demand (Barrett–Nieuwenhuis–Oliveras–Tinelli,
//! LPAR 2006), restricted to finite sorts, which is the BST lazy strategy's
//! terminating fragment. Recursive-sort splits are intentionally NOT emitted
//! (fail-open): an under-constrained recursive class either never matters for
//! the verdict or is caught by the always-on model gates, which degrade the
//! Sat to Unknown and the routing falls back to the eager lane.
//!
//! ## Soundness
//!
//! Every emitted clause is an *unconditional datatype tautology*: a value of
//! an all-nullary datatype sort with constructors `C1..Ck` IS one of the `Ck`
//! (SMT-LIB datatype exhaustiveness), so `t = C1 ∨ ... ∨ t = Ck` holds in
//! every model. Emission is therefore not assignment- or e-graph-dependent;
//! the e-graph/candidate state only SCHEDULES which tautology is materialized
//! (uncommitted + violated first). Structural validity is enforced at
//! registration, fail-closed per base: a base whose atom family does not
//! structurally re-derive as the complete `(= t Cj)` family over exactly the
//! declared constructors of `t`'s sort is REJECTED (never split on), so no
//! malformed clause can reach the SAT core. Sat verdicts still pass through
//! the always-on model gates; unsat stays conflict-derived.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Symbol, TermData, TermId, TermStore};
use ay_core::{Sort, TheoryLemma, TheoryLit};
use ay_euf::EufSolver;

/// Maximum split clauses emitted per fixpoint call. Each fixpoint
/// `NeedLemmas` costs one split-loop iteration, so a burst is batched.
const D2_MAX_SPLITS_PER_ROUND: usize = 64;

/// Total split budget per solver instance (fail-open past it: the model
/// gates and the eager fallback lane remain authoritative).
const D2_MAX_SPLITS_TOTAL: u64 = 20_000;

/// A validated enum split base: `atoms[j]` is the equality atom
/// `(= t ctor_j)` in declaration order, complete over `t`'s sort.
#[derive(Debug)]
struct SplitBase {
    t: TermId,
    atoms: Vec<TermId>,
}

/// Splitting-on-demand pass over finite (all-nullary) datatype sorts.
///
/// Construct once per solve, register datatypes via
/// [`register_datatype`](Self::register_datatype), then register executor
/// materialized split bases via [`register_base`](Self::register_base) and
/// call [`fixpoint_splits`](Self::fixpoint_splits) from the theory's
/// Nelson-Oppen fixpoint.
#[derive(Debug, Default)]
pub struct DtSplitOnDemand {
    /// Datatype name -> ordered constructor names (all-nullary sorts only).
    enum_ctors: HashMap<String, Vec<String>>,
    /// Constructor name -> datatype name (for the committed-class scan; all
    /// registered datatypes, not only enums).
    ctor_to_dt: HashMap<String, String>,
    /// Validated split bases in registration order (deterministic).
    bases: Vec<SplitBase>,
    /// Bases whose clause has been emitted (by index into `bases`).
    emitted: HashSet<usize>,
    /// Term-store scan frontier for the committed-class scan.
    scanned_len: usize,
    /// Constructor applications/constants: (term, ctor name index is not
    /// needed — presence alone commits a class).
    ctor_apps: Vec<TermId>,
    /// Total clauses emitted.
    emitted_total: u64,
    /// Bases rejected by registration-time structural validation.
    rejected_bases: u64,
}

impl DtSplitOnDemand {
    /// Create an empty pass (no datatypes/bases registered; pass is inert).
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a datatype and its ordered constructor names (internal,
    /// possibly instance-mangled names — the same names the term store
    /// uses). `all_nullary` marks enum sorts eligible for domain-closure
    /// splits; non-enum datatypes participate only in the committed scan.
    pub fn register_datatype(&mut self, dt_name: &str, constructors: &[String], all_nullary: bool) {
        for ctor in constructors {
            self.ctor_to_dt
                .entry(ctor.clone())
                .or_insert_with(|| dt_name.to_string());
        }
        if all_nullary {
            self.enum_ctors
                .entry(dt_name.to_string())
                .or_insert_with(|| constructors.to_vec());
        }
    }

    /// Register one split base: `t` with its equality-atom family `atoms`
    /// (`atoms[j]` must be `(= t Cj)` for the j-th constructor of `t`'s
    /// all-nullary datatype sort, complete and in declaration order).
    ///
    /// The family is STRUCTURALLY re-validated here against the term store
    /// and the registered constructor lists; an invalid family is rejected
    /// (fail-closed for that base — no clause will ever be emitted for it).
    pub fn register_base(&mut self, terms: &TermStore, t: TermId, atoms: &[TermId]) {
        let Some(dt_name) = Self::dt_sort_name(terms.sort(t)) else {
            self.rejected_bases += 1;
            return;
        };
        let Some(ctors) = self.enum_ctors.get(dt_name) else {
            self.rejected_bases += 1;
            return;
        };
        if ctors.len() != atoms.len() {
            self.rejected_bases += 1;
            tracing::warn!(
                base = t.0,
                "dt-d2: split base atom family incomplete; base rejected"
            );
            return;
        }
        for (atom, ctor) in atoms.iter().zip(ctors.iter()) {
            let TermData::App(Symbol::Named(eq), args) = terms.get(*atom) else {
                self.rejected_bases += 1;
                return;
            };
            if eq != "=" || args.len() != 2 {
                self.rejected_bases += 1;
                return;
            }
            // One side is t; the other is the j-th constructor CONSTANT of
            // t's sort (nullary constructors are Var terms, #1745).
            let other = if args[0] == t {
                args[1]
            } else if args[1] == t {
                args[0]
            } else {
                self.rejected_bases += 1;
                return;
            };
            let is_ctor_const = match terms.get(other) {
                TermData::Var(name, _) => name == ctor,
                _ => false,
            };
            if !is_ctor_const || Self::dt_sort_name(terms.sort(other)) != Some(dt_name) {
                self.rejected_bases += 1;
                tracing::warn!(
                    base = t.0,
                    ctor = %ctor,
                    "dt-d2: split base atom failed structural validation; base rejected"
                );
                return;
            }
        }
        self.bases.push(SplitBase {
            t,
            atoms: atoms.to_vec(),
        });
    }

    /// The datatype-instance name of a (possibly lowered) datatype sort.
    fn dt_sort_name(sort: &Sort) -> Option<&str> {
        match sort {
            Sort::Uninterpreted(n) => Some(n.as_str()),
            Sort::Datatype(dt) => Some(dt.name.as_str()),
            _ => None,
        }
    }

    /// True when the pass can never emit anything.
    #[must_use]
    pub fn is_inert(&self) -> bool {
        self.bases.is_empty() || self.emitted_total >= D2_MAX_SPLITS_TOTAL
    }

    /// Statistics: `(bases, emitted_total, rejected_bases)`.
    #[must_use]
    pub fn stats(&self) -> (usize, u64, u64) {
        (self.bases.len(), self.emitted_total, self.rejected_bases)
    }

    /// Extend the memoized constructor-term list (append-only store).
    fn scan_new_terms(&mut self, terms: &TermStore) {
        let len = terms.len();
        for raw in self.scanned_len..len {
            let tid = TermId(raw as u32);
            match terms.get(tid) {
                TermData::App(Symbol::Named(name), _) | TermData::Var(name, _)
                    if self.ctor_to_dt.contains_key(name) =>
                {
                    self.ctor_apps.push(tid);
                }
                _ => {}
            }
        }
        self.scanned_len = len;
    }

    /// Emit domain-closure split clauses for uncommitted, unsatisfied bases.
    ///
    /// `assignments` is the candidate Boolean assignment at the fixpoint: a
    /// base any of whose atoms is assigned TRUE is already committed by the
    /// candidate and is skipped (without consuming its one-shot emission).
    /// Deterministic: bases are visited in registration order.
    pub fn fixpoint_splits(
        &mut self,
        terms: &TermStore,
        euf: &mut EufSolver<'_>,
        assignments: &HashMap<TermId, bool>,
    ) -> Vec<TheoryLemma> {
        if self.is_inert() {
            return Vec::new();
        }
        self.scan_new_terms(terms);

        // Classes committed to a constructor (contain a constructor term).
        let mut committed: HashSet<u32> = HashSet::default();
        for &app in &self.ctor_apps {
            committed.insert(euf.enode_find_const(app.0));
        }

        let mut out: Vec<TheoryLemma> = Vec::new();
        for idx in 0..self.bases.len() {
            if out.len() >= D2_MAX_SPLITS_PER_ROUND {
                break;
            }
            if self.emitted.contains(&idx) {
                continue;
            }
            let base = &self.bases[idx];
            // Committed class: the e-graph already knows t's constructor —
            // no split needed NOW (skip without consuming the emission; a
            // later candidate may leave it uncommitted).
            if committed.contains(&euf.enode_find_const(base.t.0)) {
                continue;
            }
            // Candidate already satisfies one disjunct: clause not violated.
            if base.atoms.iter().any(|a| assignments.get(a) == Some(&true)) {
                continue;
            }
            let clause: Vec<TheoryLit> = base
                .atoms
                .iter()
                .map(|&a| TheoryLit::new(a, true))
                .collect();
            out.push(TheoryLemma::new(clause));
            self.emitted.insert(idx);
        }
        self.emitted_total += out.len() as u64;
        if self.emitted_total >= D2_MAX_SPLITS_TOTAL {
            tracing::warn!(
                total = self.emitted_total,
                "dt-d2: split budget exhausted; pass going inert (fail-open)"
            );
        }
        out
    }
}

/// Occurrence-driven **UNION relevance criterion** (combined-theory-engine
/// campaign, milestone M0b): the ground datatype-sorted terms a lazy DT
/// split/reconstruction pass must axiomatize on a given problem.
///
/// A ground DT-sorted term is *relevant* when it occurs in `assertions` as
///   1. the argument of a native tester `is-C`,
///   2. the argument of a native selector, **or**
///   3. an operand of a ground DT `=` / `distinct`.
///
/// The `=`/`distinct`-operand leg (3) is **load-bearing and non-negotiable**.
/// The pure tester/selector-argument criterion (legs 1+2, what the eager
/// occurrence scan enumerates) is *refutation-INCOMPLETE*: on the rusthorn
/// List-sum VC it misses `list_cons_1(self)` and `list_cons_1(self_final)`
/// (2 of z3's 7 needed terms), which appear only as reconstruction-equality
/// operands. A missed term is a term whose datatype semantics go
/// unconstrained above the depth-1 floor — i.e. a **wrong-SAT risk**. Leg (3)
/// recovers them; M0b verified the union then contains all 7 z3 terms and
/// converges in one round.
///
/// Only GROUND (quantifier-free) DT-sorted terms qualify — a split base or a
/// reconstruction subject must be ground. Bound variables are tracked
/// lexically (nested quantifiers extend the scope). Constructor applications
/// are NOT excluded here (they are committed values; the caller decides
/// whether to skip them — the reconstruction axiom is vacuous on a syntactic
/// constructor and the exhaustiveness/exclusivity clauses stay sound).
///
/// Deterministic: first-occurrence order over a pre-order walk of
/// `assertions`.
#[must_use]
pub fn occurrence_relevant_dt_terms(
    terms: &TermStore,
    assertions: &[TermId],
    dt_sort_names: &HashSet<String>,
    tester_names: &HashSet<String>,
    selector_names: &HashSet<String>,
) -> Vec<TermId> {
    let mut relevant: Vec<TermId> = Vec::new();
    let mut seen: HashSet<TermId> = HashSet::default();
    let mut bound: Vec<String> = Vec::new();
    for &root in assertions {
        collect_relevant(
            terms,
            root,
            &mut bound,
            dt_sort_names,
            tester_names,
            selector_names,
            &mut relevant,
            &mut seen,
        );
    }
    relevant
}

/// True when `sort` is one of the declared datatype sorts.
fn sort_is_dt(sort: &Sort, dt_sort_names: &HashSet<String>) -> bool {
    match sort {
        Sort::Uninterpreted(n) => dt_sort_names.contains(n),
        Sort::Datatype(dt) => dt_sort_names.contains(&dt.name),
        _ => false,
    }
}

/// True when the subtree of `t` references no lexically-bound variable in
/// `bound` (i.e. `t` is ground in the current scope). Nested quantifiers
/// extend the local scope.
fn term_is_ground(terms: &TermStore, t: TermId, bound: &[String]) -> bool {
    if bound.is_empty() {
        return true;
    }
    match terms.get(t) {
        TermData::Var(name, _) => !bound.iter().any(|b| b == name),
        TermData::Const(_) => true,
        TermData::Not(a) => term_is_ground(terms, *a, bound),
        TermData::Ite(c, th, el) => {
            term_is_ground(terms, *c, bound)
                && term_is_ground(terms, *th, bound)
                && term_is_ground(terms, *el, bound)
        }
        TermData::App(_, args) => args.iter().all(|&a| term_is_ground(terms, a, bound)),
        TermData::Let(binds, body) => {
            binds.iter().all(|(_, v)| term_is_ground(terms, *v, bound))
                && term_is_ground(terms, *body, bound)
        }
        TermData::Forall(vars, body, _) | TermData::Exists(vars, body, _) => {
            let mut inner: Vec<String> = bound.to_vec();
            inner.extend(vars.iter().map(|(n, _)| n.clone()));
            term_is_ground(terms, *body, &inner)
        }
        // Unknown future variant: assume ground (never flagged relevant unless
        // `collect_relevant` descends to it, which it does not).
        _ => true,
    }
}

/// Record a ground DT-sorted term as relevant (deduplicated).
fn note_relevant(
    terms: &TermStore,
    t: TermId,
    bound: &[String],
    dt_sort_names: &HashSet<String>,
    relevant: &mut Vec<TermId>,
    seen: &mut HashSet<TermId>,
) {
    if sort_is_dt(terms.sort(t), dt_sort_names) && term_is_ground(terms, t, bound) && seen.insert(t)
    {
        relevant.push(t);
    }
}

/// Pre-order walk collecting UNION-relevant ground DT terms.
#[allow(clippy::too_many_arguments)]
fn collect_relevant(
    terms: &TermStore,
    t: TermId,
    bound: &mut Vec<String>,
    dt_sort_names: &HashSet<String>,
    tester_names: &HashSet<String>,
    selector_names: &HashSet<String>,
    relevant: &mut Vec<TermId>,
    seen: &mut HashSet<TermId>,
) {
    match terms.get(t) {
        TermData::App(Symbol::Named(name), args) => {
            if args.len() == 1 && (tester_names.contains(name) || selector_names.contains(name)) {
                // Legs 1+2: tester / selector argument.
                note_relevant(terms, args[0], bound, dt_sort_names, relevant, seen);
            } else if (name == "=" || name == "distinct") && args.len() >= 2 {
                // Leg 3: ground DT `=` / `distinct` operands (load-bearing).
                for &operand in args {
                    note_relevant(terms, operand, bound, dt_sort_names, relevant, seen);
                }
            }
            let args = args.clone();
            for a in args {
                collect_relevant(
                    terms,
                    a,
                    bound,
                    dt_sort_names,
                    tester_names,
                    selector_names,
                    relevant,
                    seen,
                );
            }
        }
        TermData::App(_, args) => {
            let args = args.clone();
            for a in args {
                collect_relevant(
                    terms,
                    a,
                    bound,
                    dt_sort_names,
                    tester_names,
                    selector_names,
                    relevant,
                    seen,
                );
            }
        }
        TermData::Not(a) => {
            let a = *a;
            collect_relevant(
                terms,
                a,
                bound,
                dt_sort_names,
                tester_names,
                selector_names,
                relevant,
                seen,
            );
        }
        TermData::Ite(c, th, el) => {
            for a in [*c, *th, *el] {
                collect_relevant(
                    terms,
                    a,
                    bound,
                    dt_sort_names,
                    tester_names,
                    selector_names,
                    relevant,
                    seen,
                );
            }
        }
        TermData::Let(binds, body) => {
            let children: Vec<TermId> = binds
                .iter()
                .map(|(_, v)| *v)
                .chain(std::iter::once(*body))
                .collect();
            for a in children {
                collect_relevant(
                    terms,
                    a,
                    bound,
                    dt_sort_names,
                    tester_names,
                    selector_names,
                    relevant,
                    seen,
                );
            }
        }
        TermData::Forall(vars, body, _) | TermData::Exists(vars, body, _) => {
            let added = vars.len();
            let body = *body;
            for (n, _) in vars {
                bound.push(n.clone());
            }
            collect_relevant(
                terms,
                body,
                bound,
                dt_sort_names,
                tester_names,
                selector_names,
                relevant,
                seen,
            );
            bound.truncate(bound.len() - added);
        }
        TermData::Var(_, _) | TermData::Const(_) => {}
        // Unknown future variant: no descent (fail-open; the depth-1 floor and
        // the always-on model gates remain the backstop).
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::TheorySolver;

    fn enum_sort() -> Sort {
        Sort::Uninterpreted("enum".to_string())
    }
    fn tower_sort() -> Sort {
        Sort::Uninterpreted("tower".to_string())
    }

    fn setup() -> (
        TermStore,
        DtSplitOnDemand,
        TermId,
        TermId,
        TermId,
        Vec<TermId>,
    ) {
        let mut terms = TermStore::new();
        let mut pass = DtSplitOnDemand::new();
        pass.register_datatype("enum", &["A".to_string(), "B".to_string()], true);
        pass.register_datatype("tower", &["stack".to_string(), "empty".to_string()], false);
        let a = terms.mk_var("A", enum_sort());
        let b = terms.mk_var("B", enum_sort());
        let x = terms.mk_var("x", enum_sort());
        let eq_a = terms.mk_eq(x, a);
        let eq_b = terms.mk_eq(x, b);
        (terms, pass, x, a, b, vec![eq_a, eq_b])
    }

    /// An uncommitted enum base with no satisfied atom gets exactly its
    /// domain-closure clause, once.
    #[test]
    fn uncommitted_base_splits_once() {
        let (terms, mut pass, x, _a, _b, atoms) = setup();
        pass.register_base(&terms, x, &atoms);
        assert_eq!(pass.stats().0, 1, "base must validate");
        let mut euf = EufSolver::new(&terms);
        let _ = euf.check();
        let assignments: HashMap<TermId, bool> = HashMap::default();
        let lemmas = pass.fixpoint_splits(&terms, &mut euf, &assignments);
        assert_eq!(lemmas.len(), 1);
        let clause = &lemmas[0].clause;
        assert_eq!(clause.len(), 2);
        assert!(clause.iter().all(|l| l.value));
        assert!(clause.iter().all(|l| atoms.contains(&l.term)));
        // One-shot: second call emits nothing.
        let again = pass.fixpoint_splits(&terms, &mut euf, &assignments);
        assert!(again.is_empty());
    }

    /// A base whose class is committed (merged with a constructor constant)
    /// is skipped — and NOT consumed.
    #[test]
    fn committed_class_is_skipped_without_consuming() {
        let (mut terms, mut pass, x, a, _b, atoms) = setup();
        pass.register_base(&terms, x, &atoms);
        let eq = terms.mk_eq(x, a);
        let mut euf = EufSolver::new(&terms);
        euf.assert_literal(eq, true);
        let _ = euf.check();
        let assignments: HashMap<TermId, bool> = HashMap::default();
        assert!(pass
            .fixpoint_splits(&terms, &mut euf, &assignments)
            .is_empty());
        // Fresh e-graph without the merge: now it splits.
        let mut euf2 = EufSolver::new(&terms);
        let _ = euf2.check();
        assert_eq!(
            pass.fixpoint_splits(&terms, &mut euf2, &assignments).len(),
            1
        );
    }

    /// A base with a candidate-satisfied atom is skipped (clause not violated).
    #[test]
    fn satisfied_candidate_is_skipped() {
        let (terms, mut pass, x, _a, _b, atoms) = setup();
        pass.register_base(&terms, x, &atoms);
        let mut euf = EufSolver::new(&terms);
        let _ = euf.check();
        let mut assignments: HashMap<TermId, bool> = HashMap::default();
        assignments.insert(atoms[0], true);
        assert!(pass
            .fixpoint_splits(&terms, &mut euf, &assignments)
            .is_empty());
    }

    /// Structural validation rejects malformed families: wrong sort, wrong
    /// constant, incomplete family.
    #[test]
    fn malformed_bases_are_rejected() {
        let (mut terms, mut pass, x, a, _b, atoms) = setup();
        // Incomplete family.
        pass.register_base(&terms, x, &atoms[..1]);
        // Non-enum base sort.
        let t = terms.mk_var("t", tower_sort());
        let empty = terms.mk_var("empty", tower_sort());
        let stack_like = terms.mk_var("stacklike", tower_sort());
        let eq1 = terms.mk_eq(t, stack_like);
        let eq2 = terms.mk_eq(t, empty);
        pass.register_base(&terms, t, &[eq1, eq2]);
        // Wrong constant (y is not a constructor of enum).
        let y = terms.mk_var("y", enum_sort());
        let eq_y = terms.mk_eq(x, y);
        let eq_a = terms.mk_eq(x, a);
        pass.register_base(&terms, x, &[eq_a, eq_y]);
        assert_eq!(pass.stats().0, 0, "no malformed base may register");
        assert_eq!(pass.stats().2, 3, "all three must be rejected");
    }

    // ---- occurrence_relevant_dt_terms (M0b UNION relevance criterion) -------

    fn list_sort() -> Sort {
        Sort::Uninterpreted("List".to_string())
    }

    fn dt_names() -> HashSet<String> {
        let mut s = HashSet::default();
        s.insert("List".to_string());
        s
    }
    fn tester_names() -> HashSet<String> {
        let mut s = HashSet::default();
        s.insert("is-Cons".to_string());
        s.insert("is-Nil".to_string());
        s
    }
    fn selector_names() -> HashSet<String> {
        let mut s = HashSet::default();
        s.insert("list_cons_0".to_string());
        s.insert("list_cons_1".to_string());
        s
    }

    fn tester(terms: &mut TermStore, ctor: &str, arg: TermId) -> TermId {
        terms.mk_app(Symbol::named(format!("is-{ctor}")), [arg], Sort::Bool)
    }

    /// LOAD-BEARING M0b constraint: a reconstruction operand `list_cons_1(self)`
    /// that appears ONLY as an operand of a DT `=` (never as a tester/selector
    /// argument) is recovered ONLY by the `=`/`distinct` operand leg. The
    /// tester/selector-argument legs alone are refutation-INCOMPLETE.
    #[test]
    fn union_criterion_recovers_reconstruction_operand() {
        let mut terms = TermStore::new();
        let self_t = terms.mk_var("self", list_sort());
        let bridge = terms.mk_var("bridge", list_sort());
        // list_cons_1(self): a selector APP. Its ARG (self) is a selector-arg;
        // the app itself is flagged only if it is an =-operand.
        let lc1_self = terms.mk_app(Symbol::named("list_cons_1"), [self_t], list_sort());
        let is_cons_self = tester(&mut terms, "Cons", self_t);
        // (= (list_cons_1 self) bridge) — a bridge/reconstruction equality.
        let eq_bridge = terms.mk_eq(lc1_self, bridge);

        let (dt, tn, sn) = (dt_names(), tester_names(), selector_names());

        // With only the tester assertion, lc1(self) is never surfaced (self is,
        // via the tester arg).
        let tester_only = occurrence_relevant_dt_terms(&terms, &[is_cons_self], &dt, &tn, &sn);
        assert!(
            tester_only.contains(&self_t),
            "self must be relevant (tester arg)"
        );
        assert!(
            !tester_only.contains(&lc1_self),
            "lc1(self) is not a tester/selector ARG — must not appear without the = leg"
        );

        // UNION: adding the `=` atom recovers lc1(self) AND bridge via leg 3.
        let union = occurrence_relevant_dt_terms(&terms, &[is_cons_self, eq_bridge], &dt, &tn, &sn);
        assert!(union.contains(&self_t), "self still relevant");
        assert!(
            union.contains(&lc1_self),
            "lc1(self) MUST be recovered by the =-operand leg (M0b load-bearing)"
        );
        assert!(
            union.contains(&bridge),
            "the other DT = operand is relevant too"
        );
    }

    /// Selector-argument and tester-argument legs both fire; non-DT operands of
    /// a mixed `=` are ignored; duplicates are deduplicated.
    #[test]
    fn tester_and_selector_arg_legs() {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", list_sort());
        let int_x = terms.mk_var("x", Sort::Int);
        // selector on a: flags a
        let _lc1_a = terms.mk_app(Symbol::named("list_cons_1"), [a], list_sort());
        // tester on a: flags a again (dedup)
        let is_nil_a = tester(&mut terms, "Nil", a);
        // (= x 3)-style Int equality: no DT operands, ignored.
        let three = terms.mk_var("three", Sort::Int);
        let eq_int = terms.mk_eq(int_x, three);
        let lc1_a2 = terms.mk_app(Symbol::named("list_cons_1"), [a], list_sort());
        let (dt, tn, sn) = (dt_names(), tester_names(), selector_names());
        let rel = occurrence_relevant_dt_terms(&terms, &[is_nil_a, eq_int, lc1_a2], &dt, &tn, &sn);
        assert_eq!(rel, vec![a], "only the ground DT selector/tester arg, once");
    }

    /// Bound variables are excluded; a ground constant used inside a quantifier
    /// body is included.
    #[test]
    fn binders_exclude_bound_vars_keep_ground() {
        let mut terms = TermStore::new();
        let g = terms.mk_var("g", list_sort()); // ground constant
        let x = terms.mk_var("x", list_sort()); // will be bound
        let is_cons_x = tester(&mut terms, "Cons", x);
        let is_cons_g = tester(&mut terms, "Cons", g);
        let body = terms.mk_and(vec![is_cons_x, is_cons_g]);
        let forall = terms.mk_forall(vec![("x".to_string(), list_sort())], body);
        let (dt, tn, sn) = (dt_names(), tester_names(), selector_names());
        let rel = occurrence_relevant_dt_terms(&terms, &[forall], &dt, &tn, &sn);
        assert!(
            rel.contains(&g),
            "ground constant inside forall is relevant"
        );
        assert!(!rel.contains(&x), "the bound var must not be relevant");
    }
}
