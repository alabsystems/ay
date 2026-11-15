//! #entailed-bound-expansion: SOLVE-FREE derivation of integer constants the
//! problem's quantifier-free consequences ENTAIL.
//!
//! Takes `&TermStore` — NOT `&mut` — so it is STRUCTURALLY INCAPABLE of minting a
//! term. That is the whole point: a nested Executor solve here perturbs the main
//! solve badly (measured: the ext_eq push/pop SAT check 4.3s -> 33.7s, the tseitin
//! fixture to a timeout), and a model value is not an entailment anyway (models
//! report `Unknown` for a UF application like `(seq_len vec)`, and pinning it to a
//! fresh Int constant returned a WRONG value).
//!
//! Three stages:
//!   1. Collect the quantifier-free formulas in top-level CONJUNCTIVE position,
//!      modulo top-level unit facts (positive `and`; negated `or`; double
//!      negation; a positive `=>` whose antecedent is an asserted unit — modus
//!      ponens; a positive `or` all but one of whose disjuncts a unit falsifies —
//!      unit resolution).
//!   2. Union-find over the ground Int equalities among them (reflexive/symmetric/
//!      transitive closure of asserted equalities).
//!   3. Constant-fold interpreted +/-/* to a fixpoint. If a=1 and b=0 are in the
//!      premise set then a+b=1 is derived. Bails out (empty map) on any literal
//!      contradiction, and never guesses.
//!
//! ── SOUNDNESS BOUNDARY (read before touching either this or the caller's gate) ──
//! This deriver is NOT self-sufficient, and its output is NOT guaranteed to be a
//! set of entailed facts. It walks `ctx.assertions` AS THEY STAND POST-E-MATCHING,
//! and that set contains E-MATCHED INSTANCES of quantifiers. An instance of a
//! `forall` sitting in a DISJUNCTIVE obligation is NOT a consequence of the
//! problem, so if such an instance is a ground equality it can seed a class and
//! make this function emit a constant the problem does NOT entail. Adversarial
//! review measured exactly that: a `(or r (forall j. f(j)=9))` fed the map
//! `f(0)=9, n=9` for a problem that is SAT.
//!
//! What keeps the overall pass sound is the CALLER'S GATE, not this walk: the
//! result is used to rewrite the problem ONLY when
//! `snapshot_has_nonconjunctive_forall(original_assertions)` is false — i.e. only
//! when EVERY original `forall` is in a (unit-aware) conjunctive position, so
//! every instance of it IS a consequence (universal instantiation). Under that
//! condition, and only then, stages 1–3 over the premise set are entailment-
//! preserving and `val(t)=c` genuinely means the problem entails `t=c`.
//!
//! DO NOT drop that gate on the belief that this function only emits consequences.
//! It does not. Removing the gate reintroduces a false UNSAT.
//
// Derives a map `TermId -> BigInt` of ground Int terms, using ONLY unit
// propagation over top-level Bool units, a union-find over ground equalities in
// conjunctive position, and constant folding of interpreted +/-/*. NO nested
// solve, NO model reads. Sound to USE only behind the caller's non-conjunctive-
// forall gate (see the soundness boundary note above).

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{Symbol, TermData, TermId, TermStore};
use num_bigint::BigInt;

/// A top-level atom is a UNIT FACT only when it has no Boolean structure and no
/// quantifier — mirrors `result_mapping::is_unit_atom`.
fn is_unit_atom(terms: &TermStore, t: TermId) -> bool {
    match terms.get(t) {
        TermData::Forall(..) | TermData::Exists(..) | TermData::Not(_) | TermData::Ite(..) => false,
        TermData::App(Symbol::Named(n), _) => {
            !matches!(n.as_str(), "and" | "or" | "=>" | "xor" | "ite" | "not")
        }
        _ => true,
    }
}

fn unit_value(units: &HashMap<TermId, bool>, t: TermId, terms: &TermStore) -> Option<bool> {
    if let Some(&v) = units.get(&t) {
        return Some(v);
    }
    if let TermData::Const(ay_core::Constant::Bool(b)) = terms.get(t) {
        return Some(*b);
    }
    if let TermData::Not(inner) = terms.get(t) {
        return unit_value(units, *inner, terms).map(|v| !v);
    }
    None
}

/// Collect the quantifier-free formulas that are TOP-LEVEL CONSEQUENCES of
/// `assertions`, modulo top-level unit facts.
///
/// Identical descent discipline to
/// `result_mapping::forall_ids_in_conjunctive_position` (which decides where a
/// `forall` is a genuine conjunct): positive `and`, negative `or`, double
/// negation, and — modulo units — the consequent of a positive `=>` whose
/// antecedent is an asserted unit. Everything else stops the descent.
///
/// Anything returned here is TRUE IN EVERY MODEL of the problem.
pub(super) fn collect_conjunctive_ground_facts(
    terms: &TermStore,
    assertions: &[TermId],
) -> Vec<TermId> {
    let mut units: HashMap<TermId, bool> = HashMap::default();
    for &a in assertions {
        match terms.get(a) {
            TermData::Not(inner) => {
                let inner = *inner;
                if is_unit_atom(terms, inner) {
                    units.insert(inner, false);
                }
            }
            _ => {
                if is_unit_atom(terms, a) {
                    units.insert(a, true);
                }
            }
        }
    }

    let mut out: Vec<TermId> = Vec::new();
    let mut seen: HashSet<TermId> = HashSet::default();
    let mut stack: Vec<(TermId, bool)> = assertions.iter().map(|&a| (a, true)).collect();
    let mut visited: HashSet<(TermId, bool)> = HashSet::default();

    while let Some((term, positive)) = stack.pop() {
        if !visited.insert((term, positive)) {
            continue;
        }
        match terms.get(term).clone() {
            TermData::Forall(..) | TermData::Exists(..) => {
                // A quantifier is not a ground fact. (Its E-matched instances
                // arrive as separate top-level assertions.)
            }
            TermData::Not(inner) => match terms.get(inner).clone() {
                TermData::Not(inner2) => stack.push((inner2, positive)),
                TermData::Forall(..) | TermData::Exists(..) => {}
                TermData::App(Symbol::Named(ref n), ref args)
                    if matches!(n.as_str(), "and" | "or" | "=>") =>
                {
                    let _ = args;
                    stack.push((inner, !positive));
                }
                _ => {
                    // `(not atom)` in positive conjunctive position IS a fact.
                    if positive && seen.insert(term) {
                        out.push(term);
                    }
                }
            },
            TermData::App(Symbol::Named(name), args) => {
                if (name == "and" && positive) || (name == "or" && !positive) {
                    for &arg in &args {
                        stack.push((arg, positive));
                    }
                } else if name == "=>" && positive && args.len() == 2 {
                    let (a, b) = (args[0], args[1]);
                    let a_unit = unit_value(&units, a, terms);
                    let b_unit = unit_value(&units, b, terms);
                    if b_unit == Some(true) || a_unit == Some(false) {
                        // satisfied — contributes nothing
                    } else if a_unit == Some(true) {
                        stack.push((b, positive));
                    }
                } else if name == "or" && positive {
                    // Unit-resolve a positive `or` down to its single survivor.
                    if !args
                        .iter()
                        .any(|&x| unit_value(&units, x, terms) == Some(true))
                    {
                        let live: Vec<TermId> = args
                            .iter()
                            .copied()
                            .filter(|&x| unit_value(&units, x, terms) != Some(false))
                            .collect();
                        if live.len() == 1 {
                            stack.push((live[0], positive));
                        }
                    }
                } else if positive && seen.insert(term) {
                    // A plain atom (`=`, `<=`, a Bool UF app, a Bool const...).
                    out.push(term);
                }
            }
            _ => {
                if positive && seen.insert(term) {
                    out.push(term);
                }
            }
        }
    }
    out
}

/// Union-find over TermIds.
#[derive(Default)]
struct Uf {
    parent: HashMap<TermId, TermId>,
}
impl Uf {
    fn find(&mut self, t: TermId) -> TermId {
        let p = *self.parent.get(&t).unwrap_or(&t);
        if p == t {
            return t;
        }
        let root = self.find(p);
        self.parent.insert(t, root);
        root
    }
    fn union(&mut self, a: TermId, b: TermId) {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra != rb {
            // Deterministic: smaller index becomes root.
            if ra.index() < rb.index() {
                self.parent.insert(rb, ra);
            } else {
                self.parent.insert(ra, rb);
            }
        }
    }
}

fn is_int_sorted(terms: &TermStore, t: TermId) -> bool {
    matches!(terms.sort(t), ay_core::Sort::Int)
}

/// Collect every ground Int subterm of `t` (no bound vars anywhere below).
fn collect_int_subterms(
    terms: &TermStore,
    t: TermId,
    out: &mut Vec<TermId>,
    seen: &mut HashSet<TermId>,
) {
    if !seen.insert(t) {
        return;
    }
    match terms.get(t) {
        TermData::App(_, args) => {
            let args = args.clone();
            for a in args {
                collect_int_subterms(terms, a, out, seen);
            }
        }
        TermData::Not(i) => {
            let i = *i;
            collect_int_subterms(terms, i, out, seen);
        }
        TermData::Ite(c, a, b) => {
            let (c, a, b) = (*c, *a, *b);
            collect_int_subterms(terms, c, out, seen);
            collect_int_subterms(terms, a, out, seen);
            collect_int_subterms(terms, b, out, seen);
        }
        // Do NOT descend into quantifier bodies: those contain bound vars.
        TermData::Forall(..) | TermData::Exists(..) => return,
        _ => {}
    }
    if is_int_sorted(terms, t) {
        out.push(t);
    }
}

/// A top-level conjunctive fact is GROUND exactly when it contains no
/// quantifier: `TermData::Var` is ALSO how a `declare-const` free constant is
/// represented, and the only way a bound occurrence can be reached is through a
/// `Forall`/`Exists` node (which we refuse to enter). So "quantifier-free" is
/// precisely "every `Var` below is a free constant".
fn is_ground(terms: &TermStore, t: TermId) -> bool {
    !crate::ematching::contains_quantifier(terms, t)
}

/// Every entailed constant the finite-domain expander can read: the Int
/// consequences of [`derive_entailed_int_consts`] together with the narrow
/// unsigned-BV ones of [`derive_entailed_bv_consts`].
///
/// One table because both flow through the SAME soundness gate in the caller,
/// and because the expander reads bounds of both sorts. Keys are `TermId`s and
/// an Int term is never a BV term, so the two halves cannot collide; each
/// reader is sort-guarded regardless.
pub(super) fn derive_entailed_consts(
    terms: &TermStore,
    assertions: &[TermId],
) -> HashMap<TermId, BigInt> {
    let mut consts = derive_entailed_int_consts(terms, assertions);
    consts.extend(derive_entailed_bv_consts(terms, assertions));
    consts
}

/// Unsigned value of a BV literal, for widths this expander can enumerate.
fn bv_literal_value(terms: &TermStore, t: TermId) -> Option<BigInt> {
    match terms.get(t) {
        TermData::Const(ay_core::Constant::BitVec { value, width }) if *width <= 64 => {
            Some(value.clone())
        }
        _ => None,
    }
}

fn is_narrow_bv_sorted(terms: &TermStore, t: TermId) -> bool {
    matches!(terms.sort(t), ay_core::Sort::BitVec(bv) if bv.width <= 64)
}

/// Collect every ground narrow-BV subterm of `t` (no bound vars below).
fn collect_bv_subterms(
    terms: &TermStore,
    t: TermId,
    out: &mut Vec<TermId>,
    seen: &mut HashSet<TermId>,
) {
    if !seen.insert(t) {
        return;
    }
    match terms.get(t) {
        TermData::App(_, args) => {
            let args = args.clone();
            for a in args {
                collect_bv_subterms(terms, a, out, seen);
            }
        }
        TermData::Not(i) => {
            let i = *i;
            collect_bv_subterms(terms, i, out, seen);
        }
        TermData::Ite(c, a, b) => {
            let (c, a, b) = (*c, *a, *b);
            collect_bv_subterms(terms, c, out, seen);
            collect_bv_subterms(terms, a, out, seen);
            collect_bv_subterms(terms, b, out, seen);
        }
        // Never descend into a binder: everything below may be bound.
        TermData::Forall(..) | TermData::Exists(..) => return,
        _ => {}
    }
    if is_narrow_bv_sorted(terms, t) {
        out.push(t);
    }
}

/// SOLVE-FREE entailed-constant deriver for narrow unsigned BIT-VECTORS.
///
/// The bit-vector twin of [`derive_entailed_int_consts`], and deliberately the
/// weaker half of it: union-find over asserted ground BV equalities, seeded
/// from BV literals, with NO arithmetic folding. A bound like
/// `(fld_len ay_qcex_0)` is pinned by an asserted equality chain, not by
/// computing on it, and every fold rule would need its own modular-wraparound
/// argument to stay sound at the width. Nothing is derived that is not simply
/// equal, through asserted ground equalities, to a literal.
///
/// Values are UNSIGNED, matching how the finite-domain expander reads a BV
/// bound. Widths above 64 are skipped: that expander refuses them anyway.
///
/// Like its Int sibling this deriver is NOT itself the soundness argument — it
/// walks post-E-matching assertions, so an instance of a `forall` in a
/// DISJUNCTIVE position is not a consequence. The caller's
/// non-conjunctive-forall gate is what makes acting on the result sound, and
/// these constants flow through exactly that same gate.
pub(super) fn derive_entailed_bv_consts(
    terms: &TermStore,
    assertions: &[TermId],
) -> HashMap<TermId, BigInt> {
    let facts = collect_conjunctive_ground_facts(terms, assertions);

    let mut uf = Uf::default();
    let mut all_bv: Vec<TermId> = Vec::new();
    let mut seen: HashSet<TermId> = HashSet::default();
    for &f in &facts {
        if !is_ground(terms, f) {
            continue;
        }
        collect_bv_subterms(terms, f, &mut all_bv, &mut seen);
        if let TermData::App(Symbol::Named(n), args) = terms.get(f).clone() {
            if n == "=" && args.len() == 2 && is_narrow_bv_sorted(terms, args[0]) {
                uf.union(args[0], args[1]);
            }
        }
    }

    let mut val: HashMap<TermId, BigInt> = HashMap::default();
    let mut inconsistent = false;
    for &t in &all_bv {
        if let Some(c) = bv_literal_value(terms, t) {
            let r = uf.find(t);
            match val.get(&r) {
                Some(prev) if *prev != c => inconsistent = true,
                _ => {
                    val.insert(r, c);
                }
            }
        }
    }
    if inconsistent {
        // Contradictory premises: derive nothing rather than "anything follows".
        return HashMap::default();
    }

    let mut out: HashMap<TermId, BigInt> = HashMap::default();
    for &t in &all_bv {
        if bv_literal_value(terms, t).is_some() {
            continue;
        }
        if let Some(c) = val.get(&uf.find(t)) {
            out.insert(t, c.clone());
        }
    }
    out
}

/// SOLVE-FREE entailed-constant deriver.
///
/// Returns `term -> constant` for every ground Int term the CONJUNCTIVE-position
/// ground facts of `assertions` pin to a unique integer constant.
pub(super) fn derive_entailed_int_consts(
    terms: &TermStore,
    assertions: &[TermId],
) -> HashMap<TermId, BigInt> {
    let facts = collect_conjunctive_ground_facts(terms, assertions);

    // 1. Union-find over asserted ground Int EQUALITIES.
    let mut uf = Uf::default();
    let mut all_int: Vec<TermId> = Vec::new();
    let mut seen: HashSet<TermId> = HashSet::default();
    for &f in &facts {
        if !is_ground(terms, f) {
            continue;
        }
        collect_int_subterms(terms, f, &mut all_int, &mut seen);
        if let TermData::App(Symbol::Named(n), args) = terms.get(f).clone() {
            if n == "=" && args.len() == 2 && is_int_sorted(terms, args[0]) {
                uf.union(args[0], args[1]);
            }
        }
    }

    // 2. Seed class values from integer literals, then fold to fixpoint.
    let mut val: HashMap<TermId, BigInt> = HashMap::default(); // keyed by CLASS ROOT
    let mut inconsistent = false;
    for &t in &all_int {
        if let Some(c) = terms.extract_integer_constant(t) {
            let r = uf.find(t);
            match val.get(&r) {
                Some(prev) if *prev != c => inconsistent = true,
                _ => {
                    val.insert(r, c);
                }
            }
        }
    }
    if inconsistent {
        // Premises are already contradictory — derive nothing rather than
        // "anything follows" (keeps the rewrite honest).
        return HashMap::default();
    }

    let mut changed = true;
    let mut rounds = 0;
    while changed && rounds < 64 {
        changed = false;
        rounds += 1;
        for &t in &all_int {
            let r = uf.find(t);
            if val.contains_key(&r) {
                continue;
            }
            let TermData::App(Symbol::Named(op), args) = terms.get(t).clone() else {
                continue;
            };
            let arg_vals: Option<Vec<BigInt>> = args
                .iter()
                .map(|&a| {
                    let ra = uf.find(a);
                    val.get(&ra).cloned()
                })
                .collect();
            let Some(av) = arg_vals else { continue };
            let computed = match (op.as_str(), av.len()) {
                ("+", _) if !av.is_empty() => Some(av.into_iter().sum::<BigInt>()),
                ("-", 1) => Some(-av[0].clone()),
                ("-", _) => {
                    let mut it = av.into_iter();
                    let first = it.next().unwrap();
                    Some(it.fold(first, |acc, x| acc - x))
                }
                ("*", _) if !av.is_empty() => {
                    Some(av.into_iter().fold(BigInt::from(1), |acc, x| acc * x))
                }
                _ => None,
            };
            if let Some(c) = computed {
                match val.get(&r) {
                    Some(prev) if *prev != c => {
                        return HashMap::default(); // contradiction
                    }
                    Some(_) => {}
                    None => {
                        val.insert(r, c);
                        changed = true;
                    }
                }
            }
        }
    }

    // 3. Project class values back onto every member term.
    let mut out: HashMap<TermId, BigInt> = HashMap::default();
    for &t in &all_int {
        let r = uf.find(t);
        if let Some(c) = val.get(&r) {
            out.insert(t, c.clone());
        }
    }
    out
}

#[cfg(test)]
mod bv_tests {
    use super::*;
    use ay_core::Sort;

    /// The shape the finite-domain expander actually meets: a guard bound that
    /// is a SELECTOR APPLICATION pinned to a literal by an asserted ground
    /// equality, not a literal written in the guard.
    #[test]
    fn an_asserted_equality_pins_a_selector_bound_to_its_literal() {
        let mut terms = TermStore::new();
        let rec = terms.mk_var("v", Sort::Uninterpreted("Vec".into()));
        let len = terms.mk_app(Symbol::named("fld_len"), vec![rec], Sort::bitvec(64));
        let sixty_five = terms.mk_bitvec(BigInt::from(65), 64);
        let fact = terms.mk_eq(len, sixty_five);

        let derived = derive_entailed_bv_consts(&terms, &[fact]);
        assert_eq!(derived.get(&len), Some(&BigInt::from(65)));
        // The literal itself is not re-recorded; only terms that need resolving.
        assert!(!derived.contains_key(&sixty_five));
    }

    /// Equality is transitive through the union-find, and a term with no
    /// literal anywhere in its class stays underived rather than guessed.
    #[test]
    fn a_class_without_a_literal_derives_nothing() {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", Sort::bitvec(64));
        let b = terms.mk_var("b", Sort::bitvec(64));
        let c = terms.mk_var("c", Sort::bitvec(64));
        let lit = terms.mk_bitvec(BigInt::from(7), 64);
        let ab = terms.mk_eq(a, b);
        let b_lit = terms.mk_eq(b, lit);
        let unrelated = terms.mk_eq(c, c);

        let derived = derive_entailed_bv_consts(&terms, &[ab, b_lit, unrelated]);
        assert_eq!(derived.get(&a), Some(&BigInt::from(7)));
        assert_eq!(derived.get(&b), Some(&BigInt::from(7)));
        assert_eq!(derived.get(&c), None);
    }

    /// Contradictory premises derive NOTHING rather than "anything follows".
    #[test]
    fn contradictory_literals_in_one_class_derive_nothing() {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", Sort::bitvec(64));
        let one = terms.mk_bitvec(BigInt::from(1), 64);
        let two = terms.mk_bitvec(BigInt::from(2), 64);
        let e1 = terms.mk_eq(a, one);
        let e2 = terms.mk_eq(a, two);
        assert!(derive_entailed_bv_consts(&terms, &[e1, e2]).is_empty());
    }

    /// A binder's body is never entered, so nothing below a quantifier can be
    /// mistaken for a ground consequence.
    #[test]
    fn a_bound_occurrence_is_never_derived() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::bitvec(64));
        let lit = terms.mk_bitvec(BigInt::from(3), 64);
        let inner = terms.mk_eq(x, lit);
        let quantified = terms.mk_forall(vec![("x".into(), Sort::bitvec(64))], inner);
        assert!(derive_entailed_bv_consts(&terms, &[quantified]).is_empty());
    }
}
