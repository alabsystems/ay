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
