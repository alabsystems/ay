// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! TseitinCnf preprocessing pass (Z3's `tseitin-cnf` / `cnf` tactic).
//!
//! Converts a goal (a set of Boolean assertions, an implicit conjunction) into
//! **conjunctive normal form** — a conjunction of clauses, each a disjunction of
//! literals — via the classic *Tseitin encoding*: every non-trivial Boolean
//! subformula φ is given a fresh Boolean *definition variable* `t_φ`, the
//! biconditional `t_φ ↔ φ` is emitted as a small clause set, and the top-level
//! assertions are then expressed over those literals.
//!
//! # Soundness: EQUISATISFIABLE, not equivalent
//!
//! Tseitin introduces fresh auxiliary Boolean variables, so the CNF does NOT
//! have the same *models* as the input (the models differ on the new variables).
//! What it preserves is **satisfiability**:
//!
//! - every model `M` of the input extends (uniquely, by evaluating each gate) to
//!   a model of the CNF, and
//! - every model of the CNF, restricted to the input's variables, is a model of
//!   the input.
//!
//! Consequently `check-sat(cnf) == check-sat(input)` when the aux variables are
//! treated as free (existentially quantified) — exactly the soundness property a
//! single-goal goal-to-goal tactic must have. We deliberately do NOT claim
//! equivalence anywhere, and the aux variables are genuine fresh symbols
//! ([`TermStore::mk_fresh_var`]) that cannot collide with user declarations.
//!
//! # What is a "gate" vs an "atom"
//!
//! Only the Boolean *connectives* are decomposed into gates; everything else is
//! an opaque literal (an *atom*). The connectives handled are `not`, `and`,
//! `or`, `xor`, `=>`/`implies`, `=` between two Booleans (iff), a Boolean `ite`,
//! and a Boolean `distinct`. Anything else that is Boolean-sorted — a Boolean
//! variable/constant, a theory predicate such as `(> x 5)` or `(= a b)` over a
//! non-Boolean sort, an uninterpreted predicate `(p x)` — is an atom and becomes
//! a literal verbatim. (Treating an unrecognized Boolean compound as an atom is
//! always *sound*: it just leaves that compound un-clausified, never wrong.)
//!
//! # Top-level Plaisted–Greenbaum shortcut
//!
//! The top of the goal is already a conjunctive/positive context, so we avoid a
//! pointless top-level gate: a top-level `and` splits into its conjuncts (like
//! `elim-and`), and a top-level `or` becomes a single clause whose disjuncts are
//! the encoded literals. Every *nested* gate still uses the full biconditional
//! `t ↔ φ`, which is sound regardless of polarity.
//!
//! # Reference
//!
//! G. Tseitin, "On the complexity of derivation in propositional calculus"
//! (1968); Plaisted & Greenbaum, "A structure-preserving clause form
//! translation" (1986).

use super::PreprocessingPass;
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::{Constant, TermData};
use ay_core::{Sort, TermId, TermStore};

/// Z3's `tseitin-cnf` (a.k.a. `cnf`): rewrite the goal into an equisatisfiable
/// CNF with fresh auxiliary Boolean definition variables.
pub(crate) struct TseitinCnf;

impl TseitinCnf {
    /// Create a new `tseitin-cnf` pass.
    pub(crate) fn new() -> Self {
        TseitinCnf
    }
}

impl Default for TseitinCnf {
    fn default() -> Self {
        Self::new()
    }
}

impl PreprocessingPass for TseitinCnf {
    fn apply(&mut self, terms: &mut TermStore, assertions: &mut Vec<TermId>) -> bool {
        let mut enc = Encoder::new(terms);
        let mut top: Vec<TermId> = Vec::new();
        for &f in assertions.iter() {
            enc.clausify_assertion(f, &mut top);
        }
        // The final CNF is: all gate-definition clauses, then the top-level
        // clauses (unit literals / disjunctions) derived from the assertions.
        let mut result = std::mem::take(&mut enc.clauses);
        result.extend(top);

        // Honest progress reporting: only claim a change when the clausal goal
        // genuinely differs from the input (a goal already in this exact clausal
        // form is a fixpoint, so `repeat` and the solver shim see no progress).
        if result == *assertions {
            return false;
        }
        *assertions = result;
        true
    }
}

/// The Tseitin worker: owns the term store, a memo from each Boolean subformula
/// to the literal that represents it, and the accumulated gate-definition
/// clauses.
struct Encoder<'a> {
    terms: &'a mut TermStore,
    /// Memo: subformula → representative literal. A shared (DAG) subformula is
    /// thus encoded — and its defining clauses emitted — exactly once.
    cache: HashMap<TermId, TermId>,
    /// Accumulated gate-definition clauses (`t ↔ φ`), each a disjunction of
    /// literals.
    clauses: Vec<TermId>,
}

impl<'a> Encoder<'a> {
    fn new(terms: &'a mut TermStore) -> Self {
        Encoder {
            terms,
            cache: HashMap::default(),
            clauses: Vec::new(),
        }
    }

    fn is_bool(&self, t: TermId) -> bool {
        self.terms.sort(t) == &Sort::Bool
    }

    /// Push a clause into the definition set, dropping trivially-true (tautology)
    /// clauses. A `false` clause is kept — it correctly forces UNSAT.
    fn push_clause(&mut self, clause: TermId) {
        if clause != self.terms.true_term() {
            self.clauses.push(clause);
        }
    }

    /// Add a top-level clause, dropping a trivially-true one. (A top-level
    /// `false` is kept: the goal is genuinely UNSAT.)
    fn push_top(&mut self, clause: TermId, top: &mut Vec<TermId>) {
        if clause != self.terms.true_term() {
            top.push(clause);
        }
    }

    /// A fresh Boolean definition variable, guaranteed not to collide with any
    /// user symbol.
    fn fresh(&mut self) -> TermId {
        self.terms.mk_fresh_var("tseitin", Sort::Bool)
    }

    /// Clausify a top-level assertion into `top` (a conjunctive/positive
    /// context), avoiding a redundant top gate: a top-level `and` splits, a
    /// top-level `or` becomes one clause, anything else becomes a unit clause.
    fn clausify_assertion(&mut self, f: TermId, top: &mut Vec<TermId>) {
        match self.terms.get(f).clone() {
            TermData::App(sym, args) if sym.name() == "and" && !args.is_empty() => {
                for a in args {
                    self.clausify_assertion(a, top);
                }
            }
            TermData::App(sym, args) if sym.name() == "or" && args.len() >= 2 => {
                let lits: Vec<TermId> = args.iter().map(|&a| self.encode(a)).collect();
                let clause = self.terms.mk_or(lits);
                self.push_top(clause, top);
            }
            _ => {
                let lit = self.encode(f);
                self.push_top(lit, top);
            }
        }
    }

    /// Return the literal representing Boolean formula `f`, emitting any gate
    /// definitions needed. Memoized over the interned DAG.
    fn encode(&mut self, f: TermId) -> TermId {
        if let Some(&lit) = self.cache.get(&f) {
            return lit;
        }
        let lit = self.encode_uncached(f);
        self.cache.insert(f, lit);
        lit
    }

    fn encode_uncached(&mut self, f: TermId) -> TermId {
        match self.terms.get(f).clone() {
            // A Boolean constant is its own (trivial) literal.
            TermData::Const(Constant::Bool(b)) => {
                if b {
                    self.terms.true_term()
                } else {
                    self.terms.false_term()
                }
            }
            // Negation of a literal is a literal — no gate needed.
            TermData::Not(inner) => {
                let l = self.encode(inner);
                self.terms.mk_not(l)
            }
            // Boolean if-then-else gate.
            TermData::Ite(c, then_br, else_br) if self.is_bool(f) => {
                let lc = self.encode(c);
                let lt = self.encode(then_br);
                let le = self.encode(else_br);
                self.define_ite(lc, lt, le)
            }
            TermData::App(sym, args) => match sym.name() {
                "and" => {
                    let lits: Vec<TermId> = args.iter().map(|&a| self.encode(a)).collect();
                    self.define_and(&lits)
                }
                "or" => {
                    let lits: Vec<TermId> = args.iter().map(|&a| self.encode(a)).collect();
                    self.define_or(&lits)
                }
                "xor" => self.define_xor_chain(&args),
                "=>" | "implies" => self.define_implies_chain(&args),
                // `=` between two Booleans is iff; over any other sort it is a
                // theory-equality atom (handled by the `_` arm).
                "=" if args.len() == 2 && self.is_bool(args[0]) => {
                    let a = self.encode(args[0]);
                    let b = self.encode(args[1]);
                    self.define_iff(a, b)
                }
                // `distinct` over Booleans: pairwise inequality.
                "distinct" if args.len() >= 2 && self.is_bool(args[0]) => {
                    self.define_bool_distinct(&args)
                }
                // Any other Boolean application is an opaque atom (a literal).
                _ => f,
            },
            // Vars, non-Boolean ites, quantifiers, lets: opaque atoms.
            _ => f,
        }
    }

    /// Gate `t ↔ (l1 ∧ … ∧ ln)`, returning `t`.
    ///
    /// Clauses: `(¬t ∨ li)` for each `i` (t ⇒ each conjunct) and
    /// `(t ∨ ¬l1 ∨ … ∨ ¬ln)` (all conjuncts ⇒ t).
    fn define_and(&mut self, lits: &[TermId]) -> TermId {
        let true_t = self.terms.true_term();
        let false_t = self.terms.false_term();
        let mut ls = Vec::new();
        for &l in lits {
            if l == false_t {
                return false_t; // an AND with a false conjunct is false
            }
            if l == true_t {
                continue; // drop true conjuncts
            }
            ls.push(l);
        }
        if ls.is_empty() {
            return true_t;
        }
        if ls.len() == 1 {
            return ls[0];
        }
        let t = self.fresh();
        let nt = self.terms.mk_not(t);
        for &l in &ls {
            let c = self.terms.mk_or(vec![nt, l]);
            self.push_clause(c);
        }
        let mut big = Vec::with_capacity(ls.len() + 1);
        big.push(t);
        for &l in &ls {
            let nl = self.terms.mk_not(l);
            big.push(nl);
        }
        let c = self.terms.mk_or(big);
        self.push_clause(c);
        t
    }

    /// Gate `t ↔ (l1 ∨ … ∨ ln)`, returning `t`.
    ///
    /// Clauses: `(¬li ∨ t)` for each `i` (each disjunct ⇒ t) and
    /// `(¬t ∨ l1 ∨ … ∨ ln)` (t ⇒ the disjunction).
    fn define_or(&mut self, lits: &[TermId]) -> TermId {
        let true_t = self.terms.true_term();
        let false_t = self.terms.false_term();
        let mut ls = Vec::new();
        for &l in lits {
            if l == true_t {
                return true_t; // an OR with a true disjunct is true
            }
            if l == false_t {
                continue; // drop false disjuncts
            }
            ls.push(l);
        }
        if ls.is_empty() {
            return false_t;
        }
        if ls.len() == 1 {
            return ls[0];
        }
        let t = self.fresh();
        let nt = self.terms.mk_not(t);
        for &l in &ls {
            let nl = self.terms.mk_not(l);
            let c = self.terms.mk_or(vec![nl, t]);
            self.push_clause(c);
        }
        let mut big = Vec::with_capacity(ls.len() + 1);
        big.push(nt);
        big.extend_from_slice(&ls);
        let c = self.terms.mk_or(big);
        self.push_clause(c);
        t
    }

    /// Gate `t ↔ (a ↔ b)` (Boolean equality / iff), returning `t`.
    fn define_iff(&mut self, a: TermId, b: TermId) -> TermId {
        if a == b {
            return self.terms.true_term(); // x ↔ x is true
        }
        let na = self.terms.mk_not(a);
        if na == b {
            return self.terms.false_term(); // x ↔ ¬x is false
        }
        let nb = self.terms.mk_not(b);
        let t = self.fresh();
        let nt = self.terms.mk_not(t);
        // t ⇒ (a ↔ b)
        let c1 = self.terms.mk_or(vec![nt, na, b]);
        self.push_clause(c1);
        let c2 = self.terms.mk_or(vec![nt, a, nb]);
        self.push_clause(c2);
        // ¬t ⇒ (a xor b)
        let c3 = self.terms.mk_or(vec![t, a, b]);
        self.push_clause(c3);
        let c4 = self.terms.mk_or(vec![t, na, nb]);
        self.push_clause(c4);
        t
    }

    /// Gate `t ↔ (a xor b)`, returning `t`.
    fn define_xor(&mut self, a: TermId, b: TermId) -> TermId {
        if a == b {
            return self.terms.false_term(); // x xor x is false
        }
        let na = self.terms.mk_not(a);
        if na == b {
            return self.terms.true_term(); // x xor ¬x is true
        }
        let nb = self.terms.mk_not(b);
        let t = self.fresh();
        let nt = self.terms.mk_not(t);
        // t ⇒ (a xor b)
        let c1 = self.terms.mk_or(vec![nt, a, b]);
        self.push_clause(c1);
        let c2 = self.terms.mk_or(vec![nt, na, nb]);
        self.push_clause(c2);
        // ¬t ⇒ (a ↔ b)
        let c3 = self.terms.mk_or(vec![t, na, b]);
        self.push_clause(c3);
        let c4 = self.terms.mk_or(vec![t, a, nb]);
        self.push_clause(c4);
        t
    }

    /// Fold a (possibly n-ary) `xor` left-associatively through 2-input gates.
    fn define_xor_chain(&mut self, args: &[TermId]) -> TermId {
        if args.is_empty() {
            return self.terms.false_term(); // xor of nothing is false
        }
        let mut acc = self.encode(args[0]);
        for &a in &args[1..] {
            let l = self.encode(a);
            acc = self.define_xor(acc, l);
        }
        acc
    }

    /// Encode a (chainable, right-associative) `=>`: `(=> a1 … an)` is the clause
    /// `(¬a1 ∨ … ∨ ¬a_{n-1} ∨ an)`. Defensive — the elaborator normally lowers
    /// `=>` into `or`/`not` before a pass ever sees it.
    fn define_implies_chain(&mut self, args: &[TermId]) -> TermId {
        if args.is_empty() {
            return self.terms.true_term();
        }
        if args.len() == 1 {
            return self.encode(args[0]);
        }
        let mut lits = Vec::with_capacity(args.len());
        for &a in &args[..args.len() - 1] {
            let l = self.encode(a);
            let nl = self.terms.mk_not(l);
            lits.push(nl);
        }
        let last = self.encode(args[args.len() - 1]);
        lits.push(last);
        self.define_or(&lits)
    }

    /// Gate `t ↔ ite(c, a, b)` (Boolean ite), returning `t`.
    fn define_ite(&mut self, c: TermId, a: TermId, b: TermId) -> TermId {
        if a == b {
            return a; // ite(c, a, a) is a
        }
        let true_t = self.terms.true_term();
        let false_t = self.terms.false_term();
        if c == true_t {
            return a;
        }
        if c == false_t {
            return b;
        }
        let nc = self.terms.mk_not(c);
        let na = self.terms.mk_not(a);
        let nb = self.terms.mk_not(b);
        let t = self.fresh();
        let nt = self.terms.mk_not(t);
        // t ∧ c ⇒ a ; t ∧ ¬c ⇒ b
        let c1 = self.terms.mk_or(vec![nt, nc, a]);
        self.push_clause(c1);
        let c2 = self.terms.mk_or(vec![nt, c, b]);
        self.push_clause(c2);
        // c ∧ a ⇒ t ; ¬c ∧ b ⇒ t
        let c3 = self.terms.mk_or(vec![t, nc, na]);
        self.push_clause(c3);
        let c4 = self.terms.mk_or(vec![t, c, nb]);
        self.push_clause(c4);
        t
    }

    /// Encode a Boolean `distinct`: for two operands it is `xor`; for three or
    /// more it is unsatisfiable (only two Boolean values exist), i.e. `false`.
    fn define_bool_distinct(&mut self, args: &[TermId]) -> TermId {
        if args.len() == 2 {
            let a = self.encode(args[0]);
            let b = self.encode(args[1]);
            return self.define_xor(a, b);
        }
        self.terms.false_term()
    }
}

#[cfg(test)]
#[path = "tseitin_cnf_tests.rs"]
mod tests;
