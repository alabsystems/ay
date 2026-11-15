// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! From authored roots to a prenex game `Q₀X₀ Q₁X₁ … QₙXₙ. φ`.
//!
//! * Level 0 is existential and holds the free constants, every existential
//!   whose nearest enclosing quantifier is existential at level 0 (Skolem
//!   constants), and their purification variables. Levels alternate: even
//!   levels are existential, odd levels universal.
//! * Each quantifier OCCURRENCE is placed by its effective kind (after
//!   polarity) at the first level of that kind not above its nearest
//!   enclosing quantifier's level. Siblings under `and`/`or` are independent,
//!   so pulling them out in level order is an equivalence; binders are
//!   renamed to fresh engine variables, so nothing is captured.
//! * `div`/`mod` by a non-zero numeral are purified: `q = (div t k)` becomes
//!   an `Int` variable at the level of `t` with `0 ≤ t − k·q ≤ |k| − 1`,
//!   conjoined at an existential level and assumed at a universal one. Both
//!   are equivalences because the definition is total and functional.
//! * Arithmetic `ite` and `abs` are lifted out of atoms by Shannon expansion.
//!
//! Anything outside quantified linear `Int`/`Real` arithmetic over `Bool`
//! connectives (uninterpreted functions, non-arithmetic sorts, nonlinear
//! products, `to_int`/`is_int`, `let`) declines the whole problem.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};
use num_bigint::BigInt;

/// Why the normalizer refused the problem.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ShapeDecline {
    NoQuantifier,
    Sort,
    Operator,
    Nonlinear,
    QuantifierInTerm,
    Size,
    /// A quantifier with an empty binder list (`(exists () p)`): no engine
    /// variable to play, and no occurrence the publication replay can walk.
    EmptyBinder,
}

impl ShapeDecline {
    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::NoQuantifier => "shape-no-quantifier",
            Self::Sort => "shape-sort",
            Self::Operator => "shape-operator",
            Self::Nonlinear => "shape-nonlinear",
            Self::QuantifierInTerm => "shape-quantifier-in-term",
            Self::Size => "shape-size",
            Self::EmptyBinder => "shape-empty-binder",
        }
    }
}

/// One authored quantifier occurrence, as the game placed it.
#[derive(Clone, Debug)]
pub(crate) struct Occurrence {
    /// The authored `forall`/`exists` term.
    pub(crate) quantifier: TermId,
    /// Whether it occurs positively (after `not`/`=>` polarity).
    pub(crate) positive: bool,
    /// Effective kind: `true` for a universal occurrence.
    pub(crate) universal: bool,
    /// Engine variables, one per binder.
    pub(crate) vars: Vec<TermId>,
    pub(crate) level: usize,
    /// Enclosing occurrence, if any.
    pub(crate) parent: Option<usize>,
}

/// A purification definition: `var = def` where `def` is `(div t k)` over
/// engine variables.
#[derive(Clone, Debug)]
pub(crate) struct Purified {
    pub(crate) var: TermId,
    pub(crate) def: TermId,
    pub(crate) level: usize,
}

/// The prenex game.
#[derive(Clone, Debug)]
pub(crate) struct Game {
    /// Variables per level; level `i` is existential iff `i` is even.
    pub(crate) levels: Vec<Vec<TermId>>,
    pub(crate) level_of: HashMap<TermId, usize>,
    /// The quantifier-free matrix.
    pub(crate) matrix: TermId,
    /// Authored free constants (a subset of level 0).
    pub(crate) free: Vec<TermId>,
    pub(crate) occurrences: Vec<Occurrence>,
    pub(crate) purified: Vec<Purified>,
}

impl Game {
    /// The last level (the matrix is decided after it).
    pub(crate) fn last_level(&self) -> usize {
        self.levels.len().saturating_sub(1)
    }

    /// Every engine variable.
    pub(crate) fn all_vars(&self) -> Vec<TermId> {
        self.levels.iter().flatten().copied().collect()
    }
}

mod qf;

/// Distinct nodes the normalizer may create before it declines.
const MAX_NORMALIZE_WORK: usize = 2_000_000;
/// Arithmetic `ite`s lifted out of one atom.
const MAX_ITES_PER_ATOM: usize = 12;

struct Builder<'a> {
    terms: &'a mut TermStore,
    game: Game,
    /// Binding environments: `env_id -> (parent, name -> var)`.
    envs: Vec<(Option<usize>, HashMap<String, TermId>)>,
    /// `env_id -> occurrence index` of the quantifier that opened it.
    env_occ: Vec<Option<usize>>,
    memo: HashMap<(TermId, bool, usize, usize), TermId>,
    qf_memo: HashMap<(TermId, usize), TermId>,
    div_memo: HashMap<(TermId, BigInt), TermId>,
    exists_defs: Vec<TermId>,
    forall_defs: Vec<TermId>,
    free_seen: HashSet<TermId>,
    quantified: HashMap<TermId, bool>,
    work: usize,
}

fn is_arith(sort: &Sort) -> bool {
    matches!(sort, Sort::Int | Sort::Real)
}

impl Builder<'_> {
    fn tick(&mut self) -> Result<(), ShapeDecline> {
        self.work += 1;
        if self.work > MAX_NORMALIZE_WORK {
            Err(ShapeDecline::Size)
        } else {
            Ok(())
        }
    }

    fn has_quantifier(&mut self, t: TermId) -> bool {
        if let Some(&q) = self.quantified.get(&t) {
            return q;
        }
        let q = crate::ematching::contains_quantifier(self.terms, t);
        self.quantified.insert(t, q);
        q
    }

    fn lookup(&self, mut env: usize, name: &str) -> Option<TermId> {
        loop {
            let (parent, map) = &self.envs[env];
            if let Some(&v) = map.get(name) {
                return Some(v);
            }
            env = (*parent)?;
        }
    }

    fn register(&mut self, var: TermId, level: usize) {
        while self.game.levels.len() <= level {
            self.game.levels.push(Vec::new());
        }
        self.game.levels[level].push(var);
        self.game.level_of.insert(var, level);
    }

    fn free_constant(&mut self, t: TermId) -> Result<TermId, ShapeDecline> {
        let sort = self.terms.sort(t).clone();
        if !matches!(sort, Sort::Bool | Sort::Int | Sort::Real) {
            return Err(ShapeDecline::Sort);
        }
        if self.free_seen.insert(t) {
            self.game.free.push(t);
            self.register(t, 0);
        }
        Ok(t)
    }

    /// Max level of the engine variables below a rewritten term.
    fn level_of_term(&self, t: TermId) -> usize {
        let mut best = 0;
        let mut stack = vec![t];
        let mut seen = HashSet::default();
        while let Some(x) = stack.pop() {
            if !seen.insert(x) {
                continue;
            }
            if let Some(&l) = self.game.level_of.get(&x) {
                best = best.max(l);
                continue;
            }
            match self.terms.get(x) {
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(i) => stack.push(*i),
                TermData::Ite(c, a, b) => stack.extend([*c, *a, *b]),
                _ => {}
            }
        }
        best
    }

    /// `t` (or `¬t` when `!pol`) with every quantifier pulled into the game.
    fn norm(
        &mut self,
        t: TermId,
        pol: bool,
        env: usize,
        cur: usize,
    ) -> Result<TermId, ShapeDecline> {
        if !self.has_quantifier(t) {
            let r = self.qf(t, env)?;
            return Ok(if pol { r } else { self.terms.mk_not_raw(r) });
        }
        let key = (t, pol, env, cur);
        if let Some(&r) = self.memo.get(&key) {
            return Ok(r);
        }
        self.tick()?;
        let r = stacker::maybe_grow(64 * 1024, 8 * 1024 * 1024, || {
            self.norm_uncached(t, pol, env, cur)
        })?;
        self.memo.insert(key, r);
        Ok(r)
    }

    fn connective(&mut self, and: bool, parts: Vec<TermId>) -> TermId {
        let name = if and { "and" } else { "or" };
        match parts.as_slice() {
            [one] => *one,
            _ => self.terms.mk_app(Symbol::named(name), parts, Sort::Bool),
        }
    }

    fn norm_uncached(
        &mut self,
        t: TermId,
        pol: bool,
        env: usize,
        cur: usize,
    ) -> Result<TermId, ShapeDecline> {
        match self.terms.get(t).clone() {
            TermData::Not(inner) => self.norm(inner, !pol, env, cur),
            TermData::Forall(binders, body, _) | TermData::Exists(binders, body, _) => {
                if binders.is_empty() {
                    return Err(ShapeDecline::EmptyBinder);
                }
                let is_forall = matches!(self.terms.get(t), TermData::Forall(..));
                let universal = is_forall == pol;
                let level = if universal {
                    if cur % 2 == 1 {
                        cur
                    } else {
                        cur + 1
                    }
                } else if cur % 2 == 0 {
                    cur
                } else {
                    cur + 1
                };
                let mut map = HashMap::default();
                let mut vars = Vec::with_capacity(binders.len());
                for (name, sort) in &binders {
                    if !matches!(sort, Sort::Bool | Sort::Int | Sort::Real) {
                        return Err(ShapeDecline::Sort);
                    }
                    let v = self
                        .terms
                        .mk_fresh_var(&format!("qsat!{name}"), sort.clone());
                    self.register(v, level);
                    map.insert(name.clone(), v);
                    vars.push(v);
                }
                let parent = self.env_occ[env];
                let occ = self.game.occurrences.len();
                self.game.occurrences.push(Occurrence {
                    quantifier: t,
                    positive: pol,
                    universal,
                    vars,
                    level,
                    parent,
                });
                self.envs.push((Some(env), map));
                self.env_occ.push(Some(occ));
                let new_env = self.envs.len() - 1;
                self.norm(body, pol, new_env, level)
            }
            TermData::App(sym, args) => {
                let name = sym.name().to_string();
                match name.as_str() {
                    "and" | "or" => {
                        let is_and = (name == "and") == pol;
                        let parts = args
                            .iter()
                            .map(|&a| self.norm(a, pol, env, cur))
                            .collect::<Result<Vec<_>, _>>()?;
                        Ok(self.connective(is_and, parts))
                    }
                    "=>" => {
                        let (last, prem) = args.split_last().ok_or(ShapeDecline::Operator)?;
                        // (=> p… c) ≡ (or ¬p… c)
                        let mut parts = Vec::new();
                        for &p in prem {
                            parts.push(self.norm(p, !pol, env, cur)?);
                        }
                        parts.push(self.norm(*last, pol, env, cur)?);
                        Ok(self.connective(pol, parts))
                    }
                    "=" | "xor" | "distinct"
                        if args.len() == 2
                            && args
                                .iter()
                                .all(|&a| matches!(self.terms.sort(a), Sort::Bool)) =>
                    {
                        // a = b  ≡  (a ∧ b) ∨ (¬a ∧ ¬b); xor/distinct negate it.
                        let equal = (name == "=") == pol;
                        let (a, b) = (args[0], args[1]);
                        let a_t = self.norm(a, true, env, cur)?;
                        let a_f = self.norm(a, false, env, cur)?;
                        let b_t = self.norm(b, true, env, cur)?;
                        let b_f = self.norm(b, false, env, cur)?;
                        let (l, r) = if equal {
                            (
                                self.connective(true, vec![a_t, b_t]),
                                self.connective(true, vec![a_f, b_f]),
                            )
                        } else {
                            (
                                self.connective(true, vec![a_t, b_f]),
                                self.connective(true, vec![a_f, b_t]),
                            )
                        };
                        Ok(self.connective(false, vec![l, r]))
                    }
                    _ => Err(ShapeDecline::QuantifierInTerm),
                }
            }
            TermData::Ite(c, a, b) if matches!(self.terms.sort(t), Sort::Bool) => {
                // (c ∧ a) ∨ (¬c ∧ b), negated branch-wise.
                let c_t = self.norm(c, true, env, cur)?;
                let c_f = self.norm(c, false, env, cur)?;
                let a_p = self.norm(a, pol, env, cur)?;
                let b_p = self.norm(b, pol, env, cur)?;
                let l = self.connective(true, vec![c_t, a_p]);
                let r = self.connective(true, vec![c_f, b_p]);
                Ok(self.connective(false, vec![l, r]))
            }
            _ => Err(ShapeDecline::QuantifierInTerm),
        }
    }
}

/// Build the game for `roots`, or say why the problem is out of scope.
pub(crate) fn build_game(terms: &mut TermStore, roots: &[TermId]) -> Result<Game, ShapeDecline> {
    if !roots
        .iter()
        .any(|&r| crate::ematching::contains_quantifier(terms, r))
    {
        return Err(ShapeDecline::NoQuantifier);
    }
    let placeholder = terms.mk_bool(true);
    let mut b = Builder {
        terms,
        game: Game {
            levels: Vec::new(),
            level_of: HashMap::default(),
            matrix: placeholder,
            free: Vec::new(),
            occurrences: Vec::new(),
            purified: Vec::new(),
        },
        envs: vec![(None, HashMap::default())],
        env_occ: vec![None],
        memo: HashMap::default(),
        qf_memo: HashMap::default(),
        div_memo: HashMap::default(),
        exists_defs: Vec::new(),
        forall_defs: Vec::new(),
        free_seen: HashSet::default(),
        quantified: HashMap::default(),
        work: 0,
    };
    b.game.levels.push(Vec::new());
    let mut parts = Vec::with_capacity(roots.len());
    for &r in roots {
        if !matches!(b.terms.sort(r), Sort::Bool) {
            return Err(ShapeDecline::Sort);
        }
        parts.push(b.norm(r, true, 0, 0)?);
    }
    let body = b.connective(true, parts);
    // (∧ D∃) ∧ ((∧ D∀) → body)
    let guarded = if b.forall_defs.is_empty() {
        body
    } else {
        let forall_defs = std::mem::take(&mut b.forall_defs);
        let defs = b.connective(true, forall_defs);
        let not_defs = b.terms.mk_not_raw(defs);
        b.connective(false, vec![not_defs, body])
    };
    let mut top = std::mem::take(&mut b.exists_defs);
    top.push(guarded);
    let matrix = b.connective(true, top);
    let mut game = b.game;
    game.matrix = matrix;
    // Drop empty trailing levels (a universal level created only to be empty
    // cannot occur, but keep the invariant explicit).
    while game.levels.len() > 1 && game.levels.last().is_some_and(Vec::is_empty) {
        game.levels.pop();
    }
    Ok(game)
}
