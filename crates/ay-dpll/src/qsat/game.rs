// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The QSAT game loop (Bjørner–Janota, "Playing with Quantified
//! Satisfaction", LPAR-20, 2015), over a predicate abstraction whose moves
//! are truth assignments to atoms.
//!
//! Two players: ∃ keeps `A∃ = φ ∧ L∃`, ∀ keeps `A∀ = ¬φ ∧ L∀`. At level `ℓ`
//! the owner `p` of the level asks its kernel whether `A_p` is satisfiable
//! under the CUBE of `M`: every atom of `A_p` whose variables all sit below
//! level `ℓ`, fixed to its value in the current model `M`.
//!
//! * SAT (model `N`): `p` moves; `M := N`, `ℓ := ℓ + 1`. After the last level
//!   the cube fixes every matrix atom, so the next check is decided without
//!   a kernel call: its core is an implicant of the mover's base formula.
//! * UNSAT with core `C` (a sub-cube): `C ⇒ ¬A_p`, so `p` loses from every
//!   position in `C`. At level 0 the formula is false; at level 1 it is true
//!   (∃'s level-0 values are a witness). Otherwise `P = MBP(X_{ℓ−1}, C, M)`
//!   is a region where the opponent has a move into `C`; `p` learns `¬P` and
//!   backjumps to its own level at or above the deepest variable of `P`.
//!
//! Soundness of each lemma needs only that the kernel's UNSAT is right and
//! `M ⊨ C` (true by construction); termination follows from the finite image
//! of MBP. Verdicts are HINTS: publication re-derives them.
//!
//! A kernel UNSAT at level 0 or 1 ENDS the game, so it is not taken on one
//! solve's word: [`QsatHost::confirm_unsat`] must re-refute the same query
//! independently, or the game declines with `kernel-unknown`. (A probe
//! refuting a satisfiable level-0 query was measured: the game's `unsat`
//! survived only because publication refused it.)

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{TermId, TermStore};

use super::formula::{arith_eq_sides, collect_atoms, default_value, Implicant, Levels};
use super::lin::{Eval, Model, Val};
use super::mbp::{project, MbpDecline};
use super::prenex::Game;

/// The kernel's answer to `formulas ∧ assumptions`.
#[derive(Clone, Debug)]
pub(crate) enum KernelAnswer {
    /// Values of the requested targets (`None`: unconstrained).
    Sat(Vec<Option<Val>>),
    /// Indices of a subset of the assumptions that is unsatisfiable together
    /// with the formulas.
    Unsat(Vec<usize>),
    Unknown,
}

/// Term store, ground kernel and stop control.
pub(crate) trait QsatHost {
    fn terms(&mut self) -> &mut TermStore;
    /// `want_core`: whether an UNSAT answer should shrink its core (the
    /// caller projects it); otherwise every assumption may be reported.
    fn check(
        &mut self,
        formulas: &[TermId],
        assumptions: &[TermId],
        targets: &[TermId],
        want_core: bool,
    ) -> KernelAnswer;
    /// Independent re-refutation of `formulas` (no assumptions) after a
    /// decisive kernel UNSAT; `false` unless the confirmation is itself an
    /// UNSAT and nothing contradicts it.
    fn confirm_unsat(&mut self, formulas: &[TermId], targets: &[TermId]) -> bool;
    fn should_stop(&self) -> bool;
}

/// Resource caps; every cap declines.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Caps {
    pub(crate) rounds: usize,
    pub(crate) lemmas: usize,
}

impl Default for Caps {
    fn default() -> Self {
        Self {
            rounds: 20_000,
            lemmas: 10_000,
        }
    }
}

/// Why the game gave up.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Decline {
    Stop,
    KernelUnknown,
    Mbp(MbpDecline),
    Implicant,
    NoProgress,
    Cap(&'static str),
    Model,
}

impl Decline {
    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::Stop => "stop",
            Self::KernelUnknown => "kernel-unknown",
            Self::Mbp(m) => m.label(),
            Self::Implicant => "implicant",
            Self::NoProgress => "no-progress",
            Self::Cap(c) => c,
            Self::Model => "model",
        }
    }
}

/// The game's verdict (a hint).
#[derive(Clone, Debug)]
pub(crate) enum Outcome {
    Sat,
    Unsat,
    Decline(Decline),
}

/// One learned lemma: the owner of the lemma learned `¬region`, where the
/// OPPONENT had the move `subst` (at `level`) into a losing cube.
#[derive(Clone, Debug)]
pub(crate) struct Lemma {
    /// `true` when the lemma belongs to ∀ (so `subst` is an ∃ move).
    pub(crate) forall_owned: bool,
    /// Level whose variables were projected.
    pub(crate) level: usize,
    pub(crate) region: Vec<(TermId, bool)>,
    pub(crate) subst: Vec<(TermId, TermId)>,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct Stats {
    pub(crate) rounds: usize,
    pub(crate) kernel_calls: usize,
    pub(crate) max_level: usize,
    pub(crate) lemmas_exists: usize,
    pub(crate) lemmas_forall: usize,
}

/// A finished run.
#[derive(Clone, Debug)]
pub(crate) struct Run {
    pub(crate) outcome: Outcome,
    /// The final model (on `Sat`, its level-0 values are the witness).
    pub(crate) model: Model,
    pub(crate) lemmas: Vec<Lemma>,
    pub(crate) stats: Stats,
}

struct Player {
    base: TermId,
    lemmas: Vec<TermId>,
    lemma_set: HashSet<Vec<(TermId, bool)>>,
}

struct Engine<'g> {
    game: &'g Game,
    players: [Player; 2],
    atoms: Vec<TermId>,
    atom_set: HashSet<TermId>,
    atom_level: HashMap<TermId, usize>,
    targets: Vec<TermId>,
    model: Model,
    lemmas: Vec<Lemma>,
    stats: Stats,
    caps: Caps,
}

fn player_of(level: usize) -> usize {
    level % 2
}

impl Engine<'_> {
    fn level_of_atom(&mut self, terms: &TermStore, atom: TermId) -> usize {
        if let Some(&l) = self.atom_level.get(&atom) {
            return l;
        }
        let mut lv = Levels::new(&self.game.level_of);
        let l = lv.of(terms, atom);
        self.atom_level.insert(atom, l);
        l
    }

    /// The position at `level`: EVERY atom either player has seen whose
    /// variables all sit below `level`, at its value in `M`. The atom set is
    /// shared (one predicate abstraction for both players): a lemma one
    /// player learned constrains the positions the other may move to.
    /// The position at `level`: EVERY atom either player has seen whose
    /// variables all sit below `level`, at its value in `M`. The atom set is
    /// shared (one predicate abstraction for both players): a lemma one
    /// player learned constrains the positions the other may move to.
    ///
    /// A false arithmetic equality is presented as the strict inequality the
    /// model satisfies: a stronger literal, still true in `M`, and no theory
    /// disequality for the kernel to split.
    fn cube(
        &mut self,
        terms: &mut TermStore,
        level: usize,
    ) -> Result<Vec<(TermId, bool)>, Decline> {
        let atoms = self.atoms.clone();
        let mut valued = Vec::new();
        let mut strict_sides = Vec::new();
        {
            let terms_ro: &TermStore = terms;
            let mut ev = Eval::new(terms_ro, &self.model);
            for a in atoms {
                let l = match self.atom_level.get(&a) {
                    Some(&l) => l,
                    None => {
                        let mut lv = Levels::new(&self.game.level_of);
                        let l = lv.of(terms_ro, a);
                        self.atom_level.insert(a, l);
                        l
                    }
                };
                if l >= level {
                    continue;
                }
                let v = ev.boolean(a).ok_or(Decline::Model)?;
                if !v {
                    if let Some((s, t)) = arith_eq_sides(terms_ro, a) {
                        let (vs, vt) = (
                            ev.number(s).ok_or(Decline::Model)?,
                            ev.number(t).ok_or(Decline::Model)?,
                        );
                        strict_sides.push(valued.len());
                        valued.push((a, v, if vs < vt { (s, t) } else { (t, s) }));
                        continue;
                    }
                }
                valued.push((a, v, (a, a)));
            }
        }
        let mut out = Vec::with_capacity(valued.len());
        for (i, (a, v, (lo, hi))) in valued.into_iter().enumerate() {
            if strict_sides.binary_search(&i).is_ok() {
                let strict = terms.mk_app(
                    ay_core::term::Symbol::named("<"),
                    vec![lo, hi],
                    ay_core::Sort::Bool,
                );
                if self.atom_set.insert(strict) {
                    self.atoms.push(strict);
                }
                out.push((strict, true));
            } else {
                out.push((a, v));
            }
        }
        Ok(out)
    }

    fn add_lemma(
        &mut self,
        terms: &mut TermStore,
        p: usize,
        region: &[(TermId, bool)],
    ) -> Result<TermId, Decline> {
        let mut key: Vec<(TermId, bool)> = region.to_vec();
        key.sort();
        if !self.players[p].lemma_set.insert(key) {
            return Err(Decline::NoProgress);
        }
        // ¬(∧ region) as a clause.
        let lits: Vec<TermId> = region
            .iter()
            .map(|&(a, v)| if v { terms.mk_not_raw(a) } else { a })
            .collect();
        let clause = match lits.as_slice() {
            [] => terms.mk_bool(false),
            [one] => *one,
            _ => terms.mk_app(
                ay_core::term::Symbol::named("or"),
                lits,
                ay_core::Sort::Bool,
            ),
        };
        self.players[p].lemmas.push(clause);
        collect_atoms(terms, clause, &mut self.atom_set, &mut self.atoms);
        Ok(clause)
    }

    /// The core at a level past the last: every matrix atom is fixed and
    /// the mover's base formula holds in `M`, so an implicant of it refutes
    /// the other player.
    fn bottom_core(&mut self, terms: &TermStore, p: usize) -> Result<Vec<(TermId, bool)>, Decline> {
        let base = self.players[1 - p].base;
        let mut ev = Eval::new(terms, &self.model);
        let mut lv = Levels::new(&self.game.level_of);
        let mut imp = Implicant::new(&mut ev, &mut lv);
        if imp.run(base, true).is_none() {
            tracing::debug!(target: "ay::qsat", "implicant failed at the bottom level");
            return Err(Decline::Implicant);
        }
        Ok(imp.out)
    }

    /// Level-0 variables at their values in `M`, as terms.
    fn level0_pins(&self, terms: &mut TermStore) -> Vec<(TermId, TermId)> {
        let mut pins = Vec::new();
        for &v in self.game.levels.first().map(Vec::as_slice).unwrap_or(&[]) {
            let t = match (terms.sort(v).clone(), self.model.vals.get(&v)) {
                (ay_core::Sort::Bool, Some(Val::Bool(b))) => terms.mk_bool(*b),
                (ay_core::Sort::Int, Some(Val::Num(n))) if n.is_integer() => {
                    terms.mk_int(n.to_integer())
                }
                (ay_core::Sort::Real, Some(Val::Num(n))) => terms.mk_rational(n.clone()),
                _ => continue,
            };
            pins.push((v, t));
        }
        pins
    }

    /// Ask `p`'s kernel at `level`: `Ok(None)` when `p` moved (the model
    /// was replaced), `Ok(Some(core))` when `p` lost from the cube.
    fn kernel_step(
        &mut self,
        host: &mut dyn QsatHost,
        p: usize,
        level: usize,
    ) -> Result<Option<Vec<(TermId, bool)>>, Decline> {
        let cube = self.cube(host.terms(), level)?;
        let mut formulas = vec![self.players[p].base];
        formulas.extend(self.players[p].lemmas.iter().copied());
        // Level 1 ends the game on UNSAT, so no core is projected from it:
        // the ∀ player may answer the exact level-0 VALUES (a stronger
        // position than their cube, still consistent with it), which the
        // ground lanes simplify away.
        let asms: Vec<TermId> = if level == 1 {
            let pins = self.level0_pins(host.terms());
            let terms = host.terms();
            for f in &mut formulas {
                *f = super::subst::substitute_fold(terms, *f, &pins);
            }
            Vec::new()
        } else {
            let terms = host.terms();
            cube.iter()
                .map(|&(a, v)| if v { a } else { terms.mk_not_raw(a) })
                .collect()
        };
        self.stats.kernel_calls += 1;
        // Levels 0 and 1 end the game on UNSAT: no core is projected, and the
        // refutation must be confirmed (see the module docs).
        let decisive = level <= 1;
        match host.check(&formulas, &asms, &self.targets, !decisive) {
            KernelAnswer::Unsat(_) if decisive && !self.confirmed(host, &formulas, &asms) => {
                tracing::debug!(target: "ay::qsat", level, "decisive kernel unsat not confirmed");
                Err(Decline::KernelUnknown)
            }
            KernelAnswer::Unknown => Err(Decline::KernelUnknown),
            KernelAnswer::Sat(values) => {
                let mut m = Model::default();
                for (&t, v) in self.targets.iter().zip(values) {
                    let v = match v {
                        Some(v) => v,
                        None => match self.model.vals.get(&t) {
                            Some(old) => old.clone(),
                            None => default_value(host.terms(), t),
                        },
                    };
                    m.vals.insert(t, v);
                }
                self.model = m;
                Ok(None)
            }
            KernelAnswer::Unsat(indices) => Ok(Some(
                indices
                    .into_iter()
                    .filter_map(|i| cube.get(i).copied())
                    .collect(),
            )),
        }
    }

    /// Confirm a decisive kernel UNSAT of `formulas ∧ asms` (the cube is
    /// empty at levels 0 and 1, so this is normally `formulas` alone).
    fn confirmed(&self, host: &mut dyn QsatHost, formulas: &[TermId], asms: &[TermId]) -> bool {
        let mut roots = formulas.to_vec();
        roots.extend_from_slice(asms);
        host.confirm_unsat(&roots, &self.targets)
    }

    /// `p` lost from every position in `core` at `level ≥ 2`: project the
    /// opponent's level, learn the lemma, return the back-jump level.
    fn learn(
        &mut self,
        host: &mut dyn QsatHost,
        p: usize,
        level: usize,
        core: &[(TermId, bool)],
    ) -> Result<usize, Decline> {
        let vars = self.game.levels.get(level - 1).cloned().unwrap_or_default();
        let projection = project(host.terms(), core, &vars, &self.model).map_err(Decline::Mbp)?;
        tracing::debug!(
            target: "ay::qsat",
            player = p,
            level,
            core = core.len(),
            region = projection.lits.len(),
            "lemma"
        );
        // Back-jump target: p's own level at or above the deepest variable
        // of the region.
        let mut deepest = 0;
        for &(a, _) in &projection.lits {
            deepest = deepest.max(self.level_of_atom(host.terms(), a));
        }
        let _clause = self.add_lemma(host.terms(), p, &projection.lits)?;
        if p == 0 {
            self.stats.lemmas_exists += 1;
        } else {
            self.stats.lemmas_forall += 1;
        }
        if self.lemmas.len() >= self.caps.lemmas {
            return Err(Decline::Cap("cap-lemmas"));
        }
        self.lemmas.push(Lemma {
            forall_owned: p == 1,
            level: level - 1,
            region: projection.lits,
            subst: projection.subst,
        });
        Ok(if player_of(deepest) == p {
            deepest
        } else {
            deepest + 1
        })
    }

    fn run(&mut self, host: &mut dyn QsatHost) -> Result<Outcome, Decline> {
        let last = self.game.last_level();
        let mut level = 0usize;
        loop {
            self.stats.rounds += 1;
            if self.stats.rounds > self.caps.rounds {
                return Err(Decline::Cap("cap-rounds"));
            }
            if host.should_stop() {
                return Err(Decline::Stop);
            }
            self.stats.max_level = self.stats.max_level.max(level);
            let p = player_of(level);
            let core = if level > last {
                self.bottom_core(host.terms(), p)?
            } else {
                match self.kernel_step(host, p, level)? {
                    None => {
                        level += 1;
                        continue;
                    }
                    Some(core) => core,
                }
            };
            // p loses from every position in `core`.
            match level {
                0 => return Ok(Outcome::Unsat),
                1 => return Ok(Outcome::Sat),
                _ => level = self.learn(host, p, level, &core)?,
            }
        }
    }
}

/// Play the game.
pub(crate) fn solve(host: &mut dyn QsatHost, game: &Game, caps: Caps) -> Run {
    let terms = host.terms();
    let exists_base = game.matrix;
    let forall_base = terms.mk_not_raw(game.matrix);
    let mut atoms = Vec::new();
    let mut atom_set = HashSet::default();
    collect_atoms(terms, exists_base, &mut atom_set, &mut atoms);
    collect_atoms(terms, forall_base, &mut atom_set, &mut atoms);
    let mk = |base| Player {
        base,
        lemmas: Vec::new(),
        lemma_set: HashSet::default(),
    };
    let mut engine = Engine {
        game,
        players: [mk(exists_base), mk(forall_base)],
        atoms,
        atom_set,
        atom_level: HashMap::default(),
        targets: game.all_vars(),
        model: Model::default(),
        lemmas: Vec::new(),
        stats: Stats::default(),
        caps,
    };
    let outcome = match engine.run(host) {
        Ok(o) => o,
        Err(d) => Outcome::Decline(d),
    };
    Run {
        outcome,
        model: engine.model,
        lemmas: engine.lemmas,
        stats: engine.stats,
    }
}
