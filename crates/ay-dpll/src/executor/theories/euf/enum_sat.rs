// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Enum finite-domain SAT lane (#enum-sat-lane).
//!
//! Eager Algaroba-style reduction of PURE-ENUM datatype problems to
//! propositional SAT (Shah/Mora/Seshia, "An Eager Satisfiability Modulo
//! Theories Solver for Algebraic Datatypes", AAAI'24). When every datatype
//! term in the problem ranges over an all-nullary (enum) datatype and every
//! theory atom is an (dis)equality between ground enum terms, the formula is
//! exactly a finite-domain CSP (the SMT-LIB 20210312-Bouvier family is graph
//! coloring in this dress). The lazy DPLL(T) lane re-derives the finite
//! domain one EUF equality at a time — millions of theory callbacks; this
//! lane instead one-hot encodes the domain and hands ONE CNF to the SAT core.
//!
//! ## Encoding (definitional — equisatisfiable by construction)
//!
//! For every ground enum term `t` of a `k`-constructor sort we introduce
//! one-hot variables `x_{t,0..k-1}` ("t denotes constructor c") with an
//! EXACTLY-ONE constraint (at-least-one clause + pairwise or Sinz-sequential
//! at-most-one; the Sinz auxiliaries are definitional prefix-ORs). Constructor
//! constants are compile-time-fixed points of the domain, not rows. Theory
//! atoms are channeled to the one-hot layer polarity-aware:
//!
//! - `(= t c_i)` with `c_i` a constructor  ↦  literal `x_{t,i}`
//! - `(= s t)`                             ↦  per-color agreement clauses
//! - `(distinct ...)`                      ↦  pairwise per-color conflict
//!   clauses (fresh pair-equality variables `e ↔ s = t` for n-ary forms)
//!
//! Atoms nested inside Boolean structure get FULL biconditional channeling to
//! their Tseitin variable; atoms asserted as top-level units get only the
//! clauses for their asserted polarity (Plaisted–Greenbaum; the Tseitin
//! variable is unit-asserted, so its value always agrees with the decoded
//! semantics). The Boolean skeleton itself is the standard (full,
//! bidirectional) Tseitin encoding from `ay_core::Tseitin`.
//!
//! ## Soundness
//!
//! UNSAT: every model M of the original formula extends to a CNF model — set
//! `x_{t,c}` := "M(t) = c" (exactly-one holds: an enum value IS exactly one
//! constructor), pair/atom/gate variables := their defined truth values in M;
//! every emitted clause class is a logical consequence of that intended
//! interpretation, and clauses emitted for statically-false units
//! (`(= c_i c_j)`, `(distinct t t)`) only fire when no M exists at all. Hence
//! CNF-UNSAT ⇒ original UNSAT, and the verdict is conflict-derived by the SAT
//! core (no heuristic answers).
//!
//! SAT: the decoded assignment (each row's unique true color) is turned into
//! a normal `EufModel` whose elements are the constructor names and emitted
//! through `solve_and_store_model_full`, so the ALWAYS-ON model gates
//! (`finalize_sat_model_validation`: enum-cardinality gate, strict per-theory
//! oracles, full assertion re-evaluation) re-verify it exactly like any other
//! lane's model. A model the gates reject does NOT answer — the lane falls
//! through to the general DT+EUF lane (fail-closed).
//!
//! UF congruence: applications `f(args)` are admitted ONLY when every
//! argument is a CONSTRUCTOR CONSTANT. Distinct constructor tuples are
//! pairwise-distinct in EVERY model (datatype constructors are distinct), so
//! functional congruence never links two distinct admitted application terms,
//! and identical tuples are hash-consed to the SAME `TermId` (one row).
//! Treating each application as an independent finite-domain variable is
//! therefore exact — no Ackermann instances are needed. Applications with any
//! non-constructor argument (variables, selectors, nested applications) fall
//! through to the general lane, as does anything with selectors, testers,
//! recursive datatypes, non-enum sorts, quantifiers, or unrecognized Boolean
//! connectives (`enum_sat_scan` gates the fragment conservatively).

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{Sort, TermId, Tseitin, TseitinResult};
use ay_euf::EufModel;
use ay_sat::{Literal, SatResult, Solver as SatSolver, Variable};

use super::super::super::Executor;
use crate::executor_types::{Result, SolveResult};

/// Fall through to the general lane above this many estimated extra clauses.
/// The largest admitted Bouvier instance (vlsat3_h86, ~54M mostly-binary
/// clauses) peaks near 15 GB RSS and solves in ~18s — while the general lane
/// burns MORE memory (17-18 GB observed) just to time out on the same
/// instance, so the cap trades nothing away locally and stays well inside
/// single-job competition memory limits. Overridable via
/// `AY_ENUM_SAT_MAX_CLAUSES` for experiments.
const DEFAULT_MAX_EXTRA_CLAUSES: u64 = 56_000_000;

/// One-hot rows above this constructor count use the Sinz sequential
/// at-most-one encoding instead of the pairwise quadratic one.
const PAIRWISE_AMO_MAX: usize = 16;

/// A ground enum operand of an (dis)equality atom.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum EnumOperand {
    /// A constructor constant: compile-time-fixed domain point.
    Fixed { sort: u32, ctor: u32 },
    /// A colorable term (declared constant or admitted UF application):
    /// index into `EnumSatScan::rows`.
    Colored { row: u32 },
}

/// Static comparison of two operands, decided at encode time when possible.
enum PairStatus {
    StaticEqual,
    StaticDistinct,
    Dynamic,
}

#[derive(Debug)]
enum EnumAtomKind {
    Eq(EnumOperand, EnumOperand),
    Distinct(Vec<EnumOperand>),
}

struct EnumAtom {
    term: TermId,
    kind: EnumAtomKind,
    /// Asserted as a positive top-level unit.
    unit_pos: bool,
    /// Asserted as a negated top-level unit.
    unit_neg: bool,
    /// Occurs inside Boolean structure — needs full biconditional channeling.
    skeleton: bool,
}

struct EnumSortInfo {
    name: String,
    ctors: Vec<String>,
    ctor_index: HashMap<String, u32>,
}

struct EnumRow {
    term: TermId,
    sort: u32,
}

/// Output of the fragment gate + collection walk.
struct EnumSatScan {
    sorts: Vec<EnumSortInfo>,
    rows: Vec<EnumRow>,
    atoms: Vec<EnumAtom>,
    /// Constructor-constant terms seen anywhere in an atom (for the model).
    fixed_terms: Vec<(TermId, u32, u32)>,
    /// A top-level unit was statically false (e.g. `(= c_i c_j)`, i != j).
    static_conflict: bool,
}

enum AtomClass {
    Atom(EnumAtomKind),
    NotAtom,
    Invalid,
}

/// Working state for the gate walk.
struct ScanState {
    sorts: Vec<EnumSortInfo>,
    sort_by_name: HashMap<String, Option<u32>>,
    rows: Vec<EnumRow>,
    row_of: HashMap<TermId, u32>,
    atoms: Vec<EnumAtom>,
    atom_of: HashMap<TermId, usize>,
    fixed_terms: Vec<(TermId, u32, u32)>,
    fixed_seen: HashSet<TermId>,
    static_conflict: bool,
}

impl Executor {
    /// Try the enum finite-domain SAT lane. `Ok(None)` means "not applicable
    /// or not confirmed — use the general lane" (always sound to return).
    pub(in crate::executor) fn try_solve_enum_finite_domain(
        &mut self,
    ) -> Result<Option<SolveResult>> {
        // B17: CLI-populated global (--no-enum-sat) replaced the never-set
        // env var.
        if ay_core::theory_disable_flags().no_enum_sat {
            return Ok(None);
        }
        // The lane sees only `ctx.assertions`: bail when assumptions are in
        // play (they are carried separately on the assumption routes).
        if self.last_assumptions.is_some() {
            return Ok(None);
        }

        let Some(scan) = self.enum_sat_scan() else {
            return Ok(None);
        };

        // Encoding-size budget: fall through on instances whose one-hot
        // channeling would dwarf the time limit anyway. Estimated from atom
        // shapes only (upper bound; the Boolean skeleton is linear in input).
        // B10: compiled constant (the AY_ENUM_SAT_MAX_CLAUSES override
        // nothing set is retired).
        let max_clauses = DEFAULT_MAX_EXTRA_CLAUSES;
        let estimate = estimate_extra_clauses(&scan);
        if estimate > max_clauses {
            if ay_core::misc_cli_flags().phase_trace {
                eprintln!(
                    "c phase-trace enum-sat-lane skip reason=clause-budget estimate={estimate}"
                );
            }
            return Ok(None);
        }

        if ay_core::misc_cli_flags().phase_trace {
            eprintln!(
                "c phase-trace enum-sat-lane hit sorts={} rows={} atoms={} est_clauses={estimate}",
                scan.sorts.len(),
                scan.rows.len(),
                scan.atoms.len()
            );
        }

        // --- Boolean skeleton: standard Tseitin over the assertions. ---
        let mut tseitin = Tseitin::new(&self.ctx.terms);
        for &assertion in &self.ctx.assertions {
            tseitin.assert_term(assertion);
        }
        // Every skeleton atom needs its Tseitin variable for channeling; a
        // missing entry would make the encoding inexact, so fall through
        // (defensive — the scan only admits shapes Tseitin assigns vars to).
        if scan
            .atoms
            .iter()
            .any(|a| a.skeleton && !tseitin.term_to_var().contains_key(&a.term))
        {
            return Ok(None);
        }

        // --- Plan the extra variable space (rows, Sinz aux, pair vars). ---
        let plan = plan_extra_vars(&scan, tseitin.num_vars());
        let total_vars = tseitin.num_vars() as u64 + plan.extra_vars as u64;

        let mut solver = SatSolver::new(total_vars as usize);
        self.apply_random_seed_to_sat(&mut solver);
        self.apply_progress_to_sat(&mut solver);
        solver.set_congruence_enabled(false);
        if total_vars > 50_000 {
            solver.set_reorder_enabled(false);
        }
        if let Some(seed) = self.random_seed {
            solver.set_random_seed(seed);
        }

        // Size the clause arena from the encoding, not from the variable count.
        //
        // `SatSolver::new` has only `total_vars` to go on and pre-sizes the
        // arena at `num_vars * 4` clauses of 3 literals each. This lane's eager
        // lowering routinely blows past that by two orders of magnitude
        // (vlsat3_b99: 51,893,377 clauses over 563,839 variables, i.e. 23x the
        // guess), and the arena then climbs there by DOUBLING — finishing one
        // doubling past what it needed and holding hundreds of megabytes of
        // mapped, never-written slack. That slack is invisible in RSS but is
        // charged in full against `--memory`, and on vlsat3_b99 it was the
        // difference between answering and a memout.
        //
        // The count comes from running the emitter itself over a counting sink,
        // so it cannot drift from what is emitted. It is an upper bound (the
        // solver still drops duplicate literals, tautologies, and root-satisfied
        // clauses), which is the safe side for a reservation; the arena grows
        // normally if it is ever low.
        let mut planned_clauses = 0usize;
        let mut planned_literals = 0usize;
        for clause in tseitin.all_clauses() {
            planned_clauses += 1;
            planned_literals += clause.literals().len();
        }
        let (extra_clauses, extra_literals) = count_enum_clauses(&scan, &plan, &tseitin);
        planned_clauses += extra_clauses;
        planned_literals += extra_literals;
        solver.reserve_clause_capacity(planned_clauses, planned_literals);
        if ay_core::misc_cli_flags().phase_trace {
            eprintln!(
                "c phase-trace enum-sat-lane reserve clauses={planned_clauses} \
                 literals={planned_literals} arena_mb={:.1}",
                (planned_clauses * 3 + planned_literals) as f64 * 4.0 / (1024.0 * 1024.0),
            );
        }

        // Skeleton clauses.
        let mut buf: Vec<Literal> = Vec::with_capacity(16);
        for clause in tseitin.all_clauses() {
            buf.clear();
            buf.extend(clause.literals().iter().map(|&l| crate::cnf_lit_to_sat(l)));
            solver.add_clause_reusing_buffer(&mut buf);
        }

        // Channeling + domain clauses.
        emit_enum_clauses(&scan, &plan, &tseitin, &mut EmitSink::Solver(&mut solver));

        self.last_statistics
            .set_int("enum_sat.rows", scan.rows.len() as u64);
        self.last_statistics
            .set_int("enum_sat.atoms", scan.atoms.len() as u64);
        self.last_statistics.set_int("enum_sat.vars", total_vars);
        self.arm_sat_conflict_budget(&mut solver, 0);
        let should_stop = self.make_should_stop();
        let result = solver.solve_interruptible(should_stop).into_inner();
        collect_sat_stats!(self, &solver);

        // Model storage reads only the term<->var maps from the Tseitin
        // result; the clauses were streamed into the solver above, so an
        // empty clause list avoids a second multi-million-entry copy.
        let tseitin_result = TseitinResult::new(
            Vec::new(),
            tseitin.term_to_var().clone(),
            tseitin.var_to_term().clone(),
            0,
            tseitin.num_vars(),
        );
        drop(tseitin);

        match result {
            SatResult::Sat(sat_model) => {
                // Decode the one-hot assignment into a normal EUF model whose
                // elements are the constructor names, then emit it through the
                // NORMAL model path: `solve_and_store_model_full` runs
                // `finalize_sat_model_validation` (enum-cardinality gate,
                // strict oracles, full assertion re-evaluation) exactly as for
                // every other lane.
                let euf_model = decode_enum_model(self, &scan, &plan, &sat_model);
                let out = self.solve_and_store_model_full(
                    SatResult::Sat(sat_model),
                    &tseitin_result,
                    Some(euf_model),
                    None,
                    None,
                    None,
                    None,
                    None,
                    None,
                    None,
                )?;
                if matches!(out, SolveResult::Sat) {
                    self.last_statistics
                        .set_string("solver.enum_sat_lane", "sat");
                    Ok(Some(SolveResult::Sat))
                } else {
                    // Gate-rejected model: degrade to the general lane, never
                    // answer from an unverified encoding (fail-closed).
                    if ay_core::misc_cli_flags().phase_trace {
                        eprintln!("c phase-trace enum-sat-lane gate-rejected-sat fallback");
                    }
                    self.last_statistics
                        .set_string("solver.enum_sat_lane", "fallback-gate");
                    self.last_unknown_reason = None;
                    self.last_result = None;
                    self.pending_sat_unknown_reason = None;
                    Ok(None)
                }
            }
            SatResult::Unsat(_) => {
                // Proof-producing solves (--proof / --self-check) need a
                // refutation proof wired through the native tracking, which
                // this lane's direct SAT encode does not populate: leave the
                // UNSAT to the general lane (slower, proof-carrying). SAT
                // results need no refutation proof — self-check certifies
                // them by model evaluation — so only UNSAT falls through.
                //
                // The predicate is `is_producing_proofs` — "did the CALLER ask
                // for a proof artifact" — NOT `produce_proofs_enabled`, which
                // only says the internal tracker is recording and is therefore
                // ALWAYS true on the public path (`begin_public_solve` turns it
                // on for every decision so the mandatory UNSAT certificate
                // cannot be switched off; see `produce_proofs_enabled`'s doc
                // comment). Gated on the tracker, this fallthrough fired
                // unconditionally and the lane could never answer `unsat`
                // (#enum-sat-lane-dead-unsat). Nothing is weakened: the UNSAT
                // still flows through `solve_and_store_model_full`, which
                // materializes the proof envelope, and the mandatory
                // certification funnel still has to accept it or the verdict
                // degrades to `unknown`.
                if self.is_producing_proofs() {
                    self.last_statistics
                        .set_string("solver.enum_sat_lane", "fallback-proof");
                    self.pending_sat_unknown_reason = None;
                    return Ok(None);
                }
                // Conflict-derived by the SAT core over a definitional
                // encoding (see module docs for the bijection argument).
                self.last_statistics
                    .set_string("solver.enum_sat_lane", "unsat");
                let out = self.solve_and_store_model_full(
                    result,
                    &tseitin_result,
                    None,
                    None,
                    None,
                    None,
                    None,
                    None,
                    None,
                    None,
                )?;
                Ok(Some(out))
            }
            SatResult::Unknown => {
                // Budget/interrupt: fall through; the general lane (or the
                // global deadline) takes over.
                self.last_statistics
                    .set_string("solver.enum_sat_lane", "fallback-unknown");
                self.pending_sat_unknown_reason = None;
                Ok(None)
            }
            #[allow(unreachable_patterns)]
            _ => Ok(None),
        }
    }

    /// Fragment gate + collection. Returns `None` unless EVERY assertion is
    /// Boolean structure (and/or/xor2/not/ite/iff over Bool) whose only
    /// non-Boolean leaves are (dis)equality atoms between ground enum terms
    /// (constructor constants, declared enum constants, or UF applications at
    /// all-constructor-constant arguments). Anything else — selectors,
    /// testers, recursive datatypes, non-enum sorts, quantifiers, unknown
    /// predicates — rejects the lane.
    fn enum_sat_scan(&self) -> Option<EnumSatScan> {
        let mut st = ScanState {
            sorts: Vec::new(),
            sort_by_name: HashMap::default(),
            rows: Vec::new(),
            row_of: HashMap::default(),
            atoms: Vec::new(),
            atom_of: HashMap::default(),
            fixed_terms: Vec::new(),
            fixed_seen: HashSet::default(),
            static_conflict: false,
        };
        let mut skeleton_visited: HashSet<TermId> = HashSet::default();

        for &assertion in &self.ctx.assertions {
            if !self.enum_scan_assertion(assertion, &mut st, &mut skeleton_visited) {
                return None;
            }
        }

        // Nothing enum-shaped: leave the problem to its normal route.
        if st.rows.is_empty() && st.atoms.is_empty() {
            return None;
        }

        Some(EnumSatScan {
            sorts: st.sorts,
            rows: st.rows,
            atoms: st.atoms,
            fixed_terms: st.fixed_terms,
            static_conflict: st.static_conflict,
        })
    }

    /// Walk one top-level assertion: peel `not` chains, recurse through
    /// positive `and`, record unit atoms polarity-aware, and send everything
    /// else through the skeleton walk. Returns false to reject the lane.
    fn enum_scan_assertion(
        &self,
        assertion: TermId,
        st: &mut ScanState,
        skeleton_visited: &mut HashSet<TermId>,
    ) -> bool {
        let mut sign = true;
        let mut cur = assertion;
        while let TermData::Not(inner) = self.ctx.terms.get(cur) {
            sign = !sign;
            cur = *inner;
        }
        match self.ctx.terms.get(cur) {
            TermData::Const(ay_core::term::Constant::Bool(b)) => {
                if *b != sign {
                    st.static_conflict = true;
                }
                true
            }
            TermData::App(sym, args) if sign && sym.name() == "and" => {
                let args = args.to_vec();
                args.iter()
                    .all(|&arg| self.enum_scan_assertion(arg, st, skeleton_visited))
            }
            _ => match self.enum_classify_atom(cur, st) {
                AtomClass::Atom(kind) => {
                    let idx = enum_atom_entry(st, cur, kind);
                    if sign {
                        st.atoms[idx].unit_pos = true;
                    } else {
                        st.atoms[idx].unit_neg = true;
                    }
                    true
                }
                AtomClass::Invalid => false,
                AtomClass::NotAtom => self.enum_scan_skeleton(cur, st, skeleton_visited),
            },
        }
    }

    /// Validate Boolean structure and mark every contained enum atom as
    /// needing full (both-polarity) channeling. Iterative DFS; rejects any
    /// construct the Tseitin+channeling pair does not model EXACTLY.
    fn enum_scan_skeleton(
        &self,
        root: TermId,
        st: &mut ScanState,
        visited: &mut HashSet<TermId>,
    ) -> bool {
        let mut stack = vec![root];
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t) {
                TermData::Const(ay_core::term::Constant::Bool(_)) => {}
                TermData::Var(_, _) if *self.ctx.terms.sort(t) == Sort::Bool => {}
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, a, b) => {
                    if *self.ctx.terms.sort(*a) != Sort::Bool
                        || *self.ctx.terms.sort(*b) != Sort::Bool
                    {
                        return false;
                    }
                    stack.push(*c);
                    stack.push(*a);
                    stack.push(*b);
                }
                TermData::App(sym, args) => match sym.name() {
                    "and" | "or" => stack.extend(args.iter().copied()),
                    "xor" if args.len() == 2 => stack.extend(args.iter().copied()),
                    "=" if args.len() == 2 && *self.ctx.terms.sort(args[0]) == Sort::Bool => {
                        stack.extend(args.iter().copied());
                    }
                    _ => match self.enum_classify_atom(t, st) {
                        AtomClass::Atom(kind) => {
                            let idx = enum_atom_entry(st, t, kind);
                            st.atoms[idx].skeleton = true;
                        }
                        _ => return false,
                    },
                },
                _ => return false,
            }
        }
        true
    }

    /// Classify a candidate theory atom: `(= s t)` / `(distinct ...)` over
    /// admitted ground enum operands.
    fn enum_classify_atom(&self, t: TermId, st: &mut ScanState) -> AtomClass {
        let TermData::App(sym, args) = self.ctx.terms.get(t) else {
            return AtomClass::NotAtom;
        };
        let name = sym.name();
        let is_eq = name == "=" && args.len() == 2;
        let is_distinct = name == "distinct" && args.len() >= 2;
        if !is_eq && !is_distinct {
            return AtomClass::NotAtom;
        }
        if self
            .enum_resolve_sort(self.ctx.terms.sort(args[0]), st)
            .is_none()
        {
            // Bool-sorted `=` was already consumed as a connective by the
            // skeleton walk; every other sort here is outside the fragment.
            return AtomClass::Invalid;
        }
        let args = args.to_vec();
        let mut ops = Vec::with_capacity(args.len());
        for &arg in &args {
            match self.enum_classify_operand(arg, st) {
                Some(op) => ops.push(op),
                None => return AtomClass::Invalid,
            }
        }
        if is_eq {
            AtomClass::Atom(EnumAtomKind::Eq(ops[0], ops[1]))
        } else {
            AtomClass::Atom(EnumAtomKind::Distinct(ops))
        }
    }

    /// Classify a ground enum operand; registers rows / fixed terms.
    fn enum_classify_operand(&self, t: TermId, st: &mut ScanState) -> Option<EnumOperand> {
        let sort_idx = self.enum_resolve_sort(self.ctx.terms.sort(t), st)?;
        match self.ctx.terms.get(t) {
            TermData::Var(name, _) => Some(register_leaf(st, t, sort_idx, name.clone())),
            TermData::App(sym, args) if args.is_empty() => {
                Some(register_leaf(st, t, sort_idx, sym.name().to_string()))
            }
            TermData::App(sym, args) => {
                // UF application: admitted only at all-constructor-constant
                // arguments (see module docs — congruence is then vacuous).
                // A constructor/selector symbol can never head an admitted
                // application: enum constructors are nullary, and a selector's
                // argument sort is its (non-enum) datatype, so its argument
                // fails the Fixed requirement below; the explicit constructor
                // check is belt-and-braces.
                if self.ctx.is_constructor(sym.name()).is_some() {
                    return None;
                }
                for &arg in args.iter() {
                    match self.enum_classify_operand(arg, st) {
                        Some(EnumOperand::Fixed { .. }) => {}
                        _ => return None,
                    }
                }
                if let Some(&row) = st.row_of.get(&t) {
                    return Some(EnumOperand::Colored { row });
                }
                let row = st.rows.len() as u32;
                st.rows.push(EnumRow {
                    term: t,
                    sort: sort_idx,
                });
                st.row_of.insert(t, row);
                Some(EnumOperand::Colored { row })
            }
            _ => None,
        }
    }

    /// Resolve a sort to an all-nullary (enum) datatype index, caching both
    /// positive and negative answers by sort name.
    fn enum_resolve_sort(&self, sort: &Sort, st: &mut ScanState) -> Option<u32> {
        let name = match sort {
            Sort::Uninterpreted(name) => name.as_str(),
            Sort::Datatype(dt) => dt.name.as_str(),
            _ => return None,
        };
        if let Some(cached) = st.sort_by_name.get(name) {
            return *cached;
        }
        let ctors: Vec<String> = self
            .ctx
            .datatype_iter()
            .find(|(dt_name, _)| *dt_name == name)
            .map(|(_, cs)| cs.to_vec())
            .unwrap_or_default();
        let all_nullary = !ctors.is_empty()
            && ctors.iter().all(|c| {
                self.ctx
                    .constructor_selector_info(c)
                    .is_none_or(|f| f.is_empty())
            });
        let resolved = if all_nullary {
            let idx = st.sorts.len() as u32;
            let ctor_index = ctors
                .iter()
                .enumerate()
                .map(|(i, c)| (c.clone(), i as u32))
                .collect();
            st.sorts.push(EnumSortInfo {
                name: name.to_string(),
                ctors,
                ctor_index,
            });
            Some(idx)
        } else {
            None
        };
        st.sort_by_name.insert(name.to_string(), resolved);
        resolved
    }
}

/// Register a nullary leaf (declared constant or constructor constant).
fn register_leaf(st: &mut ScanState, t: TermId, sort_idx: u32, name: String) -> EnumOperand {
    if let Some(&ctor) = st.sorts[sort_idx as usize].ctor_index.get(&name) {
        if st.fixed_seen.insert(t) {
            st.fixed_terms.push((t, sort_idx, ctor));
        }
        return EnumOperand::Fixed {
            sort: sort_idx,
            ctor,
        };
    }
    if let Some(&row) = st.row_of.get(&t) {
        return EnumOperand::Colored { row };
    }
    let row = st.rows.len() as u32;
    st.rows.push(EnumRow {
        term: t,
        sort: sort_idx,
    });
    st.row_of.insert(t, row);
    EnumOperand::Colored { row }
}

/// Get-or-insert the atom entry for `t`.
fn enum_atom_entry(st: &mut ScanState, t: TermId, kind: EnumAtomKind) -> usize {
    if let Some(&idx) = st.atom_of.get(&t) {
        return idx;
    }
    let idx = st.atoms.len();
    st.atoms.push(EnumAtom {
        term: t,
        kind,
        unit_pos: false,
        unit_neg: false,
        skeleton: false,
    });
    st.atom_of.insert(t, idx);
    idx
}

/// Static comparison: identical terms / rows are equal; distinct constructor
/// constants of the same sort are semantically distinct in every model.
fn pair_status(a: EnumOperand, b: EnumOperand) -> PairStatus {
    match (a, b) {
        (EnumOperand::Fixed { sort: sa, ctor: ca }, EnumOperand::Fixed { sort: sb, ctor: cb }) => {
            debug_assert_eq!(sa, sb, "ill-sorted enum equality");
            if ca == cb {
                PairStatus::StaticEqual
            } else {
                PairStatus::StaticDistinct
            }
        }
        (EnumOperand::Colored { row: ra }, EnumOperand::Colored { row: rb }) if ra == rb => {
            PairStatus::StaticEqual
        }
        _ => PairStatus::Dynamic,
    }
}

/// Estimate of the lane's extra (non-Tseitin) clauses, mirroring the
/// per-shape emission costs (Colored/Fixed operands channel with O(1)
/// clauses, only Colored/Colored pairs pay the per-color factor). Slightly
/// over on shared n-ary-distinct pair variables (their 2k channel clauses
/// are counted per atom but emitted once); never under by more than the
/// handful of static short-circuit units.
fn estimate_extra_clauses(scan: &EnumSatScan) -> u64 {
    let k_of = |op: &EnumOperand, scan: &EnumSatScan| -> u64 {
        let sort = match op {
            EnumOperand::Fixed { sort, .. } => *sort,
            EnumOperand::Colored { row } => scan.rows[*row as usize].sort,
        };
        scan.sorts[sort as usize].ctors.len() as u64
    };
    // Dynamic pair cost: Colored/Colored pays `per_cc` clauses, any pair with
    // a Fixed side pays one, statically-decided pairs pay at most one unit.
    let pair_cost = |a: EnumOperand, b: EnumOperand, per_cc: u64, scan: &EnumSatScan| -> u64 {
        match pair_status(a, b) {
            PairStatus::StaticEqual | PairStatus::StaticDistinct => 1,
            PairStatus::Dynamic => match (a, b) {
                (EnumOperand::Colored { .. }, EnumOperand::Colored { .. }) => {
                    per_cc * k_of(&a, scan)
                }
                _ => 1,
            },
        }
    };
    let mut total: u64 = 0;
    for row in &scan.rows {
        let k = scan.sorts[row.sort as usize].ctors.len() as u64;
        let amo = if k as usize <= PAIRWISE_AMO_MAX {
            k * (k - 1) / 2
        } else {
            3 * k
        };
        total = total.saturating_add(1 + amo);
    }
    for atom in &scan.atoms {
        match &atom.kind {
            EnumAtomKind::Eq(a, b) => {
                if atom.skeleton {
                    total = total.saturating_add(pair_cost(*a, *b, 2, scan).max(2));
                }
                if atom.unit_pos {
                    total = total.saturating_add(pair_cost(*a, *b, 1, scan));
                }
                if atom.unit_neg {
                    total = total.saturating_add(pair_cost(*a, *b, 1, scan));
                }
            }
            EnumAtomKind::Distinct(ops) => {
                let n = ops.len() as u64;
                let pairs = n * (n - 1) / 2;
                let mut per_pos: u64 = 0;
                let mut per_chan: u64 = 0; // pair-var channel (2k per CC pair)
                for i in 0..ops.len() {
                    for j in (i + 1)..ops.len() {
                        per_pos = per_pos.saturating_add(pair_cost(ops[i], ops[j], 1, scan));
                        per_chan = per_chan.saturating_add(pair_cost(ops[i], ops[j], 2, scan));
                    }
                }
                if atom.unit_pos {
                    total = total.saturating_add(per_pos);
                }
                if atom.unit_neg {
                    total = total.saturating_add(per_chan + 1);
                }
                if atom.skeleton {
                    total = total.saturating_add(per_chan + pairs + 1);
                }
            }
        }
    }
    total
}

/// Extra-variable layout beyond the Tseitin block.
struct EnumVarPlan {
    /// 0-indexed base variable of each row's one-hot block.
    row_base: Vec<u32>,
    /// 0-indexed base of each row's Sinz sequential-AMO auxiliaries.
    sinz_base: Vec<Option<u32>>,
    /// Pair-equality variables for n-ary `distinct` channeling, keyed by
    /// ordered row pair.
    pair_vars: HashMap<(u32, u32), u32>,
    extra_vars: u32,
}

/// Allocate one-hot, Sinz, and pair variables after `tseitin_vars`
/// (Tseitin variables are 1-based; 0-indexed SAT variables `0..tseitin_vars`
/// belong to the skeleton).
fn plan_extra_vars(scan: &EnumSatScan, tseitin_vars: u32) -> EnumVarPlan {
    let mut next = tseitin_vars;
    let mut row_base = Vec::with_capacity(scan.rows.len());
    for row in &scan.rows {
        let k = scan.sorts[row.sort as usize].ctors.len() as u32;
        row_base.push(next);
        next += k;
    }
    let mut sinz_base = Vec::with_capacity(scan.rows.len());
    for row in &scan.rows {
        let k = scan.sorts[row.sort as usize].ctors.len();
        if k > PAIRWISE_AMO_MAX {
            sinz_base.push(Some(next));
            next += (k - 1) as u32;
        } else {
            sinz_base.push(None);
        }
    }
    // Pair variables: only n-ary `distinct` channeling needs named pair
    // equalities, and only for dynamic Colored/Colored pairs.
    let mut pair_vars: HashMap<(u32, u32), u32> = HashMap::default();
    for atom in &scan.atoms {
        let EnumAtomKind::Distinct(ops) = &atom.kind else {
            continue;
        };
        if !(atom.skeleton || atom.unit_neg) {
            continue;
        }
        if distinct_has_static_equal_pair(ops) {
            continue; // short-circuited at emit time — no pair vars needed
        }
        for i in 0..ops.len() {
            for j in (i + 1)..ops.len() {
                if let (EnumOperand::Colored { row: ra }, EnumOperand::Colored { row: rb }) =
                    (ops[i], ops[j])
                {
                    let key = (ra.min(rb), ra.max(rb));
                    pair_vars.entry(key).or_insert_with(|| {
                        let v = next;
                        next += 1;
                        v
                    });
                }
            }
        }
    }
    EnumVarPlan {
        row_base,
        sinz_base,
        pair_vars,
        extra_vars: next - tseitin_vars,
    }
}

fn distinct_has_static_equal_pair(ops: &[EnumOperand]) -> bool {
    for i in 0..ops.len() {
        for j in (i + 1)..ops.len() {
            if matches!(pair_status(ops[i], ops[j]), PairStatus::StaticEqual) {
                return true;
            }
        }
    }
    false
}

#[inline]
fn pos(v: u32) -> Literal {
    Literal::positive(Variable::new(v))
}

#[inline]
fn neg(v: u32) -> Literal {
    Literal::negative(Variable::new(v))
}

/// Where `emit_enum_clauses` sends the CNF it builds.
///
/// The lane runs the emitter twice: once into `Count`, to learn the exact
/// shape of the encoding it is about to build, and once into `Solver`, to
/// build it. Running the *same* code both times is the whole point — a
/// size formula written alongside the emitter is exactly the thing that drifts
/// out of sync with it (`estimate_extra_clauses` is such a formula, and its
/// own doc says it is approximate; it stays a budget gate, not a size).
enum EmitSink<'s> {
    Solver(&'s mut SatSolver),
    /// Upper bound on what the solver will store: clause count and total
    /// literal count as emitted, before the solver's own normalization drops
    /// duplicate literals, tautologies, and root-satisfied clauses. An upper
    /// bound is the right side to err on for a reservation.
    Count {
        clauses: usize,
        literals: usize,
    },
}

impl EmitSink<'_> {
    /// Mirrors `Solver::add_clause_reusing_buffer`, including that it leaves
    /// the buffer empty — every caller refills it before the next use, but
    /// matching the real sink keeps the two passes indistinguishable.
    fn add_clause_reusing_buffer(&mut self, lits: &mut Vec<Literal>) {
        match self {
            EmitSink::Solver(solver) => {
                solver.add_clause_reusing_buffer(lits);
            }
            EmitSink::Count { clauses, literals } => {
                *clauses += 1;
                *literals += lits.len();
                lits.clear();
            }
        }
    }

    fn add_clause(&mut self, lits: Vec<Literal>) {
        match self {
            EmitSink::Solver(solver) => {
                solver.add_clause(lits);
            }
            EmitSink::Count { clauses, literals } => {
                *clauses += 1;
                *literals += lits.len();
            }
        }
    }
}

/// Run the emitter into a counter to get the exact clause/literal shape of
/// this lane's encoding, without emitting anything.
fn count_enum_clauses(
    scan: &EnumSatScan,
    plan: &EnumVarPlan,
    tseitin: &Tseitin<'_>,
) -> (usize, usize) {
    let mut sink = EmitSink::Count {
        clauses: 0,
        literals: 0,
    };
    emit_enum_clauses(scan, plan, tseitin, &mut sink);
    match sink {
        EmitSink::Count { clauses, literals } => (clauses, literals),
        EmitSink::Solver(_) => unreachable!("counting sink cannot become a solver sink"),
    }
}

/// Emit the domain (exactly-one) and channeling clauses.
fn emit_enum_clauses(
    scan: &EnumSatScan,
    plan: &EnumVarPlan,
    tseitin: &Tseitin<'_>,
    solver: &mut EmitSink<'_>,
) {
    let mut buf: Vec<Literal> = Vec::with_capacity(16);
    let clause = |solver: &mut EmitSink<'_>, buf: &mut Vec<Literal>, lits: &[Literal]| {
        buf.clear();
        buf.extend_from_slice(lits);
        solver.add_clause_reusing_buffer(buf);
    };
    let x = |row: u32, c: u32| -> u32 { plan.row_base[row as usize] + c };
    let k_of_row = |row: u32| -> u32 {
        scan.sorts[scan.rows[row as usize].sort as usize]
            .ctors
            .len() as u32
    };

    if scan.static_conflict {
        // A top-level unit was statically false (constant `false` assertion
        // or `(= c_i c_j)` between distinct constructors): the conjunction is
        // UNSAT in every model. The empty clause is conflict-exact.
        solver.add_clause(Vec::new());
    }

    // --- Exactly-one per row (domain closure, both directions). ---
    for r in 0..scan.rows.len() as u32 {
        let k = k_of_row(r);
        debug_assert!(k >= 1);
        // At-least-one.
        buf.clear();
        for c in 0..k {
            buf.push(pos(x(r, c)));
        }
        solver.add_clause_reusing_buffer(&mut buf);
        // At-most-one.
        match plan.sinz_base[r as usize] {
            None => {
                for c1 in 0..k {
                    for c2 in (c1 + 1)..k {
                        clause(solver, &mut buf, &[neg(x(r, c1)), neg(x(r, c2))]);
                    }
                }
            }
            Some(sb) => {
                // Sinz sequential AMO: s_i := "some x_j with j <= i is true"
                // (definitional prefix-OR auxiliaries, k-1 of them).
                let s = |i: u32| -> u32 { sb + i };
                for i in 0..(k - 1) {
                    clause(solver, &mut buf, &[neg(x(r, i)), pos(s(i))]);
                }
                for i in 1..(k - 1) {
                    clause(solver, &mut buf, &[neg(s(i - 1)), pos(s(i))]);
                }
                for i in 1..k {
                    clause(solver, &mut buf, &[neg(x(r, i)), neg(s(i - 1))]);
                }
            }
        }
    }

    // --- Pair-equality variables (n-ary distinct channeling): e <-> (a = b).
    for (&(ra, rb), &e) in plan.pair_vars.iter() {
        let k = k_of_row(ra);
        debug_assert_eq!(k, k_of_row(rb));
        for c in 0..k {
            // e -> (a=c -> b=c)
            clause(solver, &mut buf, &[neg(e), neg(x(ra, c)), pos(x(rb, c))]);
            // (a=c and b=c) -> e
            clause(solver, &mut buf, &[pos(e), neg(x(ra, c)), neg(x(rb, c))]);
        }
    }

    // --- Atom channeling. ---
    for atom in &scan.atoms {
        // Tseitin variable of the atom (1-based); needed for skeleton
        // channeling only. Unit-only atoms keep their unit-asserted Tseitin
        // variable and get direction-of-polarity semantic clauses instead
        // (Plaisted-Greenbaum at the leaves; see module docs).
        let tvar: Option<u32> = tseitin.term_to_var().get(&atom.term).map(|&v| v - 1);
        match &atom.kind {
            EnumAtomKind::Eq(a, b) => {
                emit_eq_atom(scan, plan, solver, &mut buf, atom, *a, *b, tvar);
            }
            EnumAtomKind::Distinct(ops) => {
                emit_distinct_atom(scan, plan, solver, &mut buf, atom, ops, tvar);
            }
        }
    }
}

/// Emit clauses for one `(= a b)` atom under its polarity needs.
#[allow(clippy::too_many_arguments)]
fn emit_eq_atom(
    scan: &EnumSatScan,
    plan: &EnumVarPlan,
    solver: &mut EmitSink<'_>,
    buf: &mut Vec<Literal>,
    atom: &EnumAtom,
    a: EnumOperand,
    b: EnumOperand,
    tvar: Option<u32>,
) {
    let clause = |solver: &mut EmitSink<'_>, buf: &mut Vec<Literal>, lits: &[Literal]| {
        buf.clear();
        buf.extend_from_slice(lits);
        solver.add_clause_reusing_buffer(buf);
    };
    let x = |row: u32, c: u32| -> u32 { plan.row_base[row as usize] + c };

    match pair_status(a, b) {
        PairStatus::StaticEqual => {
            if atom.skeleton {
                if let Some(v) = tvar {
                    clause(solver, buf, &[pos(v)]);
                }
            }
            if atom.unit_neg {
                solver.add_clause(Vec::new()); // asserted false, statically true
            }
        }
        PairStatus::StaticDistinct => {
            if atom.skeleton {
                if let Some(v) = tvar {
                    clause(solver, buf, &[neg(v)]);
                }
            }
            if atom.unit_pos {
                solver.add_clause(Vec::new()); // asserted true, statically false
            }
        }
        PairStatus::Dynamic => match (a, b) {
            (EnumOperand::Colored { row: ra }, EnumOperand::Colored { row: rb }) => {
                let k = scan.sorts[scan.rows[ra as usize].sort as usize].ctors.len() as u32;
                if atom.skeleton {
                    let v = tvar.expect("skeleton atom must have a Tseitin variable");
                    for c in 0..k {
                        clause(solver, buf, &[neg(v), neg(x(ra, c)), pos(x(rb, c))]);
                        clause(solver, buf, &[pos(v), neg(x(ra, c)), neg(x(rb, c))]);
                    }
                } else {
                    if atom.unit_pos {
                        for c in 0..k {
                            clause(solver, buf, &[neg(x(ra, c)), pos(x(rb, c))]);
                        }
                    }
                    if atom.unit_neg {
                        for c in 0..k {
                            clause(solver, buf, &[neg(x(ra, c)), neg(x(rb, c))]);
                        }
                    }
                }
            }
            (EnumOperand::Colored { row }, EnumOperand::Fixed { ctor, .. })
            | (EnumOperand::Fixed { ctor, .. }, EnumOperand::Colored { row }) => {
                let xt = x(row, ctor);
                if atom.skeleton {
                    let v = tvar.expect("skeleton atom must have a Tseitin variable");
                    clause(solver, buf, &[neg(v), pos(xt)]);
                    clause(solver, buf, &[pos(v), neg(xt)]);
                } else {
                    if atom.unit_pos {
                        clause(solver, buf, &[pos(xt)]);
                    }
                    if atom.unit_neg {
                        clause(solver, buf, &[neg(xt)]);
                    }
                }
            }
            (EnumOperand::Fixed { .. }, EnumOperand::Fixed { .. }) => {
                unreachable!("Fixed/Fixed pairs are statically decided")
            }
        },
    }
}

/// Emit clauses for one `(distinct ...)` atom under its polarity needs.
fn emit_distinct_atom(
    scan: &EnumSatScan,
    plan: &EnumVarPlan,
    solver: &mut EmitSink<'_>,
    buf: &mut Vec<Literal>,
    atom: &EnumAtom,
    ops: &[EnumOperand],
    tvar: Option<u32>,
) {
    let clause = |solver: &mut EmitSink<'_>, buf: &mut Vec<Literal>, lits: &[Literal]| {
        buf.clear();
        buf.extend_from_slice(lits);
        solver.add_clause_reusing_buffer(buf);
    };
    let x = |row: u32, c: u32| -> u32 { plan.row_base[row as usize] + c };
    let k_of = |op: &EnumOperand| -> u32 {
        let sort = match op {
            EnumOperand::Fixed { sort, .. } => *sort,
            EnumOperand::Colored { row } => scan.rows[*row as usize].sort,
        };
        scan.sorts[sort as usize].ctors.len() as u32
    };

    let has_static_equal = distinct_has_static_equal_pair(ops);

    // Positive top-level unit: every pair must disagree.
    if atom.unit_pos {
        if has_static_equal {
            solver.add_clause(Vec::new()); // e.g. (distinct t t) — false in every model
        } else {
            for i in 0..ops.len() {
                for j in (i + 1)..ops.len() {
                    match (ops[i], ops[j]) {
                        (EnumOperand::Colored { row: ra }, EnumOperand::Colored { row: rb }) => {
                            let k = k_of(&ops[i]);
                            for c in 0..k {
                                clause(solver, buf, &[neg(x(ra, c)), neg(x(rb, c))]);
                            }
                        }
                        (EnumOperand::Colored { row }, EnumOperand::Fixed { ctor, .. })
                        | (EnumOperand::Fixed { ctor, .. }, EnumOperand::Colored { row }) => {
                            clause(solver, buf, &[neg(x(row, ctor))]);
                        }
                        _ => {} // StaticDistinct Fixed/Fixed: nothing to do
                    }
                }
            }
        }
    }

    // Pair-equality literal for the channeled forms (None = statically
    // distinct pair, i.e. the conjunct `a != b` is vacuously true).
    let pair_lit = |i: usize, j: usize| -> Option<Literal> {
        match (ops[i], ops[j]) {
            (EnumOperand::Colored { row: ra }, EnumOperand::Colored { row: rb }) => {
                let key = (ra.min(rb), ra.max(rb));
                Some(pos(plan.pair_vars[&key]))
            }
            (EnumOperand::Colored { row }, EnumOperand::Fixed { ctor, .. })
            | (EnumOperand::Fixed { ctor, .. }, EnumOperand::Colored { row }) => {
                Some(pos(x(row, ctor)))
            }
            _ => None,
        }
    };

    // Negated top-level unit: at least one pair agrees.
    if atom.unit_neg && !has_static_equal {
        buf.clear();
        let mut lits: Vec<Literal> = Vec::new();
        for i in 0..ops.len() {
            for j in (i + 1)..ops.len() {
                if let Some(l) = pair_lit(i, j) {
                    lits.push(l);
                }
            }
        }
        // All pairs statically distinct: `(not (distinct ...))` is false in
        // every model; the empty clause is exact.
        buf.extend_from_slice(&lits);
        solver.add_clause_reusing_buffer(buf);
    }

    // Skeleton: d <-> AND over pairs of (a != b).
    if atom.skeleton {
        let d = tvar.expect("skeleton atom must have a Tseitin variable");
        if has_static_equal {
            clause(solver, buf, &[neg(d)]);
        } else {
            let mut back: Vec<Literal> = vec![pos(d)];
            for i in 0..ops.len() {
                for j in (i + 1)..ops.len() {
                    if let Some(l) = pair_lit(i, j) {
                        // d -> pair disagrees
                        clause(solver, buf, &[neg(d), l.negated()]);
                        back.push(l);
                    }
                }
            }
            // all pairs disagree -> d
            buf.clear();
            buf.extend_from_slice(&back);
            solver.add_clause_reusing_buffer(buf);
        }
    }
}

/// Decode the SAT assignment into a normal `EufModel`: elements are the
/// constructor names, every collected term gets its decoded (or fixed)
/// constructor, and admitted UF applications additionally populate their
/// function table row.
fn decode_enum_model(
    exec: &Executor,
    scan: &EnumSatScan,
    plan: &EnumVarPlan,
    sat_model: &[bool],
) -> EufModel {
    let mut euf = EufModel::default();
    for info in &scan.sorts {
        euf.sort_elements
            .insert(info.name.clone(), info.ctors.clone());
    }
    // Constructor constants denote themselves.
    for &(t, sort, ctor) in &scan.fixed_terms {
        euf.term_values
            .insert(t, scan.sorts[sort as usize].ctors[ctor as usize].clone());
    }
    // Colored rows: the unique true one-hot picks the constructor.
    let mut row_color: Vec<u32> = Vec::with_capacity(scan.rows.len());
    for (r, row) in scan.rows.iter().enumerate() {
        let k = scan.sorts[row.sort as usize].ctors.len() as u32;
        let base = plan.row_base[r];
        let mut chosen: Option<u32> = None;
        for c in 0..k {
            if sat_model.get((base + c) as usize).copied().unwrap_or(false) {
                debug_assert!(chosen.is_none(), "exactly-one violated in SAT model");
                chosen = Some(c);
                if !cfg!(debug_assertions) {
                    break;
                }
            }
        }
        // At-least-one guarantees a color; default 0 keeps the decode total
        // (the model gates re-verify every assertion regardless).
        let c = chosen.unwrap_or(0);
        row_color.push(c);
        euf.term_values.insert(
            row.term,
            scan.sorts[row.sort as usize].ctors[c as usize].clone(),
        );
    }
    // Function tables for admitted UF applications.
    for (r, row) in scan.rows.iter().enumerate() {
        let TermData::App(sym, args) = exec.ctx.terms.get(row.term) else {
            continue;
        };
        if args.is_empty() {
            continue;
        }
        let arg_names: Vec<String> = args
            .iter()
            .map(|&a| {
                euf.term_values
                    .get(&a)
                    .cloned()
                    .unwrap_or_else(|| format!("@?{}", a.0))
            })
            .collect();
        let result_name = scan.sorts[row.sort as usize].ctors[row_color[r] as usize].clone();
        euf.function_tables
            .entry(sym.name().to_string())
            .or_default()
            .push((arg_names, result_name));
    }
    euf
}
