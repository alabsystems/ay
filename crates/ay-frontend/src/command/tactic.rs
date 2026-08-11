// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Parsed `(apply <tactic>)` tactic expressions (Z3 tactic surface).
//!
//! `(apply <tactic>)` applies a goal-to-goal tactic to the *current* goal (the
//! set of assertions) and prints the resulting goal(s) — it never emits a
//! sat/unsat verdict and never mutates the real assertion stack.
//!
//! This module is the parser-level representation of the tactic argument AND
//! the single **shared tactic-name registry** for the *equivalence-preserving,
//! faithfully-printable* fragment of AY's Z3-compatible tactic surface. Both
//! entry points resolve those names through the *same* [`ApplyTactic::parse`]:
//!
//! - the SMT-LIB `(apply <name>)` executor
//!   (`ay_dpll::executor::Executor::apply_tactic_goal`), and
//! - the C-API / `ayz3` `Tactic('<name>')` path (`Z3_mk_tactic`).
//!
//! Because both funnel through this one parser, the recognized name set can
//! never drift between the two surfaces (see [`SUPPORTED_TACTIC_NAMES`]).
//!
//! # Recognized primitive names (real Z3 tactic names, each backed by a real pass)
//!
//! Every recognized primitive corresponds to a genuine Z3 tactic and maps (in
//! `ay_dpll::api::Tactic::from_apply`) to a real transformation whose subgoals'
//! *disjunction* has exactly the same models as the input assertions (with the
//! sole exception of `tseitin-cnf`, which is equisatisfiable — it introduces
//! fresh existential aux variables — so it preserves `check-sat` rather than the
//! model set):
//!
//! - `skip` — the identity.
//! - `fail` — the always-failing tactic (Z3's `fail`): produces no goal, an
//!   honest `(error "tactic failed: ...")` — never a fabricated result.
//! - `simplify` — simplify each formula and split top-level conjunctions.
//! - `solve-eqs` — solve variable equalities and eliminate the solved variables.
//! - `propagate-values` — propagate ground `(= expr const)` equalities.
//! - `elim-and` — Z3's and-elimination; AY realizes it with its `FlattenAnd`
//!   pass (top-level conjunctions are split into separate goal formulas).
//! - `qe-light` — Z3's light quantifier elimination (AY's Cooper `QeLight` pass).
//! - `qe` — Z3's quantifier-elimination tactic, realized by the SAME Cooper
//!   pass as `qe-light`: every in-fragment single-Int-variable existential is
//!   eliminated (each substitution gated by Cooper's independent equivalence
//!   self-check), and every out-of-fragment quantifier is kept VERBATIM — the
//!   identity is equivalence-preserving, so the printed goal is always sound.
//!   This is a documented sound divergence from z3, whose `qe` is complete for
//!   LIA (it also eliminates multi-variable and universal quantifiers).
//! - `nnf` — Z3's negation-normal-form tactic (AY's `Nnf` pass): push negations
//!   inward to atoms and eliminate `=>`/`<->`/`xor`/`ite`-over-Bool into
//!   `and`/`or`, then split the resulting top-level conjunction into goal
//!   formulas. Equivalence-preserving.
//! - `tseitin-cnf` — Z3's Tseitin CNF conversion. The ONE tactic
//!   here that is *equisatisfiable but not equivalent*: it mints fresh auxiliary
//!   Boolean variables, so the CNF's models differ from the input's on those new
//!   variables while `check-sat` is preserved (aux treated as free).
//! - `bit-blast` — Z3's `bit-blast` tactic (AY's `BitBlast` pass): replace every
//!   bit-vector variable with `n` fresh Boolean bit-variables and every BV
//!   operator with its Boolean circuit, producing a pure-Boolean (SAT-level)
//!   goal with no BV terms for the supported fragment. Equisatisfiable. If the
//!   goal contains a BV construct outside the supported fragment, the pass
//!   HONESTLY FAILS (a `(error "tactic failed: … not supported by bit-blast")`),
//!   never a fabricated or silent-identity blast.
//! - `split-clause` — Z3's clause split: pick the first top-level disjunction
//!   `(or c1 … cn)` and produce **n subgoals**, one per disjunct (the other
//!   assertions carried through unchanged). The disjunction of the subgoals is
//!   *equivalent* to the input — a genuine sound case split.
//! - `propagate-ineqs` — Z3's inequality/bound propagation, realized as a
//!   bound-subsumption pass: drop inequalities implied by a retained
//!   same-strictness bound on the same variable or by an asserted
//!   `(= var const)` equality; value equalities are re-emitted at the end of
//!   the goal. Only drops and reorders — equivalence-preserving.
//!
//! # Full-registry names (the pinned Z3 5.0.0 batch) and their honest realizations
//!
//! Beyond the pass-backed primitives above, this registry recognizes EVERY
//! remaining Z3 5.0.0 tactic name (`z3 -tactics` lists 118). Each name has one
//! of four SOUND realizations — none
//! adds a decide path, and none can ever change a verdict:
//!
//! - **CLASS S — solver-strategy tactics → identity (`Skip`)** (`qflia`, `qfbv`,
//!   `smtfd`, `nlsat`, …): z3 runs the whole named strategy inside `(apply)`
//!   (usually emptying the goal); AY truthfully prints the goal unchanged and
//!   runs its REAL engine when the tactic is used as a solver
//!   (`check-sat-using`, `Z3_mk_solver_from_tactic`). Documented divergence:
//!   goal shape (and `:depth`) only, never the verdict.
//! - **CLASS A — alias to an existing verified pass** (`qe2`→`qe`,
//!   `ctx-simplify`→`ctx-solver-simplify`, `card2bv`→`simplify`, …): each alias
//!   inherits an already-shipped equivalence/equisat-preserving pass.
//! - **CLASS N — no-op-safe transforms → identity (`Skip`)**
//!   (`ackermannize_bv`, `fpa2bv`, `lia2pb`, `collect-statistics`, …): z3
//!   leaves the goal formulas unchanged on out-of-fragment goals (measured
//!   per-name, 2026-07-18 sweep); AY is the identity everywhere — a sound,
//!   documented identity, NEVER a fabricated transform. Note the `:depth`
//!   divergence: z3 counts its no-op pass (depth 1), AY's `Skip` stays at
//!   depth 0. Special cases (measured): `subpaving` z3 TRANSFORMS in-fragment
//!   Int goals and FAILS BV goals; `elim-predicates`/`euf-completion` z3
//!   DECIDES the BV probe (empties the goal); `nla2bv` z3 FAILS BV goals and
//!   is UNDER-approximating on Int goals; `add-bounds` is under-approximating
//!   and `normalize-bounds` mints fresh `k!i` variables in-fragment. AY stays
//!   precise-identity for all of these — strictly more precise, zero
//!   wrong-goal risk.
//! - **CLASS F — fragment-failure tactics → honest failure** (`diff-neq`,
//!   `nlqsat`, `pb2bv`, `horn`, `horn-simplify`, and the conditional
//!   `bv1-blast`): z3 FAILS these on generic goals (measured), so failing
//!   preserves `or-else` routing. `bv1-blast` is special (measured): z3
//!   SUCCEEDS as the identity on BV-free goals and fails only on goals with
//!   BV terms, so AY fails IFF the goal contains a bit-vector term and is the
//!   identity otherwise.
//! - **CLASS C** — `fail-if-undecided` wires to the real engine primitive
//!   (identity on a trivially-decided goal, honest `undecided` failure else).
//!
//! # Combinators (Z3's tactic combinator grammar)
//!
//! - `(then t1 t2 …)` / `(and-then t1 t2 …)` — sequential composition.
//! - `(or-else t1 t2 …)` — try `t1`; if it *fails*, try `t2`, and so on.
//! - `(par-then t1 t2)` / `(par-or t1 t2 …)` — Z3's parallel combinators;
//!   composed sequentially here (documented), same result set.
//! - `(repeat t)` / `(repeat t n)` — apply until fixpoint (or `n` iterations).
//! - `(try-for t ms)` — apply `t` (Z3 attaches a wall-clock bound; AY's passes
//!   are already bounded, so it reduces to `t`).
//! - `(using-params t :k v …)` / `(with t :k v …)` / `(! t :k v …)` —
//!   parameters to a tactic; AY always applies the equivalence-preserving
//!   transform, so shape-only params are parsed and ignored (documented sound
//!   divergence). `!` is z3's annotation spelling of `using-params`.
//! - `(when p t)` — apply `t` iff probe `p` holds, else `skip`.
//! - `(fail-if p)` — fail iff probe `p` holds, else `skip`.
//! - `(if p t1 t2)` / `(cond p t1 t2)` — apply `t1` iff probe `p` holds, else
//!   `t2`; exactly three arguments (z3 arity), and a failure of the CHOSEN
//!   branch propagates (no fall-through — measured z3 semantics).
//!
//! An unknown tactic name is a parse error (matching Z3, which rejects
//! `(apply no-such-tactic)`), never a silently-accepted empty goal. Notably a
//! name Z3 itself does not have — e.g. `flatten-and` — is rejected here too.

use crate::sexp::{ParseError, SExpr};

/// The canonical set of bare Z3 tactic names AY's tactic surface recognizes as
/// `Z3_mk_tactic("<name>")` / `(apply <name>)`.
///
/// This slice is the single source of truth for the *primitive* tactics shared
/// by both the SMT-LIB `(apply <name>)` path and the C-API `Z3_mk_tactic` path.
/// Combinators (`then`, `or-else`, `repeat`, …) are only usable in the
/// S-expression list form, exactly as in Z3, so they are not listed here.
/// Anything not recognized is an honest error, never a silent identity.
pub const SUPPORTED_TACTIC_NAMES: &[&str] = &[
    "skip",
    "fail",
    "simplify",
    "solve-eqs",
    "propagate-values",
    "elim-and",
    "qe-light",
    "qe",
    "nnf",
    "tseitin-cnf",
    "bit-blast",
    "split-clause",
    "ctx-solver-simplify",
    "propagate-ineqs",
    // Names z3 exposes as dedicated tactics that AY realizes by REDUCING to an
    // existing equisatisfiability-preserving pass (documented in `tactic_descr`).
    // Each is accepted and does a real equisat transform — never a fabricated
    // result — it is simply AY's general pass rather than z3's specialized one.
    "purify-arith",
    "elim-uncnstr",
    // Small self-contained z3 goal transforms, each backed by a real AY pass.
    // `cofactor-term-ite` is an ALIAS of `blast-term-ite` (same Shannon ITE
    // lift; documented condition-order/simplification divergence from z3).
    "elim-term-ite",
    "blast-term-ite",
    "cofactor-term-ite",
    "der",
    "distribute-forall",
    "reduce-args",
    // Terminal "solve" tactics (z3's smt/sat engines and default strategy). As a
    // goal transform they are the identity; turned into a solver they run AY's
    // real engine. They exist so `Then('simplify','smt').solver()` — the standard
    // z3py custom-solver idiom — builds. See `parse_name`.
    "smt",
    "default",
    "sat",
    // ------------------------------------------------------------------
    // CLASS S — per-logic solver strategies, realized like `smt`/`default`/
    // `sat` above: identity as a goal transform, the REAL engine as a solver.
    // ------------------------------------------------------------------
    "auflia",
    "auflira",
    "aufnira",
    "bv",
    "lia",
    "lira",
    "lra",
    "nlsat",
    "nra",
    "pqffd",
    "psat",
    "psmt",
    "qfaufbv",
    "qfauflia",
    "qfbv",
    "qfbv-sls",
    "qffd",
    "qffp",
    "qffpbv",
    "qffplra",
    "qfidl",
    "qflia",
    "qflra",
    "qfnia",
    "qfnra",
    "qfnra-nlsat",
    "qfuf",
    "qfufbv",
    "qfufbv_ackr",
    "qsat",
    "sls-smt",
    "smtfd",
    "ufbv",
    "uflra",
    "ufnia",
    // ------------------------------------------------------------------
    // CLASS A — aliases to an existing verified AY pass (see `parse_name`).
    // ------------------------------------------------------------------
    "propagate-values2",
    "reduce-args2",
    "elim-uncnstr2",
    "tseitin-cnf-core",
    "sat-preprocess",
    "qe2",
    "qe_rec",
    "ctx-simplify",
    "unit-subsume-simplify",
    "solver-subsumption",
    "dom-simplify",
    "degree-shift",
    "fm",
    "card2bv",
    // ------------------------------------------------------------------
    // CLASS N — no-op-safe goal transforms realized as the identity (per-name
    // measured against z3 4.15.4; see the module docs for the special cases).
    // ------------------------------------------------------------------
    "ackermannize_bv",
    "add-bounds",
    "aig",
    "bv_bound_chk",
    "bv-slice",
    "bv-divrem-bounds",
    "bvarray2uf",
    "collect-statistics",
    "demodulator",
    "dt2bv",
    "elim-predicates",
    "elim-small-bv",
    "eq2bv",
    "euf-completion",
    "fold-unfold",
    "factor",
    "fix-dl-var",
    "fpa2bv",
    "injectivity",
    "lia2card",
    "lia2pb",
    "macro-finder",
    "max-bv-sharing",
    "nla2bv",
    "normalize-bounds",
    "occf",
    "pb-preprocess",
    "propagate-bv-bounds",
    "propagate-bv-bounds2",
    "quasi-macros",
    "recover-01",
    "reduce-bv-size",
    "snf",
    "special-relations",
    "subpaving",
    "symmetry-reduce",
    "ufbv-rewriter",
    // ------------------------------------------------------------------
    // CLASS F — fragment tactics realized as an HONEST failure (z3 fails these
    // on generic goals too — measured; `bv1-blast` fails iff the goal has BV
    // terms and is the identity otherwise, matching z3's measured behavior).
    // ------------------------------------------------------------------
    "diff-neq",
    "nlqsat",
    "pb2bv",
    "horn",
    "horn-simplify",
    "bv1-blast",
    // CLASS C — wired to the real engine primitive `Tactic::FailIfNotDecided`.
    "fail-if-undecided",
];

/// A value supplied to a tactic parameter (`using-params`/`with`).
///
/// AY's tactics are always the equivalence-preserving transform, so parameters
/// that would only affect output *shape* (not the model set) are parsed for
/// fidelity and then ignored — this type just records what was written.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ParamValue {
    /// A Boolean parameter value (`:elim_and true`).
    Bool(bool),
    /// An integer parameter value (`:max_depth 4`).
    Int(i64),
    /// A symbolic/decimal/other parameter value, kept verbatim as written.
    Sym(String),
}

/// A Z3 *probe* — a numeric query over the goal used by `when` / `fail-if`.
///
/// Probes evaluate to a number over the current goal; boolean probes yield
/// `1`/`0`. The registry covers EVERY probe name z3 4.15.4 exposes (42 names,
/// `z3 -probes`), so any z3-valid `when`/`fail-if`/`if`/`cond` script parses.
/// Evaluation is honest where AY can compute the value cheaply and exactly;
/// the remaining probes evaluate CONSERVATIVELY (documented per variant, and
/// in `Z3_probe_get_descr`). A conservative probe value can only shift which
/// of two SOUND tactics a combinator picks — it can never flip a verdict.
///
/// NOT `#[non_exhaustive]`: the engine evaluator matches exhaustively, so a
/// newly added probe without an evaluation arm is a COMPILE ERROR, never a
/// silent constant.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Probe {
    /// A numeric literal, kept as its source text (parsed to a number at
    /// evaluation time). Stored as text so the whole tactic AST stays `Eq`.
    Const(String),
    /// Number of distinct NON-Boolean uninterpreted constants in the goal
    /// (`num-consts`). Matches Z3, which excludes Boolean-sorted constants.
    NumConsts,
    /// Number of distinct sub-expression nodes in the goal (`num-exprs`),
    /// computed over the goal's formulas AFTER Z3-style top-level-conjunction
    /// splitting (so a top-level `and` node is not counted).
    NumExprs,
    /// Number of formulas (assertions) in the goal (`size`), counted after
    /// Z3-style top-level-conjunction splitting (`(and A B)` reads as `size = 2`).
    Size,
    /// Z3 goal *depth* (`depth`): the number of primitive tactic applications
    /// that produced the goal. A freshly built goal (before any tactic) has
    /// depth `0`.
    Depth,
    /// Number of distinct Boolean-sorted uninterpreted constants (`num-bool-consts`).
    NumBoolConsts,
    /// Number of distinct Int/Real-sorted uninterpreted constants
    /// (`num-arith-consts`).
    NumArithConsts,
    /// Number of distinct bit-vector-sorted uninterpreted constants
    /// (`num-bv-consts`).
    NumBvConsts,
    /// `1` if the goal contains a quantifier, else `0` (`has-quantifiers`).
    HasQuantifiers,
    /// `1` if the goal is purely propositional — only Boolean sorts, no
    /// arithmetic / bit-vectors / arrays / uninterpreted functions
    /// (`is-propositional`).
    IsPropositional,
    /// `1` if the goal is in the QF_BV fragment (`is-qfbv`).
    IsQfbv,
    /// `1` if the goal is in the QF_LIA fragment (`is-qflia`).
    IsQflia,
    /// `1` if the goal is in the QF_LRA fragment (`is-qflra`).
    IsQflra,
    /// `1` if the goal is in the QF_LIRA fragment (`is-qflira`).
    IsQflira,
    /// `1` if the goal is in the LIA fragment (linear integer, quantifiers
    /// allowed) (`is-lia`).
    IsLia,
    /// `1` if the goal is in the LRA fragment (linear real, quantifiers
    /// allowed) (`is-lra`).
    IsLra,
    /// `1` if the goal is in the LIRA fragment (linear int+real, quantifiers
    /// allowed) (`is-lira`).
    IsLira,
    /// `1` if the goal is in the QF_NIA fragment — quantifier-free nonlinear
    /// integer arithmetic (`is-qfnia`).
    IsQfnia,
    /// `1` if the goal is in the QF_NRA fragment — quantifier-free nonlinear
    /// real arithmetic (`is-qfnra`).
    IsQfnra,
    /// `1` if the goal is in the NIA fragment — nonlinear integer, quantifiers
    /// allowed (`is-nia`).
    IsNia,
    /// `1` if the goal is in the NRA fragment — nonlinear real, quantifiers
    /// allowed (`is-nra`).
    IsNra,
    /// `1` if the goal contains a quantifier carrying patterns/triggers
    /// (`has-patterns`). HONEST: AY quantifier terms store their triggers, so
    /// this is computed exactly.
    HasPatterns,
    /// `1` if the goal is an integer linear program (`is-ilp`): quantifier-free
    /// linear integer arithmetic with no Boolean/other structure (measured z3
    /// semantics: Boolean constants disqualify; the empty goal qualifies).
    IsIlp,
    /// `1` if the goal is in the NIRA fragment (`is-nira`). Measured z3
    /// semantics: requires genuinely NONLINEAR int/real arithmetic (a linear
    /// goal reads 0).
    IsNira,
    /// `1` if the goal is pseudo-boolean (`is-pb`). AY evaluates the measured
    /// propositional core (z3 reads 1 on propositional goals); documented
    /// conservative under-approximation for 0/1-bounded integer PB goals.
    IsPb,
    /// `1` if the goal is quasi-pseudo-boolean (`is-quasi-pb`). CONSERVATIVE
    /// under-approximation: the propositional core (documented).
    IsQuasiPb,
    /// `1` if the goal is in QF_AUFBV (`is-qfaufbv`). AY evaluates the
    /// bool/BV core (arrays/UF read 0 — documented under-approximation).
    IsQfaufbv,
    /// `1` if the goal is in QF_AUFLIA (`is-qfauflia`). AY evaluates the
    /// bool/LIA core (arrays/UF read 0 — documented under-approximation).
    IsQfauflia,
    /// `1` if the goal is a QF_BV equation goal (`is-qfbv-eq`). Measured z3
    /// semantics: quantifier-free goals WITHOUT bit-vector arithmetic read 1
    /// (even pure-arith goals); AY reads 0 on any BV-term goal — a documented
    /// conservative under-approximation for pure =/concat/extract BV goals.
    IsQfbvEq,
    /// `1` if the goal is in QF_FP (`is-qffp`). Measured z3 semantics accept
    /// the bool/BV core (FP-free goals read 1); AY evaluates exactly that core
    /// and reads 0 on genuine FP terms (documented under-approximation).
    IsQffp,
    /// `1` if the goal is in QF_FPBV (`is-qffpbv`). Same evaluation as
    /// [`Probe::IsQffp`] (measured identical on the probe battery).
    IsQffpbv,
    /// `1` if the goal is in QF_FPLRA (`is-qffplra`). CONSERVATIVE constant 0
    /// (measured: z3 reads 0 even on the empty and pure-LRA goals; AY cannot
    /// classify FP terms and never claims membership).
    IsQffplra,
    /// `1` if the goal is in QF_UFNRA (`is-qfufnra`). AY evaluates the
    /// nonlinear-real core (UF goals read 0 — documented under-approximation).
    IsQfufnra,
    /// `1` if the goal contains an Int/Real constant with no derived
    /// lower/upper bound (`is-unbounded`). AY scans the top-level atoms for
    /// `var <op> numeral` bounds (quantified goals read 0, matching the
    /// measured z3 battery); a documented approximation of z3's bound manager.
    IsUnbounded,
    /// Upper bound on the Ackermann congruence lemmas the goal could generate
    /// (`ackr-bound-probe`): Σ over uninterpreted functions of C(n,2) for the
    /// n distinct applications of each. HONEST: computed from the real goal.
    AckrBoundProbe,
    /// Average coefficient bit width over the goal's arithmetic numerals
    /// (`arith-avg-bw`). Computed from the real numerals (documented
    /// approximation of z3's coefficient harvesting).
    ArithAvgBw,
    /// Max coefficient bit width over the goal's arithmetic numerals
    /// (`arith-max-bw`).
    ArithMaxBw,
    /// Average polynomial total degree of the goal's arithmetic atom sides
    /// (`arith-avg-deg`).
    ArithAvgDeg,
    /// Max polynomial total degree of the goal's arithmetic atom sides
    /// (`arith-max-deg`).
    ArithMaxDeg,
    /// Megabytes of memory in use (`memory`). CONSERVATIVE constant 0: AY does
    /// not meter allocator usage and never fabricates a reading (documented).
    Memory,
    /// `1` if model generation is enabled for the goal (`produce-model`).
    /// AY goals always support model extraction, matching z3's default goal.
    ProduceModel,
    /// `1` if proof generation is enabled for the goal (`produce-proofs`).
    /// AY apply-goals never carry proof mode, matching z3's default goal (0).
    ProduceProofs,
    /// `1` if unsat-core generation is enabled for the goal
    /// (`produce-unsat-cores`). AY apply-goals never carry core mode, matching
    /// z3's default goal (0).
    ProduceUnsatCores,
    /// Logical negation of a probe.
    Not(Box<Probe>),
    /// Logical conjunction of two probes.
    And(Box<Probe>, Box<Probe>),
    /// Logical disjunction of two probes.
    Or(Box<Probe>, Box<Probe>),
    /// A numeric comparison between two probes.
    Cmp(ProbeCmp, Box<Probe>, Box<Probe>),
}

/// A probe comparison operator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProbeCmp {
    /// `<`
    Lt,
    /// `<=`
    Le,
    /// `>`
    Gt,
    /// `>=`
    Ge,
    /// `=`
    Eq,
}

/// A parsed Z3-style tactic expression — the argument of `(apply <tactic>)`.
///
/// Each variant corresponds to a real Z3 tactic name/combinator and, through
/// `ay_dpll::api::Tactic::from_apply`, to a real goal-to-goal transformation.
/// The set is a deliberate, sound subset of Z3's tactic surface; anything
/// outside it is a parse error rather than a fabricated result.
///
/// NOT `#[non_exhaustive]`: `Tactic::from_apply` matches exhaustively, so a
/// newly added variant without an explicit engine mapping is a COMPILE ERROR
/// — never a silent fall-through to the identity (which would convert an
/// honest-failure tactic into a silent success and defeat `or-else` routing).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ApplyTactic {
    /// `skip` — the identity tactic. Leaves the goal unchanged (depth 0).
    Skip,
    /// `fail` — the always-failing tactic. Yields no goal; the surface reports
    /// an honest `(error "tactic failed: ...")`.
    Fail,
    /// `simplify` — simplify each formula and split top-level conjunctions.
    Simplify,
    /// `solve-eqs` — solve variable equalities and eliminate the solved
    /// variables by substitution.
    SolveEqs,
    /// `propagate-values` — propagate ground `(= expr const)` equalities.
    PropagateValues,
    /// `elim-and` — Z3's and-elimination (AY's `FlattenAnd` pass).
    ElimAnd,
    /// `qe-light` — Z3's light quantifier elimination (AY's Cooper `QeLight`).
    QeLight,
    /// `qe` — Z3's quantifier-elimination tactic, realized by the same Cooper
    /// pass as `qe-light`. In-fragment single-Int-variable existentials are
    /// eliminated (each substitution gated by Cooper's independent equivalence
    /// self-check); out-of-fragment quantifiers (multi-variable binders,
    /// universals, nested-quantifier bodies) are kept VERBATIM — the identity is
    /// equivalence-preserving, so the printed goal is always sound. A documented
    /// sound divergence from z3's LIA-complete `qe` (like the `bit-blast`
    /// fragment note above, the divergence is in coverage, never in soundness).
    Qe,
    /// `nnf` — Z3's negation-normal-form tactic: push negations to atoms and
    /// eliminate `=>`/`<->`/`xor`/`ite`-over-Bool into `and`/`or`. The resulting
    /// top-level conjunction is split into separate goal formulas, matching Z3.
    /// NNF is equivalence-preserving (stronger than equisatisfiable).
    Nnf,
    /// `tseitin-cnf` — convert the goal to CNF via Tseitin
    /// encoding. Introduces fresh auxiliary Boolean variables, so the result is
    /// **equisatisfiable** (NOT equivalent) to the input: with the aux variables
    /// treated as free, `check-sat(result) == check-sat(input)`.
    TseitinCnf,
    /// `bit-blast` — Z3's `bit-blast` tactic (AY's `BitBlast` pass): rewrite a
    /// QF_BV goal into an equisatisfiable pure-Boolean goal, replacing each BV
    /// variable with `n` fresh Boolean bits and each BV operator with its
    /// Boolean circuit. On a goal outside the supported BV fragment it HONESTLY
    /// FAILS (a tactic-failure error), never a fabricated or silent-identity blast.
    BitBlast,
    /// `split-clause` — split the first top-level disjunction into one subgoal
    /// per disjunct. Produces multiple goals; their disjunction is equivalent to
    /// the input (a sound case split).
    SplitClause,
    /// `ctx-solver-simplify` — contextual simplification using the solver: drop
    /// each top-level assertion that the OTHER assertions prove redundant, and
    /// collapse the goal to `{false}` when they prove it contradictory. Every
    /// drop/collapse is on a solver-PROVEN implication, so the result is
    /// equivalent to the input (an unknown sub-check never simplifies).
    CtxSolverSimplify,
    /// `propagate-ineqs` — z3's inequality/bound propagation, realized as a
    /// bound-subsumption pass: drop an inequality implied by a retained
    /// same-variable bound of the same strictness or by an asserted
    /// `(= var const)` value equality, and re-emit the value equalities at the
    /// end of the goal. Only drops implied conjuncts and reorders —
    /// equivalence-preserving; anything unrecognized is kept verbatim.
    PropagateIneqs,
    /// `elim-term-ite` — name every non-Boolean term-level `ite` with a fresh
    /// variable and append its guard definitions `(or (not c) (= k t))`,
    /// `(or c (= k e))`. Introduces fresh definition variables, so the result is
    /// **equisatisfiable** (NOT equivalent). AY skips `ite`s under a quantifier
    /// (a documented sound divergence: z3 names them outside the binder).
    ElimTermIte,
    /// `blast-term-ite` (alias `cofactor-term-ite`) — lift every non-Boolean
    /// term-level `ite` OUT over its enclosing predicate/function by Shannon
    /// expansion: `(<= (ite c x y) 5)` → `(ite c (<= x 5) (<= y 5))`.
    /// Equivalence-preserving. `cofactor-term-ite` maps here too: z3 cofactors in
    /// a different condition order and simplifies shared conditions more, so the
    /// produced ite-tree can differ in shape while staying logically equivalent
    /// (a documented divergence). AY skips `ite`s under a quantifier (sound
    /// divergence: z3 descends into binders).
    BlastTermIte,
    /// `der` — destructive equality resolution: resolve `(not (= x t))` literals
    /// out of universally quantified clauses via the one-point rule. Fail-closes
    /// (leaves the assertion untouched) on any nested binder to stay
    /// capture-safe. Equivalence-preserving.
    Der,
    /// `distribute-forall` — distribute `forall` over `and` (and `¬exists` over
    /// `or`), one goal formula per conjunct/disjunct. Equivalence-preserving
    /// (output order differs from z3 — a documented shape divergence).
    DistributeForall,
    /// `reduce-args` — drop function arguments that are the same literal constant
    /// in every occurrence, specializing the function per constant tuple into
    /// fresh `f!k` symbols. Equisatisfiable (fresh symbols).
    ReduceArgs,
    /// `(then t1 t2 …)` / `(and-then t1 t2 …)` — sequential composition.
    Then(Vec<ApplyTactic>),
    /// `(or-else t1 t2 …)` — try `t1`; on *failure* fall through to the next.
    OrElse(Vec<ApplyTactic>),
    /// `(par-then t1 t2)` — Z3's parallel `then`; composed sequentially here.
    ParThen(Vec<ApplyTactic>),
    /// `(par-or t1 t2 …)` — Z3's parallel `or-else`; composed sequentially here
    /// (first that succeeds wins).
    ParOr(Vec<ApplyTactic>),
    /// `(repeat t)` / `(repeat t n)` — apply `t` to fixpoint, or at most `n`
    /// iterations when a bound is given.
    Repeat(Box<ApplyTactic>, Option<usize>),
    /// `(try-for t ms)` — apply `t` under a wall-clock bound `ms`. AY's passes
    /// are already bounded, so this reduces to `t` (the bound is recorded).
    TryFor(Box<ApplyTactic>, u64),
    /// `(using-params t :k v …)` / `(with t :k v …)` — parameters to `t`.
    UsingParams(Box<ApplyTactic>, Vec<(String, ParamValue)>),
    /// `(when p t)` — apply `t` iff probe `p` holds on the goal, else `skip`.
    When(Probe, Box<ApplyTactic>),
    /// `(fail-if p)` — fail iff probe `p` holds on the goal, else `skip`.
    FailIf(Probe),
    /// `(if p t1 t2)` / `(cond p t1 t2)` — apply `t1` iff probe `p` holds on
    /// the goal, else apply `t2`. Unlike `(or-else (when p t1) t2)`, a FAILURE
    /// of the chosen branch PROPAGATES (measured z3 semantics: `(apply (if
    /// (> 1 0) fail skip))` errors, it never falls through to `skip`).
    Cond(Probe, Box<ApplyTactic>, Box<ApplyTactic>),
    /// A CLASS F fragment tactic (`diff-neq`, `nlqsat`, `pb2bv`, `horn`,
    /// `horn-simplify`): applying it always HONESTLY FAILS with `message`
    /// (z3 byte text where z3's own message is fixed — measured; `horn`/
    /// `horn-simplify` carry an AY message because z3's is a dynamic
    /// non-tactic-failed string, a documented divergence). z3 likewise fails
    /// these on generic goals, so `or-else` routing matches; on an in-fragment
    /// goal z3 succeeds where AY honestly fails (sound, catchable by
    /// `or-else`, documented in `Z3_tactic_get_descr`).
    Unsupported {
        /// The z3 tactic name (diagnostics only).
        name: &'static str,
        /// The `tactic failed: …` message body.
        message: &'static str,
    },
    /// `bv1-blast` — fails with z3's byte text iff the goal contains a
    /// bit-vector term, and is the identity otherwise (measured z3 4.15.4:
    /// success/identity on BV-free goals, `bv1 blaster cannot be applied to
    /// goal` on the 8-bit BV probe). On a pure bv1 goal z3 transforms where AY
    /// honestly fails — a documented sound divergence.
    Bv1Blast,
    /// `fail-if-undecided` — identity on a trivially decided goal (empty ⇒
    /// SAT, contains `false` ⇒ UNSAT), honest `undecided` failure otherwise.
    /// Wired to the real engine primitive `Tactic::FailIfNotDecided`.
    FailIfUndecided,
}

impl ApplyTactic {
    /// Parse a tactic expression from its S-expression form.
    ///
    /// # Errors
    ///
    /// Returns a [`ParseError`] for an unknown tactic name or a malformed
    /// combinator — mirroring Z3, which rejects unknown tactics with an error
    /// (and never silently accepts them).
    pub fn parse(sexpr: &SExpr) -> Result<Self, ParseError> {
        match sexpr {
            SExpr::Symbol(name) => Self::parse_name(name),
            SExpr::List(items) if !items.is_empty() => {
                let head = items[0]
                    .as_symbol()
                    .ok_or_else(|| ParseError::new("invalid tactic, expected a tactic name"))?;
                Self::parse_combinator(head, &items[1..])
            }
            _ => Err(ParseError::new("invalid tactic")),
        }
    }

    /// Parse a combinator application `(<head> <args…>)`.
    fn parse_combinator(head: &str, args: &[SExpr]) -> Result<Self, ParseError> {
        match head {
            "then" | "and-then" => Ok(Self::sequence(Self::parse_children(args)?, Self::Then)),
            "par-then" => Ok(Self::sequence(Self::parse_children(args)?, Self::ParThen)),
            "or-else" => Ok(Self::sequence(Self::parse_children(args)?, Self::OrElse)),
            "par-or" => Ok(Self::sequence(Self::parse_children(args)?, Self::ParOr)),
            "repeat" => Self::parse_repeat(args),
            "try-for" => Self::parse_try_for(args),
            // `(! t :k v …)` is z3's annotation spelling of `using-params`
            // (accepted in both `apply` and `check-sat-using` — measured).
            "using-params" | "with" | "!" => Self::parse_using_params(args),
            "when" => Self::parse_when(args),
            "fail-if" => Self::parse_fail_if(args),
            "if" | "cond" => Self::parse_cond(args),
            other => Err(ParseError::new(format!(
                "invalid tactic, unknown tactic {other}"
            ))),
        }
    }

    /// Parse a bare tactic name.
    ///
    /// This is THE name-recognition chokepoint for AY's whole tactic surface —
    /// the C-API `Z3_mk_tactic` resolves names through here too, so the two
    /// paths recognize exactly [`SUPPORTED_TACTIC_NAMES`]. Every accepted name
    /// is a real Z3 tactic name backed by a real pass; every other name
    /// (including Z3-nonexistent aliases like `flatten-and`) is an honest
    /// "unknown tactic" error.
    fn parse_name(name: &str) -> Result<Self, ParseError> {
        match name {
            "skip" => Ok(Self::Skip),
            "fail" => Ok(Self::Fail),
            "simplify" => Ok(Self::Simplify),
            "solve-eqs" => Ok(Self::SolveEqs),
            "propagate-values" => Ok(Self::PropagateValues),
            "elim-and" => Ok(Self::ElimAnd),
            "qe-light" => Ok(Self::QeLight),
            "qe" => Ok(Self::Qe),
            "nnf" => Ok(Self::Nnf),
            "tseitin-cnf" => Ok(Self::TseitinCnf),
            "bit-blast" => Ok(Self::BitBlast),
            "split-clause" => Ok(Self::SplitClause),
            "ctx-solver-simplify" => Ok(Self::CtxSolverSimplify),
            // z3 tactic names reduced to their closest equisatisfiable AY pass:
            // - purify-arith (normalize arithmetic atoms) -> the general simplifier
            // - elim-uncnstr (eliminate unconstrained variables) -> solve-eqs
            //   (variable elimination by substitution)
            // Both preserve satisfiability, so the reduction is sound.
            "purify-arith" => Ok(Self::Simplify),
            "elim-uncnstr" => Ok(Self::SolveEqs),
            "propagate-ineqs" => Ok(Self::PropagateIneqs),
            "elim-term-ite" => Ok(Self::ElimTermIte),
            // `cofactor-term-ite` reduces to the same Shannon ITE lift as
            // `blast-term-ite`: an equivalent ite-tree, differently
            // ordered/simplified than z3's cofactoring — documented in the
            // tactic description.
            "blast-term-ite" | "cofactor-term-ite" => Ok(Self::BlastTermIte),
            "der" => Ok(Self::Der),
            "distribute-forall" => Ok(Self::DistributeForall),
            "reduce-args" => Ok(Self::ReduceArgs),
            // Terminal "solve" tactics: z3's `smt` is the SMT engine, `sat` the
            // SAT engine, `default` its default strategy. In a tactic CHAIN they
            // are the step that decides the goal, and AY realizes that by running
            // its real engine when the tactic is turned into a solver
            // (`Z3_mk_solver_from_tactic` / `.solver()`) — the canonical z3py
            // pattern `Then('simplify','smt').solver()`. As a pure goal-to-goal
            // transform (`(apply smt)`) there is nothing to preprocess, so they
            // are the identity `Skip`: honest (they never claim to have
            // transformed) and sound (the solver does the deciding). Without
            // these, `Then('simplify','smt')` was unbuildable.
            "smt" | "default" | "sat" => Ok(Self::Skip),
            // CLASS S — per-logic solver strategies, same realization as
            // `smt`/`default`/`sat` above: identity as a goal transform (the
            // printed goal IS the input, truthfully), the REAL engine when the
            // tactic is turned into a solver. Documented divergences: z3 runs
            // the strategy inside (apply) and usually empties the goal;
            // `nlsat` errors on unpurified arith, `pqffd` errors on the Int
            // probe and `smtfd` can time out where AY's identity succeeds
            // (measured 2026-07-18; all goal-shape/or-else-routing only, never
            // a verdict).
            "auflia" | "auflira" | "aufnira" | "bv" | "lia" | "lira" | "lra" | "nlsat" | "nra"
            | "pqffd" | "psat" | "psmt" | "qfaufbv" | "qfauflia" | "qfbv" | "qfbv-sls" | "qffd"
            | "qffp" | "qffpbv" | "qffplra" | "qfidl" | "qflia" | "qflra" | "qfnia" | "qfnra"
            | "qfnra-nlsat" | "qfuf" | "qfufbv" | "qfufbv_ackr" | "qsat" | "sls-smt" | "smtfd"
            | "ufbv" | "uflra" | "ufnia" => Ok(Self::Skip),
            // CLASS A — aliases to an existing verified pass (each inherits an
            // already-shipped equivalence/equisat-preserving transform).
            "propagate-values2" => Ok(Self::PropagateValues),
            "reduce-args2" => Ok(Self::ReduceArgs),
            // Same variable-elimination reduction as `elim-uncnstr` above.
            "elim-uncnstr2" => Ok(Self::SolveEqs),
            "tseitin-cnf-core" | "sat-preprocess" => Ok(Self::TseitinCnf),
            "qe2" | "qe_rec" => Ok(Self::Qe),
            // All three are drop-what-the-context-proves-redundant; AY's pass
            // only drops solver-PROVEN-redundant assertions (equivalence-
            // preserving).
            "ctx-simplify" | "unit-subsume-simplify" | "solver-subsumption" => {
                Ok(Self::CtxSolverSimplify)
            }
            // z3's own output on the shared fragment is the simplify-normalized
            // goal (measured, e.g. `card2bv`/`degree-shift`/`fm` print the
            // simplified atom at depth 2).
            "dom-simplify" | "degree-shift" | "fm" | "card2bv" => Ok(Self::Simplify),
            // CLASS N — no-op-safe transforms realized as the identity. z3
            // leaves the goal formulas unchanged on out-of-fragment goals
            // (measured per-name); in-fragment z3 transforms where AY truthfully
            // prints the input (equivalence is trivial — never a fabricated
            // transform). Special measured cases documented in the module docs
            // and `Z3_tactic_get_descr`: subpaving / elim-predicates /
            // euf-completion / nla2bv / add-bounds / normalize-bounds.
            // `collect-statistics` is realized as the identity WITHOUT z3's
            // statistics block (a documented output divergence, resolved
            // deliberately: fabricating a partial stats block would diverge
            // across the SMT-LIB and C-API surfaces).
            "ackermannize_bv"
            | "add-bounds"
            | "aig"
            | "bv_bound_chk"
            | "bv-slice"
            | "bv-divrem-bounds"
            | "bvarray2uf"
            | "collect-statistics"
            | "demodulator"
            | "dt2bv"
            | "elim-predicates"
            | "elim-small-bv"
            | "eq2bv"
            | "euf-completion"
            | "fold-unfold"
            | "factor"
            | "fix-dl-var"
            | "fpa2bv"
            | "injectivity"
            | "lia2card"
            | "lia2pb"
            | "macro-finder"
            | "max-bv-sharing"
            | "nla2bv"
            | "normalize-bounds"
            | "occf"
            | "pb-preprocess"
            | "propagate-bv-bounds"
            | "propagate-bv-bounds2"
            | "quasi-macros"
            | "recover-01"
            | "reduce-bv-size"
            | "snf"
            | "special-relations"
            | "subpaving"
            | "symmetry-reduce"
            | "ufbv-rewriter" => Ok(Self::Skip),
            // CLASS F — honest fragment failures (z3 byte text for the first
            // three; z3's `horn`/`horn-simplify` error is a dynamic
            // non-tactic-failed string, so AY carries an honest AY message —
            // documented divergence). `pb2bv`: z3 appends `. Offending
            // expression: <term>`; AY matches the fixed prefix (documented).
            "diff-neq" => Ok(Self::Unsupported {
                name: "diff-neq",
                message: "goal is not diff neq",
            }),
            "nlqsat" => Ok(Self::Unsupported {
                name: "nlqsat",
                message: "not NRA",
            }),
            "pb2bv" => Ok(Self::Unsupported {
                name: "pb2bv",
                message: "goal is in a fragment not supported by pb2bv",
            }),
            "horn" => Ok(Self::Unsupported {
                name: "horn",
                message: "horn tactic is not supported by AY",
            }),
            "horn-simplify" => Ok(Self::Unsupported {
                name: "horn-simplify",
                message: "horn-simplify tactic is not supported by AY",
            }),
            "bv1-blast" => Ok(Self::Bv1Blast),
            // CLASS C — wired to the real engine primitive.
            "fail-if-undecided" => Ok(Self::FailIfUndecided),
            other => Err(ParseError::new(format!(
                "invalid tactic, unknown tactic {other}"
            ))),
        }
    }

    /// `(if p t1 t2)` / `(cond p t1 t2)` — exactly three arguments (z3 arity;
    /// the error text is z3's byte text, measured on z3 4.15.4).
    fn parse_cond(args: &[SExpr]) -> Result<Self, ParseError> {
        match args {
            [p, t1, t2] => Ok(Self::Cond(
                Probe::parse(p)?,
                Box::new(Self::parse(t1)?),
                Box::new(Self::parse(t2)?),
            )),
            _ => Err(ParseError::new(
                "invalid if/conditional combinator, three arguments expected",
            )),
        }
    }

    /// Parse the child tactics of a combinator, requiring at least one.
    fn parse_children(items: &[SExpr]) -> Result<Vec<Self>, ParseError> {
        if items.is_empty() {
            return Err(ParseError::new(
                "invalid tactic, combinator requires at least one tactic argument",
            ));
        }
        items.iter().map(Self::parse).collect()
    }

    /// `(repeat t)` / `(repeat t n)`.
    fn parse_repeat(args: &[SExpr]) -> Result<Self, ParseError> {
        match args {
            [t] => Ok(Self::Repeat(Box::new(Self::parse(t)?), None)),
            [t, n] => {
                let bound = Self::parse_usize(n, "repeat bound")?;
                Ok(Self::Repeat(Box::new(Self::parse(t)?), Some(bound)))
            }
            _ => Err(ParseError::new(
                "invalid tactic, repeat expects (repeat t) or (repeat t n)",
            )),
        }
    }

    /// `(try-for t ms)`.
    fn parse_try_for(args: &[SExpr]) -> Result<Self, ParseError> {
        match args {
            [t, ms] => {
                let millis = Self::parse_u64(ms, "try-for timeout")?;
                Ok(Self::TryFor(Box::new(Self::parse(t)?), millis))
            }
            _ => Err(ParseError::new(
                "invalid tactic, try-for expects (try-for t ms)",
            )),
        }
    }

    /// `(using-params t :k v …)` / `(with t :k v …)`.
    fn parse_using_params(args: &[SExpr]) -> Result<Self, ParseError> {
        let Some((first, rest)) = args.split_first() else {
            return Err(ParseError::new(
                "invalid tactic, using-params expects (using-params t :key value …)",
            ));
        };
        let inner = Self::parse(first)?;
        let params = Self::parse_params(rest)?;
        Ok(Self::UsingParams(Box::new(inner), params))
    }

    /// Parse the trailing `:key value` pairs of a `using-params`/`with`.
    fn parse_params(items: &[SExpr]) -> Result<Vec<(String, ParamValue)>, ParseError> {
        let mut out = Vec::new();
        let mut i = 0;
        while i < items.len() {
            let key = match &items[i] {
                SExpr::Keyword(k) => k.trim_start_matches(':').to_string(),
                other => {
                    return Err(ParseError::new(format!(
                        "invalid tactic, expected a :keyword parameter, got {other}"
                    )));
                }
            };
            let value = items.get(i + 1).ok_or_else(|| {
                ParseError::new(format!(
                    "invalid tactic, parameter :{key} is missing a value"
                ))
            })?;
            out.push((key, Self::parse_param_value(value)?));
            i += 2;
        }
        Ok(out)
    }

    /// Parse a single parameter value.
    fn parse_param_value(value: &SExpr) -> Result<ParamValue, ParseError> {
        match value {
            SExpr::True => Ok(ParamValue::Bool(true)),
            SExpr::False => Ok(ParamValue::Bool(false)),
            SExpr::Numeral(n) => n
                .parse::<i64>()
                .map(ParamValue::Int)
                .map_err(|_| ParseError::new(format!("invalid tactic, bad integer parameter {n}"))),
            SExpr::Decimal(d) => Ok(ParamValue::Sym(d.clone())),
            SExpr::Symbol(s) => Ok(ParamValue::Sym(s.clone())),
            other => Ok(ParamValue::Sym(other.to_string())),
        }
    }

    /// `(when p t)`.
    fn parse_when(args: &[SExpr]) -> Result<Self, ParseError> {
        match args {
            [p, t] => Ok(Self::When(Probe::parse(p)?, Box::new(Self::parse(t)?))),
            _ => Err(ParseError::new(
                "invalid tactic, when expects (when probe tactic)",
            )),
        }
    }

    /// `(fail-if p)`.
    fn parse_fail_if(args: &[SExpr]) -> Result<Self, ParseError> {
        match args {
            [p] => Ok(Self::FailIf(Probe::parse(p)?)),
            _ => Err(ParseError::new(
                "invalid tactic, fail-if expects (fail-if probe)",
            )),
        }
    }

    /// Parse a `usize` argument (a combinator bound).
    fn parse_usize(sexpr: &SExpr, what: &str) -> Result<usize, ParseError> {
        match sexpr {
            SExpr::Numeral(n) => n
                .parse::<usize>()
                .map_err(|_| ParseError::new(format!("invalid tactic, bad {what} {n}"))),
            other => Err(ParseError::new(format!(
                "invalid tactic, {what} must be a numeral, got {other}"
            ))),
        }
    }

    /// Parse a `u64` argument (a millisecond bound).
    fn parse_u64(sexpr: &SExpr, what: &str) -> Result<u64, ParseError> {
        match sexpr {
            SExpr::Numeral(n) => n
                .parse::<u64>()
                .map_err(|_| ParseError::new(format!("invalid tactic, bad {what} {n}"))),
            other => Err(ParseError::new(format!(
                "invalid tactic, {what} must be a numeral, got {other}"
            ))),
        }
    }

    /// Build a composition from a non-empty child list. A single child collapses
    /// to that child (the composition of one tactic is itself).
    fn sequence(mut children: Vec<Self>, wrap: impl FnOnce(Vec<Self>) -> Self) -> Self {
        if children.len() == 1 {
            match children.pop() {
                Some(child) => child,
                None => wrap(children),
            }
        } else {
            wrap(children)
        }
    }

    /// A **static** best-effort estimate of the Z3 goal *depth* this tactic
    /// produces (number of primitive applications; `skip`/`fail` contribute 0).
    ///
    /// The *printed* depth is computed dynamically per-goal by the engine (it
    /// depends on which `or-else` branch runs, how many times `repeat` iterates,
    /// and per-subgoal splits). This static form is retained only for diagnostics
    /// and tests over the fixed-structure combinators.
    #[must_use]
    pub fn depth(&self) -> usize {
        match self {
            Self::Skip
            | Self::Fail
            | Self::FailIf(_)
            | Self::Unsupported { .. }
            | Self::FailIfUndecided => 0,
            // bv1-blast on a BV-free goal is one applied primitive (z3 prints
            // depth 1 — measured); on a BV goal it fails (no goal at all).
            Self::Bv1Blast => 1,
            Self::Simplify
            | Self::SolveEqs
            | Self::PropagateValues
            | Self::ElimAnd
            | Self::QeLight
            | Self::Qe
            | Self::Nnf
            | Self::TseitinCnf
            | Self::BitBlast
            | Self::SplitClause
            | Self::CtxSolverSimplify
            | Self::PropagateIneqs
            | Self::ElimTermIte
            | Self::BlastTermIte
            | Self::Der
            | Self::DistributeForall
            | Self::ReduceArgs => 1,
            Self::Then(children) | Self::ParThen(children) => {
                children.iter().map(Self::depth).sum()
            }
            Self::OrElse(children) | Self::ParOr(children) => {
                children.iter().map(Self::depth).max().unwrap_or(0)
            }
            Self::Repeat(t, _) | Self::TryFor(t, _) | Self::UsingParams(t, _) => t.depth(),
            Self::When(_, t) => t.depth(),
            // Static estimate only (the printed depth is dynamic per-goal):
            // whichever branch runs contributes its own depth.
            Self::Cond(_, t1, t2) => t1.depth().max(t2.depth()),
        }
    }
}

impl Probe {
    /// Parse a probe expression (the condition of `when` / `fail-if`).
    ///
    /// # Errors
    ///
    /// Returns a [`ParseError`] for an unknown probe name/operator or a
    /// malformed application — never a silently-accepted probe.
    pub fn parse(sexpr: &SExpr) -> Result<Self, ParseError> {
        match sexpr {
            SExpr::Numeral(n) => {
                // Validate it is a number, but retain the source text (keeps `Eq`).
                n.parse::<f64>()
                    .map(|_| Probe::Const(n.clone()))
                    .map_err(|_| ParseError::new(format!("invalid probe, bad numeral {n}")))
            }
            SExpr::Decimal(d) => d
                .parse::<f64>()
                .map(|_| Probe::Const(d.clone()))
                .map_err(|_| ParseError::new(format!("invalid probe, bad decimal {d}"))),
            SExpr::Symbol(name) => Self::parse_name(name),
            SExpr::List(items) if !items.is_empty() => {
                let head = items[0]
                    .as_symbol()
                    .ok_or_else(|| ParseError::new("invalid probe, expected an operator"))?;
                Self::parse_app(head, &items[1..])
            }
            other => Err(ParseError::new(format!("invalid probe expression {other}"))),
        }
    }

    fn parse_name(name: &str) -> Result<Self, ParseError> {
        match name {
            "num-consts" => Ok(Probe::NumConsts),
            "num-exprs" => Ok(Probe::NumExprs),
            "size" => Ok(Probe::Size),
            "depth" => Ok(Probe::Depth),
            "num-bool-consts" => Ok(Probe::NumBoolConsts),
            "num-arith-consts" => Ok(Probe::NumArithConsts),
            "num-bv-consts" => Ok(Probe::NumBvConsts),
            "has-quantifiers" => Ok(Probe::HasQuantifiers),
            "is-propositional" => Ok(Probe::IsPropositional),
            "is-qfbv" => Ok(Probe::IsQfbv),
            "is-qflia" => Ok(Probe::IsQflia),
            "is-qflra" => Ok(Probe::IsQflra),
            "is-qflira" => Ok(Probe::IsQflira),
            "is-lia" => Ok(Probe::IsLia),
            "is-lra" => Ok(Probe::IsLra),
            "is-lira" => Ok(Probe::IsLira),
            "is-qfnia" => Ok(Probe::IsQfnia),
            "is-qfnra" => Ok(Probe::IsQfnra),
            "is-nia" => Ok(Probe::IsNia),
            "is-nra" => Ok(Probe::IsNra),
            // Full z3-4.15.4 probe-name coverage (42 names total): honest where
            // cheap, documented-conservative otherwise — see the variant docs.
            "has-patterns" => Ok(Probe::HasPatterns),
            "is-ilp" => Ok(Probe::IsIlp),
            "is-nira" => Ok(Probe::IsNira),
            "is-pb" => Ok(Probe::IsPb),
            "is-quasi-pb" => Ok(Probe::IsQuasiPb),
            "is-qfaufbv" => Ok(Probe::IsQfaufbv),
            "is-qfauflia" => Ok(Probe::IsQfauflia),
            "is-qfbv-eq" => Ok(Probe::IsQfbvEq),
            "is-qffp" => Ok(Probe::IsQffp),
            "is-qffpbv" => Ok(Probe::IsQffpbv),
            "is-qffplra" => Ok(Probe::IsQffplra),
            "is-qfufnra" => Ok(Probe::IsQfufnra),
            "is-unbounded" => Ok(Probe::IsUnbounded),
            "ackr-bound-probe" => Ok(Probe::AckrBoundProbe),
            "arith-avg-bw" => Ok(Probe::ArithAvgBw),
            "arith-max-bw" => Ok(Probe::ArithMaxBw),
            "arith-avg-deg" => Ok(Probe::ArithAvgDeg),
            "arith-max-deg" => Ok(Probe::ArithMaxDeg),
            "memory" => Ok(Probe::Memory),
            "produce-model" => Ok(Probe::ProduceModel),
            "produce-proofs" => Ok(Probe::ProduceProofs),
            "produce-unsat-cores" => Ok(Probe::ProduceUnsatCores),
            other => Err(ParseError::new(format!(
                "invalid probe, unknown probe expression {other}"
            ))),
        }
    }

    fn parse_app(head: &str, args: &[SExpr]) -> Result<Self, ParseError> {
        let cmp = match head {
            "<" => Some(ProbeCmp::Lt),
            "<=" => Some(ProbeCmp::Le),
            ">" => Some(ProbeCmp::Gt),
            ">=" => Some(ProbeCmp::Ge),
            "=" => Some(ProbeCmp::Eq),
            _ => None,
        };
        if let Some(op) = cmp {
            let [a, b] = args else {
                return Err(ParseError::new(format!(
                    "invalid probe, {head} expects two arguments"
                )));
            };
            return Ok(Probe::Cmp(
                op,
                Box::new(Self::parse(a)?),
                Box::new(Self::parse(b)?),
            ));
        }
        match head {
            "not" => {
                let [a] = args else {
                    return Err(ParseError::new("invalid probe, not expects one argument"));
                };
                Ok(Probe::Not(Box::new(Self::parse(a)?)))
            }
            "and" => Self::fold_binary(args, Probe::And, "and"),
            "or" => Self::fold_binary(args, Probe::Or, "or"),
            other => Err(ParseError::new(format!(
                "invalid probe, unknown probe operator {other}"
            ))),
        }
    }

    fn fold_binary(
        args: &[SExpr],
        wrap: impl Fn(Box<Probe>, Box<Probe>) -> Probe,
        what: &str,
    ) -> Result<Self, ParseError> {
        let mut it = args.iter();
        let first = it
            .next()
            .ok_or_else(|| ParseError::new(format!("invalid probe, {what} expects arguments")))?;
        let mut acc = Self::parse(first)?;
        for item in it {
            acc = wrap(Box::new(acc), Box::new(Self::parse(item)?));
        }
        Ok(acc)
    }
}

#[cfg(test)]
#[path = "tactic_tests.rs"]
mod tests;
