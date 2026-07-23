// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded Nielsen-transform word-equation solver (Track A3, Milestones 1–2).
//!
//! A standalone, `TermStore`-independent decision procedure for systems of
//! word equations over string variables and character literals:
//!
//! ```text
//!   w1 = w1'   ∧ ... ∧   wn = wn'      (words over Var ∪ Char)
//! ```
//!
//! optionally with exact per-variable length constraints and in-fragment
//! disequations. The procedure is a breadth-first exploration of the Nielsen
//! transformation graph:
//!
//! * **Normalize** every equation: strip equal head/tail symbols; an empty
//!   side forces every variable on the other side to `""` (or a conflict if a
//!   character remains); per-equation *length abstraction* (a linear
//!   Diophantine feasibility check over `|v| ≥ 0`) and a *Parikh/character
//!   count check* prune infeasible states early.
//! * **Branch** on the first unresolved equation's head pair:
//!   - `(x, c)` with variable `x`, char `c`:  `x = ""`  |  `x = c·x'`.
//!   - `(x, y)` distinct variables:  `x = y·x'`  |  `y = x·y'`
//!     (fresh `x'`, `y'` possibly empty — covers `x = y` and `x = ""`).
//! * **Leaves**: an empty equation system is a *solved form* — any assignment
//!   to the remaining free variables solves the equations. We materialize
//!   candidate assignments (all-empty, plus a distinct-values variant when
//!   disequations are present) and let the caller validate them against the
//!   FULL assertion set. `Unsat` is returned only when the whole reachable
//!   graph is explored and every branch closes with a genuine conflict —
//!   Nielsen transformation is sound and complete for word equations, so an
//!   exhausted conflict-closed graph proves unsatisfiability of the equation
//!   subset (plus any length constraints and positive regex memberships used
//!   for pruning), which soundly implies unsatisfiability of the enclosing
//!   conjunction.
//! * **Budgets** (states, fresh variables, word size) guard against the
//!   general-case non-termination of the transformation; exceeding any budget
//!   yields [`WeOutcome::Exhausted`] — a sound "don't know".
//!
//! Stage 2 (quadratic + regex coupling) adds:
//!
//! * **Per-lineage fresh variables**: fresh suffix variables are allocated per
//!   search path, not globally, so the fresh budget bounds path DEPTH. For
//!   quadratic systems (every variable occurring at most twice) Nielsen steps
//!   never grow the state, so the canonically-deduplicated graph is finite and
//!   the BFS genuinely decides them instead of burning a global counter on
//!   sibling branches.
//! * **Forced-length derivation**: each equation's length abstraction with a
//!   single unknown pins that variable's exact length (`x·a·x = b·x·c` pins
//!   `|x| = 1`); `k = 0` with same-sign coefficients pins all unknowns to
//!   `""`. Implied constraints — sound to prune on.
//! * **Primitive-root refutation**: a rotation-shaped equation `A·B = B·A`
//!   with ground `B` forces `σ(A)` to be a power of `B`'s primitive root
//!   (Lyndon–Schützenberger); ground characters/adjacent pairs inside `A`
//!   incompatible with that root refute the equation outright.
//! * **Regex-derivative pruning**: positive `str.in_re` memberships
//!   ([`WeMembership`]) are tracked as WORD-level residual constraints
//!   `σ(w) ∈ L(r)` (`w` a word over live variables/characters). Bindings
//!   substitute into the constraint words exactly, so the `x = y·x'` var-var
//!   split PROPAGATES the constraint onto `y·x'` instead of dropping it
//!   (Stage 3a). Normalization consumes leading/trailing ground characters by
//!   Brzozowski derivative (an empty residual CLOSES the branch as a genuine
//!   conflict); solved-form leaves are refuted outright when the residual
//!   constraint system (plus length windows rendered as `Σ^lo·Σ?^…` regexes)
//!   is DEFINITELY empty under the bounded product check in
//!   [`crate::we_regex::concat_membership_definitely_empty`]. Negative
//!   memberships `x ∉ R` are complemented to positive constraints `x ∈ ¬R`
//!   at seeding (Bucket B), via the exact Boolean-closed
//!   [`crate::we_regex::WeRegex::comp`], so they participate in pruning and
//!   `Unsat` on the same footing as positive memberships.
//!
//! Stage 3b adds **length-interval coupling** ([`WeLenBound`]): faithful
//! interval bounds `lo ≤ |v| ≤ hi` from the enclosing LIA lane participate in
//! the per-equation length abstraction (interval feasibility), propagate
//! across Nielsen splits (`x = y·x'` derives windows for `x'`), tighten to
//! exact lengths by interval propagation, gate empty/concat branches, and
//! guide leaf witness lengths — closing simple Norn-class QF_SLIA gaps.
//!
//! References: Nielsen (1917); Makanin (1977) for decidability;
//! CVC5 `core_solver.cpp` `processSimpleNEq` for the split taxonomy;
//! Lyndon & Schützenberger (1962) for the commutation lemma.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use std::collections::VecDeque;

use crate::we_regex::{self, WeRegex};

/// One symbol of a word: a string variable or a single character literal.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum WeSym {
    /// A string variable, identified by a dense index.
    Var(u32),
    /// A single character literal.
    Ch(char),
}

/// A word: a sequence of variables and character literals.
pub type WeWord = Vec<WeSym>;

/// A single word equation `lhs = rhs` (or disequation, by position).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WeEquation {
    /// Left-hand side word.
    pub lhs: WeWord,
    /// Right-hand side word.
    pub rhs: WeWord,
}

/// A regex membership constraint `v ∈ L(regex)` (or its negation) for an
/// original variable `v < num_vars`.
///
/// The regex must be an EXACT translation of the asserted `str.in_re`
/// constraint: positive memberships participate in branch pruning, hence in
/// `Unsat` conclusions. A negative membership is complemented to a positive
/// constraint over `¬R` at seeding, so both polarities are decided by the same
/// machinery.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WeMembership {
    /// The constrained original variable.
    pub var: u32,
    /// The regex.
    pub regex: WeRegex,
    /// Asserted polarity: `true` for `v ∈ L`, `false` for `v ∉ L`.
    pub positive: bool,
}

/// An interval length bound `lo ≤ |v| ≤ hi` for an original variable
/// (`hi = None` means unbounded above).
///
/// Must be FAITHFUL to asserted constraints: interval bounds participate in
/// branch pruning and interval propagation, hence in `Unsat` conclusions.
/// An infeasible interval (`hi < lo`) is a genuine contradiction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WeLenBound {
    /// The constrained original variable.
    pub var: u32,
    /// Inclusive lower bound on `|v|`.
    pub lo: usize,
    /// Inclusive upper bound on `|v|` (`None` = unbounded).
    pub hi: Option<usize>,
}

/// A word-equation problem: equations, in-fragment disequations, regex
/// memberships, and optional exact/interval length constraints for the
/// original variables.
#[derive(Debug, Clone, Default)]
pub struct WeProblem {
    /// Conjunction of word equations.
    pub equations: Vec<WeEquation>,
    /// Conjunction of word disequations (checked on candidate assignments
    /// only; never used to conclude `Unsat`).
    pub disequations: Vec<WeEquation>,
    /// Number of original variables; variables are `0..num_vars`.
    pub num_vars: u32,
    /// Exact length constraints `|v| = n` for original variables
    /// (must be faithful to asserted constraints: they participate in
    /// branch pruning, hence in `Unsat` conclusions).
    pub exact_lens: Vec<(u32, usize)>,
    /// Interval length bounds `lo ≤ |v| ≤ hi` for original variables
    /// (must be faithful: they participate in pruning, hence in `Unsat`).
    pub len_bounds: Vec<WeLenBound>,
    /// Regex memberships for original variables (positive ones must be
    /// faithful to asserted constraints: they participate in branch pruning,
    /// hence in `Unsat` conclusions).
    pub memberships: Vec<WeMembership>,
}

/// Budgets for the bounded Nielsen search.
#[derive(Debug, Clone)]
pub struct WeConfig {
    /// Maximum number of states popped from the frontier.
    pub max_states: usize,
    /// Maximum candidate assignments to return.
    pub max_solutions: usize,
    /// Maximum total number of symbols across a state's equations.
    pub max_word_len: usize,
    /// Maximum number of fresh variables allocated during the search.
    pub max_fresh_vars: u32,
    /// Decline the SAT witness materialization for problems with NO word
    /// equations (pure membership/disequation over the free variables).
    ///
    /// Such a problem has a single solved-form leaf: the initial state itself.
    /// Every UNSAT this fragment can prove is decided by the exhaustive
    /// emptiness reasoning that runs BEFORE candidate materialization
    /// (`normalize` conflict, per-membership `is_empty_lang`, and
    /// `leaf_res_conflict`), so declining materialization is `Unsat`-preserving
    /// — it turns only the would-be `Sat`/`Exhausted` results into `Exhausted`.
    /// The witness synthesis it skips (an unbudgeted `find_witness` over the
    /// complemented-regex intersection) is generated more cheaply downstream —
    /// by the linear skeleton-word W6 shortcut for the literal-concat regexes,
    /// and otherwise by the work-budgeted W1b regex construction (which shares
    /// `find_witness`'s BFS core, so no SAT witness is lost). Off by default;
    /// the Nielsen pre-pass sets it ONLY for the pure `str.in_re` fragment (no
    /// `str.len`/`str.++` coupling), where the downstream shortcut applies —
    /// the length-composition materializer stays live for everything else.
    pub decline_no_equation_witness: bool,
}

impl Default for WeConfig {
    fn default() -> Self {
        Self {
            max_states: 20_000,
            max_solutions: 6,
            max_word_len: 512,
            max_fresh_vars: 128,
            decline_no_equation_witness: false,
        }
    }
}

/// A candidate assignment for the original variables `0..num_vars`.
pub type WeAssignment = Vec<(u32, String)>;

/// Result of the bounded Nielsen search.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WeOutcome {
    /// Solved: candidate assignments (each satisfies every equation and every
    /// in-fragment disequation/length constraint; the caller must still
    /// validate against the full assertion set).
    Sat(Vec<WeAssignment>),
    /// The full Nielsen graph was explored and every branch closed with a
    /// conflict: the equations (together with the supplied exact lengths and
    /// positive regex memberships) are unsatisfiable.
    Unsat,
    /// A budget was exhausted, or solved forms were reached but no candidate
    /// assignment satisfied the in-fragment side constraints. Sound unknown.
    Exhausted,
}

/// A word-level positive regex constraint `σ(word) ∈ L(regex)`.
///
/// Every constraint is IMPLIED by the asserted memberships along its state's
/// binding path (bindings substitute into `word` exactly; ground characters
/// are consumed by exact Brzozowski derivatives), so a definite violation
/// closes a branch as a genuine conflict.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct WeResCon {
    word: WeWord,
    regex: WeRegex,
}

/// Cap on live word-level regex constraints per state (extras are dropped —
/// sound: prunes less).
const MAX_LIVE_RES: usize = 24;

/// Cap on interval-propagation-driven re-normalization rounds per state
/// (adversarial cyclic length couplings could otherwise tighten forever).
const MAX_INTERVAL_ROUNDS: u32 = 16;

/// A search state: the residual equation system plus the bindings that
/// produced it and the length/regex constraints still tracked for live vars.
#[derive(Debug, Clone)]
struct WeState {
    eqs: Vec<WeEquation>,
    /// Bindings in elimination order. RHS words reference only variables
    /// bound LATER or never bound (free), so value resolution terminates.
    bindings: Vec<(u32, WeWord)>,
    /// Exact lengths for live variables (original + propagated to fresh).
    lens: HashMap<u32, usize>,
    /// Interval length bounds `lo ≤ |v| ≤ hi` for live variables (faithful
    /// original bounds + windows propagated across splits). Disjoint from
    /// `lens` keys: an interval that collapses moves into `lens`.
    bounds: HashMap<u32, (usize, Option<usize>)>,
    /// Word-level positive regex constraints (see [`WeResCon`]).
    res: Vec<WeResCon>,
    /// Next fresh variable id for THIS lineage. Fresh ids are per-path (two
    /// sibling states may both use id N; states never share variables), so
    /// the fresh budget bounds path depth instead of total allocations —
    /// quadratic systems explore their full (finite, deduplicated) graph.
    next_fresh: u32,
}

/// Lower bound on `|σ(v)|` implied by tracked constraints.
fn var_lb(state: &WeState, v: u32) -> usize {
    if let Some(&l) = state.lens.get(&v) {
        return l;
    }
    state.bounds.get(&v).map_or(0, |&(lo, _)| lo)
}

/// Upper bound on `|σ(v)|` implied by tracked constraints (`None` = ∞).
fn var_ub(state: &WeState, v: u32) -> Option<usize> {
    if let Some(&l) = state.lens.get(&v) {
        return Some(l);
    }
    state.bounds.get(&v).and_then(|&(_, hi)| hi)
}

/// Lower bound on `|σ(word)|`.
fn word_lb(state: &WeState, word: &[WeSym]) -> usize {
    word.iter()
        .map(|s| match s {
            WeSym::Ch(_) => 1,
            WeSym::Var(v) => var_lb(state, *v),
        })
        .sum()
}

/// Upper bound on `|σ(word)|` (`None` = ∞).
fn word_ub(state: &WeState, word: &[WeSym]) -> Option<usize> {
    let mut total = 0usize;
    for s in word {
        match s {
            WeSym::Ch(_) => total += 1,
            WeSym::Var(v) => total += var_ub(state, *v)?,
        }
    }
    Some(total)
}

enum NormResult {
    Ok,
    Conflict,
}

/// Solve a word-equation problem with a bounded Nielsen-transform search.
#[must_use]
pub fn solve_word_equations(problem: &WeProblem, cfg: &WeConfig) -> WeOutcome {
    // Trivially violated disequation (syntactically identical sides after
    // stripping): the disequation assertion itself is false.
    for deq in &problem.disequations {
        if deq.lhs == deq.rhs {
            return WeOutcome::Unsat;
        }
    }

    let orig_lens: HashMap<u32, usize> = problem.exact_lens.iter().copied().collect();

    // Memberships seed the live regex-constraint list. A NEGATIVE membership
    // `x ∉ R` is exactly the positive constraint `x ∈ ¬R`, so we complement it
    // up front (Bucket B): the SAME residual machinery — witness search and
    // definite-emptiness — then decides both polarities, and a mixed
    // positive/negative set becomes the intersection `⋂ Rᵢ ∩ ⋂ ¬Sⱼ`.
    //
    // SOUNDNESS: `WeRegex::comp` is EXACT over the full Unicode alphabet (see
    // the `Comp` docs), and the definite-emptiness search
    // [`we_regex::concat_membership_definitely_empty`] uses an EXHAUSTIVE class
    // alphabet with an outside representative, so a complemented constraint
    // participates in UNSAT conclusions soundly. An asserted membership in a
    // DEFINITELY empty language (`R` empty, or `¬R` empty i.e. `R` universal
    // and folded to `None`) is false outright.
    let mut initial_res: Vec<WeResCon> = Vec::new();
    for m in &problem.memberships {
        let regex = if m.positive {
            m.regex.clone()
        } else {
            let c = WeRegex::comp(m.regex.clone());
            #[cfg(debug_assertions)]
            we_regex::debug_assert_complement_exact(&m.regex);
            c
        };
        if regex.is_empty_lang() {
            return WeOutcome::Unsat;
        }
        if !matches!(regex, WeRegex::All) {
            initial_res.push(WeResCon {
                word: vec![WeSym::Var(m.var)],
                regex,
            });
        }
    }

    // Seed interval bounds (faithful, so contradictions are genuine).
    let mut initial_lens = orig_lens.clone();
    let mut initial_bounds: HashMap<u32, (usize, Option<usize>)> = HashMap::default();
    for b in &problem.len_bounds {
        if matches!(b.hi, Some(h) if h < b.lo) {
            return WeOutcome::Unsat;
        }
        if let Some(&exact) = initial_lens.get(&b.var) {
            if exact < b.lo || matches!(b.hi, Some(h) if exact > h) {
                return WeOutcome::Unsat;
            }
            continue;
        }
        let entry = initial_bounds.entry(b.var).or_insert((0, None));
        entry.0 = entry.0.max(b.lo);
        entry.1 = match (entry.1, b.hi) {
            (Some(a), Some(bh)) => Some(a.min(bh)),
            (a, bh) => a.or(bh),
        };
        if let Some(h) = entry.1 {
            if h < entry.0 {
                return WeOutcome::Unsat;
            }
            if h == entry.0 {
                initial_lens.insert(b.var, h);
                initial_bounds.remove(&b.var);
            }
        }
    }

    let mut initial = WeState {
        eqs: problem.equations.clone(),
        bindings: Vec::new(),
        lens: initial_lens,
        bounds: initial_bounds,
        res: initial_res,
        next_fresh: problem.num_vars,
    };

    let mut exhausted = false;
    let mut found_leaf = false;
    let mut solutions: Vec<WeAssignment> = Vec::new();
    let mut seen_solutions: HashSet<Vec<(u32, String)>> = HashSet::default();
    // Global budget for the Stage 3c length-composition enumeration across
    // ALL solved-form leaves of this search (see `materialize_candidates`).
    let mut comp_budget: usize = 50_000;

    match normalize(&mut initial, cfg) {
        NormResult::Conflict => return WeOutcome::Unsat,
        NormResult::Ok => {}
    }

    // Per-lineage fresh cap (see `WeState::next_fresh`).
    let fresh_cap = problem.num_vars.saturating_add(cfg.max_fresh_vars);

    // Candidate-filtering side constraints (disequations / memberships) can
    // reject every candidate of the FIRST leaf in a canonical class while a
    // passing sibling hides behind a deduplicated cyclic state (e.g.
    // `x·ab = ab·x ∧ x ≠ ""`: the class keys back to itself and only the
    // filtered `x = ""` leaf is harvested). Allow a bounded number of
    // revisits per canonical key in that case — a superset exploration, so
    // Unsat soundness and termination are unaffected.
    let revisit_cap: u32 = if problem.disequations.is_empty()
        && problem.memberships.is_empty()
        && problem.len_bounds.is_empty()
    {
        1
    } else {
        3
    };
    let mut visited: HashMap<String, u32> = HashMap::default();
    let mut frontier: VecDeque<WeState> = VecDeque::new();
    visited.insert(canonical_key(&initial), 1);
    frontier.push_back(initial);

    let mut popped = 0usize;
    while let Some(state) = frontier.pop_front() {
        popped += 1;
        if popped > cfg.max_states {
            exhausted = true;
            break;
        }

        if state.eqs.is_empty() {
            // Solved form (initial state only — children reaching a solved
            // form are harvested at generation time below). A leaf whose
            // residual regex/length constraint system is DEFINITELY empty is
            // a genuine conflict (constraints are implied), not a leaf.
            if leaf_res_conflict(&state) {
                continue;
            }
            found_leaf = true;
            // No-equation problems (pure membership/disequation) reach this
            // leaf directly as the initial state; there are no sibling states.
            // The emptiness reasoning above has already settled every UNSAT the
            // fragment can prove, so declining the (unbudgeted) SAT witness
            // synthesis here is `Unsat`-preserving — the downstream skeleton /
            // work-budgeted W1b passes generate the witness. Only set for the
            // pure `str.in_re` fragment (see `decline_no_equation_witness`).
            if cfg.decline_no_equation_witness && problem.equations.is_empty() {
                continue;
            }
            for cand in materialize_candidates(&state, problem, &orig_lens, &mut comp_budget) {
                let key: Vec<(u32, String)> = cand.clone();
                if seen_solutions.insert(key) {
                    solutions.push(cand);
                }
            }
            if solutions.len() >= cfg.max_solutions {
                break;
            }
            continue;
        }

        // Branch on the first equation's head pair. After normalization both
        // sides are non-empty and the heads are not equal symbols.
        let (head_l, head_r) = {
            let eq = &state.eqs[0];
            (eq.lhs[0], eq.rhs[0])
        };

        let children: Vec<(u32, WeWord, Option<u32>)> = match (head_l, head_r) {
            (WeSym::Ch(_), WeSym::Ch(_)) => {
                // Distinct chars survive normalization only as a bug; treat
                // defensively as a closed (conflicting) branch.
                debug_assert!(false, "normalize left a Ch/Ch head pair");
                continue;
            }
            (WeSym::Var(x), WeSym::Ch(c)) | (WeSym::Ch(c), WeSym::Var(x)) => {
                // x = "" | x = c · x'. A positive length lower bound (exact
                // or interval — both faithful) excludes the empty branch as
                // a genuine conflict.
                let mut ch = Vec::new();
                if var_lb(&state, x) == 0 {
                    ch.push((x, Vec::new(), None));
                }
                if var_ub(&state, x) != Some(0) {
                    ch.push((x, vec![WeSym::Ch(c)], Some(x)));
                }
                ch
            }
            (WeSym::Var(x), WeSym::Var(y)) => {
                debug_assert_ne!(x, y, "normalize left an equal-var head pair");
                // x = "" | y = "" | x = y · x' | y = x · y'.
                //
                // The explicit empty branches are REQUIRED for completeness of
                // the exhaustion argument: with only the concat branches the
                // guided walk for a solution with |σ(x)| = |σ(y)| = 0 never
                // shrinks and cycles (e.g. `x·y = y·x` keys back to itself),
                // so a satisfiable component could exhaust without a leaf and
                // be misreported Unsat. With empties, every solution induces a
                // path that strictly decreases (Σ|σ(v)|, #live vars) lexico-
                // graphically, so a leaf is always reachable.
                //
                // Branch gating below uses IMPLIED length windows (exact or
                // interval, both faithful): skipping a branch that violates
                // them closes it as a genuine conflict. `x = y·x'` implies
                // |x| ≥ |y|, infeasible when ub(x) < lb(y).
                let mut ch = Vec::new();
                if var_lb(&state, x) == 0 {
                    ch.push((x, Vec::new(), None));
                }
                if var_lb(&state, y) == 0 {
                    ch.push((y, Vec::new(), None));
                }
                let take_a = var_ub(&state, x).is_none_or(|ub| ub >= var_lb(&state, y));
                let take_b = var_ub(&state, y).is_none_or(|ub| ub >= var_lb(&state, x));
                if take_a {
                    ch.push((x, vec![WeSym::Var(y)], Some(x)));
                }
                if take_b {
                    ch.push((y, vec![WeSym::Var(x)], Some(y)));
                }
                ch
            }
        };

        'child: for (var, prefix, len_source) in children {
            let mut child = state.clone();
            let mut replacement = prefix;

            // Allocate the fresh suffix variable when the binding is of the
            // form `var = prefix · fresh`.
            if let Some(len_of) = len_source {
                if child.next_fresh >= fresh_cap {
                    exhausted = true;
                    continue 'child;
                }
                let fresh = child.next_fresh;
                child.next_fresh += 1;
                // Length-window propagation: |fresh| = |var| - |prefix|.
                // Bounds are implied constraints, so an infeasible window
                // (prefix provably longer than var) is a genuine conflict.
                let p_lb = word_lb(&child, &replacement);
                let p_ub = word_ub(&child, &replacement);
                let v_lb = var_lb(&child, len_of);
                let v_ub = var_ub(&child, len_of);
                if let Some(vu) = v_ub {
                    if p_lb > vu {
                        // Bound variable shorter than its forced prefix.
                        continue 'child;
                    }
                }
                let f_lb = p_ub.map_or(0, |pu| v_lb.saturating_sub(pu));
                let f_ub = v_ub.map(|vu| vu - p_lb);
                if f_ub == Some(f_lb) {
                    child.lens.insert(fresh, f_lb);
                } else if f_lb > 0 || f_ub.is_some() {
                    child.bounds.insert(fresh, (f_lb, f_ub));
                }
                replacement.push(WeSym::Var(fresh));
            }

            // Bind and substitute — including into the word-level regex
            // constraints, which propagate EXACTLY across every split shape
            // (`var = ""`, `var = c·fresh`, and the var-var `var = y·fresh`);
            // normalization then consumes ground characters by derivative
            // and closes definite violations as genuine conflicts.
            child.lens.remove(&var);
            child.bounds.remove(&var);
            for eq in &mut child.eqs {
                subst_word(&mut eq.lhs, var, &replacement);
                subst_word(&mut eq.rhs, var, &replacement);
            }
            for rc in &mut child.res {
                subst_word(&mut rc.word, var, &replacement);
            }
            child.bindings.push((var, replacement));

            if state_size(&child) > cfg.max_word_len {
                exhausted = true;
                continue 'child;
            }

            match normalize(&mut child, cfg) {
                NormResult::Conflict => continue 'child,
                NormResult::Ok => {}
            }
            if state_size(&child) > cfg.max_word_len {
                exhausted = true;
                continue 'child;
            }

            if child.eqs.is_empty() {
                // Solved form: harvest IMMEDIATELY. Leaves must never be
                // deduplicated — every solved form has the same (empty)
                // canonical equation key but DIFFERENT bindings, and a later
                // leaf may produce candidates that pass the disequation /
                // length filters where an earlier one did not.
                //
                // A leaf whose residual regex/length constraint system is
                // DEFINITELY empty is a genuine conflict, not a leaf.
                if leaf_res_conflict(&child) {
                    continue 'child;
                }
                found_leaf = true;
                for cand in materialize_candidates(&child, problem, &orig_lens, &mut comp_budget) {
                    let key: Vec<(u32, String)> = cand.clone();
                    if seen_solutions.insert(key) {
                        solutions.push(cand);
                    }
                }
                continue 'child;
            }

            let key = canonical_key(&child);
            let count = visited.entry(key).or_insert(0);
            if *count < revisit_cap {
                *count += 1;
                frontier.push_back(child);
            }
        }

        if solutions.len() >= cfg.max_solutions {
            break;
        }
    }

    if !solutions.is_empty() {
        WeOutcome::Sat(solutions)
    } else if exhausted || found_leaf {
        WeOutcome::Exhausted
    } else {
        WeOutcome::Unsat
    }
}

/// Total number of symbols across a state's equations.
fn state_size(state: &WeState) -> usize {
    state.eqs.iter().map(|eq| eq.lhs.len() + eq.rhs.len()).sum()
}

/// Replace every occurrence of `var` in `word` with `replacement`.
fn subst_word(word: &mut WeWord, var: u32, replacement: &[WeSym]) {
    if !word.contains(&WeSym::Var(var)) {
        return;
    }
    let mut out = Vec::with_capacity(word.len() + replacement.len());
    for &sym in word.iter() {
        if sym == WeSym::Var(var) {
            out.extend_from_slice(replacement);
        } else {
            out.push(sym);
        }
    }
    *word = out;
}

/// Normalize a state to fixpoint: strip equal ends, force empty-side
/// bindings, drop solved equations, normalize the word-level regex
/// constraints, and run the length-abstraction and Parikh pruning checks.
fn normalize(state: &mut WeState, cfg: &WeConfig) -> NormResult {
    let mut interval_rounds = 0u32;
    loop {
        let mut changed = false;
        let mut forced: Option<Vec<u32>> = None;

        let mut i = 0;
        while i < state.eqs.len() {
            let eq = &mut state.eqs[i];
            // Strip common heads.
            let mut lo = 0usize;
            while lo < eq.lhs.len() && lo < eq.rhs.len() && eq.lhs[lo] == eq.rhs[lo] {
                lo += 1;
            }
            // Strip common tails (not crossing the stripped heads).
            let mut back = 0usize;
            while lo + back < eq.lhs.len()
                && lo + back < eq.rhs.len()
                && eq.lhs[eq.lhs.len() - 1 - back] == eq.rhs[eq.rhs.len() - 1 - back]
            {
                back += 1;
            }
            if lo > 0 || back > 0 {
                eq.lhs.drain(..lo);
                eq.rhs.drain(..lo);
                eq.lhs.truncate(eq.lhs.len() - back);
                eq.rhs.truncate(eq.rhs.len() - back);
            }

            if eq.lhs.is_empty() && eq.rhs.is_empty() {
                state.eqs.remove(i);
                changed = true;
                continue;
            }
            if eq.lhs.is_empty() || eq.rhs.is_empty() {
                let other = if eq.lhs.is_empty() { &eq.rhs } else { &eq.lhs };
                let mut vars = Vec::new();
                for sym in other {
                    match sym {
                        WeSym::Ch(_) => return NormResult::Conflict,
                        WeSym::Var(v) => {
                            if !vars.contains(v) {
                                vars.push(*v);
                            }
                        }
                    }
                }
                forced = Some(vars);
                break;
            }

            // Head/tail char clash.
            if let (WeSym::Ch(a), WeSym::Ch(b)) = (eq.lhs[0], eq.rhs[0]) {
                if a != b {
                    return NormResult::Conflict;
                }
            }
            if let (Some(WeSym::Ch(a)), Some(WeSym::Ch(b))) =
                (eq.lhs.last().copied(), eq.rhs.last().copied())
            {
                if a != b {
                    return NormResult::Conflict;
                }
            }

            i += 1;
        }

        // Length-forced empties: any live variable with an exact length of 0
        // (or an interval collapsed to [0, 0]) must be "". Binding it here
        // keeps the branching cases free of zero-length variables.
        if forced.is_none() {
            let mut zero_vars: Vec<u32> = state
                .eqs
                .iter()
                .flat_map(|eq| eq.lhs.iter().chain(eq.rhs.iter()))
                .filter_map(|s| match s {
                    WeSym::Var(v) if var_ub(state, *v) == Some(0) => Some(*v),
                    _ => None,
                })
                .collect();
            zero_vars.sort_unstable();
            zero_vars.dedup();
            if !zero_vars.is_empty() {
                forced = Some(zero_vars);
            }
        }

        if let Some(vars) = forced {
            // Empty side: every variable on the other side must be "".
            for v in vars {
                // A positive length lower bound (exact or interval, both
                // faithful) contradicts the forced "": genuine conflict.
                if var_lb(state, v) > 0 {
                    return NormResult::Conflict;
                }
                state.lens.remove(&v);
                state.bounds.remove(&v);
                for eq in &mut state.eqs {
                    eq.lhs.retain(|s| *s != WeSym::Var(v));
                    eq.rhs.retain(|s| *s != WeSym::Var(v));
                }
                // Substitute "" into the regex-constraint words; a residual
                // that then rejects its (possibly empty) word conflicts in
                // `normalize_res` below.
                for rc in &mut state.res {
                    rc.word.retain(|s| *s != WeSym::Var(v));
                }
                state.bindings.push((v, Vec::new()));
            }
            // Re-normalize from scratch (the regex constraints too).
            match normalize_res(state) {
                NormResult::Conflict => return NormResult::Conflict,
                NormResult::Ok => {}
            }
            continue;
        }

        // Word-level regex constraint normalization (derivative consumption
        // of ground characters; definite violations are genuine conflicts).
        match normalize_res(state) {
            NormResult::Conflict => return NormResult::Conflict,
            NormResult::Ok => {}
        }

        // Regex-derived length residues (Stage 3d): every single-variable
        // res constraint `σ(v) ∈ L(r)` is entailed by the faithful positive
        // memberships along the binding path, and `r.length_residues()`
        // PROVES `|σ(v)| mod m ∈ mask` — so residue-infeasible length
        // arithmetic is a genuine conflict.
        let var_residues = collect_var_residues(state);
        for (v, &(m, mask)) in &var_residues {
            // Empty residue set: the membership language is provably empty.
            if mask == 0 {
                return NormResult::Conflict;
            }
            if let Some(&l) = state.lens.get(v) {
                if mask & (1u64 << (l % m)) == 0 {
                    return NormResult::Conflict;
                }
            } else if let Some(&(lo, Some(hi))) = state.bounds.get(v) {
                // A window shorter than the modulus may miss every allowed
                // residue (windows spanning ≥ m lengths hit all residues).
                if hi - lo + 1 < m && !(lo..=hi).any(|l| mask & (1u64 << (l % m)) != 0) {
                    return NormResult::Conflict;
                }
            }
        }

        // Arithmetic + periodicity pruning per equation.
        for eq in &state.eqs {
            if !length_feasible(eq, state, &var_residues) {
                return NormResult::Conflict;
            }
            if !parikh_feasible(eq) {
                return NormResult::Conflict;
            }
            if boundary_char_conflict(eq, state) {
                return NormResult::Conflict;
            }
        }
        if commutation_conflict(state) {
            return NormResult::Conflict;
        }

        // Forced exact lengths implied by the length abstraction (a lone
        // unknown pins its exact length; `k = 0` with same-sign coefficients
        // pins every unknown to 0). Guides the quadratic classes, e.g.
        // `x·a·x = b·x·c` pins |x| = 1.
        match derive_forced_lengths(state) {
            None => return NormResult::Conflict,
            Some(true) => changed = true,
            Some(false) => {}
        }

        // Interval propagation over the per-equation length abstraction
        // (Stage 3b): tightens `lo ≤ |v| ≤ hi` windows, collapses them to
        // exact lengths, and detects infeasible windows. Bounded rounds keep
        // adversarial cyclic couplings terminating (stopping early is sound:
        // it merely prunes less).
        if interval_rounds < MAX_INTERVAL_ROUNDS {
            interval_rounds += 1;
            match propagate_length_intervals(state) {
                None => return NormResult::Conflict,
                Some(true) => changed = true,
                Some(false) => {}
            }
        }

        // Solved-variable elimination (Gaussian substitution). An equation
        // with a single-variable side `[v] = w` where `v ∉ w` is
        // DEFINITIONAL: binding `v := w` and substituting everywhere is an
        // exact equivalence transformation (the solution sets are in
        // bijection), so it is sound for BOTH the Unsat closure and the SAT
        // candidates. Without it, chains of definitions (`x9 = l8·x7`,
        // `x11 = x9·l10`, …, common in industrial sanitizer benchmarks) are
        // ground out char-by-char through the branching search, burning one
        // fresh variable per literal character and exhausting the per-lineage
        // fresh budget long before the genuinely-branching core is reached.
        //
        // Length bookkeeping: run only at quiescence (`!changed`), AFTER
        // `propagate_length_intervals` has pushed `v`'s window through this
        // very equation's length abstraction into the variables of `w`.
        // - `w = [u]` (pure rename): intersect the windows exactly — an empty
        //   intersection is a genuine conflict (|v| = |u| is implied).
        // - general `w`: drop `v`'s already-propagated window. Any residual
        //   coupling loss only WEAKENS pruning (fewer conflicts), which is
        //   sound for Unsat; SAT candidates are validated externally.
        // Word-level regex constraints substitute exactly (same as branch
        // bindings). One elimination per round; each removes an equation and
        // a live variable, so the fixpoint terminates. Oversized states stop
        // eliminating (the caller's `max_word_len` check governs).
        if !changed && state_size(state) <= cfg.max_word_len {
            let mut elim: Option<(usize, u32, WeWord)> = None;
            for (i, eq) in state.eqs.iter().enumerate() {
                let (v, w) = match (eq.lhs.as_slice(), eq.rhs.as_slice()) {
                    ([WeSym::Var(v)], w) => (*v, w),
                    (w, [WeSym::Var(v)]) => (*v, w),
                    _ => continue,
                };
                if w.contains(&WeSym::Var(v)) {
                    continue; // occurs check: leave to length/Parikh/branching
                }
                elim = Some((i, v, w.to_vec()));
                break;
            }
            if let Some((i, v, w)) = elim {
                if let [WeSym::Var(u)] = w.as_slice() {
                    // Pure rename: |v| = |u| exactly — intersect windows.
                    let u = *u;
                    let new_lo = var_lb(state, v).max(var_lb(state, u));
                    let new_hi = match (var_ub(state, v), var_ub(state, u)) {
                        (Some(a), Some(b)) => Some(a.min(b)),
                        (a, b) => a.or(b),
                    };
                    if matches!(new_hi, Some(h) if h < new_lo) {
                        return NormResult::Conflict;
                    }
                    state.lens.remove(&u);
                    state.bounds.remove(&u);
                    if new_hi == Some(new_lo) {
                        state.lens.insert(u, new_lo);
                    } else if new_lo > 0 || new_hi.is_some() {
                        state.bounds.insert(u, (new_lo, new_hi));
                    }
                }
                state.lens.remove(&v);
                state.bounds.remove(&v);
                state.eqs.remove(i);
                for eq in &mut state.eqs {
                    subst_word(&mut eq.lhs, v, &w);
                    subst_word(&mut eq.rhs, v, &w);
                }
                for rc in &mut state.res {
                    subst_word(&mut rc.word, v, &w);
                }
                state.bindings.push((v, w));
                changed = true;
            }
        }

        if !changed {
            return NormResult::Ok;
        }
    }
}

/// Normalize the word-level regex constraints to fixpoint:
///
/// * consume leading/trailing ground characters by (reversed) Brzozowski
///   derivative — an empty residual is a genuine conflict;
/// * an empty word requires a nullable residual (else conflict), and a
///   satisfied or universal constraint is dropped;
/// * oversized residuals are dropped (sound: prunes less);
/// * duplicates are removed and the live set is capped.
fn normalize_res(state: &mut WeState) -> NormResult {
    let mut i = 0usize;
    'outer: while i < state.res.len() {
        loop {
            let rc = &mut state.res[i];
            let (front, ch) = match (rc.word.first(), rc.word.last()) {
                (Some(WeSym::Ch(c)), _) => (true, *c),
                (_, Some(WeSym::Ch(c))) => (false, *c),
                _ => break,
            };
            let d = if front {
                rc.regex.derive(ch)
            } else {
                // Trailing character: derive on the reversed language.
                rc.regex.reverse().derive(ch).reverse()
            };
            if d.is_empty_lang() {
                return NormResult::Conflict;
            }
            if d.size() > we_regex::WE_REGEX_SIZE_CAP || matches!(d, WeRegex::All) {
                // Oversized/universal residual: drop the whole constraint
                // (sound: prunes less; SAT candidates are still filtered
                // against the original memberships).
                state.res.swap_remove(i);
                continue 'outer;
            }
            if front {
                rc.word.remove(0);
            } else {
                rc.word.pop();
            }
            rc.regex = d;
        }
        let rc = &state.res[i];
        if rc.word.is_empty() {
            if !rc.regex.nullable() {
                return NormResult::Conflict;
            }
            state.res.swap_remove(i); // satisfied outright
            continue;
        }
        if matches!(rc.regex, WeRegex::All) {
            state.res.swap_remove(i);
            continue;
        }
        if rc.regex.is_empty_lang() {
            // No string inhabits the empty language.
            return NormResult::Conflict;
        }
        // Length-window vs regex-window quick check is intentionally left to
        // the leaf emptiness product (`leaf_res_conflict`).
        i += 1;
    }
    state.res.sort_unstable();
    state.res.dedup();
    state.res.truncate(MAX_LIVE_RES); // extras dropped: sound, prunes less
    NormResult::Ok
}

/// Interval propagation over each equation's length abstraction: for every
/// unknown `v` with coefficient `c` in `Σ c_u·|u| = k`, bound `c·|v|` by the
/// interval of `k - Σ_{u≠v} c_u·|u|` and intersect. Returns `None` on a
/// definite conflict (empty window), `Some(changed)` otherwise. Collapsed
/// windows move into `lens`.
fn propagate_length_intervals(state: &mut WeState) -> Option<bool> {
    let mut changed = false;
    let mut derived: Vec<(u32, usize, Option<usize>)> = Vec::new();
    for eq in &state.eqs {
        let mut coeffs: HashMap<u32, i64> = HashMap::default();
        let mut k: i128 = 0;
        for sym in &eq.lhs {
            match sym {
                WeSym::Ch(_) => k -= 1,
                WeSym::Var(v) => *coeffs.entry(*v).or_insert(0) += 1,
            }
        }
        for sym in &eq.rhs {
            match sym {
                WeSym::Ch(_) => k += 1,
                WeSym::Var(v) => *coeffs.entry(*v).or_insert(0) -= 1,
            }
        }
        let entries: Vec<(u32, i64)> = coeffs
            .iter()
            .map(|(v, c)| (*v, *c))
            .filter(|(_, c)| *c != 0)
            .collect();
        for &(v, c) in &entries {
            if state.lens.contains_key(&v) {
                continue; // already exact
            }
            // Interval of rhs = k - Σ_{u≠v} c_u·|u| (None = unbounded side).
            let mut rhs_lo: Option<i128> = Some(k);
            let mut rhs_hi: Option<i128> = Some(k);
            for &(u, cu) in &entries {
                if u == v {
                    continue;
                }
                let lb = var_lb(state, u) as i128;
                let ub = var_ub(state, u).map(|x| x as i128);
                // c_u·|u| ∈ [cu·lb, cu·ub] for cu > 0, flipped for cu < 0.
                let (term_lo, term_hi) = if cu > 0 {
                    (Some(i128::from(cu) * lb), ub.map(|x| i128::from(cu) * x))
                } else {
                    (ub.map(|x| i128::from(cu) * x), Some(i128::from(cu) * lb))
                };
                rhs_lo = match (rhs_lo, term_hi) {
                    (Some(a), Some(b)) => Some(a - b),
                    _ => None,
                };
                rhs_hi = match (rhs_hi, term_lo) {
                    (Some(a), Some(b)) => Some(a - b),
                    _ => None,
                };
            }
            // c·|v| ∈ [rhs_lo, rhs_hi]  ⇒  |v| window with exact rounding.
            let (mut new_lo, new_hi): (Option<i128>, Option<i128>) = if c > 0 {
                (
                    rhs_lo.map(|a| {
                        a.div_euclid(i128::from(c)) + i128::from(a.rem_euclid(i128::from(c)) != 0)
                    }),
                    rhs_hi.map(|a| a.div_euclid(i128::from(c))),
                )
            } else {
                let cp = i128::from(-c);
                (
                    rhs_hi.map(|a| {
                        let a = -a;
                        a.div_euclid(cp) + i128::from(a.rem_euclid(cp) != 0)
                    }),
                    rhs_lo.map(|a| (-a).div_euclid(cp)),
                )
            };
            // |v| ≥ 0 intrinsically.
            new_lo = Some(new_lo.map_or(0, |l| l.max(0)));
            if let Some(h) = new_hi {
                if h < 0 {
                    return None; // definite conflict
                }
            }
            // Astronomically large values carry no usable fact (never a
            // conflict — huge strings exist).
            let Ok(lo) = usize::try_from(new_lo.unwrap_or(0)) else {
                continue;
            };
            let hi = new_hi.and_then(|h| usize::try_from(h).ok());
            if lo > 0 || hi.is_some() {
                derived.push((v, lo, hi));
            }
        }
    }
    for (v, lo, hi) in derived {
        if let Some(&exact) = state.lens.get(&v) {
            if exact < lo || matches!(hi, Some(h) if exact > h) {
                return None;
            }
            continue;
        }
        let (cur_lo, cur_hi) = state.bounds.get(&v).copied().unwrap_or((0, None));
        let m_lo = cur_lo.max(lo);
        let m_hi = match (cur_hi, hi) {
            (Some(a), Some(b)) => Some(a.min(b)),
            (a, b) => a.or(b),
        };
        if let Some(h) = m_hi {
            if h < m_lo {
                return None;
            }
        }
        if (m_lo, m_hi) != (cur_lo, cur_hi) {
            changed = true;
            if m_hi == Some(m_lo) {
                state.bounds.remove(&v);
                state.lens.insert(v, m_lo);
            } else {
                state.bounds.insert(v, (m_lo, m_hi));
            }
        }
    }
    Some(changed)
}

/// DEFINITE conflict check for a solved-form leaf's residual constraint
/// system: each variable's singleton regex constraints (intersected with its
/// length window rendered as a regex) must be jointly inhabitable, and each
/// word-level constraint must admit SOME per-occurrence split. Uses the
/// bounded exhaustive product check in
/// [`we_regex::concat_membership_definitely_empty`] — `true` only on a
/// PROOF of emptiness, so closing the leaf is a genuine conflict.
///
/// Treating repeated variables in a word as independent occurrences
/// over-approximates the solution set; emptiness of the over-approximation
/// still implies emptiness of the true set (sound).
fn leaf_res_conflict(state: &WeState) -> bool {
    if state.res.is_empty() {
        return false;
    }
    const MAX_LEAF_WORD: usize = 6;
    // Per-variable constraint sets from singleton words + length windows.
    let mut singleton: HashMap<u32, Vec<WeRegex>> = HashMap::default();
    let mut vars: Vec<u32> = Vec::new();
    for rc in &state.res {
        if let [WeSym::Var(v)] = rc.word.as_slice() {
            singleton.entry(*v).or_default().push(rc.regex.clone());
            vars.push(*v);
        }
    }
    vars.sort_unstable();
    vars.dedup();
    let var_set = |v: u32| -> Vec<WeRegex> {
        let mut set = singleton.get(&v).cloned().unwrap_or_default();
        let lo = var_lb(state, v);
        let hi = var_ub(state, v);
        if lo > 0 || hi.is_some() {
            if let Some(r) = we_regex::len_interval_regex(lo, hi) {
                set.push(r);
            }
        }
        set
    };
    // 1. Each regex-constrained variable alone must be inhabitable.
    for &v in &vars {
        let set = var_set(v);
        if !set.is_empty() && we_regex::concat_membership_definitely_empty(&[set], &[]) {
            return true;
        }
    }
    // 2. Each word-level constraint, with per-occurrence variable sets.
    for rc in &state.res {
        if rc.word.len() < 2 || rc.word.len() > MAX_LEAF_WORD {
            continue;
        }
        let parts: Vec<Vec<WeRegex>> = rc
            .word
            .iter()
            .map(|sym| match sym {
                WeSym::Ch(c) => vec![WeRegex::lit(&c.to_string())],
                WeSym::Var(v) => var_set(*v),
            })
            .collect();
        if we_regex::concat_membership_definitely_empty(&parts, std::slice::from_ref(&rc.regex)) {
            return true;
        }
    }
    false
}

/// Derive exact lengths implied by each equation's length abstraction.
///
/// Returns `None` on a definite conflict (non-integral or negative forced
/// length), `Some(changed)` otherwise. Only NEW facts set `changed`, so the
/// normalize fixpoint terminates (live-variable count bounds insertions).
fn derive_forced_lengths(state: &mut WeState) -> Option<bool> {
    let mut changed = false;
    let mut derived: Vec<(u32, usize)> = Vec::new();
    for eq in &state.eqs {
        let mut coeffs: HashMap<u32, i64> = HashMap::default();
        let mut k: i64 = 0;
        for sym in &eq.lhs {
            match sym {
                WeSym::Ch(_) => k -= 1,
                WeSym::Var(v) => *coeffs.entry(*v).or_insert(0) += 1,
            }
        }
        for sym in &eq.rhs {
            match sym {
                WeSym::Ch(_) => k += 1,
                WeSym::Var(v) => *coeffs.entry(*v).or_insert(0) -= 1,
            }
        }
        let mut unknown: Vec<(u32, i64)> = Vec::new();
        for (v, c) in &coeffs {
            if *c == 0 {
                continue;
            }
            match state.lens.get(v) {
                Some(l) => k -= *c * (*l as i64),
                None => unknown.push((*v, *c)),
            }
        }
        match unknown.as_slice() {
            [] => {
                if k != 0 {
                    return None;
                }
            }
            [(v, c)] => {
                // c·|v| = k exactly.
                if k % *c != 0 || k / *c < 0 {
                    return None;
                }
                // Out-of-usize lengths carry no usable fact (do NOT treat
                // conversion failure as a conflict — huge strings exist).
                if let Ok(l) = usize::try_from(k / *c) {
                    derived.push((*v, l));
                }
            }
            _ => {
                let all_pos = unknown.iter().all(|(_, c)| *c > 0);
                let all_neg = unknown.iter().all(|(_, c)| *c < 0);
                if k == 0 && (all_pos || all_neg) {
                    // Σ c_v·|v| = 0 with same-sign coefficients ⇒ all 0.
                    for (v, _) in &unknown {
                        derived.push((*v, 0));
                    }
                }
            }
        }
    }
    for (v, l) in derived {
        match state.lens.get(&v) {
            Some(prev) if *prev != l => return None,
            Some(_) => {}
            None => {
                // An implied exact length outside the variable's (faithful)
                // interval window is a definite conflict.
                if let Some(&(lo, hi)) = state.bounds.get(&v) {
                    if l < lo || matches!(hi, Some(h) if l > h) {
                        return None;
                    }
                    state.bounds.remove(&v);
                }
                state.lens.insert(v, l);
                changed = true;
            }
        }
    }
    Some(changed)
}

/// Primitive-root (Lyndon–Schützenberger) refutation for rotation-shaped
/// equations `A·B = B·A` (as symbol sequences).
///
/// Any solution makes `σ(A)` and `σ(B)` commute, hence powers `p^m`, `p^n`
/// of a common primitive word `p`. Two sound refutations:
///
/// 1. `B` fully ground: `p` is B's primitive root, and `m ≥ 1` whenever `A`
///    contains a ground character — so every ground character of `A` must be
///    a character of `p`, and every ADJACENT ground pair inside `A` must
///    occur as an adjacent pair of the infinite word `p^∞`.
/// 2. Both sides provably non-empty (a ground character, a positive exact
///    length, or a non-nullable membership) with provably DISJOINT possible
///    character sets: `m, n ≥ 1` forces `chars(p)` into both sides' possible
///    sets — impossible when disjoint. Closes e.g. `x·y = y·x ∧ x ∈ a+ ∧
///    y ∈ b+`.
fn commutation_conflict(state: &WeState) -> bool {
    for eq in &state.eqs {
        let n = eq.lhs.len();
        if n != eq.rhs.len() || !(2..=64).contains(&n) {
            continue;
        }
        for split in 1..n {
            let (a, b) = eq.lhs.split_at(split);
            if eq.rhs[..b.len()] != *b || eq.rhs[b.len()..] != *a {
                continue;
            }
            // Rule 1: a side provably a NONEMPTY power of a primitive word
            // `p` (fully ground, or a single variable whose membership
            // language is contained in `w*` — Stage 3c) forces the OTHER
            // side into `p*` (Lyndon–Schützenberger): commuting with a
            // non-empty `p^m` means being a power of `p`. Two refutations:
            // ground content incompatible with `p^∞`, or a length window
            // containing NO multiple of `|p|`.
            for (word, other) in [(a, b), (b, a)] {
                let Some(p) = side_forced_root(other, state) else {
                    continue;
                };
                if word_violates_period(word, &p) {
                    return true;
                }
                if !window_admits_multiple(word_lb(state, word), word_ub(state, word), p.len()) {
                    return true;
                }
            }
            // Rule 2: disjoint character sets on two non-empty sides.
            if side_provably_nonempty(a, state) && side_provably_nonempty(b, state) {
                if let (Some(ca), Some(cb)) =
                    (side_possible_chars(a, state), side_possible_chars(b, state))
                {
                    if ca.is_disjoint(&cb) {
                        return true;
                    }
                }
            }
        }
    }
    false
}

/// The characters of a fully ground word, or `None` if it contains a variable.
fn ground_word(w: &[WeSym]) -> Option<Vec<char>> {
    w.iter()
        .map(|s| match s {
            WeSym::Ch(c) => Some(*c),
            WeSym::Var(_) => None,
        })
        .collect()
}

/// The primitive root of a non-empty ground word: the shortest `p` with
/// `w = p^k`.
fn primitive_root(w: &[char]) -> Vec<char> {
    for d in 1..w.len() {
        if w.len().is_multiple_of(d) && w.chunks(d).all(|chunk| chunk == &w[..d]) {
            return w[..d].to_vec();
        }
    }
    w.to_vec()
}

/// The primitive word `p` such that `σ(side)` is PROVABLY a non-empty power
/// of `p`, when the tracked constraints force one:
///
/// * a fully ground non-empty side: its primitive root;
/// * a single variable whose singleton membership language is contained in
///   `w*` for a concrete word `w` (shapes `w*`, `w+`, `w`, and literal
///   concatenations sharing one primitive root), provided the variable is
///   provably non-empty (the regex excludes `""`, or a positive length
///   lower bound).
///
/// Soundness: `σ(side) ∈ p*` and `σ(side) ≠ ""` give `σ(side) = p^m`,
/// `m ≥ 1`, with `p` primitive — so `ρ(σ(side)) = p` exactly.
fn side_forced_root(side: &[WeSym], state: &WeState) -> Option<Vec<char>> {
    if let Some(g) = ground_word(side) {
        return if g.is_empty() {
            None
        } else {
            Some(primitive_root(&g))
        };
    }
    let [WeSym::Var(v)] = side else {
        return None;
    };
    for rc in &state.res {
        if !matches!(rc.word.as_slice(), [WeSym::Var(u)] if u == v) {
            continue;
        }
        if let Some((p, regex_nonempty)) = power_language_root(&rc.regex) {
            if !p.is_empty() && (regex_nonempty || var_lb(state, *v) > 0) {
                return Some(p);
            }
        }
    }
    None
}

/// If every string of `L(r)` is a power of a single concrete word, return
/// that word's primitive root plus whether `"" ∉ L(r)`. `None` = no such
/// word is derivable from the shape (NOT a semantic claim).
fn power_language_root(r: &WeRegex) -> Option<(Vec<char>, bool)> {
    match r {
        WeRegex::Lit(s) => {
            let cs: Vec<char> = s.chars().collect();
            if cs.is_empty() {
                None // defensive: `Lit` is non-empty by construction
            } else {
                Some((primitive_root(&cs), true))
            }
        }
        WeRegex::Star(inner) => power_language_root(inner).map(|(p, _)| (p, false)),
        WeRegex::Concat(parts) => {
            // Each part a power of the SAME primitive p ⇒ so is the concat;
            // any part excluding "" makes the whole language exclude "".
            let mut root: Option<Vec<char>> = None;
            let mut nonempty = false;
            for part in parts {
                let (p, ne) = power_language_root(part)?;
                match &root {
                    None => root = Some(p),
                    Some(r0) if *r0 == p => {}
                    Some(_) => return None,
                }
                nonempty |= ne;
            }
            root.map(|p| (p, nonempty))
        }
        _ => None,
    }
}

/// Does the length window `[lb, ub]` (`ub = None` = unbounded) contain a
/// multiple of `m`? (`0` counts — the empty string is a 0th power.)
fn window_admits_multiple(lb: usize, ub: Option<usize>, m: usize) -> bool {
    if m <= 1 {
        return true;
    }
    match ub {
        None => true,
        Some(ub) => ub / m * m >= lb,
    }
}

/// Whether `word`'s ground content is incompatible with being (part of) a
/// power of `p`: a ground character outside `chars(p)`, or two ADJACENT
/// ground characters that never occur adjacently in `p^∞`.
fn word_violates_period(word: &[WeSym], p: &[char]) -> bool {
    if p.is_empty() {
        return false;
    }
    let chars: HashSet<char> = p.iter().copied().collect();
    let pairs: HashSet<(char, char)> = (0..p.len()).map(|i| (p[i], p[(i + 1) % p.len()])).collect();
    let mut prev: Option<char> = None;
    for sym in word {
        match sym {
            WeSym::Var(_) => prev = None,
            WeSym::Ch(c) => {
                if !chars.contains(c) {
                    return true;
                }
                if let Some(pc) = prev {
                    if !pairs.contains(&(pc, *c)) {
                        return true;
                    }
                }
                prev = Some(*c);
            }
        }
    }
    false
}

/// Boundary-character conflict: when BOTH sides of an equation are provably
/// non-empty, `σ(lhs) = σ(rhs)` forces their first characters (and last
/// characters) to be equal. Disjoint over-approximated first-char (or
/// last-char) sets are therefore a genuine conflict. Closes e.g.
/// `x·y = y·x ∧ x ∈ (ab)+ ∧ y ∈ (ba)+` (first chars {a} vs {b}).
fn boundary_char_conflict(eq: &WeEquation, state: &WeState) -> bool {
    if !side_provably_nonempty(&eq.lhs, state) || !side_provably_nonempty(&eq.rhs, state) {
        return false;
    }
    if let (Some(fa), Some(fb)) = (
        word_boundary_chars(&eq.lhs, state, false),
        word_boundary_chars(&eq.rhs, state, false),
    ) {
        if fa.is_disjoint(&fb) {
            return true;
        }
    }
    if let (Some(la), Some(lb)) = (
        word_boundary_chars(&eq.lhs, state, true),
        word_boundary_chars(&eq.rhs, state, true),
    ) {
        if la.is_disjoint(&lb) {
            return true;
        }
    }
    false
}

/// Over-approximation of the possible FIRST characters of `σ(word)` (or the
/// possible LAST characters when `from_end`), or `None` when unbounded.
///
/// Walks the word from the boundary: a ground character contributes itself
/// and stops; a possibly-empty variable contributes its (filtered) possible
/// first characters and continues; a provably non-empty variable stops.
/// Character sets come from singleton regex constraints: a candidate `c`
/// survives only if EVERY constraint's derivative by `c` is not definitely
/// empty — an over-approximation of the true first-char set, so disjointness
/// conclusions are sound.
fn word_boundary_chars(word: &[WeSym], state: &WeState, from_end: bool) -> Option<HashSet<char>> {
    let mut out: HashSet<char> = HashSet::default();
    let syms: Vec<WeSym> = if from_end {
        word.iter().rev().copied().collect()
    } else {
        word.to_vec()
    };
    for sym in syms {
        match sym {
            WeSym::Ch(c) => {
                out.insert(c);
                return Some(out);
            }
            WeSym::Var(v) => {
                if var_ub(state, v) == Some(0) {
                    continue; // contributes nothing
                }
                let sets: Vec<WeRegex> = state
                    .res
                    .iter()
                    .filter(|rc| matches!(rc.word.as_slice(), [WeSym::Var(u)] if *u == v))
                    .map(|rc| {
                        if from_end {
                            rc.regex.reverse()
                        } else {
                            rc.regex.clone()
                        }
                    })
                    .collect();
                // A candidate universe from any single bounded constraint.
                let universe = sets.iter().find_map(regex_possible_chars)?;
                for c in universe {
                    if sets.iter().all(|r| !r.derive(c).is_empty_lang()) {
                        out.insert(c);
                    }
                }
                let nonempty = var_lb(state, v) > 0 || sets.iter().any(|r| !r.nullable());
                if nonempty {
                    return Some(out);
                }
                // v may be empty: later symbols can also supply the boundary.
            }
        }
    }
    Some(out)
}

/// Is `σ(word)` provably non-empty? True when the word contains a ground
/// character, a variable with a positive length lower bound (exact or
/// interval), or a variable with a non-nullable singleton membership
/// constraint.
fn side_provably_nonempty(word: &[WeSym], state: &WeState) -> bool {
    word.iter().any(|sym| match sym {
        WeSym::Ch(_) => true,
        WeSym::Var(v) => {
            var_lb(state, *v) > 0
                || state.res.iter().any(|rc| {
                    matches!(rc.word.as_slice(), [WeSym::Var(u)] if u == v) && !rc.regex.nullable()
                })
        }
    })
}

/// An over-approximation of the characters that can appear in `σ(word)`, or
/// `None` when unbounded (any character possible).
///
/// A variable `v` occurring in ANY constraint word `w` with `σ(w) ∈ L(r)`
/// has `σ(v)` as a factor of a string of `L(r)`, so `r`'s possible
/// characters bound `v`'s.
fn side_possible_chars(word: &[WeSym], state: &WeState) -> Option<HashSet<char>> {
    let mut out: HashSet<char> = HashSet::default();
    for sym in word {
        match sym {
            WeSym::Ch(c) => {
                out.insert(*c);
            }
            WeSym::Var(v) => {
                // A zero-length variable contributes nothing.
                if var_ub(state, *v) == Some(0) {
                    continue;
                }
                // Any constraint containing v bounds its characters.
                let mut bounded = false;
                for rc in &state.res {
                    if !rc.word.contains(&WeSym::Var(*v)) {
                        continue;
                    }
                    if let Some(set) = regex_possible_chars(&rc.regex) {
                        out.extend(set);
                        bounded = true;
                        break;
                    }
                }
                if !bounded {
                    return None;
                }
            }
        }
    }
    Some(out)
}

/// An over-approximation of the characters appearing in any string of
/// `L(r)`, or `None` when unbounded.
fn regex_possible_chars(r: &WeRegex) -> Option<HashSet<char>> {
    const MAX_RANGE: u32 = 64;
    let mut out: HashSet<char> = HashSet::default();
    let mut stack: Vec<&WeRegex> = vec![r];
    while let Some(cur) = stack.pop() {
        match cur {
            WeRegex::None | WeRegex::Eps => {}
            // A complement can contain characters outside its inner regex, so
            // its character set is unbounded — no finite over-approximation.
            WeRegex::AnyChar | WeRegex::All | WeRegex::Comp(_) => return None,
            WeRegex::Lit(s) => out.extend(s.chars()),
            WeRegex::Range(lo, hi) => {
                if (*hi as u32).saturating_sub(*lo as u32) > MAX_RANGE {
                    return None;
                }
                for c in *lo..=*hi {
                    out.insert(c);
                }
            }
            WeRegex::Concat(xs) | WeRegex::Union(xs) | WeRegex::Inter(xs) => {
                stack.extend(xs.iter());
            }
            // Every character of a bounded repeat comes from its body (an
            // over-approximation of the body's chars stays one for the loop).
            WeRegex::Star(x) | WeRegex::Loop(x, ..) => stack.push(x),
        }
    }
    Some(out)
}

/// Per-variable regex-derived length residues, extracted from the live
/// single-variable res constraints: `v ↦ (m, mask)` proves
/// `|σ(v)| mod m ∈ mask` (see [`WeRegex::length_residues`]). Multiple
/// constraints on one variable are combined by lifting both congruences to
/// their lcm modulus (≤ [`we_regex::LEN_RESIDUE_MAX_MODULUS`]) and
/// intersecting; when the lcm exceeds the cap the stronger-looking fact is
/// kept alone (sound: any one entailed fact may be used).
fn collect_var_residues(state: &WeState) -> HashMap<u32, (usize, u64)> {
    let mut out: HashMap<u32, (usize, u64)> = HashMap::default();
    for rc in &state.res {
        let [WeSym::Var(v)] = rc.word.as_slice() else {
            continue;
        };
        let Some((m, mask)) = rc.regex.length_residues() else {
            continue;
        };
        match out.get(v).copied() {
            None => {
                out.insert(*v, (m, mask));
            }
            Some((m0, mask0)) => {
                let combined = combine_residues((m0, mask0), (m, mask));
                out.insert(*v, combined);
            }
        }
    }
    out
}

/// Lift a residue fact `(m, mask)` to a multiple modulus `l` (`m | l`):
/// bit `r` allowed mod `l` iff bit `r mod m` allowed mod `m`.
fn lift_residues(m: usize, mask: u64, l: usize) -> u64 {
    let mut out = 0u64;
    for r in 0..l {
        if mask & (1u64 << (r % m)) != 0 {
            out |= 1u64 << r;
        }
    }
    out
}

/// Intersect two residue facts about the SAME quantity by lifting both to
/// the lcm modulus; falls back to the larger-modulus fact when the lcm
/// exceeds the cap (each fact alone is entailed, so either is sound).
fn combine_residues(a: (usize, u64), b: (usize, u64)) -> (usize, u64) {
    let (ma, xa) = a;
    let (mb, xb) = b;
    let g = gcd_u64(ma as u64, mb as u64).max(1) as usize;
    let l = ma / g * mb;
    if l > we_regex::LEN_RESIDUE_MAX_MODULUS {
        return if ma >= mb { a } else { b };
    }
    (l, lift_residues(ma, xa, l) & lift_residues(mb, xb, l))
}

/// Residue feasibility of `Σ c_v·|v| = k` over the unknowns (Stage 3d):
/// working modulo `M` = capped lcm of the unknowns' residue moduli, each
/// unknown `v` with entailed fact `|v| ≡ r (mod m_v), r ∈ R_v` contributes
/// the residues `{ c·r + c·m_v·t mod M : r ∈ R_v, t ∈ ℕ }` (a union of
/// cosets of the subgroup generated by `gcd(|c|·m_v, M)`); an unknown
/// without residue information contributes `{ c·t mod M : t ∈ ℕ }` (all
/// lengths possible — a pure over-approximation, never a restriction beyond
/// what `|v| ∈ ℕ` implies). The equation is infeasible if `k mod M` is not
/// in the sumset of the contributions — a sound congruence-only check
/// (windows are checked separately and only ever restrict further).
fn residue_feasible(
    k: i64,
    unknown_vars: &[(u32, i64)],
    residues: &HashMap<u32, (usize, u64)>,
) -> bool {
    // Modulus: capped lcm over unknowns WITH residue info.
    let mut big_m = 1u64;
    for (v, _) in unknown_vars {
        if let Some(&(m, _)) = residues.get(v) {
            let g = gcd_u64(big_m, m as u64).max(1);
            let l = big_m / g * m as u64;
            if l <= we_regex::LEN_RESIDUE_MAX_MODULUS as u64 {
                big_m = l;
            }
        }
    }
    if big_m < 2 {
        return true; // no residue information: nothing to check
    }
    let bm = big_m as usize;
    let coset = |base: usize, step_gcd: usize| -> u64 {
        // { base + t·step : t ∈ ℕ } mod bm = the coset of the subgroup
        // generated by gcd(step, bm) that contains base.
        let g = step_gcd.max(1);
        let mut out = 0u64;
        let mut r = base % g;
        while r < bm {
            out |= 1u64 << r;
            r += g;
        }
        out
    };
    let mut acc = 1u64; // {0}
    for &(v, c) in unknown_vars {
        let c_mod = (((c % bm as i64) + bm as i64) % bm as i64) as usize;
        let contrib = match residues.get(&v) {
            Some(&(m, mask)) if bm.is_multiple_of(m) => {
                // |v| = r + t·m (t ∈ ℕ, r ∈ mask): c·|v| mod M covers, for
                // each allowed r, the coset base c·r of ⟨gcd(|c|·m, M)⟩.
                let step = gcd_u64((c.unsigned_abs() % big_m).saturating_mul(m as u64), big_m)
                    .max(1) as usize;
                let mut s = 0u64;
                for r in 0..m {
                    if mask & (1u64 << r) != 0 {
                        s |= coset((c_mod * r) % bm, step);
                    }
                }
                s
            }
            // No info (or a modulus not dividing M after the lcm cap):
            // |v| ranges over all of ℕ.
            _ => coset(0, gcd_u64(c.unsigned_abs() % big_m, big_m).max(1) as usize),
        };
        acc = sumset_residues(acc, contrib, bm);
        if acc == 0 {
            return false; // some variable admits NO length at all
        }
    }
    let k_res = (((k % bm as i64) + bm as i64) % bm as i64) as usize;
    acc & (1u64 << k_res) != 0
}

/// Sumset of two residue bitmasks modulo `m` (word_eq-local copy of the
/// we_regex helper, kept private to each module).
fn sumset_residues(a: u64, b: u64, m: usize) -> u64 {
    let mut out = 0u64;
    for i in 0..m {
        if a & (1u64 << i) == 0 {
            continue;
        }
        for j in 0..m {
            if b & (1u64 << j) != 0 {
                out |= 1u64 << ((i + j) % m);
            }
        }
    }
    out
}

/// Length abstraction: `Σ_v (cnt_lhs(v) - cnt_rhs(v))·|v| = litlen_rhs -
/// litlen_lhs` must be feasible over `|v| ≥ 0` (with known exact lengths
/// substituted, faithful interval windows bounding the unknowns, and
/// regex-derived length residues constraining the unknowns mod m).
/// Sound infeasibility checks only; may miss conflicts.
fn length_feasible(
    eq: &WeEquation,
    state: &WeState,
    residues: &HashMap<u32, (usize, u64)>,
) -> bool {
    let mut coeffs: HashMap<u32, i64> = HashMap::default();
    let mut k: i64 = 0;
    for sym in &eq.lhs {
        match sym {
            WeSym::Ch(_) => k -= 1,
            WeSym::Var(v) => *coeffs.entry(*v).or_insert(0) += 1,
        }
    }
    for sym in &eq.rhs {
        match sym {
            WeSym::Ch(_) => k += 1,
            WeSym::Var(v) => *coeffs.entry(*v).or_insert(0) -= 1,
        }
    }
    // Substitute known lengths; keep unknowns (with interval windows).
    let mut unknown: Vec<i64> = Vec::new();
    let mut unknown_vars: Vec<(u32, i64)> = Vec::new();
    for (v, c) in &coeffs {
        if *c == 0 {
            continue;
        }
        match state.lens.get(v) {
            Some(l) => k -= *c * (*l as i64),
            None => {
                unknown.push(*c);
                unknown_vars.push((*v, *c));
            }
        }
    }
    if unknown.is_empty() {
        return k == 0;
    }
    let all_pos = unknown.iter().all(|c| *c > 0);
    let all_neg = unknown.iter().all(|c| *c < 0);
    if all_pos {
        if k < 0 {
            return false;
        }
        let min = unknown.iter().copied().min().unwrap_or(1);
        if k > 0 && k < min {
            return false;
        }
    }
    if all_neg {
        if k > 0 {
            return false;
        }
        let min = unknown.iter().map(|c| -c).min().unwrap_or(1);
        if k < 0 && -k < min {
            return false;
        }
    }
    let g = unknown.iter().map(|c| c.unsigned_abs()).fold(0u64, gcd_u64);
    if g > 1 && !k.unsigned_abs().is_multiple_of(g) {
        return false;
    }
    // Residue check (Stage 3d): regex-derived congruences on the unknowns
    // must let Σ c_v·|v| reach k modulo the combined modulus.
    if !residue_feasible(k, &unknown_vars, residues) {
        return false;
    }
    // Interval check (Stage 3b): Σ c_v·|v| over the unknowns' faithful
    // windows must be able to reach k.
    let mut min_sum: Option<i128> = Some(0);
    let mut max_sum: Option<i128> = Some(0);
    for &(v, c) in &unknown_vars {
        let lb = var_lb(state, v) as i128;
        let ub = var_ub(state, v).map(|x| x as i128);
        let (term_lo, term_hi) = if c > 0 {
            (Some(i128::from(c) * lb), ub.map(|x| i128::from(c) * x))
        } else {
            (ub.map(|x| i128::from(c) * x), Some(i128::from(c) * lb))
        };
        min_sum = match (min_sum, term_lo) {
            (Some(a), Some(b)) => Some(a + b),
            _ => None,
        };
        max_sum = match (max_sum, term_hi) {
            (Some(a), Some(b)) => Some(a + b),
            _ => None,
        };
    }
    if matches!(min_sum, Some(m) if i128::from(k) < m) {
        return false;
    }
    if matches!(max_sum, Some(m) if i128::from(k) > m) {
        return false;
    }
    true
}

fn gcd_u64(a: u64, b: u64) -> u64 {
    if a == 0 {
        return b;
    }
    if b == 0 {
        return a;
    }
    let (mut a, mut b) = (a, b);
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

/// Parikh (character count) check: when every variable occurs the same
/// number of times on both sides, the per-character literal counts must
/// match exactly (variable contributions cancel).
fn parikh_feasible(eq: &WeEquation) -> bool {
    let mut var_net: HashMap<u32, i64> = HashMap::default();
    let mut ch_net: HashMap<char, i64> = HashMap::default();
    for sym in &eq.lhs {
        match sym {
            WeSym::Var(v) => *var_net.entry(*v).or_insert(0) += 1,
            WeSym::Ch(c) => *ch_net.entry(*c).or_insert(0) += 1,
        }
    }
    for sym in &eq.rhs {
        match sym {
            WeSym::Var(v) => *var_net.entry(*v).or_insert(0) -= 1,
            WeSym::Ch(c) => *ch_net.entry(*c).or_insert(0) -= 1,
        }
    }
    if var_net.values().all(|c| *c == 0) {
        return ch_net.values().all(|c| *c == 0);
    }
    true
}

/// Materialize candidate assignments at a solved-form leaf.
///
/// Any assignment to the remaining free variables satisfies the equations, so
/// we produce (a) the minimal all-empty assignment (respecting tracked exact
/// lengths) and (b) when disequations exist, a distinct-values variant.
/// Candidates that violate an in-fragment disequation or an original exact
/// length are dropped.
fn materialize_candidates(
    state: &WeState,
    problem: &WeProblem,
    orig_lens: &HashMap<u32, usize>,
    comp_budget: &mut usize,
) -> Vec<WeAssignment> {
    let bound: HashMap<u32, &WeWord> = state.bindings.iter().map(|(v, w)| (*v, w)).collect();

    // Singleton regex constraints per free variable (multi-variable word
    // constraints are covered by the original-membership filter below).
    let mut singleton: HashMap<u32, Vec<WeRegex>> = HashMap::default();
    for rc in &state.res {
        if let [WeSym::Var(v)] = rc.word.as_slice() {
            singleton.entry(*v).or_default().push(rc.regex.clone());
        }
    }

    let free_value = |v: u32, distinct: bool| -> String {
        let len = state.lens.get(&v).copied();
        let (lo, hi) = state.bounds.get(&v).copied().unwrap_or((0, None));
        // Regex-constrained free variables take a verified witness from the
        // (implied) residual constraints; the membership filter below and
        // the caller's full validation keep this best-effort.
        if let Some(rs) = singleton.get(&v) {
            match len {
                Some(_) => {
                    if let Some(w) = we_regex::find_witness(rs, len) {
                        return w;
                    }
                }
                None => {
                    // Interval window: shortest witness if it fits, else a
                    // witness of exactly the lower bound.
                    if let Some(w) = we_regex::find_witness(rs, None) {
                        let n = w.chars().count();
                        if n >= lo && hi.is_none_or(|h| n <= h) {
                            return w;
                        }
                    }
                    if lo > 0 {
                        if let Some(w) = we_regex::find_witness(rs, Some(lo)) {
                            return w;
                        }
                    }
                }
            }
        }
        if distinct {
            let letter = char::from(b'a' + u8::try_from(v % 26).unwrap_or(0));
            let mut count = len.unwrap_or((v as usize) / 26 + 1).max(lo);
            if let Some(h) = hi {
                count = count.min(h).max(lo);
            }
            letter.to_string().repeat(count)
        } else {
            "a".repeat(len.unwrap_or(lo))
        }
    };

    let mut out = Vec::new();
    let variants: &[bool] = if problem.disequations.is_empty() {
        &[false]
    } else {
        &[false, true]
    };
    for &distinct in variants {
        if let Some(assignment) =
            finalize_candidate(problem, orig_lens, &bound, &free_value, distinct)
        {
            out.push(assignment);
        }
    }

    // Strings S1: WORD-LEVEL membership witnesses. The `free_value` path
    // above renders witnesses only for SINGLETON residual constraints
    // (`σ(v) ∈ R`); a residual whose word spans several symbols
    // (`σ(x·"lit"·y) ∈ R`, the slog/Stranger shape after Gaussian
    // elimination) had NO materializer, so every candidate fell to the
    // membership filter and the search exhausted. Solve the concat-membership
    // system directly with the bounded product-derivative witness BFS —
    // purely a SAT-side candidate generator (candidates still pass every
    // in-fragment filter below and the caller's full-model validation;
    // never feeds Unsat).
    if out.is_empty() && we_regex::s1_enabled() {
        if let Some(vals) = word_level_membership_vals(state, &singleton) {
            let fixed = |v: u32, distinct: bool| -> String {
                vals.get(&v)
                    .cloned()
                    .unwrap_or_else(|| free_value(v, distinct))
            };
            if let Some(assignment) = finalize_candidate(problem, orig_lens, &bound, &fixed, false)
            {
                out.push(assignment);
            }
        }
    }

    // Stage 3c: length-composition-guided witnesses. The independent
    // shortest-witness candidates above can all fail an ORIGINAL length
    // window on a BOUND variable (`x = y·z` with `4 ≤ |x| ≤ 5`: the
    // shortest `y·z` is too short). Expand each original variable
    // symbolically into (ground length, free-variable occurrence counts),
    // enumerate small length tuples for the free variables against the
    // original length windows, and render each free variable as a regex
    // witness of EXACTLY its chosen length. Purely a SAT-side candidate
    // generator: every candidate still passes the full in-fragment filter
    // pipeline (and the caller's full-model validation) — never feeds
    // `Unsat`. `comp_budget` bounds total work across ALL leaves of one
    // search; once spent, behavior is exactly today's (no candidates).
    if out.is_empty()
        && *comp_budget > 0
        && (!orig_lens.is_empty() || !problem.len_bounds.is_empty())
    {
        composition_candidates(
            state,
            problem,
            orig_lens,
            &bound,
            &singleton,
            comp_budget,
            &mut out,
        );
    }
    out
}

/// Word-level (multi-symbol) membership witness assignment for a solved-form
/// leaf (strings S1): for each residual constraint whose word spans several
/// symbols, solve the concatenation-membership system `u_1·…·u_n ∈ L(regex)`
/// with `u_i` constrained by the i-th symbol (a forced literal for ground
/// characters, the variable's singleton residuals + length window otherwise)
/// via the bounded product-derivative witness BFS
/// ([`we_regex::concat_membership_witness`]), and pin each free variable to
/// its part of the split.
///
/// Purely SAT-side and best-effort: `None` only means "no candidate from
/// this generator" (the caller falls through exactly as before). Every
/// returned value is re-filtered by `finalize_candidate` (original
/// memberships, disequations, lengths) and re-validated by the executor
/// before any SAT verdict — this generator can never affect Unsat.
fn word_level_membership_vals(
    state: &WeState,
    singleton: &HashMap<u32, Vec<WeRegex>>,
) -> Option<HashMap<u32, String>> {
    /// Part cap per constraint word (ground runs collapse into one part).
    const MAX_WITNESS_PARTS: usize = 48;

    let mut vals: HashMap<u32, String> = HashMap::default();
    let mut solved_any = false;
    for rc in &state.res {
        if rc.word.len() < 2 {
            continue; // singleton residuals are handled by `free_value`
        }
        // Build the parts: ground character runs collapse into one literal
        // part; each variable occurrence becomes a part constrained by the
        // variable's singleton residuals plus its length window.
        let mut parts: Vec<Vec<WeRegex>> = Vec::new();
        let mut part_vars: Vec<Option<u32>> = Vec::new();
        let mut ground_len = 0usize;
        let mut run = String::new();
        for sym in &rc.word {
            match sym {
                WeSym::Ch(c) => {
                    run.push(*c);
                    ground_len += 1;
                }
                WeSym::Var(v) => {
                    if !run.is_empty() {
                        parts.push(vec![WeRegex::lit(&run)]);
                        part_vars.push(None);
                        run.clear();
                    }
                    match vals.get(v) {
                        // Pinned by an earlier constraint: hold it fixed so
                        // cross-constraint assignments stay consistent.
                        Some(s) => {
                            ground_len += s.chars().count();
                            parts.push(vec![WeRegex::lit(s)]);
                            part_vars.push(None);
                        }
                        None => {
                            let mut set = singleton.get(v).cloned().unwrap_or_default();
                            let lo = var_lb(state, *v);
                            let hi = var_ub(state, *v);
                            if lo > 0 || hi.is_some() {
                                if let Some(r) = we_regex::len_interval_regex(lo, hi) {
                                    set.push(r);
                                }
                            }
                            parts.push(set);
                            part_vars.push(Some(*v));
                        }
                    }
                }
            }
        }
        if !run.is_empty() {
            parts.push(vec![WeRegex::lit(&run)]);
            part_vars.push(None);
        }
        if parts.len() > MAX_WITNESS_PARTS {
            continue; // oversized system: leave to the other generators
        }
        // The ground content must be spendable in full, plus the usual
        // witness budget for the free parts.
        let budget = ground_len.saturating_add(we_regex::witness_max_len());
        let Some(split) =
            we_regex::concat_membership_witness(&parts, std::slice::from_ref(&rc.regex), budget)
        else {
            continue; // not found — other constraints may still pin vars
        };
        for (slot, piece) in part_vars.iter().zip(split) {
            if let Some(v) = slot {
                match vals.get(v) {
                    // A repeated variable whose occurrences got different
                    // pieces cannot form a consistent assignment.
                    Some(prev) if *prev != piece => return None,
                    _ => {
                        vals.insert(*v, piece);
                    }
                }
            }
        }
        solved_any = true;
    }
    if solved_any && !vals.is_empty() {
        Some(vals)
    } else {
        None
    }
}

/// Resolve every variable value (memoized; bindings form a DAG), apply the
/// in-fragment filters (original exact lengths, interval bounds,
/// disequations, memberships), and return the surviving assignment.
fn finalize_candidate(
    problem: &WeProblem,
    orig_lens: &HashMap<u32, usize>,
    bound: &HashMap<u32, &WeWord>,
    free_value: &dyn Fn(u32, bool) -> String,
    distinct: bool,
) -> Option<WeAssignment> {
    let mut memo: HashMap<u32, String> = HashMap::default();
    fn resolve(
        v: u32,
        bound: &HashMap<u32, &WeWord>,
        memo: &mut HashMap<u32, String>,
        free_value: &dyn Fn(u32, bool) -> String,
        distinct: bool,
    ) -> String {
        if let Some(s) = memo.get(&v) {
            return s.clone();
        }
        let value = match bound.get(&v) {
            Some(word) => {
                let mut s = String::new();
                for sym in word.iter() {
                    match sym {
                        WeSym::Ch(c) => s.push(*c),
                        WeSym::Var(u) => {
                            s.push_str(&resolve(*u, bound, memo, free_value, distinct));
                        }
                    }
                }
                s
            }
            None => free_value(v, distinct),
        };
        memo.insert(v, value.clone());
        value
    }

    let mut assignment: WeAssignment = Vec::new();
    for v in 0..problem.num_vars {
        let value = resolve(v, bound, &mut memo, free_value, distinct);
        // Original exact-length filter (constraints may have been dropped
        // from the live map during var-var branching).
        if let Some(&l) = orig_lens.get(&v) {
            if value.chars().count() != l {
                return None;
            }
        }
        assignment.push((v, value));
    }
    // Original interval length-bound filter (Stage 3b).
    for b in &problem.len_bounds {
        let (_, value) = assignment.get(b.var as usize)?;
        let n = value.chars().count();
        if n < b.lo || matches!(b.hi, Some(h) if n > h) {
            return None;
        }
    }

    // In-fragment disequation filter.
    let eval_word = |w: &WeWord| -> String {
        let mut s = String::new();
        for sym in w {
            match sym {
                WeSym::Ch(c) => s.push(*c),
                WeSym::Var(v) => {
                    s.push_str(&resolve(*v, bound, &mut memo.clone(), free_value, distinct));
                }
            }
        }
        s
    };
    for deq in &problem.disequations {
        if eval_word(&deq.lhs) == eval_word(&deq.rhs) {
            return None;
        }
    }

    // Membership filter (both polarities). `matches` answers exactly or
    // `None` (resource cap) — unknown REJECTS the candidate: dropping a
    // candidate is always sound (at worst Exhausted instead of Sat).
    for m in &problem.memberships {
        let (_, value) = assignment.get(m.var as usize)?;
        if m.regex.matches(value) != Some(m.positive) {
            return None;
        }
    }

    Some(assignment)
}

/// Free-variable count cap for the length-composition enumeration.
const MAX_COMP_VARS: usize = 6;
/// Per-variable window width cap for the enumeration (lengths beyond a
/// variable's implied lower bound).
const MAX_COMP_SPAN: usize = 12;
/// Budget charge for rendering + filtering one feasible tuple (witness
/// search is much heavier than the per-tuple arithmetic check).
const COMP_RENDER_COST: usize = 64;

/// A symbolic length expansion: `(ground length, free-var occurrence counts)`.
type LenExpansion = (usize, HashMap<u32, usize>);

/// Expand `v` through the leaf bindings into `(ground_length,
/// free-variable occurrence counts)`. Saturating arithmetic — the counts
/// only feed feasibility checks, and the final filters re-verify exactly.
fn expand_len_counts(
    v: u32,
    bound: &HashMap<u32, &WeWord>,
    memo: &mut HashMap<u32, Option<LenExpansion>>,
) -> Option<LenExpansion> {
    if let Some(e) = memo.get(&v) {
        return e.clone();
    }
    // Cycle guard: bindings are acyclic by construction; defensive only.
    memo.insert(v, None);
    let result = match bound.get(&v) {
        None => {
            let mut counts: HashMap<u32, usize> = HashMap::default();
            counts.insert(v, 1);
            Some((0usize, counts))
        }
        Some(word) => {
            let mut ground = 0usize;
            let mut counts: HashMap<u32, usize> = HashMap::default();
            let mut ok = true;
            for sym in word.iter() {
                match sym {
                    WeSym::Ch(_) => ground = ground.saturating_add(1),
                    WeSym::Var(u) => match expand_len_counts(*u, bound, memo) {
                        Some((g, cs)) => {
                            ground = ground.saturating_add(g);
                            for (f, n) in cs {
                                let e = counts.entry(f).or_insert(0);
                                *e = e.saturating_add(n);
                            }
                        }
                        None => {
                            ok = false;
                            break;
                        }
                    },
                }
            }
            if ok {
                Some((ground, counts))
            } else {
                None
            }
        }
    };
    memo.insert(v, result.clone());
    result
}

/// Stage 3c enumeration body (see `materialize_candidates`). Pushes at most
/// one assignment into `out`.
#[allow(clippy::too_many_arguments)]
fn composition_candidates(
    state: &WeState,
    problem: &WeProblem,
    orig_lens: &HashMap<u32, usize>,
    bound: &HashMap<u32, &WeWord>,
    singleton: &HashMap<u32, Vec<WeRegex>>,
    comp_budget: &mut usize,
    out: &mut Vec<WeAssignment>,
) {
    // Symbolic expansion of every original variable over the free variables.
    let mut expand_memo: HashMap<u32, Option<LenExpansion>> = HashMap::default();
    let mut expansions: HashMap<u32, LenExpansion> = HashMap::default();
    for v in 0..problem.num_vars {
        if let Some(e) = expand_len_counts(v, bound, &mut expand_memo) {
            expansions.insert(v, e);
        }
    }

    // Length constraints over the expansions: `lo ≤ ground + Σ cnt·|f| ≤ hi`.
    // These are pre-render feasibility PRUNES only; the exact filters in
    // `finalize_candidate` re-verify every survivor.
    struct CompCon {
        ground: usize,
        terms: Vec<(usize, usize)>, // (free-var index, occurrence count)
        lo: usize,
        hi: Option<usize>,
    }

    // Free variables mentioned by any length-constrained original variable.
    let mut free_vars: Vec<u32> = Vec::new();
    let mut constrained: Vec<(u32, usize, Option<usize>)> = Vec::new();
    for (&v, &l) in orig_lens {
        constrained.push((v, l, Some(l)));
    }
    for b in &problem.len_bounds {
        if !orig_lens.contains_key(&b.var) {
            constrained.push((b.var, b.lo, b.hi));
        }
    }
    for &(v, _, _) in &constrained {
        if let Some((_, counts)) = expansions.get(&v) {
            free_vars.extend(counts.keys().copied());
        }
    }
    free_vars.sort_unstable();
    free_vars.dedup();
    if free_vars.is_empty() || free_vars.len() > MAX_COMP_VARS {
        return;
    }
    let idx_of: HashMap<u32, usize> = free_vars.iter().enumerate().map(|(i, &f)| (f, i)).collect();

    let mut cons: Vec<CompCon> = Vec::new();
    for &(v, lo, hi) in &constrained {
        let Some((ground, counts)) = expansions.get(&v) else {
            continue;
        };
        cons.push(CompCon {
            ground: *ground,
            terms: counts.iter().map(|(f, n)| (idx_of[f], *n)).collect(),
            lo,
            hi,
        });
    }
    if cons.is_empty() {
        return;
    }

    // Per-free-variable enumeration ranges from the leaf's tracked windows.
    let mut ranges: Vec<(usize, usize)> = Vec::with_capacity(free_vars.len());
    for &f in &free_vars {
        let lo = var_lb(state, f);
        let hi = var_ub(state, f)
            .unwrap_or(usize::MAX)
            .min(lo.saturating_add(MAX_COMP_SPAN));
        if hi < lo {
            return; // infeasible window: nothing to enumerate
        }
        ranges.push((lo, hi));
    }

    // Odometer enumeration, globally budget-bounded.
    let mut lens: Vec<usize> = ranges.iter().map(|r| r.0).collect();
    'tuples: loop {
        if *comp_budget == 0 {
            return;
        }
        *comp_budget -= 1;

        let feasible = cons.iter().all(|c| {
            let total = c.terms.iter().fold(c.ground, |acc, &(i, n)| {
                acc.saturating_add(lens[i].saturating_mul(n))
            });
            total >= c.lo && c.hi.is_none_or(|h| total <= h)
        });
        if feasible {
            if *comp_budget <= COMP_RENDER_COST {
                *comp_budget = 0;
                return;
            }
            *comp_budget -= COMP_RENDER_COST;

            // Render each free variable at exactly its chosen length.
            let mut vals: HashMap<u32, String> = HashMap::default();
            let mut ok = true;
            for (i, &f) in free_vars.iter().enumerate() {
                let l = lens[i];
                let value = match singleton.get(&f) {
                    Some(rs) => match we_regex::find_witness(rs, Some(l)) {
                        Some(w) => w,
                        None => {
                            ok = false;
                            break;
                        }
                    },
                    // Distinct letters per variable help the disequation
                    // filter without a second variant pass.
                    None => char::from(b'a' + u8::try_from(f % 26).unwrap_or(0))
                        .to_string()
                        .repeat(l),
                };
                vals.insert(f, value);
            }
            if ok {
                let fixed = |v: u32, _distinct: bool| -> String {
                    vals.get(&v).cloned().unwrap_or_default()
                };
                if let Some(assignment) =
                    finalize_candidate(problem, orig_lens, bound, &fixed, false)
                {
                    out.push(assignment);
                    return;
                }
            }
        }

        // Odometer increment.
        let mut i = 0;
        loop {
            if i == lens.len() {
                break 'tuples;
            }
            lens[i] += 1;
            if lens[i] <= ranges[i].1 {
                break;
            }
            lens[i] = ranges[i].0;
            i += 1;
        }
    }
}

/// Canonical key for visited-state deduplication: variables renamed by first
/// occurrence across the equation list, plus tracked lengths. Imperfect
/// (isomorphic states with different equation orders may key differently)
/// but sound — a missed dedup only costs work, never correctness.
fn canonical_key(state: &WeState) -> String {
    let mut rename: HashMap<u32, usize> = HashMap::default();
    let mut next = 0usize;
    let mut key = String::new();
    for eq in &state.eqs {
        for (side, word) in [("L", &eq.lhs), ("R", &eq.rhs)] {
            key.push_str(side);
            for sym in word.iter() {
                match sym {
                    WeSym::Ch(c) => {
                        key.push('c');
                        key.push(*c);
                    }
                    WeSym::Var(v) => {
                        let id = *rename.entry(*v).or_insert_with(|| {
                            let id = next;
                            next += 1;
                            id
                        });
                        key.push('v');
                        key.push_str(&id.to_string());
                        key.push(',');
                    }
                }
            }
        }
        key.push(';');
    }
    // Lengths of live (renamed) vars, in canonical order.
    let mut lens: Vec<(usize, usize)> = state
        .lens
        .iter()
        .filter_map(|(v, l)| rename.get(v).map(|id| (*id, *l)))
        .collect();
    lens.sort_unstable();
    for (id, l) in lens {
        key.push('#');
        key.push_str(&id.to_string());
        key.push('=');
        key.push_str(&l.to_string());
    }
    // Interval windows of live (renamed) vars MUST be part of the identity:
    // they prune branches, so states differing only in windows explore
    // different subtrees (windows on equation-absent vars are static
    // candidate filters and may be safely dropped from the key).
    let mut bnds: Vec<(usize, usize, i128)> = state
        .bounds
        .iter()
        .filter_map(|(v, (lo, hi))| {
            rename
                .get(v)
                .map(|id| (*id, *lo, hi.map_or(-1i128, |h| h as i128)))
        })
        .collect();
    bnds.sort_unstable();
    for (id, lo, hi) in bnds {
        key.push('%');
        key.push_str(&id.to_string());
        key.push('=');
        key.push_str(&lo.to_string());
        key.push(',');
        key.push_str(&hi.to_string());
    }
    // Regex constraints MUST be part of the identity: two states with
    // identical equations but different residual regexes explore DIFFERENT
    // subtrees (pruning differs), and deduplicating them could close a
    // branch that is only conflicting under the other state's constraints —
    // an unsound Unsat. Constraints are sorted by their raw form first
    // (deterministic), then serialized extending the rename map, so the key
    // never merges genuinely different constraint systems (a missed dedup
    // only costs work).
    let mut cons: Vec<&WeResCon> = state.res.iter().collect();
    cons.sort_unstable();
    for rc in cons {
        key.push('@');
        for sym in &rc.word {
            match sym {
                WeSym::Ch(c) => {
                    key.push('c');
                    key.push(*c);
                }
                WeSym::Var(v) => {
                    let id = *rename.entry(*v).or_insert_with(|| {
                        let id = next;
                        next += 1;
                        id
                    });
                    key.push('v');
                    key.push_str(&id.to_string());
                    key.push(',');
                }
            }
        }
        key.push(':');
        key.push_str(&format!("{:?}", rc.regex));
    }
    key
}

#[cfg(test)]
#[path = "word_eq_tests.rs"]
mod tests;
