// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Congruence for symbols the eager FP path does not interpret.
//!
//! The QF_FP pipeline Tseitin-encodes the assertions and bit-blasts only the
//! terms it recognises (`fp.*`, `to_fp`, the BV operators, the core
//! connectives). Everything else — an application of a user-declared function,
//! an array read — is left as a plain Tseitin atom or as fresh decomposed bits.
//! That is a *relaxation*, so it can never turn a satisfiable formula into
//! `unsat`, but on its own it drops congruence:
//!
//! ```smtlib
//! (declare-fun f (Float32) Bool)
//! (assert (= x y)) (assert (f x)) (assert (not (f y)))
//! ```
//!
//! is UNSAT — SMT-LIB 2.6 §5.2 makes `=` denote identity and every function
//! symbol denote a total function, so `x = y` forces `f(x) = f(y)` — yet the
//! bare relaxation happily satisfies it by giving the two unrelated atoms
//! different truth values (the wrong-SAT this module closes). The FP-sorted
//! argument matters only because FP is the one sort whose equality this
//! pipeline decides internally: the sorts routed through the EUF-carrying
//! solvers were never affected.
//!
//! Two jobs, in that order of importance:
//!
//! 1. Emit the Ackermann congruence clauses `⋀ᵢ aᵢ = bᵢ → f(a) = f(b)` for
//!    every pair of applications of one symbol. These are *valid* consequences,
//!    so they only ever remove spurious models.
//! 2. Report, via the scan's `unencodable` flag, any remaining structure this
//!    path cannot represent at all (arithmetic sorts, array equality, an
//!    argument pair whose equality cannot be bit-blasted, …). The caller must
//!    degrade a `sat` verdict to `unknown` in that case; `unsat` stays valid
//!    because the encoding is a relaxation of the input.

// #8529: Use deterministic hash sets in all builds.
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::{Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};
use ay_fp::FpSolver;
use std::collections::BTreeMap;

/// Applications of one symbol: `(application term, arguments)`.
type Application = (TermId, Vec<TermId>);

/// Largest same-symbol group that is Ackermannized in full. Beyond this the
/// pair count (n²/2) stops being worth it; the group is skipped and the scan
/// is marked unencodable so `sat` fails closed instead of dropping congruence.
const MAX_GROUP_APPLICATIONS: usize = 64;

/// The uninterpreted structure found under a set of FP-path assertions.
pub(super) struct ForeignScan {
    /// Same-symbol application groups eligible for congruence, in a
    /// deterministic (name, arity) order.
    groups: Vec<Vec<Application>>,
    /// True when some reachable term has a sort this path cannot represent at
    /// all (`Int`, `Real`, an array under a write, …). Callers that own the
    /// WHOLE formula must degrade a `sat` to `unknown` on this; the
    /// `fp.to_real` pipeline must NOT, because it deliberately hands its
    /// Real-sorted assertions to a separate mixed subproblem.
    pub(super) unencodable: bool,
}

impl ForeignScan {
    /// Whether anything at all needs congruence handling.
    pub(super) fn is_empty(&self) -> bool {
        self.groups.is_empty() && !self.unencodable
    }
}

/// A literal of a planned congruence clause, tagged with its namespace.
///
/// The FP bit-blaster numbers its variables independently of the Tseitin
/// encoding; the caller offsets the FP side when the two are concatenated.
#[derive(Debug, Clone, Copy)]
pub(super) enum PlanLit {
    /// Literal in the FP bit-blaster's variable space.
    Fp(i32),
    /// Literal in the Tseitin variable space.
    Tseitin(i32),
}

/// Congruence clauses to add to the combined CNF.
pub(super) struct CongruencePlan {
    /// Clauses in the mixed namespace described by [`PlanLit`].
    pub(super) clauses: Vec<Vec<PlanLit>>,
    /// True when some congruence obligation itself could not be encoded (an
    /// unrepresentable result sort, an argument pair whose equality will not
    /// bit-blast, a group too large to Ackermannize), so `sat` must degrade to
    /// `unknown`. Independent of the scan's `unencodable` flag.
    pub(super) incomplete: bool,
}

/// Sorts the eager FP path can represent for itself.
///
/// `RoundingMode` is carried as an uninterpreted sort but every surviving
/// RM-sorted term is a literal mode by the time this runs (`check_fp_support`
/// fails the solve closed otherwise), so it needs no bits of its own.
fn sort_is_representable(sort: &Sort) -> bool {
    match sort {
        Sort::Bool | Sort::FloatingPoint(..) | Sort::BitVec(_) => true,
        Sort::Uninterpreted(name) => name == "RoundingMode",
        _ => false,
    }
}

/// Symbols with a fixed interpretation. Anything else applied to arguments is
/// a user-declared function, whose only semantics is congruence.
///
/// MATCHING IS EXACT, NEVER BY PREFIX. This predicate decides whether an
/// application receives Ackermann congruence clauses, so a name wrongly
/// classified as interpreted silently loses congruence — and because both its
/// result and its FP arguments are "representable", nothing fails closed. The
/// result is a WRONG `sat` with a self-refuting model.
///
/// This function previously began `if name.starts_with("fp.") ||
/// name.starts_with("bv") { return true }`. Every one of those is a legal
/// user-declarable symbol: SMT-LIB simple symbols admit letters, digits and
/// `~ ! @ $ % ^ & * _ - + = < > . ? /`, so `bvf`, `bv`, `bvIsGood` and
/// `fp.foo` are all things a user may declare. Measured against z3 5.0.0 on
/// `(declare-fun N (Float32) Bool)` with `(= x y)`, `(N x)`, `(not (N y))`
/// — truth `unsat` — the prefix form answered `sat` for `bvf`, `bv` and
/// `bvIsGood`, with a model setting `x = y = +zero` while asserting both
/// `N(+zero)` and `¬N(+zero)`.
///
/// `bv*`, `select`, `store`, `concat` and friends are covered exactly by the
/// shared [`crate::features::is_builtin_symbol_name`] table — the same
/// predicate the EUF theory uses (`theories/euf.rs`) — which is exact-match
/// apart from a few deliberately-scoped prefixes. That table carries no `fp.*`
/// entries, so the floating-point operators are listed exactly here.
fn is_interpreted_name(name: &str) -> bool {
    if crate::features::is_builtin_symbol_name(name) {
        return true;
    }
    if is_fp_operator_name(name) {
        return true;
    }
    matches!(
        name,
        "true"
            | "false"
            | "and"
            | "or"
            | "not"
            | "=>"
            | "implies"
            | "xor"
            | "iff"
            | "="
            | "distinct"
            | "ite"
            | "fp"
            | "NaN"
            | "+zero"
            | "-zero"
            | "+oo"
            | "-oo"
            | "to_fp"
            | "to_fp_unsigned"
            | "select"
            | "store"
            | "concat"
            | "extract"
            | "repeat"
            | "zero_extend"
            | "sign_extend"
            | "rotate_left"
            | "rotate_right"
            | "RNE"
            | "RNA"
            | "RTP"
            | "RTN"
            | "RTZ"
            | "roundNearestTiesToEven"
            | "roundNearestTiesToAway"
            | "roundTowardPositive"
            | "roundTowardNegative"
            | "roundTowardZero"
    )
}

/// The SMT-LIB `FloatingPoint` operators, matched EXACTLY.
///
/// Listed here rather than reached by a `fp.` prefix test because `fp.foo` is a
/// symbol a user may legally declare, and treating it as interpreted would drop
/// its congruence clauses. `crate::features::is_builtin_symbol_name` carries no
/// `fp.*` entries, so this is the FP half of that table.
fn is_fp_operator_name(name: &str) -> bool {
    matches!(
        name,
        "fp.abs"
            | "fp.neg"
            | "fp.add"
            | "fp.sub"
            | "fp.mul"
            | "fp.div"
            | "fp.fma"
            | "fp.sqrt"
            | "fp.rem"
            | "fp.roundToIntegral"
            | "fp.min"
            | "fp.max"
            | "fp.leq"
            | "fp.lt"
            | "fp.geq"
            | "fp.gt"
            | "fp.eq"
            | "fp.isNormal"
            | "fp.isSubnormal"
            | "fp.isZero"
            | "fp.isInfinite"
            | "fp.isNaN"
            | "fp.isNegative"
            | "fp.isPositive"
            | "fp.to_real"
            | "fp.to_ubv"
            | "fp.to_sbv"
            | "fp.to_ieee_bv"
    )
}

/// Is this an application of a user-declared (uninterpreted) function?
fn is_uninterpreted(sym: &Symbol, args: &[TermId]) -> bool {
    if args.is_empty() {
        return false;
    }
    match sym {
        // Indexed symbols in AY are theory operators, never user functions.
        Symbol::Indexed(..) => false,
        Symbol::Named(name) => !is_interpreted_name(name),
        // `Symbol` is `#[non_exhaustive]`: an unknown future kind gets no
        // congruence clauses, and the sort walk still guards its operands.
        _ => false,
    }
}

/// Is `term` an array-sorted leaf — a variable, not a `store` or an `ite`?
///
/// Only for such a leaf can `select` be treated as a plain binary function:
/// with no write in sight, read-over-write and extensionality have nothing to
/// say and congruence is the whole theory. Any other array-sorted term (a
/// `store`, an array equality) is reported as unencodable by the walk.
fn is_array_leaf(terms: &TermStore, term: TermId) -> bool {
    matches!(terms.get(term), TermData::Var(..)) && matches!(terms.sort(term), Sort::Array(_))
}

/// Collect the uninterpreted structure reachable from `roots`.
pub(super) fn scan_foreign(terms: &TermStore, roots: &[TermId]) -> ForeignScan {
    let mut grouped: BTreeMap<(String, usize), Vec<Application>> = BTreeMap::new();
    let mut unencodable = false;
    let mut visited: HashSet<TermId> = HashSet::default();
    let mut stack: Vec<TermId> = roots.to_vec();

    while let Some(term) = stack.pop() {
        if !visited.insert(term) {
            continue;
        }
        if !sort_is_representable(terms.sort(term)) {
            unencodable = true;
        }
        match terms.get(term) {
            TermData::App(sym, args) => {
                let name = sym.name();
                // `(select <array var> i)`: congruence over the index, and the
                // array operand is deliberately NOT walked — it carries no
                // bits, and any other use of it is caught by the sort check.
                if name == "select" && args.len() == 2 && is_array_leaf(terms, args[0]) {
                    grouped
                        .entry((name.to_string(), 2))
                        .or_default()
                        .push((term, args.clone()));
                    stack.push(args[1]);
                    continue;
                }
                if is_uninterpreted(sym, args) {
                    grouped
                        .entry((name.to_string(), args.len()))
                        .or_default()
                        .push((term, args.clone()));
                }
                stack.extend_from_slice(args);
            }
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(cond, then_term, else_term) => {
                stack.push(*cond);
                stack.push(*then_term);
                stack.push(*else_term);
            }
            TermData::Let(bindings, body) => {
                for (_, value) in bindings {
                    stack.push(*value);
                }
                stack.push(*body);
            }
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
            _ => {}
        }
    }

    ForeignScan {
        groups: grouped.into_values().filter(|g| g.len() > 1).collect(),
        unencodable,
    }
}

/// Build the congruence clauses for a scan.
///
/// Every clause has the shape `¬(a₁ = b₁) ∨ … ∨ ¬(aₙ = bₙ) ∨ <results equal>`,
/// which is exactly the Ackermann instance of the congruence axiom and is
/// therefore valid in every structure: adding it cannot make a satisfiable
/// input `unsat`.
pub(super) fn plan_congruence(
    terms: &TermStore,
    fp_solver: &mut FpSolver<'_>,
    tseitin: &ay_core::TseitinResult,
    scan: &ForeignScan,
) -> CongruencePlan {
    let mut clauses: Vec<Vec<PlanLit>> = Vec::new();
    let mut incomplete = false;

    for group in &scan.groups {
        if group.len() > MAX_GROUP_APPLICATIONS {
            // Too many applications to Ackermannize; the dropped congruence
            // must not be reported as `sat`.
            incomplete = true;
            continue;
        }
        for i in 0..group.len() {
            for j in (i + 1)..group.len() {
                let (term_a, ref args_a) = group[i];
                let (term_b, ref args_b) = group[j];
                let Some(premises) =
                    argument_premises(terms, fp_solver, args_a.as_slice(), args_b.as_slice())
                else {
                    incomplete = true;
                    continue;
                };
                if premises.is_empty() {
                    // Every argument is the same interned term, so the two
                    // applications are the same term: nothing to relate.
                    continue;
                }
                let antecedent: Vec<PlanLit> =
                    premises.iter().map(|&lit| PlanLit::Fp(-lit)).collect();
                match terms.sort(term_a).clone() {
                    Sort::Bool => {
                        let (Some(var_a), Some(var_b)) =
                            (tseitin.var_for_term(term_a), tseitin.var_for_term(term_b))
                        else {
                            // Reached from an assertion yet absent from the
                            // Tseitin map: the atom lives only inside the FP
                            // bit-blaster's own namespace (an FP-sorted `ite`
                            // condition), where this plan cannot reach it.
                            incomplete = true;
                            continue;
                        };
                        let (lit_a, lit_b) = (var_a as i32, var_b as i32);
                        let mut forward = antecedent.clone();
                        forward.push(PlanLit::Tseitin(-lit_a));
                        forward.push(PlanLit::Tseitin(lit_b));
                        let mut backward = antecedent;
                        backward.push(PlanLit::Tseitin(lit_a));
                        backward.push(PlanLit::Tseitin(-lit_b));
                        clauses.push(forward);
                        clauses.push(backward);
                    }
                    Sort::FloatingPoint(..) => {
                        let equal = fp_solver.bitblast_fp_structural_eq(term_a, term_b);
                        let mut clause = antecedent;
                        clause.push(PlanLit::Fp(equal));
                        clauses.push(clause);
                    }
                    Sort::BitVec(_) => {
                        let Some(equal) = fp_solver.try_bitblast_bv_eq(term_a, term_b) else {
                            incomplete = true;
                            continue;
                        };
                        let mut clause = antecedent;
                        clause.push(PlanLit::Fp(equal));
                        clauses.push(clause);
                    }
                    _ => incomplete = true,
                }
            }
        }
    }

    CongruencePlan {
        clauses,
        incomplete,
    }
}

/// Literals asserting that each differing argument pair is equal, or `None`
/// when some pair's equality cannot be encoded in this path.
fn argument_premises(
    terms: &TermStore,
    fp_solver: &mut FpSolver<'_>,
    args_a: &[TermId],
    args_b: &[TermId],
) -> Option<Vec<i32>> {
    let mut premises = Vec::new();
    for (&arg_a, &arg_b) in args_a.iter().zip(args_b.iter()) {
        if arg_a == arg_b {
            continue;
        }
        let sort_a = terms.sort(arg_a).clone();
        if sort_a != *terms.sort(arg_b) {
            // Unreachable for well-sorted applications of one symbol at one
            // arity; fail closed rather than guess at the intended relation.
            return None;
        }
        match sort_a {
            Sort::FloatingPoint(..) => {
                premises.push(fp_solver.bitblast_fp_structural_eq(arg_a, arg_b));
            }
            Sort::BitVec(_) => premises.push(fp_solver.try_bitblast_bv_eq(arg_a, arg_b)?),
            _ => return None,
        }
    }
    Some(premises)
}
