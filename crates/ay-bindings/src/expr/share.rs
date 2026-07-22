// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! DAG-aware SMT-LIB serialization: share repeated subterms via `let`.
//!
//! [`Expr`] is an `Arc`-shared DAG, but the plain [`Display`](std::fmt::Display)
//! prints it as a TREE — every reference to a shared subterm re-prints that
//! subterm in full. For expressions produced by unrolling a loop over a state
//! machine (a value rebuilt by an `ite`-chain each iteration and read from every
//! match arm), the number of distinct nodes is polynomial but the unfolded tree
//! is EXPONENTIAL in the loop depth. This was observed as a 26 GB serialization
//! while model-checking a byte-loop parser proof: the cost was entirely in
//! `Expr`'s Display, not in building the (polynomially small) DAG.
//!
//! [`Expr::to_smtlib_shared`] prints the same expression with each non-trivial
//! subterm that is referenced more than once hoisted into a `let` binding, so
//! the output is linear in the number of DISTINCT nodes. SMT-LIB `let` is pure
//! (transparent) sharing, so the result is logically identical to `Display`.

use std::collections::{HashMap, HashSet};
use std::fmt::Write;
use std::sync::Arc;

use super::fold::rebuild_with_children;
use super::{Expr, ExprValue};
use crate::constraint::Constraint;
use crate::program::AYProgram;

/// A subterm is only worth a `let` binding when its unfolded (tree) size is at
/// least this large. Tiny shared terms are cheaper to re-print than to name,
/// and naming them would needlessly perturb output for small expressions (so
/// the existing `Display`-exact tests keep passing). This is a print-shape
/// heuristic, not a bound on anything: correctness does not depend on its value.
const SHARE_MIN_TREE_SIZE: u64 = 32;

/// Saturating cap for the tree-size estimate, so the estimate itself can never
/// blow up on the very DAGs this module exists to compress.
const TREE_SIZE_CAP: u64 = 1 << 20;

/// The share passes recurse to the DAG's DEPTH. `Expr::Display` guards its own
/// recursion with `stacker::maybe_grow`; these passes must too, or a deeply
/// nested (even polynomially small) DAG that Display would have rendered can
/// instead overflow the native stack here. Mirror Display's red zone / segment.
const SHARE_STACK_RED_ZONE: usize = 32 * 1024;
const SHARE_STACK_SIZE: usize = 1024 * 1024;

/// Identity of a node = the address of its shared `ExprValue` allocation. Two
/// `Expr`s that are `clone`s of each other share one `Arc<ExprValue>` and so
/// have the same id; structurally-equal-but-separately-built nodes do not (that
/// is fine — we only need to dedupe genuine sharing).
#[inline]
fn node_id(e: &Expr) -> usize {
    Arc::as_ptr(&e.value).cast::<()>() as usize
}

#[inline]
fn is_compound(e: &Expr) -> bool {
    e.children().next().is_some()
}

impl Expr {
    /// Render this expression as SMT-LIB, hoisting subterms that are shared (by
    /// `Arc` identity) more than once — and large enough to be worth it — into
    /// `let` bindings. Semantically identical to `Display`, but its size and
    /// running time are linear in the number of distinct nodes rather than the
    /// unfolded tree size.
    ///
    /// When nothing is worth sharing the output is byte-for-byte identical to
    /// `format!("{self}")`.
    #[must_use]
    pub fn to_smtlib_shared(&self) -> String {
        // Pass 1: reference counts + saturating tree sizes + free-var names.
        // Memoised by node identity, so it is O(distinct nodes), never the
        // exponential tree.
        let mut refs: HashMap<usize, u32> = HashMap::new();
        let mut size: HashMap<usize, u64> = HashMap::new();
        let mut free_vars: HashSet<String> = HashSet::new();
        count_refs(self, &mut refs, &mut size, &mut free_vars);

        let shareable = |e: &Self| -> bool {
            let id = node_id(e);
            is_compound(e)
                && refs.get(&id).copied().unwrap_or(0) > 1
                && size.get(&id).copied().unwrap_or(0) >= SHARE_MIN_TREE_SIZE
        };

        // Pass 2: assign let-names to shareable nodes in dependency-first
        // (post-order) order, so each binding may reference earlier ones.
        let mut names: HashMap<usize, String> = HashMap::new();
        let mut order: Vec<Self> = Vec::new();
        let mut visited: HashSet<usize> = HashSet::new();
        let mut counter: u64 = 0;
        assign_names(
            self,
            &shareable,
            &mut names,
            &mut order,
            &mut visited,
            &mut counter,
            &free_vars,
        );

        // Fast path: nothing shared -> byte-identical to plain Display.
        if order.is_empty() {
            return format!("{self}");
        }

        // Pass 3: emit nested lets (outermost = deepest dependency), then the
        // body. Each binding's definition and the body are rendered "shallowly":
        // shared sub-subterms are replaced by their let-name `Var`s, so the
        // existing `Display` prints each in size bounded by its UNIQUE subtree.
        let mut shallow_memo: HashMap<usize, Self> = HashMap::new();
        let mut out = String::new();
        for s in &order {
            let name = &names[&node_id(s)];
            let def = define(s, &names, &mut shallow_memo);
            let _ = write!(out, "(let (({name} {def})) ");
        }
        let body = define(self, &names, &mut shallow_memo);
        let _ = write!(out, "{body}");
        for _ in &order {
            out.push(')');
        }
        out
    }
}

/// Count references to each distinct node, its saturating tree size, and the
/// free variable names (so generated let-names can avoid colliding with them).
fn count_refs(
    e: &Expr,
    refs: &mut HashMap<usize, u32>,
    size: &mut HashMap<usize, u64>,
    free_vars: &mut HashSet<String>,
) {
    stacker::maybe_grow(SHARE_STACK_RED_ZONE, SHARE_STACK_SIZE, || {
        if let ExprValue::Var { name } = e.value.as_ref() {
            free_vars.insert(name.clone());
        }
        let id = node_id(e);
        let c = refs.entry(id).or_insert(0);
        *c += 1;
        if *c > 1 {
            return; // already descended on the first visit; size already recorded
        }
        let mut sz: u64 = 1;
        for ch in e.children() {
            count_refs(ch, refs, size, free_vars);
            sz = sz.saturating_add(size.get(&node_id(ch)).copied().unwrap_or(1));
        }
        size.insert(id, sz.min(TREE_SIZE_CAP));
    });
}

/// Post-order DFS assigning a fresh let-name to each shareable node. Memoised by
/// identity, so O(distinct nodes). The root is never shareable (its refcount is
/// 1), so it is emitted as the `let` body rather than bound.
fn assign_names(
    e: &Expr,
    shareable: &impl Fn(&Expr) -> bool,
    names: &mut HashMap<usize, String>,
    order: &mut Vec<Expr>,
    visited: &mut HashSet<usize>,
    counter: &mut u64,
    free_vars: &HashSet<String>,
) {
    stacker::maybe_grow(SHARE_STACK_RED_ZONE, SHARE_STACK_SIZE, || {
        let id = node_id(e);
        if !visited.insert(id) {
            return;
        }
        for ch in e.children() {
            assign_names(ch, shareable, names, order, visited, counter, free_vars);
        }
        if shareable(e) {
            let name = fresh_name(counter, free_vars);
            names.insert(id, name);
            order.push(e.clone());
        }
    });
}

/// A let-name that is a valid unquoted SMT-LIB simple symbol (so it round-trips
/// through `format_symbol` unchanged on the reference side) and does not collide
/// with any free variable of the expression.
fn fresh_name(counter: &mut u64, avoid: &HashSet<String>) -> String {
    loop {
        let name = format!("ay_let_share_{counter}");
        *counter += 1;
        if !avoid.contains(&name) {
            return name;
        }
    }
}

/// Rewrite `e` so that every SHARED proper subterm is replaced by its let-name
/// `Var`. Memoised by identity. A shared node maps to its `Var`; a unique node
/// is rebuilt with shallow children.
fn shallow(e: &Expr, names: &HashMap<usize, String>, memo: &mut HashMap<usize, Expr>) -> Expr {
    stacker::maybe_grow(SHARE_STACK_RED_ZONE, SHARE_STACK_SIZE, || {
        let id = node_id(e);
        if let Some(name) = names.get(&id) {
            return Expr::var(name.clone(), e.sort().clone());
        }
        if let Some(m) = memo.get(&id) {
            return m.clone();
        }
        let new_children: Vec<Expr> = e.children().map(|c| shallow(c, names, memo)).collect();
        let r = if new_children.is_empty() {
            e.clone()
        } else {
            rebuild_with_children(e, new_children)
        };
        memo.insert(id, r.clone());
        r
    })
}

/// The definition of a (shared, or root) node: the node expanded ONE level, with
/// its children rendered shallowly. The node itself keeps its operator (it is
/// what we are defining / the body), only its sub-subterms are shared away.
fn define(s: &Expr, names: &HashMap<usize, String>, memo: &mut HashMap<usize, Expr>) -> Expr {
    let new_children: Vec<Expr> = s.children().map(|c| shallow(c, names, memo)).collect();
    if new_children.is_empty() {
        s.clone()
    } else {
        rebuild_with_children(s, new_children)
    }
}

/// Count the distinct nodes (by `Arc` identity) reachable from `e`, adding them
/// to `seen`, stopping early once `seen` reaches `cap`. This is the size of the
/// SHARED serialization (what `to_smtlib_shared` emits), NOT the exponential
/// unfolded tree — so it is safe to call on the very DAGs that would blow up if
/// printed. O(distinct nodes), guarded against deep recursion.
fn count_distinct_into(e: &Expr, seen: &mut HashSet<usize>, cap: usize) {
    if seen.len() >= cap {
        return;
    }
    stacker::maybe_grow(SHARE_STACK_RED_ZONE, SHARE_STACK_SIZE, || {
        if !seen.insert(node_id(e)) {
            return;
        }
        for ch in e.children() {
            if seen.len() >= cap {
                break;
            }
            count_distinct_into(ch, seen, cap);
        }
    });
}

/// The expressions a command embeds at top level (the ones whose serialization
/// can be large). Non-term commands (declarations, push/pop, check-sat, …) embed
/// none. Kept in sync with `Constraint`'s `Display`.
fn constraint_exprs(c: &Constraint) -> Vec<&Expr> {
    match c {
        Constraint::Assert { expr, .. } | Constraint::SoftAssert { expr, .. } => vec![expr],
        Constraint::DefineFun { body, .. } => vec![body],
        Constraint::Rule {
            head: Some(head),
            body,
        } => vec![body, head],
        Constraint::Rule { head: None, body } => vec![body],
        Constraint::Query(rel) => vec![rel],
        Constraint::Maximize(e) | Constraint::Minimize(e) => vec![e],
        Constraint::CheckSatAssuming(es) | Constraint::GetValue(es) => es.iter().collect(),
        _ => Vec::new(),
    }
}

impl AYProgram {
    /// A saturating estimate of this program's serialized size, measured in
    /// distinct SMT-LIB term nodes across all commands (subterms shared by `Arc`
    /// identity within a command are counted once, mirroring how `Display` now
    /// serializes them via `let`). Returns as soon as the count reaches `cap`, so
    /// it is cheap even on a program whose unfolded form would be astronomically
    /// large.
    ///
    /// Consumers (e.g. a model checker writing `.smt2` files) use this to fail
    /// closed — report the harness as resource-exhausted/inconclusive — BEFORE
    /// materializing a pathologically large serialization and risking OOM, rather
    /// than after.
    #[must_use]
    pub fn serialized_node_estimate(&self, cap: usize) -> usize {
        let mut seen: HashSet<usize> = HashSet::new();
        for c in self.commands() {
            for e in constraint_exprs(c) {
                count_distinct_into(e, &mut seen, cap);
                if seen.len() >= cap {
                    return cap;
                }
            }
        }
        seen.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sort::Sort;

    /// The whole point: an expression whose DAG is small but whose unfolded tree
    /// is EXPONENTIAL must serialize in size linear in its distinct nodes. Each
    /// `ite` here shares the SAME `prev` Arc in both branches, so the naive tree
    /// doubles every level — at depth 30 that is ~10^9 nodes, which `Display`
    /// would try to materialize. `to_smtlib_shared` must stay tiny and fast.
    #[test]
    fn exponential_dag_serializes_linearly() {
        let cond = Expr::var("c", Sort::bool());
        let mut node = Expr::var("x", Sort::bitvec(8));
        for _ in 0..30 {
            // clone() shares the same Arc in both branches -> refcount 2.
            node = Expr::ite(cond.clone(), node.clone(), node.clone());
        }
        let shared = node.to_smtlib_shared();
        // Linear in depth (~30 lets), nowhere near the 2^30 unfolded tree.
        assert!(
            shared.len() < 20_000,
            "shared output must be linear, got {} bytes",
            shared.len()
        );
        assert!(
            shared.contains("(let "),
            "must hoist shared subterms into let"
        );
        assert!(
            shared.contains("ay_let_share_0"),
            "must bind shared subterms"
        );
        // Balanced parentheses (well-formed s-expression).
        let opens = shared.matches('(').count();
        let closes = shared.matches(')').count();
        assert_eq!(opens, closes, "parentheses must balance");
    }

    /// Fidelity: when nothing crosses the sharing threshold the output is
    /// byte-for-byte identical to the plain `Display`, so existing consumers and
    /// snapshot tests are unaffected.
    #[test]
    fn no_sharing_is_identical_to_display() {
        let a = Expr::var("a", Sort::bitvec(8));
        let b = Expr::var("b", Sort::bitvec(8));
        let e = a.clone().eq(b.clone()).and(b.eq(a));
        assert_eq!(e.to_smtlib_shared(), format!("{e}"));
    }

    /// The exact path the model checker serializes through:
    /// `Constraint::Assert` Display must also be linear on an exponential DAG.
    /// (The 26 GB blowup was `AYProgram` Display -> `Constraint` Display ->
    /// `Expr` Display on an asserted state-machine DAG.)
    #[test]
    fn asserted_exponential_dag_serializes_linearly() {
        use crate::constraint::Constraint;
        let cond = Expr::var("c", Sort::bool());
        let mut node = Expr::var("x", Sort::bitvec(8));
        for _ in 0..30 {
            node = Expr::ite(cond.clone(), node.clone(), node.clone());
        }
        // node is bitvec; assert an equality so the assert body is boolean.
        let assertion = node.clone().eq(node);
        let c = Constraint::assert(assertion);
        let text = format!("{c}");
        assert!(
            text.len() < 40_000,
            "asserted DAG must serialize linearly, got {} bytes",
            text.len()
        );
        assert!(text.starts_with("(assert "), "still an assert command");
        assert!(text.contains("(let "), "assert body shares via let");
    }

    /// A large subterm referenced twice is hoisted once and referenced by name
    /// at both use sites.
    #[test]
    fn large_repeated_subterm_is_hoisted_once() {
        // Build a bitvec subterm with > SHARE_MIN_TREE_SIZE distinct nodes.
        let mut s = Expr::var("v", Sort::bitvec(8));
        for i in 0..20u32 {
            s = Expr::ite(
                Expr::var(format!("c{i}"), Sort::bool()),
                s,
                Expr::bitvec_const(i, 8),
            );
        }
        // Use the SAME Arc twice.
        let eq = s.clone().eq(s.clone());
        let out = eq.to_smtlib_shared();
        assert!(
            out.contains("(let "),
            "repeated large subterm must be let-bound"
        );
        // The binding name appears at least twice (the two operands of `=`),
        // plus once at the binding site.
        let n = out.matches("ay_let_share_0").count();
        assert!(
            n >= 3,
            "shared name should appear at binding + 2 uses, got {n}"
        );
    }

    /// Build an exponential-tree / polynomial-DAG bitvec value (each `ite` shares
    /// the same `prev` Arc in both branches), used by the per-arm tests below.
    fn exp_dag() -> Expr {
        let cond = Expr::var("c", Sort::bool());
        let mut node = Expr::var("x", Sort::bitvec(8));
        for _ in 0..30 {
            node = Expr::ite(cond.clone(), node.clone(), node.clone());
        }
        node
    }

    /// Every Expr-embedding Constraint arm — not just `assert` — must serialize
    /// DAG-aware. These lock in that the CHC/OMT/define-fun/get-value paths route
    /// through `to_smtlib_shared` so an exponential DAG stays linear in bytes.
    #[test]
    fn rule_body_exponential_dag_serializes_linearly() {
        use crate::constraint::Constraint;
        let body = exp_dag().clone().eq(exp_dag()); // boolean rule body
        let head = Expr::var("P", Sort::bool());
        let text = format!(
            "{}",
            Constraint::Rule {
                head: Some(head),
                body
            }
        );
        assert!(
            text.len() < 60_000,
            "rule must serialize linearly, got {}",
            text.len()
        );
        assert!(text.starts_with("(rule (=> "), "still a horn rule");
        assert!(text.contains("(let "), "rule body shares via let");
    }

    #[test]
    fn define_fun_body_exponential_dag_serializes_linearly() {
        use crate::constraint::Constraint;
        let c = Constraint::DefineFun {
            name: "f".to_string(),
            params: vec![],
            return_sort: Sort::bitvec(8),
            body: exp_dag(),
        };
        let text = format!("{c}");
        assert!(
            text.len() < 60_000,
            "define-fun body must serialize linearly, got {}",
            text.len()
        );
        assert!(text.starts_with("(define-fun f () "), "still a define-fun");
        assert!(text.contains("(let "), "define-fun body shares via let");
    }

    #[test]
    fn query_exponential_dag_serializes_linearly() {
        use crate::constraint::Constraint;
        let text = format!("{}", Constraint::Query(exp_dag().clone().eq(exp_dag())));
        assert!(
            text.len() < 60_000,
            "query must serialize linearly, got {}",
            text.len()
        );
        assert!(text.starts_with("(query "), "still a query");
        assert!(text.contains("(let "), "query rel shares via let");
    }

    /// The serialized-size estimate must reflect DISTINCT nodes (the shared
    /// serialization), not the exponential unfolded tree — so a model checker can
    /// cheaply fail closed before serializing instead of OOMing.
    #[test]
    fn serialized_node_estimate_is_linear_on_exponential_dag() {
        let mut p = AYProgram::new();
        p.assert(exp_dag().clone().eq(exp_dag()));
        // The unfolded tree is ~2^31 nodes; the distinct-node estimate is tiny.
        let est = p.serialized_node_estimate(1_000_000);
        assert!(
            est < 1_000,
            "estimate must be linear in distinct nodes, got {est}"
        );
        // The cap is honored (early-out), so the call is cheap on huge programs.
        assert_eq!(p.serialized_node_estimate(10), 10);
        // An empty program embeds no term nodes.
        assert_eq!(AYProgram::new().serialized_node_estimate(1_000_000), 0);
    }
}
