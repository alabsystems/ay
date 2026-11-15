//! The incremental difference-logic graph and its Bellman-Ford feasibility
//! check.
//!
//! # Encoding
//!
//! A constraint `x - y <= c` is stored as a directed edge `y → x` with weight
//! `c` (see [`crate::atom`]). A satisfying assignment is exactly a set of
//! *potentials* `π` with `π(x) − π(y) <= c` for every edge `y → x : c`. The
//! shortest-path distances `d(v)` from a super-source `S` (with a zero-weight
//! edge `S → v` to every vertex) satisfy the triangle inequality
//! `d(x) <= d(y) + c`, i.e. `d(x) − d(y) <= c` — so the distances *are* a model.
//!
//! A negative-weight cycle is reachable iff the system is infeasible; its edge
//! set proves `0 < 0` and seeds the unsat core.
//!
//! # Algorithm
//!
//! We run Bellman-Ford from the implicit super-source (all vertices start at
//! distance `0`, which is equivalent to a zero-weight super-source edge to
//! each). `|V|` relaxation rounds; a relaxation possible in the `|V|`-th round
//! exposes a negative cycle, which we extract by walking predecessor pointers.
//! Complexity `O(|V|·|E|)`. This is the textbook, easy-to-audit core; an
//! incremental SSSP can replace it later behind the same interface.

use crate::atom::Negate;
use crate::weight::Weight;

/// Vertex-count limit of [`DiffGraph::check`]: a graph with `VAR_LIMIT` or more
/// vertices is [`DiffResult::Refused`] rather than decided.
///
/// Bellman-Ford keeps two dense per-vertex tables, so the vertex count is an
/// allocation size. `2^28` vertices is far beyond anything the `O(|V|·|E|)`
/// check could finish on, and the refusal happens before anything is allocated.
pub const VAR_LIMIT: usize = 1 << 28;

/// Result of [`DiffGraph::check`].
#[derive(Clone, Debug)]
pub enum DiffResult<W> {
    /// Satisfiable; carries a potential assignment `model[v]` per vertex such
    /// that every constraint holds by direct substitution.
    Sat { model: Vec<W> },
    /// Unsatisfiable; carries a negative cycle as the ordered list of edge
    /// indices (into [`DiffGraph::edges`]) forming the cycle. Summing their
    /// weights yields a value `< 0`.
    Unsat { cycle: Vec<usize> },
    /// Not decided; nothing is claimed about the system. The graph has
    /// [`VAR_LIMIT`] or more vertices, or an internal invariant (every edge
    /// endpoint is a vertex, a predecessor walk closes into a cycle) did not
    /// hold. Callers treat this as *unknown*.
    Refused,
}

/// One stored edge `from → to : weight`, i.e. the constraint `to - from <= weight`.
#[derive(Clone, Debug)]
pub struct GraphEdge<W> {
    pub from: usize,
    pub to: usize,
    pub weight: W,
}

/// An incremental difference-logic constraint graph over `n_vars` vertices.
#[derive(Clone, Debug)]
pub struct DiffGraph<W> {
    n_vars: usize,
    edges: Vec<GraphEdge<W>>,
}

impl<W: Weight + Negate> DiffGraph<W> {
    /// Create an empty graph over `n_vars` vertices `0..n_vars`.
    pub fn new(n_vars: usize) -> Self {
        Self {
            n_vars,
            edges: Vec::new(),
        }
    }

    /// Number of vertices.
    pub fn num_vars(&self) -> usize {
        self.n_vars
    }

    /// The stored edges (constraint `to - from <= weight` each).
    pub fn edges(&self) -> &[GraphEdge<W>] {
        &self.edges
    }

    /// Ensure vertex index `v` exists, growing the vertex set if needed.
    pub fn ensure_var(&mut self, v: usize) {
        if v >= self.n_vars {
            // `v == usize::MAX` saturates to a vertex count of `usize::MAX`,
            // which is at or above `VAR_LIMIT`, so `check` refuses the graph
            // rather than deciding one that lacks vertex `v`.
            self.n_vars = v.saturating_add(1);
        }
    }

    /// Add the constraint `x - y <= c` (edge `y → x : c`). Incremental: callers
    /// may interleave [`Self::add_constraint`] and [`Self::check`]. Returns the
    /// index of the newly added edge.
    pub fn add_constraint(&mut self, x: usize, y: usize, c: W) -> usize {
        self.ensure_var(x);
        self.ensure_var(y);
        let idx = self.edges.len();
        // constraint x - y <= c  ⇒  edge from=y to=x weight=c  (to - from <= w)
        self.edges.push(GraphEdge {
            from: y,
            to: x,
            weight: c,
        });
        idx
    }

    /// Decide feasibility.
    ///
    /// On `Sat`, the returned potentials are self-certified: every constraint is
    /// re-checked by direct substitution under `debug_assert!` before return.
    /// On `Unsat`, the returned cycle is self-certified: its summed weight is
    /// `debug_assert!`-ed to be `< 0`.
    pub fn check(&self) -> DiffResult<W> {
        match self.bellman_ford() {
            BfOutcome::Feasible { dist } => {
                self.certify_model(&dist);
                DiffResult::Sat { model: dist }
            }
            BfOutcome::NegativeCycle { cycle } => {
                self.certify_cycle(&cycle);
                DiffResult::Unsat { cycle }
            }
            BfOutcome::Refused => DiffResult::Refused,
        }
    }

    /// Bellman-Ford from the implicit zero-distance super-source.
    fn bellman_ford(&self) -> BfOutcome<W> {
        let n = self.n_vars;
        if n >= VAR_LIMIT {
            return BfOutcome::Refused;
        }
        // All vertices start reachable at distance 0 (super-source with 0-weight
        // edges). This finds shortest paths over the whole graph in one shot.
        let mut dist: Vec<W> = vec![W::zero(); n];
        // pred[v] = index of the edge last used to relax v (for cycle recovery).
        let mut pred: Vec<Option<usize>> = vec![None; n];

        let mut changed_vertex: Option<usize> = None;
        // n rounds: a relaxation in round n (the extra round) ⇒ negative cycle.
        for round in 0..n {
            changed_vertex = None;
            let mut any = false;
            for (ei, e) in self.edges.iter().enumerate() {
                // relax to via from: dist[to] > dist[from] + w ?
                // `add_constraint` grows the vertex set to cover both
                // endpoints, so a missing one is a broken invariant: refuse.
                let (Some(d_from), Some(d_to)) = (dist.get(e.from), dist.get(e.to)) else {
                    return BfOutcome::Refused;
                };
                let cand = d_from.add(&e.weight);
                if cand < *d_to {
                    let (Some(d_slot), Some(p_slot)) = (dist.get_mut(e.to), pred.get_mut(e.to))
                    else {
                        return BfOutcome::Refused;
                    };
                    *d_slot = cand;
                    *p_slot = Some(ei);
                    any = true;
                    changed_vertex = Some(e.to);
                }
            }
            if !any {
                // Converged early: no negative cycle.
                return BfOutcome::Feasible { dist };
            }
            // If this is the final allowed round and something still changed,
            // there is a negative cycle reachable from `changed_vertex`.
            let _ = round;
        }

        // We completed n rounds and the last one still relaxed something ⇒ a
        // negative cycle exists. Recover it from the predecessor chain.
        match changed_vertex {
            Some(start) => match self.recover_cycle(start, &pred) {
                Some(cycle) => BfOutcome::NegativeCycle { cycle },
                None => BfOutcome::Refused,
            },
            // Defensive: `any` was true so changed_vertex must be Some. If not,
            // treat as feasible (the distances are valid).
            None => BfOutcome::Feasible { dist },
        }
    }

    /// Recover a concrete negative cycle as a list of edge indices, given that a
    /// relaxation was still possible from `start` after `n` rounds.
    ///
    /// Walk predecessors `n` times to land *inside* a cycle, then follow
    /// predecessors collecting edges until we return to that vertex.
    ///
    /// `None` when the predecessor chain does not behave as Bellman-Ford
    /// guarantees (a vertex or edge index out of range, a cycle vertex with no
    /// predecessor, or a walk that does not close within the edge count); the
    /// caller then refuses to decide.
    fn recover_cycle(&self, start: usize, pred: &[Option<usize>]) -> Option<Vec<usize>> {
        // Step back n times to guarantee we are on the cycle.
        let mut v = start;
        for _ in 0..self.n_vars {
            v = match pred.get(v) {
                Some(Some(ei)) => self.edges.get(*ei)?.from,
                Some(None) => break,
                None => return None,
            };
        }
        // Now v is on the cycle. Collect edges from v back to v.
        let cycle_node = v;
        let mut edges_rev: Vec<usize> = Vec::new();
        let mut cur = cycle_node;
        loop {
            // A cycle node always has a predecessor.
            let ei = pred.get(cur).copied().flatten()?;
            edges_rev.push(ei);
            cur = self.edges.get(ei)?.from;
            if cur == cycle_node {
                break;
            }
            // Safety valve: never loop longer than the edge count. A walk
            // that has not closed by then is not a cycle; refuse it rather
            // than report it as one.
            if edges_rev.len() > self.edges.len() {
                return None;
            }
        }
        edges_rev.reverse();
        Some(edges_rev)
    }

    /// `debug_assert` that the model satisfies every stored constraint by direct
    /// substitution: for edge `from → to : w`, check `model[to] - model[from] <= w`,
    /// i.e. `model[to] <= model[from] + w`.
    fn certify_model(&self, model: &[W]) {
        for e in &self.edges {
            // An endpoint missing from the model fails the certificate.
            let holds = match (model.get(e.from), model.get(e.to)) {
                (Some(from), Some(to)) => *to <= from.add(&e.weight),
                _ => false,
            };
            debug_assert!(
                holds,
                "diff-logic SAT self-cert failed: constraint v{} - v{} <= {:?} violated by model \
                 (lhs v{}={:?}, v{}={:?})",
                e.to,
                e.from,
                e.weight,
                e.to,
                model.get(e.to),
                e.from,
                model.get(e.from),
            );
        }
    }

    /// `debug_assert` that the recovered cycle is a real cycle whose summed edge
    /// weight is `< 0`.
    fn certify_cycle(&self, cycle: &[usize]) {
        debug_assert!(!cycle.is_empty(), "diff-logic UNSAT cert: empty cycle");
        // Check it forms a closed walk: each edge's `to` == next edge's `from`.
        // An edge index outside the edge list fails the certificate.
        for w in cycle.windows(2) {
            let contiguous = match *w {
                [ai, bi] => match (self.edges.get(ai), self.edges.get(bi)) {
                    (Some(a), Some(b)) => a.to == b.from,
                    _ => false,
                },
                _ => false,
            };
            debug_assert!(
                contiguous,
                "diff-logic UNSAT cert: cycle not contiguous at edges {w:?}"
            );
        }
        if let (Some(&fi), Some(&li)) = (cycle.first(), cycle.last()) {
            let closes = match (self.edges.get(fi), self.edges.get(li)) {
                (Some(first), Some(last)) => last.to == first.from,
                _ => false,
            };
            debug_assert!(closes, "diff-logic UNSAT cert: cycle does not close");
        }
        // Sum weights and assert < 0.
        let mut sum = W::zero();
        for &ei in cycle {
            let edge = self.edges.get(ei);
            debug_assert!(
                edge.is_some(),
                "diff-logic UNSAT cert: edge index {ei} out of range"
            );
            if let Some(e) = edge {
                sum = sum.add(&e.weight);
            }
        }
        debug_assert!(
            sum < W::zero(),
            "diff-logic UNSAT cert: cycle weight {sum:?} is not negative"
        );
    }
}

enum BfOutcome<W> {
    Feasible { dist: Vec<W> },
    NegativeCycle { cycle: Vec<usize> },
    Refused,
}

#[cfg(test)]
mod tests {
    use super::*;

    type TestResult = Result<(), Box<dyn std::error::Error>>;

    /// `model[a] - model[b]`, or an error if either reading is missing or the
    /// difference overflows.
    fn model_diff(model: &[i64], a: usize, b: usize) -> Result<i64, Box<dyn std::error::Error>> {
        let x = *model
            .get(a)
            .ok_or("model has no reading for the left variable")?;
        let y = *model
            .get(b)
            .ok_or("model has no reading for the right variable")?;
        Ok(x.checked_sub(y).ok_or("model difference overflows i64")?)
    }

    /// Summed weight of `cycle`'s edges in `g`.
    fn cycle_weight(
        g: &DiffGraph<i64>,
        cycle: &[usize],
    ) -> Result<i64, Box<dyn std::error::Error>> {
        let mut sum = 0i64;
        for &e in cycle {
            let w = g
                .edges()
                .get(e)
                .ok_or("cycle names an edge not in the graph")?
                .weight;
            sum = sum.checked_add(w).ok_or("cycle weight overflows i64")?;
        }
        Ok(sum)
    }

    #[test]
    fn empty_is_sat() {
        let g = DiffGraph::<i64>::new(3);
        assert!(matches!(g.check(), DiffResult::Sat { .. }));
    }

    #[test]
    fn simple_sat_chain() -> TestResult {
        // x - y <= 5, y - z <= 3  ⇒ sat
        let mut g = DiffGraph::<i64>::new(3);
        g.add_constraint(0, 1, 5); // x - y <= 5
        g.add_constraint(1, 2, 3); // y - z <= 3
        match g.check() {
            DiffResult::Sat { model } => {
                assert!(model_diff(&model, 0, 1)? <= 5);
                assert!(model_diff(&model, 1, 2)? <= 3);
                Ok(())
            }
            DiffResult::Unsat { .. } | DiffResult::Refused => Err("expected sat".into()),
        }
    }

    #[test]
    fn two_cycle_unsat() -> TestResult {
        // x - y <= -1 and y - x <= -1  ⇒ sum cycle weight -2 < 0  ⇒ unsat
        let mut g = DiffGraph::<i64>::new(2);
        g.add_constraint(0, 1, -1);
        g.add_constraint(1, 0, -1);
        match g.check() {
            DiffResult::Unsat { cycle } => {
                let sum = cycle_weight(&g, &cycle)?;
                assert!(sum < 0);
                assert_eq!(cycle.len(), 2);
                Ok(())
            }
            DiffResult::Sat { .. } | DiffResult::Refused => Err("expected unsat".into()),
        }
    }

    #[test]
    fn equal_cycle_is_sat() -> TestResult {
        // x - y <= 1 and y - x <= -1  ⇒ x - y = 1, feasible (cycle weight 0)
        let mut g = DiffGraph::<i64>::new(2);
        g.add_constraint(0, 1, 1);
        g.add_constraint(1, 0, -1);
        match g.check() {
            DiffResult::Sat { model } => {
                assert_eq!(model_diff(&model, 0, 1)?, 1);
                Ok(())
            }
            DiffResult::Unsat { .. } | DiffResult::Refused => {
                Err("expected sat (zero-weight cycle)".into())
            }
        }
    }

    #[test]
    fn three_cycle_unsat() -> TestResult {
        // x-y<=1, y-z<=1, z-x<=-3  ⇒ cycle 1+1-3=-1 <0 unsat
        let mut g = DiffGraph::<i64>::new(3);
        g.add_constraint(0, 1, 1);
        g.add_constraint(1, 2, 1);
        g.add_constraint(2, 0, -3);
        match g.check() {
            DiffResult::Unsat { cycle } => {
                let sum = cycle_weight(&g, &cycle)?;
                assert!(sum < 0);
                Ok(())
            }
            DiffResult::Sat { .. } | DiffResult::Refused => Err("expected unsat".into()),
        }
    }

    #[test]
    fn negative_self_loop_unsat() -> TestResult {
        // x - x <= -1  ⇒ 0 <= -1  ⇒ unsat (1-edge negative cycle)
        let mut g = DiffGraph::<i64>::new(1);
        g.add_constraint(0, 0, -1);
        match g.check() {
            DiffResult::Unsat { cycle } => {
                assert_eq!(cycle.len(), 1);
                let e = cycle.first().ok_or("empty cycle")?;
                let edge = g
                    .edges()
                    .get(*e)
                    .ok_or("cycle names an edge not in the graph")?;
                assert!(edge.weight < 0);
                Ok(())
            }
            DiffResult::Sat { .. } | DiffResult::Refused => Err("expected unsat".into()),
        }
    }

    #[test]
    fn incremental_flip_to_unsat() {
        let mut g = DiffGraph::<i64>::new(2);
        g.add_constraint(0, 1, -1); // x - y <= -1
        assert!(matches!(g.check(), DiffResult::Sat { .. }));
        g.add_constraint(1, 0, 0); // y - x <= 0  ⇒ cycle -1 unsat
        assert!(matches!(g.check(), DiffResult::Unsat { .. }));
    }

    #[test]
    fn vertex_count_at_the_limit_is_refused_before_allocating() {
        // A constraint on the largest index below the limit makes the vertex
        // count exactly `VAR_LIMIT`; the check refuses instead of allocating
        // two `2^28`-entry tables.
        let mut g = DiffGraph::<i64>::new(0);
        g.add_constraint(VAR_LIMIT - 1, 0, 1);
        assert_eq!(g.num_vars(), VAR_LIMIT);
        assert!(matches!(g.check(), DiffResult::Refused));
        // The same holds for a graph created at the limit with no edges.
        assert!(matches!(
            DiffGraph::<i64>::new(VAR_LIMIT).check(),
            DiffResult::Refused
        ));
    }

    #[test]
    fn largest_vertex_index_saturates_and_is_refused() {
        // `usize::MAX + 1` overflowed the vertex count; it now saturates and
        // the graph is refused, never decided without vertex `usize::MAX`.
        let mut g = DiffGraph::<i64>::new(1);
        g.add_constraint(usize::MAX, 0, -1);
        assert_eq!(g.num_vars(), usize::MAX);
        assert!(matches!(g.check(), DiffResult::Refused));
    }
}
