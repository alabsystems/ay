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
            self.n_vars = v + 1;
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
        }
    }

    /// Bellman-Ford from the implicit zero-distance super-source.
    fn bellman_ford(&self) -> BfOutcome<W> {
        let n = self.n_vars;
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
                let cand = dist[e.from].add(&e.weight);
                if cand < dist[e.to] {
                    dist[e.to] = cand;
                    pred[e.to] = Some(ei);
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
            Some(start) => {
                let cycle = self.recover_cycle(start, &pred);
                BfOutcome::NegativeCycle { cycle }
            }
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
    fn recover_cycle(&self, start: usize, pred: &[Option<usize>]) -> Vec<usize> {
        // Step back n times to guarantee we are on the cycle.
        let mut v = start;
        for _ in 0..self.n_vars {
            v = match pred[v] {
                Some(ei) => self.edges[ei].from,
                None => break,
            };
        }
        // Now v is on the cycle. Collect edges from v back to v.
        let cycle_node = v;
        let mut edges_rev: Vec<usize> = Vec::new();
        let mut cur = cycle_node;
        loop {
            let ei = pred[cur].expect("cycle node must have predecessor");
            edges_rev.push(ei);
            cur = self.edges[ei].from;
            if cur == cycle_node {
                break;
            }
            // Safety valve: never loop longer than the edge count.
            if edges_rev.len() > self.edges.len() {
                break;
            }
        }
        edges_rev.reverse();
        edges_rev
    }

    /// `debug_assert` that the model satisfies every stored constraint by direct
    /// substitution: for edge `from → to : w`, check `model[to] - model[from] <= w`,
    /// i.e. `model[to] <= model[from] + w`.
    fn certify_model(&self, model: &[W]) {
        for e in &self.edges {
            let rhs = model[e.from].add(&e.weight);
            debug_assert!(
                model[e.to] <= rhs,
                "diff-logic SAT self-cert failed: constraint v{} - v{} <= {:?} violated by model \
                 (lhs v{}={:?}, v{}={:?})",
                e.to,
                e.from,
                e.weight,
                e.to,
                model[e.to],
                e.from,
                model[e.from],
            );
        }
    }

    /// `debug_assert` that the recovered cycle is a real cycle whose summed edge
    /// weight is `< 0`.
    fn certify_cycle(&self, cycle: &[usize]) {
        debug_assert!(!cycle.is_empty(), "diff-logic UNSAT cert: empty cycle");
        // Check it forms a closed walk: each edge's `to` == next edge's `from`.
        for w in cycle.windows(2) {
            let a = &self.edges[w[0]];
            let b = &self.edges[w[1]];
            debug_assert_eq!(
                a.to, b.from,
                "diff-logic UNSAT cert: cycle not contiguous at edges {w:?}"
            );
        }
        let first = &self.edges[cycle[0]];
        let last = &self.edges[*cycle.last().unwrap()];
        debug_assert_eq!(
            last.to, first.from,
            "diff-logic UNSAT cert: cycle does not close"
        );
        // Sum weights and assert < 0.
        let mut sum = W::zero();
        for &ei in cycle {
            sum = sum.add(&self.edges[ei].weight);
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
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_is_sat() {
        let g = DiffGraph::<i64>::new(3);
        assert!(matches!(g.check(), DiffResult::Sat { .. }));
    }

    #[test]
    fn simple_sat_chain() {
        // x - y <= 5, y - z <= 3  ⇒ sat
        let mut g = DiffGraph::<i64>::new(3);
        g.add_constraint(0, 1, 5); // x - y <= 5
        g.add_constraint(1, 2, 3); // y - z <= 3
        match g.check() {
            DiffResult::Sat { model } => {
                assert!(model[0] - model[1] <= 5);
                assert!(model[1] - model[2] <= 3);
            }
            DiffResult::Unsat { .. } => panic!("expected sat"),
        }
    }

    #[test]
    fn two_cycle_unsat() {
        // x - y <= -1 and y - x <= -1  ⇒ sum cycle weight -2 < 0  ⇒ unsat
        let mut g = DiffGraph::<i64>::new(2);
        g.add_constraint(0, 1, -1);
        g.add_constraint(1, 0, -1);
        match g.check() {
            DiffResult::Unsat { cycle } => {
                let sum: i64 = cycle.iter().map(|&e| g.edges()[e].weight).sum();
                assert!(sum < 0);
                assert_eq!(cycle.len(), 2);
            }
            DiffResult::Sat { .. } => panic!("expected unsat"),
        }
    }

    #[test]
    fn equal_cycle_is_sat() {
        // x - y <= 1 and y - x <= -1  ⇒ x - y = 1, feasible (cycle weight 0)
        let mut g = DiffGraph::<i64>::new(2);
        g.add_constraint(0, 1, 1);
        g.add_constraint(1, 0, -1);
        match g.check() {
            DiffResult::Sat { model } => assert_eq!(model[0] - model[1], 1),
            DiffResult::Unsat { .. } => panic!("expected sat (zero-weight cycle)"),
        }
    }

    #[test]
    fn three_cycle_unsat() {
        // x-y<=1, y-z<=1, z-x<=-3  ⇒ cycle 1+1-3=-1 <0 unsat
        let mut g = DiffGraph::<i64>::new(3);
        g.add_constraint(0, 1, 1);
        g.add_constraint(1, 2, 1);
        g.add_constraint(2, 0, -3);
        match g.check() {
            DiffResult::Unsat { cycle } => {
                let sum: i64 = cycle.iter().map(|&e| g.edges()[e].weight).sum();
                assert!(sum < 0);
            }
            DiffResult::Sat { .. } => panic!("expected unsat"),
        }
    }

    #[test]
    fn negative_self_loop_unsat() {
        // x - x <= -1  ⇒ 0 <= -1  ⇒ unsat (1-edge negative cycle)
        let mut g = DiffGraph::<i64>::new(1);
        g.add_constraint(0, 0, -1);
        match g.check() {
            DiffResult::Unsat { cycle } => {
                assert_eq!(cycle.len(), 1);
                assert!(g.edges()[cycle[0]].weight < 0);
            }
            DiffResult::Sat { .. } => panic!("expected unsat"),
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
}
