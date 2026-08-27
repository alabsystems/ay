Native branch-and-bound: the MILP lane (P2).

Until now a binary model left `ay-milp` through the `smt` lane — a lowering
onto ay-dpll's CDCL(T). That is a general-purpose SMT search being asked to
do a MILP solver's job, and it shows. This is the MILP solver: LP relaxations
from the float simplex, branching on fractional integer columns, and pruning
against an incumbent.

## Every prune is exact, or it does not happen

Pruning is the one place a branch-and-bound can silently lose the optimum, so
nothing here prunes on a float. The bound that closes a subtree comes from
**weak duality applied in exact rationals**:

```text
c·x  =  y·(Ax) + (c − Aᵀy)·x  =  y·s + d·x
     >=  Σ_r min(y_r·lb_r, y_r·ub_r)  +  Σ_j min(d_j·l_j, d_j·u_j)
```

The crucial property is that this holds for **any** `y` whatsoever — dual
feasibility is not required. So the float simplex's duals are rounded to
exact rationals (`f64 -> BigRational` is lossless), `d = c − Aᵀy` is computed
exactly, and the resulting number is a *rigorous* lower bound on everything in
that subtree. A bad `y` yields a weak bound and costs search; it cannot cut
off a solution. This is the Neumaier–Shcherbina safe-bounding idea with the
error analysis replaced by exact arithmetic, and it costs one pass over the
non-zeros rather than a factorization.

Everything else is fail-closed in the same spirit: a float `Infeasible` is a
numerical opinion, so an apparently-infeasible node is re-solved on the exact
rim before it is discarded; and an incumbent is only accepted after its point
is re-checked against the model exactly, integrality included.

## Scope

This lane now combines presolve, root and node cuts, probing, strong
branching, primal heuristics, and exact certificates. It remains a native,
correctness-first solver rather than a claim of performance parity with
mature industrial MILP engines.

Known incompleteness: when the relaxation is unbounded, the MILP is unbounded
only if it is FEASIBLE, and if the integer-feasibility probe cannot settle
that, this returns `Unknown` rather than guessing `Unbounded` the way most
solvers do (Gurobi's INF_OR_UNBD conflates the two).
