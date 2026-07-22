# ay-allsat

Solution enumeration (ALL-SAT) for Boolean formulas, built on the ay SAT
core. ALL-SAT finds *every* satisfying assignment of a formula, not just one.
This is useful for model counting (when the count is small), configuration
enumeration, and counterexample exploration.

## Algorithm

Iterative SAT solving with blocking clauses:

1. Solve the formula.
2. If SAT, record the model.
3. Add a blocking clause that excludes this model (or its projected cube).
4. Repeat until UNSAT.

Two backends are supported:

- **Internal** (`AllSatSolver::new()`): accumulate clauses; build a fresh
  SAT solver per iteration. Simple and correct.
- **External** (`AllSatSolver::from_solver(...)`): wrap an existing
  `ay_sat::Solver`; add blocking clauses incrementally, preserving learned
  clauses between iterations for better performance on large formulas.

See `src/lib.rs` for more detail on projected enumeration and performance
characteristics.

## CLI usage (`ay allsat`)

`ay-allsat` is exposed via the `ay` CLI as the `allsat` subcommand (#8777).
It accepts DIMACS CNF input and emits each satisfying assignment as an
SMT-LIB-compatible `(model ...)` block.

```text
$ cat /tmp/example.cnf
c (x1 OR x2) AND (NOT x1 OR NOT x2)
p cnf 2 2
1 2 0
-1 -2 0

$ ay allsat /tmp/example.cnf
(model
  (define-fun x1 () Bool true)
  (define-fun x2 () Bool false)
)

(model
  (define-fun x1 () Bool false)
  (define-fun x2 () Bool true)
)

; 2 model(s) enumerated (exhaustive)
```

### Options

| Flag | Description |
|------|-------------|
| `--max-models N` | Enumerate at most `N` models (0 = unlimited). When hit, final comment is `capped` instead of `exhaustive`. |
| `--projected-vars V1,V2,...` | Project onto the comma-separated 1-indexed variables. Blocking clauses reference only these variables, so duplicate projected cubes are never returned. |

### Output format

- Each model prints as a stand-alone `(model ...)` block with one
  `(define-fun xN () Bool true|false)` per reported variable.
- Models are separated by a blank line.
- A trailing `; N model(s) enumerated (exhaustive|capped)` comment reports
  the total count and whether the enumeration was truncated.

When `--projected-vars` is set, only the projected variables are printed
in each model (the solver only distinguishes models by these variables, so
printing non-projected ones would be misleading).

### Exit codes

`ay allsat` exits `0` on successful enumeration (including when truncated
by `--max-models`), and `1` on IO or parse errors.

## Library usage

```rust
use ay_allsat::{AllSatSolver, AllSatConfig};

let mut solver = AllSatSolver::new();
solver.add_clause(vec![1, 2]);
solver.add_clause(vec![-1, -2]);

let solutions: Vec<_> = solver.iter().collect();
assert_eq!(solutions.len(), 2);
```

For projected enumeration:

```rust
use ay_allsat::{AllSatSolver, AllSatConfig};

let mut solver = AllSatSolver::new();
solver.add_clause(vec![1]);
solver.add_clause(vec![2, 3]);

let config = AllSatConfig {
    projection: Some(vec![1]),
    ..Default::default()
};
let solutions = solver.enumerate_with_config(config);
assert_eq!(solutions.len(), 1); // only x1=true
```

## References

- McMillan, "Applying SAT Methods in Unbounded Symbolic Model Checking"
- Grumberg et al., "Memory Efficient All-Solutions SAT Solver"
