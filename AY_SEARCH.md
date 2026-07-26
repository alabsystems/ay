# AY Search

AY Search is AY's high-level finite-domain modeling library for programs that
would otherwise contain custom backtracking, branch-and-bound, or combinatorial
search. The application declares choices, rules, and an optional objective; AY
supplies propagation, search, model enumeration, and optimization.

The same model shape is available as:

- the typed Rust crate `ay-search`;
- the Python package `aysearch`;
- the typed Node entry point `ayz3/search`; and
- the versioned JSON `SearchSpec` v1 contract over AY's C ABI.

Start with the live course and game:

```bash
ay tutorial engineers
ay tutorial play sudoku
ay tutorial features integration
```

The complete runnable examples are
[`crates/ay-search/tests/worked_examples.rs`](crates/ay-search/tests/worked_examples.rs),
[`bindings/python/examples/search_sudoku.py`](bindings/python/examples/search_sudoku.py),
[`bindings/python/examples/search_token_router.py`](bindings/python/examples/search_token_router.py),
[`bindings/python/examples/search_minesweeper.py`](bindings/python/examples/search_minesweeper.py),
and their TypeScript/JavaScript counterparts under
[`bindings/js/examples`](bindings/js/examples).

## When a solver is the simpler algorithm

Search code usually mixes two concerns: what makes an answer valid, and how to
find one. As requirements accumulate, a direct implementation grows pruning,
backtracking, cache invalidation, special cases, and a second algorithm for
optimization. AY Search keeps the application focused on the first concern:

| Application concern                              | AY Search model                   |
| ------------------------------------------------ | --------------------------------- |
| Pick one route, worker, feature, or move         | finite-domain or Boolean variable |
| Enforce capacities and balances                  | linear equation or inequality     |
| Use each value once                              | `all_different`                   |
| Allow only known combinations                    | table constraint                  |
| Select an indexed value                          | element constraint                |
| Find the cheapest/fastest/highest-quality answer | linear objective                  |
| Find alternatives or prove uniqueness            | complete/capped enumeration       |

This pattern fits puzzles, schedulers, token routers, configuration systems,
test generation, resource allocation, package selection, planning, and many
game mechanics. It is particularly valuable when constraints change often or
interact globally. It is not automatically faster than every specialized
algorithm; measure the exact model and preserve `unknown`.

## Architecture

The language bindings are deliberately small. They construct a portable model;
the solver and expression parser remain in Rust.

```text
Python Model / TypeScript Model / SearchSpec JSON
                       |
                       v
               SearchSpec v1 validation
          names, finite domains, safe expressions
                       |
                       v
                 ay-search lowering
                       |
                       v
               AY finite-domain CP-SAT
                       |
                       v
              assignment re-validation
                       |
                       v
 sat / unsat / unknown / optimal / feasible / enumeration

Rust Model --------------------------------------^
                       |
                       +-----> exact QF_LIA SMT-LIB rendering
```

Python uses `ctypes` and Node uses `koffi` to call the two one-shot C functions
`ay_search_solve_json` and `ay_search_compile_json`. Their returned strings are
owned by AY and the bindings free them with `ay_string_free`. Equation strings
are parsed as data by AY's restricted grammar; neither binding calls `eval`.

## Install from this checkout

Build the CLI to use the tutorial:

```bash
cargo build --release --locked -p ay --features cli --bin ay
./target/release/ay tutorial
```

For Rust, add the workspace crate by path while developing in this repository:

```toml
[dependencies]
ay-search = { path = "../ay/crates/ay-search" }
```

For an external project, use a pinned repository revision rather than an
unbounded branch:

```toml
[dependencies]
ay-search = { git = "https://github.com/alabsystems/ay.git", rev = "<PIN>" }
```

The Python source package builds and bundles `libay_ffi`:

```bash
python3 -m pip install ./bindings/python
python3 bindings/python/examples/search_sudoku.py
```

The Node binding currently uses the native shared library:

```bash
cargo build -p ay-ffi --release
cd bindings/js
npm install
node examples/search-sudoku.mjs
```

In a package consumer, import the typed entry point as `ayz3/search`. In the
source-checkout examples the same module is imported relatively from
`../search.mjs`. [`search.d.ts`](bindings/js/search.d.ts) is shipped as the
declaration surface. Set `AYSEARCH_LIB` (or `AYZ3_LIB`) to the full
shared-library path if automatic discovery does not fit the deployment layout.
Both search loaders check `AYSEARCH_LIB` first and then `AYZ3_LIB`.

## Quick starts

### Python

```python
from aysearch import Model

m = Model("assignment")
worker = m.choice("worker", ["cpu", "gpu"])
cost = m.int("cost", 0, 20)
m.table([worker, cost], [["cpu", 7], ["gpu", 3]])
m.minimize(cost)

result = m.solve(timeout_ms=2_000)
if result.status != "optimal":
    raise RuntimeError(f"need a proved optimum, got {result.status}")
solution = result.require_solution()
print(solution[worker], result.objective)  # gpu 3
```

`Solution` is immutable and can be indexed by a variable or its name. Choice
variables decode to labels, Boolean variables decode to `bool`, and
`solution.raw_values` keeps the integer representation.

### TypeScript

```typescript
import { Model } from "ayz3/search";

const m = new Model("assignment");
const worker = m.choice("worker", ["cpu", "gpu"]);
const cost = m.int("cost", 0, 20);
m.table(
  [worker, cost],
  [
    ["cpu", 7],
    ["gpu", 3],
  ],
);
m.minimize(cost);

const result = m.solve({ timeoutMs: 2_000 });
if (result.status !== "optimal")
  throw new Error(`need a proved optimum, got ${result.status}`);
const solution = result.requireSolution();
console.log(solution.get(worker), result.objective); // gpu 3
```

`Solution.values` contains decoded values and `Solution.rawValues` contains the
integer representation. Node solving is synchronous and one-shot today.

### Rust

```rust
use ay_search::{Domain, Model, OptimizationResult};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut model = Model::new();
    let worker = model.int_var("worker", Domain::interval(0, 1)?)?;
    let cost = model.int_var("cost", Domain::interval(0, 20)?)?;
    model.set_choice_label(worker, 0, "cpu")?;
    model.set_choice_label(worker, 1, "gpu")?;
    model.table(&[worker, cost], &[vec![0, 7], vec![1, 3]])?;

    match model.minimize(cost)? {
        OptimizationResult::Optimal { solution, value } => {
            println!("{} {value}", solution.choice_label(worker)?.unwrap_or("?"));
        }
        other => println!("no proved optimum: {other:?}"),
    }
    Ok(())
}
```

Rust variable handles are scoped to their `Model`; passing a handle from a
different model is a typed error. `BoolVar` converts to the exact integer domain
`{0, 1}`, and arithmetic over handles builds normalized `LinearExpr` values.

## Modeling vocabulary

### Variables and domains

Every decision has a finite signed-integer domain. Rust supports inclusive
intervals and explicit value sets:

```rust
let day = model.int_var("day", Domain::interval(0, 6)?)?;
let port = model.int_var("port", Domain::values([80, 443, 8443])?)?;
let enabled = model.bool_var("enabled")?;
```

Python and TypeScript provide interval integers, Booleans, labeled choices,
and integer-grid conveniences:

```python
day = model.int("day", 0, 6)
enabled = model.bool("enabled")
backend = model.choice("backend", ["local", "gpu", "api"])
cell = model.int_grid("cell", 4, 4, 1, 4)
```

```typescript
const day = model.int("day", 0, 6);
const enabled = model.bool("enabled");
const backend = model.choice("backend", ["local", "gpu", "api"]);
const cell = model.intGrid("cell", 4, 4, 1, 4);
```

Names must match `[A-Za-z_][A-Za-z0-9_]*` and must be unique within a model.
Labeled choices are integers in the portable model and are decoded back to
their labels by the binding that created them.

### Linear equations

Python/TypeScript `add()` and SearchSpec expression constraints accept one
relation over affine integer expressions:

```text
2 * gpu_tokens + cached_tokens <= 32000
route_local + route_gpu + route_api == 1
finish - start >= duration
selected != 0
```

The complete grammar is intentionally small:

| Construct      | Accepted form                         |
| -------------- | ------------------------------------- |
| identifier     | a declared variable name              |
| integer        | signed through unary `+` or `-`       |
| grouping       | `(expression)`                        |
| arithmetic     | `+`, `-`, unary `+`/`-`, and `*`      |
| multiplication | at least one operand must be constant |
| relation       | exactly one of `==`, `!=`, `<=`, `>=` |

Strict `<`/`>`, division, modulo, Boolean connectives, function calls, array
access, variable-by-variable multiplication, and SMT-LIB syntax are rejected.
Use `x <= y - 1` for a strict integer inequality.

Rust constructs the same constraints without strings:

```rust
model.eq(route_local + route_gpu + route_api, 1)?;
model.le(2 * gpu_tokens + cached_tokens, 32_000)?;
model.ne(selected, 0)?;
```

### Global constraints

`all_different`/`allDifferent` requires pairwise-distinct values:

```python
model.all_different(cell[0])
```

A table allows only listed tuples. It is often clearer and less error-prone
than encoding an application catalog with many implications:

```python
model.table(
    [route, cost, latency],
    [
        ["local", 0, 180],
        ["fast_cloud", 20, 45],
        ["cheap_cloud", 7, 120],
    ],
)
```

An element constraint means `result = array[index]`, where `index` is
zero-based and every array entry is another model variable:

```python
model.element(index, [first, second, third], selected)
```

```typescript
model.element(index, [first, second, third], selected);
```

Rust exposes the same primitive as `model.element(index, &array, result)` and
SearchSpec uses the object form documented below.

### Objectives

A model has at most one linear objective in AY Search:

```python
model.minimize("5 * cloud_calls + latency")
# or
model.maximize("10 * quality - cost")
```

The Rust equivalents are `model.minimize(expr)` and `model.maximize(expr)`.
Optimization tightens a strict bound around validated incumbents until no
better solution exists, the theoretical finite-domain bound is reached, or the
solver returns `unknown`.

## SearchSpec v1

SearchSpec is the portable, strict JSON contract used by both language
bindings. This complete router model chooses the cheapest route satisfying a
latency requirement:

```json
{
  "version": 1,
  "name": "single-request-router",
  "variables": [
    {
      "name": "route",
      "domain": { "values": [0, 1, 2] },
      "labels": {
        "0": "local",
        "1": "fast_cloud",
        "2": "cheap_cloud"
      }
    },
    { "name": "cost", "domain": { "min": 0, "max": 20 } },
    { "name": "latency", "domain": { "min": 45, "max": 180 } }
  ],
  "constraints": [
    {
      "table": {
        "variables": ["route", "cost", "latency"],
        "tuples": [
          [0, 0, 180],
          [1, 20, 45],
          [2, 7, 120]
        ]
      }
    },
    { "expression": "latency <= 100" }
  ],
  "objective": {
    "sense": "minimize",
    "expression": "cost"
  },
  "limits": { "timeout_ms": 2000 }
}
```

The result is an `optimal` assignment with route `1`, cost `20`, and latency
`45`; the JSON result also carries the label `fast_cloud`.

### Top-level fields

| Field                  | Required | Meaning                                                    |
| ---------------------- | -------- | ---------------------------------------------------------- |
| `version`              | yes      | Must be the integer `1`                                    |
| `name`                 | no       | Diagnostic name                                            |
| `variables`            | yes      | Ordered declarations with unique names and finite domains  |
| `constraints`          | no       | Expression or global-constraint objects; defaults to empty |
| `objective`            | no       | `minimize` or `maximize` plus one linear expression        |
| `limits.timeout_ms`    | no       | Positive wall-clock search budget                          |
| `limits.max_solutions` | no       | Positive enumeration cap, at most 10,000                   |

Unknown JSON fields are rejected at every structured layer. A domain is exactly
one of `{"min": i64, "max": i64}` (inclusive) or
`{"values": [i64, ...]}` (nonempty; sorted/deduplicated during construction).
Label keys are domain integers encoded as JSON object keys.

### Constraint objects

Each constraint is exactly one of:

```json
{ "expression": "2*x + y <= 10" }
```

```json
{ "all_different": ["x", "y", "z"] }
```

```json
{
  "table": {
    "variables": ["route", "cost"],
    "tuples": [
      [0, 7],
      [1, 3]
    ]
  }
}
```

```json
{
  "element": {
    "index": "selected_index",
    "array": ["first", "second", "third"],
    "result": "selected_value"
  }
}
```

Table rows must have the same arity as `variables`, and every table value must
belong to the corresponding variable domain. A table must contain at least one
allowed tuple. All references must name declared variables. An element index's
entire domain must fit the zero-based range of its array.

### Fixed construction caps

After JSON parsing, SearchSpec lowering is guard-bounded: AY rejects models that
exceed fixed construction limits rather than allowing an input to request
unbounded dense encodings, quadratic explanation work, or retained result
vectors. `SearchSpec::from_json` itself must allocate the document, so Rust
callers should still cap bytes before parsing. The C ABI applies a separate
fixed whole-document limit before it invokes the JSON parser.

| Resource                                                        |   SearchSpec v1 limit |
| --------------------------------------------------------------- | --------------------: |
| variables                                                       |               100,000 |
| non-trivial constraints                                         |               100,000 |
| dense span of one domain, including holes in an explicit domain |                65,536 |
| aggregate internal domain-encoding slots                        |             1,000,000 |
| scalar cells across one table                                   |             1,000,000 |
| absolute domain bound, coefficient, constant, or constraint RHS | 2,305,843,009,213,951 |
| conservative aggregate backend-work units                       |             1,000,000 |
| UTF-8 bytes in one equation                                     |                65,536 |
| tokens in one equation                                          |                 4,096 |
| parenthesis nesting in one equation                             |                   128 |
| retained enumeration solutions                                  |                10,000 |
| retained `solutions * variables` assignment cells               |             1,000,000 |
| conservative serialized enumeration result                      |      16,777,216 bytes |
| SearchSpec SMT-LIB rendering                                     |      16,777,216 bytes |
| whole SearchSpec document at the C ABI                          |      16,777,216 bytes |

The backend-work estimate charges hidden lowering and explanation shapes,
including linear arity, table propagation, element arrays, pairwise
all-different expansion, and repeated constraints. The numeric envelope leaves
headroom for AY CP's signed bound negation, strict-bound increments, and slack
arithmetic. These are hard safety ceilings, not recommended service quotas.
Applications accepting untrusted models should impose substantially smaller
limits suited to their latency and memory envelope.

### Running or inspecting a SearchSpec from Rust

```rust
use ay_search::SearchSpec;

fn run(input: &str) -> Result<(), Box<dyn std::error::Error>> {
    let spec = SearchSpec::from_json(input)?;
    let smt2 = spec.to_smt2()?;       // validates and renders; does not solve
    let problem = spec.build()?;      // validated executable model
    let result = problem.run()?;      // mode selected by objective/limits
    println!("{result:#?}\n{smt2}");
    Ok(())
}
```

`SearchProblem::run()` optimizes when an objective is present, enumerates when
`max_solutions` is present, and otherwise performs one satisfaction solve.
An objective and `max_solutions` are mutually exclusive. The Python and
TypeScript `enumerate()` methods reject a model that already has an objective
instead of silently changing the requested operation.

## Worked example: Sudoku

Sudoku replaces a recursive puzzle-specific search with five rule families:

1. each cell is an integer from 1 through 4;
2. every row is all-different;
3. every column is all-different;
4. every 2x2 box is all-different; and
5. clues are equalities.

```python
from aysearch import Model

model = Model("4x4 Sudoku")
cell = model.int_grid("cell", 4, 4, 1, 4)

for row in cell:
    model.all_different(row)
for column in range(4):
    model.all_different(cell[row][column] for row in range(4))
for box_row in (0, 2):
    for box_column in (0, 2):
        model.all_different(
            cell[row][column]
            for row in range(box_row, box_row + 2)
            for column in range(box_column, box_column + 2)
        )

for row, column, value in (
    (0, 0, 1), (0, 3, 4),
    (1, 1, 4), (2, 2, 4),
    (3, 0, 4), (3, 3, 1),
):
    model.add(f"{cell[row][column]} == {value}")

result = model.solve(timeout_ms=2_000)
solution = result.require_solution()
for row in cell:
    print(" ".join(str(solution[value]) for value in row))
```

The same model can validate player moves by adding their equalities, enumerate
completions, or establish uniqueness when enumeration returns `complete` with
one solution. To prove a hint forced, solve once, then solve the same rules plus
`cell != candidate`; `unsat` proves the candidate is forced. The live
`ay tutorial play sudoku` game performs this style of real solver query and
independently validates the returned board.

The 4x4 model keeps the worked output bounded and readable. AY's separate
Z3-shaped CDCL(LIA) path has a known weak spot on general 9x9
integer/`Distinct` encodings and may return `unknown`. For a larger AY Search
deployment, benchmark the exact puzzle class and budget before shipping it.

## Worked example: LLM token router

A greedy router can make a locally cheap decision that consumes scarce
capacity and makes the whole batch expensive. A solver instead chooses all
routes together. This TypeScript example models each provider's cost and
latency as catalog data, adds service-level requirements, and proves the
minimum weighted token cost when it returns `optimal`:

```typescript
import { ChoiceVar, IntVar, Model } from "ayz3/search";

const model = new Model("LLM token router");
const requests = ["chat", "code", "batch"];
const tokenUnits = [1, 2, 5]; // rounded 1k-token billing units
const routes: ChoiceVar[] = [];
const costs: IntVar[] = [];
const localLoads: IntVar[] = [];

for (const [i, request] of requests.entries()) {
  const route = model.choice(`${request}_route`, [
    "local",
    "fast_cloud",
    "cheap_cloud",
  ]);
  const cost = model.int(`${request}_cost`, 0, 20);
  const latency = model.int(`${request}_latency`, 45, 180);
  const localLoad = model.int(`${request}_local_load`, 0, tokenUnits[i]);
  model.table(
    [route, cost, latency, localLoad],
    [
      ["local", 0, 180, tokenUnits[i]],
      ["fast_cloud", 20, 45, 0],
      ["cheap_cloud", 7, 120, 0],
    ],
  );
  routes.push(route);
  costs.push(cost);
  localLoads.push(localLoad);
}

model.add("chat_latency <= 100");
model.add("code_latency <= 200");
model.add("batch_latency <= 200");
model.add("chat_local_load + code_local_load + batch_local_load <= 5");
model.minimize(
  costs.map((cost, i) => `${tokenUnits[i]} * ${cost}`).join(" + "),
);

const result = model.solve({ timeoutMs: 2_000 });
if (result.status !== "optimal")
  throw new Error(`router has no proved optimum: ${result.status}`);
const solution = result.requireSolution();
requests.forEach((request, i) =>
  console.log(`${request}: ${solution.get(routes[i])}`),
);
```

The local row consumes each request's token units while both cloud rows consume
zero local load. Code needs 2 units and batch needs 5, so both are individually
eligible for the 5-unit local pool but cannot take it together. AY chooses the
globally cheaper winner instead of relying on request order.

Real routers can add Boolean capability decisions, context-window bounds,
provider quotas, tenant isolation, residency policies, concurrency capacity,
fallback requirements, and cost/quality objectives. Keep provider data in
tables and policy in named equations so changing a catalog does not require a
new search algorithm.

## Worked example: Minesweeper

For Minesweeper, every covered cell is a Boolean variable: `1` means mine and
`0` means safe. Every revealed clue is exactly the sum of its covered
neighbors. Two adjacent clues can settle several cells without any game-specific
branching code:

```python
from aysearch import Model

model = Model("Minesweeper inference")
left = model.bool("left")
center = model.bool("center")
right = model.bool("right")

model.add("left + center == 1")
model.add("center + right == 2")

result = model.enumerate(10)
if result.status != "complete":
    raise RuntimeError("cannot make a proof-strength move from partial enumeration")

for cell in (left, center, right):
    possible = {solution[cell] for solution in result.solutions}
    if possible == {False}:
        print(cell.name, "is safe")
    elif possible == {True}:
        print(cell.name, "is a forced mine")
    else:
        print(cell.name, "is undecided")
```

The unique consistent neighborhood has `left = 0`, `center = 1`, and
`right = 1`. On a full board, generate one equation per revealed square:

```python
neighbors = [
    mine[r][c].name
    for r in range(max(0, row - 1), min(height, row + 2))
    for c in range(max(0, column - 1), min(width, column + 2))
    if (r, c) != (row, column)
]
model.add(" + ".join(neighbors) + f" == {clue}")
```

Complete enumeration classifies cells across every possible board. For a
larger frontier, a cheaper proof query is to assert the opposite of a proposed
cell value in a fresh model: `unsat` proves the move forced, `sat` supplies a
counterexample board, and `unknown` means the program must not click. See the
complete 5x5 example linked at the top of this guide. That example's ordinary
`solve()` prints one possible board; it does not label cells safe or forced.
Only an UNSAT counterfactual or complete enumeration supports those claims.

## Let an LLM propose equations safely

AY Search includes `equation_prompt` in Python and `equationPrompt` in
TypeScript. The recommended architecture keeps variable creation and domains
in trusted application code and asks the model for equations over that fixed
allowlist.

```python
from aysearch import Model, equation_prompt

model = Model("request policy")
chat_latency = model.int("chat_latency", 0, 500)
code_latency = model.int("code_latency", 0, 500)
total_cost = model.int("total_cost", 0, 10_000)

prompt = equation_prompt(
    [chat_latency, code_latency, total_cost],
    "Chat must finish within 100 ms, code within 200 ms, and total cost "
    "must not exceed 3000 micro-dollars.",
)
print(prompt)
```

The generated prompt instructs the LLM to return only this shape:

```json
{
  "equations": [
    "chat_latency <= 100",
    "code_latency <= 200",
    "total_cost <= 3000"
  ]
}
```

Pre-populate that object as the expected response in a structured-output call.
Before adding it to the model, enforce the envelope yourself:

```python
import json

payload = json.loads(llm_text)
if set(payload) != {"equations"} or not isinstance(payload["equations"], list):
    raise ValueError("unexpected LLM response shape")
if len(payload["equations"]) > 20:
    raise ValueError("too many equations")
for equation in payload["equations"]:
    if not isinstance(equation, str) or len(equation) > 500:
        raise ValueError("invalid equation")
    model.add(equation)

# Forces native schema/name/grammar validation without executing the solve.
reviewable_smt2 = model.to_smt2()
result = model.solve(timeout_ms=2_000)
```

The native parser rejects undeclared variables, unsupported characters,
multiple relations, nonlinear multiplication, calls, and attempted SMT-LIB or
host-language injection. That is a syntax and model-integrity boundary, not a
complete resource sandbox. Still cap input bytes, variable/constraint counts,
domain widths, coefficients, table rows, and solve time. Put untrusted solves
in a process-level memory/CPU sandbox when adversarial resource use matters.

If an LLM must produce a complete SearchSpec instead, use `version: 1`, reject
oversized input before parsing, call `SearchSpec::from_json(...).build()` (or
the binding's native compile route), inspect `to_smt2()`, and validate the
returned assignment against the original application requirement. Never trust
an LLM's claimed status, optimum, or solution.

## Result semantics

AY Search never collapses an incomplete search into `unsat` and never labels an
incumbent `optimal` merely because time expired.

| Operation    | Rust result                             | JSON/Python/TypeScript status | Meaning                                                                                                |
| ------------ | --------------------------------------- | ----------------------------- | ------------------------------------------------------------------------------------------------------ |
| one solve    | `SolveResult::Sat`                      | `sat`                         | A post-validated satisfying assignment exists                                                          |
| one solve    | `SolveResult::Unsat`                    | `unsat`                       | Search proved there is no satisfying assignment                                                        |
| one solve    | `SolveResult::Unknown`                  | `unknown`                     | Neither SAT nor UNSAT was justified within the method/budget                                           |
| optimization | `OptimizationResult::Optimal`           | `optimal`                     | A validated incumbent exists and no strict improvement remains, or the exact finite bound was attained |
| optimization | `OptimizationResult::FeasibleOnUnknown` | `feasible`                    | A validated incumbent exists, but optimality was not proved before `unknown`                           |
| optimization | `OptimizationResult::Unsat`             | `unsat`                       | The base constraints have no solution                                                                  |
| optimization | `OptimizationResult::Unknown`           | `unknown`                     | No incumbent was found before search became incomplete                                                 |
| enumeration  | `EnumerationResult::Complete`           | `complete`                    | Blocking every emitted assignment eventually produced UNSAT                                            |
| enumeration  | `EnumerationResult::Capped`             | `capped`                      | The requested cap was reached; do not infer whether another solution exists                            |
| enumeration  | `EnumerationResult::Unknown`            | `unknown`                     | The emitted prefix is validated, but enumeration is incomplete                                         |

Python's `result.is_sat` and TypeScript's `result.isSat` mean “a usable
solution is present,” including a feasible optimization incumbent or the first
enumerated solution. They do not mean the optimum is proved. Use `status`,
`optimal`, and `complete` for the property the application actually requires.
`require_solution()`/`requireSolution()` throws when no assignment is present.

Python and TypeScript expose:

- `result.solution`: one decoded assignment when present;
- `result.solutions`: the enumeration prefix;
- `result.objective`: the incumbent objective value;
- `result.optimal`: true/false for optimization outcomes;
- `result.complete`: true/false for completed/capped enumeration;
- `result.reason`: an optional unknown reason; and
- `result.raw`: the unmodified native response envelope.

Host-side construction errors fail early. A malformed model discovered by the
one-shot native solve is returned as status `error` by the bindings; it is not
`unsat`. Rust returns a typed `SearchError`.

### Enumeration examples

Python and TypeScript enumeration is capped by default at 100 solutions:

```python
result = model.enumerate(1_000, timeout_ms=5_000)
for solution in result.solutions:
    consume(solution)
if result.status != "complete":
    print("prefix only; uniqueness/counting has not been proved")
```

```typescript
const result = model.enumerate(1_000, { timeoutMs: 5_000 });
for (const solution of result.solutions) consume(solution);
if (!result.complete) console.log("prefix only");
```

Rust additionally has `enumerate_all()`, `enumerate_up_to(limit)`, and
`enumerate(limit, SolveOptions)`.

## Inspect and interoperate with SMT-LIB

`Model.to_smt2()` in Python, `Model.toSMT2()` in TypeScript, and
`Model::to_smt2()`/`SearchSpec::to_smt2()` in Rust render a deterministic,
standalone QF_LIA model. Intervals become bound assertions, explicit domains
become disjunctions, and global constraints receive exact logical lowerings.
Every model variable is emitted as a quoted SMT identifier such as
`|cell_0_0|`. Rendering validates the model but does not execute it.

Useful reasons to render are:

- code review and logging of the exact solved model;
- reproducing a disputed case in a second SMT-LIB solver;
- preserving generated LLM equations as inspectable constraints; and
- migrating a prototype from AY Search to theory-rich native SMT.

For a SearchSpec objective, the rendering includes the corresponding
`(minimize ...)` or `(maximize ...)` command. The rendering is an
interoperability artifact, not by itself a certificate that AY's result is
correct or optimal.

## Trust and production guidance

AY Search validates every returned assignment against the original model's
domains and constraints before publishing it. Enumeration validates every
member of the prefix. Optimization evaluates the objective again and only uses
`optimal` after strict bound tightening terminates in UNSAT or an exact finite
bound is attained.

Those checks are valuable fault containment, but they live in the same Rust
implementation and are not an independent proof checker. AY Search does not
currently emit a standalone CP optimality certificate. If a result crosses a
high-assurance boundary:

1. preserve the SearchSpec or rendered SMT-LIB and binary provenance;
2. independently evaluate every returned assignment in application code;
3. preserve `unknown`, `feasible`, and `capped` exactly;
4. replay the rendered problem with a separately implemented solver when that
   adds useful assurance; and
5. for an optimum, independently establish that no better bound is satisfiable
   rather than checking only the incumbent.

Operationally:

- set a positive timeout for service requests;
- bound request/model size before construction;
- record the timeout and input hash with the result;
- run hostile inputs behind process-level memory and CPU limits;
- avoid logging sensitive model data or provider-policy details blindly;
- pin AY and the binding version together; and
- test the exact fragments and scale used by the application.

The high-level timeout is a wall-clock search deadline, not a memory limit.
Repository benchmark harnesses have stricter OOM-planning rules; follow
`scripts/_oom_guard.py` when spawning parallel solver processes.

## Current boundaries

AY Search v1 is intentionally focused:

- finite signed-integer and Boolean domains;
- affine integer equations and inequalities;
- `all_different`, table, and element globals;
- one linear objective;
- one-shot solve, enumeration, or optimization; and
- exact QF_LIA export.

It does not expose arbitrary SMT theories, nonlinear integer arithmetic,
lexicographic multi-objective optimization, incremental push/pop, soft
constraints, or every global available elsewhere in AY. Use AY's native SMT
API, SMT-LIB frontend, FlatZinc, PB, MaxSAT, or LP/MILP frontend when those are
the better abstraction. `ay tutorial features` maps those larger surfaces, and
`ay tutorial experts` contains worked examples for proofs, incremental solving,
optimization evidence, theories, CHC, and benchmarking.
