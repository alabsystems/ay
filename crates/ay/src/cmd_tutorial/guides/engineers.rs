// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use anyhow::Result;

use super::EngineerChapter;

pub(super) fn run(selected: Option<EngineerChapter>, interactive: bool) -> Result<()> {
    println!();
    println!("=== AY for Engineers ===");
    println!("Build applications by declaring valid outcomes; let AY own the search.");
    println!("Select a chapter with `ay tutorial engineers CHAPTER`.");
    println!();

    let chapters: Vec<_> = EngineerChapter::ALL
        .into_iter()
        .filter(|chapter| selected.is_none_or(|wanted| wanted == *chapter))
        .collect();
    for (index, chapter) in chapters.iter().copied().enumerate() {
        println!("--- Chapter: {} ---", chapter.title());
        println!();
        match chapter {
            EngineerChapter::Build => build()?,
            EngineerChapter::Automation => automation(),
            EngineerChapter::Rust => rust(),
            EngineerChapter::Migration => migration(),
            EngineerChapter::Production => production(),
        }
        if interactive && index + 1 < chapters.len() && !super::super::prompt_continue()? {
            println!("Course paused. Resume by selecting any chapter by name.");
            break;
        }
    }
    println!("Next: `ay tutorial play sudoku` or `ay tutorial experts`.");
    println!();
    Ok(())
}

fn build() -> Result<()> {
    println!(
        "{}",
        r#"The shift in architecture

Many programs contain a hand-written search loop:

  choose a candidate -> reject it -> backtrack -> add pruning -> repeat

With a solver, application code describes variables, domains, constraints, and
an optional objective. AY supplies propagation, conflict learning, backtracking,
and evidence machinery. This is particularly effective when requirements
change more often than the search algorithm should.

AY Search uses one finite-domain model shape across Rust (`ay-search`), Python
(`aysearch`), and TypeScript (`ayz3/search`). Equation strings are parsed by a
small linear grammar in Rust; they are never passed to `eval`.

Python shape:

  from aysearch import Model

  model = Model("tiny-schedule")
  alice = model.int("alice", 0, 4)
  bob = model.int("bob", 0, 4)
  model.add("alice + bob == 4")
  model.add("alice >= 1")
  model.add("bob >= 1")
  answer = model.solve()
  print(answer.status)
  if answer.status == "sat":
      solution = answer.require_solution()
      print(solution[alice], solution[bob])

TypeScript shape:

  import { Model } from "ayz3/search";

  const model = new Model("tiny-schedule");
  model.int("alice", 0, 4);
  model.int("bob", 0, 4);
  model.add("alice + bob == 4");
  const answer = model.solve();

Three worked application patterns follow.

1. Sudoku: feasibility, contradiction checks, and hints

  cells = model.int_grid("r", 4, 4, 1, 4)
  for each row:       model.all_different(row)
  for each column:    model.all_different(column)
  for each 2x2 box:   model.all_different(box)
  for each clue v:    model.add(f"{cells[1][2]} == 2")

This replaces a Sudoku-specific recursive backtracker. The same model can check
a player's partial board, find one completion, enumerate alternatives, or test
whether a hint is forced. The teaching model is 4x4 so a live session stays
readable. AY's separate Z3-shaped linear-integer/Distinct path has a known 9x9
weak spot; for any larger Search model, measure the exact puzzle class and
budget you plan to ship.

Live result from the tutorial's 4x4 model:"#,
    );
    super::sudoku::print_live_result()?;
    println!(
        "{}",
        r#"
2. LLM token router: optimize globally instead of nesting if-statements

Choose one route per request and use a table to derive its cost, latency, and
local load. Then declare:

  - every request is assigned exactly once;
  - unsupported capability/context pairs equal zero;
  - shared token and concurrency totals stay within capacity;
  - total cost is a weighted sum of assignments;
  - minimize cost or one explicit weighted cost/latency score.

AY Search v1 has one linear objective. Use AY's native SMT/OMT surface when a
true lexicographic sequence of objectives is part of the contract.

When a new model, quota, or policy appears, update data and constraints rather
than rewriting a greedy router. Global solving can reveal that a locally cheap
choice consumes scarce capacity and increases total fleet cost.

  # table rows: route, price, latency, local token load
  model.table([code_route, code_cost, code_latency, code_local_load], [
      ["local", 0, 180, 2], ["fast_cloud", 20, 45, 0],
      ["cheap_cloud", 7, 120, 0],
  ])
  model.table([batch_route, batch_cost, batch_latency, batch_local_load], [
      ["local", 0, 180, 5], ["fast_cloud", 20, 45, 0],
      ["cheap_cloud", 7, 120, 0],
  ])
  model.add("code_latency <= 200")
  model.add("batch_latency <= 200")
  model.add("chat_local_load + code_local_load + batch_local_load <= 5")
  model.minimize("chat_cost + 2*code_cost + 5*batch_cost")

Code and batch are each eligible for local inference, but need 2 + 5 units
together. The 5-unit shared limit forces AY to decide globally which request
gets the scarce local route. Present the minimum only when status is `optimal`.

3. Minesweeper: infer safe and forced-mine cells

Represent every covered cell as a 0/1 variable (`1` means mine). A revealed
clue is a sum over its covered neighbors:

  model.add("m_1_1 + m_1_2 + m_2_1 == 2")

To prove a cell safe, temporarily assert `m_1_2 == 1`. UNSAT means no board
consistent with the visible clues can contain a mine there. Reverse the test to
prove a forced mine. SAT gives a possible board; UNKNOWN means do not click.

The reusable pattern is the point:

  puzzle/game        -> finite choices + local/global rules
  routing/scheduling -> assignments + capacities + objective
  configuration      -> feature choices + compatibility rules
  test generation    -> symbolic inputs + path/postconditions

These models are often shorter, easier to change, and more exhaustive than a
bespoke classical search. They are not automatically faster on every instance;
measure the model, preserve UNKNOWN, and validate returned solutions.

Run the complete Python programs from a source checkout:

  cargo build -p ay-ffi
  PYTHONPATH=bindings/python python3 bindings/python/examples/search_sudoku.py
  PYTHONPATH=bindings/python python3 bindings/python/examples/search_token_router.py
  PYTHONPATH=bindings/python python3 bindings/python/examples/search_minesweeper.py

The same three programs are included for Node/TypeScript-shaped callers:

  cd bindings/js
  npm install
  node examples/search-sudoku.mjs
  node examples/search-token-router.mjs
  node examples/search-minesweeper.mjs

Safe prompt for an LLM that writes constraints

Copy this prompt and replace only the REQUIREMENTS block:

  You translate a bounded search problem into AY SearchSpec v1 JSON.
  Return exactly one JSON object and no prose or Markdown.
  Use only declared integer variables with finite domains.
  Each equation may use identifiers, integer literals, parentheses, unary +/-
  and linear +, -, *. Multiplication must have a constant operand.
  Relations are ==, !=, <=, >=. Never invent a variable or operator.
  Prefer all_different/table primitives when they express the rule directly.
  Do not include a claimed answer; AY will solve and validate the model.

  REQUIREMENTS:
  Integers x and y are between 0 and 10. They sum to 10. x is at least 3.
  Minimize y.

Expected LLM response (pre-populated):

  {
    "version": 1,
    "name": "two-variable-search",
    "variables": [
      {"name":"x", "domain":{"min":0, "max":10}},
      {"name":"y", "domain":{"min":0, "max":10}}
    ],
    "constraints": [
      {"expression":"x + y == 10"},
      {"expression":"x >= 3"}
    ],
    "objective":{"sense":"minimize", "expression":"y"}
  }

Treat even this constrained output as untrusted input: cap its size, validate
the schema, inspect `model.to_smt2()`, apply timeout/memory limits, and validate
the returned assignment in application code. Never trust an LLM's predicted
status or model.
"#,
    );
    Ok(())
}

fn automation() {
    println!(
        "{}",
        r#"Build and invoke the exact binary you intend to ship:

  cargo build --release --locked -p ay --features cli --bin ay
  ./target/release/ay --features

Batch SMT over stdin (pass argv and stdin directly, without a shell):

  ay --z3-mode --stdin < request.smt2

Long-lived incremental SMT session:

  ay --z3-mode -in

Resource and observability controls:

  ay solve --timeout 5000 --memory 1024 \
    --stats-json --progress-json progress.jsonl problem.smt2

Production result parser contract:

  1. Parse a real status token: sat / unsat / unknown (or format equivalent).
  2. Keep the rest of stdout as the model/proof protocol payload.
  3. Preserve stderr: provenance, warnings, and JSON statistics live there.
  4. Preserve UNKNOWN and its reason; never coerce it to a Boolean.
  5. Record timeout, binary provenance, input hash, and enforced memory budget.

Exit codes are format-specific. DIMACS uses 10 for SAT and 20 for UNSAT;
ordinary SMT-LIB normally exits 0 for all three solver verdicts. A normal AY
timeout prints unknown and exits 124. Do not infer an SMT verdict from the
process exit code alone, and do not treat nonempty stderr as failure.

Machine-readable helpers have intentionally narrow meanings:

  --stats-json              statistics on stderr, not a JSON verdict
  --progress-json FILE      streaming JSONL events
  --explain-format json     a reason-code object, not the entire solve result

When an answer is disputed:

  ay diagnose --reference z3 --json problem.smt2

`diagnose` combines AY/reference verdicts, explanation, statistics, and binary
identity. It is a triage tool, not a substitute for proof replay.
"#,
    );
}

fn rust() {
    println!(
        "{}",
        r#"For native embedding, use AY's public `ay::api` surface and pin a commit.

Cargo.toml:

  [dependencies]
  ay = { git = "https://github.com/alabsystems/ay.git", rev = "<PIN>" }

Minimal typed solve:

  use ay::api::{Logic, SolveResult, Solver, Sort};

  fn main() -> Result<(), Box<dyn std::error::Error>> {
      let mut s = Solver::try_new(Logic::QfLia)?;
      let x = s.declare_const("x", Sort::Int);
      let y = s.declare_const("y", Sort::Int);
      let ten = s.int_const(10);
      let sum = s.try_add(x, y)?;
      let rule = s.try_eq(sum, ten)?;
      s.try_assert_term(rule)?;

      let details = s.try_check_sat_with_details()?;
      match details.accept_for_consumer()? {
          SolveResult::Sat => println!("x={:?}, y={:?}", s.value(x), s.value(y)),
          SolveResult::Unsat(_) => println!("no assignment exists"),
          SolveResult::Unknown => println!("unknown: {:?}", details.unknown_reason),
          _ => println!("unsupported result variant"),
      }
      Ok(())
  }

Use fallible `try_*` construction in production. Detailed checks keep validation
and evidence metadata, and `accept_for_consumer` is the explicit boundary before
a definite result drives behavior. `SolverScope` provides RAII push/pop.
Assumptions, cores, interrupts, resource limits, and typed values are exposed.

Run the complete in-tree example:

  cargo run -p ay-dpll --example native_api

For finite-domain search, `ay-search` layers names, domains, linear expressions,
global constraints, enumeration, and optimization over AY's CP-SAT machinery.
Use native SMT when theory-rich terms matter; use AY Search for choices + rules.
"#,
    );
}

fn migration() {
    println!(
        "{}",
        r#"Migrate a Z3 integration at one observable boundary at a time.

1. Transcript-compatible command line

  z3 -smt2 problem.smt2
  ay --z3-mode problem.smt2

`--z3-mode` shapes stdout/stderr for transcript comparisons and suppresses
default proof sidecars. It is not a proof or self-check mode.

For tools that resolve `z3` from PATH:

  mkdir -p target/ay-z3-shim
  ln -sf "$PWD/target/release/ay" target/ay-z3-shim/z3
  PATH="$PWD/target/ay-z3-shim:$PATH" z3 -smt2 problem.smt2

2. Python source compatibility

  # import z3
  import ayz3 as z3

  x = z3.Int("x")
  s = z3.Solver()
  s.add(x > 2, x < 7)
  print(s.check(), s.model())

Install the current source package with:

  python3 -m pip install ./bindings/python

`ayz3` is a documented z3py-shaped subset, not universal z3py parity.
Unsupported operations fail explicitly or return unknown where appropriate.

3. Measure the exact corpus

  ay diagnose --reference z3 problem.smt2
  ay bench run EVAL --reference-solver "$(command -v z3)"

4. Move stable code to native Rust or AY Search when you want typed construction.

Keep three distinctions visible: parser/API compatibility, verdict/model
agreement on a preserved corpus, and independent certificate acceptance.
Success in one is not proof of the other two.
"#,
    );
}

fn production() {
    println!(
        "{}",
        r#"Production checklist

  [ ] Pin and record the AY commit/build provenance.
  [ ] Run `ay --features`; test the exact fragment and options consumed.
  [ ] Treat sat, unsat, and unknown as separate API outcomes.
  [ ] Apply both a wall-clock timeout and an enforced memory ceiling.
  [ ] Independently validate SAT assignments in application terms.
  [ ] Require an explicit artifact and named checker for high-trust UNSAT/OPT.
  [ ] Preserve input, stdout, stderr, stats, checker verdict, and limits.
  [ ] Differentially test upgrades against a pinned reference and corpus.

Trust choices:

  ay solve problem.smt2
      Requests a best-effort sidecar on supported file paths.

  ay solve --proof out.alethe problem.smt2
      Explicit artifact; emission failure is loud. Replay it independently.

  ay solve --self-check problem.smt2
      Fail closed unless AY's in-tree model/proof checks accept the answer.

  ay solve --strict-proofs problem.smt2
      Screen terminal Trust/Hole fallbacks; this is not external replay.

  ay solve --competition --no-proof problem.smt2
      Raw-throughput posture. Do not describe it as self-checking.

Resource nuance matters. `ay solve` and CHC enforce `--memory`; the main
binary's `pb` subcommand and external solvers do not gain a memory limit because
a report names one. Repository harnesses plan jobs through
`scripts/_oom_guard.py`, wrap children without a solver memory knob, and persist
the actual envelope. The budget applies even at jobs=1.

Finally, keep solver validation separate from domain validation. A Sudoku model
must still be checked as a Sudoku; an LLM route must satisfy real provider
limits; a Minesweeper hint must derive only from visible clues. That independent
checker catches integration and encoding bugs outside the solver.
"#,
    );
}
