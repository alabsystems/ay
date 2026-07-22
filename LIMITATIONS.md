# Scope and limitations

AY is a 0.x solver workspace. Support and evidence are specific to a logic,
entry point, proof format, and checker; the presence of a parser or API does not
by itself mean that the full theory combination is complete or certified.

- `sat`, `unsat`, and optimization answers are certified only when the selected
  mode emits a documented artifact and that artifact passes its named,
  designated checker. The trust boundary differs by path: some checkers are
  external tools, while native APIs also expose solver-state-independent
  in-tree verifiers. Other answers are solver results, not proof claims.
- AY's built-in DIMACS checker fails closed when it rejects a DRAT/LRAT/PR-SR
  proof, but warns and preserves the verdict when checking cannot run. SMT
  `--self-check` is the fail-closed path for AY's internal proof objects: UNSAT
  requires a strict semantic proof check and binds every reachable assumption
  to the active problem. Independent Alethe and VeriPB replay remains a separate
  certification step.
- `unknown` is an expected sound outcome for unsupported or incomplete paths.
  Callers must not reinterpret it as `sat` or `unsat`.
- `verification/lean` is the maintained Lean project named by the public proof
  claims. The public snapshot excludes admitted research modules and private
  proof-factory routing, private deductive-checker harnesses, and orchestration;
  retained proof fixtures and artifacts are not broader verification claims
  unless they identify a completed theorem and a reproducible checker invocation.
- The public workspace omits development-only code-generation integrations and
  unwired prototype crates. Their absence is deliberate; supported fallback
  solver paths remain in the exported crates and are checked under all public
  features.
- The Python incremental `arrays` and `arr_lia` fragments remain experimental
  and often return `unknown`; their bounded differential tests require zero
  verdict disagreements. `Solver` and `Optimize` fail closed with `unknown` on
  quantified-array formulas, and Python `IsSubset` deliberately raises
  `NotImplementedError`, because that FFI path is not soundly supported.
- Historical wrong-answer inputs remain in the SMT regression corpus and must
  be replayed against a reference solver before an affected logic is described
  as release-ready.
- Performance and coverage numbers are meaningful only with the exact commit,
  binary provenance, corpus, timeout, enforced memory envelope, proof mode,
  checker verdicts, and wrong/invalid counts supplied alongside them.
- Benchmark deficits are roadmap inputs, not reasons to narrow the promised
  Z3-compatibility surface or the specialist-performance target.

The release bar is zero known wrong answers and zero invalid certificates on the
advertised surface. No current public aggregate evidence packet demonstrates
that bar across the advertised surface. Treat each claim only at the granularity
of its named test or checker, and treat unlisted theory combinations and bindings
as experimental.

These are present-state limits, not a narrowing of the project goal. AY is being
built to become a universal Z3 replacement and to outperform mature specialist
solvers in their domains; each step toward that goal must earn its claim with
reproducible results and independently checked evidence.

## Known limitations (0.1.0)

- **HORN `(get-model)` under `--z3-mode`** returns a sound `unknown` rather
  than the Spacer-shaped invariant. The CHC verdict (`sat`/`unsat`) is correct;
  only the model rendering from the CHC certificate is not yet wired to
  `(get-model)`, so the theory-search model is rejected by the independent
  soundness gate. Use the emitted CHC certificate (`.chccert`) for the
  invariant. Fix tracked for 0.1.x.
