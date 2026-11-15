# Limitations

What AY does not do, or does not do yet. If you are about to rely on AY for
something that matters, read this first.

## Answers that come back `unknown`

AY returns `unknown` rather than guess. The common reasons:

- **Nonlinear arithmetic.** NRA and NIA work by incremental linearization
  (sign and tangent lemmas) plus interval constraint propagation. That decides
  many practical problems and is incomplete in general. CAD projection is
  implemented but is not wired into the search, so there is no complete
  fallback.
- **Strings.** The string solver latches to `unknown` as soon as it applies a
  reduction it cannot fully justify, rather than risk a wrong `sat`.
- **Quantifiers.** E-matching, CEGQI and MBQI are heuristics. Undecidable
  fragments stay undecidable; a missing trigger means `unknown`.
- **Resource limits.** `-t`/`--timeout` (milliseconds), z3-style `-T:`
  (seconds), and `--memory` produce `unknown` with exit code 124.

## Certificate coverage is uneven

| Problem | On `unsat` / optimal | Checkable by |
| --- | --- | --- |
| CNF (SAT) | DRAT, LRAT, DPR/SR, VeriPB, or Lean4 | `ay check drat`/`lrat`/`dpr`/`sr`, drat-trim, cake_lpr, VeriPB |
| SMT-LIB | Alethe | carcara; AY's own strict checker re-checks it during the solve, but no `ay check` subcommand reads Alethe — and see below |
| Pseudo-Boolean | VeriPB | VeriPB |
| MaxSAT | OPB + VeriPB bounds | VeriPB |
| MILP | exact rational Farkas / optimality | AY only — no external format exists |
| CHC | quotient certificate | compiled out of public builds |
| Model counting, QBF, AllSAT | nothing | — |

`sat` answers are not certified. They are *validated*: AY re-evaluates the
model against the original constraints. That catches a wrong `sat`, but it is
a check, not a proof.

**Alethe proofs are not yet hole-free.** AY emits some theory steps as opaque
`trust` steps that carcara cannot expand. The in-repo corpus gate explicitly
permits those holes. Hole-free checking is demonstrated only on a small set of
hand-written formulas.

**The two spellings of strict proofs do not yet admit the same UNSATs.**
`--strict-proofs` (`--rigor strict`) refuses an UNSAT whose rendered Alethe
document has a `hole` or `trust` step. `(set-option :check-proofs-strict true)`
does that too, and in the library it also withholds any UNSAT whose proof a
conservative known-wire-gap screen flags; that screen reports every
multi-literal bit-blast lemma as a gap, even one that renders as a complete,
hole-free blast. So some problems answer `unsat` under the flag and `unknown
(incomplete proof-trusted)` under the in-script option: for example
`benchmarks/smt/QF_ABV/wide_mul_unsat.smt2` (and the same problem over a 4- or
16-bit index), whose hole-free refutation is a two-literal bit-blast lemma.
The screen does follow `--alethe-dialect` for a datatype selector over a
constructor (below): `(assert (not (= (fst (mk a b)) a)))` answers `unsat`
under both spellings in the default (Clean) dialect, whose document prints
`dt_project`, and `unknown` under both in the pinned dialect, whose document
prints a `hole`. The screen cannot see one case the printer declines: a
selector or constructor name that a binder anchor elsewhere in the proof
binds. There it would admit a document that prints the hole.

**Strict proofs publish one default certificate per run.** Under strict
proofs, in either spelling, an SMT-LIB `unsat` is published only once its
certificate is, and the default certificate is the one file `<input>.alethe`,
which AY never replaces. So a second strict `unsat` in the same run, or a rerun
beside an earlier run's `<input>.alethe`, answers `unknown` with
`(:reason-unknown (incomplete proof-publication-failed))`. A certificate the
strict check refuses after writing it is invalidated in place, as an empty
file, and blocks later strict runs the same way; delete it first. The
in-script option behaves exactly as the flag here only since
`fix/strict-option-single-answer`. Before it, a script that set the option
without `--strict-proofs` answered `unsat` to both of two `unsat` queries,
certifying only the second, and when a certificate could not be published it
answered `unsat` and then, at the end of the run, `unknown` to the same
`check-sat`. The option applies to the queries after it: one set after a
`check-sat` does not judge that query's certificate. The first strict query
keeps the file through a `(reset)` too: a later query the reset left
non-strict answers `unsat` with no certificate, and `<input>.alethe` then
certifies a problem the end of the script no longer contains. Without strict
proofs the file certifies the last `unsat`, as before. When a later query
finds the file, the warning says it was already written by this run for an
earlier query.

**Under strict proofs, an `unsat` after an error is `unknown`.** AY publishes
no certificate for a problem in which a command printed an `(error ...)`,
because the certificate would embed source that failed. Every such error the
SMT-LIB solver route prints is recorded and makes the run exit 1, as z3's
does; `echo` text is not an error.
That covers a duplicate declaration, an unknown option, and a `(get-model)`,
`(get-value ...)`, `(get-assignment)` or `(eval ...)` with no model, or a
`(get-proof)` or `(get-unsat-core)` with no `unsat` to read. It lasts until
`(reset)`. So under strict proofs, in either spelling, every `unsat` after
such an error in the same problem answers `unknown` with `(:reason-unknown
(incomplete proof-publication-failed))`. The script goes on, and the run
exits 1 because it printed an error. The incremental habit of `(get-model)`
after every `check-sat` triggers this: the `(get-model)` after the first
`unsat` fails, and every later strict `unsat` until `(reset)` is `unknown`.
Without strict proofs that `unsat` stands, with no certificate. The promise
that each `check-sat` gets one response and the script goes on is the default
certificate's: an explicit `--proof FILE` (or `--proof-artifact`,
`--emit-firewall-lean`) instead fails the run with exit 1 at that `unsat`,
with no response to it or to the rest of the script, as it does for any
required certificate it cannot publish; the error names the request, its
target and the cause. Before `fix/strict-option-single-answer`, the flag
exited 1 at such an `unsat` with no response to it or to the rest of the
script, and the option answered `unsat` with no certificate. `(get-assignment)`
and `(eval ...)` with no model, and `(get-proof)` or `(get-unsat-core)` after
`sat`, printed an unpositioned error and exited 0, and a later strict `unsat`
was published with its certificate.

**Without a default certificate, the strict spellings still differ.** On
`--stdin`, `--incremental`, `--no-proof`, `--z3-mode` and `--competition`, no
default certificate is written. There `--strict-proofs` answers a complete
refutation `unsat`, with no certificate, while
`(set-option :check-proofs-strict true)` answers it `unknown`
(`proof-unavailable`), because no derivation is retained. This predates
`fix/strict-option-single-answer`, which leaves it unchanged.

**The solver's own strict screens read only the in-script option.** Some
strict checks run inside the solver, not where the answer is published:
a screen that withholds an `unsat` whose Alethe rendering has a known wire
gap, and strict certification of the sub-queries a quantifier lane solves.
They read `(set-option :check-proofs-strict true)` and not `--strict-proofs`.
So on the file route the two spellings can still differ. Measured on the
2016 non-CHC inputs of the differential gate at `-T:5`, identically on main
db768acbd and on `fix/strict-option-single-answer`: on two files the flag
answers `unsat` and writes `<input>.alethe` while the option answers `unknown`
(`proof-trusted`), the solver saying the rendering "has a known wire gap no
external checker accepts"; on two quantified files the flag answers `sat` and
the option `unknown` (`quantifier-unhandled`, `quantifier-ematching-exists`).

**Some Alethe proofs need carcara's default `define-fun` handling.** A proof
that reads a nullary `define-fun` through its definition assumes the premise
`(= a body)`. Carcara holds that premise only when run without
`--apply-function-defs`; with that flag it rejects such a proof at the `assume`.
In that default reading a parameterized `define-fun` is the premise
`(= f (lambda ..))`, and carcara 1.1.0 has no beta-reduction rule. So a step
that needs `(f a)` unfolded to the body is published as a disclosed `hole`.

**Three Alethe spellings and one rule are checked by Clean's Carcara, not the
pinned one.** Pinned Carcara (1.1.0, git 9a352ee, `reference/tools.toml`) and
Clean's vendored Carcara, which external-codegen promotes on, disagree on three
spellings and on the datatype rule `dt_project`, and by default AY prints
Clean's. A certificate that keeps any of them says
`carcara_surface=clean-dialect` on its `c ay.proof.certificate` line, with a
`c warning:` naming the spelling, and the library's
`UnsatProofArtifact::carcara_surface` is `CarcaraSurface::CleanDialect`
(`Solver::set_alethe_dialect` selects the dialect there). It stays
`trust_free=yes`: AY's own strict checker checks the step, and
`--strict-proofs` still publishes it. It is not a document the pinned checker
accepts. Only `carcara_surface=supported` claims that.

- The `bitblast_ashr` overshift layer. Pinned Carcara builds
  `(ite y_ult_size bit false)`; Clean builds `(ite y_ult_size bit sign)`, as
  SMT-LIB `bvashr` requires. When the sign bit is not literally `false`, no
  spelling satisfies both. AY prints the step only where the amount cannot
  reach the width or the sign bit is literally `false`. There the two circuits
  are the same function, so both spellings are true. `--alethe-dialect
  pinned-carcara` (`Executor::set_alethe_dialect`) prints the pinned zero fill,
  which pinned Carcara accepts. Pinned Carcara's zero fill is wrong for a
  negative operand shifted by at least the width, and it would accept that
  false conclusion. AY's guard is what keeps it out.
- `zero_extend`. AY relies on Clean's consumer rule
  `dialect:expand_zero_extend` (`CleanOnlySpelling::consumer_rule` says where
  Clean states it): Clean reads `((_ zero_extend k) x)` as its SMT-LIB
  definition. Clean reads it so from `ba5e28ff5` on; an older `clean`, such
  as aterm's 0.9.0, refuses these certificates. AY relies on the rule only
  through one shape, in every lane
  that prints the operator (the packed lane for sources wider than 8 bits,
  the packed-circuit lane and the complete bit-blast lane): a `refl` step
  `(= ((_ zero_extend k) x) (concat Z x))`, `Z` the all-zero word of width
  `k`, after which standard rules check the bits.
  `CleanOnlySpelling::consumer_rule` names the key. Pinned Carcara keeps the
  indexed operator and has no rule that relates a symbolic word to its bits
  (`refl`, `cong`, `evaluate` and every `bitblast_*` rule refuse;
  `rare_rewrite` needs a RARE file the gate does not pass). It checks the word only through
  `evaluate` on closed cases, one per assignment of its symbolic bits (such a
  case relies on no rule: pinned Carcara computes the operator on a value);
  every other rule reads the operator as uninterpreted. The packed lane, which
  proves one bit-vector identity, prints those cases for a word with at most
  eight symbolic bits: in both dialects for a source of at most 8 bits, and
  under `--alethe-dialect pinned-carcara` for a wider source too (a closed
  word, `(concat (_ bv0 8) b)`), which pinned Carcara then accepts. The
  packed-circuit and complete bit-blast lanes print no cases, even within
  that bound: two such identities under one conjunction, a byte read back
  from an array, or two 8-bit words in the complete bit-blast lane stay
  `concat`. Past the bound (z3_7526's two fully symbolic 16-bit words would
  need 65,536 cases each) and in those two lanes, both dialects print
  `concat` and disclose `clean-dialect`. The pinned cases cost up to 256
  closed `evaluate` leaves per `zero_extend`: `((_ zero_extend 16) (concat
  #x00 b))` grows its identity's document from about 150 KB to 1.2 MB. About
  fifty of them in one identity exhaust the packed lane's text bound; an
  explicit `--proof` then falls back to the complete bit-blast lane (still
  `clean-dialect`), and the synthesized default certificate (no `--proof`)
  is refused for its work budget, where the Clean dialect publishes one.
- The `dt_project` rule, a datatype selector over a constructor:
  `(= (fst (mk a b)) a)` for `(declare-datatypes ((Pair 0)) (((mk (fst Int)
  (snd Int)))))`. This one is a RULE, not a spelling, and the difference is
  larger. Pinned Carcara has no datatype rule at all: it answers `unknown
  rule`, and an unknown rule makes the whole document `invalid`, not one step
  `holey`. AY's strict checker has always validated the step
  (`TheoryLemmaKind::DatatypeSelectorProject`), and until Clean added the
  rule (4dc90e8ea) every dialect printed it as a `hole`. The default dialect
  now prints `dt_project` for QF_DT, followed by a `symm` step when the
  problem writes the value first (`(= a (fst (mk a b)))`). It does so only
  for a non-parametric datatype (Clean refuses parametric ones), and only
  where the printed step is exactly the projection: a plain selector and
  constructor name that the problem can have declared (an AY-internal
  `__ay_overload_N` name, for a selector two datatypes share, keeps the
  hole), the constructor's full arity, and the projected argument spelled
  exactly as the right side. Everything else keeps the `hole` in both
  dialects. `--alethe-dialect pinned-carcara` keeps the `hole`
  (`unproved_steps=1`, so `--strict-proofs` answers `unknown`); there is no
  pinned spelling to print instead. `--proof-self-check` reads each document
  in its own dialect's rule vocabulary (`ay_core::CLEAN_DIALECT_ALETHE_RULES`
  in the Clean one). In the library, `check_alethe_document`,
  `AletheDocumentChecker::new` and `AletheSelfCheckWriter::new` read the
  default (Clean) vocabulary, so they accept `dt_project`; a caller that
  screens a document for pinned Carcara asks in that dialect
  (`check_alethe_document_in_dialect`, or `with_dialect` on either type). `dt_project` is reached through a single-assertion
  projection such as `(assert (not (= (fst (mk a b)) a)))`, the datatype
  solver's lemmas, and the native API (Trust's `AYProgram`). Measured on
  2026-10-02 (Clean 4dc90e8ea, pinned Carcara 9a352ee): on the `fst`, `snd`,
  value-first and two-constructor forms of that assertion the default
  dialect says `unproved_steps=0 trust_free=yes carcara_surface=clean-dialect`,
  `clean cert verify-external` says `PASSED`, and pinned Carcara refuses the
  document at `dt_project`; the pinned dialect's document is `holey`. A QF_DT
  stack-tower query went from 516 holes to 4 (tester lemmas, which still have
  no rule), and both checkers then stop at an `eq_congruent_pred` step that
  the baseline document already carried. These still answer `unknown` in
  both dialects (`self-check-rejected`): a compound argument
  (`(fst (mk (+ a 1) b))`), an `ite` argument, an argument that is itself a
  constructor application (`(car (cons (leaf x) l))`), a projection under
  `>` or `let`, and two projections under one `or`. The projection split
  over two assertions (`(= x (mk a b))`, `(not (= (fst x) a))`) answers
  `unsat` with no certificate, and an explicit `--proof FILE` fails the run
  (`refusing to write unverifiable proof ... and_pos source no longer prints
  as an and-term`). A problem that Clean's parser refuses is refused whole,
  whatever its steps: the SMT-LIB 2.5 form `(declare-datatypes () ((Pair (mk
  ..))))`, a selector named `cl` or `assume`, or two datatypes that share a
  selector name. Its document can print `dt_project`, and it is disclosed
  `carcara_surface=unsupported`, as its `hole` document was. And
  where a problem has a second refutation that needs no datatype rule, the
  default dialect can now publish the `dt_project` one: on a projection
  beside `(assert (bvult x x))` it does, and Clean passes it where pinned
  Carcara refuses it, while the baseline published the bit-vector refutation
  both accept. The pinned dialect still publishes that one.
- The `bitblast_udiv` / `bitblast_urem` divider. AY prints Clean's fixed long
  division (e9b297e37), which compares against the carry out of the top bit
  and keeps the difference `r - y`. Pinned Carcara compares against the carry
  into the top bit and fills the remainder with ones, so it refuses every
  such step unless the dividend is literally zero (then both build the same
  terms). Its own divider is false for most operands: `(bvudiv #x80 #x02)`
  comes out `#x00`, and every non-zero divisor divides some dividend wrongly.
  It would accept those false conclusions. `--alethe-dialect pinned-carcara`
  prints it only where it is true: a divisor whose bits are all closed and
  `false`, or closed operands whose quotient or remainder it computes
  correctly (AY evaluates the printed circuit). Everywhere else both dialects
  print Clean's divider and disclose `clean-dialect`.

Measured on 2026-09-30 over external-codegen's 128-query consumer corpus, under
external-codegen's own argv:

- 14 certificates keep the `zero_extend` spelling. Pinned Carcara refuses
  each one at `refl` or `cong`. Before this change they all said
  `supported`. 13 are in the `and_simplify`, `or_simplify` and
  `whole-query-hole` classes; the 14th is `bitblast_ashr` fixture
  `d27d9c2d0fd9`.
- 16 of the other 17 `bitblast_ashr` certificates were measured. Each keeps
  the sign fill, and pinned Carcara refuses it at `bitblast_ashr`.
  `0ab585e2a382` did not answer within the sweep's 35 s on this build.
- Every certificate disclosed `supported` (97 measured) is a literal `valid`
  for pinned Carcara.
- In the pinned dialect, the 16 `bitblast_ashr` fixtures measured are
  `supported` and `valid`. `d27d9c2d0fd9` still says `clean-dialect`: it
  keeps its `zero_extend` step. `9574a9e8114b` was not measured.
- The reviser's probes p13, a05, z01 and z02 say `clean-dialect` in both
  dialects. p13 and a05 also carry a `bitblast_ashr` step, spelled in the
  pinned dialect as pinned Carcara requires.

**A `let` the problem writes is eliminated with `:rule let`, which pinned
Carcara checks in one invocation only.** AY's canonical invocation is
`carcara check -- PROOF PROBLEM`: there the `assume` must be the problem's own
`(let ...)`, and the certified bridge eliminates it with `:rule let`. Under
`--expand-let-bindings` Carcara expands that `let` at parse time and refuses
the step (`term ... is of the wrong form, expected '(let ...)'`); the one
alternative bridge, `refl`, is refused without the flag. No document is valid
in both. Such a certificate says `carcara_surface=without-let-expansion`
(`CarcaraSurface::WithoutLetExpansion` on a library `UnsatProofArtifact`), with
a `c warning:` naming the invocation, and `--strict-proofs` still publishes it.
Conversely an `assume` that matches a `let` premise only after expansion is
accepted only under the flag; AY discloses it as `foreign_assumes=yes`.

**Carcara misreads some problems with `:named` labels.** It expands a label
wherever the name occurs, even under a binder of the same name, and it lets a
binder capture a free symbol of a labelled term. Its verdict on such a
problem is not evidence. The corpus gate refuses to count it as verified.

**The DRAT/LRAT checkers are not cross-validated in-repo.** They are real,
independently written checkers, but the tests that would compare them against
drat-trim read fixtures from a `reference/drat-trim/` checkout that this repo
does not ship, and they skip silently when it is absent.

## Native maps (`map.*`)

A `(Map K V)` is a pair of arrays, its values and its domain. `map.insert`
stores into both, `map.remove` clears the key in the domain and leaves the
value, `map.get` reads the value whether or not the key is present, and two
maps are equal when both arrays are. This is not an extensional finite map:
two maps with the same entries can differ in the values outside their domains.

- **Known wrong `unsat`.** AY carries a map as its value array and gives maps
  with equal value arrays one domain. Over a finite key sort two value arrays
  can agree at every key, so a problem that needs two such maps with different
  domains answers `unsat`: `(distinct a b c d e)` over `(Map Bool Bool)` (4
  value arrays, 16 maps), or two `(Map Bool Int)` maps with equal `map.get`
  at both keys and different `map.contains_key`. The sort is erased to
  `Array` during elaboration, so map `=` cannot yet be told from array `=`.
- **Ill-sorted input is accepted.** The same erasure lets array operators and
  array terms meet maps: `(= n (store m 1 5))`, or `(= n a)` with `a` an
  `(Array Int Int)`, elaborates instead of failing to sort-check, and the
  answer means nothing. Measured: `(= n (store m 1 5))
  (map.contains_key m 1) (not (map.contains_key n 1))` answers `sat`.
- **`unknown` by design.** AY withholds `sat` where its encoding is weaker
  than these semantics: the empty map, `map.insert` or `map.remove` used as a
  value instead of read; a domain read of a map that is not a declared
  constant (a quantified or `define-fun` parameter, an `ite`, a `select` from
  an array of maps, a function result); `map.subset` of two different maps; a
  quantifier over maps that compares maps; a constant array written at a map
  sort, `((as const (Map K V)) v)`, which is not the empty map and has no
  domain of its own (its values are still all `v`). The higher-order operators
  (`map.values`, `map.fold`, ...) always answer `unknown`.
- **`unknown` on easy `sat`.** Measured: `(distinct (map.get m 1) (map.get m
  2))`, and `(map.contains_key m 1) (not (map.contains_key n 1))`, whose model
  gives `m` and `n` one value array and so one domain.

## Engines that are weaker than they look

- **`ay lp`** is a dense tableau simplex with depth-first branch-and-bound
  capped at 4096 nodes. It is sized for small test fixtures and says so in its
  own source. The serious branch-and-cut MILP engine (`ay-milp`) has **no `ay`
  subcommand**; it is reached from an SMT fast path, from inside `ay maxsat`
  and `ay pb`, and through the separate `ay-milp` binary.
- **`ay simplify`** implements four rewriting tactics. Z3's
  `ctx-solver-simplify` and quantifier elimination are not implemented.
- **`ay qbf`** is a thin wrapper over a small QDIMACS solver.
- **Compressed CNF** (`.cnf.xz`, `.cnf.gz`, `.cnf.bz2`) is not handled on the
  solve path; decompress first.

## Z3 compatibility is partial

AY accepts Z3's command-line spellings and a useful subset of its SMT-LIB
extensions, and can be symlinked as `z3`. It is not a drop-in replacement:
the C API surface is incomplete, many Z3 parameters are accepted and ignored,
and the full SMT-LIB competition corpus has not been run against it. From an AY
source checkout, use the replacement qualification runner,
`ay-z3-parity qualify`, before substituting AY for Z3. It provisions authenticated
references and runs the registered acceptance suite; incomplete coverage and
failed semantics remain explicit. `ay z3-audit` provides the older diagnostic
view and is not complete replacement acceptance.

Known Z3-surface divergences (measured 2026-10-16):

- **`(get-proof)` returns an Alethe document**, not a z3 proof term. A script
  that walks z3 proof terms cannot consume it.
- **Optimization priorities**: grouped `(assert-soft ... :id ...)` and
  soft constraints mixed with `(maximize)`/`(minimize)` arithmetic
  objectives optimize lexicographically in declaration order, under
  `:opt.priority box` (independent per-objective optima, first declared
  objective's witness), and under `:opt.priority pareto` (stateful
  front enumeration over the unified objective vector with certified
  exhaustion), as in z3, on all three surfaces (SMT-LIB, native API,
  C API). Pareto requires Int/BitVec objectives (Real falls back to
  lex with a warning), and a single unified objective degenerates to
  plain optimization, matching z3.
- **Rigor-dependent routing.** Proof-gated preprocessing differs across
  `--rigor` postures, so capability (decide vs `unknown`) can still differ
  by posture on some inputs; the direction is fail-closed (no wrong
  verdict observed).
- **muZ fixedpoint commands** (`declare-rel`/`rule`/`query`) are refused
  on the SMT stdin path; Horn problems go through the CHC engine's own
  entry points.
- **Unknown long options** (`--zzz`) in a z3 invocation still get clap's
  diagnostic (exit 2); unknown single-dash options match z3 exactly
  (exit 109).

## Build

The `ay` binary requires `--features cli`. Without it `targo --unverified build -p ay` (or `cargo build -p ay`)
produces a library and no executable, and does not explain why.
