# Competitions — per-track support, verified by execution

Every row in this file was produced by running the `ay` binary on a concrete
instance and checking the output against the track's conventions; several rows
were additionally replayed through the official external checker (drat-trim,
Carcara, VeriPB). The `check it yourself` command is the exact command that was
run. Status vocabulary: **ready** (input/output/certificate conventions work
today), **partial** (solves the format; the noted piece is missing), **not
yet** (absent, stated plainly).

Reference solver for comparative rows: **Z3 5.0.0** (the latest release,
2026-07-17, official binaries). Where a row's recorded evidence was executed
against Z3 4.15.4 and not yet re-run on 5.0.0, the row says so — every
comparative claim is being migrated to 5.0.0, and no new comparison uses an
older Z3. Known still-at-4.15.4 surfaces: the `z3-audit` reference transcript
cache and `crates/ay/z3-compatibility.json` parity baselines (re-baseline
tracked for 0.1.x); the `opt_epsilon` baselines are already Z3 5.0.0.

This file records *capability*, not competition results. AY has not yet
entered these competitions; official result packets will be linked from the
README as they exist.


## SAT Competition / CHC-COMP / QBF Gallery

| Competition | Track | Status |
| --- | --- | --- |
| SAT Competition 2026 | Main (regular + AI-tuned/AI-generated disclosure sub-classes) | ready — UNSAT: DRAT/LRAT emitted, drat-trim replays VERIFIED; SAT: model v-lines (2025/26 requires certificates in both cases); exit codes 10/20 |
| SAT Competition 2026 | Parallel (single AWS machine, 64 vcores; model required on SAT) | ready — built-in thread portfolio via --parallel N; proofs and models still emitted and verified |
| SAT Competition 2026 | Cloud (distributed, multi-node) | partial — no distributed/multi-node engine; a 'Cloud Track' packaging lane exists but it runs a single-node 32-thread portfolio |
| SAT Competition 2026 | Experimental (new 2026 sequential track, no proof requirement) | ready — same sequential solve path; dedicated experimental profile lane staged |
| SAT Competition | Hack track (CaDiCaL/kissat hack, held in some earlier years) | n/a — track is about patching the organizers' reference solver, not entering your own; also absent from the 2025/2026 track lists |
| CHC-COMP 2026 | LIA-Lin | ready — sat with printed inductive invariant + .chccert; unsat with counterexample derivation witness |
| CHC-COMP 2026 | LIA-Nonlin | ready — both verdicts verified on nonlinear (two-predicate-body) clauses |
| CHC-COMP 2026 | LIA-Lin-Arrays | ready — sat invariant uses select/store; unsat counterexample on array fact |
| CHC-COMP 2026 | LIA-Nonlin-Arrays | ready — both verdicts verified on nonlinear clauses over (Array Int Int) |
| CHC-COMP 2026 | ADT-LIA | ready — recursive list datatype handled; sat invariant synthesized via size catamorphism; unsat trace produced |
| CHC-COMP 2026 | ADT-LIA-Arrays | ready — both verdicts verified on (Array Int Pair) with a record datatype |
| CHC-COMP 2026 | LRA-Lin | ready — both verdicts verified on linear real-arithmetic Horn (transition-system shape) |
| CHC-COMP 2026 | BV-Lin | ready — both verdicts verified on (_ BitVec 8) linear Horn |
| CHC-COMP 2026 | BV-Nonlin | partial — sat side verified; a tiny reachable-unsat instance returns honest `unknown` ("CHC portfolio exhausted all strategies within budget"), no wrong answers |
| CHC-COMP 2026 | (submission tooling) | ready — dedicated CHC-COMP packaging covering all 2026 track aliases |
| QBF Gallery 2026 (QBFEVAL successor) | PCNF (main track, QDIMACS) | ready — s TRUE/FALSE with QBF Gallery exit codes 10/20 |
| QBF Gallery 2026 | 2QBF (single forall-exists alternation) | ready — 2-level instances solved in both quantifier orders |
| QBF Gallery 2026 | Crafted instances / Random formulas | ready (by format) — these tracks use the same PCNF/QDIMACS input the solver handles; no separate solver capability required |
| QBF Gallery 2026 | Prenex Non-CNF (QCIR) | not yet — QCIR input rejected; parser is QDIMACS-only at HEAD too |
| QBF Gallery 2026 | DQBF (DQDIMACS) | not yet — d-quantifier lines cleanly rejected; no DQBF support anywhere at HEAD |
| QBF Gallery 2026 | (possible certified track) | partial — Skolem/Herbrand certificate machinery exists in the library but the CLI does not emit certificates |

<details><summary>Check it yourself — the exact commands</summary>

**Main (regular + AI-tuned/AI-generated disclosure sub-classes)**
```bash
printf 'p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n' > /tmp/u.cnf && ay solve --proof /tmp/u.drat /tmp/u.cnf; drat-trim /tmp/u.cnf /tmp/u.drat
```
**Parallel (single AWS machine, 64 vcores; model required on SAT)**
```bash
ay solve --parallel 4 /tmp/u.cnf
```
**Experimental (new 2026 sequential track, no proof requirement)**
```bash
ay solve --sat-variant probe /tmp/u.cnf
```
**LIA-Lin**
```bash
printf '(set-logic HORN)\n(declare-fun inv (Int) Bool)\n(assert (forall ((x Int)) (=> (= x 0) (inv x))))\n(assert (forall ((x Int)) (=> (and (inv x) (< x 10)) (inv (+ x 1)))))\n(assert (forall ((x Int)) (=> (and (inv x) (> x 100)) false)))\n(check-sat)\n' > /tmp/h.smt2 && ay solve /tmp/h.smt2
```
**(submission tooling)**
```bash
ay submission generate chc --help
```
**PCNF (main track, QDIMACS)**
```bash
printf 'p cnf 2 2\na 1 0\ne 2 0\n1 2 0\n-1 -2 0\n' > /tmp/t.qdimacs && ay qbf solve /tmp/t.qdimacs; echo $?
```
</details>

## SMT-COMP (division by division)

| Competition | Track | Status |
| --- | --- | --- |
| SMT-COMP 2026 | Single Query — QF_LinearIntArith (QF_IDL, QF_LIA, QF_LIRA) | ready — QF_LIA/QF_LIRA in accepted-logic list, QF_IDL parses+solves too; division is in ay's planned 2026 SQ entry (QF_LIA, QF_IDL) |
| SMT-COMP 2026 | Single Query — QF_LinearRealArith (QF_LRA, QF_RDL) | ready — QF_LRA in accepted list, QF_RDL solves despite being unlisted; both in planned 2026 SQ entry |
| SMT-COMP 2026 | Single Query — QF_Bitvec (QF_BV) | ready — QF_BV accepted, correct, and in planned 2026 SQ entry |
| SMT-COMP 2026 | Single Query — QF_Equality (QF_AX, QF_UF) | ready — both logics accepted, in planned entry; ay's strongest division (QF_UF 1606/1778 ≈90% at 10 s, 0 soundness conflicts) |
| SMT-COMP 2026 | Single Query — QF_Datatypes (QF_DT, QF_UFDT) | ready — QF_DT accepted+entered; QF_UFDT absent from accepted list but parses and solves correctly |
| SMT-COMP 2026 | Single Query — QF_Equality+Bitvec (QF_ABV, QF_AUFBV, QF_UFBV, QF_UFBVDT) | ready — 3/4 logics accepted (QF_UFBVDT unlisted) and all three entered in 2026 SQ |
| SMT-COMP 2026 | Single Query — QF_Equality+LinearArith (QF_ALIA, QF_AUFLIA, QF_UFDTLIA, QF_UFDTLIRA, QF_UFIDL, QF_UFLIA, QF_UFLRA) | partial — QF_AUFLIA entered and correct; QF_UFLIA WITHDRAWN 2026-06-15 for a confirmed false-SAT (EUF+LIA ite-chain); 3/7 division logics in accepted list |
| SMT-COMP 2026 | Single Query — QF_Equality+NonLinearArith (QF_ANIA, QF_AUFNIA, QF_UFDTNIA, QF_UFNIA, QF_UFNRA) | partial — 2/5 division logics accepted (QF_UFNIA, QF_UFNRA), tiny instance correct; division not in planned 2026 entry |
| SMT-COMP 2026 | Single Query — QF_FPArith (QF_ABVFP, QF_ABVFPLRA, QF_AUFBVFP, QF_BVFP, QF_BVFPLRA, QF_FP, QF_FPLRA, QF_UFFP, QF_UFFPDTNIRA) | partial — 2/9 division logics accepted (QF_FP, QF_BVFP), both correct on tiny instances; array/UF/LRA FP combos unlisted; not in planned entry |
| SMT-COMP 2026 | Single Query — QF_NonLinearIntArith (QF_NIA, QF_NIRA) | partial — both logics accepted and tiny instance correct, but division not in planned 2026 entry |
| SMT-COMP 2026 | Single Query — QF_NonLinearRealArith (QF_NRA) | partial — logic accepted, tiny instance correct; not in planned 2026 entry |
| SMT-COMP 2026 | Single Query — QF_Strings (QF_S, QF_SLIA, QF_SNIA) | partial — all 3 division logics accepted, sat and unsat both correct on tiny instances; not in planned 2026 entry, and strings Alethe proofs contain a trust placeholder |
| SMT-COMP 2026 | Single Query — Equality (UF, UFDT) [quantified] | partial — both logics accepted and tiny quantified instance correct; ay's planned 2026 entry is QF-only, no quantified divisions entered |
| SMT-COMP 2026 | Single Query — Equality+LinearArith (ALIA, AUFDTLIA, AUFDTLIRA, AUFLIA, AUFLIRA, UFDTLIA, UFDTLIRA, UFIDL, UFLIA, UFLRA) | partial — 8/10 division logics accepted (ALIA, UFIDL missing); tiny UFLIA correct but its Alethe proof has 1 trust step; not entered |
| SMT-COMP 2026 | Single Query — Equality+MachineArith (ABV, ABVFP, ABVFPLRA, AUFBV, AUFBVDT*, AUFBVFP*, UFBV, UFBVDT*, UFBVFP*, UFBVLIA, UFFPDTNIRA — 19 logics) | not yet — 0/19 division logics in accepted list; a tiny UFBV instance still solved correctly, so parsing works but the family is unadvertised and not entered |
| SMT-COMP 2026 | Single Query — Equality+NonLinearArith (ANIA, AUFDTNIRA, AUFNIA, AUFNIRA, UFDTNIA, UFDTNIRA, UFNIA, UFNIRA) | partial — 4/8 division logics accepted (UFDTNIA, UFDTNIRA, UFNIA, UFNIRA); tiny quantified UFNIA correct; not entered |
| SMT-COMP 2026 | Single Query — Arith (LIA, LRA, NIA, NRA) [quantified] | partial — all 4 division logics accepted; tiny quantified LIA correct; quantified divisions not in planned 2026 entry |
| SMT-COMP 2026 | Single Query — Bitvec (BV) [quantified] | not yet — BV absent from accepted-logic list; a tiny quantified-BV instance solved correctly but with a trust step in its proof; not entered |
| SMT-COMP 2026 | Single Query — FPArith (BVFP, BVFPLRA, FP, FPLRA) [quantified] | not yet — 0/4 division logics in accepted list; tiny quantified FP instance solved correctly but the family is unadvertised; not entered |
| SMT-COMP 2026 | Incremental track (17 divisions) | partial — push/pop and --incremental stdin both give the exact correct sat/unsat sequence; planned 2026 entry deliberately limited to QF_UF+QF_LRA after a soundness audit; the Incremental-only division QF_Equality+Bitvec+Arith (QF_UFBVLIA/QF_BVLRA/QF_AUFBV*) returns only unknown |
| SMT-COMP 2026 | Unsat Core track (19 divisions) | partial — (get-unsat-core) with named assertions returns exact minimal cores in every division family tested (QF_UF, QF_LIA, QF_BV); however the generated 2026 submission declares no UnsatCore participation |
| SMT-COMP 2026 | Model Validation track (13 divisions) | partial — (get-model) emits well-formed (model (define-fun ...)) with correct values across QF_LIA, QF_BV, QF_DT, QF_FP (covers QF_LinearIntArith, QF_Bitvec, QF_Datatypes, QF_FPArith families incl. the MV-only QF_ADT divisions' logics QF_ABV/QF_AUFBV); planned 2026 MV entry is QF_UF+QF_LRA only |
| SMT-COMP 2026 | Proof Exhibition track (19 divisions) | partial — Alethe emission works in every division family tested: 17/17 unsat instances produced proofs via --proof FILE.alethe, and a .alethe sidecar is written by default on UNSAT; QF-division proofs are fully rule-checkable (0 trust steps in 13/17), while strings/quantified-BV/UFLIA/BV proofs contain a ':rule trust' placeholder; no ProofExhibition participation in the generated submission |
| SMT-COMP 2026 | Parallel track (19 divisions) | not yet — no SMT parallel portfolio; --parallel N is documented and implemented for DIMACS SAT only (SMT input just solves single-threaded) |
| SMT-COMP 2026 | Cloud track (19 divisions) | not yet — no distributed SMT solver; the only distributed-worker tooling is CHC-COMP-specific |

<details><summary>Check it yourself — the exact commands</summary>

**Single Query — QF_LinearIntArith (QF_IDL, QF_LIA, QF_LIRA)**
```bash
printf '(set-logic QF_LIA)(declare-const x Int)(declare-const y Int)(assert (= (+ x y) 10))(assert (> x 5))(assert (> y 3))(check-sat)' | ay solve --stdin
```
**Single Query — QF_LinearRealArith (QF_LRA, QF_RDL)**
```bash
printf '(set-logic QF_LRA)(declare-const x Real)(assert (> x 0.1))(assert (< x 0.2))(check-sat)' | ay solve --stdin
```
**Single Query — QF_Bitvec (QF_BV)**
```bash
printf '(set-logic QF_BV)(declare-const x (_ BitVec 8))(assert (distinct (bvand x x) x))(check-sat)' | ay solve --stdin
```
**Single Query — QF_Equality (QF_AX, QF_UF)**
```bash
printf '(set-logic QF_UF)(declare-sort S 0)(declare-fun f (S) S)(declare-const a S)(assert (= (f a) a))(assert (not (= (f (f a)) a)))(check-sat)' | ay solve --stdin
```
**Single Query — QF_Datatypes (QF_DT, QF_UFDT)**
```bash
printf '(set-logic QF_DT)(declare-datatype Color ((red) (green) (blue)))(declare-const c Color)(assert (distinct c red))(check-sat)' | ay solve --stdin
```
**Single Query — QF_Equality+Bitvec (QF_ABV, QF_AUFBV, QF_UFBV, QF_UFBVDT)**
```bash
printf '(set-logic QF_ABV)(declare-const a (Array (_ BitVec 4) (_ BitVec 4)))(declare-const i (_ BitVec 4))(assert (not (= (select (store a i #x3) i) #x3)))(check-sat)' | ay solve --stdin
```
**Single Query — QF_Equality+LinearArith (QF_ALIA, QF_AUFLIA, QF_UFDTLIA, QF_UFDTLIRA, QF_UFIDL, QF_UFLIA, QF_UFLRA)**
```bash
printf '(set-logic QF_AUFLIA)(declare-const arr (Array Int Int))(declare-fun f (Int) Int)(declare-const i Int)(assert (= (select (store arr i 5) i) (f i)))(check-sat)' | ay solve --stdin
```
**Single Query — QF_Equality+NonLinearArith (QF_ANIA, QF_AUFNIA, QF_UFDTNIA, QF_UFNIA, QF_UFNRA)**
```bash
printf '(set-logic QF_UFNIA)(declare-fun f (Int) Int)(declare-const x Int)(assert (= (f (* x x)) 1))(assert (= (f (* x x)) 0))(check-sat)' | ay solve --stdin
```
**Single Query — QF_FPArith (QF_ABVFP, QF_ABVFPLRA, QF_AUFBVFP, QF_BVFP, QF_BVFPLRA, QF_FP, QF_FPLRA, QF_UFFP, QF_UFFPDTNIRA)**
```bash
printf '(set-logic QF_FP)(declare-const x (_ FloatingPoint 8 24))(assert (fp.gt x ((_ to_fp 8 24) RNE 1.0)))(check-sat)' | ay solve --stdin
```
**Single Query — QF_NonLinearIntArith (QF_NIA, QF_NIRA)**
```bash
printf '(set-logic QF_NIA)(declare-const x Int)(assert (= (* x x) 25))(assert (> x 0))(check-sat)' | ay solve --stdin
```
**Single Query — QF_NonLinearRealArith (QF_NRA)**
```bash
printf '(set-logic QF_NRA)(declare-const x Real)(assert (< (* x x) 0.0))(check-sat)' | ay solve --stdin
```
**Single Query — QF_Strings (QF_S, QF_SLIA, QF_SNIA)**
```bash
printf '(set-logic QF_SLIA)(declare-const s String)(assert (= (str.len s) 3))(assert (str.prefixof "ab" s))(check-sat)' | ay solve --stdin
```
**Single Query — Equality (UF, UFDT) [quantified]**
```bash
printf '(set-logic UF)(declare-sort S 0)(declare-fun f (S) S)(assert (forall ((x S)) (= (f x) x)))(declare-const a S)(assert (not (= (f a) a)))(check-sat)' | ay solve --stdin
```
**Single Query — Equality+LinearArith (ALIA, AUFDTLIA, AUFDTLIRA, AUFLIA, AUFLIRA, UFDTLIA, UFDTLIRA, UFIDL, UFLIA, UFLRA)**
```bash
printf '(set-logic UFLIA)(declare-fun f (Int) Int)(assert (forall ((x Int)) (> (f x) x)))(assert (= (f 0) 0))(check-sat)' | ay solve --stdin
```
**Single Query — Equality+MachineArith (ABV, ABVFP, ABVFPLRA, AUFBV, AUFBVDT*, AUFBVFP*, UFBV, UFBVDT*, UFBVFP*, UFBVLIA, UFFPDTNIRA — 19 logics)**
```bash
printf '(set-logic UFBV)(declare-fun f ((_ BitVec 8)) (_ BitVec 8))(assert (forall ((x (_ BitVec 8))) (= (f x) x)))(assert (not (= (f #x01) #x01)))(check-sat)' | ay solve --stdin
```
**Single Query — Equality+NonLinearArith (ANIA, AUFDTNIRA, AUFNIA, AUFNIRA, UFDTNIA, UFDTNIRA, UFNIA, UFNIRA)**
```bash
printf '(set-logic UFNIA)(declare-const c Int)(assert (forall ((x Int)) (>= (* x x) 0)))(assert (< (* c c) 0))(check-sat)' | ay solve --stdin
```
**Single Query — Arith (LIA, LRA, NIA, NRA) [quantified]**
```bash
printf '(set-logic LIA)(assert (forall ((x Int)) (> x 0)))(check-sat)' | ay solve --stdin
```
**Single Query — Bitvec (BV) [quantified]**
```bash
printf '(set-logic BV)(assert (forall ((x (_ BitVec 4))) (bvult x #xf)))(check-sat)' | ay solve --stdin
```
**Single Query — FPArith (BVFP, BVFPLRA, FP, FPLRA) [quantified]**
```bash
printf '(set-logic FP)(assert (forall ((x (_ FloatingPoint 8 24))) (fp.lt x (_ +oo 8 24))))(check-sat)' | ay solve --stdin
```
**Incremental track (17 divisions)**
```bash
printf '(set-logic QF_LIA)(declare-const x Int)(push 1)(assert (> x 5))(check-sat)(push 1)(assert (< x 3))(check-sat)(pop 1)(check-sat)(pop 1)(check-sat)' | ay solve --stdin
```
**Unsat Core track (19 divisions)**
```bash
printf '(set-option :produce-unsat-cores true)(set-logic QF_UF)(declare-const p Bool)(declare-const q Bool)(assert (! p :named a1))(assert (! (not p) :named a2))(assert (! q :named a3))(check-sat)(get-unsat-core)' | ay solve --stdin
```
**Model Validation track (13 divisions)**
```bash
printf '(set-option :produce-models true)(set-logic QF_LIA)(declare-const x Int)(declare-const y Int)(assert (= (+ x y) 7))(assert (> x 2))(check-sat)(get-model)' | ay solve --stdin
```
**Proof Exhibition track (19 divisions)**
```bash
printf '(set-logic QF_UF)(declare-sort S 0)(declare-fun f (S) S)(declare-const a S)(assert (= (f a) a))(assert (not (= (f (f a)) a)))(check-sat)' > /tmp/uf.smt2 && ay solve --proof /tmp/uf.alethe /tmp/uf.smt2 && head /tmp/uf.alethe
```
**Parallel track (19 divisions)**
```bash
ay solve --help | grep -A1 -- '--parallel'
```
**Cloud track (19 divisions)**
```bash
ay submission worker --help
```
</details>

## Optimization and counting competitions

| Competition | Track | Status |
| --- | --- | --- |
| PB Competition (PB26; track list from competition/pb/entries.toml portal category IDs DEC-LIN=112..PARTIAL-LIN=119) | DEC-LIN | ready — correct s/v lines and exit codes on SAT (rc=10) and UNSAT (rc=20) |
| PB Competition | DEC-NLC (nonlinear) | ready — OPB parser accepts product terms and solves them correctly |
| PB Competition | OPT-LIN | ready — incremental o-lines, correct optimum, rc=30 |
| PB Competition | OPT-NLC | ready — nonlinear objective and constraint optimized correctly |
| PB Competition | WBO soft (SOFT-LIN) + partial (PARTIAL-LIN) | ready — both pure-soft and hard+soft .wbo solved with correct minimum violation cost |
| PB Competition | DEC-LIN-CERT (certified decision) | ready — emits VeriPB 'pseudo-Boolean proof version 3.0' with correct conclusions; not machine-checked locally (no VeriPB installed; third_party ships only cake_lpr/dpr-trim/dsr-trim) |
| PB Competition | OPT-LIN-CERT (certified optimization) | ready — proof logs incumbents (soli), cutting-planes derivation (pol), and a BOUNDS conclusion; same local-verification caveat |
| MaxSAT Evaluation (track list from established knowledge: exact uw/w, anytime uw/w, certified; MSE 2025/2026 pages fetched empty) | Exact unweighted | ready — new-format h-line WCNF, MSE-2022+ bitstring v-line, correct optimum |
| MaxSAT Evaluation | Exact weighted | ready — weighted softs optimized correctly |
| MaxSAT Evaluation | Anytime / incomplete | partial — genuine anytime engine (improving o-lines during search; best o + s UNKNOWN + v incumbent at its own --timeout), but no SIGTERM handler: killed externally it dies without the v-line, so it only fits the track if run with an internal --timeout under the external limit; no dedicated incomplete-mode flag |
| MaxSAT Evaluation | Certified | not yet — no proof output of any kind for MaxSAT; absence verified in both CLI and source |
| Model Counting Competition (MC-2026 tracks 1/1F, 2B, 3, 4, 5B confirmed at mccompetition.org/2026/mc_description.html) | Track 1/1F: mc (exact unweighted) | ready — exact arbitrary-precision count with the official output convention |
| Model Counting Competition | Track 2B: wmc (weighted, incl. negative weights) | ready — exact rationals, verified numerically; note the model-count --help one-liner ('exact unweighted MC/PMC') is stale vs actual behavior (cmd_model_count.rs:8-10 documents wmc/pwmc with zero/negative weights) |
| Model Counting Competition | Track 3: pmc (projected) | ready — `c p show` header honored, exact projected count |
| Model Counting Competition | Track 4: pwmc (projected weighted) + Track 5B: amc-complex | ready — pwmc returns exact rationals; amc-complex parses a+bi weights and returns exact complex rationals with real/imag log10 lines |
| MiniZinc Challenge (2026 classes FD/Free/Parallel/Open/Local confirmed at minizinc.org/challenge/2026/rules/) | FD (fixed) class | partial — solves annotated models and applies int_search annotations in source, but has a conformance bug: the CP path prints `==========` after a single satisfy solution even when more solutions exist (falsely claims exhaustive search); int/bool/set only — float models fail at parse |
| MiniZinc Challenge | Free class | ready (same caveats as FD) — -f accepted, correct `----------`/`==========`/`=====UNSATISFIABLE=====` conventions, optimization proves optimum |
| MiniZinc Challenge | Parallel class | partial — `-p N` accepted and solves, but per built-in help parallel workers apply to CP satisfaction only; optimization runs single-threaded |
| MiniZinc Challenge | Open class + builtins/globals inventory | partial — auto CP/SMT portfolio fits the open class and the solver descriptor (ay.msc) plus fzn-exec wrapper exist, but the descriptor is not auto-installed (manual MZN_SOLVER_PATH registration), only 4 globals get native mznlib redefinitions, and there is no float support; Local Search class n/a (not a local-search solver) |

<details><summary>Check it yourself — the exact commands</summary>

**DEC-LIN**
```bash
printf '* #variable= 1 #constraint= 2\n+1 x1 >= 1 ;\n+1 ~x1 >= 1 ;\n' > /tmp/d.opb && ay pb solve /tmp/d.opb
```
**DEC-NLC (nonlinear)**
```bash
printf '* #variable= 3 #constraint= 1 #product= 1 sizeproduct= 3\n+2 x1 x2 x3 >= 2 ;\n' > /tmp/n.opb && ay pb solve /tmp/n.opb
```
**OPT-LIN**
```bash
printf '* #variable= 3 #constraint= 2\nmin: +1 x1 +2 x2 +3 x3 ;\n+1 x1 +1 x2 >= 1 ;\n+1 x2 +1 x3 >= 1 ;\n' > /tmp/o.opb && ay pb solve /tmp/o.opb
```
**OPT-NLC**
```bash
printf '* #variable= 3 #constraint= 1 #product= 1 sizeproduct= 2\nmin: +1 x1 x2 +2 x3 ;\n+1 x1 x2 +1 x3 >= 1 ;\n' > /tmp/on.opb && ay pb solve /tmp/on.opb
```
**WBO soft (SOFT-LIN) + partial (PARTIAL-LIN)**
```bash
printf '* #variable= 2 #constraint= 3\nsoft: 6 ;\n[2] +1 x1 >= 1 ;\n[3] +1 x2 >= 1 ;\n+1 x1 +1 x2 <= 1 ;\n' > /tmp/t.wbo && ay pb solve /tmp/t.wbo
```
**DEC-LIN-CERT (certified decision)**
```bash
printf '* #variable= 1 #constraint= 2\n+1 x1 >= 1 ;\n+1 ~x1 >= 1 ;\n' > /tmp/d.opb && ay pb solve --proof /tmp/d.pbp /tmp/d.opb && cat /tmp/d.pbp
```
**OPT-LIN-CERT (certified optimization)**
```bash
printf '* #variable= 3 #constraint= 2\nmin: +1 x1 +2 x2 +3 x3 ;\n+1 x1 +1 x2 >= 1 ;\n+1 x2 +1 x3 >= 1 ;\n' > /tmp/o.opb && ay pb solve --proof /tmp/o.pbp /tmp/o.opb && cat /tmp/o.pbp
```
**Exact unweighted**
```bash
printf 'h 1 2 0\nh -1 -2 0\n1 1 0\n1 2 0\n' > /tmp/u.wcnf && ay maxsat solve /tmp/u.wcnf
```
**Exact weighted**
```bash
printf 'h 1 2 0\nh -1 -2 0\n1 1 0\n2 2 0\n' > /tmp/w.wcnf && ay maxsat solve /tmp/w.wcnf
```
**Anytime / incomplete**
```bash
ay maxsat solve --timeout 2 <some-hard.wcnf>
```
**Certified**
```bash
ay maxsat solve --help
```
**Track 1/1F: mc (exact unweighted)**
```bash
printf 'c t mc\np cnf 3 2\n1 2 0\n-1 -2 0\n' > /tmp/mc.cnf && ay model-count /tmp/mc.cnf
```
**Track 2B: wmc (weighted, incl. negative weights)**
```bash
printf 'c t wmc\np cnf 2 2\nc p weight 1 0.25 0\nc p weight -1 0.5 0\nc p weight 2 0.125 0\nc p weight -2 0.875 0\n1 2 0\n-1 -2 0\n' > /tmp/wmc.cnf && ay model-count /tmp/wmc.cnf
```
**Track 3: pmc (projected)**
```bash
printf 'c t pmc\np cnf 3 2\nc p show 1 2 0\n1 2 0\n-1 -2 0\n' > /tmp/pmc.cnf && ay model-count /tmp/pmc.cnf
```
**Track 4: pwmc (projected weighted) + Track 5B: amc-complex**
```bash
printf 'c t amc-complex\np cnf 2 1\nc p weight 1 0+1i 0\nc p weight -1 1+0i 0\n1 2 0\n' > /tmp/amc.cnf && ay model-count /tmp/amc.cnf
```
**FD (fixed) class**
```bash
printf 'var 1..3: x :: output_var;\nvar 1..3: y :: output_var;\nconstraint int_lt(x, y);\nsolve satisfy;\n' > /tmp/s.fzn && ay flatzinc solve /tmp/s.fzn
```
**Free class**
```bash
printf 'var 1..5: x :: output_var;\nvar 1..5: y :: output_var;\nconstraint int_lt(y, x);\nsolve minimize x;\n' > /tmp/m.fzn && ay flatzinc solve -f /tmp/m.fzn
```
**Parallel class**
```bash
ay flatzinc solve -p 4 /tmp/s.fzn
```
**Open class + builtins/globals inventory**
```bash
MZN_SOLVER_PATH=$PWD minizinc --solvers | grep -i ay
```
</details>

## Competitions AY would enter directly but does not support yet

Stated plainly: the solving cores exist; the input frontends do not.

| Competition | Track family | Status |
| --- | --- | --- |
| XCSP³ Competition (CP'25; xcsp.org) | CSP / COP over XCSP³-core (integer variables) | not yet — no XCSP³ (XML) parser; the CP/FlatZinc solving core is the same class. Frontend is the only missing piece; roadmap. |
| CASC (CADE/IJCAR ATP system competition) | FOF/FNT first-order divisions (TPTP syntax) | not yet — no TPTP parser; quantified UF/UFLIA solving overlaps but ATP-grade quantifier search is unproven here. Watch-item, not near-term. |

| SyGuS (syntax-guided synthesis; SyGuS-IF format) | PBE / invariant / general tracks | not yet — no SyGuS-IF frontend or synthesis engine. Recorded because **cvc5 competes here** (dominantly), and the benchmark corpus is public and usable. |

## Benchmark corpora we can use before any competition entry

The criterion for this list is simply: a public, well-defined benchmark set
exists. Support status is stated per row; a corpus is valuable for evaluation
even where AY has no entry path yet.

| Corpus / competition | What it is | How AY can use it today |
| --- | --- | --- |
| SyGuS-IF benchmark repository | Synthesis problems (PBE, invariants) | Invariant-synthesis subset overlaps CHC; usable as a CHC-adjacent evaluation source. Synthesis proper: not supported. |
| TPDB (Termination Problems Data Base, termCOMP) | Termination problems | Termination is routinely reduced to CHC — candidate evaluation corpus for the CHC portfolio via standard encodings. No native termination mode. |
| IPC/PDDL benchmark suites (planning) | Planning domains | Classic SAT-encoding target (planning-as-SAT); usable through the SAT core with an external encoder. No PDDL frontend. |
| PACE instances (treewidth etc.) | Parameterized-algorithm challenges | Weak overlap; some tracks have SAT encodings. Recorded for completeness only. |

## Future functionality (consolidated)

Everything marked *not yet* above, in one place — the competition-facing
roadmap, distinct from what ships today:

| Future capability | Unlocks |
| --- | --- |
| Quantified-path Alethe replay (proofs the engine currently refuses to emit rather than emit unverifiably) | SMT-COMP proof story beyond QF; the pigeonhole-class wins become independently checkable |
| MaxSAT certificates (VeriPB-for-MaxSAT) + IPAMIR incremental API | MaxSAT Evaluation certified + incremental tracks |
| QBF certificates (Skolem/Herbrand emission at the CLI) + QCIR + DQBF parsers | QBF Gallery certified / non-CNF / DQBF tracks |
| Distributed SAT engine | SAT Competition cloud track |
| FlatZinc float variables; broader global-constraint natives; parallel CP optimization | MiniZinc Challenge full classes |
| `.mps.gz` + free-form MPS acceptance | MIPLIB end-to-end convenience |
| XCSP³ (XML) frontend | XCSP³ Competition entry (solving core exists) |
| TPTP frontend + ATP-grade quantifier search | CASC entry (cvc5 precedent) |
| SyGuS-IF frontend + synthesis engine | SyGuS (cvc5 precedent) |
| FiniteSets theory (new in Z3 5.0.0) | parity with the latest Z3 surface |
| `ay bench compare run/refs/import/report` (the runner half of the comparison system) | one-command replay-class runs on the benchmark machine |

Entered-but-withdrawn is tracked separately: QF_UFLIA (SMT-COMP) returns when
the false-SAT fix is proven.

Reference points, researched 2026-07-21: XCSP³ 2025 ran at CP'25 (proceedings
arXiv:2511.06918; CoSoCo among the medalists). CASC 2025: Vampire swept every
division. SyGuS competition status and corpus locations are from established
knowledge (last formal SyGuS-Comp editions predate 2026) — verify before
citing publicly. SV-COMP is deliberately absent from the direct-entry table —
it is a software-verification competition where AY participates only as
infrastructure inside Trust MC, not as a direct entrant.

## Beyond the competitions

Capabilities with no competition home, verified the same way:

| Capability | Status |
| --- | --- |
| OMT: minimize/maximize + (get-objectives) + LRA Farkas objective certificates | ready — minimize and maximize both solve; (get-objectives) prints optima; (get-objective-certificates) emits a Farkas dual certificate with sense/bound/entails/strict fields |
| MaxSMT via assert-soft | ready — weighted (assert-soft ... :weight N) solved to the true optimum; cost reported via (get-objectives) as __ay_soft_cost |
| AllSAT enumeration (full + projected) | ready — full and projected enumeration both work with exhaustive/capped reporting; one stale-binary vs HEAD discrepancy on don't-care expansion (see evidence) |
| Incremental solving via native API (push/pop across check-sat) | ready — push/assert/check/pop verified live in-process through four language surfaces; sat→unsat→sat round-trip correct |
| Exact + projected model counting (MCC output format) | ready — exact unweighted mc and projected pmc both correct; weighted (wmc) not supported (help says "exact unweighted MC/PMC") |
| LP/MILP solving on MPS + CPLEX LP formats | ready — MPS LP and CPLEX-LP MILP both solved to correct optima with MIPLIB-style exit codes; format auto-detected |
| 7-language binding surface (Rust, C, C++, Python, Java, JavaScript/WASM, OCaml) | partial — 6 of 7 surfaces live-verified in this environment; JS/WASM has a checked-in test harness but needs `npm i` (koffi) or a wasm32 build, neither present locally |
| Native Rust in-process API | ready — the checked-in example runs and returns a correct model; note `cargo run` at HEAD did not finish within 4 min here (stale target cache vs HEAD), so the Jul 20 prebuilt example binary was run instead |
| Lean 4 verified validators (verification/lean) | ready — full `lake build` succeeded live (43 jobs, zero external deps, Lean 4.30.0-rc2); axiom audits printed [propext, Quot.sound] only — no sorryAx |
| Self-check / strict-proofs fail-closed modes | ready — both modes ran live; unsat still certified under --self-check, sat still model-certified under --self-check --strict-proofs |
| Z3 compatibility tooling: z3-audit + diagnose | ready — diagnose agreed with local z3 4.15.4 and printed a constraint-by-constraint explanation; z3-audit (cli-subset, inventory-only) exited 0 with all scoped rows Ready; full default audit not run here (long-running, and carcara/cadical are not installed locally) |
| CHC SAFE certificates + independent chc_cert_check.py replay | ready — end-to-end verified: SAFE Horn instance solved, inductive-invariant certificate emitted, and external z3 validated all 3 clauses (CERTIFICATE VALID, exit 0) |
