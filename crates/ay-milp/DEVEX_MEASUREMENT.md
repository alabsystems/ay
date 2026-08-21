# Forced Devex measurement

This is the corpus record referenced by `src/simplex.rs`. It is kept outside
`Simplex::loop_phase_inner` so measurement notes do not inflate executable
function and source-file quality debt.

⚠⚠ MEASURED, AND IT STAYS A LEVER. `--devex` gained a carrier in the
reader-without-writer census, so the first thing that happened was a
spectacular single instance — gt2 4,954 -> 116 nodes — and the
question "is the DEVEX_WIDTH gate above simply set too high?". It is
not. The corpus says this rule wins big on a minority and loses on
the majority, which is the same verdict the 2026-07 transplant
campaign recorded ("devex pricing was 3.4x worse", `tune.rs`), now
with the per-instance shape of it.

14-instance MILP corpus, `ay-milp solve --time-limit 60`, one thread,
NODES (the 11 that reproduce to the digit across two baseline runs;
mas74/misc07/qiu are budget-coupled and excluded):

| instance | rows x cols | off | `--devex` | ratio |
|---|---|---|---|---|
| gt2     | 29 x 188      | 4,954   | **116**   | 0.024 |
| qnet1   | 503 x 1,541   | 2,058   | **694**   | 0.338 |
| dcmulti | 290 x 548     | 761     | 637       | 0.837 |
| mas76   | 12 x 151      | 273,252 | 271,026   | 0.992 |
| pk1     | 45 x 86       | 274,435 | 273,891   | 0.998 |
| air03, mod010, nw04, rout | — | — | IDENTICAL | 1.000 |
| p0201   | 133 x 201     | 110     | **152**   | 1.378 |
| blend2  | 274 x 353     | 9,070   | **14,712**| 1.622 |

nw04 IS A NO-OP BY CONSTRUCTION and an earlier draft of this table got
it wrong, which is worth recording because of HOW it was wrong. At
36 x 87,482 its `n/m` is 2,430, far above `DEVEX_WIDTH`, so the LP is
already `wide`, Devex is already on, and `force_devex` cannot add
anything: base 2,571 and `--devex` 2,571 on a quiet box, while
`--no-devex` moves it to 3,998 — which is only possible if Devex was
active all along. The discarded reading (1,115/893, "nondeterministic
under `--devex`") was taken at load 20-37 against a 60s budget on a
run that uses ~17s of it: nw04 is BUDGET-COUPLED under load, and it
disguised itself as deterministic by agreeing across two quiet
baseline runs. Two agreeing runs do not establish determinism for an
instance that spends a third of its budget.

Geometric mean 0.682 — and that number is the trap. Two DETERMINISTIC
regressions sit above the 10% bar, and the witness set turns the sign
over completely: 15 MIPLIB witnesses, same budget, geometric mean
**1.219** on the nine that reproduce (lseu 1,978 -> 5,078, stein27
3,077 -> 5,002, misc03 162 -> 224, p0548 2,380 -> 2,614, enigma
16,765 -> 18,123; only p0033 287 -> 254 and stein45 58,414 -> 56,880
improve) — and **p2756 LOSES ITS VERDICT**: OPTIMAL 3124 at ~17s and
83,031/80,577 nodes in both baseline reps, `BOUND 3118` at the 60s
limit with Devex forced. A pricing rule that costs a proof is not a
default at any geometric mean.

THE ALL-CONTINUOUS RIM IS THE SAME STORY, and it is worth the space
because the rim is where forcing Devex is *safest* — no tree, so no
vertex-choice side effect on branching, only iteration count.
`examples/mps_solve --iter-ledger` on the `oracle_v2` covering leg
(load-invariant totals, deterministic, verified by repeat):

| LP | off | `--devex` | ratio |
|---|---|---|---|
| domset_mw19_13..23 (10 LPs) | 12,472–14,638 | 2,401–2,918 | 0.188–0.229 |
| hexgrid_opt_ncols_160       | 8,087         | 6,667       | 0.824 |
| hexgrid_opt_ncols_400       | 47,441        | **127,367** | **2.685** |

A uniform ~4.7x on the weighted-domset family, a 2.7x LOSS on a
hexgrid from the SAME covering class — so "model has no integer
column" is not a boundary either, it is just a smaller pool to
overfit in. PASS counts are untouched (COVER 13/17, MPS 21/21 in both
arms at 300s; no verdict moved either way, and none of the four
hexgrid timeouts is rescued).

WHAT WAS TRIED FOR A GATE AND REFUSED. The winners and losers do not
separate on anything `tune::Shape` can see: not general-integer count
(gt2 164 wins, blend2 33 loses, qnet1 129 wins at 8% of columns), not
integrality fraction, not continuous-column presence (dcmulti 473
continuous wins, p0201 zero continuous loses). The only separator on
offer is n/m — losses at 1.29 and 1.51, wins from 1.89 up — i.e. a
second, lower `DEVEX_WIDTH` around 1.75. That is a threshold fitted
to TWO losing instances, and `tune.rs`'s standard for a `Policy` rule
is a shape that wins where it fires and does not lose elsewhere. It
is not met, so no rule lands and the flag stays a lever.

`--no-devex` is NOT the inverse of this and the pair was checked:
it disables Devex entirely, so it moves exactly the `wide` members
(air03 3 -> 5, nw04 2,571 -> 3,998, mas76 273,252 -> 273,434,
mod010 2,381 -> 2,187, geometric mean 1.072) and leaves every
non-wide instance byte-identical. The two flags agree: they are the
two sides of the `DEVEX_WIDTH` gate, and the gate as it stands is
net-positive with mod010 as its one honest cost.
