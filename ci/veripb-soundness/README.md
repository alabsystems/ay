# Checker soundness fixtures

**Twenty-one** defects in published VeriPB 3.0.2 make it return a verdict that
**contradicts the truth**. This directory holds **twenty-two** formula/proof pairs
that exhibit them — twenty-two and not twenty-one because defect 7 has two
manifestations with *opposite* wrong verdicts, and each needs its own pair. They
exist so that "VeriPB verified it" is a claim CI can defend rather than repeat.

Run by `scripts/ci/pb_certified_gate.sh` (phase 4) and by
`crates/ay-pb/tests/veripb_pin_gate.rs`. Both require the pinned checker to
**reject** all twenty-two. Total runtime ~0.06s, so this gates every push.

How bad the worst ones are: **four** of the twenty-one need *nothing from the
formula*, and two of those four contain no arithmetic anywhere. Defect 10
(`11-propagation-slack-overflow`) forges `s VERIFIED UNSATISFIABLE` against an
ordinary satisfiable clause in three proof lines. Defect 11
(`12-pbc-fabricated-proofgoal`) does it in six — with **no arithmetic anywhere**
and no extreme number in sight — and through checked deletion the same
fabrication deletes a *core* constraint for free, forging
`s VERIFIED SATISFIABLE` for an unsatisfiable formula. Defect 14
(`15-order-aux-var-not-private`) does it in **four**, by asserting an order's
private variable TRUE at the top level and then letting `scope` inject the order's
own specification — which says the opposite — as unconditional premises. Defect 15
(`16-v2-parser-no-rule-scope`) does the mirror image: `sol` inside an unterminated
`pre_order` is checked against the order's private EMPTY database, "finds" a
solution to a formula that has none, and `conclusion SAT` publishes it. At an
unpatched pin, no verdict from this checker is evidence of anything, for any
formula. That is the size of the gap this directory measures.

Defects 11–21 also make a methodological point worth keeping. Defects 1–10 are
almost all integer-width bugs, and an audit that looks for integer-width bugs
finds integer-width bugs. **Ten** of the last eleven are not arithmetic at all:
missing error branches, an unvalidated variable list, a variable namespace with no
scoping, a parser that enforces no rule placement, four guarantee checks that test
a proxy instead of the hazard, and a parser reading a token's text where it needed
its value. They were found by auditing *surfaces that had never been audited* —
first the subproof, substitution and order machinery, then the surfaces that decide
what a verdict MEANS rather than how a number is computed — not by widening the
search for the previous defect class.

| dir | defect | bug | unfixed verdict | truth |
| --- | --- | --- | --- | --- |
| `01-formula-truncation-utf8` | 1 | formula parsers silently discard every constraint after the first non-UTF-8 line | `VERIFIED SATISFIABLE` | the "solution" falsifies the real formula |
| `02-cnf-unterminated-clause` | 2 | DIMACS CNF/WCNF: unterminated final clause dropped, declared clause count never checked | `VERIFIED SATISFIABLE` | the "solution" falsifies the real formula |
| `03-degree-wrap-weaken` | 3 | unchecked `i64` degree decrement in weaken / variable-form div / variable-form MIR wraps | `VERIFIED UNSATISFIABLE` in 2 proof lines, for *any* satisfiable formula | SATISFIABLE |
| `04-mir-oversized-divisor` | 4 | MIR cut oversized-divisor fallback hard-codes `ceil(A/d)=1`, so MIR of a trivially-true constraint yields a contradiction | `VERIFIED UNSATISFIABLE` | SATISFIABLE |
| `05-le-degree-negation-wrap` | 6 | OPB parser negates the degree of `<=`/`=` rows in the row's own integer width, so `<= i64::MIN` wraps an infeasible row into a trivially true one | `VERIFIED SATISFIABLE` | UNSATISFIABLE |
| `06-unchecked-deletion-conclusion-sat` | 8 | `conclusion SAT` without a solution hint is validated against `best_objective_value` instead of `best_valid_objective_value` | `VERIFIED SATISFIABLE`, exit 0, **with default flags** | UNSATISFIABLE |
| `07-normalize-cancellation-wrap` | 7a | normalization cancels opposite literals of one variable and lowers the degree with an unchecked `-=`, so a trivially true row near `i64::MIN` is stored as the empty contradiction | `VERIFIED UNSATISFIABLE` | SATISFIABLE |
| `08-normalize-negation-wrap` | 7b | the same normalization flips negative coefficients and raises the degree, wrapping an infeasible row into a trivially true one | `VERIFIED SATISFIABLE` | UNSATISFIABLE |
| `09-preserved-add-reification-wrap` | 5 | the `preserved_add` reification degree `coeff_sum - degree + 1` is computed in the row's own width; on overflow the reification literal flips and the proof goal is auto-discharged as trivial, so a variable joins the preserved set with no proof | `VERIFIED OUTPUT EQUIENUMERABLE` | input has 1 solution over its preserved set, the output has 2 |
| `10-pol-addition-cancellation-wrap` | 9 | `pol`'s `+` range-checks the *sum* of the two degrees but then subtracts the literal-cancellation constant in the narrow type, unchecked; the constant is always ≥ 0, so the underflow stores a row that is *more* trivially true than its operands as the empty contradiction | `VERIFIED UNSATISFIABLE`, exit 0, **with default flags** | SATISFIABLE |
| `11-propagation-slack-overflow` | 10 | the propagator computes its slack `coeff_sum - degree` in the row's own width at three sites in `GeneralPBWatcher`; both operands fit but the difference need not, and the wrap makes every coefficient exceed the slack, so a trivially true row is reported to propagate ALL its literals unconditionally | `VERIFIED UNSATISFIABLE` from a **three-line** proof, for *any* formula | SATISFIABLE |
| `12-pbc-fabricated-proofgoal` | 11 | `SubproofContext::pop_database_goal` FABRICATES `C_id \| witness` instead of erroring when the ID has no registered goal; a proof-by-contradiction subproof registers none, so the scope opens with the premise `¬C_id` against the still-present `C_id`, and closing it marks the enclosing subproof's obligation discharged without checking it | `VERIFIED UNSATISFIABLE` from a **six-line** proof with **no arithmetic**, for *any* formula (and `VERIFIED SATISFIABLE` for an unsatisfiable one via `delc`) | SATISFIABLE |
| `13-substitute-degree-wrap` | 12 | `substitute` lowers the degree with an unchecked `-=` per literal mapped to TRUE, so a trivially true row at `i64::MIN` becomes the empty contradiction — and a contradicting row implies every goal, so every proof goal of a `red` step is auto-discharged | `VERIFIED UNSATISFIABLE` | SATISFIABLE |
| `14-def-order-unvalidated-fresh-vars` | 13 | `def_order` stores the transitivity `fresh_right`/`fresh_aux_*` lists verbatim and zips them with `izip!`, which truncates; an empty (legal) or aliasing list makes every transitivity proofgoal equal to its own premise, so a relation with a CYCLE in its strict part installs as a preorder and dominance's descent argument is vacuous | `VERIFIED UNSATISFIABLE` | SATISFIABLE |
| `15-order-aux-var-not-private` | 14 | an order's `aux` variables live in the global namespace and `validate_aux_var` admitted exactly the wrong set (everything when no order is loaded, the order's own auxiliary variables when one is); a top-level `red +1 $a1 >= 1 : $a1 -> 1;` asserts one TRUE for free, and `scope` then injects the order's specification, which says `~$a1`, as unconditional premises | `VERIFIED UNSATISFIABLE` from a **four-line** proof with **no arithmetic**, for *any* formula | SATISFIABLE |
| `16-v2-parser-no-rule-scope` | 15 | the legacy version 2.0 parser enforces no rule placement at all, while its version 3.0 sibling always has; `sol` inside an unterminated `pre_order` is checked against the order's private EMPTY scratch database and a hint-less `conclusion SAT` treats the result as its sole evidence | `VERIFIED SATISFIABLE` from a **six-line** proof, for *any* formula | UNSATISFIABLE |
| `17-enumeration-complete-obji` | 16 | `conclusion ENUMERATION_COMPLETE n` accepts any database contradiction with no provenance test while counting only `solx` exclusions, so an `obji`-installed objective-improving constraint supplies the contradiction and the count stays 0 | `VERIFIED COMPLETE ENUMERATION OF 0 SOLUTIONS` | the formula has 3 solutions over its preserved set |
| `18-solx-empty-preserved-set` | 17 | `solx` with a legal but EMPTY preserved set builds its exclusion over no literals — the empty `>= 1` — and installs it in the database and the core | `VERIFIED BOUNDS 1000 <= obj <= 1000` | SATISFIABLE, optimum 0 |
| `19-conclusion-bounds-solx-contradiction` | 18 | the `conclusion BOUNDS` lower bound is granted for any bound not better than the best logged solution as soon as the database contains ANY contradiction, including one assembled out of `solx` exclusions, which remove solutions rather than following from the problem | `VERIFIED BOUNDS 10 <= obj <= 10` | the optimum is 0 |
| `20-output-guarantee-solx-unguarded` | 19 | `output EQUISATISFIABLE` and `output EQUIOPTIMAL` are not gated against exported solution exclusions; only `EQUIENUMERABLE` was | `VERIFIED OUTPUT EQUISATISFIABLE` | the input has 3 solutions, the exported core has none |
| `21-sol-then-obji-evades-equienum` | 20 | that `EQUIENUMERABLE` gate tested `solution_logged`, which plain `sol` does not set and `obji` cannot set, so `sol …; obji v;` walks past the guard that the identical single rule `soli … : v;` trips | `VERIFIED OUTPUT EQUIENUMERABLE` | the input has 3 solutions, the exported core has none |
| `22-wcnf-literal-token-text` | 21 | the WCNF parser names variables from the literal's token TEXT rather than its value, so the DIMACS spellings `-1`, `-01` and `-0001` become two or three different variables | `VERIFIED BOUNDS 0 <= obj <= 0` | INFEASIBLE (its two hard clauses contradict) |

Defect numbers 1–8 are the ones used in the fork's commit message and
`README.md`; 9–21 continue that numbering and were found here. The mapping is
total — every one of the twenty-one has at least one fixture:

```
defect  1   2   3   4   5   6   7        8   9   10  11  12  13
fixture 01  02  03  04  09  05  07 + 08  06  10  11  12  13  14

defect  14  15  16  17  18  19  20  21
fixture 15  16  17  18  19  20  21  22
```

## `10` to `22` — the post-fork defects, and their `variants/`

Defects 9 and 10 were found by re-auditing the code the **first** patch did not
touch for the classes it did fix; defects 11 to 13 by auditing the *subproof*,
*substitution* and *order* machinery, which neither earlier pass had looked at;
defects 14 to 21 by auditing the surfaces that decide what a verdict **means**
rather than how a number is computed — variable *scoping*, the legacy version 2.0
*parser*, solution *logging*, the conclusion and output *guarantees*, and the WCNF
front end. All thirteen were fixed here as a second patch
(`0002-ay-post-fork-soundness-fixes.patch`) and later reconciled into the private
fork, so the single pinned patch — the fork's `alab-main` delta,
`ci/veripb-patches/0001-ay-veripb-alab-main.patch` — now carries them.

Each of the thirteen directories carries the same things beyond the gated pair:

* **an opposite-verdict companion** — the same formula and the same binary,
  proved the other way (`sat.pbp`, `truth.pbp`, `bounds.pbp`, `unsat.pbp`,
  `infeasible.pbp`, depending on what the forgery claims). One checker, one
  formula, both verdicts, so the false verdict needs no external oracle to be
  recognised as false. For the three output-guarantee fixtures the claim is about
  a *pair* of formulas, so the companion is a pair of ordinary verdicts: the input
  is SATISFIABLE and the exported output is UNSATISFIABLE.
* **a one-knob control** — `variants/boundary-control/` for the arithmetic
  defects (the identical proof against a formula one unit away from the wrap),
  `variants/structure-control/` and `variants/freshvars-control/` for the two
  that are not arithmetic (the identical proof with the *one* structural feature
  that carries the forgery removed). Each is refused by the *unfixed* checker
  too, which pins causation to the defect rather than to "large numbers confuse
  the checker" or "that rule is broken in general".
* **`variants/<code path>/`** — the same defect on each representation or reach
  path it has.
* **a POSITIVE variant** for every fix that *restricts* a rule — `12`, `13`,
  `14`, and all eight of `15` to `22`. A restriction that goes one step too far is
  its own defect: each of those proofs is accepted before and after, and would
  break under the obvious over-broad "fix". Three of them are upstream's **own**
  tests, which is the strongest form the guard can take:
  `15/variants/aux-vars-in-scope-valid/` is `dominance_with_aux_vars` (19 auxiliary
  variables used throughout two `scope` blocks),
  `20/variants/redundance-export-valid/` is `decision_output` (`red`-derived
  constraints exported under `EQUISATISFIABLE`), and
  `21/variants/equioptimal-with-soli/` is
  `optimization_output_opposing_lits_objective` (a legitimate `soli` +
  `EQUIOPTIMAL` proof). The last of those is why fixture 21 is **not** fixed by
  "apply the existing `solution_logged` test to all three guarantees": that would
  reject it.

None of those are rows: `expected.tsv` is one pair per row and the headline is
the one that reaches the defect from an ordinary formula. A fix has to close
every variant anyway.

### `10` — `pol` addition

Defect 9 is the class of defects 3 and 7a (unchecked degree decrement near
`i64::MIN`) in a rule the first patch's `finish_weakening` /
`normalization_fits_in_type` guards do not reach.

The headline pair keeps every extreme number inside the *proof*: the formula is
the ordinary satisfiable clause `x1 ∨ x2`, so no formula-level sanity check can
catch it. That pair is the gated row.

`add`/`+` is implemented four times, once per stored constraint representation,
and every narrow-width copy repeated the unchecked subtraction. The
`10-.../variants/` subdirectories carry one pair per copy, plus the optimisation
surface. They are **not** rows — `expected.tsv` is one pair per row and the
headline is the one reachable from an ordinary formula — but the fix closes all
of them, and the fix is not complete until it does:

| variant | code path | unfixed verdict | truth |
| --- | --- | --- | --- |
| `clause/` | `Clause::add` | `VERIFIED UNSATISFIABLE` | SATISFIABLE |
| `cardinality/` | `Cardinality::add` | `VERIFIED UNSATISFIABLE` | SATISFIABLE |
| `general-i64/` | `GeneralPBConstraint::<i64>::add` | `VERIFIED UNSATISFIABLE` | SATISFIABLE |
| `general-i128/` | `GeneralPBConstraint::<i128>::add` | `VERIFIED UNSATISFIABLE` | SATISFIABLE |
| `bounds/` | as `cardinality/`, optimisation surface | `VERIFIED BOUNDS INF <= obj <= INF` | the optimum is 0 |

`general-i128/` matters on its own: it shows the defect is a property of the
*narrow-width* code and not an `i64` edge case, so widening would move the
threshold rather than close the hole. `bounds/` shows the forgery is not confined
to the `UNSAT` verdict. Run them by hand with the usual two arguments:

```bash
veripb --opb variants/general-i128/gen128.opb variants/general-i128/gen128.pbp
```

### `11` — propagation slack

Defect 10 is one of the two that need nothing at all from the formula.
`GeneralPBWatcher` computed the slack `coeff_sum - degree`
in the row's own width at three sites; both operands fit, the difference need
not, and the wrap makes every coefficient exceed the slack — so a **trivially
true** row is reported to propagate all of its literals unconditionally. Two such
rows, both accepted legitimately by `rup` because they really are trivially true,
leave the trail in conflict, and a trail in conflict RUPs anything:

```
f 1 ;                                  % 1 x1 1 x2 >= 1 ;  (the clause x1 v x2)
rup 2 x1  >= -9223372036854775806 ;    % honest: trivially true
rup 2 ~x1 >= -9223372036854775806 ;    % honest: trivially true
rup >= 1 ;                             % the empty contradiction
conclusion UNSAT : 4 ;
```

Its `variants/formula-borne/` reaches the same defect straight from the formula
in two proof lines. See `11-propagation-slack-overflow/README.md`.

### `12` — a fabricated proofgoal, and no arithmetic at all

Defect 11 is the other one that needs nothing from the formula, and it is the
one that most clearly is not an integer-width bug. `pop_database_goal`
reconstructed a proofgoal for any database ID that had none registered; a
proof-by-contradiction subproof registers none, so `proofgoal <id>` handed the
proof a scope whose premise `¬C_id` contradicts the still-present `C_id`. Closing
that scope set `contradiction_proven` on the *enclosing* subproof and `finalize`
short-circuited, so a `pbc`'s real obligation was never checked:

```
f 1 ;                    % 1 x1 1 x2 >= 1 ;  (the clause x1 v x2)
pbc >= 1 : subproof
proofgoal 1              % fabricated: the goal is C_1, the premise is ~C_1
rup >= 1 ;               % C_1 and ~C_1 are both present — instant conflict
qed;                     % <- "the pbc has proven its contradiction"
qed;
conclusion UNSAT ;
```

`proof_by_contradiction_subproof` is set at three places and all three are
reachable: `pbc` (v3), `red` with an empty witness (v2), and — the route that had
never been tested — `delc` under `strengthening_to_core on`, where the same
fabrication deletes a **core** constraint for free and forges
`s VERIFIED SATISFIABLE` for an unsatisfiable formula. All three have variants.
See `12-pbc-fabricated-proofgoal/README.md`.

### `13` — `substitute` wraps the degree

Defect 12 is the class of defects 3, 7a and 9 (unchecked degree decrement near
`i64::MIN`) in the *substitution* path, which the earlier guards do not reach. It
is not `rup` that is abused: `rup 1 x2 >= i64::MIN ;` is accepted *honestly*
because the row really is trivially true. The wrap happens later, when a `red`
step substitutes the level-0 propagated assignment into it, and the resulting
"contradicting" row implies every proof goal there is. `Clause::substitute`
needs no change (a clause's degree is set to `0` outright) and got none.
See `13-substitute-degree-wrap/README.md`.

### `14` — a "preorder" with a cycle in it

Defect 13 is not arithmetic either. `def_order` stored the transitivity
`fresh_right` / `fresh_aux_1` / `fresh_aux_2` lists verbatim and zipped them with
`izip!`, which stops at the shortest iterator, so the grammatically legal
`fresh_right ;` collapsed both substitutions to nothing and every transitivity
proofgoal became one of its own premises. An empty `proof … qed;` then "proved"
transitivity of a relation whose strict part is a 4-cycle, and `dom`'s descent
argument became vacuous. Aliasing the right variables has the correct arity and
does the same thing, which is why the fix checks arity **and** freshness. See
`14-def-order-unvalidated-fresh-vars/README.md`.


### `15` — an order's private variables, asserted in public

Defect 14 is the third that needs nothing from the formula, and the shortest of the
three: four proof lines. An order's `aux` variables are existentially quantified by
the order's *specification*, and `scope` injects that specification as unconditional
premises. But they live in the global variable namespace, and `validate_aux_var`
admitted exactly the wrong set — `is_none_or` let everything through when no order
was loaded, and when one was loaded it let through precisely that order's auxiliary
variables. So `red +1 $a1 >= 1 : $a1 -> 1;` asserts one TRUE for free (its own
proofgoal is trivial under the witness), the order's spec says `~$a1`, and the first
`scope` in any `dom` or `red` subproof makes the database contradictory inside every
proofgoal. Three reach paths in version 3.0 and a fourth in version 2.0, where
auxiliary variables are spelled as ordinary identifiers and there is no `$` to key
on. See `15-order-aux-var-not-private/README.md`.

### `16` — one parser checked rule placement and the other did not

Defect 15 is the fourth. `grep -n scope` in
`veripb-parser/src/pbp_parser/legacy_v2/parser.rs` returned nothing, while its
version 3.0 sibling has always answered `The rule X is not allowed in a Y context`.
`def_order`/`pre_order` swaps the database for an empty one, so `sol` written inside
an unterminated `pre_order` is checked against **nothing**, "succeeds", and a
hint-less `conclusion SAT` — for which a logged solution is the only evidence —
publishes `s VERIFIED SATISFIABLE` for a formula with no models. Two copies of a
check are two chances to have only one of them; both parsers now call the same
predicate. See `16-v2-parser-no-rule-scope/README.md`.

### `17` to `21` — five verdicts that tested a proxy instead of the hazard

The last five are one family. Each is a place where the checker had to answer "is
what I am about to certify still a statement about the ORIGINAL problem?", and each
answered with something adjacent instead:

* `17` — `ENUMERATION_COMPLETE` asked "is the database contradictory?" and never
  asked where the contradiction came from, so an `obji`-installed constraint that
  removes solutions supplied it while the exclusion count stayed 0.
* `18` — `solx` asked "is there a preserved set?" and not "does it have anything in
  it", so an empty one produced the empty contradiction and installed it in the core.
* `19` — `conclusion BOUNDS` asked "is the database contradictory?" and not "was the
  contradiction assembled out of the exclusions themselves".
* `20` — the output guarantees asked the question in **one** of three arms.
* `21` — that one arm asked "was a solution logged?", a proxy that plain `sol` did
  not set and `obji` could not, so the same step spelled as two rules walked past
  the guard that the single rule tripped.

All five are fixed the same way: the provenance travels with the CONSTRAINT
(`is_solution_excluding`, `is_objective_restricting`) instead of in a checker-wide
flag, and each verdict tests for the hazard it actually has. Constraint-borne
provenance also stops applying once the constraint is deleted, which a flag could not
express. The five directories' READMEs have the reproductions.

### `22` — a parser that read the text instead of the value

Defect 21 is in the WCNF front end, so it needs no clever proof at all: it hands the
checker a different problem from the one on disk. `"x" + &lex.slice()[1..]` names the
variable after the literal's *spelling*, and DIMACS integers may carry a sign and
leading zeros, so `-1`, `-01` and `-0001` became two or three variables. `h 1 0` and
`h -01 0` — a contradiction — parsed as `(x1) AND (~x01)`. The value was already
parsed three lines earlier. The OPB and CNF parsers were audited for the same mistake
and do not have it, which
`22-wcnf-literal-token-text/variants/sibling-cnf-parser/` pins rather than asserts.

## The two late fixtures (07/08/09) and why they were missing

Defects 5 and 7 were found *during* the work on the other six, and the fork's
own `README.md` says so: "Defects 5 and 7 were found later, during the fixes,
and are covered by in-tree tests only." So the first patch always fixed all
eight — this directory gated only six of them. That is a fixture-coverage gap,
not a missing fix, and 07/08/09 close it. `10` and `11` are a different case:
they were missing FIXES, closed by the post-fork work (ay patch 0002, now in the
fork).

### `09` is a weaker class of wrong verdict than the rest

It falsifies `s VERIFIED OUTPUT EQUIENUMERABLE`, not a SAT/UNSAT/BOUNDS
conclusion. Under this repo's own contract that is still a full acceptance
(`veripb_run` takes the first `^s ` line; `veripb_accepted` matches
`s VERIFIED `*), so it gates correctly — but defect 5 **cannot** corrupt a
satisfiability verdict and should not be described as if it could. The reason
is in the code: the preserved set's only other consumer is `solx`, and
`context.preserved_set_changed` is set unconditionally at the top of
`PreservedAddRule::compute` and never reset, so every `solx` after any
`preserved_add` is a hard error. If someone finds a route past that, replace
`09` with it.

`09`'s ground-truth column is therefore a *counting* claim rather than
`SATISFIABLE`/`UNSATISFIABLE`. It is hand-checkable in seconds: `1 x1 >= 1`
over preserved `{x1}` has one projected solution; over `{x1,x2}` it has two.

### `09/file-variant/` — the convincing form, not run by the gate

`09` uses `output EQUIENUMERABLE IMPLICIT`, and `OutputType::Implicit => {}`
performs no checking, so a skeptic can argue the false claim rides on IMPLICIT
being unchecked-by-design rather than on defect 5. `file-variant/` is the FILE
form of the same fixture, where the checker actively compares the two declared
preserved sets — it refuses when `x2` is absent from the output formula, and
reports them equal when it is present:

```bash
veripb --opb file-variant/pres.opb file-variant/pres.pbp file-variant/out.opb
#   upstream 4bb10c2c: exit 0, s VERIFIED OUTPUT EQUIENUMERABLE   (wrong)
#   pinned build:      exit 1, "Proofgoal #2 could not be autoproven."
```

It takes a fourth argument, which `expected.tsv`'s six-column schema and
`veripb_run`'s three-argument contract do not carry, so the gate runs the
IMPLICIT form and this one is kept for readers. Do not delete it to tidy up.

## Why the pin ships a patch

The fixes for all twenty-one defects are in one file,
`ci/veripb-patches/0001-ay-veripb-alab-main.patch`, applied on top of the
upstream commit named in `ci/veripb.pin`. That keeps the trusted checker
**reproducible from the public upstream plus that patch** — clone, checkout,
`git apply`, build — rather than "whatever `veripb` was on the machine that
day". The patch file is kept in the development tree only; the public snapshot
ships the pin, whose sha256 stays the checker's identity, and these fixtures.
There a checker supplied through `VERIPB_BIN` is judged by behaviour alone: the
self-test battery and all twenty-two fixtures in this directory.

It is one file on purpose. The patch is `git diff --binary 4bb10c2c <alab-main
tip>` of the private fork **verbatim**, which is checkable with `cmp` against a
fresh clone; that is its entire claim to trust. Folding a locally written fix
into it would destroy the property with no way to tell the two apart afterwards.
So a further locally found defect is fixed **in the fork** and the patch re-cut,
never added as a second numbered patch. (This repo previously carried a second
patch, `0002-ay-post-fork-soundness-fixes.patch`, for defects 9–21; those fixes
were reconciled into the fork and the second patch dropped — see
`ci/veripb-patches/README.md` and `ci/veripb.pin`.)

If you point the gate at a different checker (`VERIPB_BIN=...`), the fixtures
still run. A checker that gets any of these wrong is refused, and the gate says
which one and what it answered.

## What the first patch also carries, and what it does NOT buy

Since that patch became the full `alab-main` delta it also contains
`veripb-core-proved`, a Clean-proved kernel for seven of the arithmetic rules.
Read `ci/veripb-patches/README.md` before citing it. The short version:

* The pinned checker **directly depends on the crate** and exposes its bridge
  through `--kernel-verify`, which defaults to false. The gate's certificate
  commands do not request that mode. Phase 2b explicitly builds and runs the
  crate's Rust tests; it does not qualify the optional bridge or its proof.
  Its selected-name symbol scan remains a regression tripwire. Zero matching
  names in an optimized binary cannot establish absence of reachable code.
* An earlier `clean 1.2.0` check reported **471 of 874 declarations checked**
  and attributed the gap to toolchain lineage (see the retained record in
  `ci/veripb-patches/README.md`). This gate does not repeat that formal check
  or establish a current proof verdict.

Neither point is a reason to remove it, and neither is a licence to describe
CI as "verifying proofs". It does not.
