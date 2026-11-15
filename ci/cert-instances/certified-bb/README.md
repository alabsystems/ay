# Certified LP branch-and-bound (`certified-bb`) — AY's ninth OPT-LIN route

`certified-bb` closes `ceil(LP*) = optimum - 1` instances by a LITERAL SPLIT
instead of by a structural fact. It is an **engine**, not a ninth family: it
needs only `>=` rows and a linear `min:` over plain positive literals.

The derivation, the two prototype defects it does not inherit, and the
deterministic COUNT budgets are documented on
`crates/ay-pb-core/src/proof/cert/certified_bb.rs`. This directory holds the
incumbents and two of the emitted proofs.

## What AY emits today

Measured on the Rust route (branch `certifier9-rust-port`), checker THE PIN from
`ci/veripb.pin`, binary sha256
`c3a2fc5592ce5dc7812df155dd3f968c1fc40dd0cbbfa51011de024be94e40dc`, re-proved
against all twenty-two `ci/veripb-soundness` fixtures (22 rejected, 0 accepted)
immediately before and after every verdict below.

| instance | optimum | verdict | lines | bytes | nodes | leaves | LP polls |
|---|---|---|---|---|---|---|---|
| `normalized-g9x9` | 20 | `s VERIFIED BOUNDS 20 <= obj <= 20` | 35 | 12,509 | 29 | 15 | 1,925 |
| `normalized-dominating_set_hexgrid_opt_r6_c50` | 76 | `s VERIFIED BOUNDS 76 <= obj <= 76` | 11 | 11,624 | 5 | 3 | 4,276 |
| `normalized-addm4.r` | 165 | `s VERIFIED BOUNDS 165 <= obj <= 165` | 67 | 249,950 | 73 | 37 | 9,724 |
| `normalized-sbox_4_shg` | 22 | `s VERIFIED BOUNDS 22 <= obj <= 22` | 348 | 230,947 | 355 | 178 | 25,304 |

Against the former Python prototype (available in git history) on the same
instances and the same incumbents, the Rust route is **smaller and reaches
further**:

| instance | prototype | Rust route | |
|---|---|---|---|
| `g9x9` | 20,965 B / 29 lines | 12,509 B / 35 lines | 1.68x smaller |
| `hexgrid_r6_c50` | 19,712 B / 11 lines | 11,624 B / 11 lines | 1.70x smaller |
| `sbox_4_shg` | 435,163 B / 437 lines | 230,947 B / 348 lines | 1.88x smaller |
| `addm4.r` | NODE CAP 4000 hit at depth 18, no file | 249,950 B / 67 lines | a conversion the prototype did not make |

## The two it does NOT close, and why

Neither is a fact about the branch-and-bound argument. Both are the LP the
argument is guided by (`optimize::lp_bound`) refusing the model:

* `normalized-f20c10b_008_area_delay` (3,973 vars, 11,097 rows) —
  `exhausted(node-lp-declined) lp=no-dual-point-in-budget`. Neither LP tier
  returns a dual point for the ROOT model. Not a budget edge: still declines at
  60,000 polls (6.4 s).
* `normalized-f20c10b_011_area_delay` (13,304 vars, 43,326 rows) —
  `exhausted(node-lp-declined) lp=model-too-large(MAX_ROWS=40000,measured=43326)`.
  Rejected UNREAD by the certificate path's static size cap.

## Contents

* `g9x9.pbp`, `dominating_set_hexgrid_opt_r6_c50.pbp` — exactly what
  `ay pb solve --timeout 60000 --proof` writes, sha256
  `24a0ebac534155796df2a501990f8d454d7028216bff8a69f8c992517f288a50` and
  `bc2945e053d72ac23496338e0b6457d675d3a3c9a6c380df02e3203a2484d57a`, against
  instances sha256 `d95d204e16e4de14b50f0d1dd37ca461da293bef244ba09e56d6893f03b152cf`
  and `f979450646b0ec84eb3c3f7630157c387463c05ec9df2cb70bfc57ab9712c241`.
  `addm4.r` (`cb8aae4a…`) and `sbox_4_shg` (`c0a0ee42…`) are not committed:
  together they are 470 KB and regenerate in seconds.

  These differ from the `certified_bb_probe` output for `g9x9` and
  `hexgrid_r6_c50` and are IDENTICAL for `addm4.r` and `sbox_4_shg`. That is
  expected and worth stating rather than filing: the proof's `soli` line IS the
  incumbent, so a search that lands on a different optimal solution than the
  `sol.json` here produces different bytes for the same tree. Both verify.
* `*.sol.json` — incumbent supports, 0-based.
* Regenerate any of them with
  `targo --unverified run --release -p ay-pb-core --example certified_bb_probe -- <instance.opb> <sol.json> <optimum> <out.pbp>`.

## Both binaries, end to end

House rule: count `ay pb solve` AND `ay-pb` separately, and name the
denominator. Denominator = the FIVE instances the prototype claimed, times the
two shipped binaries = 10 of the 164 residual census pairs.

At `--timeout 60000`, from a cold `.opb`, with the whole certificate chain in
the loop and `--cert-debug` naming the rung:

| instance | `ay pb solve` (cli) | `ay-pb` | route | cross-binary bytes |
|---|---|---|---|---|
| `g9x9` | `s VERIFIED BOUNDS 20 <= obj <= 20` | same | `certified-bb` | IDENTICAL |
| `hexgrid_r6_c50` | `s VERIFIED BOUNDS 76 <= obj <= 76` | same | `certified-bb` | IDENTICAL |
| `addm4.r` | `s VERIFIED BOUNDS 165 <= obj <= 165` | same | `certified-bb` | IDENTICAL |
| `sbox_4_shg` | `s VERIFIED BOUNDS 22 <= obj <= 22` | same | `certified-bb` | IDENTICAL |
| `f20c10b_008` | no proof | no proof | — | — |
| `f20c10b_011` | no proof | no proof | — | — |

**8 of the 10 pairs convert; 2 do not.** `g9x9` is not a conversion of the same
kind — AY already certified it BY SEARCH (32,965,756 bytes, 47,748 lines) — so
what this route buys there is 2,637x fewer bytes, not coverage.

`--cert-debug` also confirms in-engine why the eight existing rungs cannot do
it: on `hexgrid_r6_c50` the LP-dual floor reports `bound=75 opt=76` and on
`g9x9` `bound=19 opt=20 converged=true`. That is `ceil(LP*) = optimum - 1`,
measured by AY's own exact simplex, so weak duality caps every LP-dual floor
strictly below the optimum and the split is the only thing left.

## Adversarial battery, run against these bytes

Fifteen mutation shapes on `g9x9.pbp` and on
`dominating_set_hexgrid_opt_r6_c50.pbp`, identical results on both:

* **eleven must-reject shapes are all REJECTED** by the pin — bound one higher;
  all derivation stripped (soli + conclusion kept); one leaf dropped; one
  resolution dropped; the `soli` line dropped; a leaf divisor one smaller; a leaf
  row multiplier bumped; a leaf's first row id changed; the logged assignment
  flipped; the `f` count one lower; the `f` count one higher.
* **two accepted no-ops are arithmetic identities** — enlarging a leaf divisor
  (every coefficient is already `<= K`, so the clause is unchanged) and swapping
  a resolution's two operands (addition commutes).
* **two accepted mutations are findings about the CHECKER, not this emitter** —
  `conclusion`'s row hint is advisory and unvalidated (pointing it at id 999999,
  which does not exist, changes nothing: the pin still finds the derived
  contradiction), and dropping the `s` from the FINAL resolution is accepted
  because that combination is already contradictory before saturation. The
  control proving the hint case is not a hole is `strip all derivation, keep soli
  + conclusion`, REJECTED on both.

**Formula binding**: relaxing ONE row of the instance by 1 makes the pin REJECT,
8 of 8 rows probed, on both instances. The proof is a proof of *this* formula.

## What a DECLINE costs

This rung is unscheduled — it never consults the caller's clock — so its global
LP-poll budget (32,768) is the only thing bounding what a decline costs. Two
measurements, and they do not agree in wall time:

| instance | outcome | polls | wall |
|---|---|---|---|
| `injcomp_..._size_29` | `exhausted(lp-poll-budget)` at depth 201 | 32,772 (full) | 3.7 s |
| `sbox_4_shg` | certified | 25,304 | ~36 s |

A poll costs 0.11 ms on the first and 1.4 ms on the second — 13x apart, with the
SMALLER model (147 vars vs 2,494) the expensive one, because its exact rational
tableau is denser. **The count bounds WORK and byte-reproducibility, not wall
time.** The honest ceiling is one full budget at the most expensive rate
measured: about 46 s.

**Independent attack on the floors** (HiGHS MIP, own OPB reader, exact integer
recheck; neither AY nor VeriPB in the loop): asked for a feasible point at
`optimum - 1` on all four certified instances, and got `kInfeasible` on all four.
No solution below any claimed floor could be constructed.

## Status: not a manifest row, for the same two reasons as before

1. `manifest.tsv` promises "nothing here depends on an external corpus, so a
   fresh clone can run the whole gate". `benchmarks/pb-comp/*` is gitignored, so
   a fresh worktree has neither the `.opb` nor the `.opb.xz`, and `veripb` there
   fails with `Failed to open file` — a SETUP failure that a naive gate would
   read as a pass.
2. The route's own end-to-end coverage is gated in-tree instead, by
   `certified_bb::tests::petersen_vertex_cover_certifies_through_a_split`: the
   Petersen graph has independence number 4, so its minimum vertex cover is 6
   while the all-half point puts `ceil(LP*)` at 5 — no LP-dual floor can reach
   the bound, so a certificate at 6 is evidence the split fired. That test needs
   no corpus.
