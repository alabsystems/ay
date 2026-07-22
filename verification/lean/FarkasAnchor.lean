/-
Copyright 2026 Andrew Yates
SPDX-License-Identifier: Apache-2.0

FIXED-FIXTURE KERNEL CROSS-CHECK for ay-pb's Farkas-certificate checker
(`crates/ay-pb/src/optimize/farkas_cert.rs` :: `check_slack`).

This file re-runs the same Boolean decision procedure as `check_slack` inside
the **Lean kernel** (by `decide`, not `native_decide`) on one emitted certificate
and one tampered certificate. It establishes agreement on those fixed literals;
it does not kernel-check the JSON deserializer or provide the general soundness
theorem for the Rust checker in this public snapshot.

## What is ported here (and why it is faithful)

`checkSlackEntailmentZ` is a self-contained port of the Boolean slack-checking
procedure used by the Rust `check_slack` implementation. The runnable checker
uses only `Int` / `List` / `Bool` / `decide` — pure Lean core, no Mathlib — so
it can be kernel-reduced with the `verification/lean` toolchain. The definitions
below are self-contained in this file. This fixture checks computational
agreement only and does not ship a general soundness theorem for the procedure.

## The JSON -> Lean mapping (from the emitted fixtures)

`crates/ay-pb/.../lp_bound.rs :: emit_farkas_cert_json_for_lean_anchor` drives a
real on-disk `.opb` through AY's certificate path and writes the emitted
`SCertZ` (serde, BigInt as decimal strings) to `farkas_anchor/{valid,
tampered}_cert.json`. The mapping is direct:

  * `QPair {num, den}`  (decimal strings)  ->  `(num, den) : Int x Int`
  * variable name string  ->  the same `String` key
  * `"Le"/"Ge"/"Eq"`     ->  `Kind.le / Kind.ge / Kind.eq`
  * `LinConZ {coeffs, kind, constant}`  ->  `{ coeffs, kind, const }`
  * `SCertZ {base = {premises, multipliers, conclusion}, slack, margin}`  ->  ditto

`demoRealCert` / `demoTamperedCert` below are the literal transcriptions of
`valid_cert.json` / `tampered_cert.json`. The deserializer itself is not in the
kernel; the kernel checks only that these literals reduce to the same Boolean
results as the Rust fixture.

The real instance is the on-disk OPT-LIN benchmark
`benchmarks/pb-comp/test-instances/optimization-small.opb`:
  min x1 + 2 x2 + 3 x3 + 4 x4
  s.t.  x1 + x2 + x3 + x4 >= 2,  x1 + x3 >= 1,  x2 + x4 >= 1
(real exact LP relaxation floor 3; vars 0-indexed in the cert: x1->"0" .. x4->"3").
It is driven through AY's certificate path (`lp_lower_bound_with_cert`
with `AY_PB_FARKAS_CERT` set), the exact wiring `native_oll` uses.

Premises (11): the 3 structural Ge rows, then 4 box rows -x_v >= -1, then 4
lower-bound rows x_v >= 0. Multipliers: row0 (>=2) = 1, row2 (x2+x4>=1) = 1,
lower-bound rows for x3,x4 = 2, all others 0. So the mu-weighted combination is
  1*(x0+x1+x2+x3) + 1*(x1+x3) + 2*x2 + 2*x3 = x0 + 2 x1 + 3 x2 + 4 x3  (= obj),
with combined constant 1*2 + 1*1 = 3. Conclusion: obj >= 3 (valid) / >= 4
(tampered). slack 0, margin 1.
-/

namespace FarkasAnchor

/-! ## Checker types. -/

/-- Relation kind. -/
inductive Kind where
  | le | ge | eq
deriving Repr, DecidableEq

/-- An unreduced rational as an integer pair `(num, den)` with `den > 0`. -/
abbrev QPair := Int × Int

/-- A linear constraint with integer-pair data. -/
structure LinConZ where
  coeffs : List (String × QPair)
  kind   : Kind
  const  : QPair
deriving Repr

/-- An entailment certificate with integer-pair data. -/
structure CertZ where
  premises    : List LinConZ
  multipliers : List QPair
  conclusion  : LinConZ
deriving Repr

/-- A slack-tolerant integer-pair entailment certificate. -/
structure SCertZ where
  base   : CertZ
  slack  : QPair
  margin : QPair
deriving Repr

/-! ## Kernel-reducible integer checks. -/

/-- `0 <= num/den` (with `den > 0`)  <=>  `0 <= num`. (`nonnegZ`.) -/
def nonnegZ (p : QPair) : Bool := decide (0 ≤ p.1)

/-- `toQ a <= toQ b` with positive denominators  <=>  `a.num*b.den <= b.num*a.den`. (`leZ`.) -/
def leZ (a b : QPair) : Bool := decide (a.1 * b.2 ≤ b.1 * a.2)

/-- `toQ a < toQ b` with positive denominators  <=>  `a.num*b.den < b.num*a.den`. (`ltZ`.) -/
def ltZ (a b : QPair) : Bool := decide (a.1 * b.2 < b.1 * a.2)

/-- `toQ a = 0`  <=>  `a.num = 0`. (`isZeroZ`.) -/
def isZeroZ (a : QPair) : Bool := decide (a.1 = 0)

/-- Product of two integer pairs (unreduced). (`mulZ`.) -/
def mulZ (a b : QPair) : QPair := (a.1 * b.1, a.2 * b.2)

/-- Sum of two integer pairs (unreduced common denominator). (`addZ`.) -/
def addZ (a b : QPair) : QPair := (a.1 * b.2 + b.1 * a.2, a.2 * b.2)

/-- Negation. (`negZ`.) -/
def negZ (a : QPair) : QPair := (-a.1, a.2)

/-! ## Map algebra. -/

/-- (`scaleMapZ`.) -/
def scaleMapZ (k : QPair) (m : List (String × QPair)) : List (String × QPair) :=
  m.map (fun p => (p.1, mulZ k p.2))

/-- (`negMapZ`.) -/
def negMapZ (m : List (String × QPair)) : List (String × QPair) :=
  m.map (fun p => (p.1, negZ p.2))

/-- (`normalizeZ`.) -/
def normalizeZ (lc : LinConZ) : List (List (String × QPair) × QPair) :=
  match lc.kind with
  | .le => [(lc.coeffs, lc.const)]
  | .ge => [(negMapZ lc.coeffs, negZ lc.const)]
  | .eq => [(lc.coeffs, lc.const), (negMapZ lc.coeffs, negZ lc.const)]

/-- (`rowCoeffsZ`.) -/
def rowCoeffsZ (μ : QPair) (lc : LinConZ) : List (String × QPair) :=
  ((normalizeZ lc).map (fun row => scaleMapZ μ row.1)).flatten

/-- (`combCoeffsZ`.) -/
def combCoeffsZ : List (LinConZ × QPair) → List (String × QPair)
  | [] => []
  | (lc, μ) :: rest => rowCoeffsZ μ lc ++ combCoeffsZ rest

/-- (`rowConstZ`.) -/
def rowConstZ (μ : QPair) (lc : LinConZ) : QPair :=
  ((normalizeZ lc).map (fun row => mulZ μ row.2)).foldr addZ (0, 1)

/-- (`combConstZ`.) -/
def combConstZ : List (LinConZ × QPair) → QPair
  | [] => (0, 1)
  | (lc, μ) :: rest => addZ (rowConstZ μ lc) (combConstZ rest)

/-- (`addEntryZ`.) -/
def addEntryZ : List (String × QPair) → String → QPair → List (String × QPair)
  | [], v, c => [(v, c)]
  | (w, d) :: rest, v, c =>
      if v = w then (w, addZ d c) :: rest
      else (w, d) :: addEntryZ rest v c

/-- (`collapseZ`.) -/
def collapseZ (m : List (String × QPair)) : List (String × QPair) :=
  m.foldl (fun acc p => addEntryZ acc p.1 p.2) []

/-- (`normalizeConclusionZ`.) -/
def normalizeConclusionZ (lc : LinConZ) : Option (List (String × QPair) × QPair) :=
  match lc.kind with
  | .le => some (lc.coeffs, lc.const)
  | .ge => some (negMapZ lc.coeffs, negZ lc.const)
  | .eq => none

/-- (`diffMapZ`.) -/
def diffMapZ (pairs : List (LinConZ × QPair))
    (conclCoeffs : List (String × QPair)) : List (String × QPair) :=
  combCoeffsZ pairs ++ negMapZ conclCoeffs

/-- (`allDenPos`.) -/
def allDenPos (cz : CertZ) : Bool :=
  (cz.premises.all (fun lc =>
      lc.coeffs.all (fun p => decide (0 < p.2.2)) && decide (0 < lc.const.2))) &&
  cz.multipliers.all (fun μ => decide (0 < μ.2)) &&
  cz.conclusion.coeffs.all (fun p => decide (0 < p.2.2)) &&
  decide (0 < cz.conclusion.const.2)

/-! ## The kernel-runnable slack checker. -/

/-- **The runnable slack checker** — a fixture-level port of `check_slack`
    (Rust). Every comparison is
    integer cross-multiplication, so `decide` reduces it in the kernel. -/
def checkSlackEntailmentZ (sc : SCertZ) : Bool :=
  let cz := sc.base
  allDenPos cz &&
  decide (0 < sc.slack.2) && decide (0 < sc.margin.2) &&
  cz.premises.length == cz.multipliers.length &&
  cz.multipliers.all (fun μ => nonnegZ μ) &&
  nonnegZ sc.slack &&
  ltZ sc.slack sc.margin &&
  (match normalizeConclusionZ cz.conclusion with
   | none => false
   | some (conclCoeffs, conclConst) =>
       let pairs := cz.premises.zip cz.multipliers
       (collapseZ (diffMapZ pairs conclCoeffs)).all (fun p => isZeroZ p.2) &&
       leZ (combConstZ pairs) (addZ conclConst sc.slack))

/-! ## The certificate transcribed from the emitted JSON fixtures.

`demoRealCert` is the literal of `farkas_anchor/valid_cert.json`; `demoTamperedCert`
of `farkas_anchor/tampered_cert.json` (conclusion constant 3 -> 4). -/

/-- The certificate emitted by AY's LP bound path for the on-disk
    `optimization-small.opb` (`min x1+2x2+3x3+4x4 s.t. x1+x2+x3+x4>=2, x1+x3>=1,
    x2+x4>=1`; real exact LP floor 3). Transcribed verbatim from `valid_cert.json`. -/
def demoRealCert : SCertZ :=
  { base :=
      { premises :=
          [ -- structural row 0:  x0+x1+x2+x3 >= 2  (multiplier 1)
            { coeffs := [("0", (1, 1)), ("1", (1, 1)), ("2", (1, 1)), ("3", (1, 1))],
              kind := Kind.ge, const := (2, 1) },
            -- structural row 1:  x0+x2 >= 1  (multiplier 0)
            { coeffs := [("0", (1, 1)), ("2", (1, 1))], kind := Kind.ge, const := (1, 1) },
            -- structural row 2:  x1+x3 >= 1  (multiplier 1)
            { coeffs := [("1", (1, 1)), ("3", (1, 1))], kind := Kind.ge, const := (1, 1) },
            -- box upper-bound rows  -x_v >= -1  (i.e. x_v <= 1), multiplier 0
            { coeffs := [("0", (-1, 1))], kind := Kind.ge, const := (-1, 1) },
            { coeffs := [("1", (-1, 1))], kind := Kind.ge, const := (-1, 1) },
            { coeffs := [("2", (-1, 1))], kind := Kind.ge, const := (-1, 1) },
            { coeffs := [("3", (-1, 1))], kind := Kind.ge, const := (-1, 1) },
            -- lower-bound rows  x_v >= 0  (multipliers 0,0,2,2)
            { coeffs := [("0", (1, 1))], kind := Kind.ge, const := (0, 1) },
            { coeffs := [("1", (1, 1))], kind := Kind.ge, const := (0, 1) },
            { coeffs := [("2", (1, 1))], kind := Kind.ge, const := (0, 1) },
            { coeffs := [("3", (1, 1))], kind := Kind.ge, const := (0, 1) } ],
        multipliers :=
          [(1, 1), (0, 1), (1, 1), (0, 1), (0, 1), (0, 1), (0, 1),
           (0, 1), (0, 1), (2, 1), (2, 1)],
        conclusion :=
          { coeffs := [("0", (1, 1)), ("1", (2, 1)), ("2", (3, 1)), ("3", (4, 1))],
            kind := Kind.ge, const := (3, 1) } },
    slack  := (0, 1),
    margin := (1, 1) }

/-- The TAMPERED cert: identical, but the conclusion lower bound is inflated from
    `>= 3` to `>= 4` (a too-HIGH lower bound — the soundness-critical failure).
    Transcribed verbatim from `tampered_cert.json`. -/
def demoTamperedCert : SCertZ :=
  { demoRealCert with
    base := { demoRealCert.base with
      conclusion :=
        { coeffs := [("0", (1, 1)), ("1", (2, 1)), ("2", (3, 1)), ("3", (4, 1))],
          kind := Kind.ge, const := (4, 1) } } }

/-! ## The kernel anchor: Lean agrees with Rust `check_slack` on the fixture.

Both are proven by `decide` (pure integer cross-multiplication in the kernel —
not `native_decide`). -/

/-- Kernel anchor (valid): the emitted certificate is accepted, matching Rust
    `check_slack(valid) = true`. -/
theorem demoRealCert_accepts : checkSlackEntailmentZ demoRealCert = true := by
  decide

/-- Kernel anchor (tampered): the inflated certificate is rejected, matching Rust
    `check_slack(tampered) = false`. The soundness-critical direction. -/
theorem demoTamperedCert_rejects : checkSlackEntailmentZ demoTamperedCert = false := by
  decide

/-! ## A second checker fixture.

Reducing `demoSlackCert` to `true` checks this executable procedure on one more
input; it does not extend that observation into a general theorem. -/

/-- Demo leaf: x <= 1, y <= 2 |- x + y <= 4, slack 1/4, margin 1/2. -/
def demoSlackCert : SCertZ :=
  { base :=
      { premises :=
          [ { coeffs := [("x", (1, 1))], kind := Kind.le, const := (1, 1) },
            { coeffs := [("y", (1, 1))], kind := Kind.le, const := (2, 1) } ],
        multipliers := [(1, 1), (1, 1)],
        conclusion :=
          { coeffs := [("x", (1, 1)), ("y", (1, 1))], kind := Kind.le, const := (4, 1) } },
    slack  := (1, 4),
    margin := (1, 2) }

/-- The ported checker reduces the canonical fixture to `true`. -/
theorem demoSlackCert_checks : checkSlackEntailmentZ demoSlackCert = true := by
  decide

/-! ## Trust-base check. Each anchor must depend only on the standard kernel axioms
       (a subset of `[propext, Classical.choice, Quot.sound]`), no `sorryAx`. -/

#print axioms demoRealCert_accepts
#print axioms demoTamperedCert_rejects
#print axioms demoSlackCert_checks

end FarkasAnchor
