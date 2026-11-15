# `veripb-core-proved` — design note for the proved checker kernel

Imported reference: the measurements below describe the maintained cohort
before AY integration. They do not qualify a current AY build. The retained
strict proof gate must recheck the artifacts and current toolchain identities.
Code examples use current named Targo lanes; they do not claim to reproduce
the historical standalone-verifier counts. The development-only measurement
harness is excluded from the public stock-Rust source snapshot.

**Status:** slices 1 and 2 landed. Every theorem named below is
machine-checked. §5 is the "not proved" ledger, and what it claims to be
exhaustive about is **categories**: every part of the checker the kernel does
not model, and every measurement this project used to make and can no longer
make. It is deliberately *not* a list of the stand-down literals
`--kernel-verify` can print — that vocabulary moves with the bridge, so §7.3
gives the command that derives the current set instead of freezing a copy
here, §7.3 groups the per-step reasons and §7.4's boundary note 2 the
run-level ones. §5 item 5 names the subset that bears on scope and says why
each unexercised literal is kept.

Slice 1: the rule kernel (ADD/MULTIPLY/DIVIDE/SATURATE/LITERAL/weaken/negate)
with i64 width guards. Slice 2 (§7): RUP propagation soundness as a checked
trail certificate, proved normalization, proof-sequence composition down to
`checker_sound`, the SAT-verdict leg, and the `--kernel-verify` wiring that
runs all of it inside the live checker.

**Artifacts**

| file | what it is | how to verify |
|---|---|---|
| `veripb-core-proved/clean/veripb_kernel.lean` | canonical, commented Clean source: semantics + every theorem | `clean check veripb-core-proved/clean/veripb_kernel.lean` → `912 passed, 0 failed` |
| `veripb-core-proved/src/trust_surface.rs` | the same kernel as a `clean { … }` parser island, plus Rust `ensures … by …` clauses | `compiler_consumer --edition 2021 --crate-type lib veripb-core-proved/src/trust_surface.rs` → `912 declaration(s) registered` (with `-O` — the citation lane verifies fully-optimized MIR), every island obligation proved at the `island_proved_obligations` pin (45 under the merged toolchain — the walker's count, not a lost proof; every citation discharges), 20 citations kernel-discharged (four at the real `i64` width, the four rule-guard contracts including the complete two-sided width guard as one conjunction, and three overflow-checked-arithmetic contracts on `Option<i128>`-returning leaves — see the ledger in §4.1) |
| `veripb-core-proved/src/lib.rs` | the executable Rust kernel: one function per rule, each gated by the guards its Clean theorem requires | `targo --unverified test --release -p veripb-core-proved` |
| `veripb-core-proved/src/{normalize,rup,db}.rs` | slice-2 Rust images: proved normalization, RUP trail replay, database-evolution driver | same |
| `veripb-checker/src/kernel_bridge.rs` | the `--kernel-verify` wiring: live checker cross-checked against the kernel | `targo --unverified test --release --test kernel_verify` → verdict-neutral on the full corpus |
| `veripb-core-proved/tests/` | width-guard regressions + island/`.lean` drift guard | `targo --unverified test --release -p veripb-core-proved` |

> **Verification status** (2026-08-24, aarch64-apple-darwin; both toolchains
> are per-machine builds):
>
> `clean check` → `Checked 912 declarations` / `912 passed, 0 failed`.
> `compiler_consumer` kernel-checks all **772** island declarations, proves **every island obligation** (the `island_proved_obligations` pin)
> `ensures` obligations across 11 cited functions (0 failed, 0 unknown,
> 0 timed out, 0 runtime-checked) and kernel-discharges all **20** citations
> over 10 distinct theorems.
>
> These numbers are gated, not hand-maintained. `scripts/verify-proofs.sh`
> derives each one from the tool output and checks it against the pin file
> `veripb-core-proved/clean/proved-core-expected.txt`. The *quoted* figures
> in this file, in `README.md` and in `CHANGELOG.md` are separately checked
> against the sources by
> `the_public_declaration_and_citation_counts_are_the_measured_ones`
> (`veripb-core-proved/tests/island_sync.rs`), which needs no toolchain — so
> a kernel that grows without a doc update turns a plain `targo --unverified test` red.
> The 29 obligations are the one figure only compiler_consumer can produce, so they are
> pinned in `proved-core-expected.txt` rather than here.
>
> *Portability note.* On an older stage the slice-1 kernel reported 3
> elaboration failures at the last bare-`Or.elim` sites
> (`le_of_mul_le_min`, `entails_divide`, `entails_of_negation_unsat`).
> They now use the `@Or.rec` form §6 prescribes — proof terms only, every
> theorem signature byte-identical. Whether `Or.elim` elaborates is
> version-dependent; the kernel avoids it everywhere.

The historical measurements used managed Clean and a developer Trust stage2.
In AY, `scripts/verify-proofs.sh` selects managed `clean` and `compiler_consumer` on PATH,
unless explicit `CLEAN_BIN`/`TRUSTC_BIN` images are supplied for comparison.
The expected identities remain pinned; strict mode refuses drift.

---

## 1. The representation, and why

### 1.1 Constraints

```
Lit        = { var : Nat, negated : Bool }
Term       = { coeff : Int, lit : Lit }
Constraint = { terms : List Term, degree : Int }        -- meaning  Σ cᵢ·lᵢ ≥ d
Assignment = Nat → Bool
```

Three decisions worth defending.

**(a) Coefficients and degrees are `Int` — arbitrary precision — not a fixed
width.** This is the direct response to bug C. Bug C is not a bug in the
*rule*; the rule (`weaken` decrements the degree) is fine. It is a bug in the
claim that `i64` arithmetic *implements* the rule. Two ways to make a proof
system robust against that:

1. prove the rules over `BitVec 64` with explicit no-overflow side conditions,
   or
2. prove the rules over `Int`, and require every machine value crossing into
   the kernel to be *certified equal* to the mathematical one.

We take (2). The reason is that (1) makes every rule lemma carry width
hypotheses that are re-proved at every step and are easy to state slightly
wrong — precisely the failure mode we are trying to eliminate. Under (2) the
soundness lemmas are about the mathematics, and there is exactly **one** place
where a width can be got wrong: the guard. The guard is small, decidable, and
checked at run time.

Concretely, the Clean side has

```
def i64Max  : Int := 9223372036854775807
def i64Min  : Int := Int.neg 9223372036854775808
def InI64   (x : Int) : Prop := And (Int.le i64Min x) (Int.le x i64Max)
def fitsI64 (x : Int) : Bool := …            -- decides InI64
def eqOkB   (x y : Int) : Bool := …          -- decides x = y, via Int.ble twice

theorem inI64_of_fitsI64 (x : Int) : fitsI64 x = true → InI64 x
theorem eq_of_eqOkB (x y : Int) : eqOkB x y = true → x = y
```

and the Rust side (`veripb_core_proved::guard`) computes the same predicates in
`i128`, which holds every sum and product of two `i64` values exactly. A
wrapped `i64` differs from the true value, so `eq_ok` rejects it; the rule then
returns `Err(GuardError::DegreeOverflow)` and produces nothing. Compare
`ctrl_eq_guard_rejects_wrap` in the `.lean` (kernel-evaluated) with
`eq_ok_rejects_a_wrapped_value` in `tests/width_guards.rs` (executed): both pin
`i64::MIN - 1` wrapping to `i64::MAX`.

The two rules whose degree arithmetic bug C actually corrupts have explicit
guarded forms in the kernel:

```
theorem entails_add_checked    …  (hs : eqOkB s (c1.degree + c2.degree) = true)
                                  (hfit : fitsI64 s = true) …
     : And (InI64 s) (Entails F { terms := c1.terms ++ c2.terms, degree := s })

theorem entails_weaken_checked …  (hr : eqOkB (r + w) c.degree = true)
                                  (hw : Int.le 0 w) (hfit : fitsI64 r = true) …
     : And (InI64 r) (Entails F (weakenC r c))
```

`entails_weaken_checked` is bug C's exact shape: `r` is whatever the machine
subtraction produced, and it is admitted only if `r + w = d` *over `Int`*.

**(b) `terms` is a list, i.e. a multiset — nothing merges like terms, and
nothing cancels `x` against `¬x`.** `ADD` is literally list append. This makes
the additivity lemma (`evalTerms_append`) trivial and true, and it moves
normalization — which is where real checkers introduce arithmetic — into a
separate, explicitly out-of-scope layer (§5).

**(c) Assignments are total (`Nat → Bool`), not partial.** Partial assignments
are needed for propagation/RUP search, not for the *semantics* of entailment.
Keeping them total means `sat`/`Holds` is a plain inequality with no
three-valued algebra, and the RUP rule is stated as a reduction to `Unsat`
(§3.6) rather than as a model of the propagation loop.

### 1.2 Semantics

```
def litVal    (a) (l : Lit)  : Bool := if l.negated then ¬(a l.var) else a l.var
def evalTerms (a) (ts)       : Int  := Σ over terms whose literal is true of coeff
def Holds     (a) (c)        : Prop := Int.le c.degree (evalTerms a c.terms)
def HoldsAll  (a) (F)        : Prop := conjunction of Holds over F
def Entails   (F) (c)        : Prop := ∀ a, HoldsAll a F → Holds a c
def Unsat     (F)            : Prop := ∀ a, HoldsAll a F → False
```

Note `Holds` and `HoldsAll` are `Prop`, not `Bool`: there is no `decide` in the
soundness path at all, so no dependence on `Decidable` instance reduction. The
`Bool`-valued images (`fitsI64`, `eqOkB`, `coeffsDominatedB`, `allNonnegB`) are
exactly the checks the *checker* runs, each paired with a lemma that lifts
`… = true` to the corresponding `Prop`.

The claim is stronger than "the soundness path", and it is checkable in one
line:

```bash
grep -cE '(:=|\() *by ' veripb-core-proved/clean/veripb_kernel.lean   # => 0
```

The whole file is explicit proof terms — no tactic invocation anywhere,
controls included. A control briefly used `(by decide)` for `Nat.le 1 3` and
`Int.lt 0 2`; those are now the named witnesses `nat_le_1_3` and
`int_lt_0_2`. Nothing was unsound about the tactic; the point is that what
the kernel must *reduce* in order to accept this file is exactly what this
section advertises.

Non-vacuity is pinned by kernel-evaluated controls (`ctrl_eval_true`,
`ctrl_litAxiom_true/false`, `ctrl_cap_hi/lo`, `ctrl_fits_*`, `ctrl_eq_guard_*`),
each mirrored by a Rust test. Without them, "the rules are sound" could be true
of a semantics that computes nothing.

---

## 2. What the top-level theorem is

A PB proof checker is sound iff, whenever it accepts, the claimed conclusion
holds. For refutations that is:

```
theorem unsat_of_entails_contradiction (F : List Constraint)
    (h : Entails F contradiction) : Unsat F
```

with `contradiction = { terms := [], degree := 1 }` (i.e. `0 ≥ 1`). A checker
run is a sequence of rule applications; each rule lemma below preserves
`Entails F ·`, so a derivation ending in `contradiction` yields `Unsat F`.

The composition of the steps ("a sequence of sound steps is sound") was out
of scope for slice 1 and is now formalized: see `DStep` / `DbOk` /
`checker_sound` in §7.

---

## 3. The rule-soundness lemmas, exactly as stated

All are in `namespace VeriPbCore`. All are proved with zero `sorry`
(`sorry` is a Clean build error, so this is enforced, not asserted).

### 3.1 ADD

```
def addC (c1 c2 : Constraint) : Constraint :=
  { terms := c1.terms ++ c2.terms, degree := c1.degree + c2.degree }

theorem entails_add (F : List Constraint) (c1 c2 : Constraint)
    (h1 : Entails F c1) (h2 : Entails F c2) : Entails F (addC c1 c2)
```

Supporting: `evalTerms_append : evalTerms a (xs ++ ys) = evalTerms a xs + evalTerms a ys`
(proved by `List.rec` with a `Bool.rec` step, the idiom Clean's `rw`/`simp`
cannot yet handle on a `match`-in-`def`), and `add_le_add`.

### 3.2 MULTIPLY

```
def scaleTerms (k : Int) : List Term → List Term          -- multiply each coeff
def scaleC (k : Int) (c : Constraint) : Constraint :=
  { terms := scaleTerms k c.terms, degree := k * c.degree }

theorem entails_multiply (F) (c) (k : Int)
    (hk : Int.le 0 k) (h : Entails F c) : Entails F (scaleC k c)
```

Supporting: `evalTerms_scale : evalTerms a (scaleTerms k ts) = k * evalTerms a ts`.
The lemma needs only `0 ≤ k`; the Rust `multiply` additionally demands `k > 0`
so the rule is non-degenerate (`k = 0` derives `0 ≥ 0`, sound but useless, and
accepting it would let a proof "use" a step that proves nothing).

### 3.3 DIVIDE — where rounding is proved, not assumed

DIVIDE is the rule real checkers get wrong, so this is the one designed most
carefully. Clean's `Int` library ships **no ceiling-division lemmas** (it has
`Int.div`, `Int.div_add_mod`, `Int.mod_lt` and essentially nothing else), so
the general rule quantifies over an *arbitrary* quotient map `f : Int → Int`
and the two defining properties of `ceil(·/k)` appear as *hypotheses that the
checker discharges by decidable comparison*:

```
def mapCoeff (f : Int → Int) : List Term → List Term
def divC (f : Int → Int) (c : Constraint) : Constraint :=
  { terms := mapCoeff f c.terms, degree := f c.degree }

def CoeffsDominated (k : Int) (f : Int → Int) : List Term → Prop
    -- pointwise:  cᵢ ≤ k * f cᵢ
def coeffsDominatedB (k) (f) : List Term → Bool          -- decides it
theorem coeffsDominated_of_check : coeffsDominatedB k f ts = true → CoeffsDominated k f ts

theorem entails_divide (F) (c) (k : Int) (f : Int → Int)
    (hk   : Int.le 0 k)
    (hdom : CoeffsDominated k f c.terms)              -- f overshoots: cᵢ ≤ k·f cᵢ
    (hmin : Int.lt (k * f c.degree) (c.degree + k))   -- f is minimal at the degree
    (h    : Entails F c) : Entails F (divC f c)
```

For `k > 0`, `hdom` bounds `f` from below at every coefficient
(`f(c_i) >= ceil(c_i/k)`) and `hmin` bounds it from above at the degree
(`f(d) <= ceil(d/k)`): the hypotheses reject exactly the unsound deviations —
a too-small coefficient quotient or a too-large degree quotient — and admit
any sound weakening.

**The concrete map is proved too, and it is what licenses the executable
rule.** The abstract form above is kept because the checker computes
quotients at *machine width*, where re-checking is what catches a wrapped or
hard-coded quotient (upstream defects C and D). But a re-check only licenses
an acceptance if it pins the value, so `veripb_core_proved::divide_with`
checks **both** bounds at **every** coefficient and at the degree, and

```
theorem ceilQuotient_unique (x q : Int) (k : Nat) (hk : Nat.le 1 k)
    (hub  : Int.le x (Int.mul (Int.ofNat k) q))
    (hmin : Int.lt (Int.mul (Int.ofNat k) q) (Int.add x (Int.ofNat k)))
    : q = intCeilDiv x k
```

proves that anything passing both **is** `intCeilDiv x k`. So an accepted
output equals `divC (fun x => intCeilDiv x k) c` whatever the machine
`ceil_div` computed, and is entailed by `entails_divide_concrete` — DIVIDE
with no side conditions left for a checker to discharge, over a self-contained
fuel-based Euclidean theory (`natDivMod`/`dmSpec`, `natCeilDiv`, `intCeilDiv`,
`intCeilDiv_ub`, `intCeilDiv_min`; §5 item 3). Before the minimality bound was
applied per coefficient, an *overshooting* map still satisfied `c_i ≤ k·q_i`
everywhere, so the accepted output was only known to satisfy
`entails_divide`'s hypotheses — not to be the concrete ceiling cut. Sampled
agreement between `ceil_div` and `intCeilDiv` (`tests/width_guards.rs`) is a
regression test on top of that, not the licensing argument.

The load-bearing arithmetic is isolated in

```
theorem le_of_mul_le_min (k Q q d : Int)
    (hk : Int.le 0 k) (hQ : Int.le d (k * Q)) (hmin : Int.lt (k * q) (d + k))
    : Int.le q Q
```

which is *why ceiling and not floor* is the sound rounding: if `q` were the
floor, `hmin` would fail and no constraint would be produced.

Two consequences that matter for the audit:

* The side conditions are checked over `Int` (unbounded). A **wrapped** machine
  quotient cannot satisfy them, so bug C cannot reach DIVIDE through the
  variable-form path.
* A **hard-coded** quotient cannot satisfy them either. Bug D is the
  oversized-divisor fallback that hard-codes `ceil(A/d) = 1`; `hdom`/`hmin` are
  precisely the inequalities such a value fails. `tests/width_guards.rs`
  exercises the oversized-divisor case and shows the guarded implementation
  computes `1` *and proves it*.

### 3.4 SATURATE

```
def capCoeff (d c : Int) : Int := if Int.ble c d then c else d       -- min c d
def satTerms (d : Int) : List Term → List Term
def satC (c : Constraint) : Constraint :=
  { terms := satTerms c.degree c.terms, degree := c.degree }

def AllNonneg : List Term → Prop                       -- 0 ≤ cᵢ, pointwise
def allNonnegB : List Term → Bool                      -- decides it
theorem allNonneg_of_check : allNonnegB ts = true → AllNonneg ts

theorem entails_saturate (F) (c)
    (hd : Int.le 0 c.degree) (hn : AllNonneg c.terms) (h : Entails F c)
    : Entails F (satC c)
```

Saturation is **unsound without normalization** (a negative coefficient breaks
it), so both side conditions are hypotheses and both are decidable; Rust's
`saturate` returns `Err(NotNormalized)` rather than saturating.

The proof is factored so that a future re-implementation of the capping
function only has to re-establish one statement:

```
def SaturateKey : Prop :=
  ∀ a d ts, Int.le 0 d → AllNonneg ts →
    Int.le (capCoeff d (evalTerms a ts)) (evalTerms a (satTerms d ts))

theorem entails_saturate_of_key : SaturateKey → …      -- the reduction
theorem saturate_key : SaturateKey                     -- discharged
```

### 3.5 LITERAL

```
def litAxiom (l : Lit) : Constraint :=
  { terms := [{coeff := 1, lit := l}, {coeff := 1, lit := negLit l}], degree := 1 }

theorem entails_literal (F : List Constraint) (l : Lit) : Entails F (litAxiom l)
```

Note the hypothesis-free `F`: the axiom is entailed by *every* formula.
Supporting: `litVal_negLit : litVal a (negLit l) = ¬ litVal a l` and
`evalTerms_litAxiom : evalTerms a (litAxiom l).terms = 1` (which is why the
constraint is tight, not merely satisfiable).

### 3.6 RUP — stated as a reduction, not as a propagation model

Unit propagation is a search procedure; its *soundness* is not about the search
at all. What must be true is: if the formula extended with the negation of `C`
is unsatisfiable, then the formula entails `C`. That is what is proved:

```
def negTerms : List Term → List Term                   -- flip every literal
def coeffSum : List Term → Int
def negC (c : Constraint) (nd : Int) : Constraint :=
  { terms := negTerms c.terms, degree := nd }

theorem evalTerms_negTerms :
    evalTerms a (negTerms ts) + evalTerms a ts = coeffSum ts

theorem entails_of_negation_unsat (F) (c) (nd : Int)
    (hnd : nd + c.degree = coeffSum c.terms + 1)       -- checked witness equation
    (hU  : Unsat (negC c nd :: F)) : Entails F c
```

`¬(Σ cᵢ lᵢ ≥ d)` is `Σ cᵢ ¬lᵢ ≥ (Σ cᵢ) − d + 1`. The negated degree is supplied
by the checker as `nd` with the *witness equation* `nd + d = Σcᵢ + 1` — stated
with `+` only, so no subtraction appears in the proof obligation, and a wrapped
`nd` cannot satisfy it. Rust's `negate` computes `nd` in `i128` and narrows
through the guard.

The propagation engine's job is to establish `Unsat (negC c nd :: F)`; that
engine is out of scope (§5).

### 3.7 Degree weakening and the top level

```
theorem entails_weaken_degree (F) (c) (d : Int)
    (hd : Int.le d c.degree) (h : Entails F c) : Entails F (weakenC d c)

theorem unsat_of_entails_contradiction (F) (h : Entails F contradiction) : Unsat F
```

---

## 4. How Rust is tied to Clean

Three distinct bindings, of decreasing strength. Being explicit about which is
which is the point.

**(1) `ensures … by …` — kernel discharge.** In `src/trust_surface.rs`:

```rust
clean {
    …the entire kernel…
    theorem capcoeff_le_self : forall (c : UInt64) (d : UInt64),
        Nat.le (UInt64.toNat (if c < d then c else d)) (UInt64.toNat c) := ...
```

The statement is deliberately phrased over the `ite`/`Decidable` term the
compiler_consumer Select mint produces (compiler_consumer >= 2026-07-26), so this single theorem
discharges both the `result`-form and call-site-form citations by
delta-reduction.

compiler_consumer reports `29 proved, 0 failed, 0 unknown, 0 timed out,
0 runtime-checked` across the eleven cited functions, plus one
`citation … kernel-discharges this postcondition statement … with a clean
certification audit` note per citation. The per-function tally is the ledger
in §4.1.

The discharge is not vacuous, and this has been checked on every clause
shape in use. Changing `cap_coeff_le_self_u64`'s clause to `<= d` (which the
cited theorem does not prove) makes compiler_consumer emit `citation capcoeff_le_self
failed the strict Clean statement/certification audit` and abort. The same
holds for the two newest and most complex clauses: weakening
`cap_coeff_i64`'s disjunct `(result >= degree || result >= coeff)` to a
conjunction, or flipping `cap_coeff_i64_le_capcoeff`'s consequent from
`result >= degree` to `result >= coeff`, each produces
`Trust strict verification failed … obligation(s) were not fully verified`
plus the failed-audit error. Verified locally.

The same was done for the two rule-guard contracts on 2026-08-24, and there
the *removal* case separates them from everything above. Changing
`fits_i64_lower_wide`'s body from `x >= -9223372036854775808` to
`x > -9223372036854775808` — one character — makes compiler_consumer emit
`citation guard_fits_lower_exact failed the strict Clean
statement/certification audit` and abort; changing `weaken_factor_nonneg`'s
`w >= 0` to `w >= 1` does the same for `weaken_factor_sign_exact`. And
*deleting* either `by` clause leaves `Trust strict verification failed …
2 obligation(s) were not fully verified`, because the native verifier returns
`Unknown` for a conjunction of disjunctions over `result` at these carriers
and the kernel discharge is the only thing proving it. That is the property
the nine `min` citations do not have: for them, deletion leaves compiler_consumer at
exit 0 with the obligation total unchanged.

`cap_coeff_le_self_u64` is the machine image of `VeriPbCore.capCoeff_le_self` —
the fact that saturation never *raises* a coefficient.

**(2) The island holds the whole kernel.** `compiler_consumer` reports
`Clean island kernel-checked: 912 declaration(s) registered`, listing every
`VeriPbCore.*` name — and the island is now *exactly* the comment-stripped
`.lean`, with no separately-maintained addendum, so that count and
`clean check`'s are the same number by construction. So the semantics and
every rule lemma are kernel-checked whenever
`src/trust_surface.rs` is compiled with compiler_consumer. The file is a genuine module
of the crate (behind the off-by-default `trust-surface` feature, so a default
build never parses it), but the check itself is a standalone single-file
compiler_consumer compile — no `targo` build of the crate runs it today.

**(3) A documented, test-enforced correspondence for everything else.**
`src/lib.rs` carries a Rust↔Clean table in its module docs, and each rule
function's doc names the theorem whose hypotheses its guards discharge.
`tests/island_sync.rs` fails if the island and `clean/veripb_kernel.lean`
drift apart.

### 4.1 The honest limit of the tie

**Signed integers are now in the fragment.** The compiler_consumer E6/E9 lane was
extended (2026-08-23) to admit `i8`-`i64` alongside `bool`/`u8`-`u64`, over a
two's-complement `BitVec 64` carrier whose comparisons go through the order
key `key64 v = Nat.xor (BitVec.toNat v) 2^63` — signed order mapped
bijectively onto `Nat` order, deliberately *not* Clean's unsigned `BitVec`
order, which would give a program's signed `<=` an unsigned meaning at
`i64::MIN`. The consequence for this crate is the one that matters:

```rust
pub fn cap_coeff_i64(degree: i64, coeff: i64) -> i64
    ensures result <= coeff && result <= degree && (result >= degree || result >= coeff)
        by capcoeff_i64_min_full
{ if coeff <= degree { coeff } else { degree } }
```

has the *token-identical body* of `veripb_core_proved::cap_coeff`, the
function the checker actually runs (the two differ only in line breaks) — so
a soundness-critical kernel function of the real crate, at its real width,
carries a compiler-checked contract instead of a `u64` stand-in. That
correspondence is itself pinned, by
`the_i64_cap_functions_have_the_body_of_the_real_cap_coeff` in
`tests/island_sync.rs`; before that test existed, editing `cap_coeff`'s body
left every test green while silently falsifying this paragraph.

**Why three conjuncts and not two.** `result <= coeff` and `result <= degree`
are both *upper* bounds, and a `cap_coeff` returning `i64::MIN` satisfies
both — while making SATURATE unsound, since from `Σ cᵢ·lᵢ ≥ d` it would
derive `0 ≥ d`. The direction saturation's soundness proof actually consumes
is the *lower* bound `le_capCoeff : d ≤ x → d ≤ capCoeff d x`
(`veripb_kernel.lean:664`, used by `entails_saturate_of_key` at `:703`), and
for a long time it was cited at no width. The third conjunct supplies it: the
three together pin `result == min(coeff, degree)` exactly. The lemma is also
cited literally, on its own function:

```rust
pub fn cap_coeff_i64_le_capcoeff(degree: i64, coeff: i64) -> i64
    ensures !(degree <= coeff) || result >= degree by capcoeff_i64_le_capcoeff
{ if coeff <= degree { coeff } else { degree } }
```

**Two of the eleven are not about `min` at all.** As of 2026-08-24 the
guard layer carries contracts too — the layer §1.1 names as the one place a
width can be got wrong:

```rust
pub fn weaken_factor_nonneg(w: i64) -> bool
    ensures (!result || w >= 0) && (result || w < 0) by weaken_factor_sign_exact
{ w >= 0 }

pub fn fits_i64_lower_wide(x: i128) -> bool
    ensures (!result || x >= -9223372036854775808) && (result || x < -9223372036854775808)
        by guard_fits_lower_exact
{ x >= -9223372036854775808 }
```

Each is a *complete characterisation* of one decidable test, in both
directions, so neither an off-by-one bound nor a flipped comparison can
satisfy it; each is stated at the width the checker runs the test at (`i64`
for the factor sign, `i128` — `Wide` — for the width guard); and both are
**load-bearing**, which none of the nine `min` citations are. Deleting
`by capcoeff_i64_min_full` leaves compiler_consumer green because the solver re-proves
that postcondition unaided; deleting either of these two turns compiler_consumer red,
because the native verifier reports these clauses `Unknown` and the kernel
discharge is the only thing proving them.

What they do **not** establish: nothing about `add`, `multiply`, `divide`,
`weaken_degree`, `negate` or `mir` themselves. Those bodies (a `Vec` walk, a
`Result` return) are far outside the E6 admission fragment and no `ensures`
can reach them. The contracts say the *tests* those rules gate on decide
their side conditions exactly; the step to rule soundness is
`entails_weaken_checked` / `entails_multiply` / `entails_add_checked`, proved
in the kernel, and the step from the twin to the function the rule calls is
`the_rule_guard_twins_have_the_predicate_of_the_real_guards` in
`tests/island_sync.rs`, a text-and-execution pin, not a compiler check.

All of `fits_i64` is cited — both halves separately, and the conjunction the
real body computes as one contract — but for most of this crate's life only
the *lower* half could be, and the reason was a measured limit of the island:
a numeral written in a `clean { }` island was definitionally equal to the
literal compiler_consumer mints only when its value was at least `2^64`, or was spelled
`Nat.zero`. `i64::MIN` at 128 bits is `2^128 - 2^63` and cleared that;
`i64::MAX` is `9223372036854775807` and did not, so
`BitVec.ofNat 128 9223372036854775807` was refused and no theorem over it
could discharge anything — the value, not the spelling, decided. The cause
was the Clean kernel's u64-capped `BitVec.ofNat` reducer parking on
multi-limb and `OfNat`-wrapped operands; it was lifted 2026-08-25
(first-party/clean `05f6b0b3d`: multi-limb read, `OfNat` numeral peel,
multi-limb emit — pure evaluation of `ofNat`'s own `mod 2^w` definition), and
in the same toolchain step compiler_consumer's citation lane learned to recognize and
mint boolean-conjunction bodies (`cmpA && cmpB` as `Bool.and` of the two
comparison mints, keyed off the short-circuit diamond's arm arrangement,
probes f45–f48 in the compiler's fragment matrix). Those two toolchain
changes are what the three newest rows below ride on. The conjunction
citation is mutation-verified in all three directions: an off-by-one in
either bound of the body turns the build red, `&&` mutated to `||` turns it
red, and deleting the `by guard_fits_exact` turns it red (the native
verifier reports the clause `Unknown` at `i128`, so the kernel discharge is
the only proof).

**The citation ledger.** The headline count is twenty discharge notes over
nineteen distinct theorems, and a reader should not read that as sixteen
soundness-critical contracts. Exactly what each one covers:

| function | width | fact | weight |
|---|---|---|---|
| `cap_coeff_i64` | **i64, real body** | `result == min(coeff, degree)`, all three conjuncts | soundness-critical |
| `cap_coeff_i64_le_capcoeff` | **i64, real body** | the image of `le_capCoeff` — the cap never falls below the degree | soundness-critical |
| `cap_coeff_i64_le_coeff` | **i64, real body** | `capCoeff_le_self` | soundness-critical |
| `cap_coeff_i64_le_degree` | **i64, real body** | `capCoeff_le_degree` | soundness-critical |
| `cap_coeff_le_self_u64` | u64 stand-in | same fact, `u64` carrier | lane coverage |
| `cap_coeff_call_site` | u64 stand-in | the clause names the *call*, not `result` — exercises the definitional-mention lane | lane coverage |
| `cap_coeff_le_other_u64` | u64 stand-in | `capCoeff_le_degree` | lane coverage |
| `cap_coeff_bounds_u64` | u64 stand-in | conjunction-splitting discharge lane | lane coverage |
| `saturated_degree` | u64 | `d <= d` on the identity function | **vacuous** — a reflexivity control, kept because it is the negative-control fixture of `scripts/verify-proofs.sh`'s citation gate |
| `fits_i64_lower_wide` | **i128, the guard's real width** | `guard::fits_i64`'s lower conjunct accepts exactly `x >= i64::MIN` — the direction bug C's WEAKEN underflow runs in | soundness-critical, **load-bearing** |
| `fits_i64_upper_wide` | **i128, the guard's real width** | the upper conjunct accepts exactly `x <= i64::MAX` — the direction the overflow family runs in; the first citation whose bound sits below `2^64` | soundness-critical, **load-bearing** |
| `fits_i64_wide` | **i128, the guard's real width** | the COMPLETE two-sided guard as the one conjunction the real `guard::fits_i64` body computes (`x >= i64::MIN && x <= i64::MAX`), by `guard_fits_exact` — `decide_and_le_exact` at `key128` | soundness-critical, **load-bearing** |
| `weaken_factor_nonneg` | **i64, real width** | `weaken_degree`'s factor test decides `0 <= w` exactly — the hypothesis of `entails_weaken_checked` (and of `entails_multiply`, whose own `k > 0` check is stricter and implies it) | soundness-critical, **load-bearing** |
| `cadd_wide` | **i128 → Option, the exact-arithmetic width** | `checked_add` commutes (`checkedAdd128_comm`) — an op-discriminating algebraic fact about the whole Option-valued result; a body swapped to `checked_sub` turns the build red | first Option-valued citation; op-pinned, not a full characterization |
| `csub_wide` | **i128 → Option** | the diagonal `csub_wide(a, a) != None` (`checkedSub128_self_isSome`) — true for sub, and bound to sub's model: a body swapped to `checked_add` turns the build red even though the claim would still be true of it | op-pinned, not a full characterization |
| `cmul_wide` | **i128 → Option** | `checked_mul` commutes (`checkedMul128_comm`) | op-pinned, not a full characterization |
| `narrow_wide` | **i128 → Option<i64>, the real narrowing shape** | the FULL functional equation `result == narrowWide(x)` — `Some` of the truncation exactly when the guard holds, `None` exactly when it does not. Uncited: it closes by delta-defeq against the island definition | soundness-critical, **the first consumer shape** |
| **`cap_coeff_wide`** | **i128, THE REAL FUNCTION** | all three SATURATE conjuncts (`capcoeff_i128_min_full`, newly proved as the `key128` restatement of the `i64` theorem) — the cap never exceeds either input and never falls below both. Mutation-verified: swapping the arms (making it a max) and collapsing both arms to `degree` (the under-capping shape the third conjunct exists to exclude) each turn the build red | soundness-critical, **on the real body**; the first real-function contract that is both kernel-certified AND natively proved |
| **`guard::eq_ok`** | **(i64, i128) → bool, THE REAL FUNCTION** | the body IS the island definition `eqOkW` — a comparison across two widths through a SIGN-extending cast, modelled as one (`sextWide v = ofInt128 (toInt64 v)`, exact on all 2^64 inputs). The only UNCITED contract: definitional equality against the E6-admitted body is the whole proof, and no theorem states that. Mutation-verified: `!=`, and comparing the TRUNCATION (`machine == truth as Coeff` — the wrap bug this guard exists to catch) each turn the build red | soundness-critical, **on the real body** |
| **`guard::fits_i64`** | **i128 → bool, THE REAL FUNCTION** | the complete two-sided width predicate (`guard_fits_exact`), carried on `lib.rs` itself. Mutation-verified: an off-by-one on either bound turns the build red | soundness-critical, **on the real body** |
| **`guard::narrow`** | **i128 → Option<i64>, THE REAL FUNCTION** | `fits_i64(x) ==> narrow(x) != None` (`narrowWide_isSome_of_fits`), carried on `lib.rs` itself as `#[cfg_attr(feature = "trust-surface", trust::ensures(...))]`. **The first contract in this crate on a function the checker actually calls** — no twin, no bridge test standing in for the compiler. Mutation-verified: swapping the arms, dropping the guard, and widening the guard to always-true each turn the build red | soundness-critical, **on the real body** |
| `narrow_wide_in_range` | same body | `fits_i64_wide(x) ==> ... != None` (`narrowWide_isSome_of_fits`) — an in-range value is never rejected | soundness-critical; logically implied by the row above, kept because it exercises the CITATION path on a consumer shape |
| **`cap_coeff_wide`** | **i128, THE REAL FUNCTION** | `result == min(coeff, degree)`, all three conjuncts, by `capcoeff_i128_min_full` — the `key128` restatement of `capcoeff_i64_min_full`, carried on `lib.rs` itself. Mutation-verified: swapping the arms, and collapsing both arms to `degree` (the under-capping shape the third conjunct exists to exclude), each turn the build red; dropping the `by` drops the function from three kernel-certified obligations to two unknown ones | soundness-critical, **on the real body** |
| **`cap_coeff`** | **i64, THE REAL FUNCTION** | `result == min(coeff, degree)`, all three conjuncts, by `capcoeff_i64_min_full` — the `i64` cap SATURATE actually runs. Blocked for most of this crate's life by the bare-name collision documented below; unblocked when the discharge lane was re-keyed on the canonical def-path. Reports `3 proved, 0 failed, 0 unknown` | soundness-critical, **on the real body** |
| **`add_degree_wide`** | **i128 → Option, THE REAL FUNCTION** | `fits_i64(a) ==> fits_i64(b) ==> add_degree_wide(a, b) != None` (`checkedAdd128_isSome_of_inI64`) — ADD's degree sum never spuriously refuses on in-range operands. Reached from `add`'s real body through `Exact::checked_add`. Mutation-verified: swapping the body to `checked_sub` drops it to `0 proved, 2 unknown` with a strict citation-audit failure | soundness-critical, **on the real body**; a **totality** claim only — it says nothing about the value returned |
| **`sub_degree_wide`** | **i128 → Option, THE REAL FUNCTION** | the same shape by `checkedSub128_isSome_of_inI64`, under WEAKEN's and `negate`'s decrements | soundness-critical, **on the real body**; totality only |
| **`mul_coeff_wide`** | **i128 → Option, THE REAL FUNCTION** | the same shape by `checkedMul128_isSome_of_inI64`, under MULTIPLY's, DIVIDE's and MIR's products | soundness-critical, **on the real body**; totality only |
| **`factor_nonneg`** | **i64 → bool, THE REAL FUNCTION** | `(!result || w >= 0) && (result || w < 0)` by `weaken_factor_sign_exact` — the exact sign test MULTIPLY, DIVIDE, WEAKEN, MIR, SATURATE and RUP all route through. Mutation-verified: flipping to `w <= 0` gives `0 proved, 2 failed` with `verified_counterexample = true` | soundness-critical, **on the real body**; proves the `>= 0` half exactly — the `!= 0` half of MULTIPLY's `k > 0` is **uncited** |
| **`wide_nonneg`** | **i128 → bool, THE REAL FUNCTION** | `(!result \|\| x >= 0) && (result \|\| x < 0)` by `wide_sign_exact` — the sign test MIR runs on floor-remainders and on the mapped coefficient, at the exact-arithmetic width. Mutation-verified: `x >= 1` gives `0 proved, 2 failed` with a strict citation-audit failure | soundness-critical, **on the real body**. Proves the machine comparison decides `key128 0 <= key128 x` exactly, in both directions — NOT that it is `Int.lt x 0`; the key-order-to-`Int` bridge exists in the kernel and is **not cited here** |
| **`wide_at_least`** | **(i128, i128) → bool, THE REAL FUNCTION** | `(!result \|\| a >= b) && (result \|\| a < b)` by `wide_le_exact` — DIVIDE's two ceiling bounds and MIR's `r >= k` order test. Mutation-verified: swapping the operands gives `0 proved, 2 failed` AND turns three behavioural tests red, which is direct evidence the live rule bodies run this leaf rather than a twin beside it | soundness-critical, **on the real body**. That `x <= k*q && k*q < x + k` characterises the ceiling is `ceilQuotient_unique` in the RULE layer; this citation is in the MACHINE layer, and nothing joins them |
| `<i64 as CoeffDomain>::zero` / `::one`, `<i128 as Exact>::zero` / `::one` | **the four constants** | `result == 0` / `result == 1`. Mutation-verified: each body perturbed to a wrong constant gives `0 proved, 2 failed` with `verified_counterexample = true` | **one tier below** every row above: 1 of 2 obligations reaches `Certified`; the authored clause reaches `Trusted`/`Deductive`, not `downstream proof consumer-citation`. A clause naming no island definition structurally cannot be kernel-cited, and no island definition of the right nullary carrier exists |

Twenty notes over nineteen distinct theorems: `capcoeff_le_self` is cited
twice (once on `result`, once on the call), and `key64`, `key128`,
`decide_le_exact` and `decide_and_le_exact` are helper declarations that are
never cited directly — `decide_le_exact` is the shared decision lemma the
per-comparison guard theorems instantiate, `decide_and_le_exact` is its
`Bool.and` lift that `guard_fits_exact` instantiates, and those two lemmas
are the only new declarations that sit *above* the
`-- EXPORT-CERT-BOUNDARY` marker, so they are the only ones replayable from
the committed bundle.

**The bare-name collision that used to block `cap_coeff` — now fixed.**
This entry is kept because the failure mode is worth recognising, not because
it is still live: `veripb_core_proved::cap_coeff` **carries a
compiler-checked contract today** and reports `3 proved, 0 failed, 0
unknown`. The discharge lane was re-keyed on the canonical def-path, which
survives eviction, exactly as the last paragraph of this entry proposed. What
follows is the diagnosis as it stood before that landed.

`veripb_core_proved::cap_coeff` — the `i64` cap SATURATE actually runs — is
recognized by compiler_consumer exactly as `cap_coeff_wide` is (`Select { cmp: Le,
cmp_left: 1, cmp_right: 0, then_param: 1, else_param: 0 }`, byte-identical),
its theorem `capcoeff_i64_min_full` is proved, and the in-walk verifier
proves all three conjuncts of the clause. What refuses it is a *spelling*
collision, not mathematics. To replace `result` with a function's imported
defining equation the discharge lane looks the function up under its **bare
item name** (`tcx.item_name`), and the facet table evicts any bare name owned
by more than one item; `cap_coeff` is also the name of `Exact::cap_coeff`,
`CoeffDomain::cap_coeff` and their four impls, so the key is evicted, `result`
stays universally quantified, and the citation is graded against the
∀-over-`result` reading — which is false, so no honest theorem proves it. The
failure surfaces as a `TypeMismatch` whose *expected* type has **three**
`BitVec 64` binders instead of two; the extra binder is the unbound `result`.
Measured directly: renaming the free function to any name no other item
claims makes the identical clause and citation discharge with no other
change. `cap_coeff_wide` carries the contract only because it is the sole
owner of its name. The fix is compiler-side — key the discharge lane on the
canonical def-path (which survives eviction) rather than the bare name — and
the def-path keying landed on 2026-08-26, and the contract now sits on the
real body.

**And the caveat that belongs next to the strongest rows.** The four
`soundness-critical, i64, real body` rows above, and the four rule-guard
rows, name theorems that sit **below** the `-- EXPORT-CERT-BOUNDARY` marker
in `veripb_kernel.lean`, together with the `key64` and `key128` helpers they
are stated through. Everything below that marker is type-checked by
`clean check` and kernel-checked by compiler_consumer as part of the island, but is
excluded from `clean export-cert` — so those theorems are the ones a third
party *cannot* replay from the committed `veripb_kernel.cleancert`, and they
appear in no line of `veripb_kernel.manifest.txt`. **332** declarations sit
there now: the four `capcoeff_i64_*`; `weaken_factor_sign_exact`; the three
width-guard theorems `guard_fits_lower_exact`, `guard_fits_upper_exact` and
`guard_fits_exact`; the two exact-arithmetic-width comparison wrappers
`wide_sign_exact` and `wide_le_exact` (the `key128` restatements the
citation lane needs, because it matches a theorem's statement against the
goal rather than instantiating a `forall (a b : Nat)` lemma at
`BitVec 128`); and the twelve overflow-checked-arithmetic
characterizations `checkedAdd64_some`/`_none`, `checkedSub64_some`/`_none`,
`checkedMul64_some`/`_none` and their 128-bit images
`checkedAdd128_some`/`_none`, `checkedSub128_some`/`_none`,
`checkedMul128_some`/`_none` — the proof-side model for the checked-arithmetic
citation lane; plus the five that lane's first shipped citations rest on:
`checkedAdd128_comm` and `checkedMul128_comm` (commutativity, the
op-discriminating claims `cadd_wide`/`cmul_wide` cite), `checkedSub128_self_isSome`
(the diagonal claim `csub_wide` cites), and their helpers `int_mul_comm`
(derived by double `Int.rec` over `Nat.mul_comm` — absent from Clean's default
environment) and `fitsI128_zero`; plus the seven closed-pipeline numeric
controls that became sayable in both checkers when the vendored
`BitVec.toNat` reducer learned the structural `ofNat` peel and `ofIntN` grew
its sign branch: `ctrl_checkedAdd64_ok` (born, dropped, and reinstated — its
doc comment carries the history), `ctrl_checkedAdd64_overflow`,
`ctrl_checkedSub64_underflow` (bug C's exact shape), `ctrl_checkedMul64_min_neg1`,
`ctrl_checkedAdd128_ok`, `ctrl_checkedAdd128_neg` and
`ctrl_checkedMul128_min_neg1` — each a boundary edge of the checked model
proved by kernel computation alone; plus the fifty declarations of the
`Nat.xor` sign-branch bridge development and the hypothesis-guarded isSome
layer built on it. The four goal bridges `xor_pivot64_of_lt`,
`xor_pivot64_of_ge`, `xor_pivot128_of_lt` and `xor_pivot128_of_ge` convert
sign-flip order-key bounds to two's-complement arithmetic; the bit-extension
scaffolding under them is `xor_two_pow_of_lt`/`xor_two_pow_of_ge`/
`xor_two_pow_add_cancel`, `xor_add_two_pow_bit_lo`/`xor_add_two_pow_bit_self`/`xor_add_two_pow_bit_hi`,
`testbit_two_pow_below`/`testbit_two_pow_self`,
`bool_xor_false`/`bool_xor_xor_cancel_right`/`nat_xor_xor_cancel_right`
(the involution the environment turned out NOT to provide),
`nat_lt_trans`/`nat_lt_of_lt_of_le`/`nat_zero_lt_two_pow`/
`nat_two_pow_lt_two_pow`/`nat_add_sub_cancel_left`/`nat_add_sub_cancel_of_le`/
`nat_sub_lt_of_lt_add`, and the `rfl` literal-to-power pins
`pow2_63_eq`/`pow2_64_eq`/`pow2_127_eq`/`pow2_128_eq`. On top of the
bridges: `guardFitsW` with `guardFitsW_bounds` and the closed-key controls
`key128_min_pattern`/`key128_max_pattern`,
`toInt128_in_i64_of_key_bounds`/`toInt128_in_i64_of_guard`, the interval
lemmas `fitsI128_add_of_bounds`/`fitsI128_sub_of_bounds`/
`fitsI128_mul_of_bounds` with the sign-split multiplication ladder
`int_pow63_sq`/`int_mul_le_pp`/`int_mul_upper_nonneg`/`int_mul_lower_nonneg`/
`int_mul_bound_nonneg`/`int_mul_neg_flip`/`int_neg_le_zero_of_le`/
`int_neg_le_p_of_neg_p_le`/`int_mul_lower_nonpos`/`int_mul_upper_nonpos`/
`int_mul_bound`/`int_in_p_of_in_i64_lo`/`int_in_p_of_in_i64_hi`, and the
three CITED payoff theorems `checkedAdd128_isSome_of_inI64`,
`checkedSub128_isSome_of_inI64` and `checkedMul128_isSome_of_inI64` — the
hypothesis-guaranteed-`Some` contracts on the checked leaves.

And the NARROWING development, the first CONSUMER shape to carry a contract.
Its model is `truncTo64` (the `x as i64` cast as what it is — two's-complement
truncation, total and guard-free) and two case splits over it: `narrowW`
(scrutinising `guardFitsW`) with `narrowW_some_of_guard` /
`narrowW_none_of_guard_false`, and `narrowWide` (scrutinising
`fitsI64 (toInt128 x)`, the spelling the GuardedNarrow mint emits) with
`narrowWide_some_of_fits` / `narrowWide_none_of_fits_false` /
`narrowWide_some_of_guard`. Cited: `narrowWide_char` — the narrowing equation
as a citable sentence, which type-checks against the goal only if the minted
Rust body IS that case split — and `narrowWide_isSome_of_fits`, the guarded
guarantee that an in-range value is never rejected. The scientific payoff is
`narrowW_value_preserving` and its twin `narrowWide_value_preserving`: under a
true guard, `toInt64 (truncTo64 x) = toInt128 x` — the `i64` admitted into
storage DENOTES THE SAME INTEGER as the `i128` it came from, the
silent-truncation-corruption class that no earlier citation could state,
because the fits twins pin the boolean guard and not the value it admits.
Packaged as `narrowW_some_value` / `narrowWide_some_value`. Supporting it:
`fitsI64_of_bounds` (the `fitsI64` CONVERSE — every earlier consumer ran the
other direction), `fitsI64_toInt128_of_guard`, the key-order-to-raw-pattern
bounds `narrow_key_lo_bound` / `narrow_hi_sub_bound` / `narrow_hi_toNat_ge`,
the negative-branch arithmetic `narrow_hi_j_le` / `narrow_hi_j_le64` /
`narrow_hi_payload` / `narrow_hi_mod`, the branch equations
`ofInt64_toInt128_lo` / `ofInt64_toInt128_hi` / `ofInt64_toInt128_eq_trunc`,
and the literal bridges `narrow_sub_lits` / `narrow_add_lits` /
`narrow_mul_lits` / `narrow_key_lo_lits` / `narrow_pos64`.

And the SIGN-EXTENSION development, which models the one remaining guard
body — `guard::eq_ok`'s `Wide::from(machine) == truth`, a comparison across
two widths through a sign-extending cast. `sextWide v = ofInt128 (toInt64 v)`
is that cast, exact on all `2^64` inputs and introducing no new primitive;
`eqOkW` is the decided equality the compiler mints for the body, and
**`eq_of_eqOkW`** is the payoff — if the machine value and the wide value
compare equal, they denote the same integer, which is precisely the `Int`
equality `entails_add_checked` and `entails_weaken_checked` consume.
Supporting it, and reusable well beyond it: `bitvec_toNat_lt64`,
`key64_raw_lo` / `key64_raw_hi`, `key64_lt64` / `key64_le_max64` (the
sign-flip order key is itself a 64-bit quantity — not definitional, since
`Nat.xor` carries no width), `toInt64_in_i64` (unconditional, unlike its
128-bit cousin), `int_i64Min_le_zero` / `int_zero_le_i64Max`,
`fitsI128_toInt64`, `nat_eq_of_decEq_true`, and the chain
`eqOkW_toNat_eq` / `sextWide_eq_of_eqOkW` / `toInt128_sextWide`.

And finally the **machine-to-rule join**, which is what makes the whole
machine development bear on soundness rather than sit beside it. Until it
existed the kernel had two halves that never referenced each other: the rule
theorems above the boundary, stated over unbounded `Int` with `fitsI64` and
`eqOkB`; and everything in this section, stated over `BitVec` with
`guardFitsW`, `eqOkW` and `narrowWide` — the domain the contracted Rust
guards are actually written in. Both halves were proved, and the claim that
the second discharges the first lived only in prose. `eqOkB_self` and
`eqOkB_of_eq` supply the converse of `eq_of_eqOkB` that the join needs (an
equation yields the Bool the rule theorems take as a hypothesis).
**`entails_add_machine`** then derives `entails_add_checked`'s conclusion
from `guard::eq_ok` and `guard::fits_i64` succeeding, and
**`entails_add_narrowed`** / **`entails_weaken_narrowed`** restate ADD and
WEAKEN at the narrowing the checker actually performs — degree
`toInt64 (truncTo64 t)`, which is what `narrowWide` returns on a passing
guard — so the stored machine word, not a postulated `Int`, is what the
entailment is about.

That residual is now **closed for ADD**. `wideAdd_denotes_exact_sum` proves
what the three theorems above took as a hypothesis: on operands the width
guard has already accepted, the wrapping 128-bit sum the elaborator mints
denotes the exact integer sum. Nothing in it is assumed — `ofInt128_add_wrap`
holds for all inputs, and `toInt128_in_i64_of_guard` supplies exactly the
bounds `fitsI128_add_of_bounds` wants. **`entails_add_from_guards`** then
reaches `entails_add_checked`'s conclusion with every remaining hypothesis
being either a guard whose Rust body carries a compiler-checked contract, or
a statement that a widened degree denotes the degree it was widened from.

So ADD's **degree leg is proved end to end**, and what remains of ADD is its
**terms leg** alone: that `Vec::extend_from_slice` twice is `List.append`.

**MULTIPLY and DIVIDE now have the same machine-domain statements.** They are
the only other rules whose degree is *computed* rather than copied, so they
are the only ones where the narrowing can be wrong.
**`entails_multiply_checked`** and **`entails_divide_checked`** admit a
machine-produced degree `s` only when `eqOkB` certifies it equals the true
scaled degree (`k * d`) or quotient (`f d`) — the same discipline
`entails_add_checked` applies to the sum — and **`entails_multiply_narrowed`**
/ **`entails_divide_narrowed`** restate them at `toInt64 (truncTo64 t)`, the
word `narrowWide` returns on a passing guard.

DIVIDE's two side conditions are carried through unchanged from
`entails_divide`: `CoeffsDominated k f c.terms` and
`Int.lt (k * f c.degree) (c.degree + k)`. Those are exactly the two
inequalities `divide_with` re-checks at **every coefficient and at the
degree**, through `checked_mul` / `checked_add`, failing closed on overflow
rather than wrapping — which is why DIVIDE stays sound even though `ceil_div`
itself is unproved and, in release, computes `q + 1` with an unchecked `+`.

Read the conclusions carefully. Each names the coefficient list as
`scaleTerms k c.terms` / `mapCoeff f c.terms` — an explicit **hypothesis**
about what the terms are, not a claim that any particular Rust loop produced
them. That is the honest factoring these theorems are for: the degree leg is
closed, and the terms leg is a *named assumption* rather than an absence.

**DIVIDE has a second, stronger statement that assumes nothing about the
quotient map.** `entails_divide_checked` models `divide_with`, which is
generic over an arbitrary `f`, so it must take `s = f c.degree` as a
hypothesis. **`entails_divide_from_checks`** models what `divide` actually
*accepts*: its only facts about the quotient are the two inequalities the
Rust re-checks at the degree through the checked leaves — `d <= k*q` and
`k*q < d + k` — and `ceilQuotient_unique` turns those into
`q = intCeilDiv d k`. So an accepted degree **is** the true ceiling quotient
no matter what `ceil_div` computed. That is the licensing argument `divide`'s
doc comment states in prose, now as a theorem, and it is why `ceil_div` being
wrong — including wrapping on its unchecked `q + 1` in a release build —
cannot produce a wrong verdict, only a rejected step. Its conclusion names
the terms as `mapCoeff (fun x => intCeilDiv x k)`, the CONCRETE map, because
`entails_divide_concrete` discharges both side conditions of the general rule
at it.

**`satterm_coeff_le_degree` is the first CITED per-term rule step.** SATURATE's
per-term body `sat_term` carries `result.coeff <= degree` discharged by that
theorem, against a goal built from the E6 import of the compiled body's
coefficient field — so the claim is about the code the checker runs, not about
a model of it. The theorem is `capcoeff_i64_le_degree` with two inert binders
added, because the per-field import is minted over the FLATTENED parameter
list (`lit : Lit` becomes `lit.var : UInt32` and `lit.negated : Bool`) and a
cited theorem must be stated over the compiler's own encoding of the body —
two binders cannot match four however true the statement is. That is the
ergonomic cost of this route, and it is per-function.

**`litctor_var_preserved` and `litnegate_var_preserved`** carry the same idea to
`Lit`: a constructor hands its variable through unchanged, and negation flips
the SIGN only. The second is the one with content — a `negate` that rewrote
`var` would silently change which literal a rule is about, and because an
uncontracted function raises NO obligation, every other magnitude in the crate
would have agreed nothing was wrong. Both are stated over the flattened
signature the per-field import is minted at, which is why `negate` carries an
inert `Bool` binder for `self.negated`.

Three of these live **below** `-- EXPORT-CERT-BOUNDARY`, so like
`entails_add_narrowed` and `wideAdd_denotes_exact_sum` they are checked but
not carried in the replayable bundle. **`wideMul_denotes_exact_product`** is
MULTIPLY's faithfulness lemma — on operands the width guard has accepted, the
wrapping 128-bit product denotes the exact integer product. It is not a
transcription of the ADD case: `ofInt128_add_wrap` holds unconditionally,
whereas the multiply wrap law `ofInt128_mul_wrap_of_fits` needs its
hypothesis, and `fitsI128_mul_of_bounds` supplies it from the same two guards.
**`entails_multiply_from_guards`** then reaches the conclusion with nothing
about the arithmetic assumed. **`capCoeff_inI64`** records why SATURATE needs
no width guard at all: `capCoeff` returns one of its two arguments, so it
cannot leave `i64` when both arguments are in it — which is why the Rust
`cap_coeff` is the one rule leaf with no overflow check beside it.

So the score by rule, for the degree alone: ADD and WEAKEN closed end to end;
MULTIPLY and DIVIDE closed modulo the faithfulness of the wide arithmetic;
SATURATE has no degree obligation at all (it copies `c.degree` unchanged) and
no width obligation either, because capping returns one of its two arguments;
LITERAL's degree is the constant `1`. NEGATE is the one rule left out, and
not incidentally: its degree is `coeffSum c.terms - d + 1`, a fold over the
term list. The kernel side is already factored — `negC` takes that degree as
a parameter rather than computing it — so what is missing is not a theorem
but the terms leg itself: that the Rust fold computes the `coeffSum` the
parameter stands for.

**Two walls stood between the terms leg and a contract. One has been
removed; the other has not.**

*Wall 1, Rust's own bound — REMOVED.* Every `ensures` predicate routes
through the `contract_build_check_ensures` lang item, which demanded
`C: Fn(&Ret) -> bool + Copy + 'static`. The `'static` forbade capturing a
borrowed parameter, so even the purely SCALAR clause
`move |ret: &Cst| ret.degree == a.degree` on a function taking `a: &Cst`
was a hard compile error — no function could state a postcondition relating
its output to its inputs. That bound was strictly stronger than its only
consumer, `core::intrinsics::contract_check_ensures`, which requires just
`Copy`. It is now relaxed to match (trust `1464e5acab5`). `Copy` stays and
is load-bearing — the checker runs at every return point — and a closure
capturing a shared reference is `Copy`, so dropping `'static` sufficed.

Measured after: `ret.degree == a.degree` reports `2 proved, 0 failed, 0
unknown`, and so does `ret.degree <= c.degree` — which is the hypothesis of
`VeriPbCore.entails_weaken_degree`, expressible as a contract for the first
time.

*Wall 2, the clause lowering — STANDS, and here is exactly how thick it is.*
`ret.terms == c.terms` now COMPILES and then reports `unsupported contract
predicate expression`. The clause language DOES have collection support — it
is simply narrower than `Constraint.terms` needs. Measured, native signature
form, one probe per axis:

| collection | element | verdict |
|---|---|---|
| `&[i64]` (slice) | scalar | **1 proved, 0 failed, 0 unknown** |
| `&[Term]` (slice) | struct | 0 proved, 1 unknown |
| `[Term; 2]` (array) | struct | 0 proved, 1 unknown |
| `Vec<i64>` | scalar | **hard compile error** |

The `Vec` row is not a soft refusal: *"collection accessor `len` requires an
Array base, found Datatype `std::vec::Vec<i64>`"*. `collection_element_domain_from_ty`
matches `ty::Array` and `ty::Slice`; a `Vec` is an Adt and never reaches it.

`Constraint.terms` is `Vec<Term<Coeff>>` — a `Vec` (not an array base) of
structs (not a scalar element) — so it fails on **both** axes. Stating the
terms leg therefore needs four independent pieces, none of which is a gate
flip:

1. `Vec` modeled as an array base (it is an Adt; its slice view would have to
   be the model).
2. Struct elements admitted into the element domain.
3. A sequence sort in `lowered_expr_ty`, which today returns `Some` only for
   bool / integral / float — so a `Vec`-typed projection has no expression
   sort. The equality arm itself is already generic (`lhs.ty == rhs.ty`), so
   it needs no change.
4. The collection-carrying environment reached from a postcondition. It is
   built only for `origin == Native` with kind `Requires`/`Decreases`;
   `Ensures` gets `None`. Widening that alone was tried and **breaks native
   `ensures` outright** — `validate_native_clause_body` has no
   `Ensures => SourceContractClause::Ensures` arm, and `function_source_sorts`
   collects HIR pattern bindings only, so there is no `result` row to resolve
   against.

**And the cheap sequence model is UNSOUND — measured, then reverted.**
Four of those five pieces are now done and the fifth has a tempting
one-line answer that must not be taken. Modelling `Vec` as an opaque slice
fat pointer in the ExternalCodegenIr bridge (following the `SymArray` precedent
already in that file) lets the clause lower, and then:

| clause | verdict |
|---|---|
| `ret.terms == c.terms`, terms carried through — **TRUE** | 0 proved, **1 FAILED**, 1 unknown, `verified_counterexample = true` |
| the same clause, terms emptied — **FALSE** | 0 proved, 0 failed, 3 unknown |

Exactly inverted: a true clause refuted with a fabricated counterexample
while a genuinely false one stays unknown. That would tell a reader their
correct code is wrong.

The reasoning error is subtle and worth keeping. `SymArray` justifies its
opaque model as *"the element value is unconstrained, so it asserts nothing
and cannot mint a native false proof."* That protects against false
**proofs**. `ret.terms == c.terms` is an equality between two such models,
and nothing links a clone to its source, so the solver picks differing
elements and reports a counterexample — a false **refutation**. Different
failure mode; the argument does not carry over.

So the fifth piece needs a model that **relates** a cloned sequence to its
source, not one that merely lowers. Anything cheaper makes the tool worse
than leaving the clause unstatable.

Two further measurements pin that down, so the next attempt does not start
by re-testing the cheap options:

* **Reflexivity does not save it.** `ensures(move |ret: &Cst| ret.terms ==
  ret.terms)` — trivially true — reports `1 proved, 1 unknown`, and the
  unknown is `trust-full-verifier: Unsupported`, the same bridge wall. So
  sequence *equality theory* is not separately missing; the obligation never
  reaches a solver. The scalar control on the identical body is `2 proved`.
* **There is no opaque-value option in ExternalCodegenIr.** Its `Ty` offers `Ptr`,
  `FatPtr`, `Unit`, `Array`, `Tuple`, `PtrConst`, `PtrMut` — no abstract
  handle. Both candidate mappings *decide* equality: `FatPtr` decomposes
  into unconstrained elements (the measured false refutation above), and
  `Ptr` compares identity, which would refute `v.clone() == v` because
  `PartialEq` on `Vec` compares contents, not addresses.

* **The IR already has the right type, and it is still not enough.**
  `ExternalCodegenIrTy::Sequence(TyId)` — "ordered variable-length sequence of elements
  of type T" — exists and the bridge CAN map `Vec<T>` to it: measured, the
  mapping lowers with no `unsupported type` message and the verifier reaches
  the postcondition for the first time. It then refutes a TRUE clause anyway,
  because `Vec::clone` is an OPAQUE CALL returning a fresh unconstrained
  sequence with nothing tying it to its input. So the wall is not the type,
  the sort, or the bridge — it is that no model RELATES the output sequence
  to the input.
* **And the obvious repair is itself unsound.** Modelling `clone(v) ≡ v`
  looks safe and is not: `Vec::clone` calls `T::clone` per element while
  `PartialEq` compares via `T::eq`, so an element type whose `Clone`
  disagrees with its `PartialEq` breaks the identity. A sound version must be
  restricted to element types where the two provably agree, and it belongs in
  the guard lane whose own comment records a false-proof incident
  ("CRATE-ANCHOR (round-5 false-proof close)") caused by an unanchored name
  match conjoining a false fact globally.

* **Relaxing the closure's `Copy` bound would not help, and an array proves
  it.** The plan was: make the leaf take its terms by value, MOVE them into
  the result, and have the clause name the captured pre-state, so both sides
  are literally the same value and equality is reflexive. That needs the
  ensures closure to capture a non-`Copy` `Vec`, hence relaxing `Copy`. But
  `[i64; 2]` is ALREADY `Copy`, so the whole pattern is testable with no
  compiler change — and measured, the true clause
  `ensures(move |ret: &Cst2| ret.terms == terms)` over
  `Cst2 { terms, degree: d }` comes back **UNKNOWN**, while its false twin
  (body writes `[0, 0]`) is correctly **FAILED**. Sound, discriminating, and
  still not proved. So the pre-state-capture route does not reach the terms
  leg, and the three coupled changes it would have required (intrinsic
  declaration, lifetime parameter, core signature, lowering) are not worth
  paying for.
* **A counterexample is only evidence of unsoundness when the clause is
  TRUE.** The safety metric used here counts `verified_counterexample = true`
  occurrences; on a deliberately false probe that count is 1 and correct. It
  means something only paired with a true twin — the pairing is the test, not
  the count.

* **A clause cannot CALL another proved function — measured, and not because
  of name ambiguity.** Composing rule-level statements out of proved leaves
  would be natural if a clause could write `result == cap_coeff(d, c)`. Five
  probes say it cannot: bare name, `crate::`-qualified path, and a leaf whose
  bare name is UNIQUE (`cap_coeff_wide`) all return `0 proved, 0 failed, 2
  unknown`, and so do their deliberately-false twins. The E6 debug line shows
  the bodies are fine — `admissible=true … recognize=Some(Select { … })` — so
  it is the clause's call that is `Unsupported`, not the function. Nothing is
  falsely proved here; the lane declines. Composition therefore goes the other
  way: restate the characterisation on each function and cite it, which is
  what `cap_coeff` and `cap_coeff_wide` already do.

* **The PER-TERM step: a verifier defect, now FIXED — and a different limit
  behind it.** If the terms list is out of reach, the natural fallback is to
  contract each rule's per-term step and leave only the `map` unproved.
  SATURATE's step is `Term { coeff: cap_coeff(d, t.coeff), lit: t.lit }`.
  Measured, the true clause `ret.coeff <= degree` was **falsely refuted** —
  `0 proved, 3 failed`, `verified_counterexample = true` against a statement
  that has no counterexample, since `cap_coeff` returns one of its two
  arguments and both are `<= degree`.

  Five probes localised it: a select returned BARE proves; an aggregate field
  holding a plain parameter proves; only a select result STORED INTO an
  aggregate field failed, identically whether the select was inline or reached
  through a call. `TRUST_DUMP_V2_VC` showed the negated clause sitting on
  `_0.0#s3_0`, tied by the merge pin to `c#s1_0_s2_0` — the reaching-def JOIN
  of the select's temp — which nothing defined. The clause was a query over a
  free value, so the "counterexample" was a model of a formula about nothing.
  It was the third instance of a family the toolchain records
  (`early_return_postcondition_tests`, `return_slot_join_version_tests`), one
  level down on a return-slot FIELD, and neither existing fix reached it:
  `is_return_slot_name` is `name == "_0" || name.starts_with("_0#")`.

  **Fixed** in trust `f3766cb6760`: `return_edge_merge_pins` now also takes as
  subjects the projection-free locals a return block stores into `_0` through a
  single `Aggregate`, so the join name is grounded to this predecessor's exit
  value. The added conjuncts are true on the executions the row covers, which
  is why it cannot make a FALSE clause provable. Re-measured on a rebuilt
  compiler: the two true clauses go from `0 proved, 3 failed` to **`3 proved,
  0 failed`**, their false twins are still refuted, and the only
  `verified_counterexample`s left in the whole crate belong to `div_mod_floor`
  (`div_euclid` genuinely traps at `k = 0` and `(MIN, -1)`) and to the
  deliberately-false twin — **none on a true clause**.

  **The leaf still cannot be landed, for a different and now-precise reason.**
  A contract carrying real content must cite a theorem — the crate's own
  `UNCITED_NATIVE_ONLY` gate allows uncited clauses only for nullary constants
  and the definitional output-degree claims, and `ret.coeff <= degree` is
  richer than that. But an aggregate-returning function cannot carry a cited
  clause in EITHER form: the closure form is refused with *"predicate must be a
  comparison or a connective"*, and the signature form with *"missing supported
  type for clause variable `result.coeff`"*. So the citation lane has no sort
  for a field projection of the result. That, not the join-name defect, is now
  what blocks the per-term leg, and the gate was left as it is rather than
  widened to accommodate the clause.

  **A contract's own closure used to destroy the admissibility the contract
  needs — that is FIXED.** Measured on `sat_term`, the same function and the
  same clause, before the fix:

  | form | admissible | obligations |
  |---|---|---|
  | closure — `move \|ret: &Term<Coeff>\| ret.coeff <= degree` | false | **3 proved** |
  | signature — `result.coeff <= degree` | true | 0 proved, 2 unknown |

  The two were mutually exclusive: the form that PROVED could never be cited,
  and the form that was citable proved nothing. `TRUST_E6_DEBUG`'s deficits
  field named the cause in one line — `Pure (not established: local _4 has type
  Adt { name: "core::option::Option", … Closure { name:
  "lib::sat_term::{closure#0}" … } })`. `contract_check_ensures` materialises a
  closure-form predicate as an `Option<{closure}>` LOCAL of the contracted
  function, and STORES the closure into it; both were non-scalar, so writing a
  specification poisoned all four facets of the body it specified.

  `facet_inference::is_contract_injected_ty` now exempts exactly that shape —
  keyed to `<def_path>::{closure#N}`, reaching the type gate and the
  destination of the store and nothing else, so a foreign closure or any USE of
  one still takes a body out. `sat_term` is now **`admissible=true` while
  keeping its 3 proved obligations**.

  Getting there took five gates, and they are listed because each one was
  invisible until the one before it moved: the aggregate whitelist admitted
  only `Option`; `is_valid_closed_leaf` required a scalar return TYPE (and
  local 0's type must equal it, so every later gate was unreachable);
  `local_ty_in_closed_fragment` allowed a struct only at a parameter;
  `ty_is_scalar_struct` did not recurse, so `Term { coeff, lit }` was refused
  for its `lit` field alone; and then the contract closure.

  **What is still missing for a CITED per-term step.** Admissibility is
  necessary, not sufficient. The recognizer reports `None` on the real body
  because `-O` reuses a parameter slot for the cap temporary, and resolving an
  operand by local index once its slot has been rewritten is exactly the
  unsoundness two earlier recognizer bugs were: it would name a parameter for a
  value that is no longer that parameter. And even once recognized, nothing is
  minted — `AggregateFields` returns no kernel term, because a clause on an
  aggregate names `result.<i>` and what the discharge lane needs is field `i`'s
  definition, not a Clean structure for every client ADT. That per-field mint,
  plus an E9 binding for `result.<i>`, is what stands between here and a
  kernel-cited rule step.

  One more measured limit found on the way: the FULL min characterisation
  `ret.coeff <= coeff && ret.coeff <= degree && (ret.coeff >= degree ||
  ret.coeff >= coeff)` is TRUE of the step and is **falsely refuted**
  (`0 proved, 2 failed`) — the separate conjunction defect probe f53 records,
  where the native lane refutes uncited `&&` clauses that are tautologies.
  Fail-safe, and unrelated to the fix above.

Together: any model that decides sequence equality without grounding
contents yields false refutations on the clone case. The sound choices are
real content grounding, or `unknown` — and `unknown` is what the toolchain
does today. The root of the grounding work is
`read_only_collection_shape_for_local`, which gates on
`local == 0 || local > arg_count` — local 0 being the return slot — and
additionally demands `Ty::Ref { inner: Slice|Array }` with a scalar element
sort. A result `Vec<Term>` field misses all three, so this is a redesign of
a parameter-only model, inside the lane that decides whether a
counterexample is real.

One encouraging measurement, because it says the *grounding* is not the
missing piece: a scalar field carried through an aggregate construction by
value IS relatable to its input. `ensures(move |ret: &Cst| ret.tag == c.tag)`
on `Cst { terms: c.terms, degree: r, tag: c.tag }` reports `2 proved, 0
failed, 0 unknown`, and mutating the body to `tag: c.tag ^ 1` drops it to
`0 proved, 2 unknown`. The field-carry lane works; it is the non-scalar sort
that is absent.

Two further limits, measured in the same run and worth recording because
each looked like a route:

* A `<=` clause over a body using `saturating_sub` is `unknown` with NO
  lowering refusal — the clause is fine and the VERIFIER cannot follow the
  arithmetic. That is a solver-reach problem, not a language one.
* `requires` + `ensures` together on the weaken shape is
  NON-DISCRIMINATING: the true body and a mutated body both report
  `1 proved, 2 unknown`, and adding the `requires` cost the `ensures` its
  proof. Not a working combination.

This is why the contracts that exist — `pack_constraint`, `weaken_apply` —
still relate the result only to scalar parameters.

Three further things were measured rather than assumed, each closing a route
that looked open:

* The `requires` half does NOT help. The collection-carrying clause
  environment is built for `Requires`/`Decreases`/`LoopInvariant` and not for
  `ensures`, which suggested `requires(terms.len() == n)` might lower. It does
  not: it yields the same `unsupported contract predicate expression`, because
  the refusal is in the expression lowering, not in the clause-kind gate.
* `Option<Constraint>` is not a workaround for the `Result` blocker — both are
  `unknown`.
* The `Ty::Seq` lowering (which makes `Vec` carry its element type) is a real
  fix and is NOT on this critical path: a passing scalar control emits the same
  `unsupported type: Seq` bridge diagnostic and still reports `2 proved`, and a
  probe using a fixed-size array — no `Vec`, no `Seq` anywhere — still fails
  the same way. Anyone attacking the terms leg by fixing the type bridge will
  move zero verdicts.

What the terms leg has instead is the **runtime** correspondence: `--kernel-verify`
re-derives every applied rule against the proved kernel, per application, and a
divergence is `CheckingError::KernelDivergence`. That is a real guarantee, and
it is a different one from a static proof — it holds for the runs you make, not
for all inputs.
That is a correspondence between a Rust aggregate and a kernel list, not a
fact about arithmetic, and it is the open question.

WEAKEN's degree leg is closed the same way.
`wideSub_denotes_exact_difference` is the subtraction twin, stated at the
elaborator's BIASED payload `(toNat a + 2^128) - toNat b` -- the bias is not
cosmetic, since `Nat.sub` truncates at zero and the naive spelling would be
wrong exactly when the difference is negative, which is the direction a degree
decrement runs. Dropping it turns the proof red. `entails_weaken_from_guards`
then discharges `entails_weaken_narrowed`'s hypothesis through
`sub_add_cancel`. So WEAKEN's remaining leg is weaker still than ADD's: its
`terms` field is UNCHANGED, so it needs no `append` -- only that an unmodified
aggregate is carried through.

MULTIPLY, DIVIDE, SATURATE and MIR have no join at all — they map over every coefficient, so their correspondence is a fallible
fold this kernel does not have.

On top of all that sit the two sections that closed the round-trip
inventory. The **toInt/ofInt round trips** (69 declarations):
`toInt64_ofInt64` and `toInt128_ofInt128` themselves with their
constructor branches `toInt64_ofInt64_ofNat`/`toInt64_ofInt64_negSucc`/
`toInt128_ofInt128_ofNat`/`toInt128_ofInt128_negSucc`; the definitional
`BitVec.toNat`/`BitVec.ofNat` pins `toNat64_ofNat`/`toNat128_ofNat` with their
range-collapsed forms `toNat64_ofNat_of_lt`/`toNat128_ofNat_of_lt`; the
mod-collapse ladder `nat_mod_eq_of_lt`/`nat_modCore_eq_of_lt`/
`modcore_succ_eq_of_lt`/`modcore_succ_unfold`/`nat_rec_const_succ_arm`/
`nat_sub_pos_absurd`/`nat_one_le_sub_of_lt`/`nat_succ_sub_self`; the
`Int.NonNeg` order inversions `int_nonneg_subNatNat_le`/`int_ofNat_le_inv`/
`int_negSucc_le_inv` with `int_ble_zero_negSucc`, `int_subNatNat_add_cancel`
and `int_subNatNat_of_le`; the `fitsI128` extractors `fitsI128_lower`/
`fitsI128_upper`; the sub shuffles `nat_add_sub_assoc`/`nat_sub_sub_cancel`/
`nat_ble_false_of_lt`; the key equations `key64_ofNat_lo`/`key64_ofNat_hi`/
`key128_ofNat_lo`/`key128_ofNat_hi` with `lt64_of_lt63`/`lt128_of_lt127`,
the sign-match rewrites `toInt64_of_key_true`/`toInt64_of_key_false`/
`toInt128_of_key_true`/`toInt128_of_key_false`, the branch selectors
`ofInt64_ofNat_eq`/`ofInt64_negSucc_arm`/`ofInt64_negSucc_eq`/
`int_add_negSucc_pow64` and their 128 twins `ofInt128_ofNat_eq`/
`ofInt128_negSucc_arm`/`ofInt128_negSucc_eq`/`int_add_negSucc_pow128`, the
bound and pivot helpers `lt_pivot64_of_le_max`/`le_pivot64_add`/
`lt_pivot128_of_le_max`/`le_pivot128_add`, and the per-width literal pins
and arithmetic steps `rt64_le_lits`/`rt64_sub_lits`/`rt64_add_lits`/
`rt64_u_ge`/`rt64_u_lt`/`rt64_shift`/`rt64_key_sub`/`rt64_key`/`rt64_key_lt`
and `rt128_le_lits`/`rt128_sub_lits`/`rt128_add_lits`/`rt128_u_ge`/
`rt128_u_lt`/`rt128_shift`/`rt128_key_sub`/`rt128_key`/`rt128_key_lt`.
And the **wrap-payload machinery with the ADD wrap restatement**
(56 declarations): `checkedAdd128_some_wrap` on top of `ofInt128_add_wrap`;
the toNat-extensionality layer `bitvec_eq_of_toNat_eq`/
`bitvec128_ofNat_congr`/`bitvec64_ofNat_congr` with `bitvec_toNat_lt128`/
`bitvec_toNat_le_max128`; the modCore fuel-sufficiency development
`nat_modCore_fuel_eq`/`modcore_fuel_case_ge`/`modcore_succ_step_of_le`/
`nat_rec_const_zero_arm`/`nat_sub_eq_zero_of_le`/`nat_strong_ind`/
`nat_pred_le_pred`/`nat_sub_le_pred`/`nat_le_pred_of_succ_le`/`nat_sub_one`
and the shift laws `nat_mod_shift`/`nat_mod_mul_shift` with
`nat_le_add_left_flip`/`nat_succ_le_add_of_pos`; the sign bridges
`toInt128_toNat_lo`/`toInt128_toNat_hi`/`toInt128_key_hi_raw`/
`toNat_hi_payload`/`toNat_hi_cancel` with `nat_succ_sub`/
`nat_add_sub_add_right`/`nat_succ_add_flip`/`int_subNatNat_of_lt`/
`nat_sub_sub_of_le`/`int_add_negSucc_pow128_wide`/`ofInt128_negSucc_wide`/
`hi_j_le`; the literal pins `posW128`/`P_le_Wm1`/`wrap_sub_lits`/
`wrap_add_lits`; and the four-way sign split `wrap_add_ll`/`wrap_add_hh`/
`wrap_add_lh`/`wrap_add_hl` with its case ladder `wrap_hh_j_le`/
`wrap_hh_sum1`/`wrap_hh_sum2`/`wrap_hh_lhs`/`wrap_dq_generic`/
`wrap_rhs_generic`/`wrap_hh_sumEq`/`wrap_lh_sEq`/`wrap_lh_WEq`/
`wrap_lh_sumEq`/`wrap_add_lh_nonneg`/`wrap_lh_neg_m_le`/
`wrap_lh_neg_payload`/`wrap_add_lh_neg`.
And the **SUB and MUL wrap restatements** (63 declarations), their minted
payload spellings measured from trust-spec-elab's `Domain::arithmetic`:
`checkedSub128_some_wrap` on `ofInt128_sub_wrap` and
`checkedMul128_some_wrap` on `ofInt128_mul_wrap_of_fits`; the pinned
`Int.sub`/`Int.mul` constructor bridges `int_sub_ofNat_negSucc`/
`int_sub_negSucc_negSucc`/`int_sub_ofNat_ofNat_succ`/
`int_sub_negSucc_ofNat_succ`/`int_sub_zero_eq` and `int_mul_ofNat_ofNat`/
`int_mul_negSucc_negSucc`/`int_mul_ofNat_succ_negSucc`/
`int_mul_zero_negSucc`; the shuffles `nat_add_swap_right`/
`nat_add_left_swap` with the bound helpers `L1_le_Wm1`/`wsub_hsWm1`/
`wsub_nbWm1`/`wsub_J_le`; SUB's Int-level case equalities
`wsub_int_bhi_alo`/`wsub_int_bhi_ahi`/`wsub_int_b0`/`wsub_int_bs_alo`/
`wsub_int_bs_ahi`, its payload algebra `wsub_sWEq`/`wsub_TEq`/
`wsub_T_bhi`/`wsub_T_bs`/`wsub_succ_bridge`/`wsub_n2_lhs`/`wsub_n2_rhs`/
`wsub_n2`/`wsub_n3`/`wsub_n5_lhs`/`wsub_n5_rhs`/`wsub_n5`/`wsub_n6`/
`wsub_n7_lhs`/`wsub_n7_rhs_inner`/`wsub_n7`, and its case leaves
`wsub_bhi_alo`/`wsub_bhi_ahi_le`/`wsub_bhi_ahi_lt`/`wsub_b0_alo`/
`wsub_b0_ahi`/`wsub_bs_alo_le`/`wsub_bs_alo_lt`/`wsub_bs_ahi`; MUL's
Int-level equalities `wmul_int_ll`/`wmul_int_hh`/`wmul_int_lh0`/
`wmul_int_lhs`, its distribution ladder `wmul_cancelA`/`wmul_hh_p1`/
`wmul_p2_left`/`wmul_p2_right`/`wmul_p2`, and its case leaves
`wmul_ll`/`wmul_hh`/`wmul_lh_zero`/`wmul_lh_succ`/`wmul_lh`/`wmul_hl`.

The twelve `_some`/`_none` characterizations
remain uncited: no ensures clause can yet state their fits-hypothesis. The
`Some`-payload equality against the clause fragment's wrapping spelling is
now PROVED for ALL THREE OPS (`checkedAdd128_some_wrap`,
`checkedSub128_some_wrap`, `checkedMul128_some_wrap`) — what remains for
citing them is the `Some`/`None`-former citation lane itself, on the
compiler side. The omission matters more than the arithmetic: the rule-guard
theorems are precisely the citations whose *deletion* compiler_consumer notices on its
own, so they are the load-bearing ones and they are outside the bundle too.
Verify with

```bash
for t in capcoeff_i64_le_coeff capcoeff_i64_le_degree capcoeff_i64_min_full \
         capcoeff_i64_le_capcoeff weaken_factor_sign_exact \
         guard_fits_lower_exact guard_fits_upper_exact guard_fits_exact \
         checkedAdd64_some checkedAdd64_none checkedSub64_some \
         checkedSub64_none checkedMul64_some checkedMul64_none \
         checkedAdd128_some checkedAdd128_none checkedSub128_some \
         checkedSub128_none checkedMul128_some checkedMul128_none; do
  grep -c "^$t " veripb-core-proved/clean/veripb_kernel.manifest.txt   # 0, twenty times
done
```

That list is not prose either: `bundle_sync.rs` derives the below-marker
theorem names from the `.lean` and fails if any of them is not named here, so
a seventh excluded theorem cannot be added without this paragraph noticing.

The reason is measured rather than defensive — exporting a certificate over
`key64`'s `Nat.xor _ 2^63` on a `BitVec 64` exhausts 128 GB and is SIGKILLed,
with the boundary in place the same export finishes in seconds — and
`veripb-core-proved/clean/README.md` ("The export boundary") states it in
full. `tests/bundle_sync.rs` splits at the same marker and asserts both
directions, including that no below-marker theorem ever appears in the
manifest claiming to have been replayed. The point of repeating it here is
that this section makes the strongest claim in the document, and the reader
who believes it should learn at the same moment that its evidence is
`clean check` plus compiler_consumer rather than the shipped bundle.

What remains outside the clause fragment is *shape*, not width: `Vec<Term>`,
`Constraint`, and other aggregates. Therefore:

* the *list-level* rule lemmas (`entails_add`, `entails_divide`, …) are proved
  in Clean and kernel-checked in the island, but they are **not** cited on the
  corresponding Rust functions;
* the correspondence between, say, `veripb_core_proved::add` and
  `VeriPbCore.entails_add` is at present a documented-and-tested claim, not a
  compiler-enforced one.

That remaining gap is a property of the bridge, not of the proofs, and
closing it needs aggregate-typed clauses. It is stated here rather than
glossed over.

### 4.2 Why `trust_surface.rs` is behind a cargo feature

`clean { … }` is grammar that vanilla rustc rejects. `src/lib.rs` declares

```rust
#[cfg(feature = "trust-surface")]
pub mod trust_surface;
```

and the feature is off by default, so a default build
(`targo --unverified build`) never *reads* the file. The workspace therefore
builds and tests without it; only `scripts/verify-proofs.sh` compiles the file
to re-verify the proofs.
`trust_surface_is_not_part_of_the_stock_build` pins this.

### 4.3 Island encoding constraints (discovered, not assumed)

A `clean { … }` island is delimited by **Rust token trees**. Consequences,
learned by compiling:

* `→`, `∀`, `—`, and backticks do not lex — the island body must be pure ASCII
  (`->`, `forall`).
* Lean block comments containing a brace break the island boundary
  (`tests/ui/trust/clean_island_lexical_block_comment.rs` pins this as a hard
  error).

So the canonical, commented source is the `.lean` file, and the island is its
comment-free ASCII projection, with `tests/island_sync.rs` as the drift guard.

---

## 5. What slice 2 closed, and what remains out of scope

The slice-1 list, item by item. "DONE" means machine-checked in
`veripb_kernel.lean` and mirrored in Rust; details in §7.

1. **Proof-sequence composition — DONE.** `DStep` (one constructor per rule —
   twelve of them, including RUP, trivial axioms, normalization and both MIR
   cuts) and `DbOk` (init/derive/delete over an id-indexed database with
   deletion holes) model the checker main loop; `checker_sound` is the
   top-level theorem: a `DbOk` database holding a stored constraint with
   nonnegative coefficients and `coeffSum < degree` refutes the formula. An
   end-to-end control refutation (`ctrl_rup_refutation_end_to_end`) is
   kernel-evaluated.

   "One constructor per rule" is now literally true, which it was not before:
   `DStep` had ten constructors and no MIR, so a derivation using a rule the
   kernel *proves* could not be expressed in the composition at all, and
   `checker_sound` said nothing about it. Closing that needed the module
   order to change — DIV/MIR/VF-MIR now sit above module D, because a
   relation with one constructor per rule can only be stated after every rule
   exists. Concrete DIVIDE deliberately did *not* get a constructor:
   `divS` is already parametric in the quotient map, so
   `dstep_div_concrete` is a derived **theorem** instantiating it at
   `intCeilDiv`, and the trusted inductive does not grow.

   Non-vacuity: `ctrl_dstep_div`, `ctrl_dstep_mir`, `ctrl_dstep_mir_var` and
   their `ctrl_dbok_*` companions instantiate those steps at concrete
   constraints, and `ctrl_mir_entailed_through_composition` carries a MIR
   step all the way through `dbOk_entailed`.

2. **Unit propagation — DONE, as a checked certificate.** The watched-literal
   engine stays fast and unproved; what it must produce is a *trail*
   certificate, replayed against `PropTrail`, whose every step is the
   decidable check `slackWithout l tr c.terms < c.degree` and whose conflict
   is `slackTerms tr cc.terms < cc.degree`. `trail_sound`, `rup_conflict_unsat`
   and `entails_of_rup` turn a replayed conflict into `Entails F c`.

3. **A concrete `ceilDiv` — DONE.** A self-contained fuel-based Euclidean
   division theory (`NatDivMod` with its spec, `natCeilDiv`, `intCeilDiv`
   with the two ceiling bounds over `Int`) culminates in
   `entails_divide_concrete`: DIVIDE with the concrete ceiling quotient map
   and no side conditions left to the checker. `ceilQuotient_unique` ties it
   to the executable rule: because `divide_with` re-checks *both* bounds at
   *every* coefficient and at the degree, an accepted output **is** the
   concrete cut (§3.3). The same foundation carries the floor pair
   (`intFloorDiv`/`intFloorMod`) and every MIR shape:

   * `entails_mir` — normalized form, with `AllNonneg`;
   * `entails_mir_signed` — the same cut with the sign condition dropped
     (the eval bound is a fold of the unconditional `mirF_subadd`, so the
     hypothesis was vestigial);
   * `entails_mir_variable` — the live checker's variable-form cut, flip and
     flip-back discharged internally by `varTerms_vfMapTerms`.

   **No MIR shape is unproved any more, and none is unwired.** The
   `mir-variable-form-unproved` skip this section used to describe is gone:
   `kernel_bridge.rs` routes `Instruction::VariableFormMIR` through
   `kernel::mir::mir_variable`, the executable image of
   `entails_mir_variable`, and the literal appears nowhere in
   `veripb-checker/src` or in `tests/kernel_verify_expected.txt`.
   `entails_mir` is retained (rather than re-derived from the signed form)
   because the bridge names it for the normalized path.

   The MIR value function is **subadditive**, `g(x + y) ≤ g(x) + g(y)`, and
   the key lemma is `mirF_subadd`. The MIR literature says *super*additive
   because it works in `≤` form; VeriPB normalizes to `≥` form, where the
   mirrored value function is subadditive, and that is the direction the
   eval-bound fold needs (`Σ g(aᵢ)·lᵢ ≥ g(Σ aᵢ·lᵢ) ≥ g(A)`). `mirF` is
   provably *not* superadditive, and `ctrl_mirF_not_superadd` refutes that
   reading inside the kernel so the name cannot drift back.

4. **Term normalization — DONE.** `normC` (insert-based merge by variable,
   cancel `x` against `~x`, flip negative coefficients, drop zeros) with the
   degree bookkeeping over unbounded `Int`, proved semantically transparent in
   *both* directions (`holds_normC_of_holds` / `holds_of_holds_normC`), output
   nonnegativity (`normC_nonneg`), and formula-level transfer
   (`unsat_of_normF_unsat`, `holdsAll_of_holdsAll_normF`). Kernel-evaluated
   controls pin a merge, a cancellation-to-empty, and a flip.

5. **Substitution/redundancy rules** (`red`, `dom`, witnesses), objective
   reasoning, and the ordering machinery (`def_order`) — still not modelled.
   Under `--kernel-verify` every *discharge* these rules rest on is
   re-derived, even though the rules themselves are not modelled: RUP-based
   discharges are kernel-replayed, trivial/DB-lookup/contradiction
   discharges are re-judged on the proved normal forms, and
   **syntactic-implication discharges are re-derived through the proved rule
   chain** — both the proofgoal form (`PremiseImplies`) and the
   obligation-*generation* shortcut that `red`/`dom`/checked deletion take
   instead of emitting a goal (`consume_autodischarge`), which is the one
   this item is about. Substituted-implication discharges
   (`DBImpliesSubstituted`) are re-derived too (§7.3). The two report on the
   summary line as `N implication` / `N substituted-implication` "re-derived
   by the proved kernel", and their counted failures are
   `implication-not-reconstructed` and
   `substituted-implication-not-reconstructed`, neither of which the corpus
   produces. What stays unmodelled is only the witness/objective/order
   *meta-steps* themselves, which are counted
   as unmodelled skips (`red-witness-unmodelled`, `dom-unmodelled`,
   `checked-deletion-witness-unmodelled`, `obju-unmodelled`,
   `pbc-unmodelled`, `order-definition-unmodelled`), so a run they decide
   never reports "nothing outside the proved fragment" (§7.3).

   **Why the unexercised skip reasons are kept.** Most reason literals in the
   checker are never produced by the test corpus. §7.3 carries the census and
   the two commands that derive it — deliberately in one place only, because
   the set moves with the bridge. What belongs here is the *policy*: they are
   kept on purpose, and none should be deleted for being unexercised. Each
   names a branch that must **fail closed**; deleting the literal would not
   remove the branch, it would make that branch silently trusted, which is
   the precise failure mode `--kernel-verify` exists to prevent. Reading them
   as four groups:

   * **width refusals** (`amount-not-i64`, `divisor-not-i64`,
     `result-not-i64-representable`, `objective-not-i64-representable`,
     `variable-index-too-wide`) — a proof with a 2⁷⁰ divisor is legal input;
     the corpus has none. These are the `i64`-boundary stand-downs §7.3 warns
     must be read as "not covered".
   * **shadow-database bookkeeping** (`constraint-missing`,
     `db-lookup-outside-shadow`, `kernel-guard-refused`,
     `kernel-shadow-unavailable`, `shadow-id-out-of-range`,
     `shadow-slot-deleted`) — each marks a hole in the run-level composition
     (§7.4) rather than assuming a slot, so they surface on the `[compose]`
     row rather than the per-step skip line.
   * **reconstruction failures** (`implication-not-reconstructed`,
     `substituted-implication-not-reconstructed`, `rup-shadow-view-rejected`,
     `varform-flip-check-failed`, `hinted-constraint-not-normalized`) — the
     kernel could not reproduce what the live checker did. Unexercised means
     reconstruction currently succeeds everywhere in the corpus, not that it
     cannot fail.
   * **assumption-scoped RUP** (`rup-under-assumptions`,
     `rup-certificate-unavailable`,
     `substituted-implication-under-assumptions`) — a trail resting on
     subproof assumptions is not a trail the kernel's `PropTrail` models.

   The only honest way to shrink this list is to add instances that reach
   these branches, or to route the step into the proved fragment. Both are
   open work; deleting the literal is not a third option.

   **What this list is not.** Those four groups are *unexercised*
   literals — not *the* unexercised literals. They name 19 of the 32 the
   checker can print but the corpus never does (47 distinct reason strings
   exist in `veripb-checker/src/`; 15 of them the corpus produces). The
   thirteen unexercised literals the four groups omit are the four width
   names `constraint-not-i64-representable`, `factor-not-i64`,
   `formula-not-i64-representable` and
   `kernel-guard-refused-with-narrow-result` (§7.3), the four formula-load
   stand-downs `formula-file-unreadable`, `formula-file-not-rereadable`,
   `formula-second-reader-refused` and `formula-not-kernel-representable`
   (§7.4), the three compose flags `shadow-id-desync`, `shadow-stack-desync`
   and `shadow-slot-mismatch` (§7.4), `rup-reason-outside-shadow` (recorded
   just below), and `rule-not-kernel-justified`. Deriving the set is a grep,
   which is why an enumeration written by hand should be read as an
   illustration and not as a census.
   "The reasons the checker can print" is wider still: the corpus itself
   produces fifteen, and this item names only six
   of them (`red-witness-unmodelled`, `dom-unmodelled`,
   `checked-deletion-witness-unmodelled`, `obju-unmodelled`,
   `pbc-unmodelled`, `order-definition-unmodelled`, in the paragraph above).
   The other nine — `solution-exclusion-unmodelled`,
   `preserved-set-unmodelled`, `output-equivalence-unmodelled` and
   `assertion-unverified` (§7.3, unmodelled meta-steps);
   `strengthening-subproof-unmodelled`, `proofgoal-premise`,
   `scope-premise`, `checked-deletion-premise` and
   `order-proof-premise` (§7.4, boundary note 2) — are documented
   where the mechanism that produces them is, not here, because they are
   *how* the meta-rules of this item show up rather than additional scope
   gaps. Derive the live set with the §7.3 commands; the two together are
   not the whole census — see the thirteen named above.

   One literal is documented in neither place and is recorded here for
   completeness: **`rup-reason-outside-shadow`**, produced in
   `resolve_reason` (`veripb-checker/src/kernel_bridge.rs`). It is a taint only —
   never a counted skip — and it fires when a RUP reason cannot be resolved
   to a *present* shadow slot: the reason's own header names id 0 (the
   negated target, an autoproving-set premise) or a stale id the live entry
   no longer confirms, or the slot at that id has been deleted. The step is
   still kernel-verified against the live constraint; what it loses is its
   place in the run-level composition (§7.4). The corpus does not produce
   it.

6. **The parsers** — still outside the proved core, which takes a
   `Constraint` as given, but no longer *unchecked*. Under
   `--kernel-verify` the formula file is read a second time by
   `veripb-second-reader` — a crate whose only dependency is
   `malachite-bigint`, so a defect in `veripb-parser` or `veripb-formula`
   cannot reach it — and the constraints and objective the checker stored
   are compared against that reading, up to proved normalization and term
   order, before `DbOk.init` files a single slot. A mismatch is a
   `KernelDivergence`; a file the second reader cannot read is a counted
   skip, never a rejection. §7.4's boundary note 1 states exactly what that
   buys and what it still does not cover. The *proof* parser is untouched by
   this: a `pol` program or a `rup` constraint is read once, and the bridge
   checks what the rule did with it, not what the text said.

7. **Conclusion handling** — the arithmetic side is now covered: under
   `--kernel-verify`, stored contradictions are re-judged by the
   `checker_sound` hypotheses (at the mid-proof `qed` discharges too, §7.3)
   and logged solutions re-evaluated under the proved semantics
   (`holdsAllB` / `sat_of_witness`); accepted objective values are
   shadow-recomputed in exact arithmetic (a cross-check, not a kernel
   theorem — the kernel has no objective model). The bookkeeping (which
   conclusion kind is permitted when) remains ordinary Rust.

8. **The i128 guard's own exactness** — unchanged, and inherited by every
   slice-2 mirror (slack sums, normalization deltas): `i128` is exact for
   every value the checker can hold (at most `u32::MAX` terms of `i64`
   coefficients), but that claim is assumed, not proved.

   The blocker is narrower than this ledger used to say, and it is not the
   one it named. The clause fragment is no longer "`u8`–`u64` and `bool`":
   `i8`–`i64` joined it on 2026-08-23 (§4.1), which is exactly what made the
   `cap_coeff_i64` contract possible, and at *statement* level a clause over
   `i128`/`u128` elaborates fine. What is missing is the E6 kernel-**import**
   width table in `trust-certify` (`ty_to_domain` / `signed_machine_width`),
   which caps at 64 bits: with no import, `result` has no kernel denotation
   at `Wide = i128` and the postcondition cannot be bound to the function.
   So the residual trust step here is a *toolchain* gap at 128 bits, not a
   signedness gap, and separately an aggregate-**shape** gap (`Vec<Term>`,
   `Constraint`) that no width widening touches.

9. **The whole-crate compiler_consumer stage — LOST to the widening, now RESTORED, and
   the reason it was pinned lost was wrong.**
   The slice-1 ledger ended at item 8 because the only compiler_consumer measurement
   this project made was over `src/trust_surface.rs` as a standalone crate
   root. `8acd6022` widened that: with the toolchain ICE fixed, compiler_consumer
   compiled the *whole* crate — `lib.rs`, `normalize.rs`, `rup.rs`, `db.rs`
   and the island — under the historical advisory verifier mode,
   and `scripts/verify-proofs.sh` ran it as an obligation ratchet.

   Adding `malachite-bigint` for the `Big` tier (§7.2) ended that, and the
   stage was pinned unavailable. **It is enabled and gating again**:
   `wholecrate_ratchet=enabled` with `wholecrate_proved_floor=56` and
   `wholecrate_incomplete_ceiling=415`, measured 2026-08-24 at
   **exit 0, 0 errors, 56 proved / 471 obligations, 415 incomplete across
   109 functions**, with the island still kernel-checked inside the same
   compilation. For scale, the pre-widening ratchet in `8acd6022` was
   29 proved / 221 incomplete over a smaller crate.

   **The reason this file used to give was wrong, and the correction matters
   because it changes what would fix it.** It said compiler_consumer "cannot build the
   dependency". Measured 2026-08-24, compiler_consumer builds `malachite-bigint` and its
   entire dependency tree (22 rlibs) in about nine seconds:

   ```
   targo --unverified build --release -p veripb-core-proved
   ```

   What actually blocked the stage was that it was **one standalone
   `compiler_consumer src/lib.rs` invocation with no dependency build step**. Given no
   `--extern` the crate root is `E0433`; the only rlib on disk was cargo's,
   produced by stock rustc, and compiler_consumer refuses that one with `E0514` because
   the two compilers do not share metadata. Both diagnostics were real — they
   were symptoms of a missing build step, not of a missing capability.

   So the fix was neither a compiler change nor a `Big` tier behind a cargo
   feature. `scripts/verify-proofs.sh` now pre-builds the tree with compiler_consumer and
   threads the result through:

   ```
   targo --unverified build --release -p veripb-core-proved
   offline deductive checker check --release --allow-l0-gaps -p veripb-core-proved --features trust-surface
   ```

   The cost is that the stage now needs `targo` and a populated registry; when
   either is absent the pre-build is skipped, the stage falls back to the lone
   invocation, and the dormant `gate_wholecrate_unavailable` arm reports it.
   (The pre-build ran stock `cargo` with the explicit unverified lane until
   2026-09-28. `targo --unverified` passes that flag itself.)

   A **separate** lane — verifying the dependencies as well, which is what a
   plain `RUSTC=<compiler_consumer> cargo build` does, because trust verification is
   default-on in compiler_consumer — is still blocked, and not by anything in this
   repository. Three obstacles sit on it, measured 2026-08-24 in this order:

   * `proc-macro2`'s build script ICEd in `codegen_select_candidate`
     (`SignatureMismatch`) — a C-FLOW `dyn` case split handed
     `Instance::try_resolve` an unsatisfiable trait reference. **Fixed** in
     compiler_consumer the same day (`6845fd100d0`).
   * Behind it, `num-traits 0.2.19` ICEs in model-checker-consumer's CHC translator with
     `EQ requires same sort: (_ BitVec 128) and (_ BitVec 64)`. Open.
   * `ryu 1.0.20` exceeds the per-function verification budget (120 s /
     64 M steps) during VC generation of `pretty::format32`, which is a hard
     `error` that the advisory policy does not downgrade. Open.

   Under the default *strict* policy, third-party crates additionally fail
   outright with "Trust strict verification failed", which is expected: they
   are not written for Trust. That lane would verify third-party code this
   project does not own, and it is not what the ratchet ever measured.

   What was lost in the interval was a measurement, not a proof: the island
   lane (§4.1), the `clean check` pass and the exported bundle were untouched
   throughout, and nothing that was proved became unproved. What is back is
   the advisory coverage of `veripb-core-proved`'s non-island Rust — the
   executable kernel the checker actually runs — as a gating ratchet rather
   than a one-off measurement. It remains a ratchet, not a proof: 415 of its
   471 obligations are still open.

   **What the 471 measures, from reading all of them rather than counting
   them.** It is a Level-0 panic-freedom ratchet over this one crate's `Vec`
   plumbing, and its rise or fall is nearly uncorrelated with whether a rule
   is right. Not one of the 471 obligations concerns a coefficient or a
   degree: the rule bodies do their arithmetic through `Option`-returning
   guards (`C::narrow`, `checked_mul`), which generate no panic obligation,
   so every `ArithmeticOverflow` in the report is over `usize` lengths and
   capacities or inside the bare `<i128 as Exact>` shims. Of the 415 open,
   76 are runtime-checked (rustc's own check still fires), 305 are one
   tooling gap wearing many hats (`Vec`/`RawVec`/`HashMap` lowering shapes
   compiler_consumer cannot model yet), and 34 are refutations — of which the honest
   and load-bearing class is the i128 shims, whose functions really can wrap
   *in isolation* and are safe only by an argument about their callers
   (widened i64s, at most ~2^36 of them, against 60+ bits of headroom; every
   divisor checked before the shim). That argument is *tested*, with a
   negative control, in `tests/wide_arithmetic_headroom.rs`, and the hostile
   half of the refuted RUP-path bounds checks in
   `tests/hostile_certificate_indices.rs`. Of the 56 proved, the 27
   `trust_surface` citations are the graded ledger of §4.1; the other ~29
   are incidental (`i - 1` behind an `if i == 0` guard, slice bounds in core
   adapters). The seven `solver reported Proved without exact kernel/native
   proof authority` rows are the ratchet refusing to bank an unauthenticated
   "Proved", which is the fail-closed direction.

   The scope caveat that completes the picture: this crate is one of six,
   reached as a shadow cross-check behind `--kernel-verify` (off by
   default). The parsers, meta-rules and propagator that emit the default
   verdict carry zero obligations in any compiler_consumer lane, and twenty of the
   twenty-six fixed wrong verdicts lived in code this lane never sees. The
   ratchet is real and worth gating; it is not a verdict about the
   checker.

---

## 6. Known lemma-availability gaps in Clean (recorded for the next slice)

Encountered while writing the kernel; each forced a workaround that is now a
named lemma in the file:

| wanted | status | workaround |
|---|---|---|
| `Int.le_of_add_le_add_right` / `_left` | declared in-tree but **not registered** in the default environment | `VeriPbCore.le_cancel_right`, derived from `Int.add_sub_add_right` and the definition `Int.le a b ≡ Int.NonNeg (b - a)` |
| `Int.lt_of_add_lt_add_right` | same | restructured `le_of_mul_le_min` to avoid cancellation entirely |
| ceiling-division lemmas | absent upstream; **supplied in-tree** | a fuel-based Euclidean theory (`natDivMod`/`dmSpec`, `natCeilDiv`, `intCeilDiv`, `ceilQuotient_unique`, `entails_divide_concrete`; §3.3, §5 item 3). The abstract certified-quotient form is retained for the machine-width live path, not because a concrete `ceilDiv` is unreachable |
| `Int.min_le_left` / `le_min` | absent (only `Int.min`, `Int.min_def`) | own `capCoeff` + `capCoeff_le_degree` / `capCoeff_le_self` / `le_capCoeff` |
| `congrArg` rewriting the **left** argument of `Int.le` | mis-unifies (`Int.le x y` unfolds to `NonNeg (y - x)`, so `x` sits under a `neg`; higher-order unification picks the wrong pattern) | `le_congr_left` / `le_congr_right` via `Eq.subst` with an explicit motive |
| `Or.elim` | fails to elaborate with an implicit result type | `@Or.rec` with an explicit motive |
| struct literal inside a list/cons | needs a type ascription | `({ … } : Term)` |


---

## 7. Slice 2 — propagation, normalization, composition, and the live wiring

### 7.1 The Clean development (all in `veripb_kernel.lean`, 912 declarations)

**Foundation.** Decidable equality `litEqB` with soundness through kernel
structure-eta; trails as `List Lit` with `memB` membership and the semantic
predicate `Agrees`; databases as `List (Option Constraint)` — the exact shape
of the live checker's `Vec<Option<DBConstraint>>` including deletion holes —
with `getO`, `HoldsAllO`, `holdsAllO_get`.

**Slack and RUP.**

```
def slackTerms   (tr) (ts) : Int   -- sum of coefficients not yet falsified
def slackWithout (l) (tr) (ts)     -- ... with the terms on l also excluded

theorem evalTerms_le_slack        : AllNonneg ts -> Agrees a tr ->
    Int.le (evalTerms a ts) (slackTerms tr ts)
theorem propagated_lit_true       : AllNonneg c.terms ->
    slackWithout l tr c.terms < c.degree ->
    (models of c agreeing with tr set l true)
theorem no_model_of_conflict      : AllNonneg c.terms ->
    slackTerms tr c.terms < c.degree ->
    (no model of c agrees with tr)

inductive PropTrail (neg DB) : List Lit -> Prop   -- nil | step (checked)
theorem trail_sound               -- every model of neg :: DB agrees with the trail
theorem entails_of_rup            -- replayed conflict  =>  Entails F c
```

The engine's approximate watched-literal conditions imply these exact ones
(the watch slack is an upper bound on the true slack), so every trail the
engine produces on a real conflict replays — and a trail it got wrong is
rejected.

**Normalization.** `normC` as described in §5.4, built from `insTerm` /
`normIns` / `flipDrop` with the eval-preservation invariant
`evalTerms a (pass ts).ts + (pass ts).delta = evalTerms a ts`.

**Composition.**

```
inductive DStep (DB) : Constraint -> Prop
  | ax | lit | addS | mulS | divS | satS | wkS | rupS | trivS | normS
  | mirS | mirVarS                        -- normalized and variable-form MIR
theorem dstep_entails : DbEntailed F DB -> DStep DB c -> Entails F c
theorem dstep_div_concrete                -- divS at `intCeilDiv`, not a ctor

inductive DbOk (F) : List (Option Constraint) -> Prop
  | init | derive | delete
theorem dbOk_entailed : DbOk F DB -> DbEntailed F DB
theorem checker_sound : DbOk F DB -> getO DB i = some cc ->
    AllNonneg cc.terms -> Int.lt (coeffSum cc.terms) cc.degree -> Unsat F
```

**SAT leg.** `holdsB`/`holdsAllB` decide `Holds`/`HoldsAll`;
`sat_of_witness` makes an accepted solution a machine-checked
counterexample to unsatisfiability.

**The backward invariant, and why `DbOkF` could not supply it.** Everything
above runs FORWARDS: a model of `F` yields a companion model of the database,
which is what a refutation needs and all it needs. An `output` equivalence
verdict needs the other direction as well — that a model of the formula the
checker EMITS is a model of the formula it was GIVEN — and no forward leg
provides it, because the forward legs are free to lose models. `delete` is
the clear case: unconditionally sound forwards, and it drops a constraint the
emitted formula then no longer carries.

`DbBack F CO := forall b, HoldsAllO b CO -> HoldsAll b F` is that direction,
and it is monotone in exactly the opposite places:

| leg | forward (`DbOkF`) | backward (`DbBack`) |
|---|---|---|
| load | `init` | `dbBack_init` |
| add anything | needs a justification per rule | `dbBack_append`, **unconditional** |
| delete | `delete`, **unconditional** | `dbBack_delete_checked`, needs the obligation |

The asymmetry is the content. Adding a constraint strengthens the hypothesis,
so `red`, `dom`, solution exclusion and the assertion rules — every rule whose
constraint `F` need not entail — cost the backward invariant nothing. Deleting
one weakens it, and is the single leg carrying an obligation: the deleted
constraint must be implied by what remains, which is precisely VeriPB's
CHECKED deletion.

There is deliberately no unchecked-delete leg, and that absence is a claim,
not an omission: an unchecked deletion genuinely does not preserve `DbBack`,
so a run that performs one cannot support an equivalence verdict. The live
checker already agrees — `Context::strong_solution_guarantees` is cleared at
`rules/deletion.rs` when it falls back to unchecked deletion, and
`rules/output.rs` refuses `EQUIOPTIMAL`/`EQUISATISFIABLE`/`EQUIENUMERABLE`
without it (measured: a plain `del id 1;` on a core constraint followed by
`output EQUISATISFIABLE` is rejected with `ExpectedStrongerGuarantees`). What
changes here is that this guard is now underwritten by a theorem about the
invariant it protects, rather than by the warning text next to it.

`output_unsat_of_unsat` is the payoff, `output_unsat_forward` is its mirror
over the forward companion, and `output_equisat` states both directions
together in the shape a checker reaches them. The forward half is a separate
theorem rather than an inlined lambda for a reason worth recording: the
island's Clean elaborator does not delta-unfold `Unsat` when a lambda is
checked against it as an expected type mid-term, and rejected the inlined form
with `not a function type, but 2 argument(s) remain` — while `clean check`
accepted the identical term with zero failures. Two checkers, one
disagreement, and
this is the spelling both accept. (It also cost 36 compiler_consumer errors to diagnose,
35 of which were citation-taint cascade from the single real failure.) The two pairings
`idx` and `src` are the checker's own bookkeeping made explicit — for each
core slot, where that constraint sits in the output formula, and for each
output constraint, which database id the lookup found. Passing them as
FUNCTIONS rather than existentials costs the caller nothing (a checker that
verified "every core constraint is in the output formula" computed those
positions already) and keeps the backward half free of `Exists`.

**Both sides are pinned concretely.** A development whose central claim is
that a leg is ABSENT cannot be mutation-tested the usual way — there is no
code to perturb — so `F0`, the two-constraint control formula `x0 >= 1,
~x0 >= 1` already proved unsatisfiable by `ctrl_rup_refutation_end_to_end`,
carries both directions: `ctrl_dbBack_init_F0` shows the invariant holds at
the formula load (so it is not vacuously false), and
`ctrl_dbBack_fails_on_unchecked_delete` shows it fails across an unchecked
deletion (so the missing leg could not have been added). The second is
exactly the regression instance
`incorrect/version3/output_equisat_after_unchecked_deletion`, where the
all-true assignment models what the deletion left while `F0` it does not.

**Routed.** `offer_output_equivalence` discharges the theorem's hypotheses
from what the checker already computes. `DbBack F CO` needs no per-rule
evidence — `dbBack_init` at the formula load, then `dbBack_append` for
everything added since, both unconditional — so the whole invariant reduces
to *was a core constraint ever deleted?*, which is the single leg carrying an
obligation. `Database::delete_constraint` is the one funnel every deletion
goes through, and it already knows whether the constraint left the core (the
entry went, or it kept a derived id and lost its core one), so the bridge
counts exactly those. The pairing is recorded as `output` looks each
constraint up, then inverted; every occupied core slot must be a modelled slot
the output formula carries.

Over the corpus this turns a blanket `output-equivalence-unmodelled x10` into
**8 runs whose backward half the kernel underwrites** and 2 that decline as
`output-equivalence-core-deletion`. The gate is load-bearing, not decorative:
disabling the `core_deletions` check makes a core-deleting instance transfer,
which it must not.

**The forward half, and where it stops.** `dbOkF_companion` reads the
companion model straight out of the combined invariant: instantiate `DbOkF`
at `excls = []` and `bound = none` and the other two disjuncts are `Excluded
a []` and `BoundHolds _ _ none _`, both `False` by definition, so the
`Or` collapses. `output_unsat_forward_of_dbOkF` then closes the direction a
model of `F` yields a model of the emitted formula.

That instantiation is the honest boundary, not a technicality. A run that
EXCLUDED a solution or established a BOUND has deliberately dropped models of
`F`, and the forward transfer is precisely the claim that it did not — so
those runs get the backward half and a skip naming which of the two it was
(`output-forward-equivalence-solutions-excluded`,
`output-forward-equivalence-bound-established`). The two shadow counters are
those two kernel parameters: `excls` grows only on the `exclude` leg and
`bound` changes only on `improve`.

With both halves, `EQUISATISFIABLE` is claimed outright and such a run
reports **nothing outside the proved fragment** for its `output`. The other
guarantees claim strictly more than equisatisfiability — `EQUIOPTIMAL` an
objective the kernel has no model for, `EQUIENUMERABLE` a counting claim it
has no model for, `DERIVABLE` a derivability claim that is not an equivalence
at all — so they keep `output-guarantee-beyond-equisatisfiability`.

**Checked core deletion.** `dbBack_delete_checked`'s obligation is
`forall b, HoldsAllO b (setNone i CO) -> Holds b c` — over the CORE database
with the slot already emptied, not over the whole database, which would be a
strictly weaker premise and would not discharge it. `check_checked_deletion`
has three paths and only two of them prove that:

* the deleted constraint is still a core slot under another id, so
  `holdsAllO_get` gives `Holds b c` with nothing assumed; and
* it is RUP — and that check runs with `only_core = true`, *after*
  `delete_constraint`, so the database it refutes `~c` against is exactly
  `setNone i CO`.

Both already route through the bridge (`consume_db_lookup`,
`consume_rup_conflict`), so the obligation is kernel-re-derived rather than
taken from the checker's say-so. Two details are load-bearing and neither is
obvious. First, those two entry points record a SKIP and return `Ok` when the
kernel cannot re-derive the step, so *calling* them is not evidence that it
did — the credit is gated on the verified counter actually advancing.
(Verified by forcing the RUP re-derivation to skip: the deletion stops being
credited and the transfer declines, as it must.) Second, a discharge is
credited to the deletion it belongs to by snapshotting the count across
`delete_constraint`, so a derived deletion cannot borrow a core deletion's
credit; and a slot that was holed at deletion time is never credited, because
`getO CO i = some c` then names no kernel constraint.

The third path — a WITNESS subproof — is deliberately not credited. It
establishes satisfiability preservation through a substitution, which is a
different claim, and would need a `red`-shaped backward leg the kernel does
not have.

**The satisfiability-level invariant, and the leg `DbBack` cannot have.**
`DbBack` is POINTWISE: the same assignment that models the core models `F`.
Checked deletion preserves that because its obligation hands back the very
model it was given. A `red`-justified deletion does not, and cannot — its
witness produces a *different* assignment `applyA w b`, so there is no route
from "b models the core after the deletion" to "b models `F`".

What survives is the claim one level up, which is also the only thing an
`EQUISATISFIABLE` verdict needs: if `F` has no model then neither does the
core. `DbBackSat F CO := Unsat F -> forall b, HoldsAllO b CO -> False`,
stated contrapositively so the development stays free of existentials, exactly
as `DbSat` is. `dbBackSat_of_dbBack` means nothing already proved is lost by
working at this level, and `dbBackSat_delete_red` is the leg that only exists
here.

Its proof splits — decidably, through `holds_cases`, so no classical axiom
enters — on whether the given assignment already satisfies the deleted
constraint. If it does, `holdsAllO_restore` puts the slot back and the old
invariant applies to that same assignment. If it does not, the witness
supplies another one satisfying both the remaining core and the deleted
constraint, and `holdsAllO_restore` puts the slot back for *that* one. Either
way some model of the full core exists, which is all `DbBackSat` claims — and
precisely why the pointwise version fails.

The hypothesis shape matches what the checker discharges, which is checked
rather than assumed: a witness-carrying `del` runs its subproof with
`only_core = true` and asks
`get_proofgoals(.., add_derived_goals = false, only_core_subproof = true, ..)`,
so its goals are over the core database with the slot removed — which is
`setNone i CO`.

`offer_red_deletion` routes it, checking the two conjuncts of `hgoal`
separately: the deleted constraint's own goal must be the kernel's image of
it, and every remaining CORE slot must either be provably untouched by the
witness or carry a discharged goal that is the kernel's image of that slot.
Restricting to core slots is not a convenience — `CO` holds derived
constraints as `none`, so they raise no obligation, and the checker agrees by
generating these goals with `add_derived_goals = false`. A derived slot the
witness moves is therefore correctly ignored, where the same slot under `red`
would have had to be dropped and holed. Both guards are mutation-verified:
forcing the skip census to look dirty, and mispairing the deleted
constraint's own goal, each make the instance decline.

**Where this leaves the census.** The ten original
`output-equivalence-unmodelled` skips are now three runs fully inside the
proved fragment and eight carrying a specific named reason: 4
bound-established, 2 beyond-equisatisfiability, 1 solutions-excluded, and 1
core-deletion-not-discharged. That last one is no longer a `del` rule at all:
its core deletion comes from subproof TEARDOWN, where the constraints a
subproof added are removed at `qed`. Cancelling an append against its own
later deletion needs a scope discipline in the invariant that the current
legs do not express. Instances reporting nothing outside the fragment: 277 of
311.

### 7.2 The Rust mirrors

Every mirror below is written **once**, generically over the coefficient
domain, and instantiated twice (`lib.rs`, `CoeffDomain` / `Exact`):

| domain | storage | exact width | `narrow` (the width guard) | mirrors |
|---|---|---|---|---|
| `Coeff` = `i64` | one machine word | `Wide` = `i128` | `fitsI64` — **can fail** | the Clean statements *plus* their width side conditions |
| `Big` = `malachite_bigint::BigInt` | arbitrary precision | itself | `Some`, always | the Clean statements **verbatim** |

The Clean development is stated over unbounded `Int`, so the `Big`
instantiation is the *more* faithful mirror of the theorems, not the less: it
has no width hypothesis to discharge because the theorems have none. The
`i64` instantiation is the fast one, and it is where `fitsI64`/`eqOkB` have
content — a value must land in a machine word, and the guard is the
obligation that it did. Because both instantiations execute the same rule
bodies, an audit of a rule is an audit of both; the only per-domain code is
the two `CoeffDomain` impls, a few lines each. `cap_coeff` is untouched by
the generic form: `<i64 as CoeffDomain>::cap_coeff` delegates to it, so
SATURATE at the narrow domain still runs the very function §4.1's
compiler-checked contract is about.

`Big` is the crate's only dependency, and it is the same integer type
`veripb-formula` already computes the live checker's constraints in, so it
adds no package to the lockfile and no algorithm to the trust surface — only
the integers themselves. Trusting `malachite` to implement `Int` is strictly
weaker than the alternative it replaces, which was trusting that no value
ever exceeds `i64`.

**It did cost something, and the cost is not in the lockfile.** Before the
widening, `veripb-core-proved` had *no* dependencies at all, and that is what
let `scripts/verify-proofs.sh` run compiler_consumer over the **whole crate** — `lib.rs`,
`normalize.rs`, `rup.rs`, `db.rs` and the island together — under
the historical advisory verifier mode, as an obligation ratchet
(added in `8acd6022`, which reported 29 proved / 221 incomplete). That stage
was one standalone `compiler_consumer src/lib.rs` with no step that builds a dependency,
so it stopped at the crate root: `E0433` with no `--extern`, and `E0514` if
handed cargo's rlib, which stock rustc produced. It was pinned unavailable
for a while, and **the reason recorded then — that compiler_consumer could not build the
dependency — was wrong.** compiler_consumer builds `malachite-bigint` and its whole tree
in about nine seconds under `RUSTC=<compiler_consumer> cargo build`; what was missing was
a build step, not a capability.

That step now exists: the script pre-builds the tree with compiler_consumer and passes
the rlib as `--extern`, so the stage is `wholecrate_ratchet=enabled` again and
gates at 56 proved / 471 obligations, 415 incomplete across 109 functions.
§5 item 9 carries the commands, the full measurement, the price (the stage now
needs `cargo` and a populated registry), and the separate obstacles that still
block *verifying the dependencies too*. Nothing that was proved became
unproved at any point — the island lane (§4.1) and the bundle were untouched
throughout.

| module | mirrors | note |
|---|---|---|
| `lib.rs` | the rules, plus the ambient `Int` | `CoeffDomain` (storage + its exact width + the guarded narrowing between them) and `Exact` (`Int.add`/`Int.sub`/`Int.mul`/`Int.neg`/`intFloorDiv`/`intFloorMod`/`capCoeff`); `guard::fits_i64` / `guard::eq_ok` stay unparameterized, being *about* a machine word |
| `normalize.rs` | `normC` | merge/flip at the domain's exact width, guarded narrowing; term order pinned to the Clean fold so the `ctrl_norm_*` values match literally |
| `rup.rs` | `PropTrail` / `entails_of_rup` | `check_rup(target, db, steps, conflict)` replays a trail; every step re-checks the kernel hypotheses at the domain's exact width. At `Big` the slack folds are exact for every constraint the *live checker* can hold, which is what lets the bridge re-judge a promoted constraint instead of standing down at it |
| `db.rs` | `DStep` / `DbOk` / `checker_sound` | a stand-alone driver: `Op` trees evaluated through the guarded rules only. The mapping is one-way — every `Op` variant has a `DStep` constructor, but `mirS`/`mirVarS` have no `Op`, so a MIR step is covered by `checker_sound` yet cannot be replayed through this driver |
| `mir.rs` | `entails_mir` / `entails_mir_variable` (via `intFloorDiv`, `intFloorMod`, `mirF`, `vfMirTerms`) | both MIR forms, computed at the exact width and narrowed once per value; each theorem hypothesis is a guard and each produced value is re-checked (`intFloor_spec`, `intFloorMod_nonneg`/`_lt`, `mirF_nonneg`). A zero remainder is `GuardError::MirZeroRemainder`, not a refusal: the rule has no content there and the caller derives the trivial constraint. Pinned against `ctrl_ifd_*`, `ctrl_ifm_*`, `ctrl_mirF_*`, `ctrl_mir_5_3_*` and `ctrl_vf_*` by `mir_matches_the_clean_controls` |

`tests/width_guards.rs` pins the relationship between the two: every rule
that refuses at `i64` on a width boundary *fires* at `Big`
(`every_rule_that_refuses_on_width_fires_at_the_complete_domain`), computes
the value the wrap would have destroyed
(`the_complete_domain_computes_the_value_a_wrap_would_have_destroyed`), and —
randomized over all nine rules the bridge instantiates at both tiers
(ADD/MULTIPLY/DIVIDE/SATURATE/WEAKEN/NEGATE/NORMALIZE and the two MIR forms,
the latter composed with `normalize` because that is how `shadow_mir`
dispatches them) — agrees with the narrow domain everywhere the narrow
domain accepts (`the_two_domains_agree_wherever_the_narrow_one_accepts`),
with a per-rule floor on both the accepting and the width-refusing arm so a
rule cannot quietly stop being generated.

What makes the two-tier dispatch safe is the **dispatcher**, not that test:
`tiered_step` is `let first = narrow()?; match first.check { Some(r) if
width_limited(r) => wide(), _ => Ok(first) }`, so a narrow `KernelDivergence`
never reaches the wide closure and a narrow verdict is escalated only when it
was a width-limited *skip*. Replaying a tier up can therefore add coverage
and never change a verdict the narrow tier already reached, for all nine
rules, and each tier is independently sound. The randomized test is the
regression guard that the two instantiations of a rule cannot drift apart —
which is a different claim, and the one MIR was missing.

### 7.3 `--kernel-verify`: the wiring into the live checker

`veripb --kernel-verify` cross-checks the live checker against the kernel
*while it runs* (`veripb-checker/src/kernel_bridge.rs`):

- **The formula load**: the formula file is read a *second* time, by
  `veripb-second-reader`, and the constraints (and objective) the checker
  stored are compared against that reading. This is the only check here that
  is not about an inference — it is about the *input* — and it is what makes
  the `F` of `DbOk.init` the bytes on disk rather than the parser's opinion
  of them (§7.4, boundary note 1).
- **pol**: every instruction sequence is replayed on a shadow stack of
  kernel constraints kept in proved normalized form (so the per-term rules
  SATURATE/DIVIDE see the same merged view the live code does); the final
  constraint must agree with the live result up to proved normalization and
  term order.
- **RUP**: every engine conflict is captured as a `KernelCertificate`
  (trail + reasons + conflict, taken before the trail unwinds) and replayed
  through `rup::check_rup`. All seven engine acceptance sites funnel through
  one shared *implementation* (`rup_conflict_outcome`), reached by two thin
  wrappers: the discharge form `consume_rup_conflict`, for acceptances that
  decide a goal without storing anything (checked deletion, the two proofgoal
  RUP discharges, the two top-level subproof discharges — five sites), and
  the deriving form `consume_rup_derivation`, which additionally feeds the
  shadow database (the `rup` rule, `red` strengthening's RUP shortcut — two
  sites). Hinted RUP carries no engine certificate: it is re-propagated over
  exactly the hinted constraints with the kernel's decidable conditions
  (`consume_hinted_rup`), and is not one of the seven.
- **Verdicts**: stored contradictions are re-judged by the `checker_sound`
  hypotheses — at the mid-proof subproof/proofgoal `qed` discharges that
  decide red-step subproofs (whose constraints are deleted at `qed`, so
  conclusion-time re-judging could never cover them) as well as at
  conclusion time; accepted solutions are re-evaluated under the proved
  semantics.
- **Trivial and DB-lookup accepts**: every trivial discharge (proofgoal
  `Trivial`, autoproved order reflexivity) is re-judged by proved
  normalization + degree at most zero (`entails_trivial`); every "equals a
  database constraint" accept (proofgoal `DBLookup`, the red/pbc/checked-
  deletion DB shortcuts, the `e`/`ea` rule, the `output ... FILE`
  constraint-set check) is re-judged by equality of the two proved normal
  forms.
- **Obligations proofgoal *generation* discharges**: `red`, `dom` and
  checked deletion do not turn every touched database constraint into a
  goal. Four things can happen instead, and all four are acceptances:
  the substituted form is trivially true; the original constraint implies
  it; an equal constraint is already in the database (all three inside
  `add_non_obvious_proofgoals`); or the constraint carries a literal the
  witness *satisfies*, in which case it is never even collected, on the
  unstated weakening argument `C |= C|w`. Those are the same acceptance
  shapes as the explicit `Trivial` / `DBImplies` / `DBLookup` proofgoal
  discharges, so they are routed back through the same entry points
  (`kernel_bridge::consume_autodischarge`) and land in the same counters.
  Without that routing they would be a whole class of accepts — 69 of them
  on the shipped corpus — that the summary line never mentioned. Collecting
  them costs a `substitute()` per witness-satisfied constraint, so it is
  gated on the flag.
- **Substituted-implication accepts** (proofgoal `DBImpliesSubstituted`):
  the accept "a database constraint, simplified under the propagated
  assignment, implies the simplified goal" is re-derived end to end. Every
  trail literal the acceptance consumed is certified as a kernel trail
  certificate through `rup::check_rup` (unit target `1·l >= 1`, negated at
  view index 0, the engine-trail prefix as steps, the literal's own reason
  as the conflict — `entails_of_rup`; the reasons are database constraints
  plus the autoproving premises, the same licensing as the RUP
  certificates); the substitution is modelled by proved adds of those
  scaled units and trivial axioms (`entails_multiply`, `entails_add`,
  `entails_trivial`, `normC` equivalence); the residual implication closes
  through the same proved chain as the syntactic-implication accepts, and
  the reconstruction must land exactly on the goal's proved normal form
  (`entails_of_normC_eq`).
- **Objective values**: every accepted objective value (`sol`/`soli`, the
  `BOUNDS` upper-bound leg) is *shadow-recomputed* in exact arithmetic —
  `i128` while the objective stays inside `i64` coefficients, `BigInt` from
  the first coefficient that does not — plus the `BigInt` constant. This is a
  cross-check, not a kernel theorem: the kernel has no objective model (§5,
  item 5).

**Every one of these checks runs at two coefficient tiers.** The live
checker promotes its own arithmetic from `i64` to `i128` to `BigInt` as
values grow; a kernel that stood down at `i64` therefore stood down exactly
where the live checker had just promoted, which is where two of the three
wrong verdicts an adversarial review found were living. Each entry point in
`kernel_bridge.rs` is now a thin dispatcher (`tiered_step` /
`tiered_outcome`) over a generic `_at::<C>` body: it replays at
`Tier = i64` — the fast path, and what essentially the whole corpus takes —
and, **only when that pass stood down for a width reason** (`width_limited`),
replays the same step at `Tier = Big`, where nothing refuses on width.

Two properties make this safe rather than merely broader:

* A *divergence* reported by the narrow pass is returned immediately and is
  never re-litigated. The narrow tier only reports one after computing every
  value exactly (in `i128`) and passing every guard, so its disagreement with
  the live checker is real. The second pass exists for the opposite case —
  the narrow tier could not compute at all, so it had nothing to disagree
  with.
* Where both tiers compute, they compute the same constraint (§7.2, the
  randomized agreement test), so the retry cannot turn a narrow "verified"
  into a wide "skipped" or vice versa.

The shadow database spans both tiers in one id space (`AnyConstraint`): a
slot is narrow unless the constraint the live checker stored genuinely does
not fit a machine word, and a wide-tier derivation whose result *does* fit is
filed narrow again, so one wide constraint does not make every downstream
step wide.

Divergence is a hard checking error (`KernelDivergence`): the two
implementations disagree on a soundness-critical step, so the proof is
rejected rather than trusted. A step the kernel cannot express — or a rule
it does not model at all — is **counted and reported** in an end-of-run
summary line, never silently trusted. The reasons fall into six categories:

* **width refusals** — a coefficient, degree, factor, divisor or weakening
  amount outside `i64` (`constraint-not-i64-representable`,
  `result-not-i64-representable`, `factor-not-i64`, `divisor-not-i64`,
  `amount-not-i64`, `objective-not-i64-representable`), or a variable index
  outside `u32` (`variable-index-too-wide`). Only the `u32` half is a real
  stand-down now: the `i64`-named reasons are produced by the *narrow* tier,
  and a step that reports one is immediately re-checked at `Big`, so it
  reaches the census only if the wide tier also gave up. None of them
  appears in `tests/kernel_verify_expected.txt` any more.

  **Two of those names are misnomers, and the reader has to know which.**
  `Big` holds every coefficient a live constraint can hold, so no
  *coefficient* survives the retry — but `to_kernel` narrows the whole
  constraint, terms included, and `kernel_lit` fails on a variable index
  above `u32`. A wide variable index therefore reaches the census under
  `constraint-not-i64-representable` (per step) and
  `formula-not-i64-representable` (as a formula-load taint, §7.4), neither of
  which mentions a variable index, while `variable-index-too-wide` — the name
  that does — is *not* what those paths print. So a surviving
  `constraint-not-i64-representable` should be read as "a variable index the
  kernel cannot represent", never as "a coefficient too large": the latter
  is impossible after the widening. The two names are on the list to be
  corrected; correcting them means moving the string literals in
  `kernel_bridge.rs`, re-blessing `tests/kernel_verify_expected.txt`, and
  updating the derivation commands below, so it is a change to make
  deliberately rather than in passing;
* **guard refusals** — a value the live checker accepted that a kernel guard
  rejects (`kernel-guard-refused`), split from the case where the live
  checker's own *result* fits `i64` although the kernel's exact replay left
  that range (`kernel-guard-refused-with-narrow-result`). Both names survive
  the widening, and both are retried at `Big` before being counted, which
  sharpens what a surviving one means: at the complete domain no rule refuses
  on width, so `kernel-guard-refused` in the census is now a genuine
  *hypothesis* failure — a non-positive factor or divisor, a quotient that is
  not the ceiling, a constraint that is not `AllNonneg` — and not a machine
  word running out. A derivation that legitimately dips outside `i64` and
  comes back (multiply then divide) is verified at the second tier instead of
  counted, which is why `version3::kernel_verify_guard_refused_narrow` no
  longer reports the reason it was written to pin;
* **unmodelled meta-steps** — the remaining machinery the kernel has no model
  for (`obju-unmodelled`, `preserved-set-unmodelled`), the model-preserving
  rules whose added constraints are satisfiability-preserving rather than
  entailed and so break the `DbEntailed` invariant `checker_sound` rests on
  (`solution-exclusion-unmodelled` for `sol`/`solx`/`soli` and `obji`,
  `preserved-set-unmodelled` for `preserved_add`/`preserved_rm`/
  `preserved_set_equals`), the `output` rule's formula-level equivalence
  claim (`output-equivalence-unmodelled`; its per-constraint database
  lookups *are* re-judged, it is the licence that is unmodelled), and
  assertions, which are axioms-by-fiat with no proof obligation
  (`assertion-unverified`);
* **reconstruction failures** — a step the kernel could not reproduce in a
  shape it can justify (`rup-shadow-view-rejected`,
  `varform-flip-check-failed`);
* **shadow-database holes** — a run-level slot the composition cannot
  account for (§7.4);
* **formula-file stand-downs** — the second reading of the formula file
  could not be made (`formula-file-unreadable`, or
  `formula-file-not-rereadable` when the path does not denote the same bytes
  twice — a FIFO, a process substitution's `/dev/fd/N`, or on macOS any
  `/dev/fd/N` at all, whose `open` dups the descriptor the checker already
  read to the end instead of reopening the object) or could not be decided
  (`formula-second-reader-refused` when the independent reader will not read
  the file under its own plain reading of the format,
  `formula-not-kernel-representable` when the kernel cannot hold a
  constraint at either tier, which after the cross-check's own dense
  variable numbering means over `u32::MAX` distinct variables). Each is
  counted **once for the run** as a *skip*, not once per constraint: what
  stood down is the whole comparison. What is counted per constraint is the
  *taint* it leaves — a stand-down holes every formula slot, §7.4 boundary
  note 1 — so the same event shows as `x1` in the skip list and as `xN` in
  the taint census, and that is not a discrepancy. None appears in
  `tests/kernel_verify_expected.txt`.

  **`dom` and the order machinery are no longer on that list, and the
  distinction is between MODELLED and ROUTED.** `VeriPbCore.DbOkF` has a
  dominance leg and `full_complete`/`full_unsat` cover it. Three pieces got it
  there:

  - **Descent.** `red` requires the witness to SATISFY the constraint being
    added; `dom` requires no such thing, only that the witness strictly
    decrease a measure. So the argument iterates: a model of the database
    either satisfies the new constraint already, or the witness hands back one
    that still models the database and measures strictly less. A decreasing
    sequence of naturals must stop (`dom_companion`, stated with an explicit
    bound so it is ordinary induction rather than well-founded recursion).
  - **The measure.** A VeriPB order is a RELATION, not a rank. The bridge is
    counting: the rank of `x` is how many indices are strictly below it.
    Transitivity makes "below `y`" a subset of "below `x`", irreflexivity
    makes it a PROPER subset, and a proper subset of a finite set is strictly
    smaller (`rankOf`, `rank_lt_of_rel`). Well-foundedness is `Nat`'s, assumed
    nowhere. Finiteness is not smuggled in: `load_order` fixes a finite
    variable list, so behaviour under the order is fixed by the restriction to
    those.
  - **The hypothesis.** `rank_lt_of_rel` wants transitivity AND
    irreflexivity; `def_order` proves transitivity and REFLEXIVITY. The
    mismatch is only apparent. `Order::get_proofgoals_strict` emits the
    definition twice — once saying `w(a) <= a`, once at the opposite scope
    saying NOT `a <= w(a)` — so what a `dom` step discharges is the STRICT
    PART of the preorder, and the strict part of a transitive relation is
    transitive and irreflexive for free. `dbOkF_dom_from_preorder` therefore
    takes ONE hypothesis about the order, and it is the one the format
    supplies.

  What is NOT done is routing: the bridge must still supply the relation, the
  index map and the bound from the `def_order` block, and check that the
  transitivity subproof was kernel-discharged. `dom-unmodelled` and
  `order-definition-unmodelled` are still counted, and this file will keep
  counting them until that lands. The difference is that it is now plumbing
  against a settled theorem rather than a missing one.

  **`red` is no longer in that list, and the distinction matters.** The RULE
  is proved: `VeriPbCore.dbOkR_red_of_goals` states redundance-based
  strengthening over exactly the proofgoals a checker discharges, resting on
  the substitution lemma (`evalTerms_applyA`, `holds_substC`) and on a
  database invariant weakened from entailment to satisfiability preservation
  (`DbSat`, `DbOkR`, `checker_sound_red`) — because `red` genuinely does not
  entail what it adds. `veripb-core-proved/src/subst.rs` is the Rust image of
  `substC`.

  What is NOT done is ROUTING: the bridge still records
  `red-witness-unmodelled` and the corpus census is unchanged. The step that
  remains is accounting, not mathematics. `dbOkR_red_of_goals` asks about
  EVERY database slot, while real proof formats emit goals only for the slots
  the witness touches, so the bridge must re-check the rest with
  `subst::subst_c_is_identity` rather than assume the omission was safe. Until
  that lands, this file must not claim `red` is covered end to end.

The first category used to be the load-bearing one, and the reason is worth
recording because it is what the two-tier dispatch closed. The proved
fragment was **`i64`-only**: `to_kernel` narrowed by *value*, so an
`i128`-typed constraint whose values happened to fit was verified normally,
but a step whose values genuinely exceeded `i64` was one the shadow could not
represent at all and the whole cross-check stood down for it. That is exactly
the tier where the live checker's width defects live, so the stand-down was
not a rounding error — it was a hole the size of the defect class. Measured
against the pre-fix binary at `443f8abb`, `--kernel-verify` *missed* eight of
the eleven degree-wrap and watcher-slack regression instances, reporting
`s VERIFIED UNSATISFIABLE` on satisfiable formulas with nothing worse than a
counted skip in the summary.

Closing it did **not** need a wider guard predicate in Clean. The Clean
theorems are already stated over unbounded `Int`; it was the Rust mirror that
had narrowed them. Instantiating the same rules at `Big` (§7.2) mirrors those
statements with no width side condition at all, and the bridge replays there
whenever the narrow tier stands down. No single commit carries both the
defects and the widening, so the comparison needs a build that has to be
constructed — `90d5acf5` with `git revert --no-commit 70229b7a` and the
now-dangling `saturating_neg` re-export dropped from
`veripb-formula/src/prelude.rs`; README's "Wrong verdicts fixed" gives the
recipe. Against that build all eleven
instances report `KernelDivergence`. On the shipped corpus the
width-related skips and shadow taints are gone entirely — 10 skips and 7
taints, down to zero — and `version3::kernel_verify_wide_coefficient` (a
`2^64` coefficient) and `version{2,3}::multiplication` (a `10^56` factor),
which previously pinned the boundary, now report `nothing outside the proved
fragment` with an empty taint census in `tests/kernel_verify_expected.txt`.
All three end in `conclusion NONE;`, so their `kernel-compose:` line reads
`no refutation conclusion to compose` before and after alike: the widening
removed their holes, it did not give them a run-level certificate, and no
coefficient domain could — composition needs a refutation conclusion to
certify. "Composed" is reserved throughout this document for a run whose
`kernel-compose:` line literally begins `COMPOSED` (§7.4).

What remains outside is the part that is not about coefficient width at all:
a variable index above `u32` and the unmodelled meta-rules of the third
category.

**The wide-variable-index stand-down is now unreachable, and this paragraph
has been wrong about it twice in opposite directions.** It first claimed the
condition could not be reached at all; it was then corrected with a runnable
two-line recipe that did reach it, through `--lenient-header-counts`:

```bash
printf 'p cnf 2 1\n4294967300 0\n' > wide.cnf
printf 'pseudo-Boolean proof version 3.0\nf 1;\npol 1 1 +;\noutput NONE;\nconclusion NONE;\nend pseudo-Boolean proof;\n' > wide.pbp
veripb --kernel-verify --lenient-header-counts wide.cnf wide.pbp
```

That recipe no longer produces a verdict. `MAX_DENSE_VAR_IDX`
(`veripb-formula/src/var_type.rs`), added later for an unrelated
denial-of-service reason, refuses any variable index above `2^27` in the CNF
parser, unconditionally and before `--lenient-header-counts` is consulted, so
the run above now exits **1** with

```
Error: wide.cnf:2: variable index 4294967300 exceeds 134217728, the largest variable
index this checker builds a dense variable space for! …
```

and no `kernel-verify:` or `kernel-compose:` line at all. The two windows do
not overlap and cannot be made to: `kernel_lit` stands down only for an index
above `u32::MAX`, and the parser refuses everything above `2^27`, which is 32x
smaller — so no smaller index repairs the recipe, and a variable *named* in
proof text cannot have a wide index either, because `VarNameManager` hands out
indices sequentially. **No input can now exhibit this stand-down through a
formula file.** The honest statement is therefore the strong one rather than
the weak one: it is not that no input has yet been found, it is that the
parser closes the only route.

What survives from the corrected edition is the observation it was offered as
evidence for, which is about the code rather than about that run:
`variable-index-too-wide` is not the literal these paths print. The CNF parser
is the one place a `Lit` is built from the file's own index rather than from
the name table, so a wide index would be stored as such and `to_kernel` would
fail on it in `kernel_lit` — and the two paths that report that failure are
named after `i64` instead (`constraint-not-i64-representable` per step,
`formula-not-i64-representable` on the formula-load slot). See the misnomer
note in the width-refusal bullet above. `variable-index-too-wide` itself is
reachable only from paths the corpus does not take (§7.4 and the note below on
`Proofgoal::autoprove`).

The same goes for §5 item 5's width group: the corpus exercises none of them,
but that is a property of the corpus, not of the inputs the checker accepts.

This document deliberately does **not** pin the exact literal set: it moves
with the bridge, and a frozen list here would rot into a claim about
coverage the code no longer has. The authoritative set is the string
literals in `kernel_bridge.rs` and the rule files that call it; derive it
with

```bash
grep -rhoE '"[a-z0-9]+(-[a-z0-9]+)+"' veripb-checker/src | sort -u
```

That is a *vocabulary* grep, matched deliberately on the literal alone
rather than on the call that carries it. An earlier version of this command
anchored on `(\.skip|::skipped|Err|Some)\("…"\)`, and two things went wrong
with it, both worth stating because they are the failure modes of any
derivation printed in a document. It missed
`kernel-guard-refused-with-narrow-result`, whose `StepOutcome::skipped(…)`
call `rustfmt` had split across lines — so a pure-formatting commit silently
invalidated a measurement whose entire purpose was to be re-derivable. And
it reached only the per-step skips, never the shadow-database taint reasons
(`Slot::Hole`, `break_composition`, the `kernel_slot_taint()` overrides in
the rule files), which is a whole second family. Today the unanchored form
over-matches nothing: every kebab-case string literal under
`veripb-checker/src` is a reason.

The reasons the corpus actually *produces* come from the blessed snapshot,
in two families that do not coincide — counted skips on the coverage line:

```bash
grep -o 'outside the proved fragment: .*' tests/kernel_verify_expected.txt \
  | sed 's/outside the proved fragment: //' | tr ',' '\n' \
  | sed 's/ x[0-9]*//;s/^ *//' | sort -u
```

and shadow taints on the `[compose]` line (§7.4):

```bash
grep -o 'recorded over the run: .*' \
  tests/kernel_verify_expected.txt | sed 's/.*run: //' | tr ',' '\n' \
  | sed 's/ x[0-9]*//;s/^ *//' | grep -v '^none$' | sort -u
```

Append `| wc -l` for the counts. They are not printed here: they move with
every bridge change and every corpus addition, and a figure frozen in this
paragraph is exactly what rotted last time. Run the commands.

What *is* stable, and is the point of the census: after the widening no
width-related literal is produced at all. `constraint-not-i64-representable`,
`factor-not-i64` and `kernel-guard-refused-with-narrow-result` used to
appear and no longer do, and grepping the snapshot for any of the width
group in §5 item 5 finds nothing. The literals that remain unproduced are
retained on purpose; §5 item 5 says which and why. Note in particular that
`substituted-implication-under-assumptions` is a defensive guard with no live
path from `Proofgoal::autoprove`, so its absence from the corpus is not a
coverage gap.

`variable-index-too-wide` is a harder case and the honest statement is
narrower than "unexercised". It guards four sites — `pol` weakening, the
`pol` literal axiom, the RUP certificate's trail literals, and the
substituted-implication trail — and every one of them needs a `Lit` whose
variable index exceeds `u32::MAX`. A variable *named* in proof text cannot
have one: `VarNameManager::add_by_name` hands out indices sequentially, so
`x4294967300` in a `.pbp` is whatever small index the name table next has
free. The only source of a genuinely wide index is a DIMACS CNF file, where
the stored index *is* the file's index (§7.4's formula-load row), and on
that route the constraint carrying the index is already a hole or already
fails `to_kernel`, so what the run would print is
`constraint-not-i64-representable` — the misnomer above. And that route is
closed as well: `MAX_DENSE_VAR_IDX` refuses any index above `2^27` in the CNF
parser, 32x below the `u32::MAX` the guard needs, unconditionally and before
`--lenient-header-counts` is consulted (§7.3). So the statement is not "no
input has yet been exhibited" but the stronger one: **no accepted input can
reach these four sites at all today.** The guard stays because it is the
unconditional backstop for a parser bound that is one line and documented as
raisable, not because anything currently exercises it.

`tests/kernel_verify.rs` runs the complete corpus (both proof versions,
correct and incorrect instances) and asserts the flag is verdict-neutral.

### 7.4 Run-level composition: the shadow database

Everything in §7.3 re-derives *one step*. A run of a thousand verified
steps still only says "each of these inferences was correct" — it does not
say the run proved anything, because nothing ties the steps to each other or
to the formula. `--kernel-verify` closes that gap with a **shadow
database** (`KernelShadowDb` in `kernel_bridge.rs`): a `Vec` of slots
mirroring the live `Database`'s id space one for one, mutated only through
kernel-justified operations.

| live event | shadow | licensed by |
|---|---|---|
| formula load | slot `i` := `normC` of the stored constraint `i`, **after** the stored formula is checked against a second, independent reading of the file | `DbOk.init` / `dbEntailed_init`, then `entails_normC`; that `F` is the file is a cross-check, not a theorem (boundary note 1) |
| a derivation the bridge re-derived **from present slots** | slot := the kernel constraint the replay produced | `DbOk.derive`, via `dstep_entails` on that step's own `DStep` witness |
| any other addition | unjustified slot naming the reason | — (nothing is claimed) |
| deletion | slot := empty, **not** a taint | `DbOk.delete` (`setNone`) |
| order definition swaps the database | outer slots pushed on a stack; the sub-database mirrored from empty; popped on the way out | — (structure, not a rule) |

The formula-load row has a failure case, and it is the only taint that can
exist before a single rule has run: a stored constraint the kernel's domain
cannot hold gets a hole named `formula-not-i64-representable`. The name is
now a misnomer and is on the list to be corrected — after the two-tier
widening (§7.3) no *coefficient* can fail here, `Big` holding everything a
live constraint can, so the only way to reach it is a variable index above
`u32`, which is the same condition `variable-index-too-wide` names
elsewhere. **No exhibited input reaches it.** The corpus produces it nowhere,
and the two-line DIMACS file §7.3 used to offer as a witness stopped working
when `MAX_DENSE_VAR_IDX` closed that route in the parser (§7.3) — this row
therefore has no witness at all, which is worth stating plainly rather than
leaving a stale recipe standing in for one.

The invariant every present slot carries is the one `dbOk_entailed`
establishes for a `DbOk` database, pointwise: `Entails F c`. When a
refutation conclusion (`UNSAT`, an infeasible lower bound, a complete
enumeration) is accepted at id `i`, the bridge checks `slots[i]` against the
`checker_sound` hypotheses — present, `AllNonneg`, coefficient sum below the
degree. If they hold and the shadow mirrored the id space without a desync,
the **whole run** is certified: `Unsat F`. That verdict is printed as a
second summary line:

```
kernel-compose: COMPOSED: the contradiction at id 8 certifies the whole run through
DbOk/checker_sound over the stored formula; 9 slot(s) in the live id space,
0 unjustified slot(s) and 0 subproof premise(s) recorded over the run: none
kernel-compose: NOT composed (no kernel-justified slot at id 24: solution-exclusion-unmodelled);
25 slot(s) in the live id space, 3 unjustified slot(s) and 0 subproof premise(s) recorded over the run: solution-exclusion-unmodelled x3
```

The slot count is the current database's; the taint census is run-wide, so it
also counts holes in order sub-databases that have since been swapped back
out and can exceed the slot count.

Composition is **per-slot, not global**: a hole taints only the slots that
consume it. A `red` step deep in a proof does not erase the composition of
an unrelated branch — but it does make every constraint derived from it a
hole, transitively, so a hole anywhere upstream of the contradiction means
the run is not composed and the summary says so. (The census therefore
counts each hole under its *root* reason, which is why a reason can appear
more often than the steps that introduced it.)

**Strengthened leaves.** Composition makes it worth asking not just "is this
a valid inference?" but "is it an inference from *this database*". So a
`pol` `ConstraintId` leaf and a RUP reason are replayed as **the shadow
slot's own constraint**, and the live entry at that id is compared against
it: a mismatch means the live database drifted from the derivation that
produced it, which is a `KernelDivergence`, not a skip. A RUP reason is only
matched to a slot once *pointer identity* confirms the live entry at the id
its header names really is that reason; otherwise it is replayed from the
live constraint and taints composition. Substituting slots for stored
shapes hands the kernel proved normal forms where the engine propagated on
the stored ones; the two agree on every fold the replay evaluates, but
verdict-neutrality is not argued for — a rejected substituted replay is
retried on the unsubstituted constraints, and only a rejection of *that* is
a divergence.

**The honest boundary.** Four things this does *not* claim:

1. `F` is the formula the checker **stored**. The parse-and-store step is
   outside the kernel and always will be — no rule models it — so what
   stands between `F` and the bytes on disk is not a theorem but a **second
   opinion**: under `--kernel-verify`, `shadow_init` reads the formula file
   again through `veripb-second-reader` and compares the two readings before
   filing a single slot. Two shipped defects lived in exactly this gap and
   both of them made the summary *more* confident rather than less — the
   WCNF parser taking variable identity from a literal's spelling, and
   `Clause::from_unnormalized_lits` storing a unit clause as the empty one,
   the second of which printed `nothing outside the proved fragment` and
   `COMPOSED: ... over the stored formula`, every word of it true. A
   mismatch is now a `KernelDivergence`.

   The claim is worth stating precisely, because it is weaker than the ones
   above it:

   * The second reader shares **no code** with `veripb-parser`, and none
     with `veripb-formula` either — its `Cargo.toml` lists one dependency
     (`malachite-bigint`), and that dependency list is the whole
     independence argument. It is a hand-written character scanner over
     `String` names and `BigInt` coefficients, deliberately slower and more
     allocation-happy than the parser it checks, so that a reviewer can read
     it against `proof_format_overview.md` and the development design notes and check
     it by eye.
   * The comparison is **up to `normC` and term order**, not byte equality:
     the checker legitimately merges, cancels, flips and re-tiers what it
     stores, and the reader hands the kernel the constraint as the file
     spells it and lets the proved normalization do the rest. It runs at
     both coefficient tiers, narrow first, so a `<= i64::MIN` row is
     compared at `Big` rather than stood down at. Constraints are compared
     position by position first and, only if that fails, as multisets — a
     permutation is not a divergence, because `DbOk.init` claims
     `Entails F c` per constraint and says nothing about the order.
   * The objective is compared too, in exact arithmetic rather than through
     `normC` (the kernel has no objective model, §5 item 5). For WCNF that
     is not a detail: a unit soft clause stores **no constraint at all**, so
     the objective is the only place the soft half of the format appears.
   * The second reading is a second `open` of the **path**, and that only
     works for a path whose bytes can be read twice. A FIFO, or the
     `/dev/fd/N` of a process substitution, hands its bytes to the first
     reader and nothing to the second; on macOS `open`ing any `/dev/fd/N`
     (including `/dev/stdin`) dups the descriptor the parser already read to
     the end rather than reopening the object, so even
     `veripb --kernel-verify /dev/stdin proof.pbp < f.opb` reads back
     nothing. Every one of those looked exactly like a truncated file, so
     `veripb --kernel-verify <(cat f.opb) proof.pbp` used to *reject* — with
     `Report this.` — a proof the same binary verified without the flag, and
     a FIFO hung the run instead. They are stand-downs now
     (`formula-file-not-rereadable`), detected by `stat` before anything is
     opened (opening a FIFO with no writer blocks) and by a nonzero starting
     offset after it is (a freshly opened file is always at zero). Teeing the
     parser's own byte stream would cover these inputs rather than skipping
     them; it would also put `veripb-parser` between the file and the second
     reader, which is the one thing the second reader may not have in front
     of it.
   * What it does **not** cover: the `preserved:` set, the second formula an
     `output ... FILE` step loads, and any file the reader cannot read — a
     refusal by the second reader is a counted skip
     (`formula-second-reader-refused`), never a rejection, because the
     checker's parser and not this reader is the authority on what is a
     legal file. That refusal surface is **not** confined to files the
     checker rejects anyway, and an earlier edition of this paragraph said
     it was: it offered invalid UTF-8 and a clause that ends mid-file as
     its examples — both genuinely hard parser errors — which left the
     impression that a refusal only ever costs a comparison the run was
     going to fail on its own.

     ```bash
     printf '* #variable= 1 #constraint= 2\n1 x1 >= 1 ; #\n1 ~x1 >= 1 ;\n' > junk.opb
     ```

     is one `#` away from a formula the corpus would accept, and the
     checker parses it without a word: its OPB parser stops at the `;` and
     never looks at the rest of the line. The reader refuses it at `line 2:
     unrecognized input "#"`, because it tokenizes the whole line before
     deciding what it means and has no token for `#`. The honest statement
     is that the reader is *strictly* stricter than the parser — on files
     the parser accepts as well as on files it rejects — and that every one
     of those files is a run whose stored formula goes uncross-checked.
   * A stand-down is therefore **not free**, and no longer pretends to be.
     Whatever its reason, standing down leaves the premise of `DbOk.init`
     unchecked — that the `F` the slots are filled from is the `F` on disk
     — so `shadow_init` turns every formula slot into a `Slot::Hole` under
     the stand-down's own reason. The holes propagate into everything
     derived from them, the run reports `NOT composed`, and the taint
     census names the reason. On the `junk.opb` above, the run now ends

     ```text
     NOT composed (no kernel-justified slot at id 3: formula-second-reader-refused);
     4 slot(s) in the live id space, 3 unjustified slot(s) and 0 subproof premise(s)
     recorded over the run:
     formula-second-reader-refused x3
     ```

     where it used to end `COMPOSED: the contradiction at id 3 certifies
     the whole run through DbOk/checker_sound over the stored formula; ...
     0 unjustified slot(s) and 0 subproof premise(s) recorded over the run: none` — the exact sentence
     this second opinion exists to qualify, printed with the qualification
     missing. A formula with no constraints has no slot to hole, so
     `shadow_record_refutation` also reads the stand-down directly: "the
     cross-check stood down" and "the run composed" cannot both be true.
   * The two counters are on the summary line: `N formula constraint(s) and
     M formula objective(s) cross-checked against the file on disk`. Zero
     with no skip means the file has no constraints; zero *with* a skip
     means the comparison stood down, and the reason says which of the four
     ways.
   * The **output** formula of an `output ... FILE` rule is cross-checked the
     same way, by `output_formula_cross_check`, before any of its constraints
     is looked up in the core. Until that existed the only reading of that
     file was `veripb-parser`'s, on both sides of the comparison: the rule
     matched the checker's own parse against the database, so a parse that
     dropped or mis-signed an output constraint would have agreed with itself.
     What this underwrites is narrow — that the constraints the rule ranges
     over are the ones the file spells — and it says nothing about whether the
     equivalence *guarantee* holds, which stays unmodelled (§5). It reports as
     `N output formula constraint(s) cross-checked against the file on disk`,
     appended only when an `output` rule ran, and stands down the same
     fail-soft way rather than failing.
2. The shadow models entailment, not the model-preserving meta-rules.
   `red`, `dom`, `sol`/`soli` and assertions add constraints that are
   satisfiability-preserving but not entailed by `F`, and subproof premises
   (proofgoal premises, dominance scopes, the negated constraint of a
   checked deletion, an order's proof obligations) are assumptions rather
   than derivations; every one of those is a hole by construction:
   `red-witness-unmodelled`, `dom-unmodelled`,
   `strengthening-subproof-unmodelled`, `solution-exclusion-unmodelled`,
   `obju-unmodelled`, `pbc-unmodelled`, `assertion-unverified`,
   `proofgoal-premise`, `scope-premise`,
   `checked-deletion-premise`,
   `order-proof-premise`. That is exactly what makes an
   all-slots-present refutation a genuine `checker_sound` instance rather
   than a restatement of the live verdict — and it is why an enumeration
   proof, whose contradiction rests on the solutions it excluded, correctly
   reports NOT composed.
3. Every comparison the bridge makes is up to term order. `normC` is
   order-sensitive as a *function*, but the Clean predicates the shadow
   feeds (`evalTerms`, `slackTerms`, `coeffSum`, `AllNonneg`) fold over the
   term list, and a leaf is always replayed as the slot's own constraint, so
   the term order the Clean side sees is the slot's. The canonical
   comparison against the live entry is a divergence detector, not a link in
   the entailment chain.
4. A rule that adds a constraint without offering the bridge a justification
   produces a hole under the backstop name `rule-not-kernel-justified`,
   never a trusted slot. Silence is the tainted case, so a rule added
   tomorrow cannot quietly widen the claim; no corpus instance reaches the
   backstop today, because every constraint-adding rule either justifies its
   slot or names its meta-step.

Structural failures — an id the shadow cannot line up with the live id space,
an unpaired database swap, an offered slot that is not the constraint the
checker stored — clear a run-level `composed` flag under the names
`shadow-id-desync`, `shadow-stack-desync` and `shadow-slot-mismatch`, and are
`debug_assert`ed so they surface in development rather than as a quietly
weakened claim.

The census below is **derived, not hand-maintained**: every figure in it is
regenerated from `tests/kernel_verify_expected.txt` by
`the_composition_census_in_the_docs_is_the_measured_one`
(`veripb-core-proved/tests/island_sync.rs`), which rebuilds the whole
paragraph — categories included — and fails with the corrected text when it
does not match. An earlier hand-maintained version of it was wrong in all
five of its numbers and carried a category (`1 on variable-form MIR`) that
no instance had ever produced, which is why it is now generated. To
re-derive it by hand:

```bash
grep -c '\[compose\]' tests/kernel_verify_expected.txt                  # total
grep -c 'kernel-compose: COMPOSED' tests/kernel_verify_expected.txt     # composed
grep -c 'NOT composed' tests/kernel_verify_expected.txt                 # not composed
grep -oE 'no kernel-justified slot at id [0-9]+: [a-z-]+' \
  tests/kernel_verify_expected.txt | sed 's/.*: //' | sort | uniq -c    # by reason
```

<!-- census:begin -->
Over the shipped corpus, 66 of the 311 accepted instances reach a refutation conclusion at all (the rest conclude `NONE`, `SAT`, or a bound met by a solution), and **66 of those 66 compose end to end**. Every one of them does.
<!-- census:end -->

`red-witness-touches-database` is a hole that got NARROWER by being split, and
`red-witness-unmodelled` no longer blocks any composition at all.
`VeriPbCore.dbOkR_red_of_goals` asks, for every database slot `D`, that `D|w`
holds; real proof formats emit goals only for the constraints the witness
touches and say nothing about the rest. The bridge now CHECKS that omission
instead of trusting it, by computing `substC w D` for every stored slot and
requiring it to be `D` itself. Where the witness moves nothing — the common
shape, a `red` introducing a fresh auxiliary variable — the whole `substDB`
premise discharges and the step is kernel-justified. Where it does move a
stored constraint, this reason is recorded, because justifying that needs the
per-slot goal accounting the bridge does not yet do.

Routing the untouched case took `red-witness-unmodelled` from **1194 steps to
764** across the accepted corpus, and left composition unchanged at 16 of 64 —
those instances were never blocked by `red` alone.

**Solution exclusion then moved it: 16 → 19.** The constraint an excluding
`sol` stores is the BLOCKING CLAUSE of the exhibited solution, and
`VeriPbCore.agrees_of_not_holds_blockC` is what it needs: an assignment that
fails that clause agrees with the solution on every variable it was built
over, so excluding it loses only assignments already exhibited.

This one could not be absorbed by widening an invariant, and the reason is
worth stating plainly: exclusion is **not** satisfiability-preserving. If the
excluded assignment was the formula's only model, the database becomes
unsatisfiable while `F` is satisfiable — so `DbSat`, which was enough for
`red`, fails outright. What survives is `DbEnum`, and a run using it proves a
DIFFERENT sentence: not `Unsat F`, but that `F` has no models beyond the ones
exhibited. The summary line says so, naming `DbOkE/enumeration_complete`
rather than `checker_sound`, because claiming the latter on a satisfiable
formula would be false.

`DbOkE` has no `red` constructor, deliberately. Redundance hands back a
DIFFERENT assignment, and the enumeration invariant is a claim about the model
you started with — a rule that replaces it says nothing about whether that
model was exhibited. A run using both is refused
(`enumeration-with-red-unmodelled`) rather than composed under whichever
theorem happens to be named.

**The objective then moved it again: 19 → 32.** The improving form stores the
objective, negated, at degree `1 + constant - value` — which is
`VeriPbCore.improveC`, and says "objective strictly below `value`".
`VeriPbCore.bound_of_not_holds_improveC` is what it needs: an assignment
failing that constraint has objective value at least `value`, so it loses only
assignments no better than the one exhibited. The kernel now has an objective
(`objValNeg`, read off the negated coefficient list the constraint carries, so
the whole development is subtraction and never negation).

One hypothesis there is not free: `Int.le v bound`, that solutions IMPROVE. A
model already known to be no better than the old bound is only known to be no
better than the new one if the new one is smaller. The bridge checks it against
the bound the last improving step established, rather than assuming it from the
rule's name.

So the 64 refutation-reaching instances now compose under THREE verdicts, and
which one is named is what each run is entitled to claim: 16 by
`checker_sound` (the formula is unsatisfiable), 13 by `bound_complete` (nothing
beats the exhibited bound — such a formula is typically SATISFIABLE, and the
exhibited solution proves it), 3 by `enumeration_complete` (no models beyond
the ones exhibited).

**Two more rules turned out to be the SAME step under a different name, taking
composition 32 → 36 with no new mathematics.**

`obji` is a separate `Checkable` from `sol` that builds a byte-identical
improving constraint; it had simply never been routed, and kept a blanket skip
naming the kernel's old lack of an objective. It takes `DbOkB.improve`
directly, because that leg's only non-free hypothesis is `Int.le v bound` —
NOT that a solution achieving `v` was exhibited.

The `a` (assertion) rule is an axiom-by-fiat in general, and stays one: the
format itself says a proof containing it is invalid, and `assertion_used` still
qualifies the verdict. But one SHAPE is not an assumption at all. Refuting `F`
together with `obj < v` proves `obj >= v` over `F` whether or not anything
achieving `v` was ever shown — so an `a` storing exactly `improveC` is a sound
bounds step with a theorem behind it. Recognition is exact rather than
special-cased: the bridge normalizes the asserted constraint against `improveC`
at `v = 0`, requires the term lists to agree, and reads the real `v` off the
degree difference, which is sound because `improveC`'s degree is affine in `v`
and normalization shifts it by a constant depending only on the terms. Any
other assertion keeps its hole.

**The combined induction closed the mixture entirely.** `VeriPbCore.DbOkF` is
ONE induction carrying all five legs — derivation, deletion, redundance,
exclusion and improvement — so a run using several of them is an instance of it
like any other, and `mixed-verdict-inductions-unmodelled` no longer exists.

What reconciles them is the PRESERVED SET. `red` hands back a DIFFERENT
assignment, which is why it could not live in `DbOkE` or `DbOkB`: those are
claims about the model you started with. `DbFull` keeps a COMPANION instead —
a model of the database agreeing with the real one on `P` — and a rule whose
witness FIXES `P` may replace the companion freely, because the replacement
still agrees where agreement is used. That is `WitFixes w P`, and it is exactly
the side condition VeriPB imposes on `red` in the presence of solution logging.
`Companion` is the one place in this kernel that uses `Exists`: the companion is
produced, not computed.

`P` is built LAZILY, from the legs that need it, and that is the difference
between a usable condition and a useless one. Only `exclude` needs the blocking
clause's variables in `P`; only `improve` needs the objective's. A run doing
neither has `P` empty, so `WitFixes` costs nothing. Seeding `P` with the
objective up front instead refuses every `red` touching a problem variable —
measured, and it is most of them.

The check is also RETROACTIVE. A `red` justified while a variable was still
free is not covered once that variable joins `P`, and by then the slot is
handed out — so the run's composition is refused rather than the offer.

**That retroaction is what the objective-update proofs tripped, and fixing it
properly took composition 39 → 55 of 66.** Those proofs `red` over `y1`, then `obju`
brings `y1` into the objective, then a `soli` needs a bound. The naive reading
is "the objective changed, so the induction does not apply". The real situation
is better: `obju` emits `f_new >= f_old` and `f_old >= f_new` as proofgoals
proved FROM THE DATABASE, which is exactly "the two objectives agree on every
model of it" — and those discharges were already kernel-checked.

So the `improve` leg now takes the CURRENT objective for its constraint and the
REFERENCE one for the transfer, related by that agreement. The bound is
established for the companion under the current objective, moved to the
reference objective by the agreement (the companion models the database, which
is where they agree), and then to the real model by agreement on `P`. Only the
REFERENCE objective's variables need to lie in `P` — so a `red` may move a
variable a LATER objective mentions, which is precisely the shape these proofs
have.

Carrying the agreement on the leg rather than adding an `obju` constructor
keeps `negObj`/`konst` parameters rather than indices, and is also the faithful
place for it: DELETION shrinks the database, so an agreement established
earlier need not survive. The bridge tracks that explicitly — an `obju` is
recorded as verified at a deletion count, and a bound refuses to transfer
across any deletion since (`objective-equality-predates-deletion`), rather than
assuming the deleted constraint was not one the equality used.

**The TOUCHED case is now justified too, by per-slot goal accounting.**
`dbOkR_red_of_goals` asks, for every slot `D`, that `D|w` holds. A slot the
witness does not move needs no goal — `substC w D` IS `D`. A slot it does move
needs one, and the pairing is recovered from `copy_ids`, which carries a source
constraint's live ids onto its substituted image; a live id IS a shadow slot
index. `Implied` auto-discharges pair the same way. `Trivial` and `DbLookup`
do not — their payload has a fresh header — so a slot discharged that way
simply does not appear, and is refused rather than assumed.

Three things are checked for a moved slot, and none trusts the occurrences
index: that the slot appears at all; that the goal is the image the KERNEL
computes from the slot, `subst_c(w, D)`, and not whatever the checker's own
`substitute` produced; and that the discharges added no skip, so each was
kernel-justified rather than merely accepted. A slot the index wrongly omitted
has neither identity nor a matching goal, so the step is refused.
`objective_update` now composes with ZERO unjustified slots.

**The census now separates PREMISES from GAPS, and the difference is large.**
A subproof stores its own assumption as a slot — the negated constraint, an
order premise, a proofgoal premise — and those slots are not kernel-justified,
because an assumption is not a theorem. Reporting them beside genuine gaps made
the gap look an order of magnitude bigger than it is: measured across the
corpus, **96% of every "tainted hole" was a premise**. The real figure is 90
unjustified slots against 3379 subproof premises.

They remain HOLES for justification purposes — nothing derived from one is
justified, which is the conservative direction and is exactly why an assumption
cannot escape its subproof. Only the reporting changed, and the names changed
with it: a reason ending `-premise` says what the slot is, where
`red-witness-unmodelled` read as a failure to model something.

**Nothing remains.** The last ten closed as three separate accounting gaps,
none of them mathematics:

`Trivial` and `DbLookup` auto-discharges did not carry the SOURCE constraint,
only its substituted image — which has a fresh header and no ids — so a slot
discharged that way was invisible to the pairing. The enum now carries it.

Subproof `red`s and subproof `obju`s both compute what they need in the rule
and offer at the `qed`, by which point it is gone. The goal/slot pairs, the
clean-discharge flag and the reference objective now travel on the subproof
context. The reference objective in particular must be captured BEFORE the
update is applied, because `finalize_unchecked` applies it — after that, the
objective the run started with no longer exists.

The last one was a `strengthening_to_core` proof whose witness moved a DERIVED
slot. Under that mode `get_proofgoals` is asked with `add_derived_goals =
false`, so derived constraints raise no obligation at all and there is nothing
to pair with. Refusing would have been wrong-headed: `DbOkF.delete` is
unconditional, so the theorem may simply be instantiated at the database
WITHOUT those slots. They are dropped, and the drop is paid for honestly — a
dropped slot becomes a hole, so anything later derived from it cannot be
justified, and the taint census reports `dropped-derived-slot` by name.
That the run still composes means its chain never needed them; dropping slots
can only make composition harder, never easier.

`tests/kernel_verify.rs` snapshots the `kernel-compose:` line per instance
alongside the coverage line, and pins three fully-composed runs — one per leg
of the `DbOk` induction (`conclusion_UNSAT_no_hint` for `init`,
`variable_form_division` for a `pol` chain, and a synthetic `rup` refutation
for `DStep.rupS`) — so that "every instance reports NOT composed" cannot
become a silently passing steady state.

### 7.5 Clean pitfalls discovered in slice 2 (recorded for the next slice)

- Structural recursion silently **mis-compiles when the decreasing scrutinee
  is not the first-matched argument** (the compiled `List.rec` bakes in the
  outer index instead of the decreasing one). `setNone` is therefore a
  definitional wrapper over a worker `setNoneGo` that matches the list first.
  Watch for this in any two-index recursion.
- `congrArg (fun z => z + T) h` (rewriting the *left* operand of `+`)
  mis-unifies when it appears in argument position; the file carries named
  wrappers (`add_congr_left`/`add_congr_right`) instead, generalizing the
  slice-1 `le_congr_left` workaround.
- Recursor applications must be applied to their scrutinee explicitly; an
  eta-contracted `@List.rec ...` against a `forall` goal fails to elaborate.
