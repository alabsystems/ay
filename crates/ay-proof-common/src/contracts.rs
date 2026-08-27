// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Contract vocabulary for VerifierConsumer verification.
//
// PHASE 2 HAS SHIPPED, AND THIS MODULE NO LONGER STUBS IT OUT.
//
// This file used to define `requires!`/`ensures!`/`invariant!`/`decreases!` as
// `macro_rules!` that expanded to `{}`, with a header promising that "Phase 2
// will replace them with real deductive_contract_macros attributes". Phase 2 landed in the
// compiler and this crate had simply not moved. The erasing macros are gone;
// the crate now carries FIRST-CLASS compiler contracts, in the same
// `` form already used by `ay-pb-core`
// (src/eval.rs, src/portfolio.rs) and `ay-dpll`.
//
// HOW THE FIRST-CLASS FORM RESOLVES (verified against the toolchain source,
// rustc_resolve/src/macros.rs:806-866 and :1404-1424). `#[trust::requires(..)]`
// and `#[trust::ensures(..)]` are replaced, after name resolution and before
// expansion, by the compiler-owned builtins `trust_contracts_requires` /
// `trust_contracts_ensures`, so the verifier sees the ORIGINAL payload. Three
// conditions must ALL hold or the attribute is not a contract:
//
//   1. verification is enabled (`sess.trust_verification_enabled()`);
//   2. `cfg(deductive_verify)` holds, or the `cfg_attr` never fires. NOTE: this cfg
//      is NOT something a build passes in. The compiler injects it ITSELF
//      whenever verification is on (rustc_session/src/config/cfg.rs:210-212),
//      attributes are unconditionally present under the verifier — there is
//      no "verified build that quietly skips the contracts";
//   3. an EXTERNAL crate whose *lib* name is `trust` is in scope, supplying
//      crate-root `requires`/`ensures` attribute proc macros — that is the
//      `trust-spec` package. The resolver keys on the RESOLVED def, not the
//      literal path, so renames and `use` aliases all work; but with no such
//      crate the path does not resolve at all.
//
// Conditions 2 and 3 together have a sharp consequence worth stating plainly,
// because it cost a red lane to discover: a verified compile of this crate
// WITHOUT the `trust` crate does not silently skip the contracts, it FAILS with
// E0433 `cannot find module or crate `trust``. The contracts are fail-closed,
// never fail-open. That is why the committed manifest stays standalone and the
// dependency is supplied by an OVERLAY at verification time — the arrangement
// the development proof harness documents for
// `ay-pb`, and which `scripts/ci/trust_verification_ratchet_gate.sh` now
// implements by building `trust-spec` into the lane and passing `--extern
// trust=…`. Under stock rustc there is no verification, hence no
// `cfg(deductive_verify)`, hence no attribute, no dependency and zero codegen.
//
// WHAT THE SPEC LANGUAGE SUPPORTS — AND THE TRAP, WHICH IS THAT PARSING AND
// LOWERING ARE DIFFERENT QUESTIONS. A payload that is a plain typeable boolean
// expression over the parameters keeps upstream's typed contract lowering. A
// payload using spec-only vocabulary — `result`, `old(..)`, `forall`, `exists`,
// `==>` — is OPAQUE: span-only verifier metadata that bypasses name resolution
// and typeck (see tests/ui/contracts/trust-spec-opaque-spec-clauses.rs in the
// toolchain tree). It is very easy to read that UI test as a menu of what the
// prover understands. IT IS NOT. That test is `check-pass`: it establishes only
// that those forms PARSE.
//
// MEASURED on trust-e26541e3, by writing each form and reading the verdict, the
// fragment that actually LOWERS INTO A VERIFIER FORMULA is far narrower —
// comparisons of PARAMETERS against LITERALS, and conjunctions of those:
//
//     requires(dimacs != 0)              LOWERS, and PROVES the body's assert
//     requires(id <= 2_147_483_647)      LOWERS, and PROVES the body's assert
//     requires(id <= Variable::MAX_ID)   REFUSED — associated constant
//     requires(idx <= u32::MAX as usize) REFUSED — associated constant AND cast
//     ensures(result.variable() == var)  REFUSED — `result` and method calls
//
// A refused predicate does not fail closed into an error; it is reported as
// "compiler contract predicate was not lowered into a typed verifier formula:
// unsupported contract predicate expression `…`" and lands in UNKNOWN,
// discharging nothing. Importantly it is also not ASSUMED — no
// `assumption:requires` obligation is emitted for it — so a refused contract is
// inert rather than dangerous. It is still worth avoiding: it adds an UNKNOWN
// that looks like a verifier weakness when it is really a frontend gap. Where
// this crate could not express a condition in the lowerable fragment it says so
// at the definition (see `literal::Literal::to_dimacs` and
// `literal::Literal::negated`) instead of shipping an approximation, because a
// precondition that DOES lower is assumed inside the body, so a wrong one is
// worse than none.
//
// WHAT IS NOT AVAILABLE, AND WHY THERE IS NO REPLACEMENT HERE FOR TWO OF THE
// FOUR OLD MACROS. The resolver maps EXACTLY `requires` and `ensures`. The
// `trust-spec` crate also exports `invariant`, but nothing maps it to a
// builtin, so it stays a passthrough no-op — i.e. it would erase, which is the
// defect this change exists to remove. There is no `decreases` attribute at
// all. Loop invariants and termination measures therefore have NO first-class
// spelling today; `leb128::read_u32`/`read_u64` still carry `termination`
// obligations in the UNKNOWN class for that reason. Writing an erasing
// `invariant!` back would not state them — it would only look like it did.
//
// See the development design notes

// ---------------------------------------------------------------------------
// Propagation-redundancy (PR) functional contract — shared documentation anchor
// for the DPR/LPR symmetry-breaking emitter (the lex-leader SBP PR route).
// ---------------------------------------------------------------------------

/// The propagation-redundancy (PR) clause-addition contract (Heule–Kiesl–Biere,
/// "Short Proofs Without New Variables", CADE 2017).
///
/// A clause `C` is **PR-redundant** in a formula `F` with a *witness assignment*
/// `w` iff
///   1. `w ⊨ C` (the witness satisfies the added clause), and
///   2. for every clause `D ∈ F`: `F | α  ⊢_RUP  D | w`,
///      where `α = ¬C` is the assignment falsifying `C`.
///
/// PR generalises RAT: a RAT clause on pivot `p` is the special case where the
/// witness flips only `p`. The DRAT checker in `ay-drat-check` verifies RUP and
/// RAT only and therefore **must reject** a clause that is PR-but-not-RAT — it is
/// not in the checker's trusted fragment. The trust anchor for PR additions is an
/// external verified LPR checker (cake_lpr); a buggy emitter is *caught* (the
/// checker rejects), never silently trusted.
///
/// ## Symmetry-breaking instantiation (the lex-leader SBP)
///
/// For a verified formula automorphism `σ` (a permutation of the variables under
/// which `F` is invariant as a clause multiset) the lex-leader clause
/// `C = (x_{w_j} ∨ ¬x_{σ⁻¹(w_j)} ∨ …)` is PR with witness `w = σ(α)`, the image
/// of `α = ¬C` under `σ`:
///   * `w ⊨ C` because the σ-image of the negated deciding literal lands back on
///     the clause's own original-variable literal with satisfying polarity, and
///   * `F | α` and `F | w` are isomorphic under `σ` (an automorphism), so the
///     required RUP entailments hold.
///
/// This is sound **only when every literal of `C` lies in `σ`'s support** (i.e.
/// the clause is *aux-free*): fresh equal-prefix Tseitin aux variables `e_j` are
/// outside `σ`'s domain, so the σ-image witness does not constrain them and the
/// clause is not certifiable by this construction alone. Those aux-carrying lex
/// clauses (and the `e_j ↔ prefix-equal` definitions) must be emitted on the
/// RAT/blocked route instead (the `#8011` tower concern): only the aux-free lex
/// clauses carry `σ` as a PR witness.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrRedundancyContract;

impl PrRedundancyContract {
    /// Necessary syntactic precondition for the σ-image PR witness to be valid:
    /// the witness must satisfy the clause via at least one shared literal, and
    /// the clause must be non-empty. This is *not* a full PR verification (that is
    /// the external LPR checker's job) — it is the cheap local guard the emitter
    /// applies before writing a PR `a`-line, so a structurally malformed witness
    /// is never emitted.
    ///
    /// `clause` and `witness` are DIMACS-signed literal lists.
    #[must_use]
    pub fn witness_satisfies_clause(clause: &[i32], witness: &[i32]) -> bool {
        !clause.is_empty() && clause.iter().any(|c| witness.contains(c))
    }
}
