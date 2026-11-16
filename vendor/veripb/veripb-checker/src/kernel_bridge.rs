//! Bridge between the live checker and the proved kernel
//! (`veripb-core-proved`), active under `--kernel-verify`.
//!
//! The live checker stays the fast path; this module *re-derives* its
//! soundness-critical conclusions through the machine-checked kernel:
//!
//! - every `pol` derivation is replayed instruction-by-instruction on a
//!   shadow stack of kernel constraints (kept in the kernel's proved
//!   normalized form), and the final constraint must agree with the live
//!   result up to normalization;
//! - every RUP conflict is replayed as a checked propagation-trail
//!   certificate (`VeriPbCore.PropTrail` / `entails_of_rup`);
//! - every stored contradiction and every logged solution is re-judged by
//!   the kernel's decidable checks (`checker_sound` hypotheses /
//!   `holdsAllB`) — contradictions at the mid-proof `qed` discharges that
//!   decide subproofs as well as at conclusion time;
//! - every trivial-accept (proofgoal discharges, order reflexivity) and
//!   every DB-lookup accept ("this constraint equals a database
//!   constraint") is re-judged on the kernel's proved normal forms —
//!   including the obligations that proofgoal *generation* discharges
//!   without ever making them goals (see [`consume_autodischarge`]);
//! - every substituted-implication accept (proofgoal
//!   `DBImpliesSubstituted`) is re-derived by certifying the consumed
//!   trail literals as kernel trail certificates, modelling the
//!   substitution with proved adds of those units and trivial axioms, and
//!   closing the residual implication through the proved rule chain;
//! - every accepted objective value is shadow-recomputed in exact
//!   arithmetic (a cross-check, not a kernel theorem — the kernel has no
//!   objective model);
//! - the formula file is read a second time, independently, and the
//!   constraints and objective the checker stored are compared against that
//!   reading before the shadow database's first slot is filled
//!   ([`formula_cross_check`]).
//!
//! A step the kernel cannot represent — RUP under assumptions, a variable
//! index beyond `u32` — is **counted and reported**, never silently trusted;
//! so is a rule the kernel has no model of at all (`red` witnesses,
//! dominance, solution exclusion, preserved sets, the `output` equivalence
//! claim). A step the kernel can represent but *disagrees on* is a
//! [`CheckingError`]: the two implementations diverged, and one of them is
//! wrong.
//!
//! # Two coefficient tiers, and why
//!
//! The live checker promotes its own arithmetic from `i64` to `i128` to
//! `BigInt` as values grow. The proved kernel used to be `i64`-only, so it
//! stood down at exactly the widths the live checker had just promoted into —
//! and the widths a checker promotes into are where its width defects live.
//! Measured against the pre-fix binary, `--kernel-verify` *missed* eight of
//! the ten degree-wrap and watcher-slack regression instances for that reason
//! alone, counting a skip while the run reported `s VERIFIED UNSATISFIABLE`
//! on a satisfiable formula.
//!
//! The kernel is now generic over its coefficient domain and instantiated
//! twice (see [`Tier`]): at `i64`, where the proved width guards have content
//! and the whole corpus runs, and at `BigInt`, which mirrors the Clean `Int`
//! statements with no width side condition at all. Every entry point here is
//! a thin dispatcher ([`tiered_step`] / [`tiered_outcome`]) over a generic
//! `_at::<C>` body: replay narrow, and — only if that pass stood down on
//! *width* ([`width_limited`]) — replay the same step wide. A divergence from
//! the narrow pass is never re-litigated: it was reached by computing every
//! value exactly and passing every guard, so it is real. The second pass
//! exists for the opposite case, where the narrow tier could not compute at
//! all and so had nothing to disagree with.
//!
//! # Why the comparators are `pub`
//!
//! Exactly two items in this module are called from outside this crate by
//! *production* code — `KernelStats::summary` and [`composition_summary`],
//! both from the end-of-run report in the root crate's `src/lib.rs`. Yet
//! [`verify_pol`], [`verify_trivial`], [`verify_db_lookup`],
//! [`verify_contradiction`], [`verify_solution`], [`verify_db_solution`],
//! [`verify_objective_value`], [`verify_implication`],
//! [`verify_rup_certificate`], [`verify_hinted_rup`] and
//! [`verify_substituted_implication`] are public, as are the shadow-database
//! entry points [`KernelShadowDb`], [`shadow_init`], [`shadow_record_added`]
//! and [`shadow_record_refutation`] and the `consume_*` drivers. That is
//! deliberate and load-bearing: `tests/kernel_divergence.rs` drives them
//! directly with *deliberately wrong* live results, which is the only way to
//! test the reject path. No proof can reach it — a corpus of proofs the live
//! checker gets right never makes the kernel disagree — so without that file a
//! bridge whose comparators all returned "verified" would pass every other
//! test in the tree. Narrowing this surface means moving those tests inside
//! the crate, not deleting them.
//!
//! # Run-level composition: the shadow database
//!
//! Re-deriving each step in isolation says "this step was a correct
//! inference"; it does not say "this run proved anything". [`KernelShadowDb`]
//! closes that gap. It mirrors the live [`Database`]'s id space slot for
//! slot, and is mutated *only* through kernel-justified operations:
//!
//! - the formula load fills the slots with the proved normal forms of the
//!   constraints the checker **stored** (`VeriPbCore.DbOk.init` /
//!   `dbEntailed_init`, then `VeriPbCore.entails_normC`) — after
//!   [`formula_cross_check`] has established that what was stored is what
//!   the formula file says;
//! - a derivation whose bridge check succeeded **from present slots only**
//!   stores the kernel constraint it derived (`VeriPbCore.DbOk.derive`,
//!   justified by `VeriPbCore.dstep_entails` on that step's own `DStep`
//!   witness);
//! - a derivation the bridge could not justify — an unrepresentable step, an
//!   unmodelled meta-rule (`red`, `dom`, `sol`, assertions), or a leaf whose
//!   own slot is a hole — becomes a **tainted hole** carrying the reason;
//! - a deletion clears the slot (`VeriPbCore.DbOk.delete`); a hole from a
//!   deletion is *not* a taint, because deletion is unconditionally sound;
//! - an order definition swaps in a fresh empty database, so the shadow
//!   pushes the current slots on a stack and mirrors the sub-database from
//!   empty, restoring on the way out; a desync of that pairing, or of the
//!   id space itself, sets `composed = false` under a named taint.
//!
//! The invariant every present slot carries is exactly the one
//! `VeriPbCore.dbOk_entailed` establishes for a `DbOk` database — pointwise
//! `DbEntailed F DB`, i.e. `Entails F c` for the slot's constraint `c`, with
//! `F` the **stored** formula. When a refutation conclusion is accepted at
//! id `i` and `slots[i]` is present, nonnegative and has coefficient sum
//! below its degree, those are precisely the hypotheses of
//! `VeriPbCore.checker_sound`, so the *whole run* is certified: `Unsat F`.
//! Otherwise the summary reports the taint census instead — a hole anywhere
//! upstream of the contradiction is never trusted.
//!
//! ## The honest boundary
//!
//! - `F` is the formula the checker **stored**. The parse-and-store step is
//!   outside the kernel and no rule models it, so what ties `F` to the bytes
//!   on disk is not a theorem but a second opinion: [`formula_cross_check`]
//!   reads the file again through `veripb-second-reader` — a crate that
//!   links neither `veripb-parser` nor `veripb-formula` — and compares the
//!   two readings up to `normC` and term order. That comparison rejects on a
//!   mismatch and *stands down*, counted, on a file it cannot read; it does
//!   not cover the `preserved:` set or an `output ... FILE` formula. A
//!   stand-down holes every formula slot under its own reason, so a run
//!   whose formula was never cross-checked cannot report `COMPOSED` — the
//!   composition claim is never wider than the premises actually
//!   established. See the development design notes §7.4, boundary note 1.
//! - Slots hold `normC` images and every comparison the bridge makes is up
//!   to term order. `normC` is order-sensitive as a *function*, but every
//!   Clean predicate the shadow feeds (`evalTerms`, `slackTerms`,
//!   `coeffSum`, `AllNonneg`) folds over the term list, and — this is the
//!   point — a leaf is always replayed as **the slot's own constraint**, so
//!   the term order the Clean side sees is the slot's. Canonical comparison
//!   against the live entry is a *divergence detector*, not a link in the
//!   entailment chain.
//! - The shadow models entailment (`Entails F`), not the model-preserving
//!   meta-rules. `red`, `dom`, `sol` and friends add constraints that are
//!   satisfiability-preserving but not entailed, so their slots are holes by
//!   construction — which is what makes an all-slots-present refutation a
//!   genuine `checker_sound` instance.
//! - Core/derived status is a completeness restriction of the live checker
//!   and does not affect `Entails F`, so the shadow does not model it.

use std::collections::BTreeMap;
use std::rc::Rc;

use ahash::{AHashMap, AHashSet};

use malachite_bigint::BigInt;
use veripb_core_proved as kernel;
use veripb_core_proved::normalize::normalize;
use veripb_core_proved::rup;
use veripb_core_proved::{Big, CoeffDomain, Exact};
use veripb_formula::prelude::*;
use veripb_propagator::propagation_engine::KernelCertificate;
use veripb_propagator::trail::{Reason, Trail as LiveTrail};
use veripb_rules::Instruction;
use veripb_second_reader as second_reader;

use crate::database::Database;
use crate::error::CheckingError;

/// Counters for the end-of-run report.
#[derive(Debug, Default, Clone)]
pub struct KernelStats {
    /// `pol` derivations fully re-derived by the kernel.
    pub pol_verified: usize,
    /// RUP conflicts fully replayed by the kernel.
    pub rup_verified: usize,
    /// Stored contradictions re-judged by the kernel.
    pub contradiction_verified: usize,
    /// Logged solutions re-evaluated by the kernel.
    pub solution_verified: usize,
    /// Syntactic implications re-derived through the proved rule chain.
    pub implication_verified: usize,
    /// Substituted-implication accepts (proofgoal `DBImpliesSubstituted`)
    /// re-derived by the kernel: the trail's units certified through
    /// `rup::check_rup`, the substitution modelled by proved adds of those
    /// units and trivial axioms, and the residual implication re-derived
    /// through the proved rule chain.
    pub substituted_implication_verified: usize,
    /// Trivial accepts (proofgoal discharges, order reflexivity) re-judged
    /// by the kernel (proved normalization + degree at most zero).
    pub trivial_verified: usize,
    /// DB-lookup accepts re-judged by the kernel: goal and found database
    /// constraint agree on their proved normal forms.
    pub db_lookup_verified: usize,
    /// Objective values shadow-recomputed in exact arithmetic (a
    /// cross-check, not a kernel theorem: the kernel has no objective
    /// model).
    pub objective_verified: usize,
    /// Stored formula constraints matched, up to proved normalization and
    /// term order, against a second and independent reading of the formula
    /// file (`veripb-second-reader`). This is what makes the `F` of
    /// `DbOk.init` the bytes on disk rather than the parser's opinion of
    /// them; see [`formula_cross_check`]. Zero means the cross-check stood
    /// down, and the reason is in [`KernelStats::skipped`].
    pub formula_constraints_cross_checked: usize,
    /// The formula's objective, likewise matched against the second reading:
    /// 0 or 1. Counted apart from the constraints because the kernel has no
    /// objective model, so this comparison rests on exact arithmetic rather
    /// than on `normC`.
    pub formula_objectives_cross_checked: usize,
    /// Output formula constraints likewise matched against a second and
    /// independent reading of the *output* file, before `output` looks them
    /// up in the core. See [`output_formula_cross_check`]: without it the
    /// only reading of the file an `output` verdict is about was the
    /// checker's own. Zero also means "no `output` rule ran", which is the
    /// common case — unlike the input formula, there is not always one.
    pub output_constraints_cross_checked: usize,
    /// `output` rules whose BACKWARD equivalence half the kernel underwrote
    /// through `VeriPbCore.output_unsat_of_unsat`: a model of the emitted
    /// formula yields a model of the given one. Counted apart from the
    /// re-derivation counters because it licenses a claim about two formulas
    /// rather than re-deriving one step, and because the FORWARD half of the
    /// same verdict is still unmodelled -- a run with this at 1 still carries
    /// an `output-forward-equivalence-unmodelled` skip.
    pub output_backward_transfers: usize,
    /// `output` rules where BOTH halves went through, so the kernel has the
    /// two formulas equisatisfiable outright
    /// (`output_unsat_of_unsat` and `output_unsat_forward_of_dbOkF`). Always
    /// at most `output_backward_transfers`.
    pub output_equivalences: usize,
    /// Steps not re-derived by the kernel, by reason — steps the kernel
    /// cannot represent as well as rules it does not model at all (an
    /// assertion is representable but carries no proof obligation). A
    /// width-limited reason lands here only when *both* coefficient tiers
    /// stood down; see [`Tier`].
    pub skipped: BTreeMap<&'static str, usize>,
}

impl KernelStats {
    /// Record a skipped verification.
    /// Every counted skip, summed. A stage that leaves this UNCHANGED made no
    /// claim the kernel could not justify, which is how a caller checks that
    /// the goals it just discharged were all kernel-established.
    pub fn total_skips(&self) -> usize {
        self.skipped.values().sum()
    }

    pub fn skip(&mut self, reason: &'static str) {
        *self.skipped.entry(reason).or_insert(0) += 1;
    }

    /// Total number of skipped verifications.
    pub fn total_skipped(&self) -> usize {
        self.skipped.values().sum()
    }

    /// One-line human summary for the end of the run.
    pub fn summary(&self) -> String {
        let mut s = format!(
            "kernel-verify: {} pol, {} rup, {} contradiction, {} solution, {} implication, {} substituted-implication, {} trivial, {} db-lookup check(s) re-derived by the proved kernel, {} objective value(s) shadow-recomputed, {} formula constraint(s) and {} formula objective(s) cross-checked against the file on disk",
            self.pol_verified,
            self.rup_verified,
            self.contradiction_verified,
            self.solution_verified,
            self.implication_verified,
            self.substituted_implication_verified,
            self.trivial_verified,
            self.db_lookup_verified,
            self.objective_verified,
            self.formula_constraints_cross_checked,
            self.formula_objectives_cross_checked,
        );
        // Appended only when an `output` rule actually ran, so the reports of
        // the overwhelming majority of runs — which have no output formula —
        // are not padded with a permanent ", 0 output ...".
        if self.output_constraints_cross_checked > 0 {
            s.push_str(&format!(
                ", {} output formula constraint(s) cross-checked against the file on disk",
                self.output_constraints_cross_checked,
            ));
        }
        if self.output_backward_transfers > 0 {
            s.push_str(&format!(
                ", {} output equivalence backward half/halves kernel-transferred ({} \
                 full equisatisfiability)",
                self.output_backward_transfers, self.output_equivalences,
            ));
        }
        if self.skipped.is_empty() {
            s.push_str("; nothing outside the proved fragment");
        } else {
            s.push_str(&format!(
                "; {} step(s) outside the proved fragment:",
                self.total_skipped()
            ));
            for (reason, n) in &self.skipped {
                s.push_str(&format!(" {reason} x{n},"));
            }
            s.pop();
        }
        s
    }
}

/// The outcome of one bridge verification: verified, or skipped for a
/// stated reason. Divergence is an `Err(CheckingError)` instead.
pub type BridgeOutcome = Result<Option<&'static str>, CheckingError>;

/// What one bridge check contributes to the shadow database: the kernel
/// constraint it justified (`Entails F c` by the step's own `DStep`
/// witness), or the reason it could not justify one.
pub type SlotOutcome = Result<AnyConstraint, &'static str>;

/// The outcome of a bridge check on a rule that *derives a constraint*: the
/// per-step re-derivation verdict, plus the shadow-database contribution.
///
/// The two are deliberately independent. A step can be re-derived from the
/// live database (so it counts as verified) and still fail to compose,
/// because one of the database entries it consumed has no kernel-justified
/// shadow slot. Conflating them would make an upstream `red` step silently
/// erase the coverage statistics of every `pol` below it.
#[derive(Debug)]
pub struct StepOutcome {
    /// Per-step re-derivation: `None` re-derived, `Some(reason)` skipped.
    pub check: Option<&'static str>,
    /// The shadow-database contribution (see [`KernelShadowDb`]).
    pub slot: SlotOutcome,
}

impl StepOutcome {
    /// The bridge could not re-derive this step at all: it is neither
    /// counted as verified nor composable.
    fn skipped(reason: &'static str) -> Self {
        StepOutcome {
            check: Some(reason),
            slot: Err(reason),
        }
    }

    /// The bridge re-derived the step; `slot` says whether the derivation
    /// also grounds out in kernel-justified shadow slots.
    fn verified(slot: SlotOutcome) -> Self {
        StepOutcome { check: None, slot }
    }
}

// ---------------------------------------------------------------------------
// The shadow database
// ---------------------------------------------------------------------------

/// How the run's current objective relates to the reference one.
///
/// `VeriPbCore.DbOkF.improve` takes the CURRENT objective for its constraint
/// and the REFERENCE one for the transfer, related by a hypothesis that the
/// two agree on every model of the database. `obju` is what supplies that: it
/// emits `f_new >= f_old` and `f_old >= f_new` as proofgoals proved FROM the
/// database, which is exactly the agreement.
#[derive(Debug, Clone, PartialEq, Eq)]
enum ObjuState {
    /// No update yet, so the current objective IS the reference and the
    /// hypothesis is reflexivity.
    Unchanged,
    /// Updated, with both equality goals kernel-discharged, at this deletion
    /// count. Between then and now the database may only have GROWN, so a
    /// model of it now is a model of it then and the equality still applies.
    VerifiedAt(usize),
    /// Updated without the equality being kernel-established, or after a
    /// deletion that could have invalidated it. No bound may transfer.
    Broken,
}

/// One slot of the shadow database, mirroring one live database id.
#[derive(Debug, Clone)]
pub enum Slot {
    /// A kernel constraint the bridge justified: this slot is a leg of
    /// `VeriPbCore.DbOkF`.
    ///
    /// **It does NOT mean `Entails F c`, and reading it that way is unsound.**
    /// It did once, when the only legs were `init` and `derive`. `DbOkF` now
    /// also has `red`, `exclude`, `improve` and `dom`, every one of which
    /// justifies a constraint that is satisfiability-preserving but NOT
    /// entailed by `F` -- that is the whole point of those rules. So a present
    /// slot licenses the run's VERDICT (`full_unsat` / `full_complete`), which
    /// is what composition claims, and licenses nothing constraint-by-
    /// constraint.
    ///
    /// A consumer that needs entailment per slot -- `output DERIVABLE` is the
    /// live example -- must additionally establish that no non-entailing leg
    /// was used: `red_slots`, `excluded_slots` and `bound_slots` all zero.
    ///
    /// Always a `normC` image, so `VeriPbCore.normC_nonneg` gives
    /// `AllNonneg` for free. Held at whichever coefficient tier can express
    /// it — see [`AnyConstraint`].
    Present(AnyConstraint),
    /// Empty because the constraint was deleted (`VeriPbCore.DbOkF.delete` /
    /// `setNone`) or because the id was never populated (the live database
    /// reserves id 0). Deletion is unconditionally sound, so this is **not**
    /// a taint.
    Deleted,
    /// Empty because the bridge could not justify what the live checker put
    /// here. Carries the reason; counted in the taint census.
    Hole(&'static str),
}

/// The recorded outcome of a refutation conclusion, for the summary line.
#[derive(Debug, Clone)]
struct Refutation {
    /// The live database id the checker accepted as contradicting.
    id: usize,
    /// `None` when the run composes end to end; otherwise why it does not.
    obstacle: Option<String>,
}

/// A shadow of the live database's id space, mutated only through
/// kernel-justified operations. See the module header for what it buys and
/// where its boundary is.
#[derive(Debug)]
pub struct KernelShadowDb {
    /// One slot per live database id, in the same order. `slots[i]` mirrors
    /// live id `i`, which mirrors Clean list index `i - 1` (the live
    /// database reserves id 0 as a never-populated dummy).
    slots: Vec<Slot>,
    /// Variable -> ids of `Slot::Present` slots whose constraint mentions it.
    ///
    /// This exists for one premise: `red` must establish `substDB w DB = DB`
    /// for every slot the witness does not move, and checking that by
    /// substituting every slot on every `red` is quadratic in the proof
    /// length (measured: 512 ms at n=10000 on the `red` shape of
    /// `kernel_verify_perf`, against a 218 ms budget). Only a slot that
    /// MENTIONS a variable the witness names can be moved by it, so the index
    /// turns the sweep into a visit of the candidates.
    ///
    /// Soundness rests on the index being a SUPERSET of the truth, never a
    /// subset: a missing entry would let a moved slot pass as untouched. So
    /// it is append-only — entries are never removed when a slot is deleted
    /// or holed, because a stale id merely costs one `subst_c` call that
    /// answers exactly — and it is cleared wholesale, next to `slots`,
    /// wherever `slots` is replaced rather than appended to.
    var_occ: std::collections::HashMap<u32, Vec<usize>>,
    /// Slot contributions offered by the bridge checks of the rule currently
    /// being executed, in the order the rule will add its constraints.
    pending: std::collections::VecDeque<SlotOutcome>,
    /// CORE constraints that left the core set over the run.
    ///
    /// This is the one number the BACKWARD invariant `VeriPbCore.DbBack`
    /// turns on. `dbBack_append` is unconditional, so every rule that ADDS --
    /// `red`, `dom`, solution exclusion, the assertion rules, whatever `F`
    /// does not entail -- costs it nothing. `dbBack_delete_checked` is the
    /// only leg carrying an obligation, and there is deliberately no
    /// unchecked-delete leg because the invariant genuinely does not survive
    /// one (`ctrl_dbBack_fails_on_unchecked_delete`).
    ///
    /// So while this is zero, the current core set is reachable from
    /// `liftDB F` by `dbBack_init` followed by `dbBack_append` alone, with no
    /// obligation to discharge anywhere. Once it is nonzero the bridge would
    /// have to establish each deleted constraint's proofgoal through the
    /// kernel, which it does not yet do -- so a nonzero count is reported as
    /// its own skip rather than quietly assumed away.
    core_deletions: usize,
    /// Of those, the ones whose `dbBack_delete_checked` obligation --
    /// `forall b, HoldsAllO b (setNone i CO) -> Holds b c` -- the KERNEL
    /// discharged. The backward invariant survives a deletion only for these,
    /// so the transfer needs this to equal `core_deletions` exactly.
    core_deletions_discharged: usize,
    /// Whether the core deletion currently being processed had a MODELLED
    /// slot when it happened. `dbBack_delete_checked` needs
    /// `getO CO i = some c`, so a deletion of a holed slot names no kernel
    /// constraint and can never be credited however it was justified.
    pending_core_deletion_modelled: bool,
    /// Slots justified by solution EXCLUSION (`VeriPbCore.DbOkE.exclude`).
    /// Counted because they change what a composed run PROVES: not `Unsat F`,
    /// but that `F` has no models beyond the ones exhibited.
    excluded_slots: usize,
    /// Slots justified by `red` (`VeriPbCore.dbOkR_red_of_goals`). Counted for
    /// the same reason, and because the two do not mix -- see
    /// [`KernelShadowDb::verdict_obstacle`].
    red_slots: usize,
    /// Slots justified by an objective-improving `sol`
    /// (`VeriPbCore.DbOkB.improve`), and the bound the last one established.
    bound_slots: usize,
    bound: Option<BigInt>,
    /// The preserved universe `P` the combined induction (`VeriPbCore.DbOkF`)
    /// is instantiated at: the RUNNING UNION of every preserved variable and
    /// every objective variable the run has shown.
    ///
    /// `DbOkF` fixes `P`, and a preserved set legitimately GROWS during a run,
    /// so freezing it at first use would refuse ordinary proofs. The union is
    /// the `P` the theorem is instantiated at instead -- it contains every
    /// exclusion's variables and every objective's, which is what the
    /// `exclude` and `improve` legs need, and it only ever makes `WitFixes` on
    /// `red` HARDER, which is the safe direction.
    preserved: std::collections::BTreeSet<u32>,
    /// Why this run's slots cannot be read as ONE `DbOkF` induction, if they
    /// cannot. Distinct from [`Self::break_composition`], which asserts the
    /// shadow DESYNCHRONIZED and is a bug: this is a modelling limit, reported
    /// rather than panicked on.
    verdict_block: Option<&'static str>,
    /// Every variable any justified `red` witness has touched.
    ///
    /// Checked against `preserved` at every offer, because a `red` justified
    /// while a variable was still free is NOT covered once that variable joins
    /// `P`. The slot was already handed out by then, so the run's composition
    /// is broken rather than the single offer refused.
    red_witness_vars: std::collections::BTreeSet<u32>,
    /// How the run's CURRENT objective relates to the REFERENCE one the
    /// bounds leg transfers through.
    obju: ObjuState,
    /// The REFERENCE objective's variables: the ones `P` must contain. Set at
    /// the FIRST objective update, from the objective as it stood BEFORE it,
    /// so later updates never widen `P` -- which is the whole point, since a
    /// `red` may legitimately move a variable a later objective mentions.
    ref_objective_vars: Option<Vec<u32>>,
    /// Orders whose transitivity the kernel established, by name.
    ///
    /// `VeriPbCore.dbOkF_dom_from_preorder` takes transitivity as its only
    /// hypothesis about the order, so this set is exactly the orders a `dom`
    /// step may be justified under.
    verified_orders: std::collections::BTreeSet<String>,
    /// Whether the order currently loaded is one of them. `false` when none is
    /// loaded, which is why `dom` without an order is refused rather than
    /// silently justified.
    active_order_verified: bool,
    /// Slots justified by dominance (`VeriPbCore.DbOkF.dom`).
    dom_slots: usize,
    /// Slots deleted so far. An `obju`'s equality goals are proved from the
    /// database AS IT THEN STOOD, so a later DELETION can invalidate them: a
    /// model of the smaller database need not satisfy the equality. Growth is
    /// harmless, deletion is not, so only deletions are counted.
    deletions: usize,
    /// Slot vectors of databases swapped out by order definitions, innermost
    /// last.
    saved: Vec<(Vec<Slot>, std::collections::HashMap<u32, Vec<usize>>)>,
    /// Why holes exist, by reason.
    taints: BTreeMap<&'static str, usize>,
    /// Cleared once the shadow could not faithfully mirror the live
    /// database's *structure* (as opposed to merely failing to justify one
    /// constraint). A false value invalidates the whole composition claim.
    composed: bool,
    /// The refutation conclusion this run reached, if any.
    refutation: Option<Refutation>,
    /// Set when [`formula_cross_check`] stood down instead of comparing the
    /// stored formula against the file, carrying the reason it stood down.
    ///
    /// A stand-down leaves the *premise* of `DbOk.init` unchecked — that the
    /// `F` the slots are filled from is the `F` on disk — so it holes every
    /// formula slot (see [`shadow_init`]) and, because a formula with no
    /// constraints has no slot to hole, is also read directly by
    /// [`shadow_record_refutation`]. Composition must not be able to outlive
    /// the check it rests on.
    formula_unchecked: Option<&'static str>,
}

impl Default for KernelShadowDb {
    fn default() -> Self {
        KernelShadowDb {
            slots: Vec::new(),
            pending: std::collections::VecDeque::new(),
            excluded_slots: 0,
            red_slots: 0,
            bound_slots: 0,
            bound: None,
            verified_orders: std::collections::BTreeSet::new(),
            active_order_verified: false,
            dom_slots: 0,
            verdict_block: None,
            preserved: std::collections::BTreeSet::new(),
            red_witness_vars: std::collections::BTreeSet::new(),
            obju: ObjuState::Unchanged,
            ref_objective_vars: None,
            deletions: 0,
            core_deletions: 0,
            core_deletions_discharged: 0,
            pending_core_deletion_modelled: false,
            var_occ: std::collections::HashMap::new(),
            saved: Vec::new(),
            taints: BTreeMap::new(),
            composed: true,
            refutation: None,
            formula_unchecked: None,
        }
    }
}

impl KernelShadowDb {
    /// The slot mirroring live database id `id`; out-of-range ids read as
    /// unmirrored holes rather than panicking.
    fn slot(&self, id: usize) -> &Slot {
        const OUT_OF_RANGE: Slot = Slot::Hole("shadow-id-out-of-range");
        self.slots.get(id).unwrap_or(&OUT_OF_RANGE)
    }

    /// Record the variables of the slot at `id` in [`Self::var_occ`].
    ///
    /// Called for every `Slot::Present` the shadow ever holds — the two
    /// construction sites are `shadow_init` and `shadow_record_added`. A slot
    /// that is not `Present` contributes nothing, since only `Present` slots
    /// are candidates for the `substDB w DB = DB` premise.
    fn index_slot(&mut self, id: usize) {
        let Some(Slot::Present(c)) = self.slots.get(id) else {
            return;
        };
        for v in c.vars() {
            self.var_occ.entry(v).or_default().push(id);
        }
    }

    /// Record why a hole exists.
    fn taint(&mut self, reason: &'static str) {
        self.taint_n(reason, 1);
    }

    /// Record `n` holes that exist for the same reason, in one go. The census
    /// counts *holes*, so a stand-down that holes many slots at once must
    /// count all of them.
    fn taint_n(&mut self, reason: &'static str, n: usize) {
        *self.taints.entry(reason).or_insert(0) += n;
    }

    /// The shadow could not mirror the live database's structure. This is
    /// unrecoverable for the run: no later slot can be trusted to line up
    /// with the id the live checker means.
    fn break_composition(&mut self, reason: &'static str) {
        debug_assert!(false, "kernel shadow database desynchronized: {reason}");
        self.composed = false;
        self.taint(reason);
    }

    /// Total number of tainted holes.
    fn total_taints(&self) -> usize {
        self.taints.values().sum()
    }

    /// `reason x n, ...`, or `none`.
    /// Why this run's slots cannot be read as one induction, if they cannot.
    ///
    /// `VeriPbCore.DbOkE` has no `red` constructor and that is not an
    /// oversight: redundance hands back a DIFFERENT assignment, and the
    /// enumeration invariant is a claim about the model you started with, so
    /// a rule that replaces it says nothing about whether that model was
    /// exhibited. Combining them needs side conditions on preserved variables
    /// that are not modelled here. A run using both is refused rather than
    /// composed under whichever theorem happens to be named.
    fn verdict_obstacle(&self) -> Option<&'static str> {
        // `VeriPbCore.DbOkF` is ONE induction carrying all five legs --
        // derivation, deletion, redundance, exclusion and improvement -- so a
        // run mixing them is an instance of it like any other. Mixture is no
        // longer an obstacle by itself; what remains is whether the run stayed
        // inside the theorem's side conditions, which is what
        // [`Self::verdict_block`] records.
        self.verdict_block
    }

    /// Is this taint an ASSUMPTION the surrounding subproof discharges, rather
    /// than something the kernel could not justify?
    ///
    /// The distinction is the difference between a census that means something
    /// and one that does not. A subproof stores its premise -- the negated
    /// constraint, an order premise, a proofgoal premise -- as a slot, and
    /// those slots are not kernel-justified because an assumption is not a
    /// theorem. Reporting them beside genuine gaps made the gap look an order
    /// of magnitude larger than it is: measured on this corpus, 96% of every
    /// "tainted hole" was a premise.
    ///
    /// They stay HOLES for justification purposes -- nothing derived from one
    /// is justified, which is the conservative direction and is why an
    /// assumption cannot escape its subproof. Only the reporting changes.
    fn is_premise(reason: &str) -> bool {
        reason.ends_with("-premise")
    }

    /// Slots that are premises of some subproof.
    fn premise_count(&self) -> usize {
        self.taints
            .iter()
            .filter(|(r, _)| Self::is_premise(r))
            .map(|(_, n)| *n)
            .sum()
    }

    /// Slots the kernel could not justify and which are NOT premises.
    fn gap_count(&self) -> usize {
        self.total_taints() - self.premise_count()
    }

    fn taint_census(&self) -> String {
        let render = |premises: bool| -> String {
            let mut s = String::new();
            for (reason, n) in self
                .taints
                .iter()
                .filter(|(r, _)| Self::is_premise(r) == premises)
            {
                if !s.is_empty() {
                    s.push_str(", ");
                }
                s.push_str(&format!("{reason} x{n}"));
            }
            s
        };
        let gaps = render(false);
        let premises = render(true);
        match (gaps.is_empty(), premises.is_empty()) {
            (true, true) => "none".to_string(),
            (true, false) => format!("none; subproof premises: {premises}"),
            (false, true) => gaps,
            (false, false) => format!("{gaps}; subproof premises: {premises}"),
        }
    }
}

/// Create the shadow database for a run, if `--kernel-verify` is on.
pub fn new_shadow(kernel_verify: bool) -> Option<KernelShadowDb> {
    kernel_verify.then(KernelShadowDb::default)
}

/// Fill the shadow's initial slots from the constraints the checker
/// **stored** for the formula, and check that those are the constraints the
/// formula file on disk actually spells.
///
/// The first half is `VeriPbCore.DbOk.init`: `dbEntailed_init` gives
/// `Entails F c` for every constraint of `F`, and `VeriPbCore.entails_normC`
/// lifts that to the `normC` image the slot holds.
///
/// The second half is [`formula_cross_check`], and it is what makes the `F`
/// in that sentence mean the file rather than the parser's opinion of it. It
/// is the only part of the bridge that is not a claim about an inference: it
/// is a claim about the *input*, and the kernel has nothing to say about it,
/// so it is stated as a comparison between two independent readings rather
/// than as a theorem.
///
/// The two halves are **not** independent, and this function is where that is
/// enforced. A slot filled by the first half asserts `Entails F c` for `F`
/// the formula on disk; all the first half can see is the formula the parser
/// stored, and only the second half closes that gap. So when the second half
/// stands down — an unreadable file, a reader refusal, a constraint the
/// kernel cannot hold — every slot it would have underwritten becomes a
/// [`Slot::Hole`] carrying the stand-down's own reason, and the run's taint
/// census says so. Before that, a stand-down was invisible past this
/// function: a proof over the `#`-terminated formula the second reader will
/// not read still printed `COMPOSED: ... over the stored formula` with `0
/// tainted hole(s) ... none`, which is precisely the sentence this crate
/// exists to qualify.
///
/// On divergence, returns the error together with the zero-based line of the
/// formula file to attribute it to.
pub fn shadow_init(
    context: &mut crate::context::Context,
    database: &Database,
) -> Result<(), (CheckingError, usize)> {
    let Some(shadow) = context.kernel_shadow.as_mut() else {
        return Ok(());
    };
    shadow.slots.clear();
    // Cleared next to `slots`: the index is append-only within a database,
    // so a wholesale replacement of the slots must replace it too.
    shadow.var_occ.clear();
    shadow.slots.reserve(database.entries.len());
    for entry in database.entries.iter() {
        let slot = match entry {
            // Live id 0 is the never-populated dummy entry.
            None => Slot::Deleted,
            Some(c) => match AnyConstraint::normalized_from_live(&c.constraint) {
                Some(n) => Slot::Present(n),
                // NOTE: since the kernel gained its BigInt domain this can no
                // longer fire on a wide COEFFICIENT -- `Big::narrow` is total.
                // The one remaining way to reach it is a variable index above
                // `u32`, which is why the name is kept in the `width_limited`
                // family and pinned by the snapshot vocabulary.
                None => Slot::Hole("formula-not-i64-representable"),
            },
        };
        if let Slot::Hole(reason) = slot {
            shadow.taint(reason);
        }
        shadow.slots.push(slot);
        shadow.index_slot(shadow.slots.len() - 1);
    }
    let stood_down = formula_cross_check(context, database)?;
    if let Some(reason) = stood_down {
        let shadow = context
            .kernel_shadow
            .as_mut()
            .expect("the shadow exists: it was borrowed above");
        shadow.formula_unchecked = Some(reason);
        let mut holed = 0usize;
        for slot in shadow.slots.iter_mut() {
            // Only the slots the cross-check underwrites. A `Deleted` slot
            // (live id 0) claims nothing, and a slot that is already a hole
            // is already counted under its own reason.
            if matches!(slot, Slot::Present(_)) {
                *slot = Slot::Hole(reason);
                holed += 1;
            }
        }
        shadow.taint_n(reason, holed);
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// The formula cross-check: is the stored formula the file on disk?
// ---------------------------------------------------------------------------

/// The shape both readings of a constraint are reduced to before they are
/// compared: the kernel's proved normal form, terms sorted by
/// `(variable, polarity)`, every value widened to `BigInt`.
///
/// Widening the *result* is what lets one comparison span both coefficient
/// tiers. It is exact in both directions that matter here — `i64 -> BigInt`
/// loses nothing — and §7.2's randomized
/// `the_two_domains_agree_wherever_the_narrow_one_accepts` is the statement
/// that the narrow normal form widened is the wide normal form, so a
/// constraint that normalizes narrow and one that only normalizes wide are
/// still being compared on the same object.
type CanonicalConstraint = (Vec<(u32, bool, BigInt)>, BigInt);

/// An objective reduced to "coefficient on the positive literal, per
/// variable, plus a constant".
///
/// The kernel has no objective model (§5 item 5), so there is no `normC` to
/// lean on and this canonical form is computed here, in exact `BigInt`, from
/// the one identity involved: `c·~x = c - c·x`. Both readings go through the
/// same four lines, so what is being compared is the objective's *meaning*
/// rather than which literal each side chose to spell it with.
type CanonicalObjective = (BTreeMap<u32, BigInt>, BigInt);

/// A dense `u32` numbering of variable **names**, built fresh for the
/// cross-check.
///
/// Neither side's own variable indices are usable here. The checker's are
/// assigned in interning order, which is an implementation detail a
/// cross-check must not depend on; the file's are, for DIMACS, the literal
/// magnitudes, which can be far outside `u32` (defect 17's literal is
/// `2^63 - 1`). Names are the one thing the *format* fixes, so the
/// comparison happens on names — which is also what turns "this parser
/// interned `1` and `01` as different variables" from a shared assumption
/// into a mismatch.
#[derive(Default)]
struct VarIndex {
    by_name: AHashMap<String, u32>,
    names: Vec<String>,
}

impl VarIndex {
    /// The index for `name`, allocating one on first sight. `None` only when
    /// the formula mentions more than `u32::MAX` distinct variables, which is
    /// the kernel's `Lit` limit rather than this table's.
    fn intern(&mut self, name: &str) -> Option<u32> {
        if let Some(idx) = self.by_name.get(name) {
            return Some(*idx);
        }
        let idx = u32::try_from(self.names.len()).ok()?;
        self.by_name.insert(name.to_string(), idx);
        self.names.push(name.to_string());
        Some(idx)
    }

    fn name(&self, idx: u32) -> &str {
        &self.names[idx as usize]
    }

    /// Render a canonical constraint the way an OPB line spells it, for the
    /// divergence message.
    fn render(&self, c: &CanonicalConstraint) -> String {
        let mut out = String::new();
        for (var, negated, coeff) in &c.0 {
            out.push_str(&format!(
                "{coeff} {}{} ",
                if *negated { "~" } else { "" },
                self.name(*var)
            ));
        }
        out.push_str(&format!(">= {}", c.1));
        out
    }

    /// Render a canonical objective, likewise.
    fn render_objective(&self, o: &CanonicalObjective) -> String {
        let mut out = String::new();
        for (var, coeff) in &o.0 {
            out.push_str(&format!("{coeff} {} ", self.name(*var)));
        }
        out.push_str(&o.1.to_string());
        out
    }
}

/// The proved normal form of `sum coeff * lit >= degree`, at the narrowest
/// tier that can express it.
///
/// The tier dispatch is [`tiered_outcome`]'s, specialised: try `i64`, and if
/// anything there does not fit — a coefficient, the degree, or a value
/// `normC` computes on the way — try `Big`, where nothing refuses on width.
/// `None` therefore means only that the *variable indices* are outside the
/// kernel's `u32`, which [`VarIndex`] has already made unreachable for any
/// formula with fewer than `u32::MAX` variables.
fn canonical_constraint(
    terms: &[(BigInt, kernel::Lit)],
    degree: &BigInt,
) -> Option<CanonicalConstraint> {
    fn at<C: Tier>(
        terms: &[(BigInt, kernel::Lit)],
        degree: &BigInt,
    ) -> Option<CanonicalConstraint> {
        let mut kernel_terms = Vec::with_capacity(terms.len());
        for (coeff, lit) in terms {
            kernel_terms.push(kernel::Term {
                coeff: C::from_bigint(coeff)?,
                lit: *lit,
            });
        }
        let c = kernel::Constraint::new(kernel_terms, C::from_bigint(degree)?);
        let mut n = normalize(&c).ok()?;
        n.terms.sort_by_key(|t| (t.lit.var, t.lit.negated));
        Some((
            n.terms
                .iter()
                .map(|t| (t.lit.var, t.lit.negated, C::to_bigint(&t.coeff)))
                .collect(),
            C::to_bigint(&n.degree),
        ))
    }
    at::<kernel::Coeff>(terms, degree).or_else(|| at::<Big>(terms, degree))
}

/// Reduce an objective to [`CanonicalObjective`] by rewriting every negated
/// literal with `c·~x = c - c·x` and dropping the terms that cancel to zero.
fn canonical_objective(
    terms: impl Iterator<Item = (BigInt, u32, bool)>,
    mut constant: BigInt,
) -> CanonicalObjective {
    let mut coeffs: BTreeMap<u32, BigInt> = BTreeMap::new();
    for (coeff, var, negated) in terms {
        let entry = coeffs.entry(var).or_insert_with(|| BigInt::from(0));
        if negated {
            constant += &coeff;
            *entry -= coeff;
        } else {
            *entry += coeff;
        }
    }
    coeffs.retain(|_, c| *c != BigInt::from(0));
    (coeffs, constant)
}

/// How a stored constraint's variable index is turned back into the name the
/// *format* knows that variable by.
#[derive(Clone, Copy, PartialEq, Eq)]
enum StoredNaming {
    /// OPB and WCNF: every index the checker holds was handed out by its own
    /// `VarNameManager` when the parser interned a name, so the table is both
    /// authoritative and total. An index outside it is impossible by
    /// construction, and is treated as a name no format can produce
    /// (`#unnamed-<idx>`) rather than as a panic on the out-of-range lookup.
    Table,
    /// DIMACS CNF: the stored index **is** the DIMACS index — the CNF parser
    /// is the one place a `Lit` is built from untrusted text rather than from
    /// the name table — and `proof_format_overview.md` fixes what that index
    /// is called: "the variable `i` in the DIMACS CNF format is represented by
    /// `x<i>`". Going through the name table here would instead make the
    /// comparison depend on the `p cnf` header, which sizes the table: under
    /// `--lenient-header-counts` an under-declared header leaves a perfectly
    /// legitimate clause naming a variable the table does not reach, and the
    /// cross-check would report a divergence about the header rather than
    /// about the formula. Reading the index by the format's own rule is both
    /// the faithful reading and one less thing shared with the parser.
    DimacsIndex,
}

/// The name the format knows the stored variable `var` by.
fn stored_var_name(var: usize, var_names: &impl VarNameLookup, naming: StoredNaming) -> String {
    match naming {
        StoredNaming::DimacsIndex => format!("x{var}"),
        StoredNaming::Table if var < var_names.len() => var_names.get_name(var).to_string(),
        StoredNaming::Table => format!("#unnamed-{var}"),
    }
}

/// Resolves a stored variable index to a [`VarIndex`] slot, remembering what
/// it decided.
///
/// The mapping index -> name -> comparison index is a *function*, so
/// recomputing it per term is pure waste; on a formula with a million rows
/// that is a million `format!` allocations and a million hash lookups on a
/// freshly built `String`. The cache is keyed on the live index rather than
/// on a table position because a DIMACS index need not fit one (see
/// [`StoredNaming::DimacsIndex`]).
#[derive(Default)]
struct StoredVars {
    seen: AHashMap<usize, u32>,
}

impl StoredVars {
    fn index_of(
        &mut self,
        var: usize,
        var_names: &impl VarNameLookup,
        naming: StoredNaming,
        index: &mut VarIndex,
    ) -> Option<u32> {
        if let Some(idx) = self.seen.get(&var) {
            return Some(*idx);
        }
        let idx = index.intern(&stored_var_name(var, var_names, naming))?;
        self.seen.insert(var, idx);
        Some(idx)
    }
}

/// The terms and degree of a constraint the checker **stored**, with each
/// variable resolved back to the name the format knows it by.
fn stored_constraint_terms(
    c: &PBConstraintEnum,
    var_names: &impl VarNameLookup,
    naming: StoredNaming,
    vars: &mut StoredVars,
    index: &mut VarIndex,
) -> Option<(Vec<(BigInt, kernel::Lit)>, BigInt)> {
    let mut terms = Vec::with_capacity(c.len());
    for i in 0..c.len() {
        let term = c.get_term(i)?;
        terms.push((
            term.get_coeff().clone(),
            kernel::Lit {
                var: vars.index_of(term.lit.get_var(), var_names, naming, index)?,
                negated: term.lit.is_negated(),
            },
        ));
    }
    // The same per-variant reading as `to_kernel`, in `BigInt` so the tier
    // choice can be made after the fact rather than before.
    let degree = match c {
        PBConstraintEnum::Clause(_) => BigInt::from(1),
        PBConstraintEnum::Cardinality(card) => BigInt::from(*card.get_degree()),
        PBConstraintEnum::GeneralPBI64(g) => BigInt::from(*g.get_degree()),
        PBConstraintEnum::GeneralPBI128(g) => BigInt::from(*g.get_degree()),
        PBConstraintEnum::GeneralPBBigInt(g) => g.get_degree().clone(),
    };
    Some((terms, degree))
}

/// The terms and degree of a constraint the second reader read.
fn file_constraint_terms(
    c: &second_reader::Constraint,
    index: &mut VarIndex,
) -> Option<(Vec<(BigInt, kernel::Lit)>, BigInt)> {
    let mut terms = Vec::with_capacity(c.terms.len());
    for t in &c.terms {
        terms.push((
            t.coeff.clone(),
            kernel::Lit {
                var: index.intern(&t.var)?,
                negated: t.negated,
            },
        ));
    }
    Some((terms, c.degree.clone()))
}

/// Read the formula file a second time, or say why a second reading of the
/// *same bytes* is not available.
///
/// The cross-check reads the formula **by path**, after the checker's parser
/// has already read it. That is only sound for a path that denotes the same,
/// rewindable bytes twice, and a shell hands the checker paths that do not:
///
/// * a FIFO, or the `/dev/fd/N` of a process substitution
///   (`veripb --kernel-verify <(cat f.opb) proof.pbp`): the first reader
///   consumed the bytes, so a second read returns nothing — and opening a
///   FIFO with no writer *blocks*, which is why the file type is checked with
///   `stat` and not by opening it;
/// * `/dev/stdin` and `/dev/fd/N` on macOS even when they lead to a regular
///   file: opening them **dups the descriptor** rather than reopening the
///   object, so the second read starts wherever the first one stopped.
///   `stat` reports the underlying regular file and cannot see this; a
///   freshly opened file is always at offset zero, so a nonzero starting
///   offset is exactly the signal.
///
/// Every one of these used to make the second reading look like a truncated
/// file and the run like a divergence — `--kernel-verify` turned an accept
/// into a `Report this.` rejection on a proof it verified without the flag,
/// which is the one thing the flag must never do. They are stand-downs now:
/// `formula-file-not-rereadable`, counted like every other stand-down and,
/// per [`shadow_init`], tainting what it did not check.
///
/// Standing down rather than teeing the parser's own byte stream is a
/// deliberate trade: teeing would cover these inputs instead of skipping
/// them, but it would put `veripb-parser` between the file and the second
/// reader, and the second reader's whole value is that nothing shared sits
/// there.
///
/// `Err` carries the skip reason and a human detail for the log.
fn reread_formula_bytes(path: &std::path::Path) -> Result<Vec<u8>, (&'static str, String)> {
    use std::io::{Read, Seek};

    let metadata =
        std::fs::metadata(path).map_err(|err| ("formula-file-unreadable", format!("{err}")))?;
    if !metadata.file_type().is_file() {
        let kind = if metadata.is_dir() {
            "a directory"
        } else {
            "a FIFO, device or socket"
        };
        return Err((
            "formula-file-not-rereadable",
            format!(
                "it is {kind} rather than a regular file, so the bytes the checker already read \
                 cannot be read a second time"
            ),
        ));
    }
    let mut file =
        std::fs::File::open(path).map_err(|err| ("formula-file-unreadable", format!("{err}")))?;
    match file.stream_position() {
        Ok(0) => {}
        Ok(offset) => {
            return Err((
                "formula-file-not-rereadable",
                format!(
                    "opening it yielded a descriptor already at offset {offset} rather than a \
                     fresh read of the file, so a second reading would start mid-file"
                ),
            ));
        }
        Err(err) => {
            return Err((
                "formula-file-not-rereadable",
                format!("it is not seekable ({err}), so it cannot be read from the start again"),
            ));
        }
    }
    let mut bytes = Vec::with_capacity(usize::try_from(metadata.len()).unwrap_or(0));
    file.read_to_end(&mut bytes)
        .map_err(|err| ("formula-file-unreadable", format!("{err}")))?;
    Ok(bytes)
}

/// Check that the constraints (and objective) the checker stored are the ones
/// the formula file spells.
///
/// This is the only check in this module that is **not** a kernel theorem,
/// and the module header says why: `DbOk.init` files whatever it is handed,
/// so the entire chain of trust below it is conditional on the parse-and-store
/// step, which no rule covers. What replaces the theorem here is
/// *independence*: `veripb-second-reader` reads the same bytes without
/// linking `veripb-parser` or `veripb-formula`, and the two readings are
/// compared **up to the kernel's proved normalization** (`normC`) and term
/// order, never byte for byte — the checker legitimately merges, flips and
/// re-tiers what it stores, and none of that is a divergence.
///
/// What *is* a divergence is a disagreement that survives normalization: two
/// readings of one file that are not the same multiset of PB constraints.
/// Then one of the two is wrong about the input, and since the checker's
/// verdict is a statement about that input, the run is rejected
/// ([`CheckingError::KernelDivergence`]).
///
/// Anything the second reader cannot decide is a **counted skip** under a
/// named reason and never a silent pass:
///
/// * `formula-file-unreadable` — the bytes could not be read at all;
/// * `formula-file-not-rereadable` — the path does not denote the same bytes
///   a second time, so there is nothing to read *again*; see
///   [`reread_formula_bytes`];
/// * `formula-second-reader-refused` — the reader could not read the file
///   under its own plain reading of the format. It is deliberately *not* the
///   authority on what is legal — the checker's parser is — so its refusal
///   stands the cross-check down instead of rejecting the proof;
/// * `formula-not-kernel-representable` — a constraint the kernel cannot hold
///   at either tier, which after [`VarIndex`] means over `u32::MAX` distinct
///   variables.
///
/// Each is counted once for the run as a *skip*, not once per constraint:
/// what stood down is the whole comparison. The returned reason is separate
/// from that counter and is what [`shadow_init`] uses to hole the slots the
/// comparison would have underwritten; those holes are counted individually,
/// because the taint census counts holes.
///
/// Returns `Ok(None)` when the two readings were compared and agreed, and
/// `Ok(Some(reason))` when the comparison stood down.
fn formula_cross_check(
    context: &mut crate::context::Context,
    database: &Database,
) -> Result<Option<&'static str>, (CheckingError, usize)> {
    if !context.config.kernel_verify {
        return Ok(None);
    }
    let path = context.config.formula_path.clone();
    let (format, naming) = match crate::config::FormulaFormat::resolve(
        context.config.formula_format_override,
        &path,
    ) {
        crate::config::FormulaFormat::OPB => (second_reader::Format::Opb, StoredNaming::Table),
        crate::config::FormulaFormat::CNF => {
            (second_reader::Format::Cnf, StoredNaming::DimacsIndex)
        }
        crate::config::FormulaFormat::WCNF => (second_reader::Format::Wcnf, StoredNaming::Table),
    };

    let bytes = match reread_formula_bytes(&path) {
        Ok(bytes) => bytes,
        Err((reason, detail)) => {
            log::info!(
                "kernel-verify: not cross-checking the stored formula against '{}': {detail}",
                path.display()
            );
            context.kernel_stats.skip(reason);
            return Ok(Some(reason));
        }
    };
    let file = match second_reader::read(&bytes, format) {
        Ok(file) => file,
        Err(err) => {
            log::info!(
                "kernel-verify: the independent formula reader could not read '{}' ({err}), so the \
                 stored formula is not cross-checked against it",
                path.display()
            );
            context.kernel_stats.skip("formula-second-reader-refused");
            return Ok(Some("formula-second-reader-refused"));
        }
    };

    let mut index = VarIndex::default();
    let mut stored_vars = StoredVars::default();
    let mut stored: Vec<CanonicalConstraint> = Vec::with_capacity(database.entries.len());
    for entry in database.entries.iter().flatten() {
        let Some((terms, degree)) = stored_constraint_terms(
            &entry.constraint,
            &context.var_names,
            naming,
            &mut stored_vars,
            &mut index,
        ) else {
            context
                .kernel_stats
                .skip("formula-not-kernel-representable");
            return Ok(Some("formula-not-kernel-representable"));
        };
        let Some(canonical) = canonical_constraint(&terms, &degree) else {
            context
                .kernel_stats
                .skip("formula-not-kernel-representable");
            return Ok(Some("formula-not-kernel-representable"));
        };
        stored.push(canonical);
    }
    // Kept alongside the canonical form so a mismatch can name the line of
    // the file it came from rather than only the constraint.
    let mut from_file: Vec<(CanonicalConstraint, usize)> =
        Vec::with_capacity(file.constraints.len());
    for c in &file.constraints {
        let Some((terms, degree)) = file_constraint_terms(c, &mut index) else {
            context
                .kernel_stats
                .skip("formula-not-kernel-representable");
            return Ok(Some("formula-not-kernel-representable"));
        };
        let Some(canonical) = canonical_constraint(&terms, &degree) else {
            context
                .kernel_stats
                .skip("formula-not-kernel-representable");
            return Ok(Some("formula-not-kernel-representable"));
        };
        from_file.push((canonical, c.line));
    }

    let diverged = |detail: String, line: usize| {
        (
            CheckingError::KernelDivergence(format!(
                "the constraints the checker stored are not the constraints the formula file \
                 '{}' spells ({detail}). The proof may well be correct about what was stored; \
                 what was stored is not the input",
                path.display()
            )),
            line,
        )
    };

    // The checker files the formula's constraints at ids `1, 2, ...` in the
    // order it read them, so the two readings normally line up position for
    // position, and that comparison is linear and needs no ordering on
    // constraints at all. Only when it fails is the question re-asked as a
    // *multiset* one, because the order is not part of what `DbOk.init`
    // claims (`Entails F c` for each `c` of `F`) and a permutation is not a
    // divergence.
    let aligned = from_file.len() == stored.len()
        && from_file
            .iter()
            .zip(stored.iter())
            .all(|(file_entry, stored_entry)| file_entry.0 == *stored_entry);
    if !aligned {
        stored.sort();
        from_file.sort_by(|a, b| a.0.cmp(&b.0));
        for (file_entry, stored_entry) in from_file.iter().zip(stored.iter()) {
            if file_entry.0 != *stored_entry {
                let line = file_entry.1;
                return Err(diverged(
                    format!(
                        "the file has '{}' (line {line}) where the checker stored '{}'",
                        index.render(&file_entry.0),
                        index.render(stored_entry),
                    ),
                    line.saturating_sub(1),
                ));
            }
        }
        match from_file.len().cmp(&stored.len()) {
            std::cmp::Ordering::Greater => {
                let extra = &from_file[stored.len()];
                return Err(diverged(
                    format!(
                        "the file has {} constraint(s), the checker stored {}; the first \
                         unmatched one is '{}' at line {}",
                        from_file.len(),
                        stored.len(),
                        index.render(&extra.0),
                        extra.1,
                    ),
                    extra.1.saturating_sub(1),
                ));
            }
            std::cmp::Ordering::Less => {
                return Err(diverged(
                    format!(
                        "the file has {} constraint(s), the checker stored {}; the first \
                         unmatched one is '{}'",
                        from_file.len(),
                        stored.len(),
                        index.render(&stored[from_file.len()]),
                    ),
                    0,
                ));
            }
            // A permutation of the same multiset: every position differed,
            // but nothing is missing and nothing is extra.
            std::cmp::Ordering::Equal => {}
        }
    }

    // The objective is part of the file and part of every optimization
    // verdict, so it is cross-checked too — separately, because the kernel
    // has no objective model to normalize it with (§5 item 5) and because
    // for WCNF it is where the whole soft-clause half of the format lands.
    let mut objectives_checked = 0usize;
    // Both sides bail rather than dropping a term they cannot number: an
    // objective silently missing a term would compare equal to one that never
    // had it. (`intern` only refuses past `u32::MAX` distinct variables.)
    let mut file_objective = None;
    if let Some(o) = file.objective.as_ref() {
        let mut terms = Vec::with_capacity(o.terms.len());
        for t in &o.terms {
            // Most names here are already interned; a variable that occurs in
            // the objective and in no constraint is normal (it is what a WCNF
            // unit soft clause produces).
            let Some(var) = index.intern(&t.var) else {
                context
                    .kernel_stats
                    .skip("formula-not-kernel-representable");
                return Ok(Some("formula-not-kernel-representable"));
            };
            terms.push((t.coeff.clone(), var, t.negated));
        }
        file_objective = Some(canonical_objective(terms.into_iter(), o.constant.clone()));
    }
    let mut stored_objective = None;
    if let Some(o) = context.objective.as_ref() {
        let mut terms = Vec::with_capacity(o.terms.len());
        for term in o.terms.values() {
            let name = stored_var_name(term.lit.get_var(), &context.var_names, naming);
            let Some(var) = index.intern(&name) else {
                context
                    .kernel_stats
                    .skip("formula-not-kernel-representable");
                return Ok(Some("formula-not-kernel-representable"));
            };
            terms.push((term.coeff.clone(), var, term.lit.is_negated()));
        }
        stored_objective = Some(canonical_objective(terms.into_iter(), o.constant.clone()));
    }
    if file_objective != stored_objective {
        let render = |o: &Option<CanonicalObjective>| match o {
            None => "no objective".to_string(),
            Some(o) => format!("'min: {}'", index.render_objective(o)),
        };
        return Err(diverged(
            format!(
                "the file has {} where the checker stored {}",
                render(&file_objective),
                render(&stored_objective),
            ),
            0,
        ));
    }
    if file_objective.is_some() {
        objectives_checked = 1;
    }

    context.kernel_stats.formula_constraints_cross_checked = stored.len();
    context.kernel_stats.formula_objectives_cross_checked = objectives_checked;
    Ok(None)
}

/// Cross-check the OUTPUT formula the way the input formula is cross-checked.
///
/// `output ... FILE` decides a verdict about a file, and until this existed
/// the only reading of that file was the checker's own parser. The input
/// formula has had a second, independent reader since the shadow database was
/// built; the output formula had none, so a parser bug that dropped or
/// mis-signed an output constraint would have been invisible on both sides of
/// the comparison — the checker would have compared its own misreading against
/// the database and found them consistent.
///
/// The claim being underwritten is narrow and worth stating exactly: the
/// constraints `output.rs` goes on to look up in the core are the constraints
/// the output file spells. It says nothing about whether the equivalence
/// *guarantee* holds — that is the kernel's job, and for everything but
/// `DERIVABLE` it is still unmodelled (§5). What it removes is the asymmetry
/// where one of the two formulas a verdict ranges over was trusted to a single
/// reader.
///
/// Stands down, rather than failing, when the file cannot be re-read or the
/// second reader refuses it — the same fail-soft shape as the input check,
/// counted as a skip so the census shows it.
pub fn output_formula_cross_check(
    context: &mut crate::context::Context,
    parsed: &[&PBConstraintEnum],
) -> Result<(), CheckingError> {
    if !context.config.kernel_verify {
        return Ok(());
    }
    let Some(path) = context.config.output_formula.clone() else {
        return Ok(());
    };
    let (format, naming) = match crate::config::FormulaFormat::resolve(
        context.config.formula_format_override,
        &path,
    ) {
        crate::config::FormulaFormat::OPB => (second_reader::Format::Opb, StoredNaming::Table),
        // `output` with a CNF output formula is refused before this point, so
        // reaching here with one would mean that refusal moved. Stand down
        // rather than cross-check under a naming convention that is not the
        // one the checker parsed with.
        crate::config::FormulaFormat::CNF => {
            context
                .kernel_stats
                .skip("output-formula-cnf-not-cross-checked");
            return Ok(());
        }
        crate::config::FormulaFormat::WCNF => (second_reader::Format::Wcnf, StoredNaming::Table),
    };

    let bytes = match reread_formula_bytes(&path) {
        Ok(bytes) => bytes,
        Err((reason, detail)) => {
            log::info!(
                "kernel-verify: not cross-checking the parsed output formula against '{}': \
                 {detail}",
                path.display()
            );
            context.kernel_stats.skip(reason);
            return Ok(());
        }
    };
    let file = match second_reader::read(&bytes, format) {
        Ok(file) => file,
        Err(err) => {
            log::info!(
                "kernel-verify: the independent formula reader could not read the output formula \
                 '{}' ({err}), so it is not cross-checked",
                path.display()
            );
            context
                .kernel_stats
                .skip("output-formula-second-reader-refused");
            return Ok(());
        }
    };

    let mut index = VarIndex::default();
    let mut vars = StoredVars::default();
    let mut mine: Vec<CanonicalConstraint> = Vec::with_capacity(parsed.len());
    for c in parsed {
        let Some((terms, degree)) =
            stored_constraint_terms(c, &context.var_names, naming, &mut vars, &mut index)
        else {
            context
                .kernel_stats
                .skip("output-formula-not-kernel-representable");
            return Ok(());
        };
        let Some(canonical) = canonical_constraint(&terms, &degree) else {
            context
                .kernel_stats
                .skip("output-formula-not-kernel-representable");
            return Ok(());
        };
        mine.push(canonical);
    }
    let mut from_file: Vec<(CanonicalConstraint, usize)> =
        Vec::with_capacity(file.constraints.len());
    for c in &file.constraints {
        let Some((terms, degree)) = file_constraint_terms(c, &mut index) else {
            context
                .kernel_stats
                .skip("output-formula-not-kernel-representable");
            return Ok(());
        };
        let Some(canonical) = canonical_constraint(&terms, &degree) else {
            context
                .kernel_stats
                .skip("output-formula-not-kernel-representable");
            return Ok(());
        };
        from_file.push((canonical, c.line));
    }

    let diverged = |detail: String| {
        CheckingError::KernelDivergence(format!(
            "the constraints the checker parsed out of the output formula '{}' are not the \
             constraints that file spells ({detail}). The `output` verdict would have been \
             about a formula that is not the one on disk",
            path.display()
        ))
    };

    // A multiset comparison, with no alignment fast path: unlike the input
    // formula, nothing downstream depends on the ORDER of the output
    // constraints. `output.rs` looks each one up in the core and then checks
    // every core constraint was marked, which is a set claim both ways, so a
    // permutation is not a divergence and there is no position to preserve.
    mine.sort();
    from_file.sort_by(|a, b| a.0.cmp(&b.0));
    for (file_entry, entry) in from_file.iter().zip(mine.iter()) {
        if file_entry.0 != *entry {
            return Err(diverged(format!(
                "the file has '{}' (line {}) where the checker parsed '{}'",
                index.render(&file_entry.0),
                file_entry.1,
                index.render(entry),
            )));
        }
    }
    match from_file.len().cmp(&mine.len()) {
        std::cmp::Ordering::Greater => {
            let extra = &from_file[mine.len()];
            return Err(diverged(format!(
                "the file has {} constraint(s), the checker parsed {}; the first unmatched one \
                 is '{}' at line {}",
                from_file.len(),
                mine.len(),
                index.render(&extra.0),
                extra.1,
            )));
        }
        std::cmp::Ordering::Less => {
            return Err(diverged(format!(
                "the file has {} constraint(s), the checker parsed {}; the first unmatched one \
                 is '{}'",
                from_file.len(),
                mine.len(),
                index.render(&mine[from_file.len()]),
            )));
        }
        std::cmp::Ordering::Equal => {}
    }

    context.kernel_stats.output_constraints_cross_checked = mine.len();
    Ok(())
}

/// The live checker's witness, presented as the kernel's `Wit`.
///
/// The two vocabularies are the same one: `VeriPbCore.WitVal` is
/// keep/true/false/literal and `SubstitutionValue` is literal-or-truth-value,
/// with "absent from the map" meaning the variable is left alone. Keeping the
/// kernel witness TOTAL is what makes `applyA` an ordinary assignment, so the
/// adapter answers `Keep` for everything outside the support rather than
/// refusing.
///
/// A variable index above `u32`, or a substituted literal whose variable is,
/// cannot be named in the kernel's `Lit`. Those answer `None` through
/// [`RedWitness::get_checked`], and the caller refuses the whole step --
/// answering `Keep` for them would silently claim the witness leaves a
/// variable alone when it does not.
struct RedWitness<'a>(&'a Substitution);

impl RedWitness<'_> {
    fn get_checked(&self, var: u32) -> Option<kernel::subst::WitVal> {
        use kernel::subst::WitVal;
        let Some(value) = self.0.get(var as VarIdx) else {
            return Some(WitVal::Keep);
        };
        if value == SubstitutionValue::TRUE {
            return Some(WitVal::IsTrue);
        }
        if value == SubstitutionValue::FALSE {
            return Some(WitVal::IsFalse);
        }
        Some(WitVal::ToLit(kernel_lit(&value.get_lit())?))
    }

    /// Every variable the witness names is expressible in the kernel.
    fn is_expressible(&self) -> bool {
        self.0
            .syntactic_support()
            .all(|&v| u32::try_from(v).is_ok_and(|v| self.get_checked(v).is_some()))
    }
}

impl kernel::subst::Wit for RedWitness<'_> {
    fn get(&self, var: u32) -> kernel::subst::WitVal {
        // Only ever called after `is_expressible`, and fail-closed if not:
        // `Keep` is the identity, so an inexpressible witness would look
        // MORE like identity, not less -- which is why the caller must check
        // expressibility first and refuse, rather than rely on this.
        self.get_checked(var).unwrap_or(kernel::subst::WitVal::Keep)
    }
}

/// Offer the shadow contribution of a `red` step, justified by
/// `VeriPbCore.DbOkF.red`, with the per-slot proofgoal pairing that lets the
/// TOUCHED case be justified.
///
/// `dbOkR_red_of_goals` asks, for every slot `D`, that `D|w` holds. A slot the
/// witness does not move needs no goal -- `substC w D` IS `D`. A slot it DOES
/// move needs one, and `goals` is what pairs them: each entry is a slot id
/// together with the substituted constraint the checker actually made a goal
/// of.
///
/// Three things are checked for a moved slot, and none of them trusts the
/// checker's occurrences index:
///
///   1. the slot appears in `goals` at all;
///   2. the goal is the image the KERNEL computes, `subst_c(w, D)`, not
///      whatever the checker's own `substitute` produced -- if the two
///      disagree, the discharged obligation was about a different constraint;
///   3. `discharged_cleanly`, which says the goal discharges added no skip, so
///      each was kernel-justified rather than merely accepted.
///
/// A slot the index wrongly omitted has neither identity nor a matching goal,
/// so the step is refused. Over-reporting costs nothing.
pub fn offer_red(
    context: &mut crate::context::Context,
    witness: &Substitution,
    constraint: &PBConstraintEnum,
    goals: &[(usize, PBConstraintEnum)],
    discharged_cleanly: bool,
    derived_slots: &[usize],
) {
    if context.kernel_shadow.is_none() {
        return;
    }
    // `VeriPbCore.DbOkF.red` carries `WitFixes w P`, and it is what lets `red`
    // coexist with solution logging at all: the invariant keeps a COMPANION
    // model agreeing with the real one on `P`, and a witness that leaves `P`
    // alone may replace the companion freely because the replacement still
    // agrees where agreement is used. A witness that moves a preserved or
    // objective variable is refused -- that is the side condition, not a
    // conservatism.
    let p = current_preserved(context);
    let wit = RedWitness(witness);
    let outcome = if p
        .iter()
        .all(|&v| wit.get_checked(v) == Some(kernel::subst::WitVal::Keep))
    {
        red_slot(
            context,
            witness,
            constraint,
            goals,
            discharged_cleanly,
            derived_slots,
        )
    } else {
        Err("red-witness-moves-preserved")
    };
    // Apply the drops the scan decided on BEFORE the slot is offered, so the
    // shadow the offer lands in is the database the theorem was instantiated
    // at.
    let outcome = match outcome {
        Ok((slot, drops)) => {
            if let Some(shadow) = context.kernel_shadow.as_mut() {
                for id in drops {
                    if let Some(s) = shadow.slots.get_mut(id) {
                        *s = Slot::Hole("dropped-derived-slot");
                    }
                    shadow.taint("dropped-derived-slot");
                }
            }
            Ok(slot)
        }
        Err(reason) => Err(reason),
    };
    match &outcome {
        Ok(_) => {
            note_red_witness(context, witness);
            if let Some(shadow) = context.kernel_shadow.as_mut() {
                shadow.red_slots += 1;
            }
        }
        Err(reason) => context.kernel_stats.skip(reason),
    }
    shadow_offer(context, outcome);
}

fn red_slot(
    context: &crate::context::Context,
    witness: &Substitution,
    constraint: &PBConstraintEnum,
    goals: &[(usize, PBConstraintEnum)],
    discharged_cleanly: bool,
    derived_slots: &[usize],
) -> Result<(AnyConstraint, Vec<usize>), &'static str> {
    let wit = RedWitness(witness);
    if !wit.is_expressible() {
        return Err("red-witness-not-representable");
    }
    // EVERY `red` needs this, not only one whose witness moves a slot. The
    // premise of `dbOkR_red_of_goals` includes `Holds b (substC w c)` -- the
    // goal for the constraint the rule is ADDING -- which exists whatever the
    // witness does to the database. Checking it only in the moved-slot branch
    // meant a `red` over a fresh variable was granted without any evidence
    // that its own proofgoal had been kernel-discharged.
    if !discharged_cleanly {
        return Err("red-goal-discharge-not-kernel-verified");
    }
    let Some(shadow) = context.kernel_shadow.as_ref() else {
        return Err("red-witness-unmodelled");
    };

    // The `substDB w DB = DB` premise, checked slot by slot rather than
    // assumed from the absence of a proofgoal.
    // Slots the witness moves that received NO goal, and which the run is
    // entitled not to have given one: under `strengthening_to_core`,
    // `get_proofgoals` is asked with `add_derived_goals = false`, so DERIVED
    // constraints raise no obligation at all. Rather than refuse the step,
    // those slots are DROPPED -- `VeriPbCore.DbOkF.delete` is unconditional,
    // so the theorem may simply be instantiated at the database without them.
    //
    // The cost is real and is paid here rather than hidden: a dropped slot
    // becomes a hole, so anything later derived FROM it cannot be justified.
    // That is the honest accounting, because under this mode a derived
    // constraint genuinely need not survive the witness -- VeriPB's own
    // soundness rests on it being re-derivable from the core, which this
    // bridge does not re-derive.
    //
    // Only slots that MENTION a variable the witness names are visited. That
    // is not an assumption about the proof: `substC w D = D` holds outright
    // when `D` names nothing in the witness's support, since every one of its
    // literals maps to itself. Sweeping the whole database instead made this
    // quadratic in the proof length; see `KernelShadowDb::var_occ`, which is
    // append-only precisely so this candidate set can only be too large.
    let mut candidates: Vec<usize> = Vec::new();
    for v in witness.syntactic_support() {
        let Ok(v) = u32::try_from(*v) else {
            // Not expressible in the kernel -- but `is_expressible` above
            // already refused the whole step, so this is unreachable. Refuse
            // again rather than silently narrowing the candidate set.
            return Err("red-witness-not-representable");
        };
        if let Some(ids) = shadow.var_occ.get(&v) {
            candidates.extend_from_slice(ids);
        }
    }
    candidates.sort_unstable();
    candidates.dedup();
    // The index is trusted to be a SUPERSET of the slots the witness moves,
    // and that trust is what makes skipping the rest sound. Rather than leave
    // it to review, every debug run re-establishes it the expensive way: any
    // slot the index left out must genuinely be its own image. A missing
    // entry then fails the suite here instead of silently granting a `red`.
    debug_assert!(
        shadow
            .slots
            .iter()
            .enumerate()
            .all(|(id, slot)| match slot {
                Slot::Present(stored) =>
                    candidates.binary_search(&id).is_ok() || any_subst_is_identity(stored, &wit),
                _ => true,
            }),
        "var_occ missed a slot the witness moves"
    );

    // Indexed by slot id once, rather than scanned per candidate. A `red`
    // whose goals are all auto-discharged carries one goal per database
    // constraint, so the scan was n goals for each of n candidates -- the
    // second quadratic in this loop, and the dominant one (measured growth
    // 4.0x per doubling on the `red` shape of `kernel_verify_perf`).
    let mut goals_by_id: std::collections::HashMap<usize, Vec<&PBConstraintEnum>> =
        std::collections::HashMap::with_capacity(goals.len());
    for (gid, goal) in goals {
        goals_by_id.entry(*gid).or_default().push(goal);
    }

    let mut drop_slots: Vec<usize> = Vec::new();
    for id in candidates {
        let Slot::Present(stored) = shadow.slot(id) else {
            continue;
        };
        if any_subst_is_identity(stored, &wit) {
            continue;
        }
        // Moved: it needs a goal, and the goal must be the image the KERNEL
        // computes from the slot -- not the one the checker substituted.
        if !goals_by_id
            .get(&id)
            .is_some_and(|gs| gs.iter().any(|goal| goal_is_slot_image(stored, &wit, goal)))
        {
            // `binary_search`, not `contains`: this runs once per candidate
            // slot, and a linear scan over the derived ids made the pair
            // quadratic in the proof length. `derived_slot_ids` yields
            // ASCENDING ids by construction, which is what makes it valid.
            if derived_slots.binary_search(&id).is_ok() {
                drop_slots.push(id);
                continue;
            }
            // A refusal here says only "no goal covered this slot", which is
            // two very different situations: the slot got no obligation at
            // all, or it got one about a DIFFERENT constraint than the kernel
            // computes. Distinguishing them took a one-off instrumentation
            // once; it stays, because the next reader will want it too.
            if std::env::var_os("TRUST_RED_DEBUG").is_some() {
                let covered: Vec<usize> = goals.iter().map(|(g, _)| *g).collect();
                eprintln!(
                    "TRUST_RED_DEBUG refuse slot={id} had_a_goal={} \
                     goal_was_a_different_constraint={} covered={covered:?}",
                    covered.contains(&id),
                    goals
                        .iter()
                        .any(|(gid, goal)| *gid == id && !goal_is_slot_image(stored, &wit, goal)),
                );
            }
            return Err("red-witness-touches-database");
        }
    }

    // The new constraint, at the narrow tier first and widened only if it
    // does not read there -- the same tier discipline every other slot uses.
    let narrow = to_kernel::<kernel::Coeff>(constraint).and_then(|c| normalize(&c).ok());
    if let Some(c) = narrow {
        return Ok((AnyConstraint::Narrow(c), drop_slots));
    }
    let wide = to_kernel::<Big>(constraint)
        .and_then(|c| normalize(&c).ok())
        .ok_or("red-constraint-not-representable")?;
    Ok((AnyConstraint::Wide(wide), drop_slots))
}

/// Is `goal` the kernel's own image `substC w stored`?
///
/// Computed from the SLOT, then compared to the goal the checker discharged.
/// The checker's `substitute` is never taken as the statement of the
/// obligation: if the two disagree the pairing fails and the step is refused.
fn goal_is_slot_image(
    stored: &AnyConstraint,
    wit: &RedWitness<'_>,
    goal: &PBConstraintEnum,
) -> bool {
    fn at<C: Tier>(
        stored: &kernel::Constraint<C>,
        wit: &RedWitness<'_>,
        goal: &PBConstraintEnum,
    ) -> bool {
        let Ok(image) = kernel::subst::subst_c(wit, stored) else {
            return false;
        };
        let (Ok(image), Some(g)) = (normalize(&image), to_kernel::<C>(goal)) else {
            return false;
        };
        let Ok(g) = normalize(&g) else { return false };
        image == g || sort_canon(&image) == sort_canon(&g)
    }
    match stored {
        AnyConstraint::Narrow(c) => at(c, wit, goal),
        AnyConstraint::Wide(c) => at(c, wit, goal),
    }
}

/// `subst_c_is_identity` at whichever tier the slot is held.
fn any_subst_is_identity(stored: &AnyConstraint, wit: &RedWitness<'_>) -> bool {
    match stored {
        AnyConstraint::Narrow(c) => kernel::subst::subst_c_is_identity(wit, c),
        AnyConstraint::Wide(c) => kernel::subst::subst_c_is_identity(wit, c),
    }
}

/// Offer the shadow contribution of an EXCLUDING `sol`, justified by
/// `VeriPbCore.DbOkE.exclude`.
///
/// The stored constraint is the BLOCKING CLAUSE of the exhibited solution: for
/// each preserved variable, the literal that solution falsifies, at degree 1.
/// `VeriPbCore.agrees_of_not_holds_blockC` is the content -- an assignment
/// that fails that clause agrees with the solution on every variable it was
/// built over, so excluding it loses only assignments already exhibited.
///
/// This does NOT preserve satisfiability, and no widening of `DbSat` would
/// cover it: if the excluded assignment was the formula's only model, the
/// database becomes unsatisfiable while `F` is satisfiable. So a run that uses
/// it proves a DIFFERENT sentence, and
/// [`KernelShadowDb::verdict_obstacle`] is what keeps the summary from
/// claiming the old one.
///
/// Only the blocking-clause form. The IMPROVING form stores an
/// objective-bounding constraint, and the kernel has no objective at all.
pub fn offer_solution_exclusion(
    context: &mut crate::context::Context,
    constraint: &PBConstraintEnum,
) {
    if context.kernel_shadow.is_none() {
        return;
    }
    // `DbOkF.exclude` carries `SubsetN vars P`, where `vars` are the blocking
    // clause's own variables. The checker builds it over the PRESERVED set,
    // which is inside `P` by construction; checked here rather than assumed,
    // because the clause is what the theorem is instantiated at.
    let outcome = to_kernel::<kernel::Coeff>(constraint)
        .and_then(|c| normalize(&c).ok())
        .map(AnyConstraint::Narrow)
        .or_else(|| {
            to_kernel::<Big>(constraint)
                .and_then(|c| normalize(&c).ok())
                .map(AnyConstraint::Wide)
        })
        .ok_or("solution-exclusion-not-representable")
        .and_then(|slot| {
            // `SubsetN vars P` is made true by GROWING `P` to hold the clause's
            // variables, which is what the theorem is instantiated at.
            grow_preserved(context, &exclusion_vars(&slot))?;
            Ok(slot)
        });
    match &outcome {
        Ok(_) => {
            if let Some(shadow) = context.kernel_shadow.as_mut() {
                shadow.excluded_slots += 1;
            }
        }
        Err(reason) => context.kernel_stats.skip(reason),
    }
    shadow_offer(context, outcome);
}

/// Offer the shadow contribution of an IMPROVING `sol`, justified by
/// `VeriPbCore.DbOkB.improve`.
///
/// The stored constraint is the objective, negated, at degree
/// `1 + constant - value` -- which is `VeriPbCore.improveC`, and says
/// "objective strictly below `value`".
/// `VeriPbCore.bound_of_not_holds_improveC` is the content: an assignment
/// failing it has objective value at least `value`, so the constraint loses
/// only assignments no better than the one just exhibited.
///
/// The one hypothesis that is NOT free is `Int.le v bound` -- that solutions
/// IMPROVE. The kernel needs it (a model already known to be no better than
/// the old bound is only known to be no better than the new one if the new
/// one is smaller), and it is checked here against the bound the last
/// improving step established rather than assumed from the rule's name.
pub fn offer_solution_improving(
    context: &mut crate::context::Context,
    constraint: &PBConstraintEnum,
    value: &BigInt,
) {
    if context.kernel_shadow.is_none() {
        return;
    }
    // `DbOkF.improve` carries `SubsetN (termVars negObj) P`. `P` is built to
    // contain the objective's variables, so this holds by construction -- and
    // is fixed here anyway, because capturing `P` is what makes a later change
    // to it visible.
    // `P` grows by the REFERENCE objective's variables, not the current ones.
    // That is what lets a `red` move a variable a LATER objective mentions --
    // the shape every `objective_update` proof in the corpus has -- while the
    // bound still transfers, because it transfers through the reference.
    let preserved = reference_objective_vars(context)
        .ok_or("objective-variable-not-representable")
        .and_then(|vars| grow_preserved(context, &vars))
        .and_then(|()| objective_transfers(context));
    let monotone = context
        .kernel_shadow
        .as_ref()
        .is_some_and(|s| s.bound.as_ref().is_none_or(|b| value <= b));
    let outcome = if let Err(reason) = preserved {
        Err(reason)
    } else if monotone {
        to_kernel::<kernel::Coeff>(constraint)
            .and_then(|c| normalize(&c).ok())
            .map(AnyConstraint::Narrow)
            .or_else(|| {
                to_kernel::<Big>(constraint)
                    .and_then(|c| normalize(&c).ok())
                    .map(AnyConstraint::Wide)
            })
            .ok_or("objective-bound-not-representable")
    } else {
        Err("objective-bound-not-improving")
    };
    match &outcome {
        Ok(_) => {
            if let Some(shadow) = context.kernel_shadow.as_mut() {
                shadow.bound_slots += 1;
                shadow.bound = Some(value.clone());
            }
        }
        Err(reason) => context.kernel_stats.skip(reason),
    }
    shadow_offer(context, outcome);
}

/// Offer the shadow contribution of an ASSERTION whose constraint happens to
/// be an objective bound.
///
/// The `a` rule is an axiom-by-fiat in general: the format itself says a proof
/// containing it is invalid, because one could assert contradiction directly.
/// Nothing here changes that, and `assertion_used` still qualifies the verdict.
///
/// But ONE shape is not an assumption at all. `VeriPbCore.improveC` says
/// "objective strictly below `v`", and `VeriPbCore.DbOkB.improve` needs only
/// `Int.le v bound` to admit it -- NOT that a solution achieving `v` was
/// exhibited. Refuting `F` together with `obj < v` proves `obj >= v` over `F`
/// whether or not anything achieving `v` was ever shown. So an `a` that stores
/// exactly that constraint is a sound bounds step, and the kernel already has
/// its theorem.
///
/// `cand0` is `improveC` at `v = 0`, built by the CALLER with the same
/// constructors an improving `sol` uses. Recognition is then exact: normalize
/// both, require the term lists to agree, and read `v` off the degree
/// difference. Because the degree of `improveC` is affine in `v` and
/// normalization shifts it by a constant that depends only on the terms, term
/// agreement plus that `v` means the asserted constraint IS
/// `normC (improveC negObj konst v)` -- nothing is guessed.
///
/// Any other assertion keeps its hole.
pub fn offer_assertion_bound(
    context: &mut crate::context::Context,
    asserted: &PBConstraintEnum,
    cand0: &PBConstraintEnum,
) {
    if context.kernel_shadow.is_none() {
        return;
    }
    let Some((slot, value)) = assertion_bound_slot(asserted, cand0) else {
        context.kernel_stats.skip("assertion-unverified");
        shadow_offer(context, Err("assertion-unverified"));
        return;
    };
    let monotone = context
        .kernel_shadow
        .as_ref()
        .is_some_and(|s| s.bound.as_ref().is_none_or(|b| &value <= b));
    if !monotone {
        context.kernel_stats.skip("objective-bound-not-improving");
        shadow_offer(context, Err("objective-bound-not-improving"));
        return;
    }
    if let Some(shadow) = context.kernel_shadow.as_mut() {
        shadow.bound_slots += 1;
        shadow.bound = Some(value);
    }
    shadow_offer(context, Ok(slot));
}

/// The asserted constraint as an objective bound, with the `v` it bounds at,
/// or `None` when it is not one.
fn assertion_bound_slot(
    asserted: &PBConstraintEnum,
    cand0: &PBConstraintEnum,
) -> Option<(AnyConstraint, BigInt)> {
    // At the narrow tier first, then widened, the same discipline every other
    // slot uses. Both constraints must read at the SAME tier for the degree
    // difference to mean anything.
    fn at<C: Tier>(
        asserted: &PBConstraintEnum,
        cand0: &PBConstraintEnum,
    ) -> Option<(kernel::Constraint<C>, BigInt)> {
        let a = normalize(&to_kernel::<C>(asserted)?).ok()?;
        let z = normalize(&to_kernel::<C>(cand0)?).ok()?;
        // Term lists must agree up to order; the degree carries `v`.
        if sort_canon(&a).terms != sort_canon(&z).terms {
            return None;
        }
        Some((a.clone(), C::to_bigint(&z.degree) - C::to_bigint(&a.degree)))
    }
    if let Some((c, v)) = at::<kernel::Coeff>(asserted, cand0) {
        return Some((AnyConstraint::Narrow(c), v));
    }
    let (c, v) = at::<Big>(asserted, cand0)?;
    Some((AnyConstraint::Wide(c), v))
}

/// Slot ids the database holds as DERIVED rather than core.
///
/// A rule that asks `Database::get_proofgoals` with `add_derived_goals =
/// false` raises no obligation for these, so a witness that moves one has
/// nothing to pair it with. Rather than refuse the step, `offer_red` drops
/// them -- `VeriPbCore.DbOkF.delete` is unconditional, so the theorem may be
/// instantiated at the database without them.
///
/// The caller passes what it actually asked for. `red` requests derived goals
/// unless `strengthening_to_core` is on; `dom` NEVER requests them, and
/// keying this on the mode instead of on the request left every `dom` whose
/// witness moved a derived slot refused for a reason that was about `red`.
/// The ids come out ASCENDING, and `red_slot` binary-searches them; keep any
/// future construction sorted or that lookup silently starts missing slots,
/// which would refuse steps rather than accept them but would still be wrong.
pub fn derived_slot_ids(database: &Database, add_derived_goals: bool) -> Vec<usize> {
    if add_derived_goals {
        return Vec::new();
    }
    (0..database.len())
        .filter(|&i| {
            database
                .get_entry_usize(i)
                .is_ok_and(|c| !c.is_core_constraint())
        })
        .collect()
}

/// Offer the shadow contribution of a `dom` step, justified by
/// `VeriPbCore.dbOkF_dom_from_preorder`.
///
/// Dominance is redundance with one goal exchanged: `red` must SATISFY the
/// constraint it adds, `dom` must strictly DECREASE the order instead. So the
/// database side of the premise is identical -- every slot the witness moves
/// needs a discharged goal, every slot it does not is its own image -- and
/// `red_slot` does that work unchanged.
///
/// What dominance adds is the order, and the kernel needs exactly ONE property
/// of it: TRANSITIVITY. Irreflexivity is not assumed and reflexivity is not
/// used, because `Order::get_proofgoals_strict` emits the definition twice --
/// once saying `w(a) <= a`, once at the opposite scope saying NOT `a <= w(a)`
/// -- so what a step discharges is the STRICT part of the preorder, whose
/// irreflexivity is free.
///
/// Refused when no order is loaded. `dom` also admits an OBJECTIVE in place of
/// an order, and that form would need the measure built from objective values
/// rather than from the order's rank; it is not routed, and says so.
pub fn offer_dom(
    context: &mut crate::context::Context,
    witness: &Substitution,
    constraint: &PBConstraintEnum,
    goals: &[(usize, PBConstraintEnum)],
    discharged_cleanly: bool,
    derived_slots: &[usize],
) {
    if context.kernel_shadow.is_none() {
        return;
    }
    let ordered = context
        .kernel_shadow
        .as_ref()
        .is_some_and(|s| s.active_order_verified);
    if !ordered {
        let reason = if context.active_order.is_some() {
            "dom-order-not-kernel-verified"
        } else {
            "dom-without-order-unmodelled"
        };
        context.kernel_stats.skip(reason);
        shadow_offer(context, Err(reason));
        return;
    }
    // Reattributed by COMPARING the counter across the call, not by testing
    // that it is non-zero: `offer_red` increments only when it accepts, and a
    // bare `> 0` test would steal a count from an earlier `red` whenever this
    // step was refused.
    let red_before = context.kernel_shadow.as_ref().map_or(0, |s| s.red_slots);
    offer_red(
        context,
        witness,
        constraint,
        goals,
        discharged_cleanly,
        derived_slots,
    );
    if let Some(shadow) = context.kernel_shadow.as_mut() {
        // Counted apart from `red`: they are different legs of `DbOkF`, and a
        // census that merged them would hide which theorem a run leaned on.
        if shadow.red_slots == red_before + 1 {
            shadow.red_slots = red_before;
            shadow.dom_slots += 1;
        }
    }
}

/// Record whether an order definition's transitivity was kernel-established.
pub fn note_order_definition(context: &mut crate::context::Context, name: &str, verified: bool) {
    if let Some(shadow) = context.kernel_shadow.as_mut() {
        if verified {
            shadow.verified_orders.insert(name.to_string());
        } else {
            // Once unverified it STAYS unverified: a redefinition under the
            // same name would otherwise silently launder the first one.
            shadow.verified_orders.remove(name);
        }
    }
}

/// Record which order is now active, so `dom` can ask whether it is one the
/// kernel can be instantiated at. `None` unloads.
pub fn note_order_loaded(context: &mut crate::context::Context, name: Option<&str>) {
    if let Some(shadow) = context.kernel_shadow.as_mut() {
        shadow.active_order_verified = name.is_some_and(|n| shadow.verified_orders.contains(n));
    }
}

/// Grow the preserved universe `P` and re-check every `red` witness against it.
///
/// `P` is built LAZILY, from the legs that actually need it, and that is the
/// difference between a usable condition and a useless one. Only `exclude`
/// needs the blocking clause's variables in `P`; only `improve` needs the
/// objective's. A run that does neither has `P` empty, so `WitFixes` on `red`
/// costs nothing -- whereas seeding `P` with the objective up front refuses
/// every `red` that touches a problem variable, which is most of them.
///
/// The re-check is retroactive on purpose. A `red` justified while variable
/// `v` was free is NOT covered by an induction at a `P` containing `v`, and by
/// the time `v` joins `P` that slot has already been handed out -- so the
/// honest response is to break the run's composition, not to refuse the
/// current offer and leave an unsound slot standing.
fn grow_preserved(context: &mut crate::context::Context, vars: &[u32]) -> Result<(), &'static str> {
    let shadow = context
        .kernel_shadow
        .as_mut()
        .ok_or("preserved-set-unavailable")?;
    shadow.preserved.extend(vars.iter().copied());
    if !shadow.preserved.is_disjoint(&shadow.red_witness_vars) {
        // A `red` justified while this variable was free is not covered by an
        // induction at a `P` containing it, and that slot is already handed
        // out -- so the RUN cannot be read as one `DbOkF`, even though every
        // individual offer was sound when made. Recorded, not asserted: this
        // is a limit of the theorem, not a desynchronized shadow.
        shadow.verdict_block = Some("red-witness-later-preserved");
        return Err("red-witness-later-preserved");
    }
    Ok(())
}

/// The objective's variables, which the `improve` leg needs inside `P`.
fn objective_vars(context: &crate::context::Context) -> Option<Vec<u32>> {
    let objective = context.objective.as_ref()?;
    objective
        .terms
        .keys()
        .map(|&v| u32::try_from(v).ok())
        .collect()
}

/// The blocking clause's own variables, which the `exclude` leg needs inside
/// `P` (`SubsetN vars P`).
fn exclusion_vars(slot: &AnyConstraint) -> Vec<u32> {
    fn at<C: Tier>(c: &kernel::Constraint<C>) -> Vec<u32> {
        c.terms.iter().map(|t| t.lit.var).collect()
    }
    match slot {
        AnyConstraint::Narrow(c) => at(c),
        AnyConstraint::Wide(c) => at(c),
    }
}

/// `P` as it currently stands, for the `WitFixes` check on `red`.
fn current_preserved(context: &crate::context::Context) -> Vec<u32> {
    context
        .kernel_shadow
        .as_ref()
        .map(|s| s.preserved.iter().copied().collect())
        .unwrap_or_default()
}

/// Record the variables a justified `red` witness touched.
fn note_red_witness(context: &mut crate::context::Context, witness: &Substitution) {
    if let Some(shadow) = context.kernel_shadow.as_mut() {
        shadow.red_witness_vars.extend(
            witness
                .syntactic_support()
                .filter_map(|&v| u32::try_from(v).ok()),
        );
    }
}

/// Record an objective update: `verified` says both equality proofgoals were
/// kernel-discharged.
///
/// Once broken it stays broken. An unverified update means the current
/// objective is not known to agree with the reference on database models, and
/// nothing later re-establishes it.
/// Capture the REFERENCE objective's variables, which must happen BEFORE the
/// update is applied -- for the first update, the objective as it stands right
/// now IS the reference, and afterwards it is gone.
///
/// Separate from [`note_objective_update`] because a subproof `obju` applies
/// its update inside `finalize_unchecked`, while whether the update was
/// verified is only known once that same call has discharged the goals. The
/// two facts are learned at different moments and are recorded at each.
pub fn capture_reference_objective(context: &mut crate::context::Context) {
    let before = objective_vars(context);
    if let Some(shadow) = context.kernel_shadow.as_mut() {
        if shadow.ref_objective_vars.is_none() {
            shadow.ref_objective_vars = before;
        }
    }
}

pub fn note_objective_update(context: &mut crate::context::Context, verified: bool) {
    let Some(shadow) = context.kernel_shadow.as_mut() else {
        return;
    };
    shadow.obju = match (verified, &shadow.obju) {
        (_, ObjuState::Broken) | (false, _) => ObjuState::Broken,
        (true, _) => ObjuState::VerifiedAt(shadow.deletions),
    };
}

/// The variables `P` must contain for a bound to transfer: the REFERENCE
/// objective's if the run ever updated its objective, else the current one's
/// (which is then the same thing).
fn reference_objective_vars(context: &crate::context::Context) -> Option<Vec<u32>> {
    match context
        .kernel_shadow
        .as_ref()
        .and_then(|s| s.ref_objective_vars.clone())
    {
        Some(vars) => Some(vars),
        None => objective_vars(context),
    }
}

/// May a bound transfer through the reference objective right now?
fn objective_transfers(context: &crate::context::Context) -> Result<(), &'static str> {
    let shadow = context
        .kernel_shadow
        .as_ref()
        .ok_or("preserved-set-unavailable")?;
    match shadow.obju {
        ObjuState::Unchanged => Ok(()),
        // The equality was proved from the database as it then stood. Growth
        // preserves it; a deletion since does not, so refuse rather than
        // assume the deleted constraint was not one the equality used.
        ObjuState::VerifiedAt(n) if n == shadow.deletions => Ok(()),
        ObjuState::VerifiedAt(_) => Err("objective-equality-predates-deletion"),
        ObjuState::Broken => Err("objective-update-unverified"),
    }
}

/// Start a rule: drop any slot contributions the previous rule offered but
/// never used (a proofgoal discharge inside a rule that also derives, say).
pub fn shadow_begin_rule(context: &mut crate::context::Context) {
    if let Some(shadow) = context.kernel_shadow.as_mut() {
        shadow.pending.clear();
    }
}

/// Offer the shadow contribution of the constraint the current rule is about
/// to add. Consumed in order by [`shadow_record_added`].
fn shadow_offer(context: &mut crate::context::Context, slot: SlotOutcome) {
    if let Some(shadow) = context.kernel_shadow.as_mut() {
        shadow.pending.push_back(slot);
    }
}

/// Mirror one constraint addition: the live checker is about to store
/// `stored` at id `id`.
///
/// `default_taint` names the reason for rules that never offered a
/// justification — every meta-rule the kernel does not model lands here, so
/// a rule added tomorrow is a *named hole* rather than a silent trust.
pub fn shadow_record_added(
    context: &mut crate::context::Context,
    id: usize,
    stored: &PBConstraintEnum,
    default_taint: &'static str,
) {
    let Some(shadow) = context.kernel_shadow.as_mut() else {
        return;
    };
    if id != shadow.slots.len() {
        // The id space and the slot vector disagree: from here on no slot
        // index means what the live checker means by it. Taint, resync so
        // later ids at least stay addressable, and never claim composition.
        shadow.break_composition("shadow-id-desync");
        shadow.slots.resize(id, Slot::Hole("shadow-id-desync"));
    }
    let slot = match shadow.pending.pop_front() {
        None => Slot::Hole(default_taint),
        Some(Err(reason)) => Slot::Hole(reason),
        // The offered constraint must be the one the live checker stores;
        // otherwise the bridge's queue slipped against the rule's output and
        // the slot would describe a different constraint than its id.
        Some(Ok(c)) => match slot_matches_live(&c, stored) {
            Some(true) => Slot::Present(c),
            _ => {
                shadow.break_composition("shadow-slot-mismatch");
                Slot::Hole("shadow-slot-mismatch")
            }
        },
    };
    if let Slot::Hole(reason) = slot {
        shadow.taint(reason);
    }
    shadow.slots.push(slot);
    shadow.index_slot(shadow.slots.len() - 1);
}

/// Offer the backward half of an `output` equivalence, justified by
/// `VeriPbCore.output_unsat_of_unsat`.
///
/// The theorem says: with `DbBack F CO` and, for every occupied core slot, a
/// position in the output formula carrying that same constraint, an
/// unsatisfiable `F` forces an unsatisfiable output formula -- equivalently,
/// and this is the direction a user cares about, a model of what the checker
/// EMITTED yields a model of what it was GIVEN. That is the direction
/// `DbOkF` structurally cannot give, because its legs may lose models.
///
/// The three hypotheses and where each comes from:
///
/// * `DbBack F CO` -- from `dbBack_init` at the formula load, then
///   `dbBack_append` for every constraint added since. Both are
///   unconditional, so this needs no per-rule evidence at all; what it needs
///   is that no core constraint was ever DELETED, since that is the one leg
///   carrying an obligation. Hence the `core_deletions` gate.
/// * the pairing `idx` -- `pairs` carries it, built by `output` as it looked
///   each output constraint up. The kernel wants it the other way round (core
///   slot to output position), so it is inverted here and every occupied core
///   slot must be covered.
/// * that the slots really are the formula -- the shadow's own business, and
///   why a run whose formula cross-check stood down cannot use this.
///
/// Returns `None` when the transfer is justified, or `Some(reason)` naming
/// what stopped it. Every path is fail-closed: anything the bridge cannot
/// establish declines rather than assumes.
/// What the kernel could underwrite about one `output` rule.
#[derive(Clone, Copy, Debug)]
pub enum OutputTransfer {
    /// Neither direction; the reason names what stopped the backward half.
    None(&'static str),
    /// The backward half only (`output_unsat_of_unsat`); the reason names
    /// what stopped the forward one.
    Backward(&'static str),
    /// Both directions: with `output_unsat_forward_of_dbOkF` as well, the two
    /// formulas are equisatisfiable outright.
    Equivalence,
}

pub fn offer_output_equivalence(
    context: &mut crate::context::Context,
    database: &Database,
    pairs: &[(usize, usize)],
) -> OutputTransfer {
    let Some(shadow) = context.kernel_shadow.as_ref() else {
        return OutputTransfer::None("output-equivalence-no-shadow");
    };
    if !shadow.composed {
        return OutputTransfer::None("output-equivalence-shadow-desynchronized");
    }
    // `DbBack F CO` is anchored at `dbBack_init`, which is about the formula
    // the FILE spells. If the stored formula was never checked against it,
    // there is no anchor.
    if shadow.formula_unchecked.is_some() {
        return OutputTransfer::None("output-equivalence-formula-not-cross-checked");
    }
    // The only leg with an obligation. While this is zero the core database
    // is reachable from `liftDB F` by `dbBack_append` alone.
    // Every core deletion must have had its obligation discharged BY THE
    // KERNEL. The checker discharging it is not the same thing, and the
    // witness-subproof path does not discharge this obligation at all.
    if shadow.core_deletions != shadow.core_deletions_discharged {
        return OutputTransfer::None("output-equivalence-core-deletion-not-discharged");
    }

    // Invert the checker's pairing: core slot id -> output formula position.
    let mut idx: std::collections::HashMap<usize, usize> =
        std::collections::HashMap::with_capacity(pairs.len());
    for (db_id, out_pos) in pairs {
        idx.insert(*db_id, *out_pos);
    }

    // Every occupied CORE slot must be one the kernel can talk about AND one
    // the output formula carries. A core slot the pairing misses would be a
    // constraint of `CO` with no `getC O (idx i) = some c`, which is exactly
    // the hypothesis that would be unsupported.
    for id in 0..database.len() {
        let Ok(entry) = database.get_entry_usize(id) else {
            continue;
        };
        if !entry.is_core_constraint() {
            continue;
        }
        match shadow.slot(id) {
            Slot::Present(_) => {}
            // A holed core slot is one the kernel has no constraint for, so
            // `DbBack` cannot be stated over this core database at all.
            _ => return OutputTransfer::None("output-equivalence-core-slot-not-modelled"),
        }
        if !idx.contains_key(&id) {
            return OutputTransfer::None("output-equivalence-core-slot-not-in-output");
        }
    }

    // The FORWARD half needs `output_unsat_forward_of_dbOkF`, whose
    // `DbOkF F P negObj konst [] none DB` fixes the exclusion list EMPTY and
    // the bound NONE. That is not a technicality: a run that excluded a
    // solution or established a bound has deliberately dropped models of `F`,
    // and the forward transfer is exactly the claim that it did not. The two
    // shadow counters ARE those two kernel parameters -- `excls` grows only on
    // the `exclude` leg and `bound` changes only on `improve` -- so zero on
    // both is the instantiation the theorem asks for.
    if shadow.excluded_slots > 0 {
        return OutputTransfer::Backward("output-forward-equivalence-solutions-excluded");
    }
    if shadow.bound_slots > 0 {
        return OutputTransfer::Backward("output-forward-equivalence-bound-established");
    }
    OutputTransfer::Equivalence
}

/// Credit a `red`-justified core deletion, justified by
/// `VeriPbCore.dbBackSat_delete_red`.
///
/// This is the leg the POINTWISE invariant cannot have. A witness-carrying
/// `del` hands back a different assignment (`applyA w b`), so `DbBack` does
/// not survive it; `DbBackSat` does, and is all an `EQUISATISFIABLE` verdict
/// needs.
///
/// The theorem's `hgoal` is
/// `forall b, HoldsAllO b (setNone i CO) -> (Holds b c -> False) ->
///  And (HoldsAllO (applyA w b) (setNone i CO)) (Holds (applyA w b) c)`,
/// and its two conjuncts are checked here as two separate things:
///
/// * the DELETED constraint's own goal must be the kernel's image of it,
///   which is `Holds (applyA w b) c` through `holds_substC`; and
/// * every remaining CORE slot must survive the witness -- either the witness
///   provably leaves it alone, or it carries a discharged goal that is the
///   kernel's image of that slot.
///
/// The restriction to CORE slots is not a convenience: `CO` holds derived
/// constraints as `none`, so they raise no obligation, and the checker agrees
/// -- it generates these goals with `add_derived_goals = false` and
/// `only_core_subproof = true`, under `only_core = true`. A derived slot the
/// witness moves is therefore correctly ignored, where the same slot under
/// `red` would have had to be dropped and holed.
///
/// `discharged_cleanly` is the caller's skip-census check: the goals were not
/// merely accepted but kernel-discharged. Everything here is fail-closed.
#[allow(clippy::too_many_arguments)]
pub fn offer_red_deletion(
    context: &mut crate::context::Context,
    database: &Database,
    witness: &Substitution,
    deleted: &PBConstraintEnum,
    deleted_id: usize,
    goals: &[(usize, PBConstraintEnum)],
    discharged_cleanly: bool,
    core_deletions_before: usize,
) {
    if !context.config.kernel_verify {
        return;
    }
    if !discharged_cleanly {
        return;
    }
    let wit = RedWitness(witness);
    if !wit.is_expressible() {
        return;
    }
    let Some(shadow) = context.kernel_shadow.as_ref() else {
        return;
    };
    if !shadow.composed {
        return;
    }

    // Conjunct two: the deleted constraint's own goal. The slot is already
    // emptied by the time this runs, so the constraint is taken from the live
    // entry the rule cloned -- normalized here so the comparison is the
    // kernel's, not the checker's `Eq`.
    let Some(deleted_norm) = AnyConstraint::normalized_from_live(deleted) else {
        return;
    };
    if !goals
        .iter()
        .any(|(gid, goal)| *gid == deleted_id && goal_is_slot_image(&deleted_norm, &wit, goal))
    {
        return;
    }

    // Conjunct one: every remaining CORE slot survives the witness.
    for id in 0..database.len() {
        if id == deleted_id {
            continue;
        }
        let Ok(entry) = database.get_entry_usize(id) else {
            continue;
        };
        if !entry.is_core_constraint() {
            continue;
        }
        let Slot::Present(stored) = shadow.slot(id) else {
            // A holed core slot is one the kernel has no constraint for, so
            // `HoldsAllO (applyA w b) (setNone i CO)` cannot be stated.
            return;
        };
        if any_subst_is_identity(stored, &wit) {
            continue;
        }
        if !goals
            .iter()
            .any(|(gid, goal)| *gid == id && goal_is_slot_image(stored, &wit, goal))
        {
            return;
        }
    }

    shadow_note_core_deletion_discharged(context, core_deletions_before);
}

/// Record that a CORE constraint left the core set.
///
/// Called from `Database::delete_constraint`, the single funnel every
/// deletion path goes through, and only when the constraint really did leave
/// the core -- either the whole entry went, or it kept a derived id and lost
/// its core one. Deleting a purely DERIVED constraint is invisible here,
/// correctly: it is a `none` slot of the core database either way, and
/// `VeriPbCore.DbBack` says nothing about it.
///
/// Note what this does NOT record: whether the deletion was CHECKED. The
/// checker's own `strong_solution_guarantees` already tracks that and the
/// `output` rule already refuses an equivalence without it. What the bridge
/// needs is stronger -- that the obligation was discharged BY THE KERNEL --
/// and it does not have that yet, so it counts every core deletion and
/// declines the backward transfer when any occurred.
pub fn shadow_record_core_deletion(context: &mut crate::context::Context, id: usize) {
    if let Some(shadow) = context.kernel_shadow.as_mut() {
        shadow.core_deletions += 1;
        // Read BEFORE `shadow_record_deleted` empties the slot, which is why
        // this call sits ahead of it in `Database::delete_constraint`.
        shadow.pending_core_deletion_modelled = matches!(shadow.slot(id), Slot::Present(_));
    }
}

/// How many core deletions the run has seen. Snapshotted by the deletion rule
/// so a discharge can be credited to the deletion it actually belongs to.
pub fn shadow_core_deletions(context: &crate::context::Context) -> usize {
    context
        .kernel_shadow
        .as_ref()
        .map_or(0, |shadow| shadow.core_deletions)
}

/// Credit the core deletion that just happened with a kernel-discharged
/// `dbBack_delete_checked` obligation.
///
/// `before` is the count taken before the deletion, and the credit only lands
/// when EXACTLY one core deletion happened in between -- so a derived
/// deletion (which moves nothing) cannot be credited, and neither can a call
/// that deleted several. That matters in the unsafe direction: a spurious
/// credit would make `core_deletions_discharged` reach `core_deletions` while
/// some deletion went unjustified, which is precisely the state the gate
/// exists to catch.
///
/// Only the two implication-shaped paths may call this: the deleted
/// constraint is still in the core database under another id (so
/// `holdsAllO_get` gives `Holds b c` outright), or it is RUP against the
/// core-only database with the constraint already removed -- which is
/// `setNone i CO` and exactly the obligation. The WITNESS subproof path must
/// not: it establishes satisfiability preservation through a substitution,
/// which is a different claim and needs a `red`-shaped backward leg the
/// kernel does not have.
pub fn shadow_note_core_deletion_discharged(context: &mut crate::context::Context, before: usize) {
    if let Some(shadow) = context.kernel_shadow.as_mut() {
        if shadow.core_deletions == before + 1 && shadow.pending_core_deletion_modelled {
            shadow.core_deletions_discharged += 1;
        }
    }
}

/// Mirror one deletion: `VeriPbCore.DbOk.delete` (`setNone`). Deletion is
/// unconditionally sound, so the resulting hole is never a taint.
pub fn shadow_record_deleted(context: &mut crate::context::Context, id: usize) {
    let Some(shadow) = context.kernel_shadow.as_mut() else {
        return;
    };
    shadow.deletions += 1;
    match shadow.slots.get_mut(id) {
        Some(slot) => *slot = Slot::Deleted,
        None => shadow.break_composition("shadow-id-desync"),
    }
}

/// The live checker swapped the current database out for a fresh empty one
/// (an order definition or specification): stack the current slots and
/// mirror the sub-database from empty, matching `Database::new()`'s single
/// dummy entry.
pub fn shadow_save(context: &mut crate::context::Context) {
    let Some(shadow) = context.kernel_shadow.as_mut() else {
        return;
    };
    let outer = std::mem::replace(&mut shadow.slots, vec![Slot::Deleted]);
    let outer_occ = std::mem::take(&mut shadow.var_occ);
    shadow.saved.push((outer, outer_occ));
}

/// The live checker swapped a previously stacked database back in.
pub fn shadow_restore(context: &mut crate::context::Context) {
    let Some(shadow) = context.kernel_shadow.as_mut() else {
        return;
    };
    match shadow.saved.pop() {
        Some((outer, outer_occ)) => {
            shadow.slots = outer;
            shadow.var_occ = outer_occ;
        }
        None => shadow.break_composition("shadow-stack-desync"),
    }
}

/// Record the run's refutation verdict: the live checker accepted the
/// constraint at `id` as a contradiction that decides the whole proof.
///
/// Composition holds when the shadow mirrored the id space faithfully and
/// `slots[id]` is present with the `VeriPbCore.checker_sound` hypotheses —
/// `AllNonneg cc.terms` and `coeffSum cc.terms < cc.degree`. Then
/// `checker_sound` applies to the shadow database and the stored formula is
/// unsatisfiable; the live checker's own verdict is re-earned from the
/// proved kernel alone.
///
/// …and when the stored formula was established to be the file on disk. A
/// [`formula_cross_check`] stand-down normally shows up here as a hole under
/// its own reason, because it holed every formula slot; the explicit
/// `formula_unchecked` arm below is for the one case where that leaves
/// nothing to trip over — a formula with no constraints to hole — so that
/// "the cross-check stood down" and "the run composed" can never both be
/// true.
pub fn shadow_record_refutation(context: &mut crate::context::Context, id: usize) {
    let Some(shadow) = context.kernel_shadow.as_mut() else {
        return;
    };
    let obstacle = if !shadow.composed {
        Some("the shadow database could not mirror the live id space".to_string())
    } else {
        match shadow.slot(id) {
            Slot::Hole(reason) => Some(format!("no kernel-justified slot at id {id}: {reason}")),
            Slot::Deleted => Some(format!(
                "shadow slot {id} is empty (deleted or never filled)"
            )),
            Slot::Present(c) => {
                if !c.all_nonneg() {
                    Some(format!("shadow slot {id} is not AllNonneg"))
                } else if !c.coeff_sum_below_degree() {
                    Some(format!(
                        "shadow slot {id} does not satisfy the checker_sound hypotheses"
                    ))
                } else {
                    None
                }
            }
        }
    };
    let obstacle = obstacle.or_else(|| {
        shadow.formula_unchecked.map(|reason| {
            format!("the stored formula was never checked against the file on disk: {reason}")
        })
    });
    // The first refutation conclusion decides the run; later ones (a proof
    // has at most one `conclusion`) do not overwrite it.
    if shadow.refutation.is_none() {
        shadow.refutation = Some(Refutation { id, obstacle });
    }
}

/// The end-of-run composition line, or `None` when `--kernel-verify` is off.
///
/// The slot count is the *current* database's, while the taint census is
/// run-wide — it includes holes in order sub-databases that have since been
/// swapped back out — so the census can exceed the slot count. The line says
/// so rather than inviting the reader to divide one by the other.
pub fn composition_summary(context: &crate::context::Context) -> Option<String> {
    let shadow = context.kernel_shadow.as_ref()?;
    let census = shadow.taint_census();
    // Premises are counted APART from gaps. A subproof's own assumption is not
    // a failure to justify anything, and lumping the two together reported a
    // gap 25x its real size.
    let scale = format!(
        "{} slot(s) in the live id space, {} unjustified slot(s) and {} subproof \
         premise(s) recorded over the run: {census}",
        shadow.slots.len(),
        shadow.gap_count(),
        shadow.premise_count(),
    );
    Some(match &shadow.refutation {
        None => format!("kernel-compose: no refutation conclusion to compose; {scale}"),
        Some(Refutation { id, obstacle: None }) => match shadow.verdict_obstacle() {
            Some(why) => format!("kernel-compose: NOT composed ({why}); {scale}"),
            // ONE induction, `VeriPbCore.DbOkF`, but FOUR sentences -- and
            // which one a run is entitled to depends on what it did. A run
            // that logged a solution or bounded the objective is NOT entitled
            // to "unsatisfiable": its formula is typically satisfiable, and
            // the exhibited solution proves it. So the theorem named is the
            // one whose conclusion this run actually establishes.
            None => match (shadow.excluded_slots > 0, shadow.bound_slots > 0) {
                (false, false) => format!(
                    "kernel-compose: COMPOSED: the contradiction at id {id} certifies the \
                     whole run through DbOkF/full_unsat over the stored formula; {scale}"
                ),
                (true, false) => format!(
                    "kernel-compose: COMPOSED (enumeration): the contradiction at id {id} \
                     certifies through DbOkF/full_complete that the stored formula has NO \
                     models beyond the {} exhibited solution(s); {scale}",
                    shadow.excluded_slots
                ),
                (false, true) => format!(
                    "kernel-compose: COMPOSED (bounds): the contradiction at id {id} \
                     certifies through DbOkF/full_complete that no assignment satisfying \
                     the stored formula has objective value below the {} established \
                     bound(s); {scale}",
                    shadow.bound_slots
                ),
                (true, true) => format!(
                    "kernel-compose: COMPOSED (enumeration+bounds): the contradiction at id \
                     {id} certifies through DbOkF/full_complete that every model of the \
                     stored formula is one of the {} exhibited solution(s) or no better \
                     than the {} established bound(s); {scale}",
                    shadow.excluded_slots, shadow.bound_slots
                ),
            },
        },
        Some(Refutation {
            obstacle: Some(why),
            ..
        }) => {
            format!("kernel-compose: NOT composed ({why}); {scale}")
        }
    })
}

/// Record a step outcome: its per-step statistic and its shadow slot.
fn record_step(
    context: &mut crate::context::Context,
    outcome: StepOutcome,
    bump: fn(&mut KernelStats),
) {
    match outcome.check {
        None => bump(&mut context.kernel_stats),
        Some(reason) => context.kernel_stats.skip(reason),
    }
    shadow_offer(context, outcome.slot);
}

fn kernel_lit(l: &Lit) -> Option<kernel::Lit> {
    let var: u32 = l.get_var().try_into().ok()?;
    Some(if l.is_negated() {
        kernel::Lit::neg(var)
    } else {
        kernel::Lit::pos(var)
    })
}

// ---------------------------------------------------------------------------
// The two coefficient tiers
// ---------------------------------------------------------------------------

/// One coefficient tier the bridge replays a step at.
///
/// The proved kernel is generic over [`kernel::CoeffDomain`] — the same rule
/// bodies, the same `normC`, the same RUP replay, instantiated at a storage
/// type and its exact arithmetic. This trait adds the two things a *bridge*
/// needs on top of that: how a live coefficient crosses into the tier, and
/// how a derived constraint is filed in the shadow database.
///
/// There are exactly two instantiations, and the split is the whole point of
/// this module's tiering:
///
/// * [`kernel::Coeff`] (`i64`) — the **fast** tier. The corpus is
///   `i64`-dominated, so this is what essentially every step is replayed at,
///   and it is where the proved width guards (`VeriPbCore.fitsI64`) have
///   content: a value that leaves the machine word makes the rule refuse.
/// * [`Big`] (`BigInt`) — the **complete** tier. It holds everything the live
///   checker can hold (the live constraint representations top out at
///   `BigInt` themselves), so it never refuses on width, and it mirrors the
///   Clean `Int` statements with no side condition left over.
///
/// The live checker *promotes* its own arithmetic from `i64` to `i128` to
/// `BigInt` as values grow. Replaying only at the narrow tier meant the
/// kernel stood down precisely where the live checker had just promoted —
/// which is where two of the three wrong verdicts an adversarial review found
/// were living, and why eight of their ten regression instances used to pass
/// under the flag. Every entry point therefore replays narrow first and, when
/// (and only when) the narrow tier stood down *on width*, replays again here
/// (see [`width_limited`] and [`tiered_step`]).
pub trait Tier: kernel::CoeffDomain {
    /// `true` for the narrow tier, whose width refusals are worth retrying
    /// one tier up. Reasons that mention `i64` are only ever produced there.
    const NARROW: bool;

    /// Convert a live `i64` coefficient. Total at both tiers.
    fn from_i64(x: i64) -> Self;

    /// Convert a live `i128` coefficient (the checker's middle tier).
    fn from_i128(x: i128) -> Option<Self>;

    /// Convert a live `BigInt` coefficient.
    fn from_bigint(b: &BigInt) -> Option<Self>;

    /// This tier's value as an exact `BigInt`. Total at both tiers — widening
    /// never loses anything — which is what lets a value computed at the
    /// narrow tier and one computed at the complete tier be compared in one
    /// place (see [`CanonicalConstraint`]).
    fn to_bigint(x: &Self) -> BigInt;

    /// File a derived constraint in the shadow database, at the narrowest
    /// tier that can hold it.
    fn into_any(c: kernel::Constraint<Self>) -> AnyConstraint;
}

impl Tier for kernel::Coeff {
    const NARROW: bool = true;

    #[inline]
    fn from_i64(x: i64) -> Self {
        x
    }
    #[inline]
    fn from_i128(x: i128) -> Option<Self> {
        x.try_into().ok()
    }
    #[inline]
    fn from_bigint(b: &BigInt) -> Option<Self> {
        b.try_into().ok()
    }
    #[inline]
    fn to_bigint(x: &Self) -> BigInt {
        BigInt::from(*x)
    }
    #[inline]
    fn into_any(c: kernel::Constraint<Self>) -> AnyConstraint {
        AnyConstraint::Narrow(c)
    }
}

impl Tier for Big {
    const NARROW: bool = false;

    #[inline]
    fn from_i64(x: i64) -> Self {
        Big::from(x)
    }
    #[inline]
    fn from_i128(x: i128) -> Option<Self> {
        Some(Big::from(x))
    }
    #[inline]
    fn from_bigint(b: &BigInt) -> Option<Self> {
        Some(b.clone())
    }
    #[inline]
    fn to_bigint(x: &Self) -> BigInt {
        x.clone()
    }
    /// A wide-tier derivation whose result happens to fit a machine word is
    /// filed *narrow*, so later steps that read this slot stay on the fast
    /// path. Widening is exact, so nothing is lost either way; this only
    /// keeps one wide constraint from making every downstream step wide.
    fn into_any(c: kernel::Constraint<Self>) -> AnyConstraint {
        let mut terms = Vec::with_capacity(c.terms.len());
        for t in &c.terms {
            match kernel::Coeff::from_bigint(&t.coeff) {
                Some(coeff) => terms.push(kernel::Term { coeff, lit: t.lit }),
                None => return AnyConstraint::Wide(c),
            }
        }
        match kernel::Coeff::from_bigint(&c.degree) {
            Some(degree) => AnyConstraint::Narrow(kernel::Constraint::new(terms, degree)),
            None => AnyConstraint::Wide(c),
        }
    }
}

/// A kernel constraint held at whichever [`Tier`] can express it.
///
/// The shadow database spans both tiers in one id space: nearly every slot is
/// [`Narrow`](AnyConstraint::Narrow), and a slot goes
/// [`Wide`](AnyConstraint::Wide) only when the constraint the live checker
/// stored genuinely does not fit a machine word. [`at`](AnyConstraint::at)
/// re-expresses a slot at the tier a replay is running at: widening is exact
/// and always succeeds, narrowing is the kernel's own guard and may not.
#[derive(Debug, Clone)]
pub enum AnyConstraint {
    /// Fits `i64`.
    Narrow(kernel::Constraint<kernel::Coeff>),
    /// Does not fit `i64`; held exactly.
    Wide(kernel::Constraint<Big>),
}

impl AnyConstraint {
    /// Every variable this constraint mentions, with repeats.
    ///
    /// Used to build [`KernelShadowDb::var_occ`], so it must not miss one: a
    /// variable left out here becomes a missing index entry, which is the one
    /// direction of that index that would be unsound.
    fn vars(&self) -> Vec<u32> {
        match self {
            AnyConstraint::Narrow(c) => c.terms.iter().map(|t| t.lit.var).collect(),
            AnyConstraint::Wide(c) => c.terms.iter().map(|t| t.lit.var).collect(),
        }
    }

    /// This constraint at tier `C`, or `None` when `C` cannot hold it.
    fn at<C: Tier>(&self) -> Option<kernel::Constraint<C>> {
        match self {
            AnyConstraint::Narrow(c) => Some(kernel::Constraint::new(
                c.terms
                    .iter()
                    .map(|t| kernel::Term {
                        coeff: C::from_i64(t.coeff),
                        lit: t.lit,
                    })
                    .collect(),
                C::from_i64(c.degree),
            )),
            AnyConstraint::Wide(c) => {
                let mut terms = Vec::with_capacity(c.terms.len());
                for t in &c.terms {
                    terms.push(kernel::Term {
                        coeff: C::from_bigint(&t.coeff)?,
                        lit: t.lit,
                    });
                }
                Some(kernel::Constraint::new(terms, C::from_bigint(&c.degree)?))
            }
        }
    }

    /// The proved normal form of a live constraint, at the narrowest tier
    /// that can hold it. `None` only when the *variable indices* are outside
    /// the kernel's domain — no coefficient can fail here, `Big` holding
    /// everything a live constraint can.
    fn normalized_from_live(live: &PBConstraintEnum) -> Option<AnyConstraint> {
        if let Some(k) = to_kernel::<kernel::Coeff>(live) {
            if let Ok(n) = normalize(&k) {
                return Some(AnyConstraint::Narrow(n));
            }
        }
        let k = to_kernel::<Big>(live)?;
        normalize(&k).ok().map(Big::into_any)
    }

    /// `VeriPbCore.AllNonneg`, at whichever tier the slot is held.
    fn all_nonneg(&self) -> bool {
        match self {
            AnyConstraint::Narrow(c) => c.all_nonneg(),
            AnyConstraint::Wide(c) => c.all_nonneg(),
        }
    }

    /// `coeffSum c.terms < c.degree` — the second `checker_sound` hypothesis.
    fn coeff_sum_below_degree(&self) -> bool {
        match self {
            // Trait-qualified: a bare `.widen()` on an integer collides with
            // the unstable inherent `widen` in compiler_consumer 1.99-dev's std
            // (`unstable_name_collisions`).
            AnyConstraint::Narrow(c) => c.coeff_sum() < CoeffDomain::widen(&c.degree),
            AnyConstraint::Wide(c) => c.coeff_sum() < CoeffDomain::widen(&c.degree),
        }
    }
}

/// Convert a live constraint into the kernel representation at tier `C`, if
/// its coefficients, degree and variable indices fit.
///
/// At [`Big`] the only way this fails is a variable index above `u32`: every
/// live coefficient representation (`i64`, `i128`, `BigInt`) converts.
pub fn to_kernel<C: Tier>(c: &PBConstraintEnum) -> Option<kernel::Constraint<C>> {
    let mut terms = Vec::with_capacity(c.len());
    for idx in 0..c.len() {
        let term = c.get_term(idx)?;
        let coeff = C::from_bigint(term.get_coeff())?;
        let lit = kernel_lit(&term.lit)?;
        terms.push(kernel::Term { coeff, lit });
    }
    let degree = match c {
        PBConstraintEnum::Clause(_) => C::one(),
        PBConstraintEnum::Cardinality(card) => C::from_i64(*card.get_degree()),
        PBConstraintEnum::GeneralPBI64(g) => C::from_i64(*g.get_degree()),
        PBConstraintEnum::GeneralPBI128(g) => C::from_i128(*g.get_degree())?,
        PBConstraintEnum::GeneralPBBigInt(g) => C::from_bigint(g.get_degree())?,
    };
    Some(kernel::Constraint::new(terms, degree))
}

// ---------------------------------------------------------------------------
// Tier dispatch
// ---------------------------------------------------------------------------

/// Skip reasons that name a *width the narrow tier could not hold*, and which
/// the complete tier can therefore resolve.
///
/// Everything else is the same answer at every tier and is never retried: an
/// unmodelled meta-rule, a certificate the kernel rejects for a reason that
/// is not about width, a reconstruction the proved chain does not cover, a
/// variable index above `u32`.
///
/// `kernel-guard-refused` is in the list even though it can also be a
/// genuine, tier-independent hypothesis failure (a non-positive divisor, a
/// quotient that is not the ceiling). Retrying costs one extra replay of a
/// step that was going to be a skip anyway, and the alternative — splitting
/// the reason by [`kernel::GuardError`] variant at every call site — would
/// churn a vocabulary that the development design notes §7.3 and the blessed
/// coverage snapshot both pin.
fn width_limited(reason: &'static str) -> bool {
    matches!(
        reason,
        "constraint-not-i64-representable"
            | "formula-not-i64-representable"
            | "result-not-i64-representable"
            | "factor-not-i64"
            | "divisor-not-i64"
            | "amount-not-i64"
            | "objective-not-i64-representable"
            | "kernel-guard-refused"
            | "kernel-guard-refused-with-narrow-result"
    )
}

/// Run a constraint-deriving bridge check at the narrow tier, and — only when
/// it stood down for a width reason — again at the complete tier.
///
/// A *divergence* from the narrow pass is returned immediately and is never
/// re-litigated: the narrow tier only reports one after computing every value
/// exactly (in `i128`) and passing every guard, so its disagreement with the
/// live checker is real. What the second pass is for is the opposite case —
/// the narrow tier could not compute at all, so it had nothing to disagree
/// with.
fn tiered_step(
    narrow: impl FnOnce() -> Result<StepOutcome, CheckingError>,
    wide: impl FnOnce() -> Result<StepOutcome, CheckingError>,
) -> Result<StepOutcome, CheckingError> {
    let first = narrow()?;
    match first.check {
        Some(reason) if width_limited(reason) => wide(),
        _ => Ok(first),
    }
}

/// [`tiered_step`] for the checks that decide an obligation without deriving
/// anything.
fn tiered_outcome(
    narrow: impl FnOnce() -> BridgeOutcome,
    wide: impl FnOnce() -> BridgeOutcome,
) -> BridgeOutcome {
    match narrow()? {
        Some(reason) if width_limited(reason) => wide(),
        other => Ok(other),
    }
}

/// Canonical form for comparison: kernel-normalized, terms sorted by
/// (variable, polarity). Normalization is proved sound; sorting is only a
/// comparison aid.
fn canonical<C: kernel::CoeffDomain>(c: &kernel::Constraint<C>) -> Option<kernel::Constraint<C>> {
    let mut n = normalize(c).ok()?;
    n.terms.sort_by_key(|t| (t.lit.var, t.lit.negated));
    Some(n)
}

/// [`canonical`] for a constraint the bridge already maintains as a proved
/// normal form (a `normC` fixpoint: every `Ok` shadow — `shadow_norm` runs
/// after each arithmetic op, and the axiom/saturate/multiply-by-zero/
/// degree-weaken outputs are fixpoints by construction): clone + sort only.
///
/// On a fixpoint, `normalize` merges nothing, cancels nothing and drops
/// nothing — all coefficients are positive and the variables distinct — so
/// it can only reverse the term order (`normIns` folds from the right),
/// which the sort erases, and it cannot fail (every value it re-narrows is
/// already an `i64`). Hence `canonical(c) == Some(sort_canon(c))` for every
/// fixpoint, and skipping the re-normalization removes recomputation only.
/// The debug assertion keeps the invariant honest, order-insensitively.
fn sort_canon<C: kernel::CoeffDomain>(c: &kernel::Constraint<C>) -> kernel::Constraint<C> {
    debug_assert!(
        {
            let mut vars: Vec<u32> = c.terms.iter().map(|t| t.lit.var).collect();
            vars.sort_unstable();
            let zero = C::zero();
            c.terms.iter().all(|t| t.coeff > zero) && vars.windows(2).all(|w| w[0] != w[1])
        },
        "sort_canon caller handed a constraint that is not a normC fixpoint"
    );
    let mut n = c.clone();
    n.terms.sort_by_key(|t| (t.lit.var, t.lit.negated));
    n
}

/// Does a shadow slot describe the same constraint as the live database
/// entry it mirrors, up to term order?
///
/// `None` means the live constraint is outside the kernel's domain (not
/// `i64`-representable, or normalization refused) so the question cannot be
/// answered — never that the answer is "no".
///
/// Both sides are `normC` images (every slot is stored as one), but `normC`
/// folds from the right and so pins the output order to the *input's*
/// order, which the two sides need not share; hence the sorted fallback
/// after the cheap direct comparison. This predicate is a **divergence
/// detector**, not a link in any entailment chain: wherever the kernel needs
/// a database constraint, the bridge replays the slot's own constraint, so
/// the Clean side never sees the live term order at all.
fn slot_matches_live(slot: &AnyConstraint, live: &PBConstraintEnum) -> Option<bool> {
    fn at<C: Tier>(slot: &kernel::Constraint<C>, live: &PBConstraintEnum) -> Option<bool> {
        let k = to_kernel::<C>(live)?;
        let n = normalize(&k).ok()?;
        if *slot == n {
            return Some(true);
        }
        Some(sort_canon(slot) == sort_canon(&n))
    }
    // Compared at the slot's own tier first, which for the overwhelming
    // majority of slots is `i64`. When that cannot answer — the live entry
    // has values `i64` cannot read, or `normC` refused there — the slot is
    // widened and the question is asked again at `Big`, which reads every
    // constraint the live checker can hold. That turns "unknown, so taint"
    // into a real yes or no: a slot that disagrees with its own live entry is
    // precisely the drift this predicate exists to detect, and it should not
    // escape as a stand-down just because the two sides were being read at
    // different widths.
    match slot {
        AnyConstraint::Narrow(c) => match at(c, live) {
            Some(answer) => Some(answer),
            None => at(&slot.at::<Big>()?, live),
        },
        AnyConstraint::Wide(c) => at(c, live),
    }
}

/// The shadow of one `pol` stack slot. `Err(reason)` poisons the slot: some
/// step feeding it was outside the proved fragment.
type Shadow<C> = Result<kernel::Constraint<C>, &'static str>;

fn shadow_norm<C: Tier>(c: kernel::Constraint<C>) -> Shadow<C> {
    normalize(&c).map_err(|_| "kernel-guard-refused")
}

/// Replay a `pol` instruction sequence on a shadow stack of kernel
/// constraints and compare the outcome with the live result.
///
/// The control flow mirrors [`execute_pol_instructions`] *exactly* —
/// including the literal-axiom stash and the weakening stash, whose
/// deferred processing changes which stack shapes are accepted (the legacy
/// v2 parser emits `pol x1 + x2`-style programs whose `Add` fires with only
/// the literal axiom on the stack). The one deliberate difference: the
/// shadow stash holds *whole constraints*, degrees included, where the live
/// stash keeps only the term. If the live stash ever discards information
/// that matters, the final comparison diverges instead of following suit.
///
/// Must run *after* [`execute_pol_instructions`] on the same instruction
/// slice: constraint ids have been normalized to absolute ids by then, and
/// the live result is known.
///
/// # Leaves and composition
///
/// A `ConstraintId` leaf is replayed as **the shadow slot's own
/// constraint**, so the whole replay is a `DStep` chain whose `DStep.ax`
/// steps read the shadow database — which is what makes the result
/// composable (`VeriPbCore.dstep_entails`). The live entry at that id is
/// converted and compared against the slot up to term order: a mismatch
/// means the live database drifted from what the kernel derived for that
/// very id, which is a [`CheckingError::KernelDivergence`], not a skip.
/// When the slot is *not* present (a hole from an unmodelled meta-rule, or
/// no shadow at all), the leaf falls back to the live entry so the per-step
/// statistic is unaffected, and the program's slot contribution is tainted
/// with the hole's reason.
///
/// [`execute_pol_instructions`]: crate::rules::cutting_planes::execute_pol_instructions
pub fn verify_pol(
    instructions: &[Instruction],
    database: &Database,
    shadow: Option<&KernelShadowDb>,
    live_result: &PBConstraintEnum,
) -> Result<StepOutcome, CheckingError> {
    tiered_step(
        || verify_pol_at::<kernel::Coeff>(instructions, database, shadow, live_result),
        || verify_pol_at::<Big>(instructions, database, shadow, live_result),
    )
}

/// [`verify_pol`] at one coefficient tier. See [`Tier`] for why there are two
/// and [`tiered_step`] for when the second one runs.
fn verify_pol_at<C: Tier>(
    instructions: &[Instruction],
    database: &Database,
    shadow: Option<&KernelShadowDb>,
    live_result: &PBConstraintEnum,
) -> Result<StepOutcome, CheckingError> {
    fn shadow_add<C: Tier>(a: Shadow<C>, b: Shadow<C>) -> Shadow<C> {
        match (a, b) {
            (Ok(a), Ok(b)) => match kernel::add(&a, &b) {
                Ok(sum) => shadow_norm(sum),
                Err(_) => Err("kernel-guard-refused"),
            },
            (Err(r), _) | (_, Err(r)) => Err(r),
        }
    }

    /// A whole batch of variables weakened away in ONE trivial axiom:
    /// `C + sum_i coeff_i * ~l_i >= 0`.
    ///
    /// This derives exactly what the per-variable chain
    /// (`C + coeff_1 * ~l_1`, normalize, `+ coeff_2 * ~l_2`, normalize, …)
    /// derives, and it is the same `DStep.trivS` shape: `C` is a `normC`
    /// fixpoint (every `Ok` stack entry is), so the doomed literals sit on
    /// *distinct* variables with positive coefficients — the axiom is
    /// `AllNonneg` with degree 0 — and under `normC` each `l_i`/`~l_i` pair
    /// cancels independently of the others, dropping that variable's term and
    /// shifting the degree by exactly `-coeff_i`. Summing those shifts in one
    /// step reaches the same degree the chain reaches one subtraction at a
    /// time, and because the coefficients are positive the partial sums are
    /// monotone: the batched narrowing fails exactly when some prefix of the
    /// chain's narrowing would have failed. (This is the argument step 1 of
    /// [`verify_implication_kernel`] already carries, applied here.)
    ///
    /// Filtering the constraint's terms by a set of doomed variables — rather
    /// than looking each variable up in the constraint — visits every term
    /// once and dedupes the stash for free: a variable weakened twice is a
    /// no-op the second time in the chain (its term is already gone), and
    /// contributes one axiom term here.
    fn shadow_weaken_vars<C: Tier>(c: Shadow<C>, vars: &[usize]) -> Shadow<C> {
        let c = c?;
        let mut doomed_vars: AHashSet<u32> = AHashSet::with_capacity(vars.len());
        for v in vars {
            match u32::try_from(*v) {
                Ok(v) => {
                    doomed_vars.insert(v);
                }
                // Preserved verbatim from the per-variable chain: a variable
                // index the kernel cannot represent poisons the slot even
                // when no term carries it.
                Err(_) => return Err("variable-index-too-wide"),
            }
        }
        debug_assert!(
            {
                let mut seen: Vec<u32> = c.terms.iter().map(|t| t.lit.var).collect();
                seen.sort_unstable();
                seen.windows(2).all(|w| w[0] != w[1])
            },
            "shadow_weaken_vars expects a normC fixpoint (one term per variable)"
        );
        let doomed: Vec<kernel::Term<C>> = c
            .terms
            .iter()
            .filter(|t| doomed_vars.contains(&t.lit.var))
            .map(|t| kernel::Term {
                coeff: t.coeff.clone(),
                lit: t.lit.negate(),
            })
            .collect();
        if doomed.is_empty() {
            return Ok(c);
        }
        match kernel::add(&c, &kernel::Constraint::new(doomed, C::zero())) {
            Ok(sum) => shadow_norm(sum),
            Err(_) => Err("kernel-guard-refused"),
        }
    }

    /// Variable-form division, reconstructed from proved pieces:
    /// flip negated-literal terms into variable space (each flip checked to
    /// preserve the proved normal form, licensed by
    /// `VeriPbCore.entails_of_normC_eq`), ceiling-divide there
    /// (`entails_divide`; the kernel's ceiling on negatives is truncation,
    /// exactly the live rule), and flip back (checked again).
    fn shadow_variable_form_div<C: Tier>(c: Shadow<C>, divisor: Option<C>) -> Shadow<C> {
        let c = c?;
        let Some(k) = divisor else {
            return Err("divisor-not-i64");
        };
        if k <= C::zero() {
            return Err("kernel-guard-refused");
        }
        let flip = |input: &kernel::Constraint<C>,
                    should_flip: &dyn Fn(&kernel::Term<C>) -> bool|
         -> Result<kernel::Constraint<C>, &'static str> {
            let mut terms = Vec::with_capacity(input.terms.len());
            let mut degree = input.degree.widen();
            for t in &input.terms {
                if should_flip(t) {
                    let w = t.coeff.widen();
                    degree = degree.sub(&w);
                    let coeff = C::narrow(&w.neg()).ok_or("kernel-guard-refused")?;
                    terms.push(kernel::Term {
                        coeff,
                        lit: t.lit.negate(),
                    });
                } else {
                    terms.push(t.clone());
                }
            }
            let degree = C::narrow(&degree).ok_or("kernel-guard-refused")?;
            Ok(kernel::Constraint::new(terms, degree))
        };
        // Into variable space: every negated literal flips. `c` is an `Ok`
        // shadow and hence a `normC` fixpoint, so its side of the flip check
        // needs only sorting (`sort_canon`); the flipped form is genuinely
        // re-normalized, which is the flip soundness check itself.
        let c_var = flip(&c, &|t| t.lit.negated)?;
        if canonical(&c_var) != Some(sort_canon(&c)) {
            return Err("varform-flip-check-failed");
        }
        // Proved ceiling division (truncation on the negative coefficients).
        let d_var = kernel::divide(k, &c_var).map_err(|_| "kernel-guard-refused")?;
        // Back to normalized literal space: negative coefficients flip.
        let zero = C::zero();
        let d = flip(&d_var, &|t| t.coeff < zero)?;
        // `d` is NOT a fixpoint (divide can send a flipped-negative
        // coefficient to zero — ceil(-1/2) = 0 — and `flip(coeff < 0)`
        // leaves that zero-coefficient term in place), so it is normalized
        // in full — but exactly once: the same result serves the second
        // flip check and becomes the returned shadow, where previously
        // `canon_eq` and `shadow_norm` each normalized `d` separately.
        // A refusal here is a width guard, not a disagreement about the
        // flip, and is named as one so that the tier dispatch can retry it.
        let Ok(nd) = normalize(&d) else {
            return Err("kernel-guard-refused");
        };
        if canonical(&d_var) != Some(sort_canon(&nd)) {
            return Err("varform-flip-check-failed");
        }
        Ok(nd)
    }

    /// Apply one of the proved MIR rules ([`kernel::mir`] for the normalized
    /// form, [`kernel::mir_variable`] for the variable form) to a shadow.
    ///
    /// The rule lives in the proved crate next to DIVIDE and SATURATE, under
    /// the same `missing_docs`/control-mirror discipline
    /// (`veripb-core-proved/src/mir.rs`, pinned against the Clean controls by
    /// `mir_matches_the_clean_controls`); the only thing decided here is the
    /// bridge-level bookkeeping. A zero remainder is not a refusal: the Clean
    /// rule has no content when `k` divides the degree, and the live rule
    /// produces the trivial constraint, which `entails_trivial` licenses
    /// outright — the same treatment `Multiply(0)` and a nonpositive-degree
    /// `Saturate` already get.
    fn shadow_mir<C: Tier>(
        c: Shadow<C>,
        divisor: Option<C>,
        rule: fn(C, &kernel::Constraint<C>) -> Result<kernel::Constraint<C>, kernel::GuardError>,
    ) -> Shadow<C> {
        let c = c?;
        let Some(d) = divisor else {
            return Err("divisor-not-i64");
        };
        match rule(d, &c) {
            Ok(cut) => shadow_norm(cut),
            Err(kernel::GuardError::MirZeroRemainder) => {
                Ok(kernel::Constraint::new(Vec::new(), C::zero()))
            }
            Err(_) => Err("kernel-guard-refused"),
        }
    }

    /// Fold the stashed literal axioms into the constraint below them, as the
    /// live machine does: ONE add of the whole stash instead of one add and
    /// one re-normalization per axiom.
    ///
    /// The two compute the same constraint. `kernel::add` is `addC` — term
    /// concatenation plus a degree sum — and for a merged multiset of terms
    /// the proved `normC` is a function of, per variable, the total positive
    /// coefficient `p_v`, the total negative-literal coefficient `m_v` and the
    /// degree: it keeps `|p_v - m_v|` on the surviving polarity and shifts the
    /// degree by `-min(p_v, m_v)`. Normalizing early therefore replaces
    /// `(p_v, m_v)` by `(max(N_v,0), max(-N_v,0))` with `N_v = p_v - m_v`, and
    /// `min(P, M) + min(max(N,0) + p, max(-N,0) + m) = min(P + p, M + m)`
    /// holds in both sign cases — so the chain's accumulated degree shifts
    /// telescope to the batched one, and the surviving terms are the same
    /// multiset. Term *order* may differ, which nothing downstream can see:
    /// every kernel operation here is either termwise or a concatenation, and
    /// the comparison against the live result is [`sort_canon`].
    ///
    /// The guards move rather than disappear: intermediate coefficient sums
    /// are formed in the normalizer's `i128`, so batching can only *widen* the
    /// set of programs that survive narrowing (a pair of axioms that cancels
    /// no longer has to pass through an unrepresentable partial sum). The
    /// degree cannot regress either, every stash element carrying degree 0 —
    /// they are literal axioms, possibly multiplied — and the sum is narrowed
    /// before the add so an engineered non-zero stash degree still fails
    /// closed. Error precedence is the fold's, verbatim: a poisoned base wins
    /// over the stash, and within the stash the first reason wins.
    fn flush_literal_stash<C: Tier>(
        stack: &mut Vec<Shadow<C>>,
        stash: &mut Vec<Shadow<C>>,
        pop_temp_axiom: bool,
    ) -> Result<(), CheckingError> {
        let last = if pop_temp_axiom { stack.pop() } else { None };
        let first = stack
            .pop()
            .ok_or(CheckingError::NotEnoughConstraintsOnStack)?;
        let acc = match first {
            Err(reason) => {
                stash.clear();
                Err(reason)
            }
            Ok(base) => {
                let mut terms: Vec<kernel::Term<C>> = Vec::new();
                let mut degree = <C::Exact as Exact>::zero();
                let mut poison: Option<&'static str> = None;
                for ax in stash.drain(..) {
                    match ax {
                        Ok(a) => {
                            terms.extend_from_slice(&a.terms);
                            degree = degree.add(&a.degree.widen());
                        }
                        Err(reason) => poison = poison.or(Some(reason)),
                    }
                }
                match (poison, C::narrow(&degree)) {
                    (Some(reason), _) => Err(reason),
                    (None, None) => Err("kernel-guard-refused"),
                    (None, Some(degree)) => {
                        shadow_add(Ok(base), Ok(kernel::Constraint::new(terms, degree)))
                    }
                }
            }
        };
        stack.push(acc);
        if let Some(last) = last {
            stack.push(last);
        }
        Ok(())
    }

    fn flush_weakening_stash<C: Tier>(
        stack: &mut Vec<Shadow<C>>,
        stash: &mut Vec<usize>,
    ) -> Result<(), CheckingError> {
        let top = stack
            .pop()
            .ok_or(CheckingError::NotEnoughConstraintsOnStack)?;
        let weakened = shadow_weaken_vars(top, stash);
        stash.clear();
        stack.push(weakened);
        Ok(())
    }

    let mut stack: Vec<Shadow<C>> = Vec::new();
    let mut top_is_literal_axiom = false;
    let mut literal_axiom_stash: Vec<Shadow<C>> = Vec::new();
    let mut weakening_stash: Vec<usize> = Vec::new();

    // The first reason this program cannot ground out in the shadow
    // database. Set conservatively: any leaf that did not come from a
    // present slot taints the whole program, even if a later `* 0` happens
    // to discard it. Over-tainting only ever loses composition coverage; it
    // can never manufacture it.
    let mut program_taint: Option<&'static str> = None;

    // Per-call memo of the resolved shadow of each database id this pol
    // program loads. The cached value is a pure function of the id (the slot
    // and the live entry both stay fixed for the whole call, and `to_kernel`
    // + `shadow_norm` are deterministic), so a hit hands back exactly what
    // the miss path would recompute. Divergence exits before any insert, so
    // the cache never memoizes a leaf whose check failed.
    let mut load_cache: AHashMap<usize, Shadow<C>> = AHashMap::new();

    for instruction in instructions {
        if !literal_axiom_stash.is_empty() {
            let need_to_process_stash = if top_is_literal_axiom {
                !matches!(instruction, Instruction::Multiply(_) | Instruction::Add)
            } else {
                !matches!(instruction, Instruction::LiteralAxiom(_))
            };
            if need_to_process_stash {
                flush_literal_stash(&mut stack, &mut literal_axiom_stash, top_is_literal_axiom)?;
            }
        }
        if !weakening_stash.is_empty() && !matches!(instruction, Instruction::Weaken(_)) {
            flush_weakening_stash(&mut stack, &mut weakening_stash)?;
        }

        match instruction {
            Instruction::ConstraintId(index) => {
                let id = *index as usize;
                let entry = match load_cache.get(&id) {
                    Some(hit) => hit.clone(),
                    None => {
                        let resolved = resolve_pol_leaf(id, database, shadow, &mut program_taint)?;
                        load_cache.insert(id, resolved.clone());
                        resolved
                    }
                };
                stack.push(entry);
                top_is_literal_axiom = false;
            }
            Instruction::LiteralAxiom(lit) => {
                let shadow = match kernel_lit(lit) {
                    Some(l) => Ok(kernel::Constraint::new(
                        vec![kernel::Term {
                            coeff: C::one(),
                            lit: l,
                        }],
                        C::zero(),
                    )),
                    None => Err("variable-index-too-wide"),
                };
                stack.push(shadow);
                top_is_literal_axiom = true;
            }
            Instruction::Saturate => {
                let top = stack
                    .pop()
                    .ok_or(CheckingError::NotEnoughConstraintsOnStack)?;
                stack.push(match top {
                    Ok(c) => {
                        if c.degree <= C::zero() {
                            // Live saturation clears a trivial constraint.
                            Ok(kernel::Constraint::new(Vec::new(), c.degree.clone()))
                        } else {
                            match kernel::saturate(&c) {
                                Ok(sat) => Ok(sat),
                                Err(_) => Err("kernel-guard-refused"),
                            }
                        }
                    }
                    Err(r) => Err(r),
                });
                top_is_literal_axiom = false;
            }
            Instruction::Weaken(var_idx) => {
                weakening_stash.push(*var_idx);
                top_is_literal_axiom = false;
            }
            Instruction::NormalizedFormDivide(divisor) => {
                let top = stack
                    .pop()
                    .ok_or(CheckingError::NotEnoughConstraintsOnStack)?;
                stack.push(match top {
                    Ok(c) => match C::from_bigint(divisor) {
                        Some(k) => match kernel::divide(k, &c) {
                            Ok(d) => shadow_norm(d),
                            Err(_) => Err("kernel-guard-refused"),
                        },
                        None => Err("divisor-not-i64"),
                    },
                    Err(r) => Err(r),
                });
                top_is_literal_axiom = false;
            }
            Instruction::VariableFormDivide(divisor) => {
                let top = stack
                    .pop()
                    .ok_or(CheckingError::NotEnoughConstraintsOnStack)?;
                stack.push(shadow_variable_form_div(top, C::from_bigint(divisor)));
                top_is_literal_axiom = false;
            }
            Instruction::NormalizedFormMIR(divisor) => {
                let top = stack
                    .pop()
                    .ok_or(CheckingError::NotEnoughConstraintsOnStack)?;
                stack.push(shadow_mir(
                    top,
                    C::from_bigint(divisor),
                    kernel::mir::mir::<C>,
                ));
                top_is_literal_axiom = false;
            }
            Instruction::VariableFormMIR(divisor) => {
                let top = stack
                    .pop()
                    .ok_or(CheckingError::NotEnoughConstraintsOnStack)?;
                stack.push(shadow_mir(
                    top,
                    C::from_bigint(divisor),
                    kernel::mir::mir_variable::<C>,
                ));
                top_is_literal_axiom = false;
            }
            Instruction::Multiply(factor) => {
                // NOTE: the live machine leaves `top_is_literal_axiom` alone
                // here, so a multiplied literal axiom still counts as one.
                let top = stack
                    .pop()
                    .ok_or(CheckingError::NotEnoughConstraintsOnStack)?;
                stack.push(match top {
                    Ok(c) => match C::from_bigint(factor) {
                        // Multiplying by zero yields 0 >= 0, entailed by
                        // everything (`entails_multiply` needs only 0 <= k;
                        // equivalently `entails_trivial`).
                        Some(k) if k == C::zero() => {
                            Ok(kernel::Constraint::new(Vec::new(), C::zero()))
                        }
                        Some(k) => match kernel::multiply(k, &c) {
                            Ok(m) => shadow_norm(m),
                            Err(_) => Err("kernel-guard-refused"),
                        },
                        None => Err("factor-not-i64"),
                    },
                    Err(r) => Err(r),
                });
            }
            Instruction::Add => {
                let second = stack
                    .pop()
                    .ok_or(CheckingError::NotEnoughConstraintsOnStack)?;
                if !top_is_literal_axiom {
                    let first = stack
                        .pop()
                        .ok_or(CheckingError::NotEnoughConstraintsOnStack)?;
                    stack.push(shadow_add(first, second));
                } else {
                    // The live stash keeps only the axiom's term; keeping the
                    // whole constraint means a dropped degree would show up
                    // as a final divergence rather than being replicated.
                    literal_axiom_stash.push(second);
                    top_is_literal_axiom = false;
                }
            }
            Instruction::LowerRHS(amount) => {
                let top = stack
                    .pop()
                    .ok_or(CheckingError::NotEnoughConstraintsOnStack)?;
                stack.push(match top {
                    Ok(c) => match C::from_bigint(amount) {
                        Some(w) => match kernel::weaken_degree(&c, w) {
                            Ok(l) => Ok(l),
                            Err(_) => Err("kernel-guard-refused"),
                        },
                        None => Err("amount-not-i64"),
                    },
                    Err(r) => Err(r),
                });
                // Mirrors the live machine: a lowered axiom is an ordinary
                // constraint from here on.
                top_is_literal_axiom = false;
            }
        }
    }

    if !literal_axiom_stash.is_empty() {
        // The final live flush merges into the current top even when that
        // top is itself a literal axiom.
        flush_literal_stash(&mut stack, &mut literal_axiom_stash, false)?;
    }
    if !weakening_stash.is_empty() {
        flush_weakening_stash(&mut stack, &mut weakening_stash)?;
    }

    if stack.len() != 1 {
        return Err(CheckingError::KernelDivergence(format!(
            "pol shadow stack ended with {} entries where the live stack had 1",
            stack.len()
        )));
    }
    let derived = match stack.pop().unwrap() {
        Ok(c) => c,
        // A guard refusal alongside a *narrow* live result is not the same
        // fact as a guard refusal alongside a wide one, and the census should
        // not spell them the same way. The kernel refuses only when the exact
        // value of some step leaves `i64`; the live machine, when its own
        // arithmetic leaves `i64`, promotes the constraint to `i128` or
        // `BigInt`. So a run that ends *inside* `i64` while the kernel's exact
        // replay went outside it is either a derivation that legitimately dips
        // out and comes back (multiply then divide), or a narrow-width wrap of
        // the shape upstream defects 1 and 7 had — and this function cannot
        // tell which, having only the live *result*, not the live
        // intermediates. It stays a counted skip rather than a divergence for
        // exactly that reason; naming it separately is what stops it hiding
        // among the honest representability limits.
        // Only the narrow tier can reach this: at the complete tier no rule
        // refuses on width, so a refusal there is a genuine hypothesis
        // failure and keeps its own name.
        Err("kernel-guard-refused") if C::NARROW && to_kernel::<C>(live_result).is_some() => {
            return Ok(StepOutcome::skipped(
                "kernel-guard-refused-with-narrow-result",
            ));
        }
        Err(reason) => return Ok(StepOutcome::skipped(reason)),
    };

    let live = match to_kernel::<C>(live_result) {
        Some(k) => k,
        None => return Ok(StepOutcome::skipped("result-not-i64-representable")),
    };
    // The final shadow is a `normC` fixpoint (every `Ok` stack entry is),
    // so `sort_canon` computes exactly what `canonical` computed here — and
    // since re-normalizing a fixpoint cannot fail, dropping the shadow from
    // the `else` guard leaves the skip path unchanged.
    let derived_canon = sort_canon(&derived);
    let Some(live_canon) = canonical(&live) else {
        return Ok(StepOutcome::skipped("kernel-guard-refused"));
    };
    if derived_canon != live_canon {
        return Err(CheckingError::KernelDivergence(format!(
            "pol result diverges from the proved kernel: live {:?} vs kernel {:?}",
            live_canon, derived_canon
        )));
    }
    Ok(StepOutcome::verified(match program_taint {
        Some(reason) => Err(reason),
        // The replay is a `DStep` chain over the shadow database (`DStep.ax`
        // on the leaves, the arithmetic rules on the operations), so
        // `VeriPbCore.dstep_entails` gives `Entails F` for its result; the
        // final `normC` image is the same constraint by
        // `VeriPbCore.entails_normC` (`DStep.normS`) and cannot fail to
        // normalize, `derived` being a fixpoint.
        None => match normalize(&derived) {
            Ok(n) => Ok(C::into_any(n)),
            Err(_) => Err("kernel-guard-refused"),
        },
    }))
}

/// Resolve one `pol` `ConstraintId` leaf against the shadow database and the
/// live database, checking the two for drift.
///
/// Returns the constraint the replay should push. When the shadow slot is
/// present it *is* that constraint, so the replay's `DStep.ax` step reads
/// the shadow database (see [`verify_pol`]); otherwise the live entry is
/// converted as before and `program_taint` records why this program cannot
/// compose.
fn resolve_pol_leaf<C: Tier>(
    id: usize,
    database: &Database,
    shadow: Option<&KernelShadowDb>,
    program_taint: &mut Option<&'static str>,
) -> Result<Shadow<C>, CheckingError> {
    let live = database.get_entry_usize(id);
    let slot = shadow.map(|s| s.slot(id));
    if let (Some(Slot::Present(c)), Ok(entry)) = (slot, &live) {
        // The composition-grade leaf: the live database entry at this id
        // must still be the constraint the kernel justified for it. A
        // mismatch is the exact class of bug this feature exists to catch —
        // the live database drifted from the derivation that produced it.
        match slot_matches_live(c, &entry.constraint) {
            // A slot the *replay's* tier cannot hold is a width limit of this
            // tier, named as one so the dispatch retries a tier up.
            Some(true) => {
                return Ok(match c.at::<C>() {
                    Some(k) => Ok(k),
                    None => {
                        program_taint.get_or_insert("constraint-not-i64-representable");
                        Err("constraint-not-i64-representable")
                    }
                });
            }
            Some(false) => {
                return Err(CheckingError::KernelDivergence(format!(
                    "database id {id} diverges from the proved kernel: the live entry {:?} is not \
                     the constraint {:?} the kernel derived for that id",
                    entry.constraint, c
                )));
            }
            // The live entry is outside the kernel's domain, so the slot and
            // the entry cannot be compared at all: fall through to a taint.
            None => {
                program_taint.get_or_insert("constraint-not-i64-representable");
                return Ok(Err("constraint-not-i64-representable"));
            }
        }
    }
    // No usable slot: replay the live entry, and say why this program is not
    // composable.
    program_taint.get_or_insert(match slot {
        None => "kernel-shadow-unavailable",
        Some(Slot::Hole(reason)) => reason,
        Some(Slot::Deleted) => "shadow-slot-deleted",
        Some(Slot::Present(_)) => "constraint-missing",
    });
    Ok(match live {
        Ok(entry) => match to_kernel::<C>(&entry.constraint) {
            Some(k) => shadow_norm(k),
            None => Err("constraint-not-i64-representable"),
        },
        Err(_) => Err("constraint-missing"),
    })
}

/// Kernel-verify one `pol` derivation and feed the shadow database.
pub fn consume_pol(
    context: &mut crate::context::Context,
    database: &Database,
    instructions: &[Instruction],
    live_result: &PBConstraintEnum,
) -> Result<(), CheckingError> {
    if !context.config.kernel_verify {
        return Ok(());
    }
    // The shadow is read while `context` is mutated below; moving it out and
    // back is an `Option` swap, not a copy.
    let shadow = context.kernel_shadow.take();
    let outcome = verify_pol(instructions, database, shadow.as_ref(), live_result);
    context.kernel_shadow = shadow;
    record_step(context, outcome?, |s| s.pol_verified += 1);
    Ok(())
}

/// Replay a RUP conflict certificate captured by the propagation engine.
/// `target` is the RUP conclusion; `None` means the goal was contradiction
/// itself (top-level subproof discharge), whose negation is trivial.
///
/// # Reasons and composition
///
/// Every reason the engine propagated on is looked up in the live database
/// by the id its header carries, and that lookup is *confirmed by pointer
/// identity* against the database entry — so when it succeeds, the reason
/// genuinely is the constraint stored at that id, and the shadow slot for
/// that id is authoritative for it. The kernel then replays on the slot's
/// own constraint, making the trail a literal `VeriPbCore.DStep.rupS` over
/// the shadow database (`getG` index `i` is live id `i`, the same off-by-one
/// that maps slot `i` to Clean list index `i - 1`). A slot that disagrees
/// with the live entry is a divergence; a reason with no confirmable id (the
/// negated target, an autoproving-set premise) or no present slot is
/// replayed from the live constraint as before and taints composition.
///
/// `DbEntailed` is pointwise (`forall i c, getO DB i = some c -> Entails F
/// c`), so the compacted view handed to `rup::check_rup` — a list whose
/// every entry is a present shadow slot — is itself a `DbEntailed`
/// database, which is what `VeriPbCore.entails_of_rup` requires.
pub fn verify_rup_certificate(
    target: Option<&PBConstraintEnum>,
    cert: &KernelCertificate,
    database: &Database,
    shadow: Option<&KernelShadowDb>,
) -> Result<StepOutcome, CheckingError> {
    tiered_step(
        || verify_rup_certificate_at::<kernel::Coeff>(target, cert, database, shadow),
        || verify_rup_certificate_at::<Big>(target, cert, database, shadow),
    )
}

/// [`verify_rup_certificate`] at one coefficient tier.
fn verify_rup_certificate_at<C: Tier>(
    target: Option<&PBConstraintEnum>,
    cert: &KernelCertificate,
    database: &Database,
    shadow: Option<&KernelShadowDb>,
) -> Result<StepOutcome, CheckingError> {
    let kernel_target = match target {
        Some(c) => match to_kernel::<C>(c) {
            Some(k) => k,
            None => return Ok(StepOutcome::skipped("constraint-not-i64-representable")),
        },
        None => kernel::Constraint::contradiction(),
    };

    // Assemble the constraint view: index 0 is the (kernel's own) negation
    // of the target; every distinct reason constraint gets the next index.
    // `slots` deduplicates by constraint address in O(1); this is pure
    // bridge-side bookkeeping (which slot a reason maps to), not proved
    // semantics — the view handed to `check_rup` is unchanged. Keying by raw
    // pointer is sound here because the certificate holds an `Rc` clone of
    // every reason for the whole call, so no keyed allocation can be freed
    // (and thus none reused) while the map lives.
    let mut view = ReasonView::<C>::new();
    let mut steps: Vec<(usize, kernel::Lit)> = Vec::new();

    for (reason, lit) in &cert.steps {
        let rc = match reason {
            Reason::Assumption => return Ok(StepOutcome::skipped("rup-under-assumptions")),
            Reason::Constraint(rc) => rc,
        };
        let idx = match view.index_of(rc, cert.negated.as_ref(), database, shadow) {
            Ok(i) => i,
            Err(ReasonError::Skip(reason)) => return Ok(StepOutcome::skipped(reason)),
            Err(ReasonError::Diverged(err)) => return Err(err),
        };
        let Some(l) = kernel_lit(lit) else {
            return Ok(StepOutcome::skipped("variable-index-too-wide"));
        };
        steps.push((idx, l));
    }
    let conflict = match &cert.conflict {
        Reason::Assumption => return Ok(StepOutcome::skipped("rup-under-assumptions")),
        Reason::Constraint(rc) => {
            match view.index_of(rc, cert.negated.as_ref(), database, shadow) {
                Ok(i) => i,
                Err(ReasonError::Skip(reason)) => return Ok(StepOutcome::skipped(reason)),
                Err(ReasonError::Diverged(err)) => return Err(err),
            }
        }
    };

    view.replay(&kernel_target, &steps, conflict, |e| {
        CheckingError::KernelDivergence(format!(
            "RUP conflict certificate rejected by the proved kernel: {e:?}"
        ))
    })
}

/// The constraint view a RUP replay runs against: one entry per distinct
/// reason, at the index the kernel's `getG` will look it up under.
struct ReasonView<C: Tier> {
    /// View entry `k` is `getG` index `k + 1` (index 0 is the negated
    /// target, which `rup::check_rup` computes itself).
    owned: Vec<kernel::Constraint<C>>,
    /// The live reason each entry came from, parallel to `owned`, kept so
    /// the replay can be repeated on the unsubstituted constraints.
    origins: Vec<Rc<DBConstraint>>,
    /// Deduplication by constraint address. Sound because the caller holds
    /// an `Rc` clone of every reason for the whole call, so no keyed
    /// allocation can be freed (and thus none reused) while the map lives.
    seen: AHashMap<*const DBConstraint, usize>,
    /// Set when at least one entry is a shadow slot rather than a plain
    /// conversion of the live constraint.
    substituted: bool,
    /// Why this replay cannot compose, if it cannot.
    taint: Option<&'static str>,
}

impl<C: Tier> ReasonView<C> {
    fn new() -> Self {
        ReasonView {
            owned: Vec::new(),
            origins: Vec::new(),
            seen: AHashMap::new(),
            substituted: false,
            taint: None,
        }
    }

    /// The `getG` index of `rc`, adding it to the view on first sight.
    /// `negated` is the engine's temporary negated-target constraint, which
    /// the kernel keeps at index 0.
    fn index_of(
        &mut self,
        rc: &Rc<DBConstraint>,
        negated: Option<&Rc<DBConstraint>>,
        database: &Database,
        shadow: Option<&KernelShadowDb>,
    ) -> Result<usize, ReasonError> {
        if let Some(neg) = negated {
            if Rc::ptr_eq(rc, neg) {
                return Ok(0);
            }
        }
        let p = Rc::as_ptr(rc);
        if let Some(&pos) = self.seen.get(&p) {
            return Ok(pos);
        }
        let (k, from_slot) = resolve_reason(rc, database, shadow, &mut self.taint)?;
        self.substituted |= from_slot;
        self.owned.push(k);
        self.origins.push(Rc::clone(rc));
        self.seen.insert(p, self.owned.len());
        Ok(self.owned.len())
    }

    /// Run the kernel's RUP replay over this view.
    ///
    /// Substituting shadow slots for the live constraints is what makes the
    /// trail a `DStep.rupS` over the shadow database, but it also hands the
    /// kernel proved *normal forms* where the live checker propagated on the
    /// stored shapes. Those agree on every predicate the replay evaluates —
    /// `slackTerms`, `slackWithout` and `AllNonneg` are folds over the term
    /// list, and a slot is a permutation of the entry's normal form — but
    /// verdict-neutrality is not something to argue for: if the substituted
    /// replay is rejected, the replay is repeated on the unsubstituted
    /// constraints, exactly as before this shadow existed. Only a rejection
    /// of *that* is a divergence; a substituted-only rejection costs
    /// composition and nothing else.
    fn replay(
        &self,
        target: &kernel::Constraint<C>,
        steps: &[(usize, kernel::Lit)],
        conflict: usize,
        diverged: impl Fn(rup::RupError) -> CheckingError,
    ) -> Result<StepOutcome, CheckingError> {
        let refs: Vec<&kernel::Constraint<C>> = self.owned.iter().collect();
        match rup::check_rup(target, &refs, steps, conflict) {
            Ok(()) => Ok(StepOutcome::verified(rup_slot(target, self.taint))),
            // Failing to negate the target is an i64-representability limit
            // of the kernel, not a disagreement with the live checker.
            Err(rup::RupError::NegationOverflow(_)) => {
                Ok(StepOutcome::skipped("kernel-guard-refused"))
            }
            Err(e) => {
                if !self.substituted {
                    return Err(diverged(e));
                }
                let mut raw: Vec<kernel::Constraint<C>> = Vec::with_capacity(self.origins.len());
                for rc in &self.origins {
                    match to_kernel::<C>(&rc.constraint) {
                        Some(k) => raw.push(k),
                        None => return Err(diverged(e)),
                    }
                }
                let refs: Vec<&kernel::Constraint<C>> = raw.iter().collect();
                match rup::check_rup(target, &refs, steps, conflict) {
                    Ok(()) => Ok(StepOutcome {
                        check: None,
                        slot: Err("rup-shadow-view-rejected"),
                    }),
                    Err(rup::RupError::NegationOverflow(_)) => {
                        Ok(StepOutcome::skipped("kernel-guard-refused"))
                    }
                    Err(e) => Err(diverged(e)),
                }
            }
        }
    }
}

/// Why a RUP reason could not be turned into a view entry.
enum ReasonError {
    /// Counted skip: the reason is outside the kernel's domain.
    Skip(&'static str),
    /// The live database and the shadow disagree about an id.
    Diverged(CheckingError),
}

/// Turn one RUP reason into the constraint the kernel replays on, together
/// with whether that constraint came from the shadow database.
///
/// Prefers the shadow slot of the id the reason is stored at — confirmed by
/// pointer identity against the live database entry, so the slot really is
/// this reason's slot — and falls back to converting the live constraint,
/// tainting composition. See [`verify_rup_certificate`].
fn resolve_reason<C: Tier>(
    rc: &Rc<DBConstraint>,
    database: &Database,
    shadow: Option<&KernelShadowDb>,
    taint: &mut Option<&'static str>,
) -> Result<(kernel::Constraint<C>, bool), ReasonError> {
    if let Some(shadow) = shadow {
        let id = rc.get_some_id();
        // `get_some_id` reads the reason's own header, which can name an id
        // of a database this reason no longer lives in (id 0 for the
        // negated target and the autoproving-set premises, a stale id for a
        // constraint the engine kept as a saved reason past its deletion),
        // so the id is only usable once the live entry confirms it.
        let confirmed = id != 0
            && matches!(
                database.entries.get(id),
                Some(Some(entry)) if Rc::ptr_eq(entry, rc)
            );
        if confirmed {
            if let Slot::Present(c) = shadow.slot(id) {
                return match slot_matches_live(c, &rc.constraint) {
                    // A slot this tier cannot hold is a width limit of the
                    // tier: named as such so the dispatch retries wider.
                    Some(true) => match c.at::<C>() {
                        Some(k) => Ok((k, true)),
                        None => Err(ReasonError::Skip("constraint-not-i64-representable")),
                    },
                    Some(false) => Err(ReasonError::Diverged(CheckingError::KernelDivergence(
                        format!(
                            "RUP reason at database id {id} diverges from the proved kernel: the \
                             live entry {:?} is not the constraint {:?} the kernel derived for \
                             that id",
                            rc.constraint, c
                        ),
                    ))),
                    None => Err(ReasonError::Skip("constraint-not-i64-representable")),
                };
            }
            taint.get_or_insert(match shadow.slot(id) {
                Slot::Hole(reason) => reason,
                _ => "rup-reason-outside-shadow",
            });
        } else {
            taint.get_or_insert("rup-reason-outside-shadow");
        }
    } else {
        taint.get_or_insert("kernel-shadow-unavailable");
    }
    match to_kernel::<C>(&rc.constraint) {
        Some(k) => Ok((k, false)),
        None => Err(ReasonError::Skip("constraint-not-i64-representable")),
    }
}

/// The shadow contribution of a verified RUP derivation: the target itself,
/// entailed by `VeriPbCore.entails_of_rup` and stored as its `normC` image
/// (`VeriPbCore.entails_normC`).
fn rup_slot<C: Tier>(
    kernel_target: &kernel::Constraint<C>,
    taint: Option<&'static str>,
) -> SlotOutcome {
    if let Some(reason) = taint {
        return Err(reason);
    }
    normalize(kernel_target)
        .map(C::into_any)
        .map_err(|_| "kernel-guard-refused")
}

/// Verify a hinted RUP acceptance: run kernel-checked propagation round-robin
/// over exactly the hinted constraints until a kernel-checked conflict.
///
/// The hint names database ids outright, so the reason resolution of
/// [`verify_rup_certificate`] applies with the id already in hand — see
/// [`ReasonView::replay`] for why a substituted view can never cost a
/// verdict.
pub fn verify_hinted_rup(
    target: &PBConstraintEnum,
    hinted: &[(usize, Rc<DBConstraint>)],
    database: &Database,
    shadow: Option<&KernelShadowDb>,
) -> Result<StepOutcome, CheckingError> {
    tiered_step(
        || verify_hinted_rup_at::<kernel::Coeff>(target, hinted, database, shadow),
        || verify_hinted_rup_at::<Big>(target, hinted, database, shadow),
    )
}

/// [`verify_hinted_rup`] at one coefficient tier.
fn verify_hinted_rup_at<C: Tier>(
    target: &PBConstraintEnum,
    hinted: &[(usize, Rc<DBConstraint>)],
    database: &Database,
    shadow: Option<&KernelShadowDb>,
) -> Result<StepOutcome, CheckingError> {
    let Some(kernel_target) = to_kernel::<C>(target) else {
        return Ok(StepOutcome::skipped("constraint-not-i64-representable"));
    };
    let Ok(neg) = kernel::negate(&kernel_target) else {
        return Ok(StepOutcome::skipped("kernel-guard-refused"));
    };
    let mut reasons = ReasonView::<C>::new();
    for (id, rc) in hinted {
        // Feeding the id straight in is the same confirmation
        // `resolve_reason` performs, without the header round-trip: the
        // caller resolved this `Rc` *through* `database` at this id.
        debug_assert!(matches!(database.entries.get(*id), Some(Some(e)) if Rc::ptr_eq(e, rc)));
        match reasons.index_of(rc, None, database, shadow) {
            Ok(_) => {}
            Err(ReasonError::Skip(reason)) => return Ok(StepOutcome::skipped(reason)),
            Err(ReasonError::Diverged(err)) => return Err(err),
        }
    }
    let diverged = |e: rup::RupError| {
        CheckingError::KernelDivergence(format!(
            "hinted RUP replay rejected by the proved kernel: {e:?}"
        ))
    };
    let no_conflict = || {
        CheckingError::KernelDivergence(
            "hinted RUP accepted by the checker, but kernel propagation over the same hints reaches no conflict".to_string(),
        )
    };

    match hinted_search(&neg, &reasons.owned) {
        Ok((steps, conflict)) => reasons.replay(&kernel_target, &steps, conflict, diverged),
        Err(HintedSearch::NotNormalized) => {
            Ok(StepOutcome::skipped("hinted-constraint-not-normalized"))
        }
        // No conflict over the shadow-substituted constraints. A slot is a
        // proved normal form of the same constraint and so propagates at
        // least as strongly as the stored shape, but that argument must not
        // be what stands between a real engine/kernel disagreement and a
        // rejection: repeat the whole search on the unsubstituted
        // constraints and let *that* decide the verdict.
        Err(HintedSearch::NoConflict) => {
            if !reasons.substituted {
                return Err(no_conflict());
            }
            let mut raw: Vec<kernel::Constraint<C>> = Vec::with_capacity(reasons.origins.len());
            for rc in &reasons.origins {
                match to_kernel::<C>(&rc.constraint) {
                    Some(k) => raw.push(k),
                    None => return Err(no_conflict()),
                }
            }
            match hinted_search(&neg, &raw) {
                Ok((steps, conflict)) => {
                    let refs: Vec<&kernel::Constraint<C>> = raw.iter().collect();
                    match rup::check_rup(&kernel_target, &refs, &steps, conflict) {
                        Ok(()) => Ok(StepOutcome {
                            check: None,
                            slot: Err("rup-shadow-view-rejected"),
                        }),
                        Err(rup::RupError::NegationOverflow(_)) => {
                            Ok(StepOutcome::skipped("kernel-guard-refused"))
                        }
                        Err(e) => Err(diverged(e)),
                    }
                }
                Err(HintedSearch::NotNormalized) => {
                    Ok(StepOutcome::skipped("hinted-constraint-not-normalized"))
                }
                Err(HintedSearch::NoConflict) => Err(no_conflict()),
            }
        }
    }
}

/// Why the hinted round-robin search stopped without a conflict.
enum HintedSearch {
    /// A hinted constraint has a negative coefficient, so the kernel's
    /// slack conditions (`AllNonneg`) do not apply to it.
    NotNormalized,
    /// Propagation reached a fixpoint with no conflict.
    NoConflict,
}

/// Kernel-checked round-robin propagation over the negated target followed by
/// `reasons`, in the kernel's `getG` indexing (index 0 is the negation).
/// Returns the propagation order and the conflicting index.
///
/// This is bridge *search*, not a proved mirror: whatever it returns is
/// re-checked step by step by `rup::check_rup` before anything is counted, so
/// the only thing it owes the caller is not to *under*-propagate — a spurious
/// `NoConflict` becomes a [`CheckingError::KernelDivergence`]. The fast pass
/// (see [`hinted_search_pass`]) can under-propagate on a constraint carrying
/// duplicate literals, so any non-`Ok` outcome is re-derived by the exact
/// pass, which is the implementation this function had before the index. A
/// fast `Ok` needs no such fallback: every step it emits satisfies the exact
/// `slackWithout` condition (that is what makes the estimate one-sided), and
/// `check_rup` re-verifies each one regardless.
fn hinted_search<C: Tier>(
    neg: &kernel::Constraint<C>,
    reasons: &[kernel::Constraint<C>],
) -> Result<(Vec<(usize, kernel::Lit)>, usize), HintedSearch> {
    match hinted_search_pass(neg, reasons, true) {
        Ok(found) => Ok(found),
        Err(_) => hinted_search_pass(neg, reasons, false),
    }
}

/// One round-robin propagation search, exact or with the running-slack
/// estimate.
///
/// With `fast` the per-term test `slack_without(l, trail, c.terms) < degree`
/// is answered as `slack_terms(trail_at_visit, c.terms) - t.coeff < degree`.
/// That is the *same* value whenever `c` mentions `l` once and nothing has
/// been inserted since the visit began, and otherwise an over-estimate of the
/// slack, because (a) the trail only grows, so the visit's `slack_terms` is at
/// least the current one, and (b) with `AllNonneg` already checked, dropping
/// one term of literal `l` drops at most what `slackWithout` drops. So the
/// test fires only where the exact one does: the pass propagates a subset of
/// the exact fixpoint and can never emit a step `check_rup` would reject.
fn hinted_search_pass<C: Tier>(
    neg: &kernel::Constraint<C>,
    reasons: &[kernel::Constraint<C>],
    fast: bool,
) -> Result<(Vec<(usize, kernel::Lit)>, usize), HintedSearch> {
    let mut view: Vec<&kernel::Constraint<C>> = Vec::with_capacity(reasons.len() + 1);
    view.push(neg);
    view.extend(reasons.iter());

    // The trail is queried only for membership, so the kernel's insert-only
    // `Trail` set answers the same `memB` predicate the search needs in
    // O(1); the `steps` Vec keeps the propagation order `check_rup` replays.
    let mut trail = rup::Trail::new();
    let mut steps: Vec<(usize, kernel::Lit)> = Vec::new();
    // `AllNonneg` is a pure function of a constraint's terms, which never
    // change here, so it is computed on first visit and remembered. The check
    // still *fires* exactly where it fired before — in visit order, before
    // that constraint's slack test — so which constraint is reported as
    // un-normalized is unchanged.
    let mut nonneg: Vec<Option<bool>> = vec![None; view.len()];
    loop {
        let mut changed = false;
        for (i, c) in view.iter().enumerate() {
            let ok = match nonneg[i] {
                Some(known) => known,
                None => {
                    let known = c.all_nonneg();
                    nonneg[i] = Some(known);
                    known
                }
            };
            if !ok {
                return Err(HintedSearch::NotNormalized);
            }
            let degree = c.degree.widen();
            let slack_at_visit = rup::slack_terms(&trail, &c.terms);
            if slack_at_visit < degree {
                return Ok((steps, i));
            }
            for t in &c.terms {
                let l = t.lit;
                if trail.assigned(l) || trail.falsified(l) {
                    continue;
                }
                let slack = if fast {
                    let estimate = slack_at_visit.sub(&t.coeff.widen());
                    debug_assert!(
                        estimate >= rup::slack_without(l, &trail, &c.terms),
                        "the running-slack estimate must never under-state slackWithout"
                    );
                    estimate
                } else {
                    rup::slack_without(l, &trail, &c.terms)
                };
                if slack < degree {
                    trail.insert(l);
                    steps.push((i, l));
                    changed = true;
                }
            }
        }
        if !changed {
            return Err(HintedSearch::NoConflict);
        }
    }
}

/// Consume the engine's certificate after a conflicting RUP check and verify
/// it, updating the run statistics.
///
/// This is the *discharge* form, for acceptances that decide a proof goal
/// without storing anything. A `rup` step that adds its conclusion to the
/// database uses [`consume_rup_derivation`], which additionally feeds the
/// shadow database. The two are wrappers over one shared implementation
/// (`rup_conflict_outcome`), and between them they are what every
/// engine-conflict acceptance in the checker funnels through.
pub fn consume_rup_conflict(
    context: &mut crate::context::Context,
    database: &Database,
    target: Option<&PBConstraintEnum>,
) -> Result<(), CheckingError> {
    if !context.config.kernel_verify {
        return Ok(());
    }
    let outcome = rup_conflict_outcome(context, database, target)?;
    match outcome.check {
        None => context.kernel_stats.rup_verified += 1,
        Some(reason) => context.kernel_stats.skip(reason),
    }
    Ok(())
}

/// [`consume_rup_conflict`] for a `rup`-style step that stores its
/// conclusion: the verified target also becomes the new shadow slot.
pub fn consume_rup_derivation(
    context: &mut crate::context::Context,
    database: &Database,
    target: &PBConstraintEnum,
) -> Result<(), CheckingError> {
    if !context.config.kernel_verify {
        return Ok(());
    }
    let outcome = rup_conflict_outcome(context, database, Some(target))?;
    record_step(context, outcome, |s| s.rup_verified += 1);
    Ok(())
}

fn rup_conflict_outcome(
    context: &mut crate::context::Context,
    database: &Database,
    target: Option<&PBConstraintEnum>,
) -> Result<StepOutcome, CheckingError> {
    let cert = context.propagation_engine.kernel_certificate.take();
    // The shadow is read while `context` is borrowed; moving it out and back
    // is an `Option` swap, not a copy.
    let shadow = context.kernel_shadow.take();
    let outcome = match &cert {
        Some(cert) => verify_rup_certificate(target, cert, database, shadow.as_ref()),
        // The engine accepts a trivially-true conclusion without building a
        // trail; the kernel must agree it is trivial. Any other
        // certificate-less accept is counted, not trusted.
        None => match target {
            // `entails_trivial` needs no database at all, so a trivial
            // conclusion composes unconditionally.
            Some(c) if c.is_trivial() => match verify_trivial(c) {
                Ok(None) => Ok(StepOutcome::verified(
                    AnyConstraint::normalized_from_live(c).ok_or("kernel-guard-refused"),
                )),
                Ok(Some(reason)) => Ok(StepOutcome::skipped(reason)),
                Err(err) => Err(err),
            },
            _ => Ok(StepOutcome::skipped("rup-certificate-unavailable")),
        },
    };
    context.kernel_shadow = shadow;
    outcome
}

/// Kernel-verify one hinted `rup` derivation and feed the shadow database.
pub fn consume_hinted_rup(
    context: &mut crate::context::Context,
    database: &Database,
    hinted: &[(usize, Rc<DBConstraint>)],
    target: &PBConstraintEnum,
) -> Result<(), CheckingError> {
    if !context.config.kernel_verify {
        return Ok(());
    }
    let shadow = context.kernel_shadow.take();
    let outcome = verify_hinted_rup(target, hinted, database, shadow.as_ref());
    context.kernel_shadow = shadow;
    record_step(context, outcome?, |s| s.rup_verified += 1);
    Ok(())
}

/// A constraint the live checker accepted as trivially true — a RUP
/// conclusion without propagation, a trivial proofgoal discharge, an order
/// reflexivity obligation: the kernel must agree (normalized degree at most
/// zero, licensed by `entails_trivial` on the proved normal form).
pub fn verify_trivial(c: &PBConstraintEnum) -> BridgeOutcome {
    tiered_outcome(
        || verify_trivial_at::<kernel::Coeff>(c),
        || verify_trivial_at::<Big>(c),
    )
}

/// [`verify_trivial`] at one coefficient tier.
fn verify_trivial_at<C: Tier>(c: &PBConstraintEnum) -> BridgeOutcome {
    let Some(k) = to_kernel::<C>(c) else {
        return Ok(Some("constraint-not-i64-representable"));
    };
    let Ok(n) = normalize(&k) else {
        return Ok(Some("kernel-guard-refused"));
    };
    if n.degree <= C::zero() {
        Ok(None)
    } else {
        Err(CheckingError::KernelDivergence(
            "constraint accepted as trivial, but the proved kernel computes a positive normalized degree".to_string(),
        ))
    }
}

/// Consume one trivial-accept: re-judge it through [`verify_trivial`] and
/// record the outcome. This is the shared entry point for every acceptance
/// path that rests on the live `is_trivial()` alone (trivial proofgoal
/// discharges, autoproved order reflexivity).
pub fn consume_trivial(
    context: &mut crate::context::Context,
    c: &PBConstraintEnum,
) -> Result<(), CheckingError> {
    if !context.config.kernel_verify {
        return Ok(());
    }
    match verify_trivial(c) {
        Ok(None) => {
            context.kernel_stats.trivial_verified += 1;
            Ok(())
        }
        Ok(Some(reason)) => {
            context.kernel_stats.skip(reason);
            Ok(())
        }
        Err(err) => Err(err),
    }
}

/// Kernel-verify a DB-lookup accept: the live checker accepted `goal`
/// because a database lookup (hash probe + structural `Eq` on the live
/// representation) found `found`. Both sides are converted, kernel-
/// normalized and sorted ([`canonical`]); the accept is licensed by
/// database membership (the ax rule on a stored constraint) plus
/// `VeriPbCore.entails_of_normC_eq`, which requires the two proved normal
/// forms to be *equal*. The live lookup may match by hash/`Eq` on a
/// different representation than the kernel's — if the canonical forms
/// differ, the two implementations disagree about constraint equality, and
/// that is a divergence, never a skip.
///
/// With today's derived structural `PartialEq` on `PBConstraintEnum` the
/// two live objects are content-identical whenever this is reached, so the
/// comparison cannot fail; its value is (a) truthful coverage accounting,
/// (b) surfacing i64-unrepresentable DB-equality accepts as counted skips,
/// and (c) a backstop that turns any future loosening of live equality /
/// hash / unique-index semantics into a `KernelDivergence` instead of
/// silent trust.
pub fn verify_db_lookup(goal: &PBConstraintEnum, found: &PBConstraintEnum) -> BridgeOutcome {
    tiered_outcome(
        || verify_db_lookup_at::<kernel::Coeff>(goal, found),
        || verify_db_lookup_at::<Big>(goal, found),
    )
}

/// [`verify_db_lookup`] at one coefficient tier.
fn verify_db_lookup_at<C: Tier>(
    goal: &PBConstraintEnum,
    found: &PBConstraintEnum,
) -> BridgeOutcome {
    let (Some(g), Some(f)) = (to_kernel::<C>(goal), to_kernel::<C>(found)) else {
        return Ok(Some("constraint-not-i64-representable"));
    };
    let (Some(gc), Some(fc)) = (canonical(&g), canonical(&f)) else {
        return Ok(Some("kernel-guard-refused"));
    };
    if gc == fc {
        Ok(None)
    } else {
        Err(CheckingError::KernelDivergence(format!(
            "DB-lookup accept diverges from the proved kernel: goal {:?} and found database constraint {:?} disagree after kernel normalization",
            gc, fc
        )))
    }
}

/// Consume one DB-lookup accept: re-judge it through [`verify_db_lookup`]
/// and record the outcome. This is the shared entry point for every
/// "constraint equals a database constraint" acceptance (proofgoal
/// DBLookup, the red/pbc "constraint is in DB already" shortcuts, checked
/// deletion's DB shortcut, and the `e`/`ea` rule).
pub fn consume_db_lookup(
    context: &mut crate::context::Context,
    goal: &PBConstraintEnum,
    found: &PBConstraintEnum,
) -> Result<(), CheckingError> {
    if !context.config.kernel_verify {
        return Ok(());
    }
    match verify_db_lookup(goal, found) {
        Ok(None) => {
            context.kernel_stats.db_lookup_verified += 1;
            Ok(())
        }
        Ok(Some(reason)) => {
            context.kernel_stats.skip(reason);
            Ok(())
        }
        Err(err) => Err(err),
    }
}

/// Consume one syntactic-implication accept that discharges an obligation
/// without storing anything: re-judge it through [`verify_implication`] and
/// record the outcome.
pub fn consume_implication(
    context: &mut crate::context::Context,
    source: &PBConstraintEnum,
    target: &PBConstraintEnum,
) -> Result<(), CheckingError> {
    if !context.config.kernel_verify {
        return Ok(());
    }
    match verify_implication(source, target) {
        Ok(None) => {
            context.kernel_stats.implication_verified += 1;
            Ok(())
        }
        Ok(Some(reason)) => {
            context.kernel_stats.skip(reason);
            Ok(())
        }
        Err(err) => Err(err),
    }
}

/// Re-judge one obligation that proofgoal *generation* discharged.
///
/// `red`, `dom` and checked deletion do not turn every touched database
/// constraint into a proof goal: an obligation whose substituted form is
/// trivially true, or which its own original implies, or which equals a usable
/// database constraint, is discharged inside
/// [`Database::get_proofgoals`](crate::database::Database::get_proofgoals) and
/// never becomes a goal at all. Those are the same three acceptance shapes as
/// the explicit `Trivial` / `DBImplies` / `DBLookup` proofgoal discharges, so
/// they go through the same three entry points and land in the same counters —
/// the alternative being a whole class of accepts that the summary line never
/// mentions.
///
/// This is a *re-derivation only*: the enclosing rule's own slot contribution
/// is unaffected (the meta-step it rests on — the `red` witness, the dominance
/// order, the deletion witness — is unmodelled and already counted where it
/// happens), so nothing is offered to the shadow database here.
pub fn consume_autodischarge(
    context: &mut crate::context::Context,
    discharged: &crate::database::AutoDischarge,
) -> Result<(), CheckingError> {
    use crate::database::AutoDischarge;
    match discharged {
        AutoDischarge::Trivial(_, image) => consume_trivial(context, &image.constraint),
        AutoDischarge::Implied(source, target) => {
            consume_implication(context, &source.constraint, &target.constraint)
        }
        AutoDischarge::DbLookup(_, goal, found) => {
            consume_db_lookup(context, &goal.constraint, &found.constraint)
        }
    }
}

/// [`consume_db_lookup`] for a step that *stores* a copy of the database
/// constraint it found (the `red` / v2 `pbc` "constraint is in DB already"
/// shortcuts): the found id's shadow slot becomes the new slot.
///
/// The `DStep.ax` step names the found id, and the accept establishes that
/// goal and found agree on their proved normal forms, so
/// `VeriPbCore.entails_of_normC_eq` carries the entailment to the stored
/// copy. As everywhere, what is *stored* is the slot's own constraint, so
/// the term-order gap between the two normal forms never reaches the kernel.
pub fn consume_db_lookup_derivation(
    context: &mut crate::context::Context,
    database: &Database,
    goal: &PBConstraintEnum,
    found: &Rc<DBConstraint>,
) -> Result<(), CheckingError> {
    if !context.config.kernel_verify {
        return Ok(());
    }
    let outcome = match verify_db_lookup(goal, &found.constraint) {
        Ok(None) => StepOutcome::verified(db_lookup_slot(context, database, found)),
        Ok(Some(reason)) => StepOutcome::skipped(reason),
        Err(err) => return Err(err),
    };
    record_step(context, outcome, |s| s.db_lookup_verified += 1);
    Ok(())
}

/// The shadow slot of a database constraint the checker looked up, or the
/// reason there is none. The id comes from the constraint's own header and
/// is only usable once the live entry confirms it (see [`resolve_reason`]).
fn db_lookup_slot(
    context: &crate::context::Context,
    database: &Database,
    found: &Rc<DBConstraint>,
) -> SlotOutcome {
    let Some(shadow) = context.kernel_shadow.as_ref() else {
        return Err("kernel-shadow-unavailable");
    };
    let id = found.get_some_id();
    if id == 0 || !matches!(database.entries.get(id), Some(Some(entry)) if Rc::ptr_eq(entry, found))
    {
        return Err("db-lookup-outside-shadow");
    }
    match shadow.slot(id) {
        Slot::Present(c) => Ok(c.clone()),
        Slot::Hole(reason) => Err(reason),
        Slot::Deleted => Err("shadow-slot-deleted"),
    }
}

/// Kernel-verify a syntactic-implication step that *stores* its conclusion
/// (the `ia` rule with `add_result`).
///
/// The proved reconstruction chain of [`verify_implication`] is run from the
/// source's shadow slot rather than from the live entry, so the whole chain
/// is a `DStep` over the shadow database rooted at `DStep.ax` on `source_id`
/// — `VeriPbCore.dstep_entails` then gives `Entails F` for the target, whose
/// `normC` image (`VeriPbCore.entails_normC`) becomes the new slot. Without
/// a usable slot the chain still runs from the live source, so the
/// per-step statistic is unchanged, and the new slot is a tainted hole.
pub fn consume_implication_derivation(
    context: &mut crate::context::Context,
    database: &Database,
    source_id: isize,
    target: &PBConstraintEnum,
) -> Result<(), CheckingError> {
    if !context.config.kernel_verify {
        return Ok(());
    }
    let source = &database.get_entry(source_id)?.constraint;
    // The shadow is read while `context` is mutated below; moving it out and
    // back is an `Option` swap, not a copy.
    let shadow = context.kernel_shadow.take();
    let outcome = tiered_step(
        || {
            implication_derivation_outcome::<kernel::Coeff>(
                database,
                shadow.as_ref(),
                source_id,
                source,
                target,
            )
        },
        || {
            implication_derivation_outcome::<Big>(
                database,
                shadow.as_ref(),
                source_id,
                source,
                target,
            )
        },
    );
    context.kernel_shadow = shadow;
    record_step(context, outcome?, |s| s.implication_verified += 1);
    Ok(())
}

/// [`consume_implication_derivation`] at one coefficient tier.
fn implication_derivation_outcome<C: Tier>(
    database: &Database,
    shadow: Option<&KernelShadowDb>,
    source_id: isize,
    source: &PBConstraintEnum,
    target: &PBConstraintEnum,
) -> Result<StepOutcome, CheckingError> {
    let (Some(sk), Some(tk)) = (to_kernel::<C>(source), to_kernel::<C>(target)) else {
        return Ok(StepOutcome::skipped("constraint-not-i64-representable"));
    };
    let id = database.normalize_id(source_id);
    let slot: Result<kernel::Constraint<C>, &'static str> = if id < 0 {
        Err("shadow-id-out-of-range")
    } else {
        match shadow {
            None => Err("kernel-shadow-unavailable"),
            Some(shadow) => match shadow.slot(id as usize) {
                Slot::Present(c) => match slot_matches_live(c, source) {
                    Some(true) => c.at::<C>().ok_or("constraint-not-i64-representable"),
                    Some(false) => {
                        return Err(CheckingError::KernelDivergence(format!(
                            "database id {id} diverges from the proved kernel: the live entry \
                             {source:?} is not the constraint {c:?} the kernel derived for that id"
                        )));
                    }
                    None => Err("constraint-not-i64-representable"),
                },
                Slot::Hole(reason) => Err(*reason),
                Slot::Deleted => Err("shadow-slot-deleted"),
            },
        }
    };
    Ok(
        match verify_implication_kernel(slot.as_ref().unwrap_or(&sk), &tk) {
            Ok(None) => StepOutcome::verified(match slot {
                Err(reason) => Err(reason),
                Ok(_) => normalize(&tk)
                    .map(C::into_any)
                    .map_err(|_| "kernel-guard-refused"),
            }),
            Ok(Some(reason)) => StepOutcome::skipped(reason),
            Err(err) => return Err(err),
        },
    )
}

/// Kernel-verify that the constraint stored at `id` really is a
/// contradiction, recording the outcome in the run statistics. One shared
/// implementation for every discharge-by-contradiction accept: the
/// conclusion rules (`UNSAT`, infeasible/enumeration bounds) *and* the
/// mid-proof subproof/proofgoal `qed` discharges, which decide red-step
/// subproofs long before conclusion time (their constraints are deleted at
/// `qed`, so conclusion-time re-judging could never cover them).
pub fn kernel_check_contradiction_id(
    context: &mut crate::context::Context,
    database: &Database,
    id: isize,
) -> Result<(), CheckingError> {
    if !context.config.kernel_verify {
        return Ok(());
    }
    let entry = database.get_entry(id)?;
    match verify_contradiction(&entry.constraint) {
        Ok(None) => {
            context.kernel_stats.contradiction_verified += 1;
            Ok(())
        }
        Ok(Some(reason)) => {
            context.kernel_stats.skip(reason);
            Ok(())
        }
        Err(err) => Err(err),
    }
}

/// [`kernel_check_contradiction_id`] for a contradiction that *concludes the
/// run* — `conclusion UNSAT`, an infeasible lower bound, a complete
/// enumeration.
///
/// On top of re-judging the constraint, this records the run-level verdict:
/// whether the shadow database composes into a `VeriPbCore.checker_sound`
/// instance at this id (see [`shadow_record_refutation`]). Mid-proof `qed`
/// discharges deliberately do *not* go through here: they decide a subproof,
/// not the run.
pub fn kernel_certify_refutation(
    context: &mut crate::context::Context,
    database: &Database,
    id: isize,
) -> Result<(), CheckingError> {
    kernel_check_contradiction_id(context, database, id)?;
    if context.config.kernel_verify {
        // `get_entry` above resolved this id against the same entry vector
        // the shadow mirrors, so the normalized index addresses the slot.
        let idx = database.normalize_id(id);
        if idx >= 0 {
            shadow_record_refutation(context, idx as usize);
        }
    }
    Ok(())
}

/// Shadow-recompute a claimed objective value from the objective terms and
/// the assignment, in exact arithmetic.
///
/// This is a **shadow recomputation, not a kernel theorem**: the proved
/// kernel has no objective model (the development design notes section 5, item 5),
/// so there is nothing to re-derive through proved code. Instead the bridge
/// sums the satisfied terms itself, in exact arithmetic, adds the objective
/// constant and requires exact agreement with the value the live checker
/// computed. A mismatch means the two arithmetic implementations diverged on
/// the same data.
///
/// The sum is tiered like every other check here: `i128` while the objective
/// stays inside `i64` coefficients (exact — at most `u32::MAX` terms of `i64`
/// coefficients), `BigInt` from the first coefficient that does not, so an
/// objective the live checker promoted is re-computed rather than skipped.
pub fn verify_objective_value(
    objective: &PBObjective,
    assignment: &Assignment<BooleanVar>,
    claimed: &BigInt,
) -> BridgeOutcome {
    /// The satisfied-term total at one width, or `None` when a coefficient
    /// does not fit it.
    fn total<C: Tier>(
        objective: &PBObjective,
        assignment: &Assignment<BooleanVar>,
    ) -> Result<Option<C::Exact>, CheckingError> {
        let mut sum = <C::Exact as Exact>::zero();
        for term in objective.terms.values() {
            let Some(coeff) = C::from_bigint(&term.coeff) else {
                return Ok(None);
            };
            match assignment.get_lit_value(term.lit) {
                BoolValue::Unassigned => {
                    return Err(CheckingError::KernelDivergence(
                        "objective value accepted by the checker, but an objective literal is unassigned in the shadow recomputation".to_string(),
                    ));
                }
                BoolValue::Assigned(true) => sum = sum.add(&coeff.widen()),
                BoolValue::Assigned(false) => {}
            }
        }
        Ok(Some(sum))
    }

    let sum: BigInt = match total::<kernel::Coeff>(objective, assignment)? {
        Some(narrow) => BigInt::from(narrow),
        None => match total::<Big>(objective, assignment)? {
            Some(wide) => wide,
            // Unreachable: `Big::from_bigint` is the identity.
            None => return Ok(Some("objective-not-i64-representable")),
        },
    };
    let recomputed = sum + &objective.constant;
    if recomputed == *claimed {
        Ok(None)
    } else {
        Err(CheckingError::KernelDivergence(format!(
            "objective value diverges: live checker computed {claimed}, exact shadow recomputation yields {recomputed}"
        )))
    }
}

/// Re-judge a stored contradiction through the kernel: after proved
/// normalization it must satisfy the `checker_sound` hypotheses.
pub fn verify_contradiction(c: &PBConstraintEnum) -> BridgeOutcome {
    tiered_outcome(
        || verify_contradiction_at::<kernel::Coeff>(c),
        || verify_contradiction_at::<Big>(c),
    )
}

/// [`verify_contradiction`] at one coefficient tier.
fn verify_contradiction_at<C: Tier>(c: &PBConstraintEnum) -> BridgeOutcome {
    let Some(k) = to_kernel::<C>(c) else {
        return Ok(Some("constraint-not-i64-representable"));
    };
    let Ok(n) = normalize(&k) else {
        return Ok(Some("kernel-guard-refused"));
    };
    if n.all_nonneg() && n.coeff_sum() < n.degree.widen() {
        Ok(None)
    } else {
        Err(CheckingError::KernelDivergence(
            "constraint accepted as a contradiction, but the proved kernel judges it satisfiable"
                .to_string(),
        ))
    }
}

/// Kernel-verify a syntactic implication accept: reconstruct `target` from
/// `source` as a chain of proved operations — weaken away variables the
/// target lacks, raise low coefficients with trivial axioms (`l >= 0`),
/// weaken the degree down, saturate, raise once more — and demand the chain
/// lands exactly on the target's proved normal form. Every link is a kernel
/// rule, so success means the implication is derivable, not merely
/// syntactically plausible. Reconstruction failure is a counted skip (the
/// live `implies()` may accept shapes this chain does not cover), never a
/// divergence.
///
/// The two early exits are rule-free, but they check exactly the hypotheses
/// of `VeriPbCore.entails_trivial` and
/// `entails_anything_of_entails_contradicting` on the proved normal forms —
/// no derivation is asserted that the kernel would not license.
pub fn verify_implication(source: &PBConstraintEnum, target: &PBConstraintEnum) -> BridgeOutcome {
    tiered_outcome(
        || verify_implication_at::<kernel::Coeff>(source, target),
        || verify_implication_at::<Big>(source, target),
    )
}

/// [`verify_implication`] at one coefficient tier.
fn verify_implication_at<C: Tier>(
    source: &PBConstraintEnum,
    target: &PBConstraintEnum,
) -> BridgeOutcome {
    let (Some(sk), Some(tk)) = (to_kernel::<C>(source), to_kernel::<C>(target)) else {
        return Ok(Some("constraint-not-i64-representable"));
    };
    verify_implication_kernel(&sk, &tk)
}

/// The kernel-constraint-level core of [`verify_implication`]: same proved
/// chain, for callers whose source/target already live in the kernel
/// representation (the substituted-implication path derives its source by
/// kernel operations and computes its target hint kernel-side).
fn verify_implication_kernel<C: Tier>(
    sk: &kernel::Constraint<C>,
    tk: &kernel::Constraint<C>,
) -> BridgeOutcome {
    let (Ok(mut acc), Ok(t)) = (normalize(sk), normalize(tk)) else {
        return Ok(Some("kernel-guard-refused"));
    };
    let not_reconstructed = Ok(Some("implication-not-reconstructed"));

    // Fast path: a trivially-true target is entailed by anything
    // (`entails_trivial`; normalized coefficients are nonnegative).
    if t.degree <= C::zero() {
        return Ok(None);
    }
    // Fast path: a contradictory source entails everything
    // (`entails_anything_of_entails_contradicting`).
    if acc.coeff_sum() < acc.degree.widen() {
        return Ok(None);
    }

    // 1. Weaken away variables the target does not use with this polarity.
    //
    // All doomed literals are batched into ONE trivial axiom
    // `sum coeff_i * ~l_i >= 0` — still exactly the `DStep.trivS` shape
    // (`AllNonneg`, since `acc` is normalized so every coeff is positive,
    // and degree 0 <= 0) — followed by one add and one normalize. This
    // derives the same constraint the per-literal chain derives: `acc` has
    // at most one term per variable, so the doomed literals are on distinct
    // variables and each `l_i`/`~l_i` pair cancels independently under
    // `normC`, shifting the degree by the same total. The guards agree too:
    // the batched degree walks monotonically between the same two
    // representable endpoints the singleton chain visits, and the cancelled
    // coefficients never need narrowing (they merge to zero and drop).
    let tmap: AHashSet<kernel::Lit> = t.terms.iter().map(|u| u.lit).collect();
    let doomed_terms: Vec<kernel::Term<C>> = acc
        .terms
        .iter()
        .filter(|st| !tmap.contains(&st.lit))
        .map(|st| kernel::Term {
            coeff: st.coeff.clone(),
            lit: st.lit.negate(),
        })
        .collect();
    if !doomed_terms.is_empty() {
        let axiom = kernel::Constraint::new(doomed_terms, C::zero());
        let Ok(sum) = kernel::add(&acc, &axiom) else {
            return Ok(Some("kernel-guard-refused"));
        };
        let Ok(n) = normalize(&sum) else {
            return Ok(Some("kernel-guard-refused"));
        };
        acc = n;
    }

    // 2. Raise coefficients that are below the target's with trivial axioms.
    acc = match raise_to(&acc, &t) {
        Ok(raised) => raised,
        Err(reason) => return Ok(Some(reason)),
    };

    // 3. Weaken the degree down to the target's.
    if acc.degree < t.degree {
        return not_reconstructed;
    }
    if acc.degree > t.degree {
        let Some(gap) = C::narrow(&acc.degree.widen().sub(&t.degree.widen())) else {
            return Ok(Some("kernel-guard-refused"));
        };
        let Ok(w) = kernel::weaken_degree(&acc, gap) else {
            return Ok(Some("kernel-guard-refused"));
        };
        acc = w;
    }

    // 4. Saturate to cap overshooting coefficients (sound only on the
    //    normalized form, which acc is).
    if acc.degree >= C::zero() {
        if let Ok(sat) = kernel::saturate(&acc) {
            acc = sat;
        }
    }

    // 5. Saturation caps coefficients at the degree, so a target with an
    //    un-saturated coefficient is reached by raising back up: run the
    //    step-2 pass once more. This is the pass the previous version of
    //    this function only *asserted* ("one more trivial-axiom pass would
    //    only lower it") behind a hand-written domination predicate; running
    //    it accepts exactly the same landings — a chain result whose every
    //    literal occurs in the target with no larger coefficient, at the same
    //    degree, is precisely what one raise turns into the target — with no
    //    link left that is not a kernel rule.
    acc = match raise_to(&acc, &t) {
        Ok(raised) => raised,
        Err(reason) => return Ok(Some(reason)),
    };

    // 6. The chain must land exactly on the target, up to proved
    //    normalization. A wrong degree, a literal the target does not carry,
    //    or a coefficient the raise could not lift (because the chain
    //    overshot it) all fail here.
    match (canonical(&acc), canonical(&t)) {
        (Some(a), Some(b)) if a == b => Ok(None),
        (Some(_), Some(_)) => not_reconstructed,
        _ => Ok(Some("kernel-guard-refused")),
    }
}

/// One batched "raise the low coefficients" pass of the implication chain:
/// add the trivial axiom `sum_{l in t, have_l < t_l} (t_l - have_l) * l >= 0`
/// and re-normalize; `acc` unchanged when nothing is below the target.
///
/// The axiom is exactly the `DStep.trivS` shape licensed by
/// `VeriPbCore.entails_trivial`: every gap is positive, so it is `AllNonneg`,
/// and its degree is 0. Batching the gaps into one axiom derives what the
/// per-literal chain derives — `t` is normalized, so the raised literals sit
/// on distinct variables and merge independently, each landing on `t_l`,
/// which is representable by construction.
fn raise_to<C: Tier>(
    acc: &kernel::Constraint<C>,
    t: &kernel::Constraint<C>,
) -> Result<kernel::Constraint<C>, &'static str> {
    let amap: AHashMap<kernel::Lit, &C> = acc.terms.iter().map(|u| (u.lit, &u.coeff)).collect();
    let zero = C::zero();
    let mut raise_terms: Vec<kernel::Term<C>> = Vec::new();
    for tt in &t.terms {
        let have = amap.get(&tt.lit).copied().unwrap_or(&zero);
        if *have < tt.coeff {
            // Both are stored coefficients of a normalized constraint, so the
            // gap is between them and lands in the domain; the narrowing is
            // still guarded rather than asserted.
            let gap =
                C::narrow(&tt.coeff.widen().sub(&have.widen())).ok_or("kernel-guard-refused")?;
            raise_terms.push(kernel::Term {
                coeff: gap,
                lit: tt.lit,
            });
        }
    }
    if raise_terms.is_empty() {
        return Ok(acc.clone());
    }
    let axiom = kernel::Constraint::new(raise_terms, C::zero());
    let sum = kernel::add(acc, &axiom).map_err(|_| "kernel-guard-refused")?;
    normalize(&sum).map_err(|_| "kernel-guard-refused")
}

/// Kernel-verify a substituted-implication accept (proofgoal
/// `DBImpliesSubstituted`): the live checker accepted `target` because a
/// database constraint `source`, with both sides simplified under the
/// engine's propagated assignment ρ (the current `trail`), syntactically
/// implies the simplified target. The bridge re-derives that accept from
/// existing kernel machinery only — nothing about the live `substitute()`
/// or `implies()` is trusted.
///
/// The re-derivation, and the theorem licensing each step:
///
/// 1. **The trail's units.** Every trail literal `l` the accept consumes (a
///    ρ-false literal of the source, a ρ-true literal of the target) is
///    certified as a kernel trail certificate via [`rup::check_rup`]:
///    target `1·l >= 1`, whose kernel negation `1·~l >= 1` sits at view
///    index 0 and propagates `~l` as the first step; then the engine-trail
///    *prefix* before `l` replays step by step (slack is monotone under
///    trail extension, so every re-checked `PropTrail.step` hypothesis
///    still holds with `~l` added); `l`'s own reason constraint is the
///    conflict (with `l` falsified, `slackTerms` there equals exactly the
///    `slackWithout` the engine propagated on). Success establishes the
///    hypotheses of `VeriPbCore.entails_of_rup`: the unit is entailed by
///    anything entailing the view. The view holds exactly the trail's
///    reason constraints — database constraints plus the autoproving-set
///    premises (the negated strengthening constraint of a `red`/`dom`
///    step), which are premises of this proofgoal's obligation
///    (`DB ∧ ¬C |= target`) — the same licensing as
///    [`verify_rup_certificate`] gives its reasons.
/// 2. **The substituted source.** `source|ρ` is *derived*, never assumed,
///    from the source's proved normal form: the ρ-true literals `m_i` with
///    coefficients `a_i` are cancelled by one batched trivial axiom
///    `sum a_i·~m_i >= 0` (the `DStep.trivS` shape, licensed by
///    `VeriPbCore.entails_trivial`); each ρ-false literal `m` is cancelled
///    by adding `multiply(a, ~m >= 1)` of its certified unit
///    (`VeriPbCore.entails_multiply` + `VeriPbCore.entails_add`); every add
///    is followed by proved normalization, an equivalence
///    (`VeriPbCore.holds_normC_of_holds` / `holds_of_holds_normC`).
/// 3. **The residual implication.** The substituted target is computed
///    kernel-side (drop ρ-assigned terms; a ρ-true term also lowers the
///    degree by its coefficient) purely as a *hint*: the
///    [`verify_implication`] chain re-derives it from the derived
///    `source|ρ` through proved rules, so its entailment never rests on
///    that computation.
/// 4. **The target itself.** From the hint, each ρ-true target literal is
///    restored by adding its certified unit scaled by its coefficient, and
///    the ρ-false target literals by one batched trivial axiom; the result
///    must equal the target's proved normal form up to term order
///    (`VeriPbCore.entails_of_normC_eq`). This inverts step 3's bookkeeping
///    exactly, so a mismatch means the bridge failed to justify the accept,
///    never that the accept is wrong — a counted skip.
///
/// An empty trail degenerates to the plain [`verify_implication`] chain.
/// Anything outside the certified shape stays a counted skip — an
/// `Assumption` reason on the trail (ρ would rest on unproved premises),
/// unrepresentable constraints or variables (ρ would be modelled
/// incompletely), guard refusals, an implication the proved chain cannot
/// reconstruct. A trail step or conflict the kernel *rejects* is a
/// [`CheckingError::KernelDivergence`]: the engine and the kernel disagree
/// about propagation itself.
pub fn verify_substituted_implication(
    source: &PBConstraintEnum,
    target: &PBConstraintEnum,
    trail: &LiveTrail,
) -> BridgeOutcome {
    tiered_outcome(
        || verify_substituted_implication_at::<kernel::Coeff>(source, target, trail),
        || verify_substituted_implication_at::<Big>(source, target, trail),
    )
}

/// [`verify_substituted_implication`] at one coefficient tier.
fn verify_substituted_implication_at<C: Tier>(
    source: &PBConstraintEnum,
    target: &PBConstraintEnum,
    trail: &LiveTrail,
) -> BridgeOutcome {
    /// Certify `premises |= (1·l >= 1)` for trail literal `l`: negated unit
    /// at view index 0, engine-trail prefix before `l` as steps, `l`'s own
    /// reason as the conflict (step 1 of the module plan above).
    fn certify_unit<C: Tier>(
        l: kernel::Lit,
        on_trail: &AHashMap<kernel::Lit, (usize, usize)>,
        engine_steps: &[(usize, kernel::Lit)],
        view: &[&kernel::Constraint<C>],
        certified: &mut AHashSet<kernel::Lit>,
    ) -> BridgeOutcome {
        if certified.contains(&l) {
            return Ok(None);
        }
        let Some(&(pos, slot)) = on_trail.get(&l) else {
            // ρ assigns exactly the trail literals, so a consumed literal
            // that is off the trail cannot be certified from it.
            return Ok(Some("substituted-implication-not-reconstructed"));
        };
        let unit = kernel::Constraint::new(
            vec![kernel::Term {
                coeff: C::one(),
                lit: l,
            }],
            C::one(),
        );
        let mut steps = Vec::with_capacity(pos + 1);
        steps.push((0, l.negate()));
        steps.extend_from_slice(&engine_steps[..pos]);
        match rup::check_rup(&unit, view, &steps, slot) {
            Ok(()) => {
                certified.insert(l);
                Ok(None)
            }
            Err(rup::RupError::NegationOverflow(_)) => Ok(Some("kernel-guard-refused")),
            Err(e) => Err(CheckingError::KernelDivergence(format!(
                "substituted-implication trail unit {:?} rejected by the proved kernel: {:?}",
                l, e
            ))),
        }
    }

    let (Some(sk), Some(tk)) = (to_kernel::<C>(source), to_kernel::<C>(target)) else {
        return Ok(Some("constraint-not-i64-representable"));
    };
    let (Ok(s), Ok(t)) = (normalize(&sk), normalize(&tk)) else {
        return Ok(Some("kernel-guard-refused"));
    };

    // Convert the engine trail: each propagation becomes a replayable step
    // (reason view slot, literal), and `on_trail` records position + reason
    // slot per literal — the kernel-side image of ρ. Any entry the kernel
    // cannot represent poisons the whole verification (ρ would be modelled
    // incompletely), so it is a counted skip. As in [`verify_rup_certificate`],
    // keying the slot map by constraint address is sound because `trail`
    // holds an `Rc` clone of every reason for the whole call.
    let mut owned: Vec<kernel::Constraint<C>> = Vec::new();
    let mut slots: AHashMap<*const DBConstraint, usize> = AHashMap::new();
    let mut engine_steps: Vec<(usize, kernel::Lit)> = Vec::new();
    let mut on_trail: AHashMap<kernel::Lit, (usize, usize)> = AHashMap::new();
    for (pos, propagation) in trail.trail.iter().enumerate() {
        let rc = match &propagation.reason {
            Reason::Assumption => {
                return Ok(Some("substituted-implication-under-assumptions"));
            }
            Reason::Constraint(rc) => rc,
        };
        let Some(l) = kernel_lit(&propagation.lit) else {
            return Ok(Some("variable-index-too-wide"));
        };
        let p = Rc::as_ptr(rc);
        let slot = match slots.get(&p) {
            Some(&i) => i,
            None => {
                let Some(k) = to_kernel::<C>(&rc.constraint) else {
                    return Ok(Some("constraint-not-i64-representable"));
                };
                owned.push(k);
                slots.insert(p, owned.len());
                owned.len()
            }
        };
        engine_steps.push((slot, l));
        on_trail.insert(l, (pos, slot));
    }
    let view: Vec<&kernel::Constraint<C>> = owned.iter().collect();
    let mut certified: AHashSet<kernel::Lit> = AHashSet::new();

    let rho_true = |l: kernel::Lit| on_trail.contains_key(&l);
    let rho_false = |l: kernel::Lit| on_trail.contains_key(&l.negate());

    // Step 2: derive source|ρ from the source's proved normal form. Both
    // term classes are collected up front (a normalized constraint has at
    // most one term per variable, so the classes are disjoint).
    let doomed: Vec<kernel::Term<C>> = s
        .terms
        .iter()
        .filter(|st| rho_true(st.lit))
        .map(|st| kernel::Term {
            coeff: st.coeff.clone(),
            lit: st.lit.negate(),
        })
        .collect();
    let cancelled: Vec<kernel::Term<C>> = s
        .terms
        .iter()
        .filter(|st| rho_false(st.lit))
        .cloned()
        .collect();
    let mut acc = s;
    if !doomed.is_empty() {
        let axiom = kernel::Constraint::new(doomed, C::zero());
        let Ok(sum) = kernel::add(&acc, &axiom) else {
            return Ok(Some("kernel-guard-refused"));
        };
        let Ok(n) = normalize(&sum) else {
            return Ok(Some("kernel-guard-refused"));
        };
        acc = n;
    }
    for st in cancelled {
        match certify_unit(
            st.lit.negate(),
            &on_trail,
            &engine_steps,
            &view,
            &mut certified,
        ) {
            Ok(None) => {}
            other => return other,
        }
        let unit = kernel::Constraint::new(
            vec![kernel::Term {
                coeff: C::one(),
                lit: st.lit.negate(),
            }],
            C::one(),
        );
        let Ok(scaled) = kernel::multiply(st.coeff, &unit) else {
            return Ok(Some("kernel-guard-refused"));
        };
        let Ok(sum) = kernel::add(&acc, &scaled) else {
            return Ok(Some("kernel-guard-refused"));
        };
        let Ok(n) = normalize(&sum) else {
            return Ok(Some("kernel-guard-refused"));
        };
        acc = n;
    }

    // Step 3: the substituted target, computed kernel-side as a hint whose
    // entailment the proved implication chain itself establishes.
    let mut hint_terms: Vec<kernel::Term<C>> = Vec::new();
    let mut hint_degree = t.degree.widen();
    for tt in &t.terms {
        if rho_true(tt.lit) {
            hint_degree = hint_degree.sub(&tt.coeff.widen());
        } else if !rho_false(tt.lit) {
            hint_terms.push(tt.clone());
        }
    }
    let Some(hint_degree) = C::narrow(&hint_degree) else {
        return Ok(Some("kernel-guard-refused"));
    };
    let hint = kernel::Constraint::new(hint_terms, hint_degree);
    match verify_implication_kernel(&acc, &hint) {
        Ok(None) => {}
        Ok(Some("implication-not-reconstructed")) => {
            return Ok(Some("substituted-implication-not-reconstructed"));
        }
        other => return other,
    }

    // Step 4: reconstruct the target from the hint plus the certified
    // units and one batched trivial axiom.
    let restored: Vec<kernel::Term<C>> = t
        .terms
        .iter()
        .filter(|tt| rho_true(tt.lit))
        .cloned()
        .collect();
    let missing: Vec<kernel::Term<C>> = t
        .terms
        .iter()
        .filter(|tt| rho_false(tt.lit))
        .cloned()
        .collect();
    let Ok(mut recon) = normalize(&hint) else {
        return Ok(Some("kernel-guard-refused"));
    };
    for tt in restored {
        match certify_unit(tt.lit, &on_trail, &engine_steps, &view, &mut certified) {
            Ok(None) => {}
            other => return other,
        }
        let unit = kernel::Constraint::new(
            vec![kernel::Term {
                coeff: C::one(),
                lit: tt.lit,
            }],
            C::one(),
        );
        let Ok(scaled) = kernel::multiply(tt.coeff, &unit) else {
            return Ok(Some("kernel-guard-refused"));
        };
        let Ok(sum) = kernel::add(&recon, &scaled) else {
            return Ok(Some("kernel-guard-refused"));
        };
        let Ok(n) = normalize(&sum) else {
            return Ok(Some("kernel-guard-refused"));
        };
        recon = n;
    }
    if !missing.is_empty() {
        let axiom = kernel::Constraint::new(missing, C::zero());
        let Ok(sum) = kernel::add(&recon, &axiom) else {
            return Ok(Some("kernel-guard-refused"));
        };
        let Ok(n) = normalize(&sum) else {
            return Ok(Some("kernel-guard-refused"));
        };
        recon = n;
    }

    // The reconstruction must land exactly on the target's proved normal
    // form (both sides are `normC` fixpoints, so sorting is the whole
    // comparison). A mismatch means the bridge could not justify the
    // accept — a counted skip, never a forced verdict.
    if sort_canon(&recon) == sort_canon(&t) {
        Ok(None)
    } else {
        Ok(Some("substituted-implication-not-reconstructed"))
    }
}

/// Re-judge a mid-proof logged solution (`sol`/`soli`) against the same
/// database constraints the live check consulted.
pub fn verify_db_solution(
    database: &Database,
    assignment: &Assignment<BooleanVar>,
) -> BridgeOutcome {
    tiered_outcome(
        || verify_db_solution_at::<kernel::Coeff>(database, assignment),
        || verify_db_solution_at::<Big>(database, assignment),
    )
}

/// [`verify_db_solution`] at one coefficient tier.
fn verify_db_solution_at<C: Tier>(
    database: &Database,
    assignment: &Assignment<BooleanVar>,
) -> BridgeOutcome {
    let a =
        |v: u32| -> bool { matches!(assignment.get_value(v as usize), BoolValue::Assigned(true)) };
    for c in database.unique_constraints.iter() {
        let Some(k) = to_kernel::<C>(&c.constraint) else {
            return Ok(Some("constraint-not-i64-representable"));
        };
        if !k.holds(&a) {
            return Err(CheckingError::KernelDivergence(
                "logged solution accepted by the checker, but the proved kernel evaluates a database constraint to false under it".to_string(),
            ));
        }
    }
    Ok(None)
}

/// Re-judge an accepted solution through the kernel semantics
/// (`holdsAllB`): every original constraint must hold under the assignment.
pub fn verify_solution(
    constraints: &[PBConstraintEnum],
    assignment: &Assignment<BooleanVar>,
) -> BridgeOutcome {
    tiered_outcome(
        || verify_solution_at::<kernel::Coeff>(constraints, assignment),
        || verify_solution_at::<Big>(constraints, assignment),
    )
}

/// [`verify_solution`] at one coefficient tier.
fn verify_solution_at<C: Tier>(
    constraints: &[PBConstraintEnum],
    assignment: &Assignment<BooleanVar>,
) -> BridgeOutcome {
    let a =
        |v: u32| -> bool { matches!(assignment.get_value(v as usize), BoolValue::Assigned(true)) };
    for c in constraints {
        let Some(k) = to_kernel::<C>(c) else {
            return Ok(Some("constraint-not-i64-representable"));
        };
        if !k.holds(&a) {
            return Err(CheckingError::KernelDivergence(
                "solution accepted by the checker, but the proved kernel evaluates a constraint to false under it".to_string(),
            ));
        }
    }
    Ok(None)
}
