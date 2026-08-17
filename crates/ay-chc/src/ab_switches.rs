// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Engine A/B switches, set ONCE by the frontend before any solve.
//!
//! B15 of the env-flag retirement: these were `AY_CHC_*`/`AY_DT_*` env vars
//! nothing set. Every switch guards a SOUND alternative path (each site's
//! comment carries the argument); disabling is for A/B measurement and
//! bisection, never correctness. Same set-once shape as
//! `ay_pb_core::ab_switches` — the sites are free functions across six
//! modules, and threading a config there is churn without benefit for
//! process-constant switches.

use std::sync::OnceLock;

/// The switch set. Every field defaults to ON (the shipped engine).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ChcAbSwitches {
    /// Derivation expansion in clause inlining.
    pub deriv_expansion: bool,
    /// Early direct safety check at PDR startup convergence.
    pub early_safety_check: bool,
    /// Ground-derivation witness solve.
    pub ground_witness: bool,
    /// Disequality-swap lemma refinement.
    pub diseq_swap: bool,
    /// Forward-simulation init-sample fix (bounded extra init states).
    pub fwdsim_fix: bool,
    /// Guarded implication hints for Houdini.
    pub guarded_impl_hints: bool,
    /// Houdini phase-B fast dropping.
    pub houdini_phaseb_fast: bool,
    /// Datatype-BMC intermediate-definition elimination.
    pub dt_bmc_elim: bool,
    /// Bit-blast dynamic abort (B27).
    pub bitblast_dynamic_abort: bool,
    /// BMC multi-predicate transition system (B27).
    pub bmc_multipred_ts: bool,
    /// BMC incremental transition system (B27).
    pub bmc_ts_incremental: bool,
    /// Array store-forwarding transform (B27).
    pub array_store_forwarding: bool,
    /// Catamorphism element abstraction (B27).
    pub cata_elements: bool,
    /// Ground-derivation backtranslation (B27).
    pub ground_backtranslation: bool,
    /// Ground-table read concretization (B27).
    pub ground_table_concretization: bool,
    /// Houdini BV lane (B27).
    pub houdini_bv: bool,
    /// Predicate-component split transform (B27).
    pub pc_split: bool,
    /// Symmetric-split transform (B27).
    pub split_sym: bool,
    /// Word-to-BV transform (B27).
    pub word_bv: bool,
    /// PDR may-POB route (B27).
    pub may_pob: bool,
    /// Executor decision-variable retry (B27).
    pub exec_dv_retry: bool,
    /// Executor unknown-memo (B27).
    pub exec_unknown_memo: bool,
    /// Frontend probe clamp (B27).
    pub front_probe_clamp: bool,
    /// Graph collapse preprocessing (B27).
    pub graph_collapse: bool,
    /// Houdini disjunctive pool (B27).
    pub houdini_disjunctive: bool,
    /// Houdini stage-5 widening classes (B27).
    pub houdini_stage5: bool,
    /// IMC proof-backed interpolants (B27).
    pub imc_proof_itp: bool,
    /// PDR lemma sanitization (B27).
    pub pdr_lemma_sanitize: bool,
    /// TPA fixpoint check (B27; the env was an opt-out spelled `=1`).
    pub tpa_fixpoint: bool,
    /// Array branch of relational-equality Houdini (B33; the env opt-out was
    /// spelled `=1`). Disabling it also disables the v2 templates.
    pub array_relational: bool,
    /// Richer v2 relational templates (affine alignment + select couplings)
    /// layered under the lane above (B33).
    pub array_relational_v2: bool,
    /// Bounded datatype-aware BMC refutation (B33).
    pub dt_bmc: bool,
    /// Qualifier-mining pass (B33).
    pub qual_mine: bool,
    /// Mixed control∨data CNF qualifier class (B33).
    pub qual_mixed: bool,
    /// Catamorphism abstraction route (B54; was the `AY_CHC_DISABLE_CATA`
    /// kill switch).
    pub cata_route: bool,
    /// CATA v2 relational abstraction (B54).
    pub cata_v2: bool,
    /// Condense superpass (B54).
    pub condense: bool,
}

impl Default for ChcAbSwitches {
    fn default() -> Self {
        Self {
            deriv_expansion: true,
            early_safety_check: true,
            ground_witness: true,
            diseq_swap: true,
            fwdsim_fix: true,
            guarded_impl_hints: true,
            houdini_phaseb_fast: true,
            dt_bmc_elim: true,
            bitblast_dynamic_abort: true,
            bmc_multipred_ts: true,
            bmc_ts_incremental: true,
            array_store_forwarding: true,
            cata_elements: true,
            ground_backtranslation: true,
            ground_table_concretization: true,
            houdini_bv: true,
            pc_split: true,
            split_sym: true,
            word_bv: true,
            may_pob: true,
            exec_dv_retry: true,
            exec_unknown_memo: true,
            front_probe_clamp: true,
            graph_collapse: true,
            houdini_disjunctive: true,
            houdini_stage5: true,
            imc_proof_itp: true,
            pdr_lemma_sanitize: true,
            tpa_fixpoint: true,
            array_relational: true,
            array_relational_v2: true,
            dt_bmc: true,
            qual_mine: true,
            qual_mixed: true,
            cata_route: true,
            cata_v2: true,
            condense: true,
        }
    }
}

static SWITCHES: OnceLock<ChcAbSwitches> = OnceLock::new();

/// Install the switch set. First caller wins.
///
/// # Errors
///
/// The rejected `switches` when a set was already installed.
pub fn set(switches: ChcAbSwitches) -> Result<(), ChcAbSwitches> {
    SWITCHES.set(switches).map_err(|_| switches)
}

/// The installed switch set, or the all-on default.
#[must_use]
pub fn get() -> ChcAbSwitches {
    #[cfg(test)]
    if let Some(overridden) = TEST_OVERRIDE.with(std::cell::Cell::get) {
        return overridden;
    }
    SWITCHES.get().copied().unwrap_or_default()
}

#[cfg(test)]
thread_local! {
    /// In-process per-test override (B33; same seam as
    /// `ay_pb_core::ab_switches`): the set-once global cannot be flipped
    /// inside one test binary, so A/B tests scope an override through
    /// [`TestOverride`] — the seam the retired `ScopedEnvVar` steering used
    /// to provide.
    static TEST_OVERRIDE: std::cell::Cell<Option<ChcAbSwitches>> =
        const { std::cell::Cell::new(None) };
}

/// RAII scope for a test's switch override; restores the previous value
/// (usually `None`) on drop.
#[cfg(test)]
pub(crate) struct TestOverride(Option<ChcAbSwitches>);

#[cfg(test)]
impl TestOverride {
    pub(crate) fn set(switches: ChcAbSwitches) -> Self {
        let prev = TEST_OVERRIDE.with(|c| c.replace(Some(switches)));
        TestOverride(prev)
    }
}

#[cfg(test)]
impl Drop for TestOverride {
    fn drop(&mut self) {
        let prev = self.0;
        TEST_OVERRIDE.with(|c| c.set(prev));
    }
}
