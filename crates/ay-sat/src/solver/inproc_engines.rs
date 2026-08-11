// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Inprocessing engine sub-struct for hot/cold field separation (#5090).
//!
//! Groups cold inprocessing engine instances into a single struct so the
//! Solver's hot BCP fields are not intermixed with cold engine state.
//! All fields are accessed only during inprocessing rounds, not during
//! BCP or conflict analysis.

use crate::bce::BCE;
use crate::bve::BVE;
use crate::cce::Cce;
use crate::condition::Conditioning;
use crate::congruence::CongruenceClosure;
use crate::decompose::Decompose;
use crate::factor::Factor;
use crate::gates::GateExtractor;
#[cfg(feature = "gpu")]
use crate::gpu::bve::GpuBvePipeline;
#[cfg(feature = "gpu")]
use crate::gpu::GpuContext;
use crate::htr::HTR;
use crate::kitten::Kitten;
use crate::preprocess_transaction::PreprocessTransactionLedger;
use crate::reconstruct::ReconstructionStack;
use crate::sbva::Sbva;
use crate::subsume::Subsumer;
use crate::sweep::Sweeper;
use crate::transred::TransRed;
use crate::vivify::Vivifier;

/// Cold inprocessing engine state, separated from the Solver's hot BCP fields.
///
/// These fields are only accessed during inprocessing/preprocessing rounds.
/// Grouping them reduces cognitive overhead (Solver has ~140 fields) and
/// provides a clear hot/cold boundary for cache analysis.
///
/// Reference: CaDiCaL groups these as separate subsystem objects; AY's flat
/// struct intermixed them with BCP state, polluting field adjacency analysis.
pub(crate) struct InprocessingEngines {
    /// Vivification engine
    pub vivifier: Vivifier,
    /// Subsumption engine
    pub subsumer: Subsumer,
    /// Failed literal prober
    pub prober: crate::probe::Prober,
    /// Bounded Variable Elimination
    pub bve: BVE,
    /// Blocked Clause Elimination
    pub bce: BCE,
    /// Covered Clause Elimination (ACCE)
    pub cce: Cce,
    /// Conditioning (Globally Blocked Clause Elimination)
    pub conditioning: Conditioning,
    /// Decompose (SCC-based Equivalent Literal Substitution)
    pub decompose_engine: Decompose,
    /// Factorization (CaDiCaL factor.cpp)
    pub factor_engine: Factor,
    /// Structured BVA (Manthey 2023)
    pub sbva_engine: Sbva,
    /// Transitive Reduction
    pub transred_engine: TransRed,
    /// Hyper-Ternary Resolution
    pub htr: HTR,
    /// Gate Extraction
    pub gate_extractor: GateExtractor,
    /// Congruence Closure (gate-based equivalence detection)
    pub congruence: CongruenceClosure,
    /// SAT Sweeping
    pub sweeper: Sweeper,
    /// Dedicated kitten instance for BVE definition extraction.
    pub definition_kitten: Kitten,
    /// Model Reconstruction
    pub reconstruction: ReconstructionStack,
    /// Execution-path preprocessing transaction ledger.
    pub preprocess_transactions: PreprocessTransactionLedger,
    // ══════════════════════════════════════════════════════════════════════
    // GPU: lazily-initialized compute accelerators (behind feature gate)
    // ══════════════════════════════════════════════════════════════════════
    /// Lazily-initialized GPU context shared across all GPU-accelerated passes.
    /// `None` until first GPU dispatch attempt; stays `None` if no adapter.
    #[cfg(feature = "gpu")]
    pub gpu_context: Option<GpuContext>,
    /// Cached GPU BVE pipeline (shader + bind group layout compiled once,
    /// against `gpu_context`'s device).
    /// `None` until first BVE GPU dispatch; stays `None` if GPU unavailable.
    #[cfg(feature = "gpu")]
    pub gpu_bve_pipeline: Option<GpuBvePipeline>,
    /// Whether GPU initialization was already attempted (prevents retrying
    /// on every inprocessing round after a failed adapter probe).
    #[cfg(feature = "gpu")]
    pub gpu_init_attempted: bool,
    /// Whether BVE pipeline compilation was already attempted (prevents
    /// re-compiling the shader on every BVE candidate after a failure).
    #[cfg(feature = "gpu")]
    pub gpu_bve_pipeline_attempted: bool,
}

impl InprocessingEngines {
    /// Create all inprocessing engines for `num_vars` variables.
    pub(crate) fn new(num_vars: usize) -> Self {
        // `AY_SAT_MEM_PROBE=1`: per-engine construction footprint. This
        // constructor is 685 of the ~849 resident bytes per variable AY commits
        // before reading a clause, so the breakdown decides what to make lazy.
        if std::env::var_os("AY_SAT_MEM_PROBE").is_some() {
            let mut last = ay_sys::current_footprint_bytes();
            macro_rules! probe {
                ($label:literal, $e:expr) => {{
                    let v = $e;
                    let now = ay_sys::current_footprint_bytes();
                    let d = now.saturating_sub(last);
                    eprintln!(
                        "c mem_probe   engine {:<20} {:>9.1} MB {:>7.1} B/var",
                        $label,
                        d as f64 / 1e6,
                        d as f64 / num_vars.max(1) as f64
                    );
                    last = now;
                    v
                }};
            }
            let probes = (
                probe!("subsumer", Subsumer::new(num_vars)),
                probe!("prober", crate::probe::Prober::new(num_vars)),
                probe!("bve", BVE::new(num_vars)),
                probe!("bce", BCE::new(num_vars)),
                probe!("cce", Cce::new(num_vars)),
                probe!("conditioning", Conditioning::new(num_vars)),
                probe!("decompose", Decompose::new(num_vars)),
                probe!("factor", Factor::new(num_vars)),
                probe!("sbva", Sbva::new(num_vars)),
                probe!("transred", TransRed::new(num_vars)),
                probe!("htr", HTR::new(num_vars)),
                probe!("gate_extractor", GateExtractor::new(num_vars)),
            );
            let more = (
                probe!("congruence", CongruenceClosure::new(num_vars)),
                probe!("sweeper", Sweeper::new(num_vars)),
            );
            drop((probes, more));
        }
        let mut definition_kitten = Kitten::new();
        definition_kitten.enable_antecedent_tracking();
        Self {
            vivifier: Vivifier::new(),
            subsumer: Subsumer::new(num_vars),
            prober: crate::probe::Prober::new(num_vars),
            bve: BVE::new(num_vars),
            bce: BCE::new(num_vars),
            cce: Cce::new(num_vars),
            conditioning: Conditioning::new(num_vars),
            decompose_engine: Decompose::new(num_vars),
            factor_engine: Factor::new(num_vars),
            sbva_engine: Sbva::new(num_vars),
            transred_engine: TransRed::new(num_vars),
            htr: HTR::new(num_vars),
            gate_extractor: GateExtractor::new(num_vars),
            congruence: CongruenceClosure::new(num_vars),
            sweeper: Sweeper::new(num_vars),
            definition_kitten,
            reconstruction: ReconstructionStack::new(),
            preprocess_transactions: PreprocessTransactionLedger::new(),
            #[cfg(feature = "gpu")]
            gpu_context: None,
            #[cfg(feature = "gpu")]
            gpu_bve_pipeline: None,
            #[cfg(feature = "gpu")]
            gpu_init_attempted: false,
            #[cfg(feature = "gpu")]
            gpu_bve_pipeline_attempted: false,
        }
    }

    /// Lazily initialize the GPU context on first use.
    ///
    /// Returns `Some(&GpuContext)` if a GPU adapter is available, `None` otherwise.
    /// After the first attempt (success or failure), subsequent calls return the
    /// cached result without retrying. This amortizes the wgpu adapter probe cost
    /// and avoids repeated error logging on headless systems.
    #[cfg(feature = "gpu")]
    pub(crate) fn gpu_context(&mut self) -> Option<&GpuContext> {
        if !self.gpu_init_attempted {
            self.gpu_init_attempted = true;
            match GpuContext::initialize() {
                Ok(ctx) => {
                    tracing::info!(
                        backend = ?ctx.backend(),
                        adapter = ?ctx.adapter_info().name,
                        "GPU context initialized for inprocessing acceleration"
                    );
                    self.gpu_context = Some(ctx);
                }
                Err(err) => {
                    tracing::debug!("GPU initialization failed (falling back to CPU): {err}");
                }
            }
        }
        self.gpu_context.as_ref()
    }

    /// Lazily initialize the GPU context and BVE pipeline on first use.
    ///
    /// Returns the shared context together with the pipeline compiled
    /// against it (`dispatch_resolve` requires both). Returns `None` when
    /// no GPU adapter is available or pipeline compilation failed; each of
    /// those is attempted at most once per solver.
    #[cfg(feature = "gpu")]
    pub(crate) fn gpu_bve(&mut self) -> Option<(&GpuContext, &GpuBvePipeline)> {
        if !self.gpu_init_attempted {
            let _ = self.gpu_context();
        }
        if !self.gpu_bve_pipeline_attempted {
            self.gpu_bve_pipeline_attempted = true;
            if let Some(context) = self.gpu_context.as_ref() {
                self.gpu_bve_pipeline = GpuBvePipeline::try_new(context);
                if self.gpu_bve_pipeline.is_some() {
                    tracing::info!("GPU BVE pipeline initialized");
                }
            }
        }
        match (self.gpu_context.as_ref(), self.gpu_bve_pipeline.as_ref()) {
            (Some(context), Some(pipeline)) => Some((context, pipeline)),
            _ => None,
        }
    }

    /// Reset all engine-internal watermarks to their initial values.
    ///
    /// MUST be called when `search_ticks` or `num_propagations` is reset
    /// (i.e., in `reset_search_state()`). Without this, the `saturating_sub`
    /// effort computation in each engine yields 0 until the tick/propagation
    /// counter re-accumulates past the stale watermark — starving the
    /// technique of budget for the entire second solve (#8159).
    ///
    /// Centralizes the reset so future engine authors have a single place
    /// to add their watermark reset line.
    pub(crate) fn reset_watermarks(&mut self) {
        self.prober.set_last_search_ticks(0);
        // HTR uses Option<u64>: None means "first call uses INIT budget".
        // Resetting to None (not Some(0)) preserves first-call behavior.
        self.htr.reset_last_search_ticks();
        self.transred_engine.set_last_propagations(0);
    }

    /// Resize all engines to accommodate `num_vars` variables.
    pub(crate) fn ensure_num_vars(&mut self, num_vars: usize) {
        self.subsumer.ensure_num_vars(num_vars);
        self.prober.ensure_num_vars(num_vars);
        self.bve.ensure_num_vars(num_vars);
        self.bce.ensure_num_vars(num_vars);
        self.cce.ensure_num_vars(num_vars);
        self.decompose_engine.ensure_num_vars(num_vars);
        self.factor_engine.ensure_num_vars(num_vars);
        self.sbva_engine.ensure_num_vars(num_vars);
        self.transred_engine.ensure_num_vars(num_vars);
        self.htr.ensure_num_vars(num_vars);
        self.gate_extractor.ensure_num_vars(num_vars);
        self.congruence.ensure_num_vars(num_vars);
        self.sweeper.ensure_num_vars(num_vars);
        self.conditioning.ensure_num_vars(num_vars);
    }
}
