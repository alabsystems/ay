// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The problem-scoped Alethe export, and the one place its document and the
//! external-recheck surface verdict of that document (owner decision D7) are
//! produced together.
//!
//! The export renders with one of two override tables — the source-syntax
//! table with the invented datatype-field renderings merged in
//! (`proof_export_term_overrides`), or a sealed finite-enum proof's own
//! table. A surface verdict scanned on any other table describes a different
//! rendering: measured on a datatype constant spelled `|a\|b|` beside an
//! unrelated integer refutation, the source-syntax table alone reads
//! `Supported` while the table the document is rendered with reads
//! `Unsupported` for the field rendering `(fst |a\|b|)`. So the verdict a
//! consumer checks the document against is computed here, by the same call,
//! on the same proof and the same table object handed to the printer.

use ay_core::kani_compat::DetHashMap;
use ay_core::{Proof, TermId};
use ay_proof::{AlethePrintError, AletheStreamError, CarcaraSurface};

use super::{Executor, DEFAULT_ALETHE_EMISSION_WORK_BUDGET, MAX_FINITE_ENUM_RENDER_WORK};

impl Executor {
    /// Select the Carcara dialect every Alethe document this executor renders
    /// is spelled for: `(get-proof)`, the problem-scoped exports, and the
    /// canonical rescue. The default is [`ay_proof::AletheDialect::Clean`];
    /// [`ay_proof::AletheDialect::PinnedCarcara`] prints the spelling pinned
    /// Carcara 9a352ee accepts wherever one exists. Kept across `(reset)`.
    pub fn set_alethe_dialect(&mut self, dialect: ay_proof::AletheDialect) {
        self.alethe_dialect = dialect;
    }

    /// The dialect selected by [`Self::set_alethe_dialect`].
    #[must_use]
    pub fn alethe_dialect(&self) -> ay_proof::AletheDialect {
        self.alethe_dialect
    }

    /// Run `render` with this executor's dialect selected. Every export entry
    /// point goes through here; the printer reads the selection per thread.
    pub(in crate::executor) fn in_alethe_dialect<R>(&self, render: impl FnOnce() -> R) -> R {
        ay_proof::with_alethe_dialect(self.alethe_dialect, render)
    }

    /// Export the last proof through the same problem-scoped Alethe path used by
    /// `(get-proof)`.
    ///
    /// File-backed SMT proof output must not emit declarations for symbols that
    /// are already declared by the SMT-LIB problem. External checkers such as
    /// Carcara read the problem file separately and expect the proof file to
    /// contain only proof commands.
    ///
    /// A consumer that hands this document to an external checker, and so must
    /// read its external-recheck surface first (D7), calls
    /// [`Self::try_export_last_proof_alethe_for_problem_scope_with_carcara_surface`]
    /// instead, which returns this exact document with that verdict.
    #[must_use]
    pub fn try_export_last_proof_alethe_for_problem_scope(
        &self,
    ) -> Option<Result<String, AlethePrintError>> {
        self.render_last_proof_alethe_for_problem_scope(|document, _, _| document)
    }

    /// [`Self::try_export_last_proof_alethe_for_problem_scope`] together with
    /// the external-recheck surface verdict (owner decision D7, 2026-09-22) of
    /// the document it returns.
    ///
    /// The verdict is computed in the same call, on the same proof and the
    /// same override table object the printer rendered the document with —
    /// the verdict `UnsatProofArtifact::carcara_surface` discloses for the
    /// same document. Like that verdict it covers the problem's own
    /// declarations as well ([`Self::problem_and_proof_surface`]): the checker
    /// is handed the problem beside this document and parses both. It also
    /// covers what the render printed: a document that keeps a spelling only
    /// Clean's vendored Carcara accepts is [`CarcaraSurface::CleanDialect`]
    /// (`ay_proof::AletheDialect`), and one that eliminates a problem `let`
    /// with `:rule let` is [`CarcaraSurface::WithoutLetExpansion`], never
    /// `Supported`. This is
    /// the read for any consumer that CLAIMS an external Carcara check of the
    /// problem-scoped document: refuse anything but
    /// [`CarcaraSurface::Supported`] with the disclosed reason before invoking
    /// the checker, and treat a variant this build does not know as
    /// unsupported (`CarcaraSurface` is `#[non_exhaustive]`).
    ///
    /// [`Self::last_unsat_proof_carcara_surface`] is this verdict without the
    /// bytes; a consumer that hands the document on reads both here, from one
    /// rendering.
    ///
    /// `None` and `Some(Err(_))` exactly when the plain export returns them;
    /// no verdict is reported for a document that was not rendered.
    #[must_use]
    pub fn try_export_last_proof_alethe_for_problem_scope_with_carcara_surface(
        &self,
    ) -> Option<Result<(String, CarcaraSurface), AlethePrintError>> {
        // The dialect report describes exactly the bytes returned.
        let (rendered, dialect) = ay_proof::capture_alethe_dialect_report(|| {
            self.render_last_proof_alethe_for_problem_scope(|document, proof, overrides| {
                let surface = self.problem_and_proof_surface(proof, overrides);
                (document, surface)
            })
        });
        rendered.map(|rendered| {
            rendered.map(|(document, surface)| (document, surface.with_dialect_report(&dialect)))
        })
    }

    /// The external-recheck surface verdict (D7) of the document
    /// [`Self::try_export_last_proof_alethe_for_problem_scope`] renders: the
    /// verdict of [`Self::try_export_last_proof_alethe_for_problem_scope_with_carcara_surface`],
    /// whose document this call renders and drops. So a document that keeps a
    /// spelling only Clean's vendored Carcara checks is
    /// [`CarcaraSurface::CleanDialect`], and one that eliminates the problem's
    /// own `let` with `:rule let` is [`CarcaraSurface::WithoutLetExpansion`],
    /// never `Supported`.
    ///
    /// REGRESSION (6835fec57 made the artifact and the paired export say what
    /// the render printed, and left this reader scanning sorts and symbols):
    /// it read `Supported` for the UMULL `zero_extend` twin of
    /// `tests/bv_frontier_source.rs`, whose document checks `zero_extend` as
    /// `concat` and which pinned Carcara 9a352ee refuses, and for a document
    /// eliminating a problem `let`, which it refuses under
    /// `--expand-let-bindings`.
    ///
    /// Owner decision D7 (2026-09-22): the surface is DISCLOSED, never a
    /// reason to withhold the document; only a consumer that CLAIMS an
    /// external check refuses anything but `Supported`, with its reason.
    ///
    /// Each call renders the whole document (inside its own
    /// [`ay_proof::capture_alethe_dialect_report`], which also reports to an
    /// enclosing capture); a consumer that hands the document on reads both
    /// from the paired export once. `None` exactly when that export renders
    /// no document (no retained UNSAT proof, no proof output requested, a
    /// suppressed reconstruction, an unauthenticated Alethe surface, a render
    /// error or exhausted budget). The strict gates' own parse verdict is not
    /// public: it does not render.
    #[must_use]
    pub fn last_unsat_proof_carcara_surface(&self) -> Option<CarcaraSurface> {
        self.try_export_last_proof_alethe_for_problem_scope_with_carcara_surface()?
            .ok()
            .map(|(_, surface)| surface)
    }

    /// [`Self::try_export_last_proof_alethe_for_problem_scope_to`] together
    /// with the verdict the CLI's `c ay.proof.certificate` line discloses for
    /// exactly the bytes it streamed into `out`. The dialect report is
    /// captured around that render, here, so a document that keeps a spelling
    /// only Clean's vendored Carcara checks is [`CarcaraSurface::CleanDialect`]
    /// and one that eliminates the problem's own `let` with `:rule let` is
    /// [`CarcaraSurface::WithoutLetExpansion`], never `Supported`. No caller
    /// hands a report in, so none can pair a verdict with a report of other
    /// bytes, or with none.
    ///
    /// Its parse half is scanned on the proof and table the `--strict-proofs`
    /// and `--self-check` gates refuse on, so the line's `unsupported` and
    /// their refusal never disagree; that table can differ from the one the
    /// bytes are rendered with (datatype-field renderings, a sealed
    /// finite-enum table). A consumer that hands the document to an external
    /// checker reads the document's own verdict from
    /// [`Self::try_export_last_proof_alethe_for_problem_scope_with_carcara_surface`].
    ///
    /// `None` and `Some(Err(_))` when the plain stream returns them; on an
    /// error the sink may hold a partial prefix, as there. A streamed document
    /// implies the retained proof the gates scan; were that ever broken, this
    /// is an error, never an invented verdict.
    #[must_use]
    pub fn try_export_last_proof_alethe_for_problem_scope_to_with_carcara_surface<
        W: std::io::Write,
    >(
        &self,
        out: &mut W,
    ) -> Option<Result<CarcaraSurface, AletheStreamError>> {
        // The dialect report describes exactly the bytes streamed.
        let (streamed, rendered) = ay_proof::capture_alethe_dialect_report(|| {
            self.try_export_last_proof_alethe_for_problem_scope_to(out)
        });
        streamed.map(|streamed| {
            streamed.and_then(|()| {
                // `last_proof` is the gates' retained proof, further gated.
                self.strict_gate_carcara_surface()
                    .map(|parsed| parsed.with_dialect_report(&rendered))
                    .ok_or(AletheStreamError::Print(
                        AlethePrintError::UnavailableAuthenticatedSurface {
                            reason: "no retained UNSAT proof to read the streamed surface on",
                        },
                    ))
            })
        })
    }

    /// Render the problem-scoped document, in this executor's dialect, and
    /// hand it to `finish` with the proof and the override table it was
    /// rendered with.
    fn render_last_proof_alethe_for_problem_scope<T>(
        &self,
        finish: impl FnOnce(String, &Proof, Option<&DetHashMap<TermId, String>>) -> T,
    ) -> Option<Result<T, AlethePrintError>> {
        self.in_alethe_dialect(|| self.render_problem_scope_in_dialect(finish))
    }

    fn render_problem_scope_in_dialect<T>(
        &self,
        finish: impl FnOnce(String, &Proof, Option<&DetHashMap<TermId, String>>) -> T,
    ) -> Option<Result<T, AlethePrintError>> {
        if self.last_unsat_proof_reconstruction_suppressed {
            return None;
        }
        let proof = self.last_proof_with_authenticated_alethe_surface()?;
        // #A2b: `proof_reconstruction_step_budget` is set ONLY for the
        // synthesized-default certificate (never for explicit `--proof`,
        // `--strict-proofs`, `--self-check`, or `:produce-proofs`). Extend
        // that contract over Alethe EMISSION as well: rendering work is
        // capped so a seconds-fast UNSAT verdict is never followed by
        // minutes of certificate materialization (QF_ALIA pp-family). On
        // exhaustion the caller prints the honest "no proof certificate
        // emitted" warning; the verdict is already out and unchanged.
        if self.last_proof_has_finite_enum_sidecar() {
            let Some(overrides) = self.finite_enum_surface_overrides_for_proof(proof) else {
                return Some(Err(AlethePrintError::UnavailableAuthenticatedSurface {
                    reason: "the finite-enum proof surface is absent or stale",
                }));
            };
            let Some(scope) = self.proof_export_scope_assertions_for(proof) else {
                return Some(Err(AlethePrintError::UnavailableAuthenticatedSurface {
                    reason: "the finite-enum proof scope is absent or stale",
                }));
            };
            return Some(
                ay_proof::try_export_alethe_with_problem_scope_overrides_and_budget(
                    proof,
                    &self.ctx.terms,
                    &scope,
                    Some(overrides),
                    Some(MAX_FINITE_ENUM_RENDER_WORK),
                )
                .map(|document| finish(document, proof, Some(overrides))),
            );
        }
        let emission_budget = self
            .proof_reconstruction_step_budget
            .map(|_| DEFAULT_ALETHE_EMISSION_WORK_BUDGET);
        let scope = self.proof_export_scope_assertions_for(proof)?;
        let overrides = self.proof_export_term_overrides();
        let surfaces = self.authored_export_surfaces();
        Some(
            ay_proof::try_export_alethe_with_authored_surfaces(
                proof,
                &self.ctx.terms,
                &scope,
                overrides.as_ref(),
                surfaces.channels(),
                emission_budget,
            )
            .map(|document| finish(document, proof, overrides.as_ref())),
        )
    }
}
