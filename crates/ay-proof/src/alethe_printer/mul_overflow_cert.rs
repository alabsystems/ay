// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A complete Alethe certificate for the checked multiplication overflow
//! identity of [`row::Row`] (external-codegen's u128 `checked_mul` lowering) and of
//! [`signed::Signed`] (its i128 one, `bvsdiv` expanded): the pinned
//! checker's restoring divider is followed stage by stage through a
//! quantified stage lemma inside ONE quantified division lemma
//! ([`div_lemma`]) that every use instantiates, the schoolbook high half is
//! related to the wide product through lifted limb products, and quotient
//! uniqueness comes from a monotonicity lemma — every Boolean step locally
//! checked, every ring step a `poly_simp`. The signed identity is the
//! unsigned one over the operands' magnitudes plus a case analysis of the
//! four `bvsdiv` cases ([`signed_facts`]).
//!
//! Bit-blasting the identity at 128 bits is out of reach for the pinned
//! checker's normalizer budget (the two 128-bit multipliers and the 128-stage
//! divider alone exceed it), so the certificate never blasts the whole
//! formula, and prints the divider's circuit once: the checker normalizes
//! every term of the document within a fixed work budget.

mod assembly;
mod assembly_f3;
mod bits;
mod cdcl;
mod chain;
mod clean;
mod div;
mod div_lemma;
mod div_spec;
mod helpers;
mod horner;
mod lift;
mod lin;
mod lin_bits;
mod local;
mod localsat;
mod mono;
#[cfg(test)]
#[path = "mul_overflow_cert/owner_tests.rs"]
mod owner_tests;
mod print;
mod proof;
mod propagation;
mod recognize;
pub(super) mod remainder;
mod row;
mod school;
mod shift;
mod signed;
mod signed_cases;
mod signed_facts;
mod signed_ground;
mod term;
#[cfg(test)]
#[path = "mul_overflow_cert/tests.rs"]
mod tests;

use super::emission_progress::EmissionProgress;
use super::AlethePrinter;
use ay_core::{ProofId, TermId, TermStore};

/// Whether `clause` is exactly the unit `(cl (= L R))` of the checked
/// multiplication overflow identity over four distinct `m`-bit limb
/// variables (`m` even, `4 <= m <= 64`), unsigned or signed — the clause
/// [`ay_core::TheoryLemmaKind::BvMulOverflowDivision`] certifies.
pub fn recognize_mul_overflow_division(terms: &TermStore, clause: &[TermId]) -> bool {
    recognize::shape(terms, clause).is_some()
}

/// The certificate text for limb width `m` over the printed limb spellings
/// `[a_lo, a_hi, b_lo, b_hi]`, its step ids under `final_id` and its names
/// under `prefix`, neither of which may collide with the rest of the
/// document. With `clause` (the caller's spelling of `(cl (= L R))`), its
/// step `final_id` concludes that clause; without, the text assumes
/// `(not (= L R))` and closes `(cl)`.
fn certificate(
    m: u32,
    names: [&str; 4],
    prefix: &str,
    final_id: &str,
    clause: Option<&str>,
    signed: bool,
    progress: EmissionProgress<'_>,
) -> Option<String> {
    if m < 4 || m % 2 != 0 {
        return None;
    }
    progress.poll().then_some(())?;
    let mut p =
        proof::Proof::new_with_progress(format!("{final_id}.mo"), format!("{prefix}w"), progress);
    let leaves = row::Row::leaves(&mut p.t, m, names);
    let (row, signed) = if signed {
        let (sg, core) = signed::Signed::new(&mut p.t, m, leaves);
        (core, Some(sg))
    } else {
        (row::Row::new(&mut p.t, m, leaves), None)
    };
    let (l, r) = signed.as_ref().map_or((row.l, row.r), |sg| (sg.l, sg.r));
    let h0 = if let Some(spelled) = clause {
        p.named_spelling = Some(spelled.to_string());
        None
    } else {
        let e = p.t.eq(l, r);
        let ne = p.t.not(e);
        Some(p.assume(ne))
    };
    let n = 2 * m;
    p.observe()?;
    p.opaque = [row.a_lo, row.a_hi, row.b_lo, row.b_hi]
        .into_iter()
        .collect();
    p.observe()?;
    let ctx = school::Ctx::new(&mut p, row, prefix)?;
    p.observe()?;
    let sc = ctx.schoolbook(&mut p)?;
    p.observe()?;
    let dstage = div::DivStage::new(&mut p, n, &format!("{prefix}v"))?;
    p.observe()?;
    let dl = div_lemma::DivLemma::new(&mut p, m, &dstage, &format!("{prefix}u"))?;
    p.observe()?;
    let mono = mono::Mono::new(&mut p, n, &format!("{prefix}m"))?;
    p.observe()?;
    let asm = assembly::Asm::new(&mut p, &ctx, sc, mono)?;
    let Some(sg) = signed else {
        p.observe()?;
        asm.run(&mut p, &dl, h0, clause.map(|_| final_id))?;
        p.observe()?;
        return Some(p.out);
    };
    p.observe()?;
    let (tb, zero) = asm.equivalence(&mut p, &dl)?;
    p.observe()?;
    // the signed facts read the limbs as extracts of the magnitudes
    p.opaque.clear();
    let core = signed_facts::Core {
        row: &ctx.row,
        tb,
        zero,
    };
    p.observe()?;
    let g = signed_facts::prove(&mut p, &sg, &core, &dl)?;
    p.observe()?;
    let e = p.t.eq(l, r);
    let lr = if clause.is_some() {
        p.emit_named(final_id, &[e], "cong", &[g])
    } else {
        p.emit(&[e], "cong", &[g], &[])
    };
    if let Some(h0) = h0 {
        p.emit(&[], "resolution", &[h0, lr], &[]);
    }
    p.observe()?;
    Some(p.out)
}

impl AlethePrinter<'_> {
    /// The complete certificate of a `BvMulOverflowDivision` lemma, whose
    /// last step is `id` itself, or `None` (the honest hole) when the clause
    /// is not exactly the recognized identity or its limbs do not print as
    /// plain symbols.
    pub(super) fn format_mul_overflow_division(
        &self,
        id: ProofId,
        clause: &[TermId],
    ) -> Option<String> {
        self.emission_progress.poll().then_some(())?;
        let shape = recognize::shape(self.terms, clause)?;
        let names = shape.leaves.map(|leaf| self.format_term(leaf));
        if names.iter().any(|name| !plain_symbol(name)) {
            return None;
        }
        let prefix = (0_u64..64)
            .map(|nonce| format!("@ay_mo_{id}_{nonce}_"))
            .find(|prefix| !self.proof_definition_name_collision(prefix))?;
        let names = [&*names[0], &*names[1], &*names[2], &*names[3]];
        let spelled = self.format_clause(clause);
        let key = CertificateKey {
            m: shape.m,
            names: names.map(str::to_string),
            prefix,
            final_id: id.to_string(),
            clause: spelled,
            signed: shape.signed,
        };
        self.check_emission_progress(0).ok()?;
        let document = remembered_certificate_with_progress(key, &self.emission_progress, |key| {
            let names = [
                &*key.names[0],
                &*key.names[1],
                &*key.names[2],
                &*key.names[3],
            ];
            certificate(
                key.m,
                names,
                &key.prefix,
                &key.final_id,
                Some(&key.clause),
                key.signed,
                self.emission_progress.clone(),
            )
        });
        self.check_emission_progress(0).ok()?;
        document
    }
}

/// The arguments determining the certificate bytes, not permission to render.
/// Reuse still observes this attempt's original sticky owner.
#[derive(Clone, PartialEq, Eq)]
struct CertificateKey {
    m: u32,
    names: [String; 4],
    prefix: String,
    final_id: String,
    clause: String,
    signed: bool,
}

thread_local! {
    /// The last certificate built on this thread, and what it was built from.
    static LAST_CERTIFICATE: std::cell::RefCell<Option<(CertificateKey, String)>> =
        const { std::cell::RefCell::new(None) };
}

/// The certificate for `key`, built by `build` or served from the last one
/// this thread built for exactly `key`.
///
/// One publication renders its document more than once — the strict
/// document scan before the answer, then the export — and each render built
/// this lemma's certificate from scratch. Measured 2026-10-01 on external-codegen's
/// i128 `checked_mul` definitional row 2025 (load average ~100 on 18 cores):
/// a 77.7 MB certificate, built twice, and the query answered in 20.4 s;
/// built once, in 9.9 s. [`certificate`] is a function of its arguments, so
/// serving the last one preserves the bytes, not permission to complete this
/// attempt. Its original owner is polled around lookup, copies and publication;
/// the printed document is checked the same either way.
#[cfg(test)]
fn remembered_certificate(
    key: CertificateKey,
    build: impl FnOnce(&CertificateKey) -> Option<String>,
) -> Option<String> {
    remembered_certificate_with_progress(key, &EmissionProgress::default(), build)
}

/// A candidate text is not settled until its original owner accepts. The
/// destructor also revokes it when a callback unwinds during publication.
struct CertificatePublication {
    previous: Option<(CertificateKey, String)>,
    settled: bool,
}

impl Drop for CertificatePublication {
    fn drop(&mut self) {
        if !self.settled {
            let previous = self.previous.take();
            let refused =
                LAST_CERTIFICATE.with(|last| std::mem::replace(&mut *last.borrow_mut(), previous));
            drop(refused);
        }
    }
}

/// Copying retained text supplies no new caller permission. No callback is
/// invoked while borrowing the thread-local cache.
fn remembered_certificate_with_progress(
    key: CertificateKey,
    progress: &EmissionProgress<'_>,
    build: impl FnOnce(&CertificateKey) -> Option<String>,
) -> Option<String> {
    progress.poll().then_some(())?;
    let kept = LAST_CERTIFICATE.with(|last| {
        last.borrow()
            .as_ref()
            .filter(|(built, _)| *built == key)
            .map(|(_, text)| text.clone())
    });
    progress.poll().then_some(())?;
    if kept.is_some() {
        return kept;
    }
    let text = build(&key)?;
    progress.poll().then_some(())?;
    let retained = text.clone();
    progress.poll().then_some(())?;
    let mut publication = CertificatePublication {
        previous: LAST_CERTIFICATE.with(|last| last.borrow_mut().replace((key, retained))),
        settled: false,
    };
    progress.poll().then_some(())?;
    drop(publication.previous.take());
    progress.poll().then_some(())?;
    publication.settled = true;
    Some(text)
}

/// Whether the printer renders the `BvMulOverflowDivision` lemma `clause`
/// as its complete certificate under the export's `overrides`: the clause is
/// the recognized identity and its four limbs print as plain symbols. The
/// certificate itself is built only by the printer (it is large); a builder
/// that still declines leaves the honest hole, which the strict document scan
/// counts, so this screen can only ever be optimistic about a hole, never
/// about an invalid step.
pub fn mul_overflow_division_lowering_supported(
    terms: &TermStore,
    clause: &[TermId],
    overrides: Option<&ay_core::kani_compat::DetHashMap<TermId, String>>,
) -> bool {
    let Some(shape) = recognize::shape(terms, clause) else {
        return false;
    };
    let printer = AlethePrinter::new_with_overrides_and_budget(terms, overrides, None);
    shape
        .leaves
        .iter()
        .all(|&leaf| plain_symbol(&printer.format_term(leaf)))
}

/// A simple SMT-LIB symbol that is not one of the names the certificate
/// introduces (all of which start with `@`).
fn plain_symbol(name: &str) -> bool {
    !name.is_empty()
        && !name.starts_with('@')
        && !name.starts_with(|c: char| c.is_ascii_digit())
        && name
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || "~!$%^&*_-+=<>.?/".contains(c))
}
