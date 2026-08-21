// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// ---------------------------------------------------------------------------
// Digests
// ---------------------------------------------------------------------------

pub(super) fn hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        let _ = write!(s, "{b:02x}");
    }
    s
}

/// SHA-256 of arbitrary bytes, lowercase hex.
#[must_use]
pub fn sha256_hex(bytes: &[u8]) -> String {
    hex(&Sha256::digest(bytes))
}

/// The canonicalisation rule, version 1.
///
/// EVERY value is taken from the exact side-store when one exists — never from
/// the `f64` proxy — because that store is what the certificate verifier reads.
/// A digest over the proxies would bind a model the proof is not about.
///
/// This rule is FROZEN. A future change gets `v2` alongside; `v1` never moves,
/// or every certificate ever written stops matching.
pub(super) fn write_canonical_model_v1(writer: &mut impl fmt::Write, model: &Model) -> fmt::Result {
    writeln!(writer, "ayc-canon-v1")?;
    writeln!(writer, "sense {}", sense_token(model.sense()))?;
    writeln!(writer, "objective {}", u8::from(model.has_objective()))?;
    writeln!(writer, "offset {}", fmt_rat(&model.obj_offset_exact()))?;
    writeln!(writer, "cols {}", model.num_cols())?;
    for j in 0..model.num_cols() {
        let c = Col(j as u32);
        let (lb, ub) = model.col_bounds(c);
        let kind = match model.col_kind(c) {
            ColKind::Binary => "b",
            ColKind::Integer => "i",
            ColKind::Continuous => "c",
        };
        let objf = model.obj_coeff(c);
        // Frozen canonical-v1 rule: the importer records objective overrides
        // only for nonzero advice coefficients, so stored zero encodes exact
        // zero on every admitted wire model. Preserve that historical byte
        // encoding; arbitrary transformed models would require canonical v2.
        let obj = if objf == 0.0 {
            BigRational::zero()
        } else {
            model.obj_coeff_exact_at(j as u32, objf)
        };
        writeln!(
            writer,
            "col {j} {kind} {} {} {}",
            fmt_bound(exact(lb).as_ref(), false),
            fmt_bound(exact(ub).as_ref(), true),
            fmt_rat(&obj)
        )?;
    }
    writeln!(writer, "rows {}", model.num_rows())?;
    for i in 0..model.num_rows() {
        let (coeffs, lb, ub) = model.row(Row(i as u32));
        write!(
            writer,
            "row {i} {} {} {}",
            fmt_bound(model.row_lb_exact(i, lb).as_ref(), false),
            fmt_bound(model.row_ub_exact(i, ub).as_ref(), true),
            coeffs.len()
        )?;
        // `Model::row` guarantees sorted, duplicate-free, zero-free.
        for &(c, a) in coeffs {
            write!(writer, " {c} {}", fmt_rat(&model.row_coeff_exact(i, c, a)))?;
        }
        writer.write_char('\n')?;
    }
    Ok(())
}

/// Materialize canonical model v1 exactly as it is hashed and written in AYC.
#[must_use]
pub fn canonical_model_v1(model: &Model) -> String {
    let mut text = String::new();
    // `String` implements an infallible `fmt::Write` sink.
    let _ = write_canonical_model_v1(&mut text, model);
    text
}

pub(super) struct CanonicalDigestWriter {
    digest: Sha256,
    bytes: usize,
    max_bytes: Option<usize>,
    deadline: Option<Instant>,
    failed: bool,
}

impl CanonicalDigestWriter {
    fn new(max_bytes: Option<usize>, deadline: Option<Instant>) -> Self {
        Self {
            digest: Sha256::new(),
            bytes: 0,
            max_bytes,
            deadline,
            failed: false,
        }
    }

    fn finish(self) -> Option<[u8; 32]> {
        if self.failed
            || self
                .deadline
                .is_some_and(|deadline| Instant::now() >= deadline)
        {
            return None;
        }
        Some(self.digest.finalize().into())
    }
}

impl fmt::Write for CanonicalDigestWriter {
    fn write_str(&mut self, text: &str) -> fmt::Result {
        let Some(next) = self.bytes.checked_add(text.len()) else {
            self.failed = true;
            return Err(fmt::Error);
        };
        if self.max_bytes.is_some_and(|limit| next > limit)
            || self
                .deadline
                .is_some_and(|deadline| Instant::now() >= deadline)
        {
            self.failed = true;
            return Err(fmt::Error);
        }
        self.digest.update(text.as_bytes());
        self.bytes = next;
        Ok(())
    }
}

/// Stream canonical v1 directly into SHA-256 under an absolute deadline and
/// byte cap. No canonical-model `String` is materialized.
pub(crate) fn canonical_digest_bytes_bounded(
    model: &Model,
    deadline: Option<Instant>,
    max_bytes: usize,
) -> Option<[u8; 32]> {
    let mut writer = CanonicalDigestWriter::new(Some(max_bytes), deadline);
    write_canonical_model_v1(&mut writer, model).ok()?;
    writer.finish()
}

/// The `model canon v1` digest.
#[must_use]
pub fn canonical_digest(model: &Model) -> String {
    let digest = canonical_digest_bytes(model);
    let mut encoded = String::with_capacity(64);
    for byte in digest {
        let _ = write!(encoded, "{byte:02x}");
    }
    encoded
}

pub(crate) fn canonical_digest_bytes(model: &Model) -> [u8; 32] {
    let mut writer = CanonicalDigestWriter::new(None, None);
    // With neither a byte cap nor a deadline, the sink can fail only if the
    // canonical length overflows `usize`, impossible for an addressable model.
    let _ = write_canonical_model_v1(&mut writer, model);
    writer.digest.finalize().into()
}

pub(super) fn emitted_model_canon_digest(
    model: &Model,
    outcome: &Outcome,
    sat_relu: Option<&SatReluInfeasibilityCertificate>,
) -> String {
    // The SAT/ReLU certificate is constructed only after the bounded producer
    // has replayed its RUP DAG, and its private constructor binds the exact
    // canonical-model digest before the session can publish the refutation.
    // Reuse that retained digest when this is the evidence `emit` will write;
    // hashing the full model again here used to duplicate verdict-critical
    // work on every SAT/ReLU UNSAT. A manually assembled, mismatched EmitCtx
    // remains fail-closed: the public checker re-derives this header digest
    // from the supplied model text and rejects the mismatch.
    if matches!(
        outcome,
        Outcome::Infeasible {
            cert: None,
            tree_cert: None
        }
    ) {
        if let Some(certificate) = sat_relu {
            return digest_hex(certificate.model_canon_sha256());
        }
    }
    canonical_digest(model)
}
