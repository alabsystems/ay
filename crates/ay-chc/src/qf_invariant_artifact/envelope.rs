// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Closed canonical envelope preparation, not model parsing or source authority.

mod canonical;
mod strings;
#[cfg(test)]
mod tests;

use super::{QfInvariantModelEnvelope, CHC_QF_INVARIANT_MODEL_ARTIFACT_MAX_BYTES};
use ay_core::original_query::{QueryError, WorkBudget};
use std::panic::{catch_unwind, resume_unwind, AssertUnwindSafe};

/// Preparation failure carries no accepting replay or source-binding authority.
#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
pub enum QfEnvelopePreparationError {
    #[error(transparent)]
    Control(#[from] QueryError),
    #[error("QF invariant envelope exceeds the existing artifact byte limit")]
    TooLarge,
    #[error("malformed QF invariant envelope")]
    Malformed,
    #[error("QF invariant envelope is not byte-canonical")]
    NonCanonical,
}

impl QfEnvelopePreparationError {
    /// Fold preparation failure into the caller's OriginalAdmission scope.
    /// Structural refusal is Invalid, never fabricated timeout/cancellation.
    pub fn query_error(self) -> QueryError {
        match self {
            Self::Control(error) => error,
            Self::TooLarge => QueryError::Invalid("QF envelope exceeds artifact byte bound"),
            Self::Malformed => QueryError::Invalid("malformed QF envelope"),
            Self::NonCanonical => QueryError::Invalid("noncanonical QF envelope"),
        }
    }
}

pub(super) trait Control {
    fn offer(&mut self, work: usize, bytes: usize) -> Result<(), QfEnvelopePreparationError>;
    fn allocation_failed(&mut self) -> QfEnvelopePreparationError;
}

pub(super) struct Legacy;
impl Control for Legacy {
    fn offer(&mut self, _: usize, _: usize) -> Result<(), QfEnvelopePreparationError> {
        Ok(())
    }
    fn allocation_failed(&mut self) -> QfEnvelopePreparationError {
        QfEnvelopePreparationError::Malformed
    }
}
struct BorrowedWork<'a, 'owner>(&'a mut WorkBudget<'owner>);
impl Control for BorrowedWork<'_, '_> {
    fn offer(&mut self, work: usize, bytes: usize) -> Result<(), QfEnvelopePreparationError> {
        self.0.admit(work, bytes).map_err(Into::into)
    }
    fn allocation_failed(&mut self) -> QfEnvelopePreparationError {
        self.0.refuse_exhaustion().into()
    }
}

/// Borrowed decoded fields. Hash spellings and model text remain UNTRUSTED.
/// No schema, exact-problem identity, model typing, inductiveness or proof was checked.
#[derive(Clone, Copy)]
pub struct QfInvariantEnvelopeView<'a> {
    pub schema: &'a str,
    pub schema_version: u64,
    pub role: &'a str,
    pub model_format: &'a str,
    pub normalized_input_sha256: &'a str,
    pub predicate_count: u64,
    pub model_sha256: &'a str,
    pub model_smtlib: &'a str,
}

/// Untrusted envelope payload retaining the SAME borrowed ledger until cleanup.
/// Plain Drop destroys prepaid DATA without a checked final poll or acceptance;
/// use with_envelope for checked cooperative consumption.
pub struct PreparedQfInvariantEnvelope<'budget, 'owner> {
    envelope: QfInvariantModelEnvelope,
    work: &'budget mut WorkBudget<'owner>,
}

impl PreparedQfInvariantEnvelope<'_, '_> {
    /// Consume through one unit callback, dispose of envelope and callback captures,
    /// then poll the SAME owner. This is a cooperative no-returned-carrier seam:
    /// callback captures can still export copies, whose pricing belongs to the caller.
    /// Use inside OriginalAdmission::with_work so callback errors and caught unwinds
    /// latch the original owner; no observer/grant/end is created here.
    pub fn with_envelope(
        self,
        operation: impl FnOnce(
            QfInvariantEnvelopeView<'_>,
            &mut WorkBudget<'_>,
        ) -> Result<(), QueryError>,
    ) -> Result<(), QueryError> {
        let Self { envelope, work } = self;
        let result = catch_unwind(AssertUnwindSafe(|| {
            work.charge(0)?;
            work.charge(std::mem::size_of::<QfInvariantEnvelopeView<'_>>())?;
            operation(view(&envelope), work)
        }));
        drop(envelope);
        let final_poll = work.charge(0);
        match result {
            Err(payload) => resume_unwind(payload),
            Ok(result) => {
                result?;
                final_poll
            }
        }
    }
}

/// Prepare exact JSON envelope DATA, not an InvariantModel or replay credential.
///
/// Each scan/read, checked scalar update, copied byte and canonical comparison
/// is offered BEFORE work. Each requested payload capacity and eventual disposal
/// is prepaid before fallible reserve. The original input storage remains caller-owned.
/// Source identity hashing, SMT parsing/typing/canonical model rendering and native
/// validation are downstream UNPRICED operations, never invoked here.
/// No cancellation polling inside the allocator or UTF-8 primitive is promised.
pub fn prepare_qf_invariant_envelope_with_work<'budget, 'owner>(
    bytes: &[u8],
    work: &'budget mut WorkBudget<'owner>,
) -> Result<PreparedQfInvariantEnvelope<'budget, 'owner>, QfEnvelopePreparationError> {
    work.charge(0)?;
    let result = decode(bytes, &mut BorrowedWork(work));
    // Failed decoding destroys all partial strings/cursor scratch before returning.
    let final_poll = work.charge(0);
    match result {
        Err(error) => {
            final_poll?;
            Err(error)
        }
        Ok(envelope) => {
            if let Err(error) = final_poll {
                drop(envelope);
                work.charge(0)?;
                return Err(error.into());
            }
            if let Err(error) =
                work.charge(std::mem::size_of::<PreparedQfInvariantEnvelope<'_, '_>>())
            {
                drop(envelope);
                work.charge(0)?;
                return Err(error.into());
            }
            Ok(PreparedQfInvariantEnvelope { envelope, work })
        }
    }
}

fn view(envelope: &QfInvariantModelEnvelope) -> QfInvariantEnvelopeView<'_> {
    QfInvariantEnvelopeView {
        schema: &envelope.schema,
        schema_version: envelope.schema_version,
        role: &envelope.role,
        model_format: &envelope.model_format,
        normalized_input_sha256: &envelope.normalized_input_sha256,
        predicate_count: envelope.predicate_count,
        model_sha256: &envelope.model_sha256,
        model_smtlib: &envelope.model_smtlib,
    }
}

pub(super) fn decode<C: Control>(
    bytes: &[u8],
    control: &mut C,
) -> Result<QfInvariantModelEnvelope, QfEnvelopePreparationError> {
    control.offer(0, 0)?;
    if bytes.len() > CHC_QF_INVARIANT_MODEL_ARTIFACT_MAX_BYTES {
        return Err(QfEnvelopePreparationError::TooLarge);
    }
    // from_utf8 scans at most the supplied bytes and allocates nothing.
    control.offer(bytes.len(), 0)?;
    std::str::from_utf8(bytes).map_err(|_| QfEnvelopePreparationError::Malformed)?;
    let envelope = {
        control.offer(std::mem::size_of::<Reader<'_, '_, C>>(), 0)?;
        let mut reader = Reader {
            bytes,
            at: 0,
            control,
        };
        reader.object()?
    };
    canonical::check(&envelope, bytes, control)?;
    control.offer(0, 0)?;
    Ok(envelope)
}

struct Reader<'bytes, 'control, C> {
    bytes: &'bytes [u8],
    at: usize,
    control: &'control mut C,
}
impl<C: Control> Reader<'_, '_, C> {
    fn peek(&mut self) -> Result<Option<u8>, QfEnvelopePreparationError> {
        self.control.offer(1, 0)?;
        Ok(self.bytes.get(self.at).copied())
    }
    fn take(&mut self) -> Result<u8, QfEnvelopePreparationError> {
        let byte = self.peek()?.ok_or(QfEnvelopePreparationError::Malformed)?;
        self.control.offer(1, 0)?;
        self.at += 1;
        Ok(byte)
    }
    fn whitespace(&mut self) -> Result<(), QfEnvelopePreparationError> {
        while matches!(self.peek()?, Some(b' ' | b'\n' | b'\r' | b'\t')) {
            self.take()?;
        }
        Ok(())
    }
    fn punctuation(&mut self, byte: u8) -> Result<(), QfEnvelopePreparationError> {
        self.whitespace()?;
        if self.take()? != byte {
            return Err(QfEnvelopePreparationError::Malformed);
        }
        Ok(())
    }
    fn number(&mut self) -> Result<u64, QfEnvelopePreparationError> {
        self.whitespace()?;
        let first = self.take()?;
        if !first.is_ascii_digit() {
            return Err(QfEnvelopePreparationError::Malformed);
        }
        let mut value = u64::from(first - b'0');
        while let Some(byte) = self.peek()?.filter(u8::is_ascii_digit) {
            if first == b'0' {
                return Err(QfEnvelopePreparationError::Malformed);
            }
            self.control.offer(2, 0)?;
            value = value
                .checked_mul(10)
                .and_then(|v| v.checked_add(u64::from(byte - b'0')))
                .ok_or(QfEnvelopePreparationError::Malformed)?;
            self.take()?;
        }
        Ok(value)
    }
    fn object(&mut self) -> Result<QfInvariantModelEnvelope, QfEnvelopePreparationError> {
        self.punctuation(b'{')?;
        self.control.offer(
            std::mem::size_of::<[Option<String>; 6]>()
                + std::mem::size_of::<[Option<u64>; 2]>()
                + std::mem::size_of::<QfInvariantModelEnvelope>(),
            0,
        )?;
        let mut text: [Option<String>; 6] = std::array::from_fn(|_| None);
        let mut numbers = [None; 2];
        let mut seen = 0u8;
        loop {
            if seen != 0 {
                self.punctuation(b',')?;
            }
            let key = self.string()?;
            // At most eight fixed-key comparisons; prepay before reading names.
            let comparisons = key
                .len()
                .checked_mul(8)
                .and_then(|n| n.checked_add(8))
                .ok_or_else(|| self.control.allocation_failed())?;
            self.control.offer(comparisons, 0)?;
            let field = match key.as_str() {
                "schema" => 0,
                "role" => 1,
                "model_format" => 2,
                "normalized_input_sha256" => 3,
                "model_sha256" => 4,
                "model_smtlib" => 5,
                "schema_version" => 6,
                "predicate_count" => 7,
                _ => return Err(QfEnvelopePreparationError::Malformed),
            };
            drop(key);
            self.control.offer(3, 0)?;
            if seen & (1 << field) != 0 {
                return Err(QfEnvelopePreparationError::Malformed);
            }
            seen |= 1 << field;
            self.punctuation(b':')?;
            if field < 6 {
                text[field] = Some(self.string()?);
            } else {
                numbers[field - 6] = Some(self.number()?);
            }
            self.whitespace()?;
            if self.peek()? == Some(b'}') {
                self.take()?;
                break;
            }
        }
        self.whitespace()?;
        if self.peek()?.is_some() || seen != u8::MAX {
            return Err(QfEnvelopePreparationError::Malformed);
        }
        assemble(text, numbers)
    }
}

fn assemble(
    text: [Option<String>; 6],
    numbers: [Option<u64>; 2],
) -> Result<QfInvariantModelEnvelope, QfEnvelopePreparationError> {
    let [schema, role, model_format, normalized_input_sha256, model_sha256, model_smtlib] = text;
    Ok(QfInvariantModelEnvelope {
        schema: schema.ok_or(QfEnvelopePreparationError::Malformed)?,
        schema_version: numbers[0].ok_or(QfEnvelopePreparationError::Malformed)?,
        role: role.ok_or(QfEnvelopePreparationError::Malformed)?,
        model_format: model_format.ok_or(QfEnvelopePreparationError::Malformed)?,
        normalized_input_sha256: normalized_input_sha256
            .ok_or(QfEnvelopePreparationError::Malformed)?,
        predicate_count: numbers[1].ok_or(QfEnvelopePreparationError::Malformed)?,
        model_sha256: model_sha256.ok_or(QfEnvelopePreparationError::Malformed)?,
        model_smtlib: model_smtlib.ok_or(QfEnvelopePreparationError::Malformed)?,
    })
}
