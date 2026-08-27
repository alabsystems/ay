// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fail-closed boundary for the retired SAT-level Alethe adapter.
//!
//! A [`crate::proof_certificate::ProofCertificate`] retains derived LRAT
//! clauses and their hints, but not the literals of the original DIMACS
//! clauses. The former exporter replaced those unavailable clauses with
//! `(assume hN true)`. Such assumptions are not bound to the input CNF, so the
//! resulting text cannot certify that input even if an Alethe parser accepts
//! its shape.
//!
//! DRAT and LRAT remain the supported SAT proof formats. SMT Alethe emission is
//! a separate, input-bound path in `ay-proof` and is unaffected.

use std::io::{self, Write};

pub(crate) const SAT_ALETHE_UNAVAILABLE: &str =
    "SAT Alethe export is unavailable because ProofCertificate does not retain original DIMACS clause literals; use LRAT or DRAT";

/// Refuse the unbound SAT-to-Alethe conversion without writing partial output.
pub(crate) fn refuse_unbound_alethe(_writer: &mut dyn Write) -> io::Result<()> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        SAT_ALETHE_UNAVAILABLE,
    ))
}

#[cfg(test)]
mod tests {
    use crate::proof_certificate::ProofCertificate;

    #[test]
    #[allow(deprecated)]
    fn public_adapter_refuses_without_writing() {
        let certificate = ProofCertificate::empty();
        let mut output = b"existing".to_vec();

        let error = certificate
            .write_alethe(&mut output)
            .expect_err("unbound SAT Alethe export must fail closed");

        assert_eq!(error.kind(), std::io::ErrorKind::Unsupported);
        assert!(error
            .to_string()
            .contains("original DIMACS clause literals"));
        assert_eq!(output, b"existing");
    }
}
