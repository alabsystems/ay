// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded opt-in diagnostics for strict certification and datatype derivation.

use ay_core::{ProofId, TermId};

use super::Executor;

const CERT_REJECT_PROBE_MAX_TERMS: usize = 32;
const CERT_REJECT_PROBE_MAX_TERM_CHARS: usize = 8 * 1024;

/// Print a certification-rejection diagnostic when `--probe-cert-reject` is set.
///
/// Downstream embedders (deductive-checks) surface only the opaque
/// `(incomplete self-check-rejected)` reason code, so the gate that actually
/// refused a refutation -- and, for a strict-checker refusal, the Alethe rule
/// and step it names -- is otherwise unobservable outside this crate. The
/// message is computed lazily so a disabled typed flag does no formatting.
pub(in crate::executor) fn probe_cert_reject(message: impl FnOnce() -> String) {
    emit_probe_cert_reject(ProbeFormat::Prefixed, message);
}

/// Print one unprefixed certification/datatype diagnostic through the shared
/// output boundary.
///
/// Raw diagnostics retain their historical `c ...` spelling and are visible
/// only under `--probe-cert-reject`. Callers still decide which work to perform:
/// in particular, the authority census remains guarded by the same typed flag
/// before it invokes this sink.
pub(crate) fn probe_cert_reject_raw(message: impl FnOnce() -> String) {
    emit_probe_cert_reject(ProbeFormat::Raw, message);
}

enum ProbeFormat {
    Prefixed,
    Raw,
}

fn emit_probe_cert_reject(format: ProbeFormat, message: impl FnOnce() -> String) {
    let enabled = ay_core::misc_cli_flags().probe_cert_reject;
    if !enabled {
        return;
    }
    let prefix = match format {
        ProbeFormat::Prefixed => "--probe-cert-reject: ",
        ProbeFormat::Raw => "",
    };
    ay_core::safe_eprintln!("{prefix}{}", message());
}

impl Executor {
    fn bounded_cert_reject_probe_term(&self, term: TermId) -> String {
        let formatted = self.format_term(term);
        let Some((cut, _)) = formatted
            .char_indices()
            .nth(CERT_REJECT_PROBE_MAX_TERM_CHARS)
        else {
            return formatted;
        };
        format!("{}…", &formatted[..cut])
    }

    pub(in crate::executor) fn bounded_cert_reject_probe_terms(&self, terms: &[TermId]) -> String {
        let mut formatted: Vec<String> = terms
            .iter()
            .take(CERT_REJECT_PROBE_MAX_TERMS)
            .map(|&term| self.bounded_cert_reject_probe_term(term))
            .collect();
        if terms.len() > CERT_REJECT_PROBE_MAX_TERMS {
            formatted.push(format!(
                "… {} term(s) omitted",
                terms.len() - CERT_REJECT_PROBE_MAX_TERMS
            ));
        }
        format!("[{}]", formatted.join(", "))
    }

    pub(super) fn deferred_trust_probe_message(
        &self,
        collected: &[(ProofId, Vec<TermId>)],
        authored: &[TermId],
    ) -> String {
        let mut lines = vec![format!(
            "deferred trust details: collected_steps={}",
            collected.len()
        )];
        for (step, clause) in collected.iter().take(CERT_REJECT_PROBE_MAX_TERMS) {
            lines.push(format!(
                "  step {step} clause={}",
                self.bounded_cert_reject_probe_terms(clause)
            ));
        }
        if collected.len() > CERT_REJECT_PROBE_MAX_TERMS {
            lines.push(format!(
                "  … {} trust step(s) omitted",
                collected.len() - CERT_REJECT_PROBE_MAX_TERMS
            ));
        }
        lines.push(format!(
            "  authored_assertions={}",
            self.bounded_cert_reject_probe_terms(authored)
        ));
        lines.join("\n")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deferred_trust_probe_formats_step_clauses_and_authored_scope() {
        let mut executor = Executor::new();
        let authored = executor.ctx.terms.mk_var("authored", ay_core::Sort::Bool);
        let lemma = executor.ctx.terms.mk_var("lemma", ay_core::Sort::Bool);
        let not_lemma = executor.ctx.terms.mk_not_raw(lemma);

        let message = executor
            .deferred_trust_probe_message(&[(ProofId(7), vec![lemma, not_lemma])], &[authored]);

        assert_eq!(
            message,
            "deferred trust details: collected_steps=1\n  step t7 clause=[lemma, (not lemma)]\n  authored_assertions=[authored]"
        );
    }
}
