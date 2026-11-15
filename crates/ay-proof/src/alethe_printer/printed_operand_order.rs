// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pairing a PRINTED argument list with the INTERNAL argument list of the
//! SAME application.
//!
//! Several printer lanes read one argument list off the printed application
//! (`split_application` over [`AlethePrinter::format_term`]) and one off the
//! term DAG, then treat position `k` of each as the same argument. That holds
//! only while the surface spelling and the stored spelling agree on ORDER. A
//! whole-application surface override supplies the AUTHOR's spelling, and for
//! an operator whose internal form is order-normalized the author's order need
//! not be the stored one — so position `k` of the printed list can name a
//! different argument than position `k` of the internal one, and whatever the
//! lane reads off the internal argument (its sort, its sub-terms) is then read
//! off the wrong node.
//!
//! [`AlethePrinter::internal_args_in_printed_order`] is the ONE place that
//! decides such a pairing. It is deliberately not a search: it answers `None`
//! unless every printed argument is matched to a DISTINCT internal argument
//! whose own rendering is byte-identical to it. A caller therefore gets either
//! the exact assignment or the stored order it already had — never a guess.
//! `None` also covers the ordinary case where the stored order already renders
//! in the printed order, which is what keeps every un-overridden step
//! byte-identical.

use super::AlethePrinter;
use ay_core::TermId;

#[cfg(test)]
#[path = "printed_operand_order/tests.rs"]
mod tests;

impl AlethePrinter<'_> {
    /// The internal arguments reordered so that position `k` holds the one
    /// that RENDERS as printed argument `k`, or `None` when the stored order
    /// already does (so there is only one reading) or when no exact assignment
    /// exists (so there is nothing to guess with).
    ///
    /// A reordering is offered only when every printed argument is matched to
    /// a DISTINCT internal argument whose own rendering is byte-identical to
    /// it. This is the same greedy multiset match the `or` decomposition lanes
    /// already use to align a printed disjunct list with its clause
    /// (`or_conclusion_in_premise_order`, `reorient_or_decomposition`); the
    /// congruence lane was the one printed-against-internal pairing left
    /// without it.
    pub(in crate::alethe_printer) fn internal_args_in_printed_order(
        &self,
        printed: &[String],
        internal: &[TermId],
    ) -> Option<Vec<TermId>> {
        if printed.len() != internal.len() || printed.len() < 2 {
            return None;
        }
        let rendered: Vec<String> = internal.iter().map(|&arg| self.format_term(arg)).collect();
        if printed
            .iter()
            .zip(rendered.iter())
            .all(|(printed, rendered)| printed == rendered)
        {
            return None;
        }
        let mut consumed = vec![false; internal.len()];
        let mut aligned = Vec::with_capacity(internal.len());
        for want in printed {
            let position = rendered
                .iter()
                .enumerate()
                .position(|(index, rendered)| !consumed[index] && rendered == want)?;
            consumed[position] = true;
            aligned.push(internal[position]);
        }
        Some(aligned)
    }
}
