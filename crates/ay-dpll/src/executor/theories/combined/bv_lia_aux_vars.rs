// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The BV-LIA bridge's fresh auxiliary variables, spelled without a `TermId`.
//!
//! Every fresh variable the bridge mints goes through [`mint_bv_lia_aux_var`],
//! which spells it `{prefix}_{n}` (`TermStore::mk_fresh_var`), `n` being the
//! store's variable counter. The name identifies the KIND of variable and
//! nothing else; nothing reads it back.
//!
//! These names used to spell the `TermId` they stood for
//! (`__ay_bv_lia_cong_k{source}_w{width}`, `__ay_bv_lia_i{term}_w{width}`,
//! `__ay_bv_lia_q{arg}_w{width}`, `__ay_bv_lia_ib{var}_w{width}` and
//! `__ay_bv_lia_ir{var}_w{width}`). Nothing parsed the id back. But an
//! internal name that carries an id vetoes every arena prune
//! (`carries_name_encoded_term_ids`), and the bridge mints these names into
//! the live arena. The deferred-trust re-solve (`RECONFIRM(4)` in
//! `unsat_cert.rs`) and the forged-UNSAT guard's rebuild then ran on a clone
//! of the enclosing solve's whole arena, proof scratch included, instead of
//! the compacted one `compact_derived_arena` exists for. Measured on
//! `deductive_checks_set_fold_posture`'s captured obligation at 6ccb67539 (test
//! profile, X925 cores): the re-solve's clone held 17,475 terms instead of
//! 229 and ran past the 180 s deadline (`unknown`); pruned, it answers
//! `unsat` in 32 s.
//!
//! [`is_bv_lia_aux_var_name`] is the exact grammar of what the minter spells.
//! The prune's allow-list (`is_counter_only_internal_name`) reads it, so the
//! exemption cannot drift from the producer.

use ay_core::{Sort, TermId, TermStore};

/// The kinds of auxiliary variable the BV-LIA bridge mints, one prefix each.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::executor) enum BvLiaAuxVar {
    /// The Int slack `k` of the modular congruence `bv2nat(b) = s - 2^w * k`
    /// (`push_bv2nat_congruence`, `push_residue_congruence`).
    CongruenceSlack,
    /// The bit-blast probe's BV residue standing for `int2bv(w, t)`
    /// (`BvLiaBitblastTranslator::int_residue_var`).
    ResidueVector,
    /// The Int quotient `k` of `e = bv2nat(int2bv(W, e)) + 2^W * k`
    /// (`collect_bv_lia_residue_bridge_assertions`).
    EuclideanQuotient,
    /// The Int-blast lane's vector for a bounded Int variable.
    BoundedBlastVector,
    /// The Int-blast lane's vector for a residue-only Int variable.
    ResidueBlastVector,
}

impl BvLiaAuxVar {
    /// Every kind, for the grammar check.
    const ALL: [Self; 5] = [
        Self::CongruenceSlack,
        Self::ResidueVector,
        Self::EuclideanQuotient,
        Self::BoundedBlastVector,
        Self::ResidueBlastVector,
    ];

    /// The fixed prefix `mk_fresh_var` extends with `_{n}`.
    const fn prefix(self) -> &'static str {
        match self {
            Self::CongruenceSlack => "__ay_bv_lia_cong",
            Self::ResidueVector => "__ay_bv_lia_i",
            Self::EuclideanQuotient => "__ay_bv_lia_q",
            Self::BoundedBlastVector => "__ay_bv_lia_ib",
            Self::ResidueBlastVector => "__ay_bv_lia_ir",
        }
    }
}

/// A fresh, unconstrained variable of `sort` for `kind`, spelled
/// `{prefix}_{n}`, where `n` is `TermStore::var_counter` (which
/// `mark_and_compact` does not relabel) and never a `TermId`.
pub(in crate::executor) fn mint_bv_lia_aux_var(
    terms: &mut TermStore,
    kind: BvLiaAuxVar,
    sort: Sort,
) -> TermId {
    terms.mk_fresh_var(kind.prefix(), sort)
}

/// Whether `name` is exactly a spelling [`mint_bv_lia_aux_var`] produces:
/// one of the five prefixes, `_`, and a non-empty all-digit counter. The
/// former spellings (`__ay_bv_lia_cong_k4_w64_14`, `__ay_bv_lia_i4_w64_9`)
/// and any longer or mixed tail do not match.
pub(in crate::executor) fn is_bv_lia_aux_var_name(name: &str) -> bool {
    BvLiaAuxVar::ALL.iter().any(|kind| {
        name.strip_prefix(kind.prefix())
            .and_then(|rest| rest.strip_prefix('_'))
            .is_some_and(|tail| !tail.is_empty() && tail.bytes().all(|b| b.is_ascii_digit()))
    })
}

#[cfg(test)]
#[path = "bv_lia_aux_vars_tests.rs"]
mod tests;
