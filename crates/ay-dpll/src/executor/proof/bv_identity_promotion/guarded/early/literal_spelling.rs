// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Compact only canonical literal leaves after the caller's full canonical
//! source roundtrip. No second source rendering, parsing or interning occurs.

use super::*;
use ay_core::kani_compat::{DetHashMap, DetHashSet};
use ay_core::{AletheRule, Constant, ProofStep, TermData};
use num_traits::ToPrimitive;

impl Executor {
    /// Optional presentation only for a checked new-intrinsic early candidate
    /// whose root/negative already passed the ordinary canonical roundtrip.
    /// Err is a live stop; None keeps the old presentation. Source work is
    /// never refunded, and no source premise or literal value is changed.
    pub(in crate::executor::proof) fn checked_ground_literal_spellings(
        &mut self,
        root: TermId,
        negative: TermId,
        candidate: &Proof,
    ) -> Result<Option<DetHashMap<TermId, String>>, ()> {
        if self.alethe_dialect() != ay_proof::AletheDialect::Clean
            || self
                .last_proof_term_overrides
                .as_ref()
                .is_some_and(|map| !map.is_empty())
        {
            return Ok(None);
        }
        let stop = self.make_proof_assembly_should_stop();
        if stop() {
            return Err(());
        }
        if !self.proof_source_work.spend_canonical_scan_work(32) {
            return Ok(None);
        }
        if self.ctx.terms.entry_stamp(root).is_none()
            || self.ctx.terms.entry_stamp(negative).is_none()
            || self.ctx.terms.sort(root) != &Sort::Bool
            || self.ctx.terms.sort(negative) != &Sort::Bool
            || !matches!(self.ctx.terms.get(negative), TermData::Not(child) if *child == root)
        {
            return Ok(None);
        }
        if !self
            .proof_source_work
            .spend_canonical_scan_work(candidate.steps.len())
        {
            return Ok(None);
        }
        if !candidate.steps.iter().any(|step| {
            matches!(
                step,
                ProofStep::Step {
                    rule: AletheRule::BvOffsetSpinesV1 | AletheRule::BvReconstructV1,
                    ..
                }
            )
        }) {
            return Ok(None);
        }
        if !self.proof_source_work.spend_canonical_scan_work(128) {
            return Ok(None);
        }
        let bound = crate::executor::proof::authored_ground_closure::MAX_NODES;
        let mut pending = vec![root];
        let mut seen = DetHashSet::default();
        let mut literals = DetHashMap::default();
        while let Some(term) = pending.pop() {
            if stop() {
                return Err(());
            }
            if !self.proof_source_work.spend_canonical_scan_work(8) {
                return Ok(None);
            }
            if seen.contains(&term) {
                continue;
            }
            if seen.len() == bound || self.ctx.terms.entry_stamp(term).is_none() {
                return Ok(None);
            }
            if !self.proof_source_work.spend_canonical_scan_work(128) {
                return Ok(None);
            }
            seen.insert(term);
            match self.ctx.terms.get(term) {
                TermData::Const(Constant::BitVec { value, width }) => {
                    if !(1..=128).contains(width)
                        || value.sign() == num_bigint::Sign::Minus
                        || value.bits() > u64::from(*width)
                        || self.ctx.terms.sort(term).bitvec_width() != Some(*width)
                    {
                        return Ok(None);
                    }
                    if width % 4 == 0 {
                        let Some(bits) = value.to_u128() else {
                            return Ok(None);
                        };
                        literals.insert(
                            term,
                            format!("#x{bits:0digits$x}", digits = (*width / 4) as usize),
                        );
                    }
                }
                TermData::App(_, children) => {
                    if children.len() > bound.saturating_sub(pending.len()) {
                        return Ok(None);
                    }
                    if !self
                        .proof_source_work
                        .spend_canonical_scan_work(children.len().saturating_mul(8))
                    {
                        return Ok(None);
                    }
                    pending.extend(children.iter().copied());
                }
                TermData::Not(child) => pending.push(*child),
                TermData::Ite(a, b, c) => {
                    if pending.len().saturating_add(3) > bound {
                        return Ok(None);
                    }
                    pending.extend([*a, *b, *c]);
                }
                TermData::Const(_) | TermData::Var(..) => {}
                _ => return Ok(None),
            }
        }
        if literals.is_empty() {
            return Ok(None);
        }
        // Each replacement is a complete standard literal of the SAME value
        // and width as its canonical constant. No application, name, operator,
        // sort, source ID or proof AST can be overridden by this table. The
        // caller already checked the full canonical source roundtrip; a second
        // render/parse/reintern would be redundant source work. Actual export
        // remains metered by its existing owner and exact surface guards.
        if stop() {
            return Err(());
        }
        Ok(Some(literals))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_frontend::{parse, Command};

    fn fixture() -> (Executor, TermId, TermId, Proof) {
        let input="(set-option :produce-proofs true)(set-logic QF_BV)(declare-const x (_ BitVec 8))(assert (not (= (bvor ((_ zero_extend 4) ((_ extract 3 0) x)) (bvshl ((_ zero_extend 4) ((_ extract 7 4) x)) (_ bv4 8))) x)))";
        let mut exec = Executor::new();
        for command in parse(input).unwrap() {
            if !matches!(command, Command::CheckSat | Command::Exit) {
                exec.execute_all(&[command]).unwrap();
            }
        }
        let source = exec.ctx.assertions_parsed()[0].clone();
        let root = exec.raw_intern_ground_bv_surface(&source).unwrap();
        let negative = exec.ctx.terms.mk_not_raw(root);
        let proof = exec.early_ground_closure_memory_candidate(root).unwrap();
        assert!(exec
            .check_proof_strict_derivation_with_datatypes(&proof)
            .unwrap()
            .is_complete());
        (exec, root, negative, proof)
    }

    #[test]
    fn checked_ground_literal_spellings_preserve_literal_identity_and_prior_channel() {
        let (mut exec, root, negative, proof) = fixture();
        assert!(exec.early_ground_memory_terms_print_faithfully(&[root, negative]));
        let before = exec.proof_source_work.remaining_for_test();
        let compact = exec
            .checked_ground_literal_spellings(root, negative, &proof)
            .unwrap()
            .unwrap();
        assert!(!compact.is_empty());
        assert!(compact.values().all(|text| text.starts_with("#x")));
        assert!(exec.last_proof_term_overrides.is_none());
        assert!(exec.proof_source_work.remaining_for_test() < before);
        assert!(
            exec.checked_ground_literal_spellings(root, root, &proof)
                .unwrap()
                .is_none(),
            "invalid derived shell is not a source-depth exception"
        );
        assert!(exec.last_proof_term_overrides.is_none());
        let mut forged = DetHashMap::default();
        forged.insert(root, "false".into());
        exec.last_proof_term_overrides = Some(forged.clone());
        assert!(exec
            .checked_ground_literal_spellings(root, negative, &proof)
            .unwrap()
            .is_none());
        assert_eq!(exec.last_proof_term_overrides, Some(forged));
    }

    #[test]
    fn checked_ground_literal_spellings_keep_work_stop_pinned_and_actual_pop_boundaries() {
        let (mut exec, root, negative, proof) = fixture();
        let arena = exec.ctx.terms.len();
        exec.proof_source_work.set_remaining_for_test(0);
        assert!(exec
            .checked_ground_literal_spellings(root, negative, &proof)
            .unwrap()
            .is_none());
        assert!(exec.last_proof_term_overrides.is_none());
        assert_eq!(exec.ctx.terms.len(), arena);
        let (mut exec, root, negative, proof) = fixture();
        exec.set_alethe_dialect(ay_proof::AletheDialect::PinnedCarcara);
        let before = exec.proof_source_work.remaining_for_test();
        assert!(exec
            .checked_ground_literal_spellings(root, negative, &proof)
            .unwrap()
            .is_none());
        assert_eq!(exec.proof_source_work.remaining_for_test(), before);
        let (mut exec, root, negative, proof) = fixture();
        exec.set_interrupt(std::sync::Arc::new(std::sync::atomic::AtomicBool::new(
            true,
        )));
        assert!(exec
            .checked_ground_literal_spellings(root, negative, &proof)
            .is_err());
        assert!(exec.last_proof_term_overrides.is_none());
        let (mut exec, root, negative, proof) = fixture();
        let compact = exec
            .checked_ground_literal_spellings(root, negative, &proof)
            .unwrap()
            .unwrap();
        exec.last_proof_term_overrides = Some(compact);
        exec.execute_all(&parse("(push 1)(pop 1)").unwrap())
            .unwrap();
        assert!(exec.last_proof_term_overrides.is_none());
    }
}
