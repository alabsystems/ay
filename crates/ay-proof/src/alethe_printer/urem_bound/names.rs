// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Short, proof-local names keep wide divider certificates within the original
//! checker input bound. Hexadecimal fields plus separators are injective over
//! (proof ID, nonce); the full source and all override channels still reserve
//! their names. Namespace selection shares the original export-work owner.

use super::{AlethePrinter, ProofId, TermData, TermId};

#[cfg(test)]
mod tests;

impl AlethePrinter<'_> {
    pub(super) fn urem_definition_prefix(&self, id: ProofId) -> Option<String> {
        for nonce in 0_u64..64 {
            self.admit_emission_work(32).then_some(())?;
            let prefix = format!("@u{:x}_{nonce:x}_", id.0);
            if !self.urem_namespace_collision(&prefix)? {
                self.check_emission_progress(0).ok()?;
                return Some(prefix);
            }
        }
        None
    }

    fn urem_namespace_collision(&self, prefix: &str) -> Option<bool> {
        for index in 0..self.terms.len() {
            self.admit_emission_work(1).then_some(())?;
            let term = self.terms.get(TermId(u32::try_from(index).ok()?));
            let collision = match term {
                TermData::Var(name, _) => self.urem_name_starts_with(name, prefix)?,
                TermData::App(symbol, _) => self.urem_name_starts_with(symbol.name(), prefix)?,
                TermData::Let(bindings, _) => {
                    let mut collision = false;
                    for (name, _) in bindings {
                        if self.urem_name_starts_with(name, prefix)? {
                            collision = true;
                            break;
                        }
                    }
                    collision
                }
                TermData::Forall(bindings, ..) | TermData::Exists(bindings, ..) => {
                    let mut collision = false;
                    for (name, _) in bindings {
                        if self.urem_name_starts_with(name, prefix)? {
                            collision = true;
                            break;
                        }
                    }
                    collision
                }
                _ => false,
            };
            if collision {
                return Some(true);
            }
        }
        let skolems = self.skolem_overrides.borrow();
        let bridges = self.let_bridge_renderings.borrow();
        for surface in self
            .term_overrides
            .into_iter()
            .flat_map(|map| map.values())
            .chain(skolems.values())
            .chain(bridges.values())
        {
            let work = surface.len().checked_mul(prefix.len())?.checked_add(1)?;
            self.admit_emission_work(u64::try_from(work).ok()?)
                .then_some(())?;
            if surface.contains(prefix) {
                return Some(true);
            }
        }
        Some(false)
    }

    fn urem_name_starts_with(&self, name: &str, prefix: &str) -> Option<bool> {
        self.admit_emission_work(u64::try_from(prefix.len().checked_add(1)?).ok()?)
            .then_some(())?;
        Some(name.starts_with(prefix))
    }
}
