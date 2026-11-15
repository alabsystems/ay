// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

// These are the App identities this closure interprets or generates. Not/Ite
// use intrinsic TermData variants, so unrelated declarations with those names
// do not change their meaning. An arbitrary declared scalar UF is left opaque.
const IDENTITIES: [&str; 5] = ["select", "store", "const-array", "=", "distinct"];

/// Fixed-size semantic dependencies, separate from the physical store stamp.
#[derive(Clone, Copy, Default)]
pub(super) struct Primitives(u8);

impl Primitives {
    /// Called within the paid source classification, which already covers the
    /// name bytes. Generated equality is recorded before expansion begins.
    pub(super) fn observe(&mut self, name: &str) {
        self.0 |= match name {
            "select" => 1,
            "store" => 2,
            "const-array" => 4,
            "=" => 8,
            "distinct" => 16,
            _ => 0,
        };
    }

    /// Registry membership overrides spelling even for a Named symbol.
    /// Registration is append-only but does not advance the snapshot stamp,
    /// so source validation must repeat these exact original dependencies.
    pub(super) fn validate(&self, terms: &TermStore, owner: &CountedAdmission) -> Result<()> {
        for (index, identity) in IDENTITIES.iter().enumerate() {
            owner.admit(1, 0)?;
            if self.0 & (1 << index) != 0 {
                // One logical dictionary lookup plus its exact name bytes.
                owner.admit(identity.len() + 1, 0)?;
                if terms.is_declared_function(identity) {
                    return Err(Error::Unsupported);
                }
            }
        }
        owner.check()?;
        Ok(())
    }
}
