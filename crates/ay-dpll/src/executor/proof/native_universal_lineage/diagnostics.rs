// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bounded comparison at the actual preprocessor/Skolem producer boundary.
//! Diagnostics create no assertion, registry entry, or proof authority.

use super::NativeUniversalSource;
use crate::executor::Executor;
use ay_core::{TermData, TermId};

impl Executor {
    pub(in crate::executor) fn note_native_skolem_instance(
        &mut self,
        original: TermId,
        quantified: TermId,
        witness: TermId,
        recorded: TermId,
        asserted: TermId,
    ) {
        if !ay_core::misc_cli_flags().debug_cert {
            return;
        }
        let Some(source) = NativeUniversalSource::capture(self) else {
            eprintln!("CERT/native-skolem: no original native receipt source={original:?} q={quantified:?}");
            return;
        };
        let Some(exact) =
            self.native_negative_universal_instance(&source, original, quantified, witness)
        else {
            eprintln!("CERT/native-skolem: no exact source instance source={original:?} q={quantified:?} witness={witness:?}");
            return;
        };
        if self
            .admit_native_universal_terms(&[recorded, asserted])
            .is_none()
            || self.charge_native_universal(64 * 1024, 64 * 2048).is_none()
        {
            return;
        }
        eprintln!("CERT/native-skolem: source={original:?} q={quantified:?} witness={witness:?} raw={exact:?} recorded={recorded:?} asserted={asserted:?} exact_match={}", exact == recorded);
        if exact == recorded {
            return;
        }
        let mut pending = vec![(exact, 0usize), (recorded, 0usize)];
        let mut left = 64usize;
        while let Some((term, depth)) = pending.pop() {
            let Some(rest) = left.checked_sub(1) else {
                break;
            };
            left = rest;
            let children: &[TermId] = match self.ctx.terms.get(term) {
                TermData::App(symbol, args) => {
                    let name: String = symbol.name().chars().take(128).collect();
                    eprintln!(
                        "CERT/native-skolem-node: id={term:?} depth={depth} app={name:?} arity={}",
                        args.len()
                    );
                    args
                }
                TermData::Var(name, id) => {
                    let name: String = name.chars().take(128).collect();
                    eprintln!("CERT/native-skolem-node: id={term:?} depth={depth} var={name:?} var_id={id}");
                    &[]
                }
                TermData::Not(child) => {
                    eprintln!("CERT/native-skolem-node: id={term:?} depth={depth} not={child:?}");
                    std::slice::from_ref(child)
                }
                TermData::Ite(c, t, e) => {
                    eprintln!(
                        "CERT/native-skolem-node: id={term:?} depth={depth} ite={c:?},{t:?},{e:?}"
                    );
                    if depth < 3 && pending.len().checked_add(3).is_some_and(|n| n <= left) {
                        pending.extend([(*c, depth + 1), (*t, depth + 1), (*e, depth + 1)]);
                    }
                    continue;
                }
                TermData::Const(_) => {
                    eprintln!("CERT/native-skolem-node: id={term:?} depth={depth} constant");
                    &[]
                }
                _ => return,
            };
            if depth < 3
                && pending
                    .len()
                    .checked_add(children.len())
                    .is_some_and(|n| n <= left)
            {
                pending.extend(children.iter().map(|&child| (child, depth + 1)));
            }
        }
    }
}
