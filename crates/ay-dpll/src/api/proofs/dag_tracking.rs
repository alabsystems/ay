// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact proof-premise substitution for assertion-time tracking guards.
use super::{NativeProofApplication as App, NativeProofDag, Solver, Term};
use ay_frontend::DeclarationId;
use std::collections::HashMap;

/// How one authored assertion was tracked when the native proof was built.
#[derive(Clone, Debug)]
pub enum NativeProofInputBinding {
    /// The assertion was not named or guarded.
    Untracked,
    /// The assertion was guarded by an exact declaration identity.
    Tracked {
        /// Authored tracking-label name.
        name: String,
        /// Source declaration identity of the tracking label.
        identity: DeclarationId,
    },
    /// The source used a tracking form this projection cannot preserve.
    Unsupported,
}

/// Destination-owned identities, retained independently of source reset/pop.
#[derive(Default)]
pub struct NativeProofTrackingCache(HashMap<DeclarationId, Term>);

impl Solver {
    pub(super) fn bind_native_tracking(
        &mut self,
        dag: NativeProofDag,
        inputs: &[Term],
        bindings: &[NativeProofInputBinding],
        cache: &mut NativeProofTrackingCache,
    ) -> Option<(NativeProofDag, Vec<Term>)> {
        let mut actual = Vec::new();
        let mut replacements = HashMap::new();
        let mut applications = Vec::new();
        for (&assertion, binding) in inputs.iter().zip(bindings) {
            match binding {
                NativeProofInputBinding::Untracked => actual.push(assertion),
                NativeProofInputBinding::Unsupported => return None,
                NativeProofInputBinding::Tracked { name, identity } => {
                    let label = if let Some(label) = cache.0.get(identity) {
                        *label
                    } else {
                        let id = self
                            .terms_mut()
                            .mk_fresh_named_var(name.clone(), ay_core::Sort::Bool);
                        let label = self.wrap_term(id);
                        cache.0.insert(identity.clone(), label);
                        label
                    };
                    let lhs = self.resolve_term("tracked proof", label).ok()?;
                    let rhs = self.resolve_term("tracked proof", assertion).ok()?;
                    let guard_id = self.terms_mut().mk_app(
                        ay_core::Symbol::named("=>"),
                        [lhs, rhs],
                        ay_core::Sort::Bool,
                    );
                    let guard = self.wrap_term(guard_id);
                    actual.extend([guard, label]);
                    let start = applications.len();
                    applications.extend([
                        App::Asserted(label),
                        App::Asserted(guard),
                        App::ModusPonens {
                            premises: [start, start + 1],
                            conclusion: assertion,
                        },
                    ]);
                    replacements.entry(assertion).or_insert(start + 2);
                }
            }
        }
        // Check assumptions follow all active assertion/label pairs, in order.
        actual.extend_from_slice(&inputs[bindings.len()..]);
        let mut indices = Vec::new();
        for node in dag.applications {
            let app = match node {
                App::Asserted(term) => {
                    if let Some(index) = replacements.get(&term) {
                        indices.push(*index);
                        continue;
                    }
                    App::Asserted(term)
                }
                App::UnitResolution {
                    premises,
                    conclusion,
                } => App::UnitResolution {
                    premises: [*indices.get(premises[0])?, *indices.get(premises[1])?],
                    conclusion,
                },
                App::ModusPonens { .. } => return None,
            };
            indices.push(applications.len());
            applications.push(app);
        }
        Some((
            NativeProofDag {
                applications,
                root: *indices.get(dag.root)?,
            },
            actual,
        ))
    }
}
