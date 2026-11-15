// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

//! Frozen unpolled collector and traversal for semantic/error-order comparison.

use super::*;

pub(super) fn collect(
    proof: &Proof,
    terms: &TermStore,
    problem_assertions: Option<&[TermId]>,
) -> Result<FreshDefRegistry, ProofCheckError> {
    let bindings = collect_bindings(proof, terms)?;
    if bindings.is_empty() {
        return Ok(FreshDefRegistry { bindings });
    }
    verify(proof, terms, problem_assertions, &bindings)?;
    Ok(FreshDefRegistry { bindings })
}

fn collect_bindings(
    proof: &Proof,
    terms: &TermStore,
) -> Result<DetHashMap<String, FreshDefBinding>, ProofCheckError> {
    let mut bindings: DetHashMap<String, FreshDefBinding> = DetHashMap::default();
    for (index, step) in proof.steps.iter().enumerate() {
        let ProofStep::Step {
            rule: rule @ (AletheRule::FreshDefBound | AletheRule::FreshDefEq),
            clause,
            premises,
            args,
        } = step
        else {
            continue;
        };
        let step_id = ProofId(index as u32);
        // The two rules matched above each introduce exactly one binding.
        let introduced = recognize_fresh_definition(terms, rule, clause, premises.len(), args)
            .map_err(|reason| invalid(step_id, &reason))?;
        let &[(definiendum, definiens)] = introduced.as_slice() else {
            return Err(invalid(
                step_id,
                "a bound or equality introduces one binding",
            ));
        };
        let name = definiendum_name(terms, step_id, definiendum)?;
        match bindings.get(&name) {
            Some(prior) => {
                if prior.definiens != definiens {
                    return Err(invalid(
                        step_id,
                        &format!(
                            "fresh definition `{name}` is given a SECOND definiens (already \
                         bound at step {}); two definitions of one symbol equate their \
                         defining terms and are not a conservative extension",
                            prior.step,
                        ),
                    ));
                }
            }
            None => {
                bindings.insert(
                    name,
                    FreshDefBinding {
                        definiens,
                        step: step_id,
                    },
                );
            }
        }
    }
    Ok(bindings)
}

fn verify(
    proof: &Proof,
    terms: &TermStore,
    problem_assertions: Option<&[TermId]>,
    bindings: &DetHashMap<String, FreshDefBinding>,
) -> Result<(), ProofCheckError> {
    let mut constrained = DetHashSet::default();
    let mut visited = DetHashSet::default();
    for &assertion in problem_assertions.unwrap_or(&[]) {
        collect_names(terms, assertion, &mut constrained, &mut visited);
    }
    for step in &proof.steps {
        if let ProofStep::Assume(term) = step {
            collect_names(terms, *term, &mut constrained, &mut visited);
        }
    }
    let mut definiens_names = DetHashSet::default();
    let mut definiens_visited = DetHashSet::default();
    for binding in bindings.values() {
        collect_names(
            terms,
            binding.definiens,
            &mut definiens_names,
            &mut definiens_visited,
        );
    }
    for (name, binding) in bindings {
        if definiens_names.contains(name) {
            return Err(invalid(
                binding.step,
                &format!(
                    "fresh definition `{name}` occurs inside a definiens; the definitions \
                 would be recursive and need not admit any simultaneous assignment"
                ),
            ));
        }
        if constrained.contains(name) {
            return Err(invalid(
                binding.step,
                &format!(
                    "fresh definition `{name}` is NOT fresh: the symbol also occurs in the \
                 problem or in an `assume` of this proof, so bounding it is an ordinary \
                 added constraint rather than a conservative extension"
                ),
            ));
        }
    }
    Ok(())
}

fn collect_names(
    terms: &TermStore,
    root: TermId,
    names: &mut DetHashSet<String>,
    visited: &mut DetHashSet<TermId>,
) {
    let mut stack = vec![root];
    while let Some(id) = stack.pop() {
        if !visited.insert(id) {
            continue;
        }
        match terms.get(id) {
            TermData::Var(name, _) => {
                names.insert(name.clone());
            }
            TermData::App(sym, args) => {
                names.insert(sym.name().to_string());
                stack.extend(args.iter().copied());
            }
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, t, e) => {
                stack.push(*c);
                stack.push(*t);
                stack.push(*e);
            }
            TermData::Let(bindings, body) => {
                for (name, value) in bindings {
                    names.insert(name.clone());
                    stack.push(*value);
                }
                stack.push(*body);
            }
            TermData::Forall(vars, body, triggers) | TermData::Exists(vars, body, triggers) => {
                for (name, _) in vars {
                    names.insert(name.clone());
                }
                stack.push(*body);
                stack.extend(triggers.iter().flatten().copied());
            }
            _ => {}
        }
    }
}
