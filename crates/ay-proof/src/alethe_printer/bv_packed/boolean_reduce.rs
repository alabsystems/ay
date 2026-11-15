// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Checked local simplification before enumerating a Boolean carry identity.

use super::boolean_cases::Boolean;
use super::*;

impl PackedProof<'_, '_> {
    pub(super) fn boolean_reduce(&mut self, term: &Boolean) -> Option<(Boolean, Equality)> {
        let Boolean::Apply(op, args) = term else {
            return Some((
                term.clone(),
                self.equality(&term.text(), &term.text(), "refl", &[])?,
            ));
        };
        let mut children = Vec::new();
        let mut proofs = Vec::new();
        for arg in args {
            let (child, proof) = self.boolean_reduce(arg)?;
            children.push(child);
            proofs.push(proof);
        }
        let changed = self.congruence(op, &proofs)?;
        let reduced = Boolean::Apply(op, children);
        let text: Vec<_> = proofs.iter().map(|p| p.right.as_str()).collect();
        let Some(target) = simple_boolean(op, &text) else {
            return Some((reduced, changed));
        };
        let target = Boolean::term(&target);
        let key = (reduced.text(), target.text());
        let simple = if let Some(proof) = self.boolean_lemmas.get(&key) {
            proof.clone()
        } else {
            let proof = if matches!(*op, "and" | "or") {
                let rule = format!("{op}_simplify");
                if matches!(target.text().as_str(), "true" | "false") {
                    self.equality(&reduced.text(), &target.text(), &rule, &[])?
                } else {
                    // One argument survives, and it may itself be an `and`/`or`
                    // application (see `simplify_to_survivor`).
                    self.simplify_to_survivor(&reduced.text(), &target.text(), op, &rule)?
                }
            } else {
                let mut atoms = Vec::new();
                reduced.atoms(&mut atoms);
                target.atoms(&mut atoms);
                if atoms.len() > 2 {
                    return None;
                }
                self.boolean_cases(&reduced, &target, &atoms)?
            };
            self.boolean_lemmas.insert(key, proof.clone());
            proof
        };
        Some((target, self.chain(changed, simple)?))
    }
}

fn simple_boolean(op: &str, args: &[&str]) -> Option<String> {
    match (op, args) {
        ("and", [a, b]) if *a == "false" || *b == "false" => Some("false".into()),
        ("and", [a, b]) if *a == "true" || a == b => Some((*b).into()),
        ("and", [a, "true"]) => Some((*a).into()),
        ("or", [a, b]) if *a == "true" || *b == "true" => Some("true".into()),
        ("or", [a, b]) if *a == "false" || a == b => Some((*b).into()),
        ("or", [a, "false"]) => Some((*a).into()),
        ("xor", ["false", b]) | ("xor", [b, "false"]) => Some((*b).into()),
        ("xor", ["true", b]) | ("xor", [b, "true"]) => Some(negated(b)),
        ("xor", [a, b]) if a == b => Some("false".into()),
        ("not", [a]) if matches!(*a, "true" | "false") || a.starts_with("(not ") => {
            Some(negated(a))
        }
        _ => None,
    }
}

fn negated(term: &str) -> String {
    match term {
        "true" => "false".into(),
        "false" => "true".into(),
        _ => term
            .strip_prefix("(not ")
            .and_then(|s| s.strip_suffix(')'))
            .map_or_else(|| format!("(not {term})"), str::to_owned),
    }
}
