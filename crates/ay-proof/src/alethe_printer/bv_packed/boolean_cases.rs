// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Small Boolean identities proved by exhaustive, discharged cases.

use super::*;

#[derive(Clone)]
pub(super) enum Boolean {
    Atom(String),
    Constant(bool),
    Apply(&'static str, Vec<Boolean>),
}

impl Boolean {
    pub(super) fn term(text: &str) -> Self {
        match text {
            "true" => Self::Constant(true),
            "false" => Self::Constant(false),
            _ => Self::parse_application(text).unwrap_or_else(|| Self::Atom(text.into())),
        }
    }

    fn parse_application(text: &str) -> Option<Self> {
        for op in ["not", "and", "or", "xor"] {
            if let Some(inner) = text
                .strip_prefix(&format!("({op} "))
                .and_then(|s| s.strip_suffix(')'))
            {
                if op == "not" {
                    return Some(Self::Apply(op, vec![Self::term(inner)]));
                }
                let mut depth = 0usize;
                for (i, ch) in inner.char_indices() {
                    match ch {
                        '(' => depth += 1,
                        ')' => depth = depth.checked_sub(1)?,
                        ' ' if depth == 0 => {
                            return Some(Self::Apply(
                                op,
                                vec![Self::term(&inner[..i]), Self::term(&inner[i + 1..])],
                            ))
                        }
                        _ => {}
                    }
                }
            }
        }
        None
    }

    pub(super) fn app(op: &'static str, args: impl IntoIterator<Item = Self>) -> Self {
        Self::Apply(op, args.into_iter().collect())
    }

    pub(super) fn text(&self) -> String {
        match self {
            Self::Atom(text) => text.clone(),
            Self::Constant(value) => value.to_string(),
            Self::Apply(op, args) => {
                let args: Vec<_> = args.iter().map(Self::text).collect();
                application(op, args.iter().map(String::as_str))
            }
        }
    }

    pub(super) fn atoms(&self, atoms: &mut Vec<String>) {
        match self {
            Self::Atom(text) if !atoms.contains(text) => atoms.push(text.clone()),
            Self::Apply(_, args) => args.iter().for_each(|arg| arg.atoms(atoms)),
            _ => {}
        }
    }

    fn evaluate(&self) -> Option<bool> {
        match self {
            Self::Constant(value) => Some(*value),
            Self::Apply(op, args) => {
                let args = args
                    .iter()
                    .map(Self::evaluate)
                    .collect::<Option<Vec<_>>>()?;
                match (*op, args.as_slice()) {
                    ("not", [a]) => Some(!a),
                    ("and", [a, b]) => Some(*a && *b),
                    ("or", [a, b]) => Some(*a || *b),
                    ("xor", [a, b]) => Some(a ^ b),
                    _ => None,
                }
            }
            _ => None,
        }
    }
}

impl PackedProof<'_, '_> {
    pub(super) fn boolean_identity(&mut self, left: Boolean, right: Boolean) -> Option<Equality> {
        let key = (left.text(), right.text());
        if let Some(equality) = self.boolean_lemmas.get(&key) {
            return Some(equality.clone());
        }
        let mut atoms = Vec::new();
        left.atoms(&mut atoms);
        right.atoms(&mut atoms);
        if atoms.len() > 2 {
            return None;
        }
        let (left, first) = self.boolean_reduce(&left)?;
        let (right, last) = self.boolean_reduce(&right)?;
        let middle = self.boolean_cases(&left, &right, &atoms)?;
        let reverse = self.equality(&last.right, &last.left, "symm", &[&last.step])?;
        let equality = self.chain(first, middle)?;
        let equality = self.chain(equality, reverse)?;
        // Only fully discharged lemmas are reusable outside their anchor.
        self.boolean_lemmas.insert(key, equality.clone());
        Some(equality)
    }

    pub(super) fn boolean_cases(
        &mut self,
        left: &Boolean,
        right: &Boolean,
        atoms: &[String],
    ) -> Option<Equality> {
        if left.text() == right.text() {
            return self.equality(&left.text(), &right.text(), "refl", &[]);
        }
        if let Some((atom, remaining)) = atoms.split_first() {
            let yes = self.boolean_case(left, right, atom, remaining, true)?;
            let no = self.boolean_case(left, right, atom, remaining, false)?;
            return self.equality(&left.text(), &right.text(), "resolution", &[&yes, &no]);
        }
        let value = left.evaluate()?;
        if value != right.evaluate()? {
            return None;
        }
        let value = value.to_string();
        let first = self.equality(&left.text(), &value, "evaluate", &[])?;
        let last = self.equality(&right.text(), &value, "evaluate", &[])?;
        let reverse = self.equality(&value, &last.left, "symm", &[&last.step])?;
        self.chain(first, reverse)
    }

    fn boolean_case(
        &mut self,
        left: &Boolean,
        right: &Boolean,
        atom: &str,
        remaining: &[String],
        positive: bool,
    ) -> Option<String> {
        let end = self.fresh();
        let assumption = self.fresh();
        let literal = if positive {
            atom.into()
        } else {
            format!("(not {atom})")
        };
        self.append(&format!(
            "(anchor :step {end})\n(assume {assumption} {literal})\n"
        ))?;
        let equation = format!("(= {atom} {positive})");
        let simple = self.equality(&equation, &literal, "equiv_simplify", &[])?;
        let implication = self.step(
            &format!("{equation} (not {literal})"),
            "equiv2",
            &[&simple.step],
        )?;
        let unit = self.step(&equation, "resolution", &[&implication, &assumption])?;
        let replacement = Equality {
            left: atom.into(),
            right: positive.to_string(),
            step: unit,
        };
        let (new_left, first) = self.boolean_substitute(left, &replacement, positive)?;
        let (new_right, last) = self.boolean_substitute(right, &replacement, positive)?;
        let middle = self.boolean_cases(&new_left, &new_right, remaining)?;
        let reverse = self.equality(&last.right, &last.left, "symm", &[&last.step])?;
        let equality = self.chain(first, middle)?;
        let equality = self.chain(equality, reverse)?;
        self.named_step(
            &end,
            &format!(
                "(not {literal}) (= {} {})",
                self.spelling(&equality.left),
                self.spelling(&equality.right)
            ),
            "subproof",
            &[],
            &format!(" :discharge ({assumption})"),
        )?;
        Some(end)
    }

    fn boolean_substitute(
        &mut self,
        term: &Boolean,
        replacement: &Equality,
        value: bool,
    ) -> Option<(Boolean, Equality)> {
        match term {
            Boolean::Atom(atom) if atom == &replacement.left => {
                Some((Boolean::Constant(value), replacement.clone()))
            }
            Boolean::Apply(op, args) => {
                let mut children = Vec::new();
                let mut proofs = Vec::new();
                for arg in args {
                    let (child, proof) = self.boolean_substitute(arg, replacement, value)?;
                    children.push(child);
                    if proof.left != proof.right {
                        proofs.push(proof);
                    }
                }
                let result = Boolean::Apply(op, children);
                let references: Vec<_> = proofs.iter().map(|p| p.step.as_str()).collect();
                let rule = if references.is_empty() {
                    "refl"
                } else {
                    "cong"
                };
                let equality = self.equality(&term.text(), &result.text(), rule, &references)?;
                Some((result, equality))
            }
            _ => Some((
                term.clone(),
                self.equality(&term.text(), &term.text(), "refl", &[])?,
            )),
        }
    }
}
