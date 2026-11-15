// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

impl Circuit<'_, '_, '_> {
    pub(super) fn atom(&mut self, text: &str) -> Option<i32> {
        if let Some(inner) = text.strip_prefix("(not ").and_then(|s| s.strip_suffix(')')) {
            if let Some(&id) = self.nodes.get(inner) {
                return Some(-id);
            }
        }
        if let Some(&index) = self.nodes.get(text) {
            return Some(index);
        }
        if self.atoms.len() >= MAX_VARIABLES {
            return None;
        }
        self.atoms.push(text.into());
        let id = i32::try_from(self.atoms.len()).ok()?;
        self.nodes.insert(text.into(), id);
        if matches!(text, "true" | "false") {
            let positive = text == "true";
            let value = if positive { "true" } else { "(not false)" };
            let step = self.proof.step(value, text, &[])?;
            self.input(vec![if positive { id } else { -id }], step)?;
        }
        Some(id)
    }

    pub(super) fn gate(&mut self, op: &str, args: &[i32]) -> Option<i32> {
        let texts = args
            .iter()
            .map(|&n| self.text(n))
            .collect::<Option<Vec<_>>>()?;
        let source = application(op, texts.iter().map(String::as_str));
        if let Some(&id) = self.nodes.get(&source) {
            return Some(id);
        }
        if self.atoms.len() >= MAX_VARIABLES || args.is_empty() {
            return None;
        }
        let name = self.proof.define_term(&source, "Bool")?;
        self.atoms.push(name.clone());
        let n = i32::try_from(self.atoms.len()).ok()?;
        self.nodes.insert(source.clone(), n);
        self.nodes.insert(name.clone(), n);
        let not_name = format!("(not {name})");
        let nots = texts
            .iter()
            .map(|s| format!("(not {s})"))
            .collect::<Vec<_>>();
        match op {
            "not" => self.negation_gate(args, n, &source)?,
            "and" => {
                for (i, &arg) in args.iter().enumerate() {
                    self.clause(
                        &[-n, arg],
                        &[not_name.clone(), texts[i].clone()],
                        "and_pos",
                        &format!(" :args ({i})"),
                    )?;
                }
                let clause = std::iter::once(n)
                    .chain(args.iter().map(|x| -x))
                    .collect::<Vec<_>>();
                let text = std::iter::once(name).chain(nots).collect::<Vec<_>>();
                self.clause(&clause, &text, "and_neg", "")?;
            }
            "or" => {
                let clause = std::iter::once(-n)
                    .chain(args.iter().copied())
                    .collect::<Vec<_>>();
                let text = std::iter::once(not_name)
                    .chain(texts.iter().cloned())
                    .collect::<Vec<_>>();
                self.clause(&clause, &text, "or_pos", "")?;
                for (i, &arg) in args.iter().enumerate() {
                    self.clause(
                        &[n, -arg],
                        &[name.clone(), nots[i].clone()],
                        "or_neg",
                        &format!(" :args ({i})"),
                    )?;
                }
            }
            "ite" => {
                let [c, yes, no] = args else { return None };
                self.clause(
                    &[-n, *c, *no],
                    &[not_name.clone(), texts[0].clone(), texts[2].clone()],
                    "ite_pos1",
                    "",
                )?;
                self.clause(
                    &[-n, -c, *yes],
                    &[not_name, nots[0].clone(), texts[1].clone()],
                    "ite_pos2",
                    "",
                )?;
                self.clause(
                    &[n, *c, -no],
                    &[name.clone(), texts[0].clone(), nots[2].clone()],
                    "ite_neg1",
                    "",
                )?;
                self.clause(
                    &[n, -c, -yes],
                    &[name, nots[0].clone(), nots[1].clone()],
                    "ite_neg2",
                    "",
                )?;
            }
            "xor" | "=" => self.binary_gate_clauses(op, args, n, &texts)?,
            _ => return None,
        }
        Some(n)
    }

    fn negation_gate(&mut self, args: &[i32], n: i32, source: &str) -> Option<()> {
        let [arg] = args else { return None };
        let name = self.text(n)?;
        let eq = self.proof.equality(&name, source, "refl", &[])?;
        let forward = self
            .proof
            .step(&format!("(not {name}) {source}"), "equiv1", &[&eq.step])?;
        self.input(vec![-n, -*arg], forward)?;
        let backward = self
            .proof
            .step(&format!("{name} (not {source})"), "equiv2", &[&eq.step])?;
        // As with binary gates, preserve the rule's exact double negations.
        self.input(vec![n, *arg], backward)
    }

    fn binary_gate_clauses(
        &mut self,
        op: &str,
        args: &[i32],
        n: i32,
        texts: &[String],
    ) -> Option<()> {
        let name = self.text(n)?;
        let not_name = format!("(not {name})");
        let nots = texts
            .iter()
            .map(|text| format!("(not {text})"))
            .collect::<Vec<_>>();

        let [a, b] = args else { return None };
        let (rules, rows): ([&str; 4], [[i32; 3]; 4]) = if op == "xor" {
            (
                ["xor_pos1", "xor_pos2", "xor_neg1", "xor_neg2"],
                [[-n, *a, *b], [-n, -a, -b], [n, *a, -b], [n, -a, *b]],
            )
        } else {
            (
                ["equiv_pos1", "equiv_pos2", "equiv_neg1", "equiv_neg2"],
                [[-n, *a, -b], [-n, -a, *b], [n, -a, -b], [n, *a, *b]],
            )
        };
        // Keep the exact rule topology, including syntactic double
        // negations when a gate input already has negative polarity.
        let choices = if op == "xor" {
            [[true, true], [false, false], [true, false], [false, true]]
        } else {
            [[true, false], [false, true], [false, false], [true, true]]
        };
        for (i, row) in rows.iter().enumerate() {
            let text = vec![
                if row[0] < 0 {
                    not_name.clone()
                } else {
                    name.clone()
                },
                if choices[i][0] {
                    texts[0].clone()
                } else {
                    nots[0].clone()
                },
                if choices[i][1] {
                    texts[1].clone()
                } else {
                    nots[1].clone()
                },
            ];
            self.clause(row, &text, rules[i], "")?;
        }
        Some(())
    }

    fn clause(&mut self, clause: &[i32], text: &[String], rule: &str, extra: &str) -> Option<()> {
        if clause.iter().any(|lit| clause.contains(&-lit)) {
            return Some(());
        }
        let id = self.proof.fresh();
        self.proof
            .named_step(&id, &text.join(" "), rule, &[], extra)?;
        let (id, text) = self.respell_duplicates(clause, text, id)?;
        let mut unique = Vec::new();
        let mut words: Vec<String> = Vec::new();
        for (&lit, word) in clause.iter().zip(&text) {
            match unique.iter().position(|&seen| seen == lit) {
                // `contraction` drops only a literal printed the same way.
                Some(at) if words[at] == *word => {}
                Some(_) => return None,
                None => {
                    unique.push(lit);
                    words.push(word.clone());
                }
            }
        }
        let id = if unique.len() != clause.len() {
            self.proof.step(&words.join(" "), "contraction", &[&id])?
        } else {
            id
        };
        self.input(unique, id)
    }

    /// A gate rule spells each input as written, so one literal can appear
    /// twice in two spellings: `(= (not p) q)` with `p` and `q` the same
    /// atom `x` gives `equiv_pos2`'s `(not (not x))` beside `q`'s `x`. The
    /// two are one literal, but `contraction` is syntactic and keeps both.
    /// Each `(not (not x))` of such a literal is rewritten to `x` by a
    /// `not_not` step and one resolution, so `clause` can contract it. A
    /// clause without such a pair is returned as it is, and so is its step.
    fn respell_duplicates(
        &mut self,
        clause: &[i32],
        text: &[String],
        id: String,
    ) -> Option<(String, Vec<String>)> {
        let respelled = |i: usize| {
            clause
                .iter()
                .zip(text)
                .any(|(&lit, word)| lit == clause[i] && *word != text[i])
        };
        let mut words = text.to_vec();
        let mut premises = vec![id.clone()];
        let mut bridged: Vec<&str> = Vec::new();
        for i in 0..clause.len() {
            if !respelled(i) {
                continue;
            }
            let plain = self.text(clause[i])?;
            if text[i] == plain {
                continue;
            }
            // The only other spelling a gate prints is the double negation.
            if text[i] != format!("(not (not {plain}))") {
                return None;
            }
            // One bridge per spelling: a second would find no pivot left.
            if !bridged.contains(&text[i].as_str()) {
                bridged.push(&text[i]);
                premises.push(self.proof.step(
                    &format!("(not {}) {plain}", text[i]),
                    "not_not",
                    &[],
                )?);
            }
            words[i] = plain;
        }
        if premises.len() == 1 {
            return Some((id, words));
        }
        let premises = premises.iter().map(String::as_str).collect::<Vec<_>>();
        let id = self.proof.step(&words.join(" "), "resolution", &premises)?;
        Some((id, words))
    }
}
