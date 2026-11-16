// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) struct Derivation<'a, 'terms> {
    pub meter: Meter<'a, 'terms>,
    pub output: String,
    prefix: String,
    next: usize,
}

impl<'a, 'terms> Derivation<'a, 'terms> {
    pub(super) fn new(id: ProofId, meter: Meter<'a, 'terms>) -> Self {
        Self {
            meter,
            output: String::new(),
            prefix: format!("{id}.subst"),
            next: 0,
        }
    }

    pub(super) fn same(&mut self, a: &str, b: &str) -> Option<bool> {
        self.meter.spend(a.len().min(b.len()) as u64 + 1)?;
        Some(a == b)
    }

    fn fresh(&mut self) -> Option<String> {
        self.meter.spend(64)?;
        if self.next >= 4096 {
            return None;
        }
        let label = format!("{}.{}", self.prefix, self.next);
        self.next += 1;
        Some(label)
    }

    pub(super) fn append(&mut self, text: &str) -> Option<()> {
        self.meter.spend(text.len() as u64)?;
        if self.output.len().checked_add(text.len())? > MAX_OUTPUT {
            return None;
        }
        self.output.push_str(text);
        Some(())
    }

    pub(super) fn assume(&mut self, text: &str) -> Option<String> {
        self.meter.spend(text.len() as u64 + 128)?;
        let label = self.fresh()?;
        self.append(&format!("(assume {label} {text})\n"))?;
        Some(label)
    }

    pub(super) fn step(&mut self, clause: &str, rule: &str, premises: &[String]) -> Option<String> {
        let rule = CheckableRule::new(rule)?;
        self.step_with_rule(clause, rule, premises)
    }

    fn step_with_rule(
        &mut self,
        clause: &str,
        rule: CheckableRule,
        premises: &[String],
    ) -> Option<String> {
        let bytes = premises
            .iter()
            .try_fold(clause.len() + rule.as_str().len() + 128, |n, p| {
                n.checked_add(p.len() + 1)
            })?;
        self.meter.spend(bytes as u64)?;
        let label = self.fresh()?;
        let suffix = if premises.is_empty() {
            String::new()
        } else {
            format!(" :premises ({})", premises.join(" "))
        };
        self.append(&format!(
            "(step {label} (cl {clause}) :rule {rule}{suffix})\n"
        ))?;
        Some(label)
    }

    pub(super) fn eq(
        &mut self,
        a: &str,
        b: &str,
        rule: &str,
        premises: &[String],
    ) -> Option<String> {
        self.meter
            .spend((a.len().checked_add(b.len())? + 8) as u64)?;
        self.step(&format!("(= {a} {b})"), rule, premises)
    }

    pub(super) fn substitute_pinned(
        &mut self,
        source: &Node,
        pins: &[(&Node, &Node, String)],
    ) -> Option<(Node, Option<String>)> {
        self.meter.spend(1)?;
        for (key, value, label) in pins {
            if self.same(&source.text, &key.text)? {
                self.meter.spend(label.len() as u64)?;
                return Some((value.copy(&mut self.meter)?, Some(label.clone())));
            }
        }
        let Some(head) = &source.head else {
            return Some((source.copy(&mut self.meter)?, None));
        };
        let mut args = Vec::new();
        let mut premises = Vec::new();
        for arg in &source.args {
            let (image, proof) = self.substitute_pinned(arg, pins)?;
            args.push(image);
            premises.extend(proof);
        }
        let result = Node::app(head, args, &mut self.meter)?;
        let proof = if premises.is_empty() {
            None
        } else {
            Some(self.eq(&source.text, &result.text, "cong", &premises)?)
        };
        Some((result, proof))
    }

    /// Every change produces an equality, including changes below an operator.
    /// Integer order normalization is deliberately left to a separate checked
    /// arithmetic derivation; it is never guessed from printed operand names.
    pub(super) fn normalize(&mut self, source: &Node) -> Option<(Node, Option<String>)> {
        self.meter.spend(1)?;
        let Some(head) = &source.head else {
            return Some((source.copy(&mut self.meter)?, None));
        };
        let mut args = Vec::new();
        let mut premises = Vec::new();
        for arg in &source.args {
            let (normal, proof) = self.normalize(arg)?;
            args.push(normal);
            premises.extend(proof);
        }
        let rebuilt = Node::app(head, args, &mut self.meter)?;
        let mut chain = Vec::new();
        if !premises.is_empty() {
            chain.push(self.eq(&source.text, &rebuilt.text, "cong", &premises)?);
        }
        let (normal, rules) = self.fold(&rebuilt)?;
        chain.extend(rules);
        let proof = match chain.len() {
            0 => None,
            1 => chain.pop(),
            _ => Some(self.eq(&source.text, &normal.text, "trans", &chain)?),
        };
        Some((normal, proof))
    }

    fn fold(&mut self, source: &Node) -> Option<(Node, Vec<String>)> {
        let head = source.head.as_deref()?;
        if matches!(head, "and" | "or") {
            return self.junction(source, head == "or");
        }
        let (target, rule) = match (head, source.args.as_slice()) {
            ("=", [a, b]) if self.same(&a.text, &b.text)? => {
                (Node::atom("true", &mut self.meter)?, "eq_simplify")
            }
            ("not", [a]) if a.text == "true" => {
                (Node::atom("false", &mut self.meter)?, "not_simplify")
            }
            ("not", [a]) if a.text == "false" => {
                (Node::atom("true", &mut self.meter)?, "not_simplify")
            }
            ("not", [a]) if a.unary("not").is_some() => {
                (a.unary("not")?.copy(&mut self.meter)?, "not_simplify")
            }
            ("ite", [c, t, _]) if c.text == "true" => (t.copy(&mut self.meter)?, "ite_simplify"),
            ("ite", [c, _, e]) if c.text == "false" => (e.copy(&mut self.meter)?, "ite_simplify"),
            _ => return Some((source.copy(&mut self.meter)?, Vec::new())),
        };
        let proof = self.eq(&source.text, &target.text, rule, &[])?;
        Some((target, vec![proof]))
    }

    fn junction(&mut self, source: &Node, is_or: bool) -> Option<(Node, Vec<String>)> {
        let (identity, absorber, rule, head) = if is_or {
            ("false", "true", "or_simplify", "or")
        } else {
            ("true", "false", "and_simplify", "and")
        };
        let mut kept = Vec::new();
        for arg in &source.args {
            if self.same(&arg.text, absorber)? {
                let target = Node::atom(absorber, &mut self.meter)?;
                let proof = self.eq(&source.text, &target.text, rule, &[])?;
                return Some((target, vec![proof]));
            }
            if !self.same(&arg.text, identity)? {
                kept.push(arg.copy(&mut self.meter)?);
            }
        }
        let mut chain = Vec::new();
        let target = match kept.len() {
            0 => Node::atom(identity, &mut self.meter)?,
            1 => {
                // The checker removes identity operands and singleton wrappers
                // separately when the surviving operand has the same operator.
                if source.args.len() > 1 && kept[0].head.as_deref() == Some(head) {
                    let singleton =
                        Node::app(head, vec![kept[0].copy(&mut self.meter)?], &mut self.meter)?;
                    chain.push(self.eq(&source.text, &singleton.text, rule, &[])?);
                    chain.push(self.eq(&singleton.text, &kept[0].text, rule, &[])?);
                }
                kept.pop()?
            }
            _ => Node::app(head, kept, &mut self.meter)?,
        };
        if chain.is_empty() && !self.same(&source.text, &target.text)? {
            chain.push(self.eq(&source.text, &target.text, rule, &[])?);
        }
        Some((target, chain))
    }
}
