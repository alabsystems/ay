// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) struct Meter<'a, 'terms> {
    pub printer: &'a AlethePrinter<'terms>,
    remaining: u64,
    nodes: usize,
}

impl<'a, 'terms> Meter<'a, 'terms> {
    pub fn new(printer: &'a AlethePrinter<'terms>) -> Self {
        Self {
            printer,
            remaining: MAX_WORK,
            nodes: MAX_NODES,
        }
    }

    pub fn spend(&mut self, work: u64) -> Option<()> {
        self.printer.charge(work);
        self.remaining = self.remaining.checked_sub(work)?;
        (!self.printer.work_budget_exhausted()).then_some(())
    }
}

#[derive(Clone)]
pub(super) struct Node {
    pub text: String,
    pub head: Option<String>,
    pub args: Vec<Node>,
    storage: usize,
}

impl Node {
    pub fn parse(text: &str, depth: usize, meter: &mut Meter<'_, '_>) -> Option<Self> {
        meter.nodes = meter.nodes.checked_sub(1)?;
        meter.spend((text.len().checked_mul(3)? + 64) as u64)?;
        if depth > MAX_DEPTH {
            return None;
        }
        if !text.starts_with('(') {
            let parts = split_smt_term_slices_bounded(text, 1, MAX_INPUT).ok()?;
            return (parts.len() == 1 && parts[0] == text).then(|| Self {
                text: text.to_owned(),
                head: None,
                args: Vec::new(),
                storage: text.len() + 64,
            });
        }
        let inner = text.strip_prefix('(')?.strip_suffix(')')?;
        let parts = split_smt_term_slices_bounded(inner, MAX_NODES, MAX_INPUT).ok()?;
        let (head, arguments) = parts.split_first()?;
        if matches!(
            *head,
            "forall" | "exists" | "let" | "lambda" | "choice" | "match"
        ) {
            return None;
        }
        let args = arguments
            .iter()
            .map(|s| Self::parse(s, depth + 1, meter))
            .collect::<Option<Vec<_>>>()?;
        let storage = args.iter().try_fold(text.len() + head.len() + 64, |n, a| {
            n.checked_add(a.storage)
        })?;
        Some(Self {
            text: text.to_owned(),
            head: Some((*head).to_owned()),
            args,
            storage,
        })
    }

    pub fn copy(&self, meter: &mut Meter<'_, '_>) -> Option<Self> {
        meter.spend(self.storage as u64)?;
        Some(self.clone())
    }

    pub fn atom(text: &str, meter: &mut Meter<'_, '_>) -> Option<Self> {
        meter.spend((text.len() + 64) as u64)?;
        Some(Self {
            text: text.to_owned(),
            head: None,
            args: Vec::new(),
            storage: text.len() + 64,
        })
    }

    pub fn app(head: &str, args: Vec<Self>, meter: &mut Meter<'_, '_>) -> Option<Self> {
        let bytes = args
            .iter()
            .try_fold(head.len() + 2, |n, a| n.checked_add(a.text.len() + 1))?;
        meter.spend((bytes + head.len() + 64) as u64)?;
        if bytes > MAX_INPUT {
            return None;
        }
        let mut text = String::with_capacity(bytes);
        text.push('(');
        text.push_str(head);
        for arg in &args {
            text.push(' ');
            text.push_str(&arg.text);
        }
        text.push(')');
        let storage = args
            .iter()
            .try_fold(bytes + head.len() + 64, |n, a| n.checked_add(a.storage))?;
        Some(Self {
            text,
            head: Some(head.to_owned()),
            args,
            storage,
        })
    }

    pub fn unary(&self, head: &str) -> Option<&Self> {
        (self.head.as_deref() == Some(head) && self.args.len() == 1).then(|| &self.args[0])
    }
}
