// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Printing a planned link of the closed-spelling chain repair as checked
//! steps, for the chain itself and for the printed-resolution pivot bridge.

use super::{plan_link, Plan, MAX_BRIDGE_WORK};
use crate::alethe_printer::parse_printed_bitvec_literal;
use std::fmt::Write as _;

/// The rule proving one bridge link. Each wire spelling is a fixed `:rule`
/// literal, so the wire-rule inventory (`tests/wire_rule_coverage.rs`) reads
/// and probes it; a `:rule {rule}` placeholder would be an unconnected site.
#[derive(Clone, Copy)]
enum LinkRule {
    Evaluate,
    Trans,
    Cong,
    ArraysIdx,
}

impl LinkRule {
    fn wire(self) -> &'static str {
        match self {
            Self::Evaluate => ":rule evaluate",
            Self::Trans => ":rule trans",
            Self::Cong => ":rule cong",
            Self::ArraysIdx => ":rule arrays_idx",
        }
    }
}

pub(super) struct Emitter<'a> {
    pub(super) id: &'a str,
    pub(super) next: usize,
    pub(super) out: String,
}

impl Emitter<'_> {
    fn equality(&mut self, left: &str, right: &str, rule: LinkRule, premises: &[String]) -> String {
        let name = format!("{}.gb{}", self.id, self.next);
        self.next += 1;
        let _ = write!(
            self.out,
            "(step {name} (cl (= {left} {right})) {}",
            rule.wire()
        );
        if !premises.is_empty() {
            let _ = write!(self.out, " :premises ({})", premises.join(" "));
        }
        self.out.push_str(")\n");
        name
    }

    /// Emit `plan`; the proved equality as `(step, left, right)`.
    pub(super) fn emit(&mut self, plan: &Plan<'_>) -> Option<(String, String, String)> {
        match plan {
            Plan::Same => None,
            Plan::Eval { left, right, value } => {
                // `evaluate` proves `(= term value)` with the value on the
                // right, so orient each evaluated side against a literal.
                if parse_printed_bitvec_literal(right).is_some() {
                    let step = self.equality(left, right, LinkRule::Evaluate, &[]);
                    Some((step, (*left).to_string(), (*right).to_string()))
                } else if parse_printed_bitvec_literal(left).is_some() {
                    let step = self.equality(right, left, LinkRule::Evaluate, &[]);
                    Some((step, (*right).to_string(), (*left).to_string()))
                } else {
                    let literal = format!("(_ bv{} {})", value.0, value.1);
                    let first = self.equality(left, &literal, LinkRule::Evaluate, &[]);
                    let second = self.equality(right, &literal, LinkRule::Evaluate, &[]);
                    let step = self.equality(left, right, LinkRule::Trans, &[first, second]);
                    Some((step, (*left).to_string(), (*right).to_string()))
                }
            }
            Plan::Cong { left, right, args } => {
                let mut premises = Vec::new();
                for arg in args {
                    if !matches!(arg, Plan::Same) {
                        premises.push(self.emit(arg)?.0);
                    }
                }
                let step = self.equality(left, right, LinkRule::Cong, &premises);
                Some((step, (*left).to_string(), (*right).to_string()))
            }
            Plan::ReadOverWrite {
                read,
                element,
                other,
                link,
            } => {
                let step = match link {
                    None => self.equality(read, other, LinkRule::ArraysIdx, &[]),
                    Some(link) => {
                        let read_back = self.equality(read, element, LinkRule::ArraysIdx, &[]);
                        let (element_link, _, _) = self.emit(link)?;
                        self.equality(read, other, LinkRule::Trans, &[read_back, element_link])
                    }
                };
                Some((step, (*read).to_string(), (*other).to_string()))
            }
        }
    }
}

/// A checked derivation of `(= left right)` (or its mirror) between two
/// printed spellings of one term, for a consumer outside the chain repair.
pub(in crate::alethe_printer) struct BridgedEquality {
    /// The steps, each ending in a newline; the last one is `step`.
    pub(in crate::alethe_printer) steps: String,
    /// The id of the step concluding the equality.
    pub(in crate::alethe_printer) step: String,
    /// `true` when that step concludes `(= right left)`.
    pub(in crate::alethe_printer) mirrored: bool,
}

/// [`BridgedEquality`] between `left` and `right` from the same planner and
/// emitter the chain repair uses, under step ids `{id}.gb{n}`; `None` when the
/// two texts are one term to carcara already or no supported link joins them.
pub(in crate::alethe_printer) fn bridged_printed_equality(
    id: &str,
    left: &str,
    right: &str,
) -> Option<BridgedEquality> {
    let mut budget = MAX_BRIDGE_WORK;
    let plan = plan_link(left, right, &mut budget)?;
    let mut emitter = Emitter {
        id,
        next: 0,
        out: String::new(),
    };
    let (step, proved_left, proved_right) = emitter.emit(&plan)?;
    let mirrored = match (proved_left == left, proved_right == right) {
        (true, true) => false,
        _ if proved_left == right && proved_right == left => true,
        _ => return None,
    };
    Some(BridgedEquality {
        steps: emitter.out,
        step,
        mirrored,
    })
}
