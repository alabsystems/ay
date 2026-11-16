// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Opt-in observations of the existing search, never proof/search authority.

use std::fmt::Write as _;

use super::*;

/// One bounded diagnostic, independent of (and never returned to) search work.
const MAX_PROBE_GOALS: usize = 32;

struct GoalProbe {
    work: usize,
    rows: usize,
    same: usize,
    truncated: bool,
    text: String,
}

impl Default for GoalProbe {
    fn default() -> Self {
        Self {
            work: goal::MAX_GOAL_WORK,
            rows: 0,
            same: 0,
            truncated: false,
            text: String::new(),
        }
    }
}

impl Executor {
    /// Read only class identities. No term renderer, constructor, recognizer,
    /// path explanation, fact insertion or solver call is allowed here.
    fn ground_goal_probe_leaf(
        &self,
        search: &GroundSearch,
        term: TermId,
        depth: usize,
        probe: &mut GoalProbe,
    ) {
        if probe.truncated {
            return;
        }
        let Some(work) = probe.work.checked_sub(1) else {
            probe.truncated = true;
            return;
        };
        probe.work = work;
        if depth > goal::MAX_GOAL_DEPTH || probe.rows >= MAX_PROBE_GOALS {
            probe.truncated = true;
            return;
        }
        if let Some(body) = self.true_equality_body(term) {
            self.ground_goal_probe_leaf(search, body, depth + 1, probe);
            return;
        }
        if let TermData::App(symbol, args) = self.ctx.terms.get(term) {
            if symbol.name() == "and" {
                for &arg in args {
                    self.ground_goal_probe_leaf(search, arg, depth + 1, probe);
                    if probe.truncated {
                        break;
                    }
                }
                return;
            }
        }
        let Some((lhs, rhs)) = decode_eq_local(&self.ctx.terms, term) else {
            return;
        };
        let sort = self.ctx.terms.sort(lhs);
        if *sort == Sort::Bool {
            return;
        }
        let same_sort = sort == self.ctx.terms.sort(rhs);
        let same = same_sort && search.closure.same_class(lhs, rhs);
        probe.rows += 1;
        probe.same += usize::from(same);
        let name = match self.ctx.terms.get(rhs) {
            TermData::Var(name, _) => name.as_str(),
            TermData::App(symbol, args) if args.is_empty() => symbol.name(),
            _ => "<compound>",
        };
        // A short identity label only; long or non-ASCII source names are not
        // traversed/escaped into arbitrarily large diagnostic strings.
        let name = if name.len() <= 64 && name.is_ascii() {
            name
        } else {
            "<wide-name>"
        };
        let _ = write!(
            probe.text,
            "\n  goal={} lhs={} rhs={} rhs_name={name:?} lhs_class={:?} rhs_class={:?} same_sort={same_sort} same={same}",
            term,
            lhs,
            rhs,
            search.closure.class(lhs),
            search.closure.class(rhs),
        );
    }

    fn ground_goal_class_probe(&self, search: &GroundSearch) -> GoalProbe {
        let mut probe = GoalProbe::default();
        for fact in search.facts.facts() {
            let Some(work) = probe.work.checked_sub(1) else {
                probe.truncated = true;
                break;
            };
            probe.work = work;
            if let TermData::Not(inner) = self.ctx.terms.get(fact.literal) {
                self.ground_goal_probe_leaf(search, *inner, 0, &mut probe);
                if probe.truncated {
                    break;
                }
            }
        }
        probe
    }

    pub(super) fn ground_terminal_probe(
        &self,
        search: &GroundSearch,
        phase: &str,
        disposition: &str,
        round: usize,
        proposals: usize,
        work: usize,
    ) -> String {
        let goals = self.ground_goal_class_probe(search);
        format!(
            "ground terminal disposition={disposition} phase={phase} round={round} shared_work={work} proposals={proposals} nodes={} edges={} facts={} probes={} goals={} same={} truncated={} diagnostic_work={}{}",
            search.closure.nodes().len(),
            search.closure.edges().len(),
            search.facts.facts().len(),
            search.probes,
            goals.rows,
            goals.same,
            goals.truncated,
            goal::MAX_GOAL_WORK - goals.work,
            goals.text,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn diagnostic_observes_all_eleven_goal_classes_without_state_growth() {
        let mut exec = Executor::new();
        let mut search = GroundSearch::default();
        let mut goals = Vec::new();
        for index in 0..11 {
            let lhs = exec
                .ctx
                .terms
                .mk_var(format!("lhs{index}"), Sort::bitvec(64));
            let rhs = exec
                .ctx
                .terms
                .mk_var(format!("rhs{index}"), Sort::bitvec(64));
            search.closure.register(lhs);
            search.closure.register(rhs);
            let equality = exec
                .ctx
                .terms
                .mk_app(Symbol::named("="), [lhs, rhs], Sort::Bool);
            if index < 2 {
                search
                    .closure
                    .merge(lhs, rhs, EdgeReason::Authored(equality));
            }
            goals.push(equality);
        }
        let conjunction = exec
            .ctx
            .terms
            .mk_app(Symbol::named("and"), goals, Sort::Bool);
        let root = exec.ctx.terms.mk_not_raw(conjunction);
        exec.seed_ground_root_facts(&mut search, &[root]).unwrap();
        let before = (
            exec.ctx.terms.len(),
            search.closure.nodes().len(),
            search.closure.edges().len(),
            search.facts.facts().len(),
            search.probes,
        );
        let probe = exec.ground_goal_class_probe(&search);
        assert_eq!((probe.rows, probe.same, probe.truncated), (11, 2, false));
        assert_eq!(
            before,
            (
                exec.ctx.terms.len(),
                search.closure.nodes().len(),
                search.closure.edges().len(),
                search.facts.facts().len(),
                search.probes
            )
        );
        assert!(exec.last_proof.is_none());
        assert_eq!(exec.last_proof_raw_original_assertions, [] as [TermId; 0]);
    }
}
