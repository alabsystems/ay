// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact constant propagation for large systems of string word equations.
//!
//! The Nielsen pre-pass is intentionally capped because its search is
//! exponential.  This pass complements it with three polynomial, refutational
//! rules over a larger entailed equation set:
//!
//! 1. A ground side uniquely determines the only remaining variable on the
//!    other side, including repeated occurrences of that variable.
//! 2. A ground side cannot be shorter than the constants on the other side.
//! 3. Determined leading or trailing constant blocks cannot disagree.
//!
//! Every substitution is entailed by an asserted equation, and the pass only
//! returns `Unsat` after finding a contradiction.  It never returns `Sat`.
//! Resource exhaustion, allocation failure, interrupt, timeout, or failure to
//! reach a fixpoint all fail open to the ordinary string pipeline.  Proof mode
//! also bypasses the pass: until these deductions have proof reconstruction,
//! they must not originate an uncertified `Unsat` result.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, Symbol, TermData, TermId};
use ay_core::Sort;
use ay_frontend::OptionValue;

use crate::executor_types::{Result, SolveResult};

use super::super::Executor;

/// Production limits are deterministic and deliberately independent of the
/// host machine.  The cumulative expansion caps bound allocations even when a
/// large forced value occurs in many equations or rounds.
#[derive(Clone, Copy)]
struct PropLimits {
    max_equations: usize,
    max_closure_literals: usize,
    max_source_chars: usize,
    max_total_elements: usize,
    max_expanded_chars: usize,
    max_work: usize,
    max_rounds: usize,
    max_depth: usize,
}

const DEFAULT_LIMITS: PropLimits = PropLimits {
    max_equations: 4096,
    max_closure_literals: 1 << 15,
    max_source_chars: 1 << 20,
    max_total_elements: 1 << 21,
    max_expanded_chars: 1 << 24,
    max_work: 1 << 26,
    max_rounds: 64,
    max_depth: 64,
};

/// Monotone accounting for one invocation.  Counts are cumulative rather than
/// live-set estimates, so repeated substitutions cannot evade the limits.
struct PropBudget {
    limits: PropLimits,
    source_chars: usize,
    total_elements: usize,
    expanded_chars: usize,
    work: usize,
}

impl PropBudget {
    fn new(limits: PropLimits) -> Self {
        Self {
            limits,
            source_chars: 0,
            total_elements: 0,
            expanded_chars: 0,
            work: 0,
        }
    }

    fn charge(counter: &mut usize, amount: usize, limit: usize) -> Option<()> {
        let next = counter.checked_add(amount)?;
        if next > limit {
            return None;
        }
        *counter = next;
        Some(())
    }

    fn charge_source_chars(&mut self, amount: usize) -> Option<()> {
        Self::charge(&mut self.source_chars, amount, self.limits.max_source_chars)
    }

    fn charge_elements(&mut self, amount: usize) -> Option<()> {
        Self::charge(
            &mut self.total_elements,
            amount,
            self.limits.max_total_elements,
        )
    }

    fn charge_expanded_chars(&mut self, amount: usize) -> Option<()> {
        Self::charge(
            &mut self.expanded_chars,
            amount,
            self.limits.max_expanded_chars,
        )
    }

    fn charge_work(&mut self, amount: usize) -> Option<()> {
        Self::charge(&mut self.work, amount, self.limits.max_work)
    }
}

/// One element of a flattened word: a ground block or a variable occurrence.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Elem {
    Const(Vec<char>),
    Var(TermId),
}

/// A flattened word equation `lhs = rhs`.
#[derive(Clone)]
struct PropEq {
    lhs: Vec<Elem>,
    rhs: Vec<Elem>,
}

/// Outcome of one inference step over a single equation.
enum Step {
    Conflict,
    Forced(TermId, Vec<char>),
    Inert,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PropOutcome {
    Conflict,
    Inconclusive,
    Limited,
    Aborted,
}

enum FlattenOutcome {
    Word(Vec<Elem>),
    Unsupported,
    Limited,
}

fn append_chars(out: &mut Vec<Elem>, chars: &[char]) -> Option<()> {
    if chars.is_empty() {
        return Some(());
    }
    if let Some(Elem::Const(previous)) = out.last_mut() {
        previous.try_reserve(chars.len()).ok()?;
        previous.extend_from_slice(chars);
        return Some(());
    }
    let mut copied = Vec::new();
    copied.try_reserve(chars.len()).ok()?;
    copied.extend_from_slice(chars);
    out.try_reserve(1).ok()?;
    out.push(Elem::Const(copied));
    Some(())
}

fn append_string(out: &mut Vec<Elem>, value: &str, budget: &mut PropBudget) -> Option<()> {
    // Do not traverse an arbitrarily large source constant merely to discover
    // that it exceeds the cap. One character beyond the remaining allowance
    // is enough to decline the pass.
    let remaining = budget
        .limits
        .max_source_chars
        .checked_sub(budget.source_chars)?;
    let probe = remaining.checked_add(1)?;
    let char_count = value.chars().take(probe).count();
    if char_count > remaining {
        return None;
    }
    budget.charge_source_chars(char_count)?;
    // One scan counted the characters and one copies them into the flat word.
    budget.charge_work(char_count.checked_mul(2)?.checked_add(1)?)?;
    if char_count == 0 {
        return Some(());
    }
    if let Some(Elem::Const(previous)) = out.last_mut() {
        previous.try_reserve(char_count).ok()?;
        previous.extend(value.chars());
        return Some(());
    }
    budget.charge_elements(1)?;
    let mut copied = Vec::new();
    copied.try_reserve(char_count).ok()?;
    copied.extend(value.chars());
    out.try_reserve(1).ok()?;
    out.push(Elem::Const(copied));
    Some(())
}

/// Substitute forced values and normalize neighbouring constants.  The entire
/// output shape is charged before any character copying begins.
fn substitute(
    word: &[Elem],
    env: &HashMap<TermId, Vec<char>>,
    budget: &mut PropBudget,
) -> Option<Vec<Elem>> {
    let mut chars = 0usize;
    for elem in word {
        let len = match elem {
            Elem::Const(value) => value.len(),
            Elem::Var(var) => env.get(var).map_or(0, Vec::len),
        };
        chars = chars.checked_add(len)?;
    }

    budget.charge_expanded_chars(chars)?;
    // `word.len()` is an upper bound on the normalized output element count.
    budget.charge_elements(word.len())?;
    let element_work = word.len().checked_mul(2)?;
    budget.charge_work(element_work.checked_add(chars)?)?;

    let mut out = Vec::new();
    out.try_reserve(word.len()).ok()?;
    for elem in word {
        match elem {
            Elem::Const(value) => append_chars(&mut out, value)?,
            Elem::Var(var) => match env.get(var) {
                Some(value) => append_chars(&mut out, value)?,
                None => {
                    out.push(Elem::Var(*var));
                }
            },
        }
    }
    Some(out)
}

fn ground(word: &[Elem]) -> Option<&[char]> {
    match word {
        [] => Some(&[]),
        [Elem::Const(value)] => Some(value),
        _ => None,
    }
}

fn leading(word: &[Elem]) -> &[char] {
    match word.first() {
        Some(Elem::Const(value)) => value,
        _ => &[],
    }
}

fn trailing(word: &[Elem]) -> &[char] {
    match word.last() {
        Some(Elem::Const(value)) => value,
        _ => &[],
    }
}

fn const_len(word: &[Elem]) -> Option<usize> {
    word.iter().try_fold(0usize, |sum, elem| {
        let len = match elem {
            Elem::Const(value) => value.len(),
            Elem::Var(_) => 0,
        };
        sum.checked_add(len)
    })
}

fn copy_forced_value(value: &[char], budget: &mut PropBudget) -> Option<Vec<char>> {
    budget.charge_expanded_chars(value.len())?;
    budget.charge_elements(1)?;
    budget.charge_work(value.len())?;
    let mut copied = Vec::new();
    copied.try_reserve(value.len()).ok()?;
    copied.extend_from_slice(value);
    Some(copied)
}

/// Apply the exact rules to one already-substituted, normalized equation.
/// `None` means the deterministic budget was exhausted and must fail open.
fn infer(
    lhs: &[Elem],
    rhs: &[Elem],
    env: &HashMap<TermId, Vec<char>>,
    budget: &mut PropBudget,
) -> Option<Step> {
    let lhs_chars = const_len(lhs)?;
    let rhs_chars = const_len(rhs)?;
    let elements = lhs.len().checked_add(rhs.len())?;
    let chars = lhs_chars.checked_add(rhs_chars)?;
    let scan_work = elements.checked_add(chars)?.checked_mul(4)?;
    budget.charge_work(scan_work)?;

    // Determined leading and trailing characters must agree regardless of the
    // values assigned to intervening variables.
    let (left_prefix, right_prefix) = (leading(lhs), leading(rhs));
    let overlap = left_prefix.len().min(right_prefix.len());
    if left_prefix[..overlap] != right_prefix[..overlap] {
        return Some(Step::Conflict);
    }
    let (left_suffix, right_suffix) = (trailing(lhs), trailing(rhs));
    let overlap = left_suffix.len().min(right_suffix.len());
    if left_suffix[left_suffix.len() - overlap..] != right_suffix[right_suffix.len() - overlap..] {
        return Some(Step::Conflict);
    }

    for (ground_side, other_side, other_const_len) in [(lhs, rhs, rhs_chars), (rhs, lhs, lhs_chars)]
    {
        let Some(target) = ground(ground_side) else {
            continue;
        };
        if other_const_len > target.len() {
            return Some(Step::Conflict);
        }
        if let Some(other) = ground(other_side) {
            return Some(if other == target {
                Step::Inert
            } else {
                Step::Conflict
            });
        }

        let mut variable = None;
        let mut occurrences = 0usize;
        let mut single_variable = true;
        for elem in other_side {
            if let Elem::Var(var) = elem {
                match variable {
                    None => {
                        variable = Some(*var);
                        occurrences = 1;
                    }
                    Some(previous) if previous == *var => {
                        occurrences = occurrences.checked_add(1)?;
                    }
                    Some(_) => {
                        single_variable = false;
                        break;
                    }
                }
            }
        }
        let (Some(variable), true) = (variable, single_variable) else {
            continue;
        };
        if occurrences == 0 {
            return None;
        }
        let residue = target.len().checked_sub(other_const_len)?;
        if residue % occurrences != 0 {
            return Some(Step::Conflict);
        }
        let width = residue / occurrences;

        let mut position = 0usize;
        let mut value = None;
        for elem in other_side {
            match elem {
                Elem::Const(constant) => {
                    let end = position.checked_add(constant.len())?;
                    if end > target.len() || target[position..end] != constant[..] {
                        return Some(Step::Conflict);
                    }
                    position = end;
                }
                Elem::Var(_) => {
                    let end = position.checked_add(width)?;
                    if end > target.len() {
                        return Some(Step::Conflict);
                    }
                    let piece = &target[position..end];
                    match value {
                        None => value = Some(piece),
                        Some(previous) if previous == piece => {}
                        Some(_) => return Some(Step::Conflict),
                    }
                    position = end;
                }
            }
        }
        if position != target.len() {
            return Some(Step::Conflict);
        }
        let value = value.unwrap_or(&[]);
        return Some(match env.get(&variable) {
            Some(previous) if previous != value => Step::Conflict,
            Some(_) => Step::Inert,
            None => Step::Forced(variable, copy_forced_value(value, budget)?),
        });
    }
    Some(Step::Inert)
}

fn propagate<F>(equations: &[PropEq], budget: &mut PropBudget, mut should_abort: F) -> PropOutcome
where
    F: FnMut() -> bool,
{
    let mut env: HashMap<TermId, Vec<char>> = HashMap::default();
    if budget.charge_elements(equations.len()).is_none()
        || budget.charge_work(equations.len()).is_none()
    {
        return PropOutcome::Limited;
    }
    // Outside Kani, deterministic maps are hashbrown containers and expose
    // fallible capacity reservation. Kani aliases them to BTreeMap, whose
    // model has no reserve API. One equation can force at most one new value,
    // so this bounded capacity covers every subsequent insertion.
    #[cfg(not(kani))]
    if env.try_reserve(equations.len()).is_err() {
        return PropOutcome::Limited;
    }
    for _ in 0..budget.limits.max_rounds {
        if should_abort() {
            return PropOutcome::Aborted;
        }
        let mut changed = false;
        for equation in equations {
            if should_abort() {
                return PropOutcome::Aborted;
            }
            let Some(lhs) = substitute(&equation.lhs, &env, budget) else {
                return PropOutcome::Limited;
            };
            let Some(rhs) = substitute(&equation.rhs, &env, budget) else {
                return PropOutcome::Limited;
            };
            let Some(step) = infer(&lhs, &rhs, &env, budget) else {
                return PropOutcome::Limited;
            };
            // An interrupt can race with the bounded local inference. Never
            // publish a conflict after the caller has requested cancellation.
            if should_abort() {
                return PropOutcome::Aborted;
            }
            match step {
                Step::Conflict => return PropOutcome::Conflict,
                Step::Forced(var, value) => {
                    env.insert(var, value);
                    changed = true;
                }
                Step::Inert => {}
            }
        }
        if !changed {
            return PropOutcome::Inconclusive;
        }
    }
    PropOutcome::Limited
}

fn push_accounted<T>(out: &mut Vec<T>, value: T, budget: &mut PropBudget) -> Option<()> {
    budget.charge_work(1)?;
    budget.charge_elements(1)?;
    out.try_reserve(1).ok()?;
    out.push(value);
    Some(())
}

impl Executor {
    /// Exact constant-propagation refutation for large word-equation systems.
    /// A fail-open `None` leaves the existing string pipeline unchanged.
    pub(in crate::executor) fn try_word_eq_constant_propagation(
        &mut self,
    ) -> Result<Option<SolveResult>> {
        // Re-entrant witness solves must run the ordinary pipeline.  Proof and
        // self-check modes also bypass this non-proof-producing refutation.
        let strict_proofs_requested = matches!(
            self.ctx.get_option("check-proofs-strict"),
            Some(OptionValue::Bool(true))
        );
        if self.should_abort_theory_loop() {
            return Ok(Some(SolveResult::Unknown));
        }
        if self.pivot_enum_depth != 0
            || self.produce_proofs_enabled()
            || strict_proofs_requested
            || self.self_check()
        {
            return Ok(None);
        }

        let mut budget = PropBudget::new(DEFAULT_LIMITS);
        let mut aborted = false;
        let Some(equations) = self.extract_prop_equations(&mut budget, &mut aborted) else {
            return Ok(aborted.then_some(SolveResult::Unknown));
        };
        if equations.is_empty() {
            return Ok(None);
        }

        let outcome = propagate(&equations, &mut budget, || self.should_abort_theory_loop());
        Ok(match outcome {
            PropOutcome::Conflict => Some(SolveResult::unsat()),
            PropOutcome::Aborted => Some(SolveResult::Unknown),
            PropOutcome::Inconclusive | PropOutcome::Limited => None,
        })
    }

    /// Compute only the forced-true half of the unit closure used by the word
    /// equation extractor.  This mirrors `forced_literal_closure(false)` but
    /// accounts for every queued/stored literal and every Boolean-equality
    /// rescan, so a hostile Boolean wrapper cannot evade this pass's budget.
    fn budgeted_forced_true_closure(
        &mut self,
        budget: &mut PropBudget,
        aborted: &mut bool,
    ) -> Option<Vec<TermId>> {
        let mut true_set: HashSet<TermId> = HashSet::default();
        let mut false_set: HashSet<TermId> = HashSet::default();
        let mut true_list = Vec::new();
        let mut bool_equalities = Vec::new();
        let mut work = Vec::new();

        for index in 0..self.ctx.assertions.len() {
            if self.should_abort_theory_loop() {
                *aborted = true;
                return None;
            }
            let assertion = self.ctx.assertions[index];
            push_accounted(&mut work, (assertion, true), budget)?;
        }

        let mut closure_literals = 0usize;
        while let Some((term, polarity)) = work.pop() {
            if self.should_abort_theory_loop() {
                *aborted = true;
                return None;
            }
            budget.charge_work(1)?;

            let is_new = if polarity {
                !true_set.contains(&term)
            } else {
                !false_set.contains(&term)
            };
            if !is_new {
                continue;
            }
            closure_literals = closure_literals.checked_add(1)?;
            if closure_literals > budget.limits.max_closure_literals {
                return None;
            }
            if polarity {
                // One set entry plus the ordered output-list entry.
                budget.charge_elements(2)?;
                #[cfg(not(kani))]
                true_set.try_reserve(1).ok()?;
                true_list.try_reserve(1).ok()?;
                true_set.insert(term);
                true_list.push(term);
            } else {
                budget.charge_elements(1)?;
                #[cfg(not(kani))]
                false_set.try_reserve(1).ok()?;
                false_set.insert(term);
            }

            match self.ctx.terms.get(term) {
                TermData::Not(inner) => {
                    push_accounted(&mut work, (*inner, !polarity), budget)?;
                }
                TermData::App(Symbol::Named(name), args) if name == "and" && polarity => {
                    for &arg in args {
                        push_accounted(&mut work, (arg, true), budget)?;
                    }
                }
                TermData::App(Symbol::Named(name), args) if name == "or" && !polarity => {
                    for &arg in args {
                        push_accounted(&mut work, (arg, false), budget)?;
                    }
                }
                TermData::App(Symbol::Named(name), args)
                    if name == "="
                        && args.len() == 2
                        && polarity
                        && *self.ctx.terms.sort(args[0]) == Sort::Bool =>
                {
                    push_accounted(&mut bool_equalities, (args[0], args[1]), budget)?;
                }
                _ => {}
            }

            for &(left, right) in &bool_equalities {
                budget.charge_work(4)?;
                for (known, implied) in [(left, right), (right, left)] {
                    if true_set.contains(&known) && !true_set.contains(&implied) {
                        push_accounted(&mut work, (implied, true), budget)?;
                    }
                    if false_set.contains(&known) && !false_set.contains(&implied) {
                        push_accounted(&mut work, (implied, false), budget)?;
                    }
                }
            }
        }
        Some(true_list)
    }

    fn extract_prop_equations(
        &mut self,
        budget: &mut PropBudget,
        aborted: &mut bool,
    ) -> Option<Vec<PropEq>> {
        let forced_true = self.budgeted_forced_true_closure(budget, aborted)?;
        let mut out = Vec::new();
        for assertion in forced_true {
            if self.should_abort_theory_loop() {
                *aborted = true;
                return None;
            }
            budget.charge_work(1)?;
            let Some((left, right)) = (match self.ctx.terms.get(assertion) {
                TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
                    Some((args[0], args[1]))
                }
                _ => None,
            }) else {
                continue;
            };
            if *self.ctx.terms.sort(left) != Sort::String {
                continue;
            }
            if out.len() >= budget.limits.max_equations {
                return None;
            }

            let lhs = match self.flatten_prop_word(left, budget, aborted) {
                FlattenOutcome::Word(word) => word,
                FlattenOutcome::Unsupported => continue,
                FlattenOutcome::Limited => return None,
            };
            let rhs = match self.flatten_prop_word(right, budget, aborted) {
                FlattenOutcome::Word(word) => word,
                FlattenOutcome::Unsupported => continue,
                FlattenOutcome::Limited => return None,
            };
            push_accounted(&mut out, PropEq { lhs, rhs }, budget)?;
        }
        Some(out)
    }

    /// Flatten constants, variables, and `str.++` iteratively.  Explicit depth
    /// and stack accounting avoids both call-stack growth and unbounded wide
    /// concatenation allocation.
    fn flatten_prop_word(
        &mut self,
        root: TermId,
        budget: &mut PropBudget,
        aborted: &mut bool,
    ) -> FlattenOutcome {
        let mut out = Vec::new();
        let mut stack = Vec::new();
        if push_accounted(&mut stack, (root, 0usize), budget).is_none() {
            return FlattenOutcome::Limited;
        }

        while let Some((term, depth)) = stack.pop() {
            if self.should_abort_theory_loop() {
                *aborted = true;
                return FlattenOutcome::Limited;
            }
            if budget.charge_work(1).is_none() {
                return FlattenOutcome::Limited;
            }
            if depth > budget.limits.max_depth {
                return FlattenOutcome::Limited;
            }
            match self.ctx.terms.get(term) {
                TermData::Const(Constant::String(value)) => {
                    if append_string(&mut out, value, budget).is_none() {
                        return FlattenOutcome::Limited;
                    }
                }
                TermData::Var(..) if *self.ctx.terms.sort(term) == Sort::String => {
                    if push_accounted(&mut out, Elem::Var(term), budget).is_none() {
                        return FlattenOutcome::Limited;
                    }
                }
                TermData::App(Symbol::Named(name), args) if name == "str.++" => {
                    let Some(next_depth) = depth.checked_add(1) else {
                        return FlattenOutcome::Limited;
                    };
                    for &arg in args.iter().rev() {
                        if push_accounted(&mut stack, (arg, next_depth), budget).is_none() {
                            return FlattenOutcome::Limited;
                        }
                    }
                }
                _ => return FlattenOutcome::Unsupported,
            }
        }
        FlattenOutcome::Word(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_frontend::parse;

    fn constant(value: &str) -> Elem {
        Elem::Const(value.chars().collect())
    }

    fn variable(id: u32) -> Elem {
        Elem::Var(TermId(id))
    }

    fn empty_env() -> HashMap<TermId, Vec<char>> {
        HashMap::default()
    }

    fn generous_budget() -> PropBudget {
        PropBudget::new(DEFAULT_LIMITS)
    }

    fn load_without_check(input: &str) -> Executor {
        let commands = parse(input).expect("valid SMT-LIB");
        let mut executor = Executor::new();
        assert!(executor
            .execute_all(&commands)
            .expect("load assertions")
            .is_empty());
        executor
    }

    fn infer_generously(lhs: &[Elem], rhs: &[Elem], env: &HashMap<TermId, Vec<char>>) -> Step {
        infer(lhs, rhs, env, &mut generous_budget()).expect("generous inference budget")
    }

    #[test]
    fn boundary_clashes_are_conflicts() {
        assert!(matches!(
            infer_generously(
                &[constant("abcd"), variable(1)],
                &[constant("abx"), variable(2)],
                &empty_env(),
            ),
            Step::Conflict
        ));
        assert!(matches!(
            infer_generously(
                &[constant("dcacb"), variable(1), constant("accaa")],
                &[variable(2), constant("cbdababa")],
                &empty_env(),
            ),
            Step::Conflict
        ));
    }

    #[test]
    fn ground_overflow_is_a_conflict() {
        assert!(matches!(
            infer_generously(
                &[constant("abc")],
                &[constant("ab"), variable(1), constant("xyz")],
                &empty_env(),
            ),
            Step::Conflict
        ));
    }

    #[test]
    fn unique_determination_reads_the_ground_side() {
        match infer_generously(
            &[constant("bcbdababdccbcdacdbbb")],
            &[constant("bc"), variable(1), constant("dccbcdacdbbb")],
            &empty_env(),
        ) {
            Step::Forced(var, value) => {
                assert_eq!(var, TermId(1));
                assert_eq!(value.iter().collect::<String>(), "bdabab");
            }
            _ => panic!("expected a forced value"),
        }
    }

    #[test]
    fn repeated_occurrences_must_agree_and_divide_evenly() {
        assert!(matches!(
            infer_generously(
                &[constant("abab")],
                &[variable(1), variable(1)],
                &empty_env(),
            ),
            Step::Forced(_, ref value) if value.iter().collect::<String>() == "ab"
        ));
        assert!(matches!(
            infer_generously(
                &[constant("abac")],
                &[variable(1), variable(1)],
                &empty_env(),
            ),
            Step::Conflict
        ));
        assert!(matches!(
            infer_generously(
                &[constant("abc")],
                &[variable(1), variable(1)],
                &empty_env(),
            ),
            Step::Conflict
        ));
    }

    #[test]
    fn satisfiable_and_ground_equalities_do_not_refute() {
        let open_lhs = [constant("ada"), variable(1), constant("aaddb")];
        let open_rhs = [constant("adaaacbda"), variable(2)];
        assert!(matches!(
            infer_generously(&open_lhs, &open_rhs, &empty_env()),
            Step::Inert
        ));
        assert!(matches!(
            infer_generously(&[constant("abc")], &[constant("abc")], &empty_env(),),
            Step::Inert
        ));
        assert!(matches!(
            infer_generously(&[constant("abc")], &[constant("abd")], &empty_env(),),
            Step::Conflict
        ));
    }

    #[test]
    fn substitution_normalizes_adjacent_and_empty_constants() {
        let word = [
            constant("a"),
            constant(""),
            constant("b"),
            variable(1),
            constant(""),
            constant("c"),
        ];
        let normalized = substitute(&word, &empty_env(), &mut generous_budget())
            .expect("generous substitution budget");
        assert_eq!(normalized, vec![constant("ab"), variable(1), constant("c")]);
    }

    #[test]
    fn propagation_limits_and_abort_fail_open() {
        let equation = PropEq {
            lhs: vec![constant("a")],
            rhs: vec![constant("b")],
        };

        let mut limits = DEFAULT_LIMITS;
        limits.max_expanded_chars = 0;
        assert_eq!(
            propagate(
                std::slice::from_ref(&equation),
                &mut PropBudget::new(limits),
                || false
            ),
            PropOutcome::Limited
        );

        let mut limits = DEFAULT_LIMITS;
        limits.max_total_elements = 0;
        assert_eq!(
            propagate(
                std::slice::from_ref(&equation),
                &mut PropBudget::new(limits),
                || false
            ),
            PropOutcome::Limited
        );

        let mut limits = DEFAULT_LIMITS;
        limits.max_work = 0;
        assert_eq!(
            propagate(
                std::slice::from_ref(&equation),
                &mut PropBudget::new(limits),
                || false
            ),
            PropOutcome::Limited
        );

        let mut limits = DEFAULT_LIMITS;
        limits.max_rounds = 0;
        assert_eq!(
            propagate(
                std::slice::from_ref(&equation),
                &mut PropBudget::new(limits),
                || false
            ),
            PropOutcome::Limited
        );

        assert_eq!(
            propagate(&[equation], &mut generous_budget(), || true),
            PropOutcome::Aborted
        );
    }

    #[test]
    fn extraction_limits_fail_open_without_an_unsat_verdict() {
        let flat = r#"
(set-logic QF_S)
(declare-const x String)
(assert (= x "ab"))
"#;

        let mut executor = load_without_check(flat);
        let mut limits = DEFAULT_LIMITS;
        limits.max_source_chars = 1;
        let mut aborted = false;
        assert!(executor
            .extract_prop_equations(&mut PropBudget::new(limits), &mut aborted)
            .is_none());
        assert!(!aborted);

        let mut executor = load_without_check(flat);
        let mut limits = DEFAULT_LIMITS;
        limits.max_closure_literals = 0;
        let mut aborted = false;
        assert!(executor
            .extract_prop_equations(&mut PropBudget::new(limits), &mut aborted)
            .is_none());
        assert!(!aborted);

        let mut executor = load_without_check(flat);
        let mut limits = DEFAULT_LIMITS;
        limits.max_equations = 0;
        let mut aborted = false;
        assert!(executor
            .extract_prop_equations(&mut PropBudget::new(limits), &mut aborted)
            .is_none());
        assert!(!aborted);

        let nested = r#"
(set-logic QF_S)
(declare-const x String)
(assert (= (str.++ x "a") "a"))
"#;
        let mut executor = load_without_check(nested);
        let mut limits = DEFAULT_LIMITS;
        limits.max_depth = 0;
        let mut aborted = false;
        assert!(executor
            .extract_prop_equations(&mut PropBudget::new(limits), &mut aborted)
            .is_none());
        assert!(!aborted);
    }

    fn evaluate(word: &[Elem], x: &[char], y: &[char]) -> Vec<char> {
        let mut out = Vec::new();
        for elem in word {
            match elem {
                Elem::Const(value) => out.extend_from_slice(value),
                Elem::Var(TermId(0)) => out.extend_from_slice(x),
                Elem::Var(TermId(1)) => out.extend_from_slice(y),
                Elem::Var(other) => panic!("unexpected differential variable {other:?}"),
            }
        }
        out
    }

    fn next_random(state: &mut u64) -> u64 {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        *state
    }

    fn random_word(state: &mut u64) -> Vec<Elem> {
        let len = (next_random(state) % 4 + 1) as usize;
        (0..len)
            .map(|_| match next_random(state) % 6 {
                0 => variable(0),
                1 => variable(1),
                2 => constant(""),
                3 => constant("a"),
                4 => constant("b"),
                _ => constant("ab"),
            })
            .collect()
    }

    #[test]
    fn differential_pinned_systems_match_exhaustive_evaluation() {
        // Pinning both variables makes the independent finite evaluation
        // complete for each generated system, rather than merely a bounded
        // search for an otherwise-unbounded word equation.
        let values: Vec<Vec<char>> = ["", "a", "b", "aa", "ab", "ba", "bb"]
            .into_iter()
            .map(|value| value.chars().collect())
            .collect();
        let mut state = 0x51_72_a4_19_8c_d3_e6_f0;

        for case in 0..512 {
            let x = &values[next_random(&mut state) as usize % values.len()];
            let y = &values[next_random(&mut state) as usize % values.len()];
            let mut equations = vec![
                PropEq {
                    lhs: vec![variable(0)],
                    rhs: vec![Elem::Const(x.clone())],
                },
                PropEq {
                    lhs: vec![variable(1)],
                    rhs: vec![Elem::Const(y.clone())],
                },
            ];
            let extra = (next_random(&mut state) % 5) as usize;
            for _ in 0..extra {
                equations.push(PropEq {
                    lhs: random_word(&mut state),
                    rhs: random_word(&mut state),
                });
            }

            let expected_sat = equations
                .iter()
                .all(|equation| evaluate(&equation.lhs, x, y) == evaluate(&equation.rhs, x, y));
            let outcome = propagate(&equations, &mut generous_budget(), || false);
            assert_ne!(outcome, PropOutcome::Limited, "case {case} hit a limit");
            assert_eq!(
                outcome == PropOutcome::Conflict,
                !expected_sat,
                "case {case} disagreed with complete pinned evaluation"
            );
        }
    }

    fn large_chain(last_value: &str, check_sat: bool, strict: bool) -> String {
        let mut input = String::from("(set-logic QF_S)\n");
        if strict {
            input.push_str("(set-option :produce-proofs true)\n");
            input.push_str("(set-option :check-proofs-strict true)\n");
        }
        for index in 0..24 {
            input.push_str(&format!("(declare-const x{index} String)\n"));
        }
        input.push_str("(assert (= x0 \"a\"))\n");
        for index in 0..23 {
            input.push_str(&format!("(assert (= x{index} x{}))\n", index + 1));
        }
        input.push_str(&format!("(assert (= x23 \"{last_value}\"))\n"));
        if check_sat {
            input.push_str("(check-sat)\n");
        }
        input
    }

    #[test]
    fn large_chain_direct_pass_distinguishes_sat_and_unsat() {
        let commands = parse(&large_chain("b", false, false)).expect("valid SMT-LIB");
        let mut executor = Executor::new();
        assert!(executor
            .execute_all(&commands)
            .expect("load UNSAT chain")
            .is_empty());
        assert!(executor
            .try_word_eq_constant_propagation()
            .expect("word propagation")
            .is_some_and(|result| result.is_unsat()));

        let commands = parse(&large_chain("a", false, false)).expect("valid SMT-LIB");
        let mut executor = Executor::new();
        assert!(executor
            .execute_all(&commands)
            .expect("load SAT chain")
            .is_empty());
        assert!(executor
            .try_word_eq_constant_propagation()
            .expect("word propagation")
            .is_none());
    }

    #[test]
    fn large_chain_end_to_end_sat_and_unsat() {
        for (last_value, expected) in [("a", "sat"), ("b", "unsat")] {
            let commands = parse(&large_chain(last_value, true, false)).expect("valid SMT-LIB");
            let mut executor = Executor::new();
            let outputs = executor.execute_all(&commands).expect("solve large chain");
            assert_eq!(outputs, vec![expected], "last value {last_value}");
        }
    }

    #[test]
    fn mixed_slia_lane_runs_the_large_equation_refutation() {
        let mut input = large_chain("b", false, false).replacen("QF_S", "QF_SLIA", 1);
        input.push_str("(declare-const n Int)\n");
        input.push_str("(assert (= n (str.len x0)))\n");
        input.push_str("(assert (= n 1))\n");
        input.push_str("(check-sat)\n");
        let commands = parse(&input).expect("valid mixed SMT-LIB");
        let mut executor = Executor::new();
        let outputs = executor.execute_all(&commands).expect("solve mixed chain");
        assert_eq!(outputs, vec!["unsat"]);
    }

    #[test]
    fn proof_and_self_check_modes_bypass_uncertified_word_propagation() {
        let mut strict_only = large_chain("b", false, false);
        strict_only.push_str("(set-option :check-proofs-strict true)\n");
        let commands = parse(&strict_only).expect("valid strict-only SMT-LIB");
        let mut executor = Executor::new();
        assert!(executor
            .execute_all(&commands)
            .expect("load strict-only chain")
            .is_empty());
        assert!(executor
            .try_word_eq_constant_propagation()
            .expect("strict-only bypass")
            .is_none());

        let commands = parse(&large_chain("b", false, true)).expect("valid SMT-LIB");
        let mut executor = Executor::new();
        assert!(executor
            .execute_all(&commands)
            .expect("load strict chain")
            .is_empty());
        assert!(executor
            .try_word_eq_constant_propagation()
            .expect("proof-mode bypass")
            .is_none());

        let commands = parse(&large_chain("b", false, false)).expect("valid SMT-LIB");
        let mut executor = Executor::new();
        executor.set_self_check(true);
        assert!(executor
            .execute_all(&commands)
            .expect("load self-check chain")
            .is_empty());
        assert!(executor
            .try_word_eq_constant_propagation()
            .expect("self-check bypass")
            .is_none());
    }

    #[test]
    fn strict_self_check_never_publishes_uncertified_unsat() {
        let commands = parse(&large_chain("b", true, true)).expect("valid SMT-LIB");
        let mut executor = Executor::new();
        executor.set_self_check(true);
        let outputs = executor.execute_all(&commands).expect("strict solve");
        assert_eq!(outputs.len(), 1);
        assert_ne!(outputs[0], "sat", "the chain is contradictory");
        if outputs[0] == "unsat" {
            assert!(
                executor.unsat_proof_self_certified(),
                "strict self-check emitted an uncertified UNSAT"
            );
        } else {
            assert_eq!(outputs[0], "unknown");
        }
    }

    #[test]
    fn executor_lane_refutes_conflicting_asserted_determinations() {
        let mut executor = Executor::new();
        let variable = executor.ctx.terms.mk_var("x", Sort::String);
        let ab = executor.ctx.terms.mk_string("ab".to_string());
        let ac = executor.ctx.terms.mk_string("ac".to_string());
        let variable_is_ab = executor.ctx.terms.mk_eq(variable, ab);
        let variable_is_ac = executor.ctx.terms.mk_eq(variable, ac);
        executor
            .ctx
            .assertions
            .extend([variable_is_ab, variable_is_ac]);

        let result = executor
            .try_word_eq_constant_propagation()
            .expect("constant propagation must not fail")
            .expect("the conflicting determinations must be refuted");
        assert!(result.is_unsat());
    }

    #[test]
    fn executor_lane_does_not_treat_disjunction_arms_as_forced() {
        let mut executor = Executor::new();
        let variable = executor.ctx.terms.mk_var("x", Sort::String);
        let ab = executor.ctx.terms.mk_string("ab".to_string());
        let ac = executor.ctx.terms.mk_string("ac".to_string());
        let variable_is_ab = executor.ctx.terms.mk_eq(variable, ab);
        let variable_is_ac = executor.ctx.terms.mk_eq(variable, ac);
        let choice = executor
            .ctx
            .terms
            .mk_or(vec![variable_is_ab, variable_is_ac]);
        executor.ctx.assertions.push(choice);

        assert!(executor
            .try_word_eq_constant_propagation()
            .expect("constant propagation must not fail")
            .is_none());
    }
}
