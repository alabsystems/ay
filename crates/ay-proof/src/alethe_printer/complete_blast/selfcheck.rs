// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! AY's own replay of the document it is about to print.
//!
//! Everything AY discloses about a certificate — `unproved_steps=0`,
//! `trust_free=yes`, `ay_self_checkable=yes` — is a claim about the DOCUMENT,
//! so it has to be decided from the document. This module re-reads the printed
//! TEXT (not the structures that produced it) and replays every `resolution`
//! step as the binary resolution it claims to be: two premises, one pivot,
//! and a conclusion that is exactly their resolvent. A document whose own
//! producer cannot replay it is never printed at all, so the ordinary honest
//! `hole` stays in place and the disclosure reports `unproved_steps=1`.
//!
//! ## Why this is the fail-closed boundary, and not care
//!
//! The previous transport printed one n-ary `resolution` step per derived
//! clause, replayed from an LRAT RUP hint list. A hint list is not always a
//! chain the consumer can reconstruct, and on the larger refutations the
//! pinned checker answered `checking failed on step 't1' with rule
//! 'resolution': rule validation failed` — for a document AY had already
//! disclosed as hole-free. That is strictly worse than the hole it replaced.
//! Both halves of the fix live here: the chain is BINARY (one pivot per step,
//! which is what the checker replays), and it is replayed by AY before a byte
//! of it is disclosed.
//!
//! ## What the replay does and does not decide
//!
//! It decides the propositional endgame: that the printed clauses compose,
//! by binary resolution, into the printed conclusion. It deliberately does
//! NOT re-check the `bitblast_*`, `cong`, `trans`, `poly_simp`, `ite_intro`
//! or Tseitin-tautology steps — those are the consumer's own rules, re-derived
//! by the consumer from the word-level terms, and re-checking them here would
//! only re-assert AY's opinion of AY's blaster. A replay that closes therefore
//! means "the transport is sound as printed", never "the certificate is
//! valid".

use ay_core::kani_compat::{DetHashMap, DetHashSet};

/// A printed literal: an interned base term plus the parity of the `not`
/// wrappers around it. `x` and `(not (not x))` are the same literal to every
/// resolution engine, this one included.
type Lit = u32;

/// A printed literal under the consumer's `:args` reading.
///
/// Same interned base term, but paired with the COUNT of `not` wrappers rather
/// than with their parity. The two readings differ exactly on `(not (not x))`,
/// and which one the consumer uses is decided by the step: an argument-free
/// `resolution` is compared by parity, one carrying `:args` by count, because
/// that path negates a pivot by adding a `not` (`n + 1`) instead of flipping a
/// sign. A replay that used parity for both would accept a step the consumer
/// rejects.
type CLit = u32;

/// The deepest `not` nesting a [`CLit`] holds.
///
/// A counted literal packs its base id and negation count as
/// `id * 256 + count`, so a count past this one would carry into the NEXT
/// base term's id: `a` under 256 `not`s would be the same literal as the next
/// interned term under none. A literal that deep is refused, never aliased.
const MAX_NEGATION_COUNT: u32 = 255;

/// Pack a base id and its negation count into a [`CLit`], or `None` when the
/// count does not fit the encoding (or the id does not fit a `u32`).
fn counted_literal(id: u32, count: u32) -> Option<CLit> {
    if count > MAX_NEGATION_COUNT {
        return None;
    }
    id.checked_mul(256)?.checked_add(count)
}

/// The consumer's complement of a counted literal: one more `not`, or `None`
/// when that `not` would carry past the encoding into the next base term.
fn counted_complement(literal: CLit) -> Option<CLit> {
    if literal & MAX_NEGATION_COUNT == MAX_NEGATION_COUNT {
        return None;
    }
    literal.checked_add(1)
}

/// Replay the resolution chain of `document`, treating the clause of
/// `final_step` as `final_clause`.
///
/// The final step is the theory lemma itself: it PRINTS the word-level clause
/// `(cl (not A))`, while the chain that derives it runs over the Boolean
/// circuit's own spelling of the same literal. The consumer settles that the
/// two are one term by inlining the document's `define-fun`s; the replay is
/// handed the circuit-level spelling so it checks the resolution and nothing
/// else.
///
/// Returns `true` only when every `resolution` step in the document is an
/// exact binary resolution of two earlier printed clauses (or an n-ary one
/// over its printed pivots), every `weakening` extends an earlier printed
/// clause, AND the final step is a resolution.
pub(super) fn chain_replays<'d>(
    document: &'d str,
    final_step: &str,
    final_clause: &'d str,
) -> bool {
    let mut replay = Replay::default();
    replay.run(document, final_step, final_clause)
}

#[derive(Default)]
struct Replay<'d> {
    /// Base term text -> interned id.
    interned: DetHashMap<&'d str, u32>,
    /// Step name -> the clause that step PRINTS, read by parity.
    clauses: DetHashMap<&'d str, Vec<Lit>>,
    /// Step name -> the same clause read by negation COUNT, for `:args` steps.
    counted: DetHashMap<&'d str, Vec<CLit>>,
}

impl<'d> Replay<'d> {
    fn run(&mut self, document: &'d str, final_step: &str, final_clause: &'d str) -> bool {
        let mut closed = false;
        for line in document.lines() {
            let Some(step) = parse_step(line) else {
                continue;
            };
            let printed = if step.name == final_step {
                final_clause
            } else {
                step.clause
            };
            // THE FINAL STEP IS REPLAYED AGAINST A DIFFERENT CLAUSE THAN IT
            // PRINTS: this replay is handed the circuit-level spelling while
            // the document prints the word-level lemma, and only the
            // consumer's `define-fun` inlining reconciles the two. That
            // reconciliation is by TERM, so it survives the parity reading —
            // but not the `:args` reading, which also compares NEGATION DEPTH.
            // Measured on `str.post.gpr.w4`: the consumer computed the
            // resolvent as a gate at depth 0 while the lemma printed it at
            // depth 2, and carcara answered `checking failed on step 't1' with
            // rule 'resolution'`. Refuse that combination here rather than
            // certify a document the consumer rejects.
            if step.name == final_step && !step.args.is_empty() && !clause_is_shallow(step.clause) {
                return false;
            }
            let Some(clause) = self.literals(printed) else {
                return false;
            };
            let Some(counted) = self.counted_literals(printed) else {
                return false;
            };
            if step.rule == "resolution" {
                // Replay the step the way the CONSUMER will read it: a step
                // with pivots is replayed link by link over those pivots, a
                // step without them as the single binary resolvent.
                let replayed = if step.args.is_empty() {
                    self.resolves(&step.premises, &clause)
                } else {
                    self.resolves_with_pivots(&step.premises, &step.args, &counted)
                };
                if !replayed {
                    return false;
                }
            } else if step.rule == "drup" {
                // The consumer adds each `:args` clause by reverse unit
                // propagation and then looks the conclusion up among them:
                // the transport's one argument IS the conclusion.
                if step.args != [step.clause] || !self.rup_replays(&step.premises, &clause) {
                    return false;
                }
            } else if step.rule == "weakening" {
                // The transport weakens a clause to the one its SAT engine
                // derived. The consumer demands the premise's printed
                // literals, in order, as the conclusion's prefix; anything
                // else is refused here as it would be there.
                let [premise] = step.premises.as_slice() else {
                    return false;
                };
                let Some(prefix) = self.counted.get(*premise) else {
                    return false;
                };
                if !counted.starts_with(prefix) {
                    return false;
                }
            }
            // A repeated step name would let a later clause silently stand in
            // for an earlier premise.
            if self.clauses.insert(step.name, clause).is_some() {
                return false;
            }
            self.counted.insert(step.name, counted);
            if step.name == final_step {
                if step.rule != "resolution" {
                    return false;
                }
                closed = true;
            }
        }
        closed
    }

    /// Does `claimed` follow from the named premises, read by parity, by
    /// reverse unit propagation (`rup_replay.rs`)?
    fn rup_replays(&self, premises: &[&str], claimed: &[Lit]) -> bool {
        let clauses: Option<Vec<&[Lit]>> = premises
            .iter()
            .map(|name| self.clauses.get(name).map(Vec::as_slice))
            .collect();
        clauses.is_some_and(|clauses| super::rup_replay::rup_replays(&clauses, claimed))
    }

    /// Is `claimed` exactly the binary resolvent of the two named premises?
    fn resolves(&self, premises: &[&str], claimed: &[Lit]) -> bool {
        let [left_name, right_name] = premises else {
            // One pivot per step, two premises per step: anything else is a
            // shape this replay cannot certify, so it is refused.
            return false;
        };
        let (Some(left), Some(right)) =
            (self.clauses.get(*left_name), self.clauses.get(*right_name))
        else {
            // A premise that is not an earlier printed clause.
            return false;
        };
        let Some(pivot) = sole_pivot(left, right) else {
            return false;
        };
        let mut resolvent: Vec<Lit> = Vec::new();
        let mut seen: DetHashSet<Lit> = DetHashSet::default();
        for literal in left {
            if *literal == (pivot ^ 1) {
                continue;
            }
            if seen.insert(*literal) {
                resolvent.push(*literal);
            }
        }
        for literal in right {
            if *literal == pivot {
                continue;
            }
            if seen.insert(*literal) {
                resolvent.push(*literal);
            }
        }
        same_clause(&resolvent, claimed)
    }

    /// Is `claimed` exactly what the consumer computes for an n-ary step?
    ///
    /// This mirrors carcara's `apply_generic_resolution` step for step: start
    /// from the first premise, and for each link take the declared pivot and
    /// polarity, remove that literal from the accumulated clause, and fold in
    /// the next premise minus the pivot's complement. Nothing is searched for
    /// and nothing is inferred — a pivot that is not where the step says it is
    /// fails here exactly as it would fail there.
    fn resolves_with_pivots(&self, premises: &[&str], args: &[&str], claimed: &[CLit]) -> bool {
        // One pivot and one polarity per link, and a link per premise past the
        // first. Any other arity is a shape this replay cannot certify.
        if premises.len() < 2 || args.len() != (premises.len() - 1) * 2 {
            return false;
        }
        let Some(first) = self.counted.get(premises[0]) else {
            return false;
        };
        let mut current: Vec<CLit> = Vec::new();
        for literal in first {
            if !current.contains(literal) {
                current.push(*literal);
            }
        }
        for (link, premise) in premises[1..].iter().enumerate() {
            let Some(next_clause) = self.counted.get(*premise) else {
                // A premise that is not an earlier printed clause.
                return false;
            };
            let in_current_side = match args[link * 2 + 1] {
                "true" => true,
                "false" => false,
                // The consumer demands a Boolean constant here.
                _ => return false,
            };
            let Some(pivot) = self.counted_pivot(args[link * 2]) else {
                return false;
            };
            // The consumer negates by ADDING a `not`, so the complement of the
            // argument is always one level deeper than the argument itself.
            let Some(negated) = counted_complement(pivot) else {
                return false;
            };
            let (here, there) = if in_current_side {
                (pivot, negated)
            } else {
                (negated, pivot)
            };
            let Some(at) = current.iter().position(|literal| *literal == here) else {
                return false;
            };
            current.swap_remove(at);
            let mut found = false;
            for literal in next_clause {
                if !found && *literal == there {
                    found = true;
                    continue;
                }
                if !current.contains(literal) {
                    current.push(*literal);
                }
            }
            if !found {
                return false;
            }
        }
        same_clause(&current, claimed)
    }

    /// The `:args` pivot as a counted literal, WITHOUT interning anything new.
    ///
    /// A pivot has to occur in two clauses this document already printed, so a
    /// base term that was never interned cannot be one; refusing is then the
    /// fail-closed answer rather than minting a fresh id that matches nothing.
    fn counted_pivot(&self, term: &str) -> Option<CLit> {
        let (base, count) = strip_negations_counted(term);
        let id = *self.interned.get(base)?;
        counted_literal(id, count)
    }

    /// Parse `(cl …)` into interned literals, keyed by negation COUNT.
    ///
    /// REPEATED LITERALS ARE KEPT. The consumer folds a premise into the
    /// accumulated clause by skipping only the FIRST occurrence of the pivot
    /// and inserting everything else, so a clause that prints the same literal
    /// twice contributes a copy the accumulated clause keeps. Collapsing the
    /// repeat here would make this replay agree with the transport instead of
    /// with the consumer — which is how a document AY had already disclosed as
    /// hole-free was rejected at `t1.cbbr2193` with `rule validation failed`.
    fn counted_literals(&mut self, clause: &'d str) -> Option<Vec<CLit>> {
        let inner = clause.strip_prefix("(cl")?.strip_suffix(')')?;
        let mut out = Vec::new();
        for token in tokens(inner)? {
            let (base, count) = strip_negations_counted(token);
            let next = self.interned.len() as u32;
            let id = *self.interned.entry(base).or_insert(next);
            out.push(counted_literal(id, count)?);
        }
        Some(out)
    }

    /// Parse `(cl …)` into interned literals.
    fn literals(&mut self, clause: &'d str) -> Option<Vec<Lit>> {
        let inner = clause.strip_prefix("(cl")?.strip_suffix(')')?;
        let mut out = Vec::new();
        for token in tokens(inner)? {
            let (base, negated) = strip_negations(token);
            let next = self.interned.len() as u32;
            let id = *self.interned.entry(base).or_insert(next);
            let literal = id.checked_mul(2)? | u32::from(negated);
            if !out.contains(&literal) {
                out.push(literal);
            }
        }
        Some(out)
    }
}

/// The single literal of `right` whose negation is in `left`, or `None` when
/// there is no such literal or more than one.
///
/// More than one complementary pair leaves the step's pivot ambiguous, and a
/// consumer is free to pick the other one; a document that depends on the
/// choice is refused rather than gambled on.
fn sole_pivot(left: &[Lit], right: &[Lit]) -> Option<Lit> {
    let present: DetHashSet<Lit> = left.iter().copied().collect();
    let mut pivot = None;
    for literal in right {
        if !present.contains(&(literal ^ 1)) {
            continue;
        }
        match pivot {
            Some(existing) if existing == *literal => {}
            Some(_) => return None,
            None => pivot = Some(*literal),
        }
    }
    pivot
}

fn same_clause(left: &[Lit], right: &[Lit]) -> bool {
    let left_set: DetHashSet<Lit> = left.iter().copied().collect();
    let right_set: DetHashSet<Lit> = right.iter().copied().collect();
    left_set == right_set
}

/// One parsed `(step …)` line.
struct Step<'d> {
    name: &'d str,
    clause: &'d str,
    rule: &'d str,
    premises: Vec<&'d str>,
    /// The `:args` list, as top-level terms. A pivot may itself be a compound
    /// term containing spaces, so this is tokenized by balanced parentheses
    /// rather than by whitespace.
    args: Vec<&'d str>,
}

fn parse_step(line: &str) -> Option<Step<'_>> {
    let rest = line.strip_prefix("(step ")?;
    let (name, rest) = rest.split_once(' ')?;
    let rest = rest.trim_start();
    let clause = balanced(rest)?;
    let tail = rest.get(clause.len()..)?;
    let (_, after_rule) = tail.split_once(":rule ")?;
    let rule = after_rule
        .split(|c: char| c.is_whitespace() || c == ')')
        .next()?;
    let premises = match tail.split_once(":premises (") {
        Some((_, after)) => {
            let (list, _) = after.split_once(')')?;
            list.split_whitespace().collect()
        }
        None => Vec::new(),
    };
    let args = match tail.find(":args (") {
        Some(at) => {
            // The group starts at the `(` that follows `:args `.
            let group = balanced(tail.get(at..)?.strip_prefix(":args ")?)?;
            tokens(group.strip_prefix('(')?.strip_suffix(')')?)?
        }
        None => Vec::new(),
    };
    Some(Step {
        name,
        clause,
        rule,
        premises,
        args,
    })
}

/// The balanced parenthesised group `text` starts with.
pub(super) fn balanced(text: &str) -> Option<&str> {
    let bytes = text.as_bytes();
    if bytes.first() != Some(&b'(') {
        return None;
    }
    let mut depth = 0_usize;
    for (index, byte) in bytes.iter().enumerate() {
        match byte {
            b'(' => depth = depth.checked_add(1)?,
            b')' => {
                // The group opens with `(`, so `depth` is at least one here
                // until the `)` that closes it returns.
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    return text.get(..=index);
                }
            }
            _ => {}
        }
    }
    None
}

/// Split a clause body into its top-level terms.
pub(super) fn tokens(inner: &str) -> Option<Vec<&str>> {
    let bytes = inner.as_bytes();
    let mut out = Vec::new();
    let mut index = 0_usize;
    while let Some(&byte) = bytes.get(index) {
        if byte.is_ascii_whitespace() {
            index = index.checked_add(1)?;
            continue;
        }
        if byte == b'(' {
            let group = balanced(inner.get(index..)?)?;
            out.push(group);
            index = index.checked_add(group.len())?;
            continue;
        }
        if byte == b')' {
            return None;
        }
        let start = index;
        while let Some(&byte) = bytes.get(index) {
            if byte.is_ascii_whitespace() || byte == b'(' || byte == b')' {
                break;
            }
            index = index.checked_add(1)?;
        }
        out.push(inner.get(start..index)?);
    }
    Some(out)
}

/// Whether every literal of a printed clause sits under at most one `not`.
///
/// Deeper nesting is exactly where the consumer's two readings disagree, so a
/// clause that fails this may not be compared across them.
fn clause_is_shallow(clause: &str) -> bool {
    let Some(inner) = clause
        .strip_prefix("(cl")
        .and_then(|rest| rest.strip_suffix(')'))
    else {
        return false;
    };
    let Some(items) = tokens(inner) else {
        return false;
    };
    items
        .iter()
        .all(|item| strip_negations_counted(item).1 <= 1)
}

/// Peel printed `not` wrappers, returning the base term and HOW MANY there
/// were — the reading the consumer uses for a step that carries `:args`.
fn strip_negations_counted(term: &str) -> (&str, u32) {
    let mut current = term;
    let mut count = 0_u32;
    while let Some(rest) = current.strip_prefix("(not ") {
        let Some(inner) = rest.strip_suffix(')') else {
            break;
        };
        // `(not a b)` is not a negation; only a single argument is.
        if tokens(inner).is_none_or(|parts| parts.len() != 1) {
            break;
        }
        current = inner;
        // Saturating is sound here: any count past `MAX_NEGATION_COUNT` is
        // refused by `counted_literal`, and `u32::MAX` is past it.
        count = count.saturating_add(1);
    }
    (current, count)
}

/// Peel printed `not` wrappers, returning the base term and its parity.
fn strip_negations(term: &str) -> (&str, bool) {
    let mut current = term;
    let mut negated = false;
    while let Some(rest) = current.strip_prefix("(not ") {
        let Some(inner) = rest.strip_suffix(')') else {
            break;
        };
        // `(not a b)` is not a negation; only a single argument is.
        if tokens(inner).is_none_or(|parts| parts.len() != 1) {
            break;
        }
        current = inner;
        negated = !negated;
    }
    (current, negated)
}

#[cfg(test)]
mod tests {
    use super::*;

    const LEFT: &str = "(step t1.a (cl p (not q)) :rule or_pos)";
    const RIGHT: &str = "(step t1.b (cl q) :rule or_pos)";

    fn document(final_line: &str) -> String {
        format!("{LEFT}\n{RIGHT}\n{final_line}\n")
    }

    #[test]
    fn a_closing_binary_chain_replays() {
        let text = document("(step t1 (cl (not A)) :rule resolution :premises (t1.a t1.b))");
        assert!(chain_replays(&text, "t1", "(cl p)"));
    }

    #[test]
    fn a_conclusion_that_is_not_the_resolvent_is_refused() {
        let text = document("(step t1 (cl (not A)) :rule resolution :premises (t1.a t1.b))");
        // The real resolvent is `(cl p)`; claiming anything else must fail.
        assert!(!chain_replays(&text, "t1", "(cl p r)"));
        assert!(!chain_replays(&text, "t1", "(cl)"));
        assert!(!chain_replays(&text, "t1", "(cl (not p))"));
    }

    #[test]
    fn a_premise_that_is_not_an_earlier_printed_clause_is_refused() {
        let text = document("(step t1 (cl (not A)) :rule resolution :premises (t1.a t1.z))");
        assert!(!chain_replays(&text, "t1", "(cl p)"));
    }

    #[test]
    fn an_n_ary_step_is_refused_however_true_it_is() {
        // The whole defect this module exists for: a hint list is not a chain.
        let text = format!(
            "{LEFT}\n{RIGHT}\n(step t1.c (cl (not p)) :rule or_pos)\n\
             (step t1 (cl (not A)) :rule resolution :premises (t1.a t1.b t1.c))\n"
        );
        assert!(!chain_replays(&text, "t1", "(cl)"));
    }

    #[test]
    fn an_ambiguous_pivot_is_refused() {
        let text = "(step t1.a (cl p (not q)) :rule or_pos)\n\
                    (step t1.b (cl q (not p)) :rule or_pos)\n\
                    (step t1 (cl (not A)) :rule resolution :premises (t1.a t1.b))\n";
        assert!(!chain_replays(text, "t1", "(cl p (not p))"));
    }

    /// A `weakening` must keep its premise's printed literals, in order, as
    /// its prefix (the consumer's rule); only then does the chain go on.
    #[test]
    fn a_weakening_extends_its_premise_as_a_prefix() {
        let closing = "(step t1 (cl (not A)) :rule resolution :premises (t1.w t1.b))";
        let kept = format!(
            "{LEFT}\n{RIGHT}\n(step t1.w (cl p (not q) r) :rule weakening :premises (t1.a))\n\
             {closing}\n"
        );
        assert!(chain_replays(&kept, "t1", "(cl p r)"));
        for weakened in [
            // reordered
            "(cl (not q) p r)",
            // a premise literal dropped
            "(cl p r)",
            // a premise literal re-spelled under two more `not`s
            "(cl (not (not p)) (not q) r)",
        ] {
            let text = format!(
                "{LEFT}\n{RIGHT}\n(step t1.w {weakened} :rule weakening :premises (t1.a))\n\
                 {closing}\n"
            );
            assert!(!chain_replays(&text, "t1", "(cl p r)"), "{weakened}");
        }
        let unknown = format!(
            "{LEFT}\n{RIGHT}\n(step t1.w (cl p (not q) r) :rule weakening :premises (t1.z))\n\
             {closing}\n"
        );
        assert!(!chain_replays(&unknown, "t1", "(cl p r)"));
    }

    #[test]
    fn a_missing_final_step_does_not_close() {
        let text = document("(step t1.c (cl p) :rule resolution :premises (t1.a t1.b))");
        assert!(!chain_replays(&text, "t1", "(cl p)"));
    }

    #[test]
    fn double_negation_is_the_same_literal() {
        let text = "(step t1.a (cl (not (not p)) (not q)) :rule or_pos)\n\
                    (step t1.b (cl q) :rule or_pos)\n\
                    (step t1 (cl (not A)) :rule resolution :premises (t1.a t1.b))\n";
        assert!(chain_replays(text, "t1", "(cl p)"));
    }

    #[test]
    fn a_repeated_step_name_is_refused() {
        let text = "(step t1.a (cl p (not q)) :rule or_pos)\n\
                    (step t1.b (cl q) :rule or_pos)\n\
                    (step t1.b (cl (not q)) :rule or_pos)\n\
                    (step t1 (cl (not A)) :rule resolution :premises (t1.a t1.b))\n";
        assert!(!chain_replays(text, "t1", "(cl p)"));
    }

    #[test]
    fn compound_literals_are_split_at_the_top_level() {
        let text = "(step t1.a (cl (= a b) (not (bvult c d))) :rule or_pos)\n\
                    (step t1.b (cl (bvult c d)) :rule or_pos)\n\
                    (step t1 (cl (not A)) :rule resolution :premises (t1.a t1.b))\n";
        assert!(chain_replays(text, "t1", "(cl (= a b))"));
    }

    #[test]
    fn an_n_ary_step_carrying_its_pivots_replays() {
        // Two links, on `q` then `r`, composing into `(cl p)`.
        let text = "(step t1.a (cl p (not q)) :rule or_pos)\n\
                    (step t1.b (cl q (not r)) :rule or_pos)\n\
                    (step t1.c (cl r) :rule or_pos)\n\
                    (step t1 (cl (not A)) :rule resolution :premises (t1.a t1.b t1.c) \
                     :args (q false r false))\n";
        assert!(chain_replays(text, "t1", "(cl p)"));
    }

    #[test]
    fn an_n_ary_step_whose_pivot_is_not_there_is_refused() {
        let text = "(step t1.a (cl p (not q)) :rule or_pos)\n\
                    (step t1.b (cl q) :rule or_pos)\n\
                    (step t1 (cl (not A)) :rule resolution :premises (t1.a t1.b) \
                     :args (p false))\n";
        assert!(!chain_replays(text, "t1", "(cl p)"));
    }

    #[test]
    fn an_n_ary_step_must_carry_one_pivot_per_link() {
        let text = "(step t1.a (cl p (not q)) :rule or_pos)\n\
                    (step t1.b (cl q (not r)) :rule or_pos)\n\
                    (step t1.c (cl r) :rule or_pos)\n\
                    (step t1 (cl (not A)) :rule resolution :premises (t1.a t1.b t1.c) \
                     :args (q false))\n";
        assert!(!chain_replays(text, "t1", "(cl p)"));
    }

    /// The consumer's `:args` path negates a pivot by ADDING a `not`, so
    /// `(not (not q))` and `q` are DIFFERENT literals to it. The replay has to
    /// agree, or it would bless a step the consumer rejects — which is the
    /// exact class of defect this module exists to prevent.
    #[test]
    fn a_double_negation_is_a_distinct_literal_under_explicit_pivots() {
        let text = "(step t1.a (cl p (not (not q))) :rule or_pos)\n\
                    (step t1.b (cl (not q)) :rule or_pos)\n\
                    (step t1 (cl (not A)) :rule resolution :premises (t1.a t1.b) \
                     :args (q false))\n";
        // Under a parity reading this "resolves" to `(cl p)`. Under the count
        // reading the pivot's complement is not in the first premise at all.
        assert!(!chain_replays(text, "t1", "(cl p)"));
    }

    /// The positive control for the same rule: naming the deeper literal
    /// explicitly is accepted, because then the counts line up.
    #[test]
    fn an_explicit_pivot_may_name_a_doubly_negated_literal() {
        let text = "(step t1.a (cl p (not (not q))) :rule or_pos)\n\
                    (step t1.b (cl (not (not (not q)))) :rule or_pos)\n\
                    (step t1 (cl (not A)) :rule resolution :premises (t1.a t1.b) \
                     :args ((not (not q)) true))\n";
        assert!(chain_replays(text, "t1", "(cl p)"));
    }

    /// A premise that PRINTS the pivot twice leaves a copy behind.
    ///
    /// The consumer folds a premise in by skipping only the FIRST occurrence
    /// of the pivot and inserting the rest, so the repeat survives into the
    /// accumulated clause. Collapsing it here made this replay agree with the
    /// TRANSPORT instead of with the CONSUMER, and the pinned checker
    /// (clean @ acdc24598, carcara d62d45c) rejected the resulting document at
    /// step `t1.cbbr2193` with `rule validation failed` — after AY had already
    /// replayed it. That is the disclosure outrunning the artifact again, so
    /// it is pinned here rather than left to care.
    #[test]
    fn a_premise_that_repeats_the_pivot_keeps_the_copy() {
        let text = "(step t1.a (cl p (not q) (not q)) :rule or_pos)\n\
                    (step t1.b (cl q q r) :rule or_pos)\n\
                    (step t1 (cl (not A)) :rule resolution :premises (t1.a t1.b) \
                     :args (q false))\n";
        // The surviving second `q` is part of the consumer's result, so the
        // tidy resolvent is NOT what this step derives.
        assert!(!chain_replays(text, "t1", "(cl p r)"));
        // and the clause that really is derived replays.
        assert!(chain_replays(text, "t1", "(cl p q r)"));
    }

    /// A word-level lemma printed under two `not`s may not carry pivots.
    ///
    /// The final step is replayed against the circuit-level spelling while the
    /// document prints the word-level lemma. The consumer reconciles them by
    /// inlining, which survives the parity reading but NOT the `:args` reading,
    /// because that one also compares negation depth. Measured on
    /// `str.post.gpr.w4`: resolvent computed at depth 0, lemma printed at depth
    /// 2, `checking failed on step 't1' with rule 'resolution'`.
    #[test]
    fn a_deeply_negated_final_lemma_may_not_carry_pivots() {
        let pivoted = "(step t1.a (cl p (not q)) :rule or_pos)\n\
                       (step t1.b (cl q) :rule or_pos)\n\
                       (step t1 (cl (not (not (= a b)))) :rule resolution :premises (t1.a t1.b) \
                        :args (q false))\n";
        assert!(!chain_replays(pivoted, "t1", "(cl p)"));

        // The SAME derivation without pivots stays on the parity path, which
        // does reconcile the two spellings, and is therefore still certified.
        let parity = "(step t1.a (cl p (not q)) :rule or_pos)\n\
                      (step t1.b (cl q) :rule or_pos)\n\
                      (step t1 (cl (not (not (= a b)))) :rule resolution :premises (t1.a t1.b))\n";
        assert!(chain_replays(parity, "t1", "(cl p)"));
    }

    #[test]
    fn an_n_ary_premise_that_was_never_printed_is_refused() {
        let text = "(step t1.a (cl p (not q)) :rule or_pos)\n\
                    (step t1 (cl (not A)) :rule resolution :premises (t1.a t1.z) \
                     :args (q false))\n";
        assert!(!chain_replays(text, "t1", "(cl p)"));
    }

    /// A negation count the `:args` encoding cannot hold is refused, never
    /// folded into the next base term's id.
    ///
    /// The counted reading packs a literal as `id * 256 + count`. Before the
    /// count was bounded, `a` (id 0) under 256 `not`s encoded as exactly `q`
    /// (id 1) under none, so the two DIFFERENT literals below cancelled and
    /// the replay certified the empty clause from `(cl ¬²⁵⁶a)` and
    /// `(cl (not q))`, which is not a resolution at all.
    #[test]
    fn a_negation_count_past_the_encoding_is_refused_not_aliased(
    ) -> Result<(), Box<dyn std::error::Error>> {
        let deep = format!("{}a{}", "(not ".repeat(256), ")".repeat(256));
        let text = format!(
            "(step t1.a (cl {deep}) :rule or_pos)\n\
             (step t1.b (cl (not q)) :rule or_pos)\n\
             (step t1 (cl (not A)) :rule resolution :premises (t1.a t1.b) \
             :args (q true))\n"
        );
        if chain_replays(&text, "t1", "(cl)") {
            return Err("a 256-deep negation of `a` was resolved against `q`".into());
        }
        // Positive control: a complement at 255 `not`s, the deepest count the
        // encoding holds, still replays as the resolution it is.
        let pivot = format!("{}a{}", "(not ".repeat(254), ")".repeat(254));
        let complement = format!("{}a{}", "(not ".repeat(255), ")".repeat(255));
        let text = format!(
            "(step t1.a (cl p {pivot}) :rule or_pos)\n\
             (step t1.b (cl {complement}) :rule or_pos)\n\
             (step t1 (cl (not A)) :rule resolution :premises (t1.a t1.b) \
             :args ({pivot} true))\n"
        );
        if !chain_replays(&text, "t1", "(cl p)") {
            return Err("a 255-deep complement no longer replays".into());
        }
        // The consumer's complement of a 255-deep pivot is 256 deep, which the
        // encoding cannot hold either: adding the `not` would carry into the
        // next id, making `b` (interned right after `a`) the complement of
        // `a` under 255 `not`s.
        let deepest = format!("{}a{}", "(not ".repeat(255), ")".repeat(255));
        let text = format!(
            "(step t1.a (cl p {deepest}) :rule or_pos)\n\
             (step t1.b (cl b) :rule or_pos)\n\
             (step t1 (cl (not A)) :rule resolution :premises (t1.a t1.b) \
             :args ({deepest} true))\n"
        );
        if chain_replays(&text, "t1", "(cl p)") {
            return Err("a 255-deep pivot was resolved against the next term `b`".into());
        }
        Ok(())
    }
}
