//! How many responses a refused CHC script owes.
//!
//! SMT-LIB answers every `check-sat` and `check-sat-assuming` with one response.
//! When the CHC runner refuses a whole script (an incremental script, a command
//! whose effect on the clause set it does not model, a parse error), it answers
//! each of them `unknown`. A caller that pairs responses with checks, as z3's
//! transcripts and the differential gate do, then reads the refusal as unknowns
//! rather than as a transcript cut short: the gate's chc family reported
//! `unknown` for a two-check script as an ABORT (spell_1, wit_06).

use std::iter::Peekable;
use std::str::Chars;

/// The number of top-level `check-sat` and `check-sat-assuming` commands in
/// `script`, and at least 1.
///
/// A lexical scan: `;` comments, `"..."` string literals (with `""` escapes)
/// and `|...|` quoted symbols are skipped, so a command name inside them is
/// not counted. A script too malformed to scan still owes one response.
pub(crate) fn owed_check_sat_responses(script: &str) -> usize {
    let mut chars = script.chars().peekable();
    let mut depth = 0usize;
    let mut checks = 0usize;
    while let Some(c) = chars.next() {
        match c {
            ';' => skip_through(&mut chars, '\n'),
            '|' => skip_through(&mut chars, '|'),
            '"' => skip_string(&mut chars),
            '(' => {
                if depth == 0 && is_check_sat(&head_symbol(&mut chars)) {
                    checks += 1;
                }
                depth += 1;
            }
            ')' => depth = depth.saturating_sub(1),
            _ => {}
        }
    }
    checks.max(1)
}

fn is_check_sat(head: &str) -> bool {
    head == "check-sat" || head == "check-sat-assuming"
}

fn skip_through(chars: &mut Peekable<Chars<'_>>, end: char) {
    for c in chars.by_ref() {
        if c == end {
            return;
        }
    }
}

/// An SMT-LIB 2.6 string literal: `""` inside it is an escaped quote.
fn skip_string(chars: &mut Peekable<Chars<'_>>) {
    while let Some(c) = chars.next() {
        if c == '"' && chars.next_if_eq(&'"').is_none() {
            return;
        }
    }
}

/// The symbol right after an opening parenthesis, without consuming the
/// delimiter that ends it.
fn head_symbol(chars: &mut Peekable<Chars<'_>>) -> String {
    while chars.next_if(|c| c.is_whitespace()).is_some() {}
    let mut head = String::new();
    while let Some(c) =
        chars.next_if(|c| !c.is_whitespace() && !matches!(c, '(' | ')' | ';' | '"' | '|'))
    {
        head.push(c);
    }
    head
}

#[cfg(test)]
mod tests {
    use super::owed_check_sat_responses as owed;

    #[test]
    fn counts_each_top_level_check() {
        let script = "(set-logic HORN)\n(assert true)\n(check-sat)\n(assert false)\n(check-sat)\n";
        assert_eq!(owed(script), 2);
        assert_eq!(owed("(check-sat-assuming (p))(check-sat)(exit)"), 2);
        assert_eq!(owed("( check-sat )"), 1);
    }

    #[test]
    fn a_script_without_checks_still_owes_one_response() {
        assert_eq!(owed(""), 1);
        assert_eq!(owed("(set-logic HORN)(assert true)"), 1);
        assert_eq!(owed("(((("), 1);
    }

    #[test]
    fn names_inside_comments_strings_quoted_symbols_and_terms_do_not_count() {
        let script = concat!(
            "; (check-sat)\n",
            "(set-info :source \"(check-sat) \"\" (check-sat)\")\n",
            "(declare-fun |(check-sat)| () Bool)\n",
            "(assert (check-sat))\n",
            "(check-sat)\n",
        );
        assert_eq!(owed(script), 1);
    }
}
