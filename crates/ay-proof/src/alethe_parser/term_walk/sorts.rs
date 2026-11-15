// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Sort constructors also nest; a term trampoline must not retain a recursive
//! escape through binder annotations or qualified identifiers.

use super::*;

pub(in crate::alethe_parser) fn check(
    checker: &AletheDocumentChecker,
    lexer: &mut Lexer<'_>,
) -> Result<(), AletheDefect> {
    let mut open = 0usize;
    loop {
        let (token, pos) = lexer.next_token()?;
        match token {
            Tok::Symbol(name) => known_sort(checker, &name, pos)?,
            Tok::Open => {
                check_depth(open + 1, pos)?;
                if constructor(checker, lexer)? {
                    open += 1;
                    continue;
                }
            }
            Tok::Close if open != 0 => open -= 1,
            other => return Err(unexpected(pos, "a sort", other)),
        }
        if open == 0 {
            return Ok(());
        }
    }
}

/// True leaves a parametric constructor open; an indexed sort consumes its
/// own closing token and needs no continuation. No new grammar is admitted.
fn constructor(
    checker: &AletheDocumentChecker,
    lexer: &mut Lexer<'_>,
) -> Result<bool, AletheDefect> {
    let (head, pos) = lexer.next_token()?;
    let Tok::Symbol(name) = head else {
        return Err(unexpected(pos, "a sort constructor", head));
    };
    if name == "_" {
        indexed(lexer)?;
        return Ok(false);
    }
    if !BUILTIN_SORT_CONSTRUCTORS.contains(&name.as_str()) && !checker.scope.contains_sort(&name) {
        return Err(AletheDefect::UndefinedSort { pos, name });
    }
    Ok(true)
}

fn indexed(lexer: &mut Lexer<'_>) -> Result<(), AletheDefect> {
    let (token, pos) = lexer.next_token()?;
    let Tok::Symbol(name) = token else {
        return Err(unexpected(pos, "an indexed sort name", token));
    };
    if !BUILTIN_INDEXED_SORTS.contains(&name.as_str()) {
        return Err(AletheDefect::UndefinedSort { pos, name });
    }
    loop {
        let (token, pos) = lexer.next_token()?;
        match token {
            Tok::Close => return Ok(()),
            Tok::Numeral(_) => {}
            other => return Err(unexpected(pos, "a sort index", other)),
        }
    }
}

fn known_sort(checker: &AletheDocumentChecker, name: &str, pos: Pos) -> Result<(), AletheDefect> {
    if BUILTIN_SORTS.contains(&name) || checker.scope.contains_sort(name) {
        Ok(())
    } else {
        Err(AletheDefect::UndefinedSort {
            pos,
            name: name.to_string(),
        })
    }
}
