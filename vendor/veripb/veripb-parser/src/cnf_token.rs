//! Tokenizer for DIMACS CNF formulas.

use std::num::ParseIntError;

use logos::Logos;

/// Tokens used in the OPB format as [specified by the PB competition 2024](https://www.cril.univ-artois.fr/PB24/OPBgeneral.pdf).
#[derive(Debug, Logos, PartialEq, Eq)]
#[logos(skip r"[ \t\r\n]")]
pub enum CNFToken {
    /// Comment lines.
    #[regex("c.*", allow_greedy = true)]
    Comment,

    /// DIMACS CNF problem header identifier.
    #[token("p cnf")]
    ProblemHeader,

    /// Integer used to for number of variables, number of clauses, to identify literals, or to end clause.
    #[regex("[+-]?[0-9]+", |lex| Some(lex.slice().parse()))]
    Integer(Result<isize, ParseIntError>),
}

#[cfg(test)]
mod test {
    use logos::Logos;

    use crate::cnf_token::CNFToken;

    #[test]
    fn comments() {
        let mut lex = CNFToken::lexer("c adfsde\ncsdae\nc\n");

        assert_eq!(lex.next(), Some(Ok(CNFToken::Comment)));
        assert_eq!(lex.next(), Some(Ok(CNFToken::Comment)));
        assert_eq!(lex.next(), Some(Ok(CNFToken::Comment)));
        assert_eq!(lex.next(), None);
    }

    #[test]
    fn header() {
        let mut lex = CNFToken::lexer("p cnf 31 123");

        assert_eq!(lex.next(), Some(Ok(CNFToken::ProblemHeader)));
        assert_eq!(lex.next(), Some(Ok(CNFToken::Integer(Ok(31)))));
        assert_eq!(lex.next(), Some(Ok(CNFToken::Integer(Ok(123)))));
        assert_eq!(lex.next(), None);
    }

    #[test]
    fn clauses() {
        let mut lex = CNFToken::lexer("1 2 0\n2 3 0");

        assert_eq!(lex.next(), Some(Ok(CNFToken::Integer(Ok(1)))));
        assert_eq!(lex.next(), Some(Ok(CNFToken::Integer(Ok(2)))));
        assert_eq!(lex.next(), Some(Ok(CNFToken::Integer(Ok(0)))));
        assert_eq!(lex.next(), Some(Ok(CNFToken::Integer(Ok(2)))));
        assert_eq!(lex.next(), Some(Ok(CNFToken::Integer(Ok(3)))));
        assert_eq!(lex.next(), Some(Ok(CNFToken::Integer(Ok(0)))));
        assert_eq!(lex.next(), None);
    }
}
