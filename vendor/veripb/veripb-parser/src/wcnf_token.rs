//! Tokenizer for WCNF MaxSAT files.

use logos::Logos;

/// Tokens used in the OPB format as specified by the [MaxSAT Evaluation 2022](https://maxsat-evaluations.github.io/2022/rules.html#input).
#[derive(Debug, Logos, PartialEq, Eq)]
#[logos(skip r"[ \t\r\n]")]
pub enum WCNFToken {
    /// Comment lines.
    #[regex("c.*", allow_greedy = true)]
    Comment,

    /// Identifier for a hard clause.
    #[token("h")]
    HardClause,

    /// Integer used to identify literals or end clauses.
    #[regex("[+-]?[0-9]+")]
    Integer,
}

#[cfg(test)]
mod test {
    use logos::Logos;

    use crate::wcnf_token::WCNFToken;

    #[test]
    fn comments() {
        let mut lex = WCNFToken::lexer("c adfsde\ncsdae\nc\n");

        assert_eq!(lex.next(), Some(Ok(WCNFToken::Comment)));
        assert_eq!(lex.next(), Some(Ok(WCNFToken::Comment)));
        assert_eq!(lex.next(), Some(Ok(WCNFToken::Comment)));
        assert_eq!(lex.next(), None);
    }

    #[test]
    fn hard_clause() {
        let mut lex = WCNFToken::lexer("h 31 123 0");

        assert_eq!(lex.next(), Some(Ok(WCNFToken::HardClause)));
        assert_eq!(lex.next(), Some(Ok(WCNFToken::Integer)));
        assert_eq!(lex.next(), Some(Ok(WCNFToken::Integer)));
        assert_eq!(lex.next(), Some(Ok(WCNFToken::Integer)));
        assert_eq!(lex.next(), None);
    }

    #[test]
    fn soft_clauses() {
        let mut lex = WCNFToken::lexer("-23442 1 2 0");

        assert_eq!(lex.next(), Some(Ok(WCNFToken::Integer)));
        assert_eq!(lex.next(), Some(Ok(WCNFToken::Integer)));
        assert_eq!(lex.next(), Some(Ok(WCNFToken::Integer)));
        assert_eq!(lex.next(), Some(Ok(WCNFToken::Integer)));
        assert_eq!(lex.next(), None);
    }
}
