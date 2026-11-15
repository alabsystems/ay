//! Tokenizer for constraints in OPB format.

use logos::Logos;

/// Tokens used in the OPB format as [specified by the PB competition 2024](https://www.cril.univ-artois.fr/PB24/OPBgeneral.pdf).
#[derive(Debug, Logos, PartialEq, Eq)]
#[logos(skip r"[ \t\r\n]")]
pub enum OPBToken {
    /// Comment lines.
    #[regex("\\*.*", allow_greedy = true)]
    Comment,

    /// Integer used for coefficients or degree (right-hand side).
    #[regex("[+-]?[0-9]+")]
    Integer,

    /// OPB variable.
    #[regex("[a-zA-Z_][_a-zA-Z0-9\\-\\^\\[\\]\\{\\}]+")]
    Var,

    /// Negation symbol for a literal.
    #[token("~")]
    Negation,

    /// Greater than or equal comparison for PB constraint.
    #[token(">=")]
    GreaterEqual,

    /// Less than or equal comparison for PB constraint.
    #[token("<=")]
    LessEqual,

    /// Equal comparison for PB constraint.
    #[token("=")]
    Equal,

    /// Right implication of a reification shorthand, i.e., the conjunction of the literals on the left implies the constraint on the right.
    #[token("==>")]
    RightImplication,

    /// Left implication of a reification shorthand, i.e., the constraint on the right implies the single literal on the left.
    #[token("<==")]
    LeftImplication,

    /// Equivalence of a reification shorthand, i.e., the single literal on the left and the constraint on the right imply each other.
    #[token("<==>")]
    Equivalence,

    /// Semicolon which should end a PB constraint.
    #[token(";")]
    Semicolon,

    /// Label to start the objective function that should be minimized.
    #[token("min:")]
    Minimize,

    /// Label to start the objective function that should be maximized. While we support maximization objectives in the OPB file, internally the objective is always minimized.
    #[token("max:")]
    Maximize,

    /// Constraint labels similar to the ones used in the proof format.
    #[regex("@[a-zA-Z0-9_\\-\\^\\[\\]\\{\\}]+")]
    Label,

    // Preserved set of variables.
    #[token("preserved:")]
    Preserved,
}

#[cfg(test)]
mod test {
    use logos::Logos;

    use crate::opb_token::OPBToken;

    #[test]
    fn integer() {
        let mut lex = OPBToken::lexer("424 -424 +424 +004");

        assert_eq!(lex.next(), Some(Ok(OPBToken::Integer)));
        assert_eq!(lex.next(), Some(Ok(OPBToken::Integer)));
        assert_eq!(lex.next(), Some(Ok(OPBToken::Integer)));
        assert_eq!(lex.next(), Some(Ok(OPBToken::Integer)));
        assert_eq!(lex.slice().parse::<i64>().unwrap(), 4);
        assert_eq!(lex.next(), None);
    }

    #[test]
    fn variable() {
        let mut lex = OPBToken::lexer("x12 _x12 xaK2-[]{}_^");

        assert_eq!(lex.next(), Some(Ok(OPBToken::Var)));
        assert_eq!(lex.next(), Some(Ok(OPBToken::Var)));
        assert_eq!(lex.next(), Some(Ok(OPBToken::Var)));
        assert_eq!(lex.next(), None);
    }

    #[test]
    fn implication() {
        let mut lex = OPBToken::lexer("==> <== <==> >= <= =");

        assert_eq!(lex.next(), Some(Ok(OPBToken::RightImplication)));
        assert_eq!(lex.next(), Some(Ok(OPBToken::LeftImplication)));
        assert_eq!(lex.next(), Some(Ok(OPBToken::Equivalence)));
        assert_eq!(lex.next(), Some(Ok(OPBToken::GreaterEqual)));
        assert_eq!(lex.next(), Some(Ok(OPBToken::LessEqual)));
        assert_eq!(lex.next(), Some(Ok(OPBToken::Equal)));
        assert_eq!(lex.next(), None);
    }

    #[test]
    fn equivalence_is_not_a_left_implication() {
        // The two share a prefix, so the longer one has to win.
        let mut lex = OPBToken::lexer("<==>x1");

        assert_eq!(lex.next(), Some(Ok(OPBToken::Equivalence)));
        assert_eq!(lex.next(), Some(Ok(OPBToken::Var)));
        assert_eq!(lex.next(), None);
    }

    #[test]
    fn comment() {
        let mut lex = OPBToken::lexer("*sdf sdafsd ffsdf sdf asdf dsfsdf 12 sda f\n*\n11");

        assert_eq!(lex.next(), Some(Ok(OPBToken::Comment)));
        assert_eq!(lex.next(), Some(Ok(OPBToken::Comment)));
        assert_eq!(lex.next(), Some(Ok(OPBToken::Integer)));
        assert_eq!(lex.next(), None);
    }
}
