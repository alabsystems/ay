//! Lexer for the VeriPB version 3 parser.

use crate::error::ParserError;
use crate::pbp_parser::parser::ParserArgs;
use crate::pbp_parser::reader::{Reader, StreamReader};
use crate::pbp_parser::utils::{Position, Token};
use malachite_base::num::conversion::traits::FromStringBase;
use malachite_bigint::{BigInt, BigUint, Sign};
use malachite_nz::natural::Natural;
use std::io::BufRead;

type Result<T> = std::result::Result<T, ParserError>;

/// The current parsing mode for the bit-width of integers.
#[derive(Debug, PartialEq, PartialOrd)]
pub enum IntegerParseMode {
    // Bits64 < Bits128 < BitsAny
    Bits64,
    Bits128,
    BitsAny,
}

fn is_letter_or_underscore(c: u8) -> bool {
    c.is_ascii_alphabetic() || c == b'_'
}

fn is_start_of_identifier_symbol(c: u8) -> bool {
    is_letter_or_underscore(c) || c == b'@' || c == b'$'
}

fn is_identifier_symbol(c: u8) -> bool {
    is_letter_or_underscore(c)
        || c.is_ascii_digit()
        || c == b'['
        || c == b']'
        || c == b'{'
        || c == b'}'
        || c == b'^'
        || c == b'-'
}

fn format_option(option: Option<&u8>) -> String {
    if let Some(c) = option {
        format!("`{}`", char::from_u32(*c as u32).unwrap().escape_default())
    } else {
        "EOF".to_string()
    }
}

/// Lexer for the VeriPB version 3 proof format.
pub struct Lexer<'a, R: BufRead> {
    reader: StreamReader<'a, R>,
    buffer: Vec<u8>,
    do_dynamic_integer_parse_mode: bool,
    integer_parse_mode: IntegerParseMode,
    prev_pos: Position,
    pos: Position,
}

impl<'a, R: BufRead> Lexer<'a, R> {
    /// Construct a new [`Lexer`] for the given `derivation_reader` and using the parsing arguments `args`.
    pub fn new(file_size: Option<u64>, derivation_reader: &'a mut R, args: &ParserArgs) -> Self {
        Self {
            reader: StreamReader::new(file_size, derivation_reader, args.trace_enabled),
            buffer: Vec::with_capacity(1024),
            do_dynamic_integer_parse_mode: false,
            integer_parse_mode: IntegerParseMode::Bits64,
            prev_pos: Position {
                pos: 0,
                col: 1,
                line: 1,
            },
            pos: Position {
                pos: 0,
                col: 1,
                line: 1,
            },
        }
    }

    /// Get the position in the proof file until which the [`Lexer`] has lexed the file.
    pub fn get_pos(&self) -> Position {
        self.prev_pos.clone()
    }

    /// Get the line number until which the [`Lexer`] has lexed the file.
    pub fn get_line(&self) -> usize {
        self.prev_pos.line - 1
    }

    /// Get the total size of the VeriPB proof file.
    pub fn get_len(&self) -> Option<u64> {
        self.reader.get_size()
    }

    /// Set the current [`IntegerParseMode`] for the [`Lexer`] to `mode`.
    pub fn set_integer_parse_mode(&mut self, mode: IntegerParseMode) {
        self.integer_parse_mode = mode;
    }

    /// Enable integer parsing in the [`Lexer`] to dynamically adjust to the required bit-width of the integer.
    pub fn enable_dynamic_integer_parse_mode(&mut self) {
        self.do_dynamic_integer_parse_mode = true;
    }

    /// Disable integer parsing in the [`Lexer`] to dynamically adjust to the required bit-width of the integer.
    pub fn disable_dynamic_integer_parse_mode(&mut self) {
        self.do_dynamic_integer_parse_mode = false;
        self.set_integer_parse_mode(IntegerParseMode::Bits64);
    }

    /// Lex the next token.
    pub fn get_next_token(&mut self) -> Result<Token> {
        self.prev_pos = self.pos.clone();
        match self.reader.peek() {
            Some(b' ') => Ok(self.space()),
            Some(b'\t') => Ok(self.tab()),
            Some(b'\r') | Some(b'\n') => Ok(self.eol()),
            Some(b'%') => self.comment(),
            Some(c) if is_start_of_identifier_symbol(*c) => self.identifier(),
            Some(b'+') => self.plus_sign_or_integer(),
            Some(b'-') => self.minus_sign_or_maps_to_or_integer(),
            Some(c) if c.is_ascii_digit() => self.unsigned_integer(Sign::NoSign),
            Some(b'#') => self.proofgoal_id(),
            Some(b':') => Ok(self.single(Token::Colon)),
            Some(b';') => Ok(self.single(Token::Semicolon)),
            Some(b'~') => Ok(self.single(Token::Tilde)),
            Some(b'>') => self.greater_equal(),
            Some(b'<') => self.left_implication_or_less_equal(),
            Some(b'=') => self.equal_or_right_implication(),
            Some(b'*') => Ok(self.single(Token::Star)),
            Some(b'.') => Ok(self.single(Token::Dot)),
            Some(c) => {
                let message = format!("Unexpected character `{}`", std::ascii::escape_default(*c));
                Err(self.report_error(message, self.get_pos(), 1))
            }
            None => Ok(Token::Eof),
        }
    }

    /// Advance the [`Lexer`] until an end-of-line is encountered.
    pub fn skip_to_eol(&mut self) -> Result<()> {
        self.comment()?;
        Ok(())
    }

    /// Consume bytes up to and including the next `;` (unless `;` appears in a
    /// line comment starting with `%` which is ignored as usual).
    /// The terminating `;` and commented lines are not passed to `consumed_bytes`,
    /// but everything else (including newlines) is.
    ///
    /// `error_context` should be a string to be printed in error messages describing
    /// the context in which `consume_to_semicolon` was used.
    /// `byte_consumer` is a callback that is sent the consumed bytes.
    fn consume_to_semicolon(
        &mut self,
        error_context: &str,
        mut byte_consumer: impl FnMut(u8),
    ) -> Result<()> {
        loop {
            // A comment is read and ignored, including any `;` it contains.
            if let Some(b'%') = self.reader.peek() {
                self.comment()?;
                continue;
            }
            let Some(byte) = self.reader.next() else {
                return Err(self.report_error(
                    format!("Expected `;` at the end of {error_context} but found EOF"),
                    self.pos.clone(),
                    0,
                ));
            };
            match byte {
                b';' => break,
                b'\n' => {
                    byte_consumer(byte);
                    self.pos.col = 0;
                    self.pos.line += 1;
                }
                b'\r' => {
                    byte_consumer(byte);
                    if let Some(b'\n') = self.reader.peek() {
                        byte_consumer(b'\n');
                        self.pos.pos += 1;
                        self.reader.next();
                    }
                    self.pos.col = 0;
                    self.pos.line += 1;
                }
                _ => byte_consumer(byte),
            }
            self.pos.pos += 1;
            self.pos.col += 1;
        }
        self.pos.pos += 1;
        self.pos.col += 1;
        Ok(())
    }

    /// Skips to the next semicolon (not contained within in a commented line).
    pub fn skip_to_semicolon(&mut self, error_context: &str) -> Result<()> {
        self.consume_to_semicolon(error_context, |_| {})
    }

    /// Reads to the next semicolon (no contained within in a commented line) and
    /// returns the read bytes (not including comments) as a string.
    pub fn read_to_semicolon(&mut self, error_context: &str) -> Result<String> {
        let mut buf: Vec<u8> = Vec::new();
        self.consume_to_semicolon(error_context, |b| buf.push(b))?;
        String::from_utf8(buf).map_err(|e| {
            self.report_error(
                format!("Invalid UTF-8 in {error_context}: {e}"),
                self.pos.clone(),
                0,
            )
        })
    }

    /// Format a parsing error.
    pub fn report_error(&mut self, message: String, pos: Position, len: usize) -> ParserError {
        let line = self.reader.get_current_line().replace('\t', "    ");
        ParserError::pbp_error(message, pos, len, line)
    }

    /// Flush the buffered proof file source accumulated since the last rule.
    ///
    /// The buffered source is printed when `do_print` is `true`; otherwise it is
    /// discarded. In both cases the buffer is cleared and the trace position is
    /// advanced so that subsequent traced rules show the correct lines.
    pub fn flush_trace(&mut self, do_print: bool) {
        self.reader.print_trace(&self.pos, do_print);
    }

    /// Tokenize any number of spaces into a [`Token::Space`].
    fn space(&mut self) -> Token {
        let mut len = 1;
        self.reader.next();
        while let Some(b' ') = self.reader.peek() {
            len += 1;
            self.reader.next();
        }
        self.pos.pos += len;
        self.pos.col += len;
        Token::Space(len)
    }

    /// Tokenize any number of tabs into a [`Token::Tab`].
    fn tab(&mut self) -> Token {
        let mut len = 1;
        self.reader.next();
        while let Some(b'\t') = self.reader.peek() {
            len += 1;
            self.reader.next();
        }
        self.pos.pos += len;
        self.pos.col += len;
        Token::Tab(len)
    }

    /// Tokenize any number of end-of-line characters into a [`Token::Eol`].
    fn eol(&mut self) -> Token {
        let mut len = 0;
        if let Some(b'\r') = self.reader.peek() {
            self.reader.next();
            len += 1;
        };
        if let Some(b'\n') = self.reader.peek() {
            self.reader.next();
            len += 1;
        };
        self.pos.pos += len;
        self.pos.col = 1;
        self.pos.line += 1;
        Token::Eol(len)
    }

    /// Tokenize a comment.
    fn comment(&mut self) -> Result<Token> {
        self.buffer.clear();
        self.reader.next();
        let mut len = 1;
        loop {
            len += 1;
            match self.reader.next() {
                Some(b'\n') => break,
                Some(b'\r') => {
                    if let Some(b'\n') = self.reader.peek() {
                        len += 1;
                        self.reader.next();
                    };
                    break;
                },
                None => return Err(self.report_error(
                    "Expected newline (`\\r`, `\\n` or `\\r\\n`) at the end of comment but found EOF".to_string(),
                    self.get_pos(),
                    len,
                )),
                Some(c) => self.buffer.push(c),
            };
        }
        self.pos.pos += len;
        self.pos.col = 1;
        self.pos.line += 1;
        // A `%` comment is the one token whose bytes are unconstrained — everything else in this
        // lexer is built from bytes an ASCII predicate has already accepted. `from_utf8_unchecked`
        // here made an invalid `String` out of any comment holding a non-UTF-8 byte, which is
        // undefined behaviour at the moment of construction, before anything reads it. Checked,
        // with the same shape `read_to_semicolon` above already uses for the same reason.
        let comment = String::from_utf8(self.buffer.clone()).map_err(|error| {
            self.report_error(
                format!("Invalid UTF-8 in comment: {error}"),
                self.get_pos(),
                0,
            )
        })?;
        Ok(Token::Comment(comment))
    }

    /// Tokenize an identifier.
    fn identifier(&mut self) -> Result<Token> {
        self.buffer.clear();
        self.buffer.push(self.reader.next().unwrap());
        while let Some(c) = self.reader.peek() {
            if !is_identifier_symbol(*c) {
                break;
            };
            self.buffer.push(self.reader.next().unwrap());
        }
        let len = self.buffer.len();
        if self.buffer[0] == b'@' && len == 1 {
            return Err(self.report_error(
                "Expected complete label starting with `@` followed by at least one character but only found `@`".to_string(),
                self.get_pos(),
                len,
            ));
        };
        if self.buffer[0] == b'$' && len == 1 {
            return Err(self.report_error(
                "Expected auxiliary variable starting with `$` followed by at least one character but only found `$`".to_string(),
                self.get_pos(),
                len,
            ));
        };
        self.pos.pos += len;
        self.pos.col += len;
        let identifier = unsafe { String::from_utf8_unchecked(self.buffer.clone()) };
        match self.buffer[0] {
            b'@' => Ok(Token::Label(identifier)),
            b'$' => Ok(Token::AuxiliaryVariable(identifier)),
            _ => Ok(Token::Identifier(identifier)),
        }
    }

    /// Tokenize a `+` token [`Token::Plus`] or positive signed integer.
    fn plus_sign_or_integer(&mut self) -> Result<Token> {
        self.reader.next();
        self.pos.pos += 1;
        self.pos.col += 1;
        match self.reader.peek() {
            Some(c) if c.is_ascii_digit() => self.unsigned_integer(Sign::Plus),
            _ => Ok(Token::Plus),
        }
    }

    /// Tokenize a `-` token [`Token::Minus`], a maps to `->` token [`Token::MapsTo`], or a negative integer.
    fn minus_sign_or_maps_to_or_integer(&mut self) -> Result<Token> {
        self.reader.next();
        self.pos.pos += 1;
        self.pos.col += 1;
        match self.reader.peek() {
            Some(b'>') => {
                self.reader.next();
                self.pos.pos += 1;
                self.pos.col += 1;
                Ok(Token::MapsTo)
            }
            Some(c) if c.is_ascii_digit() => self.unsigned_integer(Sign::Minus),
            _ => Ok(Token::Minus),
        }
    }

    /// Parse an unsigned integer.
    fn unsigned_integer(&mut self, sign: Sign) -> Result<Token> {
        self.buffer.clear();
        self.buffer.push(self.reader.next().unwrap());
        while let Some(c) = self.reader.peek() {
            if !c.is_ascii_digit() {
                break;
            };
            self.buffer.push(*c);
            self.reader.next();
        }
        let result = unsafe { String::from_utf8_unchecked(self.buffer.clone()) };
        let len = self.buffer.len();
        let is_zero = self.buffer[0] == b'0';
        if is_zero && len > 1 {
            Err(self.report_error(
                format!(
                    "The integer `{}{}` may not contain leading zeros",
                    if sign == Sign::Plus {
                        "+"
                    } else if sign == Sign::Minus && is_zero {
                        "-"
                    } else {
                        ""
                    },
                    result
                ),
                self.get_pos(),
                len,
            ))
        } else {
            self.pos.pos += len;
            self.pos.col += len;
            let mode = match result {
                ref s if s.len() < 19 || (s.len() == 19 && &**s <= "9223372036854775807") => {
                    IntegerParseMode::Bits64
                }
                ref s
                    if s.len() < 39
                        || (s.len() == 39 && &**s <= "170141183460469231731687303715884105727") =>
                {
                    IntegerParseMode::Bits128
                }
                _ => IntegerParseMode::BitsAny,
            };
            if self.integer_parse_mode < mode {
                if self.do_dynamic_integer_parse_mode {
                    self.integer_parse_mode = mode;
                } else {
                    return Err(self.report_error(
                        format!("The integer `{}{}` does not fit within 64 bits (as required in this context)", if sign == Sign::Plus {"+"} else if sign == Sign::Minus && is_zero {"-"} else {""}, result),
                        self.get_pos(),
                        len,
                    ));
                };
            };
            match self.integer_parse_mode {
                IntegerParseMode::Bits64 => {
                    let integer = if sign == Sign::Minus {
                        -result.parse::<i64>().unwrap()
                    } else {
                        result.parse::<i64>().unwrap()
                    };
                    Ok(Token::Integer64(sign, integer))
                }
                IntegerParseMode::Bits128 => {
                    let integer = if sign == Sign::Minus {
                        -result.parse::<i128>().unwrap()
                    } else {
                        result.parse::<i128>().unwrap()
                    };
                    Ok(Token::Integer128(sign, integer))
                }
                IntegerParseMode::BitsAny => {
                    // Hack to avoid checking UTF-8.
                    let natural = Natural::from_string_base(10, &result).unwrap();
                    let bigint = BigInt::from_biguint(
                        if sign == Sign::NoSign {
                            Sign::Plus
                        } else {
                            sign
                        },
                        Into::<BigUint>::into(natural),
                    );
                    Ok(Token::IntegerAny(sign, bigint))
                }
            }
        }
    }

    /// Parse a proof goal ID.
    fn proofgoal_id(&mut self) -> Result<Token> {
        self.reader.next();
        self.pos.pos += 1;
        self.pos.col += 1;
        match self.reader.peek() {
            Some(c) if c.is_ascii_digit() => match self.unsigned_integer(Sign::NoSign)? {
                Token::Integer64(_, 0) => Err(self.report_error(
                    "Expected a positive proofgoal ID but found `#0`".to_string(),
                    self.get_pos(),
                    2,
                )),
                Token::Integer64(_, id) => Ok(Token::ProofgoalID(id as usize)),
                _ => panic!("UNREACHABLE"),
            },
            option => {
                let message = format!(
                    "Expected complete proofgoal ID as `#` followed by an unsigned integer but found {} after `#`",
                    format_option(option)
                );
                Err(self.report_error(message, self.get_pos(), 1))
            }
        }
    }

    /// Lex a greater equal `>=` token [`Token::GreaterEqual`].
    fn greater_equal(&mut self) -> Result<Token> {
        self.reader.next();
        match self.reader.peek() {
            Some(b'=') => self.reader.next(),
            option => {
                let message = format!(
                    "Expected complete operator `>=` but found {} as the second character",
                    format_option(option)
                );
                return Err(self.report_error(message, self.get_pos(), 2));
            }
        };
        self.pos.pos += 2;
        self.pos.col += 2;
        Ok(Token::GreaterEqual)
    }

    /// Lex left implication `<==` token [`Token::LeftImplication`] or a less equal `<=` token [`Token::LessEqual`].
    fn left_implication_or_less_equal(&mut self) -> Result<Token> {
        self.reader.next();
        match self.reader.peek() {
            Some(b'=') => self.reader.next(),
            option => {
                let message = format!(
                    "Expected complete operator `<=` or `<==` but found {} as the second character",
                    format_option(option)
                );
                return Err(self.report_error(message, self.get_pos(), 2));
            }
        };
        let (len, token) = match self.reader.peek() {
            Some(b'=') => {
                self.reader.next();
                (3, Token::LeftImplication)
            }
            _ => (2, Token::LessEqual),
        };
        self.pos.pos += len;
        self.pos.col += len;
        Ok(token)
    }

    /// Lex right implication `==>` token [`Token::RightImplication`] or a equal `=` token [`Token::Equal`].
    fn equal_or_right_implication(&mut self) -> Result<Token> {
        self.reader.next();
        match self.reader.peek() {
            Some(b'=') => self.reader.next(),
            _ => {
                self.pos.pos += 1;
                self.pos.col += 1;
                return Ok(Token::Equal);
            }
        };
        match self.reader.peek() {
            Some(b'>') => self.reader.next(),
            option => {
                let message = format!(
                    "Expected complete operator `==>` but found {} as the third character",
                    format_option(option)
                );
                return Err(self.report_error(message, self.get_pos(), 3));
            }
        };
        self.pos.pos += 3;
        self.pos.col += 3;
        Ok(Token::RightImplication)
    }

    /// Lex a single character token.
    fn single(&mut self, token: Token) -> Token {
        self.reader.next();
        self.pos.pos += 1;
        self.pos.col += 1;
        token
    }
}
