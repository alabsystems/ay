// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Just enough JSON to read `cargo metadata` output in a build script, which
//! has only the standard library. Anything malformed is `None`: the caller
//! then falls back to a scope that vouches for less, never for more.

/// A parsed JSON value. Nothing here reads a number, boolean or null, so
/// those are one variant.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum Value {
    Scalar,
    String(String),
    Array(Vec<Value>),
    Object(Vec<(String, Value)>),
}

impl Value {
    /// The member `key` of an object.
    pub(crate) fn get(&self, key: &str) -> Option<&Value> {
        match self {
            Value::Object(members) => members
                .iter()
                .find(|(name, _)| name == key)
                .map(|(_, value)| value),
            _ => None,
        }
    }

    pub(crate) fn as_str(&self) -> Option<&str> {
        match self {
            Value::String(text) => Some(text),
            _ => None,
        }
    }

    pub(crate) fn as_array(&self) -> Option<&[Value]> {
        match self {
            Value::Array(items) => Some(items),
            _ => None,
        }
    }
}

/// Nesting deeper than this is refused rather than recursed into.
const MAX_DEPTH: usize = 128;

/// Parse one complete JSON document.
pub(crate) fn parse(text: &str) -> Option<Value> {
    let mut parser = Parser {
        bytes: text.as_bytes(),
        pos: 0,
        depth: 0,
    };
    let value = parser.value()?;
    parser.skip_whitespace();
    (parser.pos == parser.bytes.len()).then_some(value)
}

struct Parser<'a> {
    bytes: &'a [u8],
    pos: usize,
    depth: usize,
}

impl Parser<'_> {
    fn value(&mut self) -> Option<Value> {
        self.skip_whitespace();
        match self.peek()? {
            b'{' => self.nested(Self::object),
            b'[' => self.nested(Self::array),
            b'"' => self.string().map(Value::String),
            b't' => self.literal("true"),
            b'f' => self.literal("false"),
            b'n' => self.literal("null"),
            _ => self.number(),
        }
    }

    fn nested(&mut self, parse: fn(&mut Self) -> Option<Value>) -> Option<Value> {
        if self.depth >= MAX_DEPTH {
            return None;
        }
        self.depth += 1;
        let value = parse(self);
        self.depth -= 1;
        value
    }

    fn object(&mut self) -> Option<Value> {
        self.pos += 1;
        let mut members = Vec::new();
        self.skip_whitespace();
        if self.eat(b'}') {
            return Some(Value::Object(members));
        }
        loop {
            self.skip_whitespace();
            if self.peek()? != b'"' {
                return None;
            }
            let name = self.string()?;
            self.skip_whitespace();
            if !self.eat(b':') {
                return None;
            }
            members.push((name, self.value()?));
            self.skip_whitespace();
            if !self.eat(b',') {
                return self.eat(b'}').then_some(Value::Object(members));
            }
        }
    }

    fn array(&mut self) -> Option<Value> {
        self.pos += 1;
        let mut items = Vec::new();
        self.skip_whitespace();
        if self.eat(b']') {
            return Some(Value::Array(items));
        }
        loop {
            items.push(self.value()?);
            self.skip_whitespace();
            if !self.eat(b',') {
                return self.eat(b']').then_some(Value::Array(items));
            }
        }
    }

    fn string(&mut self) -> Option<String> {
        self.pos += 1;
        let mut text = String::new();
        loop {
            let start = self.pos;
            while self
                .peek()
                .is_some_and(|byte| byte != b'"' && byte != b'\\' && byte >= 0x20)
            {
                self.pos += 1;
            }
            text.push_str(std::str::from_utf8(self.bytes.get(start..self.pos)?).ok()?);
            match self.peek()? {
                b'"' => {
                    self.pos += 1;
                    return Some(text);
                }
                b'\\' => {
                    self.pos += 1;
                    text.push(self.escape()?);
                }
                // An unescaped control character is not JSON.
                _ => return None,
            }
        }
    }

    fn escape(&mut self) -> Option<char> {
        let byte = self.peek()?;
        self.pos += 1;
        Some(match byte {
            b'"' => '"',
            b'\\' => '\\',
            b'/' => '/',
            b'b' => '\u{8}',
            b'f' => '\u{c}',
            b'n' => '\n',
            b'r' => '\r',
            b't' => '\t',
            b'u' => return self.unicode_escape(),
            _ => return None,
        })
    }

    /// The four hex digits after `\u`, joined with a following low surrogate
    /// when they are a high one. A lone surrogate is refused.
    fn unicode_escape(&mut self) -> Option<char> {
        let high = self.hex4()?;
        if !(0xD800..0xDC00).contains(&high) {
            return char::from_u32(high);
        }
        if !(self.eat(b'\\') && self.eat(b'u')) {
            return None;
        }
        let low = self.hex4()?;
        if !(0xDC00..0xE000).contains(&low) {
            return None;
        }
        char::from_u32(0x10000 + ((high - 0xD800) << 10) + (low - 0xDC00))
    }

    fn hex4(&mut self) -> Option<u32> {
        let digits = self.bytes.get(self.pos..self.pos + 4)?;
        if !digits.iter().all(u8::is_ascii_hexdigit) {
            return None;
        }
        self.pos += 4;
        u32::from_str_radix(std::str::from_utf8(digits).ok()?, 16).ok()
    }

    fn number(&mut self) -> Option<Value> {
        let start = self.pos;
        while self.peek().is_some_and(|byte| {
            byte.is_ascii_digit() || matches!(byte, b'-' | b'+' | b'.' | b'e' | b'E')
        }) {
            self.pos += 1;
        }
        (self.pos > start).then_some(Value::Scalar)
    }

    fn literal(&mut self, word: &str) -> Option<Value> {
        let end = self.pos + word.len();
        (self.bytes.get(self.pos..end)? == word.as_bytes()).then(|| {
            self.pos = end;
            Value::Scalar
        })
    }

    fn skip_whitespace(&mut self) {
        while self
            .peek()
            .is_some_and(|byte| matches!(byte, b' ' | b'\t' | b'\n' | b'\r'))
        {
            self.pos += 1;
        }
    }

    fn peek(&self) -> Option<u8> {
        self.bytes.get(self.pos).copied()
    }

    fn eat(&mut self, byte: u8) -> bool {
        let matched = self.peek() == Some(byte);
        if matched {
            self.pos += 1;
        }
        matched
    }
}
