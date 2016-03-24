use std::fmt;

pub use tendril::StrTendril;
pub use lang::TextLocation;

#[derive(Debug,Clone,PartialEq)]
pub struct Token {
    kind: TokenKind,
    start: TextLocation,
    end: TextLocation,
    text: StrTendril,
    value: TokenValue
}

#[derive(Copy,Clone,Eq,PartialEq,Debug)]
pub enum TokenKind {
    Unknown,
    Whitespace,
    Newline,
    Comment,
    MultiLineComment,
    IdentifierName,
    Punctuator,
    Literal
}

impl fmt::Display for TokenKind {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(fmt, "{:?}", self)
    }
}

#[derive(Clone,PartialEq,Debug)]
pub enum TokenValue {
    None,
    Integer(u64),
    Float(f64),
    String(String)
}

impl fmt::Display for TokenValue {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(fmt, "{:?}", self)
    }
}

impl Token {
    pub fn new(kind: TokenKind, start: TextLocation, end: TextLocation, text: StrTendril, value: TokenValue) -> Token {
        Token {
            kind: kind,
            start: start,
            end: end,
            text: text,
            value: value
        }
    }

    #[inline]
    pub fn kind(&self) -> TokenKind {
        self.kind
    }

    #[inline]
    pub fn text(&self) -> &StrTendril {
        &self.text
    }

    #[inline]
    pub fn value(&self) -> &TokenValue {
        &self.value
    }
}
