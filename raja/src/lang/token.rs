use std::fmt;

pub use tendril::StrTendril;
pub use lang::TextLocation;

#[derive(Clone,Eq,PartialEq)]
pub struct Token {
    kind: TokenKind,
    start: TextLocation,
    end: TextLocation,
    text: StrTendril,
    value: StrTendril
}

#[derive(Copy,Clone,Eq,PartialEq,Debug)]
pub enum TokenKind {
    Unknown,
    Whitespace,
    Newline,
}

impl fmt::Display for TokenKind {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(fmt, "{:?}", self)
    }
}

impl Token {
    pub fn new(kind: TokenKind, start: TextLocation, end: TextLocation, text: StrTendril, value: StrTendril) -> Token {
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
    pub fn start(&self) -> TextLocation {
        self.start
    }

    #[inline]
    pub fn end(&self) -> TextLocation {
        self.end
    }

    #[inline]
    pub fn text(&self) -> &StrTendril {
        &self.text
    }

    #[inline]
    pub fn value(&self) -> &StrTendril {
        &self.value
    }
}