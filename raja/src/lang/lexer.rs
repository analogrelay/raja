extern crate unicode_xid;

use tendril::StrTendril;
use lang::{TextLocation,Token,TokenKind,TokenValue};
use std::collections::VecDeque;
use std::str::FromStr;

use self::unicode_xid::UnicodeXID;

pub struct Lexer {
    buf: StrTendril,
    loc: TextLocation,
    cur: Option<char>,
    lookahead: VecDeque<Option<char>>,
    text: StrTendril,
    start: TextLocation
}

impl Lexer {
    pub fn new(mut buf: StrTendril) -> Lexer {
        let ch = buf.pop_front_char();
        let mut la = VecDeque::new();
        la.push_front(buf.pop_front_char());
        Lexer {
            buf: buf,
            loc: TextLocation::new(0, 0, 0),
            cur: ch,
            lookahead: la,
            text: StrTendril::new(),
            start: TextLocation::new(0, 0, 0)
        }
    }

    // Token generators
    fn newline(&mut self) -> Option<Token> {
        let first = self.cur.unwrap();
        self.take();
        if first == '\r' && self.cur == Some('\n') {
            self.take();
        }
        self.emit(TokenKind::Newline, TokenValue::None)
    }

    fn whitespace(&mut self) -> Option<Token> {
        self.take_while(is_ws);
        self.emit(TokenKind::Whitespace, TokenValue::None)
    }

    fn unknown(&mut self) -> Option<Token> {
        self.take();
        self.emit(TokenKind::Unknown, TokenValue::None)
    }

    fn single_line_comment(&mut self) -> Option<Token> {
        self.take_assert('/');
        self.take_assert('/');
        self.take_while(|c| !is_nl(c));
        self.emit(TokenKind::Comment, TokenValue::None)
    }

    fn span_comment(&mut self) -> Option<Token> {
        self.take_assert('/');
        self.take_assert('*');

        let mut kind = TokenKind::Comment;
        loop {
            self.take_while(|c| c != '*' && !is_nl(c));
            match self.cur {
                None => break, // EOF
                Some(c) if is_nl(c) => {
                    self.take();
                    kind = TokenKind::MultiLineComment;
                },
                Some('*') => {
                    self.take();
                    if self.at('/') {
                        // End of comment
                        self.take();
                        break
                    }
                },
                _ => panic!("should not hit this case")
            }
        }

        self.emit(kind, TokenValue::None)
    }

    fn identifier(&mut self) -> Option<Token> {
        self.take();
        self.take_while(is_id_continue);
        self.emit(TokenKind::IdentifierName, TokenValue::None)
    }

    fn comparison_or_shift(&mut self) -> Option<Token> {
        let original = self.cur.unwrap();
        self.take();
        match self.cur {
            Some('=') => self.take(),
            Some(original) => {
                self.take();
                if original == '>' && self.at('>') {
                    self.take();
                }
                self.take_if('=');
            }
            _ => {}
        }
        self.emit(TokenKind::Punctuator, TokenValue::None)
    }

    fn equality(&mut self) -> Option<Token> {
        self.take();
        self.take_if('=');
        self.take_if('=');
        self.emit(TokenKind::Punctuator, TokenValue::None)
    }

    fn arith_and_logic(&mut self) -> Option<Token> {
        self.take();
        self.take_if('=');
        self.emit(TokenKind::Punctuator, TokenValue::None)
    }

    fn dec_literal(&mut self) -> Option<Token> {
        let mut float = false;
        self.take_while(is_digit);

        if self.at('.') {
            float = true;
            self.take();
            self.take_while(is_digit);
        }

        if self.at('e') || self.at('E') {
            float = true;
            self.take();
            if self.at('+') || self.at('-') {
                self.take();
            }
            self.take_while(is_digit);
        }

        let val = if float {
            TokenValue::Float(f64::from_str(&self.text).unwrap())
        } else {
            TokenValue::Integer(u64::from_str(&self.text).unwrap())
        };

        self.emit(TokenKind::NumericLiteral, val)
    }

    fn bin_literal(&mut self) -> Option<Token> {
        self.take_assert('0');
        assert!(self.cur.unwrap() == 'b' || self.cur.unwrap() == 'B');
        self.take();

        let mut val = 0u64;
        while self.at_match(|c| c == '0' || c == '1') {
            val = self.cur.unwrap().to_digit(2).unwrap() as u64 + (val * 2) as u64;
            self.take();
        }
        self.emit(TokenKind::NumericLiteral, TokenValue::Integer(val))
    }

    fn oct_literal(&mut self) -> Option<Token> {
        self.take_assert('0');
        assert!(self.cur.unwrap() == 'o' || self.cur.unwrap() == 'O');
        self.take();

        let mut val = 0u64;
        while self.at_match(|c| c >= '0' && c <= '7') {
            val = self.cur.unwrap().to_digit(8).unwrap() as u64 + (val * 8) as u64;
            self.take();
        }
        self.emit(TokenKind::NumericLiteral, TokenValue::Integer(val))
    }

    fn hex_literal(&mut self) -> Option<Token> {
        self.take_assert('0');
        assert!(self.cur.unwrap() == 'x' || self.cur.unwrap() == 'X');
        self.take();

        let mut val = 0u64;
        while self.at_match(|c| (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')) {
            val = self.cur.unwrap().to_digit(16).unwrap() as u64 + (val * 16) as u64;
            self.take();
        }
        self.emit(TokenKind::NumericLiteral, TokenValue::Integer(val))
    }

    // Helpers
    fn take_if(&mut self, ch: char) {
        if self.at(ch) {
            self.take();
        }
    }

    fn take_while<F>(&mut self, predicate: F) where F: Fn(char) -> bool {
        while let Some(c) = self.cur {
            if predicate(c) {
                self.take();
            } else {
                return
            }
        }
    }

    fn take_assert(&mut self, ch: char) {
        assert_eq!(Some(ch), self.cur);
        self.take()
    }

    fn take(&mut self) {
        if let Some(c) = self.cur {
            self.text.try_push_char(c).unwrap();
        }
        self.skip();
    }

    fn skip(&mut self) {
        if let Some(c) = self.cur {
            self.loc = self.loc.advance(c);
        }

        match self.lookahead.pop_front() {
            Some(oc) => self.cur = oc,
            None => self.cur = self.buf.pop_front_char()
        };

        if self.lookahead.len() == 0 {
            self.lookahead.push_front(self.buf.pop_front_char());
        }
    }

    fn take_emit(&mut self, kind: TokenKind) -> Option<Token> {
        self.take();
        self.emit(kind, TokenValue::None)
    }

    fn emit(&mut self, kind: TokenKind, value: TokenValue) -> Option<Token> {
        if self.text.len32() > 0 {
            Some(Token::new(kind, self.start, self.loc, self.text.clone(), value))
        } else {
            None
        }
    }

    fn la(&self, ch: char) -> bool {
        self.lookahead.len() > 0 && self.lookahead[0] == Some(ch)
    }

    fn la_match<F>(&self, predicate: F) -> bool where F: Fn(char) -> bool {
        if self.lookahead.len() == 0 {
            false
        } else if let Some(c) = self.lookahead[0] {
            predicate(c)
        } else {
            false
        }
    }

    fn at(&self, ch: char) -> bool {
        self.cur == Some(ch)
    }

    fn at_match<F>(&self, predicate: F) -> bool where F: Fn(char) -> bool {
        if let Some(c) = self.cur {
            predicate(c)
        } else {
            false
        }
    }
}

impl Iterator for Lexer {
    type Item = Token;

    fn next(&mut self) -> Option<Token> {
        self.start = self.loc;
        self.text.clear();

        match self.cur {
            // Comments
            Some('/') if self.la('/') => self.single_line_comment(),
            Some('/') if self.la('*') => self.span_comment(),

            // Newlines/Whitespace
            Some(x) if is_nl(x) => self.newline(),
            Some(x) if is_ws(x) => self.whitespace(),

            // Identifiers
            Some(x) if is_id_start(x) => self.identifier(),

            // Numeric Literals
            Some('0') if self.la('x') => self.hex_literal(),
            Some('0') if self.la('X') => self.hex_literal(),
            Some('0') if self.la('b') => self.bin_literal(),
            Some('0') if self.la('B') => self.bin_literal(),
            Some('0') if self.la('o') => self.oct_literal(),
            Some('0') if self.la('O') => self.oct_literal(),
            Some('.') if self.la_match(is_digit) => self.dec_literal(),
            Some(x) if is_digit(x) => self.dec_literal(),

            // Punctuators (aka Operators, but the ECMA spec calls them Punctuators)
            Some('{') |
                Some('}') |
                Some('(') |
                Some(')') |
                Some('[') |
                Some(']') |
                Some(';') |
                Some(',') |
                Some('?') |
                Some(':') => self.take_emit(TokenKind::Punctuator),
            Some('.') => {
                self.take_assert('.');
                if self.at('.') && self.la('.') {
                    self.take_assert('.');
                    self.take_assert('.');
                }
                self.emit(TokenKind::Punctuator, TokenValue::None)
            },
            Some('<') | Some('>') => self.comparison_or_shift(),
            Some('=') if self.la('>') => { self.take(); self.take_emit(TokenKind::Punctuator) },
            Some('=') | Some('!') => self.equality(),
            Some('&') if self.la('&') => { self.take(); self.take_emit(TokenKind::Punctuator) },
            Some('|') if self.la('|') => { self.take(); self.take_emit(TokenKind::Punctuator) },
            Some('+') if self.la('+') => { self.take(); self.take_emit(TokenKind::Punctuator) },
            Some('-') if self.la('-') => { self.take(); self.take_emit(TokenKind::Punctuator) },
            Some('+') |
                Some('-') |
                Some('*') |
                Some('/') |
                Some('%') |
                Some('&') |
                Some('^') |
                Some('|') => self.arith_and_logic(),

            // Fallback cases
            Some(x) => self.unknown(),
            None => None,
        }
    }
}

fn is_id_continue(ch: char) -> bool {
    ch == '$' ||
        ch == '_' ||
        UnicodeXID::is_xid_continue(ch) ||
        ch == '\u{200C}' ||
        ch == '\u{200D}'
}

fn is_id_start(ch: char) -> bool {
    ch == '$' ||
        ch == '_' ||
        UnicodeXID::is_xid_start(ch)
}

fn is_ws(ch: char) -> bool {
    ch == '\u{FEFF}' || ch.is_whitespace()
}

fn is_nl(ch: char) -> bool {
    ch == '\n' ||
        ch == '\r' ||
        ch == '\u{2028}' ||
        ch == '\u{2029}'
}

fn is_digit(ch: char) -> bool {
    ch >= '0' && ch <= '9'
}

#[cfg(test)]
mod test {
    use tendril::StrTendril;
    use lang::{Lexer,Token,TokenKind,TokenValue};
    use std::str::FromStr;

    macro_rules! token_test {
        ($inp:expr, $($typ:ident($text:expr, $val:expr)),*) => ({
            let mut matchers = Vec::new();
            $(
                matchers.push((TokenKind::$typ, StrTendril::from_str($text).unwrap(), $val));
            )*
            evaluate(tokenize($inp), matchers);
        });
        ($inp:expr, $($typ:ident($text:expr)),*) => ({
            let mut matchers = Vec::new();
            $(
                matchers.push((TokenKind::$typ, StrTendril::from_str($text).unwrap(), TokenValue::None));
            )*
            evaluate(tokenize($inp), matchers);
        })
    }

    #[test]
    pub fn whitespace_tokens() {
        token_test!(" ", Whitespace(" "));
        token_test!("\t", Whitespace("\t"));
        token_test!("\u{000B}", Whitespace("\u{000B}"));
        token_test!("\u{000C}", Whitespace("\u{000C}"));
        token_test!("\u{00A0}", Whitespace("\u{00A0}"));
        token_test!("\u{FEFF}", Whitespace("\u{FEFF}"));
    }

    #[test]
    pub fn newline_tokens() {
        token_test!("\n", Newline("\n"));
        token_test!("\r", Newline("\r"));
        token_test!("\r\n", Newline("\r\n"));
        token_test!("\u{2028}", Newline("\u{2028}"));
        token_test!("\u{2029}", Newline("\u{2029}"));

        // Solo '\r' is it's own newline token if not followed by '\n'
        token_test!("\r ", Newline("\r"), Whitespace(" "));
        token_test!("\r\r", Newline("\r"), Newline("\r"));
        token_test!("\r\u{2029}", Newline("\r"), Newline("\u{2029}"));
    }

    #[test]
    pub fn comment_tokens() {
        // Single-line
        token_test!("// This is a single-line comment\na",
                    Comment("// This is a single-line comment"),
                    Newline("\n"),
                    IdentifierName("a"));
        token_test!("// This is a single-line comment that isn't terminated",
                    Comment("// This is a single-line comment that isn't terminated"));

        // Span comment
        token_test!("/* this is a span comment but it isn't multi-line */a",
                    Comment("/* this is a span comment but it isn't multi-line */"),
                    IdentifierName("a"));

        // Unterminated span comment
        token_test!("/* this is a span comment but it isn't multi-line or terminated",
                    Comment("/* this is a span comment but it isn't multi-line or terminated"));

        // Multi-line (different because it is considered a line terminator)
        token_test!("/* This is a multi\nline\ncomment */a",
                    MultiLineComment("/* This is a multi\nline\ncomment */"),
                    IdentifierName("a"));

        // Nesting has no effect
        token_test!("/* this is a /* nested span comment but it isn't multi-line */a",
                    Comment("/* this is a /* nested span comment but it isn't multi-line */"),
                    IdentifierName("a"));
        token_test!("/* This is a /* nested multi\nline\ncomment */a",
                    MultiLineComment("/* This is a /* nested multi\nline\ncomment */"),
                    IdentifierName("a"));
    }

    #[test]
    pub fn identifier_tokens() {
        token_test!("this_1s_a_val1d_identifier_123",
                    IdentifierName("this_1s_a_val1d_identifier_123"));
        token_test!("valid\u{200D}identifier",
                    IdentifierName("valid\u{200D}identifier"));
        token_test!("valid\u{200C}identifier",
                    IdentifierName("valid\u{200C}identifier"));
        token_test!("$alsovalid",
                    IdentifierName("$alsovalid"));
        token_test!("_alsovalid",
                    IdentifierName("_alsovalid"));
        token_test!("0id",
                    NumericLiteral("0", TokenValue::Integer(0)),
                    IdentifierName("id", TokenValue::None));
    }

    #[test]
    pub fn punctuator_tokens() {
        token_test!("{", Punctuator("{"));
        token_test!("}", Punctuator("}"));
        token_test!("(", Punctuator("("));
        token_test!(")", Punctuator(")"));
        token_test!("[", Punctuator("["));
        token_test!("]", Punctuator("]"));
        token_test!(".", Punctuator("."));
        token_test!("...", Punctuator("..."));
        token_test!(";", Punctuator(";"));
        token_test!(",", Punctuator(","));
        token_test!("<", Punctuator("<"));
        token_test!(">", Punctuator(">"));
        token_test!("<=", Punctuator("<="));
        token_test!(">=", Punctuator(">="));
        token_test!("==", Punctuator("=="));
        token_test!("!=", Punctuator("!="));
        token_test!("===", Punctuator("==="));
        token_test!("!==", Punctuator("!=="));
        token_test!("+", Punctuator("+"));
        token_test!("-", Punctuator("-"));
        token_test!("*", Punctuator("*"));
        token_test!("/", Punctuator("/"));
        token_test!("%", Punctuator("%"));
        token_test!("++", Punctuator("++"));
        token_test!("--", Punctuator("--"));
        token_test!("<<", Punctuator("<<"));
        token_test!(">>", Punctuator(">>"));
        token_test!(">>>", Punctuator(">>>"));
        token_test!("&", Punctuator("&"));
        token_test!("&&", Punctuator("&&"));
        token_test!("|", Punctuator("|"));
        token_test!("||", Punctuator("||"));
        token_test!("?", Punctuator("?"));
        token_test!(":", Punctuator(":"));
        token_test!("=", Punctuator("="));
        token_test!("+=", Punctuator("+="));
        token_test!("-=", Punctuator("-="));
        token_test!("*=", Punctuator("*="));
        token_test!("/=", Punctuator("/="));
        token_test!("%=", Punctuator("%="));
        token_test!("<<=", Punctuator("<<="));
        token_test!(">>=", Punctuator(">>="));
        token_test!(">>>=", Punctuator(">>>="));
        token_test!("&=", Punctuator("&="));
        token_test!("|=", Punctuator("|="));
        token_test!("^=", Punctuator("^="));
        token_test!("=>", Punctuator("=>"));
    }

    #[test]
    pub fn numeric_literal_tokens() {
        // Decimal
        token_test!("0", NumericLiteral("0", TokenValue::Integer(0)));
        token_test!("123", NumericLiteral("123", TokenValue::Integer(123)));
        token_test!(".12", NumericLiteral(".12", TokenValue::Float(0.12)));
        token_test!("123.45", NumericLiteral("123.45", TokenValue::Float(123.45)));
        token_test!("123e1", NumericLiteral("123e1", TokenValue::Float(1230f64)));
        token_test!("123e+1", NumericLiteral("123e+1", TokenValue::Float(1230f64)));
        token_test!("123e-1", NumericLiteral("123e-1", TokenValue::Float(12.3)));
        token_test!("123E1", NumericLiteral("123E1", TokenValue::Float(1230f64)));
        token_test!("123E+1", NumericLiteral("123E+1", TokenValue::Float(1230f64)));
        token_test!("123E-1", NumericLiteral("123E-1", TokenValue::Float(12.3)));
        token_test!("123.45e1", NumericLiteral("123.45e1", TokenValue::Float(1234.5)));
        token_test!("123.45e+1", NumericLiteral("123.45e+1", TokenValue::Float(1234.5)));
        token_test!("123.45e-1", NumericLiteral("123.45e-1", TokenValue::Float(12.345)));
        token_test!("123.45E1", NumericLiteral("123.45E1", TokenValue::Float(1234.5)));
        token_test!("123.45E+1", NumericLiteral("123.45E+1", TokenValue::Float(1234.5)));
        token_test!("123.45E-1", NumericLiteral("123.45E-1", TokenValue::Float(12.345)));

        // Hex
        token_test!("0xABCD", NumericLiteral("0xABCD", TokenValue::Integer(0xABCD)));
        token_test!("0XABCD", NumericLiteral("0XABCD", TokenValue::Integer(0xABCD)));

        // Octal
        token_test!("0o01234567", NumericLiteral("0o01234567", TokenValue::Integer(0o01234567)));
        token_test!("0O01234567", NumericLiteral("0O01234567", TokenValue::Integer(0o01234567)));
        token_test!("0o08",
                    NumericLiteral("0o0", TokenValue::Integer(0)),
                    NumericLiteral("8", TokenValue::Integer(8)));
        token_test!("0O08",
                    NumericLiteral("0O0", TokenValue::Integer(0)),
                    NumericLiteral("8", TokenValue::Integer(8)));

        // Binary
        token_test!("0b01", NumericLiteral("0b01", TokenValue::Integer(1)));
        token_test!("0B01", NumericLiteral("0B01", TokenValue::Integer(1)));
        token_test!("0b02",
                    NumericLiteral("0b0", TokenValue::Integer(0)),
                    NumericLiteral("2", TokenValue::Integer(2)));
        token_test!("0B02",
                    NumericLiteral("0B0", TokenValue::Integer(0)),
                    NumericLiteral("2", TokenValue::Integer(2)));
    }

    fn tokenize(input: &str) -> Vec<Token> {
        let tendril = StrTendril::from_str(input).unwrap();
        let lex = Lexer::new(tendril);
        lex.collect()
    }

    fn evaluate(actual: Vec<Token>, matchers: Vec<(TokenKind, StrTendril, TokenValue)>) {
        let mut actual_iter = actual.iter();
        let mut matchers_iter = matchers.iter();

        let mut output = "Results: \nExpected <=> Actual\n".to_string();
        let mut success = true;
        while let Some(token) = actual_iter.next() {
            match matchers_iter.next() {
                None => {
                    success = false;
                    output.push_str(&format!("{: <40} != {: <40}\n", "<end of stream>", format!("{}(\"{}\")[{}]", token.kind(), escape_str(token.text()), token.value())));
                },
                Some(&(kind, ref text, ref val)) => {
                    if token.kind() != kind || token.text() != text || token.value() != val {
                        success = false;
                        output.push_str(&format!("{: <40} != {: <40}\n",
                                                format!("{}(\"{}\")[{}]", kind, escape_str(text), val),
                                                format!("{}(\"{}\")[{}]", token.kind(), escape_str(token.text()), token.value())));
                    } else {
                        output.push_str(&format!("{: <40} == {: <40}\n",
                                                format!("{}(\"{}\")[{}]", kind, escape_str(text), val),
                                                format!("{}(\"{}\")[{}]", token.kind(), escape_str(token.text()), token.value())));
                    }
                }
            }
        }

        while let Some(&(kind, ref text, ref val)) = matchers_iter.next() {
            success = false;
            output.push_str(&format!("{: <40} != {: <40}\n", format!("{}(\"{}\")[{}]", kind, escape_str(text), val), "<end of stream>"));
        }

        if !success {
            panic!(output);
        }
    }

    fn escape_str(s: &str) -> String {
        s.chars().flat_map(|c| c.escape_default()).collect()
    }
}
