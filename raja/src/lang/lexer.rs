use tendril::StrTendril;
use lang::{TextLocation,Token,TokenKind};
use std::collections::VecDeque;

pub struct Lexer {
    buf: StrTendril,
    loc: TextLocation,
    cur: Option<char>,
    lookahead: VecDeque<Option<char>>,
    val: StrTendril,
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
            val: StrTendril::new(),
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
        self.emit(TokenKind::Newline)
    }

    fn whitespace(&mut self) -> Option<Token> {
        self.take_while(is_ws);
        self.emit(TokenKind::Whitespace)
    }

    fn unknown(&mut self) -> Option<Token> {
        self.take();
        self.emit(TokenKind::Unknown)
    }

    fn single_line_comment(&mut self) -> Option<Token> {
        self.take_assert('/');
        self.take_assert('/');
        self.take_while(|c| !is_nl(c));
        self.emit(TokenKind::Comment)
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

        self.emit(kind)
    }

    // Helpers

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
            self.val.try_push_char(c).unwrap();
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

    fn emit(&mut self, kind: TokenKind) -> Option<Token> {
        if self.val.len32() > 0 {
            Some(Token::new(kind, self.start, self.loc, self.val.clone()))
        } else {
            None
        }
    }

    fn la(&self, ch: char) -> bool {
        self.lookahead.len() > 0 && self.lookahead[0] == Some(ch)
    }

    fn at(&self, ch: char) -> bool {
        self.cur == Some(ch)
    }
}

impl Iterator for Lexer {
    type Item = Token;

    fn next(&mut self) -> Option<Token> {
        self.start = self.loc;
        self.val.clear();

        match self.cur {
            None => None,
            Some('/') if self.la('/') => self.single_line_comment(),
            Some('/') if self.la('*') => self.span_comment(),
            Some(c) if is_nl(c) => self.newline(),
            Some(x) if is_ws(x) => self.whitespace(),
            Some(x) => self.unknown()
        }
    }
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

#[cfg(test)]
mod test {
    use tendril::StrTendril;
    use lang::{Lexer,Token,TokenKind};
    use std::str::FromStr;

    macro_rules! token_test {
        ($inp:expr, $($typ:ident($text:expr)),*) => ({
            let mut matchers = Vec::new();
            $(
                matchers.push((TokenKind::$typ, StrTendril::from_str($text).unwrap()));
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
                    Unknown("a"));

        // Span comment
        token_test!("/* this is a span comment but it isn't multi-line */a",
                    Comment("/* this is a span comment but it isn't multi-line */"),
                    Unknown("a"));

        // Multi-line (different because it is considered a line terminator)
        token_test!("/* This is a multi\nline\ncomment */a",
                    MultiLineComment("/* This is a multi\nline\ncomment */"),
                    Unknown("a"));

        // Nesting has no effect
        token_test!("/* this is a /* nested span comment but it isn't multi-line */a",
                    Comment("/* this is a /* nested span comment but it isn't multi-line */"),
                    Unknown("a"));
        token_test!("/* This is a /* nested multi\nline\ncomment */a",
                    MultiLineComment("/* This is a /* nested multi\nline\ncomment */"),
                    Unknown("a"));
    }

    fn tokenize(input: &str) -> Vec<Token> {
        let tendril = StrTendril::from_str(input).unwrap();
        let lex = Lexer::new(tendril);
        lex.collect()
    }

    fn evaluate(actual: Vec<Token>, matchers: Vec<(TokenKind, StrTendril)>) {
        let mut actual_iter = actual.iter();
        let mut matchers_iter = matchers.iter();

        let mut output = "Results: \nExpected <=> Actual\n".to_string();
        let mut success = true;
        while let Some(token) = actual_iter.next() {
            match matchers_iter.next() {
                None => {
                    success = false;
                    output.push_str(&format!("{: <30} != {: <30}\n", "<end of stream>", format!("{}(\"{}\")", token.kind(), escape_str(token.value()))));
                },
                Some(&(kind, ref val)) => {
                    if token.kind() != kind || token.value() != val {
                        success = false;
                        output.push_str(&format!("{: <30} != {: <30}\n",
                                                format!("{}(\"{}\")", kind, escape_str(val)),
                                                format!("{}(\"{}\")", token.kind(), escape_str(token.value()))));
                    } else {
                        output.push_str(&format!("{: <30} == {: <30}\n",
                                                format!("{}(\"{}\")", kind, escape_str(val)),
                                                format!("{}(\"{}\")", token.kind(), escape_str(token.value()))));
                    }
                }
            }
        }

        while let Some(&(kind, ref val)) = matchers_iter.next() {
            success = false;
            output.push_str(&format!("{: <30} != {: <30}\n", format!("{}(\"{}\")", kind, escape_str(val)), "<end of stream>"));
        }

        if !success {
            panic!(output);
        }
    }

    fn escape_str(s: &str) -> String {
        s.chars().flat_map(|c| c.escape_default()).collect()
    }
}
