use tendril::StrTendril;
use lang::{TextLocation,Token,TokenKind};

pub struct Lexer {
    buf: StrTendril,
    loc: TextLocation,
    cur: Option<char>,
    text: StrTendril,
    val: StrTendril,
    start: TextLocation
}

impl Lexer {
    pub fn new(mut buf: StrTendril) -> Lexer {
        let ch = buf.pop_front_char();
        Lexer {
            buf: buf,
            loc: TextLocation::new(0, 0, 0),
            cur: ch,
            text: StrTendril::new(),
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
        self.cur = self.buf.pop_front_char();
    }

    fn emit(&mut self, kind: TokenKind) -> Option<Token> {
        if self.text.len32() > 0 {
            if self.val.len32() == 0 {
                self.val = self.text.clone();
            }
            Some(Token::new(kind, self.start, self.loc, self.val.clone(), self.text.clone()))
        } else {
            None
        }
    }
}

impl Iterator for Lexer {
    type Item = Token;

    fn next(&mut self) -> Option<Token> {
        self.start = self.loc;
        self.text.clear();
        self.val.clear();

        match self.cur {
            None => None,
            Some('\n') |
                Some('\r') |
                Some('\u{2028}') |
                Some('\u{2029}') => self.newline(),
            Some(x) if is_ws(x) => self.whitespace(),

            Some(x) => self.unknown()
        }
    }
}

fn is_ws(ch: char) -> bool {
    ch == '\u{FEFF}' || ch.is_whitespace()
}

#[cfg(test)]
mod test {
    use tendril::StrTendril;
    use lang::{Lexer,Token,TokenKind};
    use std::str::FromStr;

    macro_rules! token_test {
        ($inp:expr, $($typ:ident($text:expr)),*) => ({
            let input = StrTendril::from_str($inp).unwrap();
            let lex = Lexer::new(input);
            let mut matchers = Vec::new();
            $(
                matchers.push((TokenKind::$typ, StrTendril::from_str($text).unwrap()));
            )*
            evaluate(lex, matchers);
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

        // Solo '\r' is a newline if not followed by '\n'
        token_test!("\r ", Newline("\r"), Whitespace(" "));
        token_test!("\r\r", Newline("\r"), Newline("\r"));
        token_test!("\r\u{2029}", Newline("\r"), Newline("\u{2029}"));
    }

    fn evaluate(lex: Lexer, matchers: Vec<(TokenKind, StrTendril)>) {
        let actual : Vec<_> = lex.collect();
        let mut actual_iter = actual.iter();
        let mut matchers_iter = matchers.iter();

        let mut output = "Results: \nExpected <=> Actual\n".to_string();
        let mut success = true;
        while let Some(token) = actual_iter.next() {
            match matchers_iter.next() {
                None => {
                    success = false;
                    output.push_str(&format!("{: <30} != {: <30}\n", "<end of stream>", format!("{}(\"{}\")", token.kind(), escape_str(token.text()))));
                },
                Some(&(kind, ref text)) => {
                    if token.kind() != kind || token.text() != text {
                        success = false;
                        output.push_str(&format!("{: <30} != {: <30}\n",
                                                format!("{}(\"{}\")", kind, escape_str(text)),
                                                format!("{}(\"{}\")", token.kind(), escape_str(token.text()))));
                    } else {
                        output.push_str(&format!("{: <30} == {: <30}\n",
                                                format!("{}(\"{}\")", kind, escape_str(text)),
                                                format!("{}(\"{}\")", token.kind(), escape_str(token.text()))));
                    }
                }
            }
        }

        while let Some(&(kind, ref text)) = matchers_iter.next() {
            success = false;
            output.push_str(&format!("{: <30} != {: <30}\n", format!("{}(\"{}\")", kind, escape_str(text)), "<end of stream>"));
        }

        if !success {
            panic!(output);
        }
    }

    fn escape_str(s: &str) -> String {
        s.chars().flat_map(|c| c.escape_default()).collect()
    }
}
