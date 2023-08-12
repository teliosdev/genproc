use super::location::Span;
use std::rc::Rc;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum TokenKind {
    Error,
    Eof,
    DirectivePrefix,
    Identifier,
    Float,
    Number,
    String,
    Whitespace,
    Newline,
    Raw,
    LeftParen,
    RightParen,
    LeftBracket,
    RightBracket,
    LeftBrace,
    RightBrace,
    Comma,
    Dot,
    Colon,
    Semicolon,
    Assign,
    Equals,
    NotEquals,
    Plus,
    Minus,
    Asterisk,
    Slash,
    Percent,
    Caret,
    Ampersand,
    And,
    Pipe,
    Or,
    Exclamation,
    Tilde,
    Question,
    LessThan,
    GreaterThan,
    LessThanEqual,
    GreaterThanEqual,
}

impl TokenKind {
    pub(crate) fn is_whitespace(self) -> bool {
        matches!(self, TokenKind::Whitespace)
    }

    pub(crate) fn is_sync(self) -> bool {
        matches!(self, TokenKind::Raw | TokenKind::Eof | TokenKind::Error)
    }

    pub(crate) fn is_inline_content(self) -> bool {
        matches!(
            self,
            TokenKind::Whitespace | TokenKind::Newline | TokenKind::DirectivePrefix
        )
    }

    pub fn as_str(self) -> &'static str {
        match self {
            TokenKind::Error => "???",
            TokenKind::Eof => "<EOF>",
            TokenKind::DirectivePrefix => "<DIRECTIVE PREFIX>",
            TokenKind::Identifier => "<IDENT>",
            TokenKind::Number => "<NUMBER>",
            TokenKind::Float => "<FLOAT>",
            TokenKind::String => "<STRING>",
            TokenKind::Whitespace => "<WHITESPACE>",
            TokenKind::Newline => "<NEWLINE>",
            TokenKind::Raw => "<RAW>",
            TokenKind::LeftParen => "(",
            TokenKind::RightParen => ")",
            TokenKind::LeftBracket => "[",
            TokenKind::RightBracket => "]",
            TokenKind::LeftBrace => "{",
            TokenKind::RightBrace => "}",
            TokenKind::Comma => ",",
            TokenKind::Dot => ".",
            TokenKind::Colon => ":",
            TokenKind::Semicolon => ";",
            TokenKind::Assign => "=",
            TokenKind::Equals => "==",
            TokenKind::NotEquals => "!=",
            TokenKind::Plus => "+",
            TokenKind::Minus => "-",
            TokenKind::Asterisk => "*",
            TokenKind::Slash => "/",
            TokenKind::Percent => "%",
            TokenKind::Caret => "^",
            TokenKind::Ampersand => "&",
            TokenKind::And => "&&",
            TokenKind::Pipe => "|",
            TokenKind::Or => "||",
            TokenKind::Exclamation => "!",
            TokenKind::Tilde => "~",
            TokenKind::Question => "?",
            TokenKind::LessThan => "<",
            TokenKind::GreaterThan => ">",
            TokenKind::LessThanEqual => "<=",
            TokenKind::GreaterThanEqual => ">=",
        }
    }
}

impl std::fmt::Display for TokenKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Token<'i> {
    pub kind: TokenKind,
    pub span: Span<'i>,
}

impl<'i> Token<'i> {
    pub fn new(kind: TokenKind, span: Span<'i>) -> Self {
        Self { kind, span }
    }

    pub fn as_str(&self) -> &'i str {
        self.span.as_str()
    }
}

impl std::fmt::Display for Token<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.span.as_str())
    }
}

#[derive(Debug, Clone)]
pub struct Tokenizer<'i> {
    pub input: &'i str,
    position: u32,
    directive: Rc<str>,
    in_directive: u8,
    after_newline: bool,
}

#[derive(Copy, Clone)]
pub struct TokenMark {
    pub position: u32,
}

impl<'i> Tokenizer<'i> {
    pub fn new(input: &'i str, directive: Rc<str>) -> Self {
        Self {
            input,
            position: 0,
            directive,
            in_directive: 0,
            after_newline: true,
        }
    }

    pub fn at_eof(&self) -> Span<'i> {
        Span::new(
            self.input,
            u32::try_from(self.input.len()).expect("a file should not be too long"),
            0,
        )
    }

    pub fn is_eof(&self) -> bool {
        self.position as usize >= self.input.len()
    }

    pub fn mark(&self) -> TokenMark {
        TokenMark {
            position: self.position,
        }
    }

    pub fn since(&self, mark: TokenMark) -> Span<'i> {
        Span::new(
            self.input,
            mark.position,
            self.position.saturating_sub(mark.position),
        )
    }

    pub fn reset_mode(&mut self) {
        self.in_directive = 0;
        self.after_newline = false;
    }

    pub fn super_mode(&mut self, sup: bool) {
        debug_assert!(self.in_directive > 0);
        self.in_directive = if sup { 2 } else { 1 };
    }
}

impl<'i> Iterator for Tokenizer<'i> {
    type Item = Token<'i>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.is_eof() {
            return None;
        }

        let mut cookie = Cookie::new(self.input, self.position);

        let mut kind = if cookie.strip_prefix(&self.directive) {
            TokenKind::DirectivePrefix
        } else if self.in_directive > 0 {
            parse_token(&mut cookie)
        } else if let Some(len) = cookie.find_pattern(&self.directive) {
            cookie.advance(u32::try_from(len).expect("a file should not be this long"));
            TokenKind::Raw
        } else {
            cookie.all();
            TokenKind::Raw
        };

        self.position += cookie.length;

        if kind == TokenKind::Newline {
            if self.in_directive < 2 {
                self.in_directive = 0;
            }
            self.after_newline = true;
        } else if kind == TokenKind::DirectivePrefix {
            if self.after_newline && self.in_directive == 0 {
                self.in_directive = 1;
            } else if self.in_directive == 0 {
                kind = TokenKind::Raw;
            }
        } else if kind == TokenKind::Raw {
            self.after_newline = cookie.as_str().ends_with('\n');
        } else {
            self.after_newline = false;
        }

        Some(Token::new(kind, cookie.span()))
    }
}

#[derive(Copy, Clone)]
struct Cookie<'i> {
    input: &'i str,
    start: u32,
    length: u32,
}

impl std::fmt::Debug for Cookie<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() {
            f.debug_struct("Cookie")
                .field("input", &self.input)
                .field("start", &self.start)
                .field("length", &self.length)
                .finish()
        } else {
            f.debug_tuple("Cookie").field(&self.as_str()).finish()
        }
    }
}

impl<'i> Cookie<'i> {
    fn new(input: &'i str, start: u32) -> Self {
        Self {
            input,
            start,
            length: 0,
        }
    }

    fn as_str(&self) -> &'i str {
        &self.input[((self.start + self.length) as usize)..]
    }

    fn starts_with(&self, s: &str) -> bool {
        if self.input.len() < self.start as usize + s.len() {
            return false;
        }

        self.as_str().starts_with(s)
    }

    fn strip_prefix(&mut self, s: &str) -> bool {
        if self.starts_with(s) {
            self.advance(u32::try_from(s.len()).expect("a string should not be this long..."));
            true
        } else {
            false
        }
    }

    fn find_pattern(&mut self, pattern: &str) -> Option<usize> {
        self.as_str().find(pattern)
    }

    fn peek(&self) -> Option<char> {
        self.as_str().chars().next()
    }

    fn next(&mut self) -> Option<char> {
        let next = self.peek()?;
        self.advance(
            u32::try_from(next.len_utf8())
                .expect("a utf-8 character cannot be more than 4 bytes long"),
        );
        Some(next)
    }

    fn advance(&mut self, by: u32) -> &'i str {
        debug_assert!((self.start + self.length + by) as usize <= self.input.len());
        let old_length = self.length;
        self.length += by;
        &self.input[((self.start + old_length) as usize)..((self.start + self.length) as usize)]
    }

    fn all(&mut self) {
        self.length = u32::try_from(self.input.len()).expect("the input should not be this long")
            - self.start;
    }

    fn span(&self) -> Span<'i> {
        Span::new(self.input, self.start, self.length)
    }

    fn chomp<F>(&mut self, mut f: F) -> Option<usize>
    where
        F: FnMut(char) -> bool,
    {
        let mut count = 0;
        while let Some(ch) = self.peek() {
            if !f(ch) {
                break;
            }
            self.next();
            count += 1;
        }
        if count > 0 {
            Some(count)
        } else {
            None
        }
    }
}

static TOKEN_MAP: phf::Map<&str, TokenKind> = phf::phf_map! {
    "(" => TokenKind::LeftParen,
    ")" => TokenKind::RightParen,
    "[" => TokenKind::LeftBracket,
    "]" => TokenKind::RightBracket,
    "{" => TokenKind::LeftBrace,
    "}" => TokenKind::RightBrace,
    "," => TokenKind::Comma,
    "." => TokenKind::Dot,
    ":" => TokenKind::Colon,
    ";" => TokenKind::Semicolon,
    "=" => TokenKind::Assign,
    "==" => TokenKind::Equals,
    "!=" => TokenKind::NotEquals,
    "+" => TokenKind::Plus,
    "-" => TokenKind::Minus,
    "*" => TokenKind::Asterisk,
    "/" => TokenKind::Slash,
    "%" => TokenKind::Percent,
    "^" => TokenKind::Caret,
    "&" => TokenKind::Ampersand,
    "&&" => TokenKind::And,
    "|" => TokenKind::Pipe,
    "||" => TokenKind::Or,
    "!" => TokenKind::Exclamation,
    "~" => TokenKind::Tilde,
    "?" => TokenKind::Question,
    "<" => TokenKind::LessThan,
    "<=" => TokenKind::LessThanEqual,
    ">" => TokenKind::GreaterThan,
    ">=" => TokenKind::GreaterThanEqual,
    "\n" => TokenKind::Newline,
    "\r\n" => TokenKind::Newline,
};

static SEARCH: once_cell::sync::Lazy<aho_corasick::AhoCorasick> =
    once_cell::sync::Lazy::new(|| {
        aho_corasick::AhoCorasick::builder()
            .match_kind(aho_corasick::MatchKind::LeftmostLongest)
            .start_kind(aho_corasick::StartKind::Anchored)
            .build(TOKEN_MAP.keys().copied().collect::<Vec<_>>())
            .expect("this should not fail")
    });

pub fn is_bad_prefix(prefix: &str) -> bool {
    TOKEN_MAP.contains_key(prefix)
}

fn parse_token(cookie: &mut Cookie<'_>) -> TokenKind {
    if let Some(matches) = SEARCH.find(aho_corasick::Input::anchored(
        cookie.as_str().into(),
        aho_corasick::Anchored::Yes,
    )) {
        debug_assert_eq!(matches.start(), 0);
        let r#match =
            cookie.advance(u32::try_from(matches.len()).expect("this is literally impossible"));
        let kind = TOKEN_MAP.get(r#match).expect("this should not fail");
        return *kind;
    }

    match cookie.peek().expect("a cookie should not yet be empty") {
        '"' => parse_string(cookie),
        '0'..='9' => parse_number(cookie),
        c if c.is_whitespace() => {
            cookie.chomp(|c| c.is_whitespace() && c != '\n');
            TokenKind::Whitespace
        }
        c if unicode_xid::UnicodeXID::is_xid_start(c) => {
            cookie.chomp(unicode_xid::UnicodeXID::is_xid_continue);
            TokenKind::Identifier
        }
        _ => {
            cookie.next();
            TokenKind::Error
        }
    }
}

fn parse_string(cookie: &mut Cookie<'_>) -> TokenKind {
    let mut escape = false;
    cookie.next();

    cookie.chomp(|c| match c {
        '"' if !escape => false,
        '\\' if !escape => {
            escape = true;
            true
        }
        _ => {
            escape = false;
            true
        }
    });

    cookie
        .next()
        .filter(|c| *c == '"')
        .map_or_else(|| TokenKind::Error, |_| TokenKind::String)
}

fn parse_number(cookie: &mut Cookie<'_>) -> TokenKind {
    if let Some(result) = parse_numbered_prefix(cookie, "0x", 16) {
        return result;
    }
    if let Some(result) = parse_numbered_prefix(cookie, "0b", 2) {
        return result;
    }

    let index = cookie
        .chomp(|c| c.is_ascii_digit() || c == '_')
        .unwrap_or(0);

    debug_assert!(
        index > 0,
        "we matched on a 0..=9 to get here, so base must be at least 1"
    );

    let mut is_float = false;

    if let Some('.') = cookie.peek() {
        is_float = true;
        cookie.next();
        if cookie.chomp(|c| c.is_ascii_digit() || c == '_').is_none() {
            return TokenKind::Error;
        }
    }
    if let Some('e' | 'E') = cookie.peek() {
        is_float = true;
        cookie.next();
        if let Some('+' | '-') = cookie.peek() {
            cookie.next();
        }
        if cookie.chomp(|c| c.is_ascii_digit() || c == '_').is_none() {
            return TokenKind::Error;
        }
    }

    if is_float {
        TokenKind::Float
    } else {
        TokenKind::Number
    }
}

fn parse_numbered_prefix(cookie: &mut Cookie<'_>, prefix: &str, base: u32) -> Option<TokenKind> {
    if cookie.strip_prefix(prefix) {
        Some(
            cookie
                .chomp(|c| c.is_digit(base) || c == '_')
                .map_or_else(|| TokenKind::Error, |_| TokenKind::Number),
        )
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_number() {
        const N: TokenKind = TokenKind::Number;

        fn pn(input: &str) -> TokenKind {
            let mut cookie = Cookie::new(input, 0);
            parse_number(&mut cookie)
        }

        assert_eq!(pn("0"), N);
        assert_eq!(pn("1"), N);
        assert_eq!(pn("2"), N);
        assert_eq!(pn("123456789"), N);
        assert_eq!(pn("0x0"), N);
        assert_eq!(pn("0x1"), N);
        assert_eq!(pn("0x2"), N);
        assert_eq!(pn("0x123456789abcdef"), N);
        assert_eq!(pn("0b0"), N);
        assert_eq!(pn("0b1"), N);
        assert_eq!(pn("0b10"), N);
        assert_eq!(pn("0b11"), N);
        assert_eq!(
            pn("0b1010101010101010101010101010101010101010101010101010101010101010"),
            N
        );
        assert_eq!(pn("0x"), TokenKind::Error);
        assert_eq!(pn("0b"), TokenKind::Error);
        assert_eq!(pn("0xg"), TokenKind::Error);
        assert_eq!(pn("0bg"), TokenKind::Error);

        assert_eq!(pn("0."), TokenKind::Error);
        assert_eq!(pn("0. "), TokenKind::Error);
        assert_eq!(pn("0.1"), N);
        assert_eq!(pn("0.123456789"), N);
        assert_eq!(pn("0.123e456"), N);
        assert_eq!(pn("0.123e+456"), N);
        assert_eq!(pn("0.123e-456"), N);
        assert_eq!(pn("123E456"), N);
        assert_eq!(pn("123E+456"), N);
        assert_eq!(pn("123E-456"), N);
        assert_eq!(pn("123e"), TokenKind::Error);
        assert_eq!(pn("123e "), TokenKind::Error);
        assert_eq!(pn("123e+"), TokenKind::Error);
        assert_eq!(pn("123e+ "), TokenKind::Error);
    }

    #[test]
    fn test_parse_string() {
        const S: TokenKind = TokenKind::String;

        fn ps(input: &str) -> TokenKind {
            let mut cookie = Cookie::new(input, 0);
            parse_string(&mut cookie)
        }

        assert_eq!(ps("\"\""), S);
        assert_eq!(ps("\"a\""), S);
        assert_eq!(ps("\"abc\""), S);
        assert_eq!(ps(r##""\"""##), S);
        assert_eq!(ps("\"\\n\""), S);
        assert_eq!(ps("\"\\r\""), S);
        assert_eq!(ps("\"\\t\""), S);
        assert_eq!(ps("\"hello, world\""), S);

        assert_eq!(ps("\""), TokenKind::Error);
        assert_eq!(ps("\"hello world"), TokenKind::Error);
    }

    #[test]
    fn test_tokenizer() {
        fn tokenize(input: &str) -> Vec<TokenKind> {
            let tokenizer = Tokenizer::new(input, Rc::from("--!"));
            tokenizer.map(|token| token.kind).collect()
        }

        use TokenKind::*;

        assert_eq!(tokenize("--!"), vec![DirectivePrefix]);
        assert_eq!(tokenize("--! "), vec![DirectivePrefix, Whitespace]);
        assert_eq!(tokenize("--!  "), vec![DirectivePrefix, Whitespace]);
        assert_eq!(tokenize("--!1234"), vec![DirectivePrefix, Number]);
        assert_eq!(
            tokenize("--!\"hello, world\""),
            vec![DirectivePrefix, String]
        );
        assert_eq!(tokenize("--!hello"), vec![DirectivePrefix, Identifier]);
        assert_eq!(
            tokenize("--!hello world"),
            vec![DirectivePrefix, Identifier, Whitespace, Identifier]
        );

        assert_eq!(
            tokenize("--!if (a == 2 || startswith(b, \"hello\"))\n"),
            vec![
                DirectivePrefix,
                Identifier,
                Whitespace,
                LeftParen,
                Identifier,
                Whitespace,
                Equals,
                Whitespace,
                Number,
                Whitespace,
                Or,
                Whitespace,
                Identifier,
                LeftParen,
                Identifier,
                Comma,
                Whitespace,
                String,
                RightParen,
                RightParen,
                Newline
            ]
        );

        assert_eq!(
            tokenize("hello world\n--!define A 2\nfoo bar"),
            vec![
                Raw,
                DirectivePrefix,
                Identifier,
                Whitespace,
                Identifier,
                Whitespace,
                Number,
                Newline,
                Raw
            ]
        );
    }
}
