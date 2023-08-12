use super::error::{ParseError, ParseErrors};
use super::location::Span;
use super::tokens::{Token, TokenKind, TokenMark, Tokenizer};
use std::cell::Cell;
use std::collections::VecDeque;

#[derive(Debug)]
pub struct Root<'i> {
    pub children: Vec<Item<'i>>,
    pub span: Span<'i>,
}

impl<'i> Root<'i> {
    pub(super) fn parse(stream: &mut TokenStream<'i>) -> Result<Self, ParseErrors<'i>> {
        let mut children = Vec::new();
        let mut errors = ParseErrors::default();
        let mark = stream.mark();
        while stream.peek() != TokenKind::Eof {
            match Item::parse(stream) {
                Ok(item) => children.push(item),
                Err(err) => errors = errors.merge(err),
            }
        }

        let span = stream.release(mark);

        if errors.is_empty() {
            Ok(Root { children, span })
        } else {
            Err(errors)
        }
    }
}

#[derive(Debug)]
pub enum Item<'i> {
    Raw(Token<'i>),
    RawPrefix(Token<'i>, Token<'i>, Span<'i>),
    Directive(Directive<'i>),
}

impl<'i> Item<'i> {
    fn parse(stream: &mut TokenStream<'i>) -> Result<Self, ParseErrors<'i>> {
        match stream.peek() {
            TokenKind::DirectivePrefix => {
                let mark = stream.mark();
                let prefix = stream.demand(TokenKind::DirectivePrefix);
                // Here, we check to make sure that _immediately after_ our
                // prefix, we get an identifier.  This includes whitespace;
                // so `#hello` is valid, but `# hello` is not.  However, the
                // tokenizer automatically puts itself into a directive mode
                // state until we reach a newline, so we need to reset that
                // state if we don't get an identifier.
                let name = stream.next();
                if name.kind != TokenKind::Identifier {
                    stream.reset_mode();
                    return Ok(Self::RawPrefix(prefix, name, stream.release(mark)));
                }
                let directive = Directive::parse(stream, mark, name)?;
                Ok(Item::Directive(directive))
            }
            TokenKind::Raw => Ok(Item::Raw(stream.next())),
            _ => Err(ParseErrors {
                errors: vec![ParseError::unexpected_token(
                    vec![TokenKind::DirectivePrefix, TokenKind::Raw],
                    stream.next(),
                )],
            }),
        }
    }
}

#[derive(Debug)]
pub struct Directive<'i> {
    pub name: Token<'i>,
    pub arguments: Vec<Expression<'i>>,
    pub span: Span<'i>,
}

impl<'i> Directive<'i> {
    fn parse(
        stream: &mut TokenStream<'i>,
        mark: TokenMark,
        name: Token<'i>,
    ) -> Result<Self, ParseErrors<'i>> {
        let mut arguments = Vec::new();
        let mut errors = ParseErrors::default();
        stream.skip_whitespace();
        loop {
            let token = stream.peek();
            match token {
                TokenKind::Newline | TokenKind::Raw | TokenKind::Eof | TokenKind::Error => break,
                _ => match Expression::parse(stream) {
                    Ok(argument) => arguments.push(argument),
                    Err(err) => errors = errors.merge(err),
                },
            }

            stream.skip_whitespace();
        }

        if stream.peek() == TokenKind::Newline {
            stream.demand(TokenKind::Newline);
        } else {
            errors = errors.merge(
                ParseError::unexpected_token(vec![TokenKind::Newline], stream.peek_token()).into(),
            );
        }
        let span = stream.release(mark);

        if errors.is_empty() {
            Ok(Directive {
                name,
                arguments,
                span,
            })
        } else {
            stream.skip_to_sync();
            Err(errors)
        }
    }
}

#[derive(Debug, Clone)]
pub enum Expression<'i> {
    Parenthesized(Parenthesized<'i>),
    Identifier(Token<'i>),
    String(Token<'i>),
    Number(Token<'i>),
    BinaryOperation(BinaryOperation<'i>),
    UnaryOperation(UnaryOperation<'i>),
    Call(Call<'i>),
}

impl<'i> Expression<'i> {
    pub(super) fn span(&self) -> Span<'i> {
        match self {
            Expression::Parenthesized(p) => p.span,
            Expression::Identifier(i) => i.span,
            Expression::String(s) => s.span,
            Expression::Number(n) => n.span,
            Expression::BinaryOperation(b) => b.span,
            Expression::UnaryOperation(u) => u.span,
            Expression::Call(c) => c.span,
        }
    }

    pub(super) fn kind(&self) -> &'static str {
        match self {
            Expression::Parenthesized(_) => "parenthesized expression",
            Expression::Identifier(_) => "identifier",
            Expression::String(_) => "string literal",
            Expression::Number(_) => "number literal",
            Expression::BinaryOperation(_) => "binary operation",
            Expression::UnaryOperation(_) => "unary operation",
            Expression::Call(_) => "function call",
        }
    }

    fn parse(stream: &mut TokenStream<'i>) -> Result<Self, ParseErrors<'i>> {
        Self::parse_at(stream, PrecedenceLevel::Lowest)
    }

    fn parse_at(
        stream: &mut TokenStream<'i>,
        level: PrecedenceLevel,
    ) -> Result<Self, ParseErrors<'i>> {
        let mark = stream.mark();
        let mut base = Self::parse_atom(stream)?;
        loop {
            stream.skip_whitespace();
            let next = stream.peek();
            if next == TokenKind::Eof {
                break;
            }
            let Some(next_level) = PrecedenceLevel::from_token(next) else {
                break;
            };
            if next_level.escapes(level) {
                break;
            }
            let token = stream.next();
            stream.skip_whitespace();
            let right = Self::parse_at(stream, next_level)?;
            let span = stream.release(mark);
            base = Expression::BinaryOperation(BinaryOperation {
                left: Box::new(base),
                operator: token,
                right: Box::new(right),
                span,
            });
        }

        Ok(base)
    }

    fn parse_atom(stream: &mut TokenStream<'i>) -> Result<Self, ParseErrors<'i>> {
        match stream.peek() {
            TokenKind::LeftParen => Ok(Expression::Parenthesized(Parenthesized::parse(stream)?)),
            TokenKind::Identifier => {
                let identifier = stream.demand(TokenKind::Identifier);
                if stream.peek() == TokenKind::LeftParen {
                    Ok(Expression::Call(Call::parse(stream, identifier)?))
                } else {
                    Ok(Expression::Identifier(identifier))
                }
            }
            TokenKind::String => Ok(Expression::String(stream.demand(TokenKind::String))),
            TokenKind::Number => Ok(Expression::Number(stream.demand(TokenKind::Number))),

            TokenKind::Minus | TokenKind::Plus | TokenKind::Exclamation | TokenKind::Tilde => {
                Ok(Expression::UnaryOperation(UnaryOperation::parse(stream)?))
            }
            TokenKind::Raw => panic!("we should not see a raw token"),
            _ => Err(ParseErrors {
                errors: vec![ParseError::unexpected_token(
                    vec![
                        TokenKind::LeftParen,
                        TokenKind::Identifier,
                        TokenKind::String,
                        TokenKind::Number,
                        TokenKind::Minus,
                        TokenKind::Plus,
                        TokenKind::Exclamation,
                        TokenKind::Tilde,
                    ],
                    stream.peek_token(),
                )],
            }),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Parenthesized<'i> {
    pub expression: Box<Expression<'i>>,
    pub span: Span<'i>,
}

impl<'i> Parenthesized<'i> {
    fn parse(stream: &mut TokenStream<'i>) -> Result<Self, ParseErrors<'i>> {
        let mark = stream.mark();
        stream.demand(TokenKind::LeftParen);
        let expression = stream.delimit(|stream| {
            stream.skip_whitespace();
            let expression = Expression::parse(stream)?;
            stream.skip_whitespace();
            Ok::<_, ParseErrors<'i>>(expression)
        })?;
        stream.expect(TokenKind::RightParen)?;
        let span = stream.release(mark);
        Ok(Parenthesized {
            expression: Box::new(expression),
            span,
        })
    }
}

#[derive(Debug, Clone)]
pub struct BinaryOperation<'i> {
    pub left: Box<Expression<'i>>,
    pub operator: Token<'i>,
    pub right: Box<Expression<'i>>,
    pub span: Span<'i>,
}

#[derive(Debug, Clone)]
pub struct UnaryOperation<'i> {
    pub operator: Token<'i>,
    pub operand: Box<Expression<'i>>,
    pub span: Span<'i>,
}

impl<'i> UnaryOperation<'i> {
    fn parse(stream: &mut TokenStream<'i>) -> Result<Self, ParseErrors<'i>> {
        let mark = stream.mark();
        let operator = stream.next();
        let operand = Expression::parse_at(stream, PrecedenceLevel::Unary)?;
        let span = stream.release(mark);
        Ok(UnaryOperation {
            operator,
            operand: Box::new(operand),
            span,
        })
    }
}

#[derive(Debug, Clone)]
pub struct Call<'i> {
    pub callee: Token<'i>,
    pub arguments: Vec<Expression<'i>>,
    pub span: Span<'i>,
}

impl<'i> Call<'i> {
    fn parse(stream: &mut TokenStream<'i>, callee: Token<'i>) -> Result<Self, ParseErrors<'i>> {
        let mark = stream.mark();
        stream.expect(TokenKind::LeftParen)?;
        let arguments = stream.delimit(|stream| {
            stream.skip_whitespace();

            if stream.peek() == TokenKind::RightParen {
                return Ok::<_, ParseErrors<'i>>(vec![]);
            }

            let mut expressions = vec![Expression::parse(stream)?];
            stream.skip_whitespace();

            while let TokenKind::Comma = stream.peek() {
                stream.demand(TokenKind::Comma);
                stream.skip_whitespace();
                expressions.push(Expression::parse(stream)?);
                stream.skip_whitespace();
            }
            Ok::<_, ParseErrors<'i>>(expressions)
        })?;

        stream.expect(TokenKind::RightParen)?;
        let span = stream.release(mark).merge(callee.span);
        Ok(Call {
            callee,
            arguments,
            span,
        })
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum PrecedenceLevel {
    Lowest = 0,
    LogicalOr,
    LogicalAnd,
    BitOr,
    BitAnd,
    Equality,
    Ord,
    Additive,
    Multiplicative,
    Unary,
}

impl PrecedenceLevel {
    fn from_token(token: TokenKind) -> Option<Self> {
        match token {
            TokenKind::Asterisk | TokenKind::Slash | TokenKind::Percent => {
                Some(PrecedenceLevel::Multiplicative)
            }
            TokenKind::Plus | TokenKind::Minus => Some(PrecedenceLevel::Additive),
            TokenKind::LessThan
            | TokenKind::LessThanEqual
            | TokenKind::GreaterThan
            | TokenKind::GreaterThanEqual => Some(PrecedenceLevel::Ord),
            TokenKind::Equals | TokenKind::NotEquals => Some(PrecedenceLevel::Equality),
            TokenKind::Ampersand => Some(PrecedenceLevel::BitAnd),
            TokenKind::Pipe => Some(PrecedenceLevel::BitOr),
            TokenKind::And => Some(PrecedenceLevel::LogicalAnd),
            TokenKind::Or => Some(PrecedenceLevel::LogicalOr),
            _ => None,
        }
    }

    fn right_associative(self) -> bool {
        matches!(self, PrecedenceLevel::Unary)
    }

    fn escapes(self, current: Self) -> bool {
        if self == current {
            self.right_associative()
        } else {
            self < current
        }
    }
}

#[derive(Debug)]
pub(super) struct TokenStream<'i> {
    tokens: Tokenizer<'i>,
    buffer: VecDeque<Token<'i>>,
    within_delimiter: usize,
    peek_fuel: Cell<usize>,
}

impl<'i> TokenStream<'i> {
    pub fn new(tokens: Tokenizer<'i>) -> Self {
        TokenStream {
            tokens,
            buffer: VecDeque::with_capacity(1),
            within_delimiter: 0,
            peek_fuel: Cell::new(256),
        }
    }

    pub fn peek(&mut self) -> TokenKind {
        self.peek_token().kind
    }

    pub fn peek_token(&mut self) -> Token<'i> {
        assert_ne!(
            self.peek_fuel.get(),
            0,
            "peek fuel exhausted with token {:?}",
            self.buffer.front()
        );
        self.peek_fuel.set(self.peek_fuel.get() - 1);
        if self.buffer.is_empty() {
            if let Some(token) = self.tokens.next() {
                self.buffer.push_back(token);
            }
        }
        self.buffer
            .front()
            .copied()
            .unwrap_or_else(|| Token::new(TokenKind::Eof, self.tokens.at_eof()))
    }

    pub fn expect(&mut self, token: TokenKind) -> Result<Token<'i>, ParseErrors<'i>> {
        if self.peek() == token {
            Ok(self.next())
        } else {
            Err(ParseErrors {
                errors: vec![ParseError::UnexpectedToken {
                    expected: vec![token],
                    found: self.peek_token(),
                }],
            })
        }
    }

    pub fn demand(&mut self, token: TokenKind) -> Token<'i> {
        self.expect(token)
            .expect("peek gave one token, next gave another?")
    }

    pub fn reset_mode(&mut self) {
        debug_assert_eq!(self.buffer.len(), 0);
        self.tokens.reset_mode();
    }

    pub fn mark(&mut self) -> TokenMark {
        // if we have anything in the buffer, then the position in the
        // tokenizer will be invalid, as the tokenizer had already advanced
        // past where we want to be.  So if we have something in the buffer,
        // we'll extract the starting position of that token instead.
        if let Some(token) = self.buffer.front() {
            TokenMark {
                position: token.span.start(),
            }
        } else {
            self.tokens.mark()
        }
    }

    pub fn release(&mut self, mark: TokenMark) -> Span<'i> {
        // again, since we're releasing the mark, we need to check the buffer
        // first, to see if we have anything in there.
        if let Some(token) = self.buffer.front() {
            Span::new(
                self.tokens.input,
                mark.position,
                token.span.start().saturating_sub(mark.position),
            )
        } else {
            self.tokens.since(mark)
        }
    }

    pub fn next(&mut self) -> Token<'i> {
        self.peek_fuel.set(256);
        if self.buffer.is_empty() {
            self.tokens.next()
        } else {
            self.buffer.pop_front()
        }
        .expect("no token to get, but peek returned one?")
        // .unwrap_or_else(|| Token::new(TokenKind::Eof, self.tokens.at_eof()));
    }

    pub fn skip_to_sync(&mut self) {
        while !self.peek().is_sync() {
            self.next();
        }
    }

    pub fn delimit<F, T>(&mut self, f: F) -> T
    where
        F: FnOnce(&mut Self) -> T,
    {
        debug_assert!(self.buffer.is_empty());
        self.within_delimiter += 1;
        self.tokens.super_mode(true);
        let t = f(self);
        self.within_delimiter -= 1;
        if self.within_delimiter == 0 {
            self.tokens.super_mode(false);
        }
        t
    }

    pub fn skip_whitespace(&mut self) {
        let within_delimiter = self.within_delimiter;
        let can_skip = |kind: TokenKind| {
            kind.is_whitespace() || (within_delimiter > 0 && kind.is_inline_content())
        };

        while can_skip(self.peek()) {
            self.next();
        }
    }

    /*
    // A bit of an odd function.  We want to allow users to break up their code
    // across lines (keeping everything on one line can be unweildy), but since
    // we also want to make sure all of our code is commented out, every line
    // needs to start with our comment character.  However, we do not want to
    // confuse a continuation with a new directive, so we'll only allow skipping
    // inline content in certain circumstances (i.e., within clearly delimited
    // content).
    pub fn skip_inline_content(&mut self) {
        while let Some(token) = self.peek() {
            if !token.is_inline_content() {
                break;
            }

            self.next();
        }
    }*/
}

mod displays {
    use super::{
        BinaryOperation, Call, Directive, Expression, Item, Parenthesized, Root, UnaryOperation,
    };
    pub use std::fmt::{Display, Formatter, Result as FmtResult, Write as FmtWrite};

    impl Display for Root<'_> {
        fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
            self.print(0, f)
        }
    }

    struct AltSpan<'i>(super::Span<'i>, bool);

    impl Display for AltSpan<'_> {
        fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
            if self.1 {
                write!(f, "{{{}}}", self.0)
            } else {
                Ok(())
            }
        }
    }

    impl Root<'_> {
        fn print(&self, depth: usize, f: &mut Formatter<'_>) -> FmtResult {
            let indent = "    ".repeat(depth);
            if self.children.is_empty() {
                return writeln!(f, "{indent}(root)");
            }
            writeln!(f, "{indent}(root{}", AltSpan(self.span, f.alternate()))?;

            for item in &self.children {
                item.print(depth + 1, f)?;
            }
            writeln!(f, "{indent})")
        }
    }

    impl Item<'_> {
        fn print(&self, depth: usize, f: &mut Formatter<'_>) -> FmtResult {
            let indent = "    ".repeat(depth);
            match self {
                Item::Raw(r) => writeln!(f, "{indent}(raw{})", AltSpan(r.span, f.alternate())),
                Item::RawPrefix(p, r, s) => writeln!(
                    f,
                    "{indent}(raw-prefix{} '{}' '{}')",
                    AltSpan(*s, f.alternate()),
                    p.as_str().escape_debug(),
                    r.as_str().escape_debug()
                ),
                Item::Directive(d) => d.print(depth, f),
            }
        }
    }

    impl Directive<'_> {
        fn print(&self, depth: usize, f: &mut Formatter<'_>) -> FmtResult {
            let indent = "    ".repeat(depth);
            if self.arguments.is_empty() {
                return writeln!(
                    f,
                    "{indent}(directive{} \"{}\")",
                    AltSpan(self.span, f.alternate()),
                    self.name.as_str().escape_debug()
                );
            }
            writeln!(
                f,
                "{indent}(directive{} \"{}\"",
                AltSpan(self.span, f.alternate()),
                self.name.as_str().escape_debug()
            )?;
            for arg in &self.arguments {
                arg.print(depth + 1, f)?;
            }
            writeln!(f, "{indent})")
        }
    }

    impl Expression<'_> {
        fn print(&self, depth: usize, f: &mut Formatter<'_>) -> FmtResult {
            let indent = "    ".repeat(depth);
            match self {
                Expression::Identifier(i) => {
                    writeln!(
                        f,
                        "{indent}(ident{} \"{}\")",
                        AltSpan(i.span, f.alternate()),
                        i.as_str().escape_debug()
                    )
                }
                Expression::String(s) => {
                    writeln!(f, "{indent}(str{})", AltSpan(s.span, f.alternate()))
                    //,// s.as_str().escape_debug())
                }
                Expression::Number(n) => {
                    writeln!(
                        f,
                        "{indent}(num{} \"{}\")",
                        AltSpan(n.span, f.alternate()),
                        n.as_str().escape_debug()
                    )
                }
                Expression::Parenthesized(p) => p.print(depth, f),
                Expression::BinaryOperation(op) => op.print(depth, f),
                Expression::UnaryOperation(op) => op.print(depth, f),
                Expression::Call(call) => call.print(depth, f),
            }
        }
    }

    impl Parenthesized<'_> {
        fn print(&self, depth: usize, f: &mut Formatter<'_>) -> FmtResult {
            let indent = "    ".repeat(depth);
            writeln!(f, "{indent}(paren{}", AltSpan(self.span, f.alternate()))?;
            self.expression.print(depth + 1, f)?;
            writeln!(f, "{indent})")
        }
    }

    impl BinaryOperation<'_> {
        fn print(&self, depth: usize, f: &mut Formatter<'_>) -> FmtResult {
            let indent = "    ".repeat(depth);
            writeln!(
                f,
                "{indent}(binop{} '{}'",
                AltSpan(self.span, f.alternate()),
                self.operator.as_str()
            )?;
            self.left.print(depth + 1, f)?;
            self.right.print(depth + 1, f)?;
            writeln!(f, "{indent})")
        }
    }

    impl UnaryOperation<'_> {
        fn print(&self, depth: usize, f: &mut Formatter<'_>) -> FmtResult {
            let indent = "    ".repeat(depth);
            writeln!(
                f,
                "{indent}(unop{} '{}'",
                AltSpan(self.span, f.alternate()),
                self.operator.as_str()
            )?;
            self.operand.print(depth + 1, f)?;
            writeln!(f, "{indent})")
        }
    }

    impl Call<'_> {
        fn print(&self, depth: usize, f: &mut Formatter<'_>) -> FmtResult {
            let indent = "    ".repeat(depth);
            writeln!(f, "{indent}(call{}", AltSpan(self.span, f.alternate()),)?;
            Expression::Identifier(self.callee).print(depth + 1, f)?;
            writeln!(f, "{indent}    (params")?;
            for arg in &self.arguments {
                arg.print(depth + 2, f)?;
            }
            writeln!(f, "{indent}    )\n{indent})")
        }
    }
}
