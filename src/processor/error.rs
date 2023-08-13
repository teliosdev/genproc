use super::location::Span;
use super::tokens::{Token, TokenKind};

pub struct DisplayError<'i, 'e> {
    pub span: Span<'i>,
    pub message: &'e dyn std::fmt::Display,
    pub file: Option<&'e dyn std::fmt::Display>,
}

impl<'i, 'e> std::fmt::Display for DisplayError<'i, 'e> {
    #[allow(clippy::print_stderr)]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use owo_colors::OwoColorize;

        struct Repeat<'s>(usize, &'s str);

        impl<'s> std::fmt::Display for Repeat<'s> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                for _ in 0..self.0 {
                    write!(f, "{}", self.1)?;
                }
                Ok(())
            }
        }

        struct DisplayLineCol(line_index::LineCol);

        impl std::fmt::Display for DisplayLineCol {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(
                    f,
                    "{line}:{column}",
                    line = self.0.line,
                    column = self.0.col
                )
            }
        }

        // inefficient, but consider: bite me.
        let index = line_index::LineIndex::new(self.span.input);
        let mut start = index.line_col(line_index::TextSize::new(self.span.start()));
        let mut end = index.line_col(line_index::TextSize::new(self.span.end()));
        let file = self.file.unwrap_or(&"<unknown>");

        start.line += 1;
        end.line += 1;

        let start_display = DisplayLineCol(start);
        let end_display = DisplayLineCol(end);

        writeln!(
            f,
            "{file}:{start_display}-{end_display}: {message}",
            message = self.message.red()
        )?;

        let context = if end.line - start.line < 4 { 3 } else { 1 };
        let start_line = start.line.saturating_sub(context);
        let end_line = end.line + context;

        let lines = self.span.input.lines().enumerate().filter_map(|(i, line)| {
            let no = u32::try_from(i + 1).expect("a file with more than 4 billion lines?");
            if no >= start_line && no <= end_line {
                Some((no, line))
            } else {
                None
            }
        });

        let line_number_width = (end_line.ilog10() + 1) as usize;

        for (number, line) in lines {
            let is_within_span = number >= start.line && number <= end.line;
            let is_single_line = start.line == end.line && start.line == number;

            let line_number = format!("{number:0>line_number_width$}");

            if is_within_span && is_single_line {
                let (prefix, middle, end) = (
                    &line[..(start.col as usize)],
                    &line[(start.col as usize)..(end.col as usize)],
                    &line[(end.col as usize)..],
                );
                writeln!(
                    f,
                    "┊\t{line_number} ┃ {prefix}{middle}{end}",
                    line_number = line_number.blue().bold(),
                    middle = middle.bold(),
                )?;
                let pointer = if middle.len() <= 1 { "▲" } else { "└" };
                writeln!(
                    f,
                    "┊\t{number} ┃ {prefix}{pointer}{middle}{end}",
                    number = Repeat(line_number_width, " "),
                    prefix = Repeat(prefix.len(), " "),
                    middle = Repeat(middle.len().saturating_sub(2), "┄"),
                    end = if middle.len() > 1 { "┘" } else { "" }
                )?;
            } else if is_within_span {
                writeln!(
                    f,
                    "┊\t{line_number} ┃ {line}",
                    line_number = line_number.blue().bold()
                )?;
            } else {
                writeln!(
                    f,
                    "┊\t{line_number} ┆ {line}",
                    line_number = line_number.blue()
                )?;
            }
        }

        writeln!(f)
    }
}

#[derive(Debug)]
pub enum ParseError<'i> {
    UnexpectedToken {
        expected: Vec<TokenKind>,
        found: Token<'i>,
    },
}

impl std::fmt::Display for ParseError<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParseError::UnexpectedToken { expected, found } => {
                struct AnyOf<'i>(&'i [TokenKind]);
                impl std::fmt::Display for AnyOf<'_> {
                    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                        let mut iter = self.0.iter();
                        if let Some(kind) = iter.next() {
                            write!(f, "'{kind}'")?;
                            for kind in iter {
                                write!(f, ", '{kind}'")?;
                            }
                        }
                        Ok(())
                    }
                }
                write!(
                    f,
                    "expected one of {}, found '{}'",
                    AnyOf(&expected[..]),
                    found.kind.as_str()
                )
            }
        }
    }
}

impl<'i> ParseError<'i> {
    pub(super) fn unexpected_token(expected: Vec<TokenKind>, found: Token<'i>) -> Self {
        ParseError::UnexpectedToken { expected, found }
    }

    pub fn within_file<'s>(&'s self, file: &'s dyn std::fmt::Display) -> DisplayError<'i, 's> {
        DisplayError {
            span: self.span(),
            message: self,
            file: Some(file),
        }
    }

    fn merge_compatible(&self, other: &Self) -> bool {
        match (self, other) {
            (
                ParseError::UnexpectedToken {
                    found: left_found, ..
                },
                ParseError::UnexpectedToken {
                    found: right_found, ..
                },
            ) => left_found == right_found,
        }
    }

    fn merge(&mut self, other: &mut Self) {
        match (self, other) {
            (
                ParseError::UnexpectedToken {
                    expected: left_expected,
                    ..
                },
                ParseError::UnexpectedToken {
                    expected: right_expected,
                    ..
                },
            ) => {
                left_expected.append(right_expected);
            }
        }
    }

    pub fn span(&self) -> Span<'i> {
        match self {
            ParseError::UnexpectedToken { found, .. } => found.span,
        }
    }
}

#[derive(Default, Debug)]
pub struct ParseErrors<'i> {
    pub errors: Vec<ParseError<'i>>,
}

impl<'i> ParseErrors<'i> {
    pub(super) fn merge(self, mut rhs: Self) -> Self {
        let mut errors = self.errors;

        if errors.len() == 1 && rhs.errors.len() == 1 && errors[0].merge_compatible(&rhs.errors[0])
        {
            errors[0].merge(&mut rhs.errors[0]);
        } else {
            errors.extend(rhs.errors);
        }
        ParseErrors { errors }
    }

    pub(super) fn is_empty(&self) -> bool {
        self.errors.is_empty()
    }
}

impl std::ops::BitOr for ParseErrors<'_> {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        let mut errors = self.errors;
        errors.extend(rhs.errors);
        ParseErrors { errors }
    }
}

impl<'i> From<ParseError<'i>> for ParseErrors<'i> {
    fn from(this: ParseError<'i>) -> ParseErrors<'i> {
        ParseErrors { errors: vec![this] }
    }
}

#[derive(Debug)]
pub enum ExecError<'i> {
    UnknownDirective {
        name: Token<'i>,
    },
    UnexpectedElse {
        name: Token<'i>,
        span: Span<'i>,
    },
    UnknownFunction {
        name: Token<'i>,
        span: Span<'i>,
    },
    ExpectedParameters {
        name: Token<'i>,
        expected: usize,
        found: usize,
        span: Span<'i>,
    },
    UnexpectedParameters {
        name: Token<'i>,
        expected: usize,
        found: usize,
        span: Span<'i>,
    },
    UnknownVariable {
        name: Token<'i>,
    },
    InvalidNumber {
        value: Token<'i>,
        error: std::num::ParseIntError,
    },
    InvalidFloat {
        value: Token<'i>,
        error: std::num::ParseFloatError,
    },
    ExpectedBoolean {
        kind: &'static str,
        span: Span<'i>,
    },
    ExpectedIdentifier {
        kind: &'static str,
        span: Span<'i>,
    },
    InvalidOperation {
        left: Option<String>,
        right: String,
        operator: Token<'i>,
        span: Span<'i>,
    },
    InvalidArgumentCount {
        name: Token<'i>,
        expected: usize,
        found: usize,
        span: Span<'i>,
    },
    NoteFunctionDefinitionHere {
        name: Token<'i>,
        span: Span<'i>,
    },
    UnclosedConditional {
        span: Span<'i>,
    },
    UserError {
        message: String,
        span: Span<'i>,
    },
}

impl std::fmt::Display for ExecError<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExecError::UnknownDirective { name } => {
                write!(f, "unknown directive '{name}', ignoring")
            }
            ExecError::UnexpectedElse { name, .. } => {
                write!(f, "unexpected {name}")
            }
            ExecError::UnknownFunction { name, .. } => {
                write!(f, "unknown function '{name}'")
            }
            ExecError::ExpectedParameters {
                name,
                expected,
                found,
                ..
            } => write!(
                f,
                "directive '{name}' expects at least {expected} parameters, found {found}",
            ),
            ExecError::UnexpectedParameters {
                name,
                expected,
                found,
                ..
            } => write!(
                f,
                "directive '{name}' expects at most {expected} parameters, found {found}",
            ),
            ExecError::UnknownVariable { name } => {
                write!(f, "unknown variable '{name}'")
            }
            ExecError::ExpectedIdentifier { kind, .. } => {
                write!(f, "expected identifier, found {kind}")
            }
            ExecError::InvalidNumber { value, error } => {
                write!(f, "invalid number '{value}': {error}")
            }
            ExecError::InvalidFloat { value, error } => {
                write!(f, "invalid float '{value}': {error}")
            }
            ExecError::ExpectedBoolean { kind, .. } => {
                write!(f, "expected boolean, found {kind}")
            }
            ExecError::InvalidOperation {
                left,
                right,
                operator,
                ..
            } => {
                if let Some(left) = left {
                    write!(
                        f,
                        "invalid operation: cannot apply operator '{operator}' to '{left}' and '{right}'",
                    )
                } else {
                    write!(
                        f,
                        "invalid operation: cannot apply operator '{operator}' to '{right}'",
                    )
                }
            }
            ExecError::InvalidArgumentCount {
                name,
                expected,
                found,
                ..
            } => write!(
                f,
                "function '{name}' expects {expected} arguments, found {found}",
            ),
            ExecError::NoteFunctionDefinitionHere { name, .. } => {
                write!(f, "note: function '{name}' defined here")
            }
            ExecError::UnclosedConditional { .. } => {
                write!(
                    f,
                    "unclosed conditional; did you forget an 'endif' directive?"
                )
            }
            ExecError::UserError { message, .. } => {
                write!(f, "{message}")
            }
        }
    }
}

impl<'i> ExecError<'i> {
    pub(super) fn unknown_directive(name: Token<'i>) -> Self {
        ExecError::UnknownDirective { name }
    }

    pub(super) fn unexpected_else(name: Token<'i>, span: Span<'i>) -> Self {
        ExecError::UnexpectedElse { name, span }
    }

    pub(super) fn unknown_function(name: Token<'i>, span: Span<'i>) -> Self {
        ExecError::UnknownFunction { name, span }
    }

    pub(super) fn expected_parameters(
        name: Token<'i>,
        expected: usize,
        found: usize,
        span: Span<'i>,
    ) -> Self {
        ExecError::ExpectedParameters {
            name,
            expected,
            found,
            span,
        }
    }

    pub(super) fn unexpected_parameters(
        name: Token<'i>,
        expected: usize,
        found: usize,
        span: Span<'i>,
    ) -> Self {
        ExecError::UnexpectedParameters {
            name,
            expected,
            found,
            span,
        }
    }

    pub(super) fn invalid_number(value: Token<'i>, error: std::num::ParseIntError) -> Self {
        ExecError::InvalidNumber { value, error }
    }

    pub(super) fn invalid_float(value: Token<'i>, error: std::num::ParseFloatError) -> Self {
        ExecError::InvalidFloat { value, error }
    }

    pub(super) fn unknown_variable(name: Token<'i>) -> Self {
        ExecError::UnknownVariable { name }
    }

    pub(super) fn is_unknown_variable(&self) -> bool {
        matches!(self, ExecError::UnknownVariable { .. })
    }

    pub(super) fn expected_boolean(kind: &'static str, span: Span<'i>) -> Self {
        ExecError::ExpectedBoolean { kind, span }
    }

    pub(super) fn expected_identifier(kind: &'static str, span: Span<'i>) -> Self {
        ExecError::ExpectedIdentifier { kind, span }
    }

    pub(super) fn invalid_operation(
        left: Option<String>,
        right: String,
        operator: Token<'i>,
        span: Span<'i>,
    ) -> Self {
        ExecError::InvalidOperation {
            left,
            right,
            operator,
            span,
        }
    }

    pub(super) fn invalid_argument_count(
        name: Token<'i>,
        expected: usize,
        found: usize,
        span: Span<'i>,
    ) -> Self {
        ExecError::InvalidArgumentCount {
            name,
            expected,
            found,
            span,
        }
    }

    pub(super) fn unclosed_conditional(span: Span<'i>) -> Self {
        ExecError::UnclosedConditional { span }
    }

    pub(super) fn note_function_definition_here(name: Token<'i>, span: Span<'i>) -> Self {
        ExecError::NoteFunctionDefinitionHere { name, span }
    }

    pub(super) fn user_error(message: String, span: Span<'i>) -> Self {
        ExecError::UserError { message, span }
    }

    pub fn span(&self) -> Span<'i> {
        match self {
            ExecError::UnknownDirective { name } | ExecError::UnknownVariable { name } => name.span,
            ExecError::InvalidNumber { value, .. } | ExecError::InvalidFloat { value, .. } => {
                value.span
            }
            ExecError::UnexpectedElse { span, .. }
            | ExecError::UnknownFunction { span, .. }
            | ExecError::ExpectedParameters { span, .. }
            | ExecError::UnexpectedParameters { span, .. }
            | ExecError::ExpectedBoolean { span, .. }
            | ExecError::ExpectedIdentifier { span, .. }
            | ExecError::InvalidOperation { span, .. }
            | ExecError::InvalidArgumentCount { span, .. }
            | ExecError::NoteFunctionDefinitionHere { span, .. }
            | ExecError::UnclosedConditional { span }
            | ExecError::UserError { span, .. } => *span,
        }
    }

    pub fn within_file<'s>(&'s self, file: &'s dyn std::fmt::Display) -> DisplayError<'i, 's> {
        DisplayError {
            span: self.span(),
            message: self,
            file: Some(file),
        }
    }
}
