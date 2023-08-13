mod directives;
mod scope;

use self::scope::Scope;
use super::error::ExecError;
use super::location::Span;
use super::parser::{Call, Directive, Expression, Item};
use super::tokens::Token;
use super::Root;
use crate::processor::tokens::TokenKind;
use std::borrow::Cow;

#[derive(Debug)]
pub struct Engine {
    scopes: Vec<Scope<'static>>,
}

impl Engine {
    pub fn new() -> Self {
        Engine {
            scopes: vec![Scope::std(), Scope::default()],
        }
    }

    pub fn define_strings<I, K, V>(&mut self, iter: I)
    where
        I: IntoIterator<Item = (K, V)>,
        K: Into<Cow<'static, str>>,
        V: Into<Value<'static>>,
    {
        for (name, value) in iter {
            self.scopes
                .last_mut()
                .unwrap()
                .variables
                .insert(name.into(), ExprValue::of(value.into()));
        }
    }

    pub fn replace_strings<I, K, V>(&mut self, iter: I)
    where
        I: IntoIterator<Item = (K, Option<V>)>,
        K: Into<Cow<'static, str>>,
        V: Into<Value<'static>>,
    {
        for (name, value) in iter {
            let name = name.into();
            let value = value.map(|v| ExprValue::of(v.into())).or_else(|| {
                self.scopes
                    .iter()
                    .find_map(|s| s.variables.get(&name))
                    .cloned()
            });

            if let Some(value) = value {
                self.scopes
                    .last_mut()
                    .unwrap()
                    .replacements
                    .insert(name.into(), value);
            }
        }
    }

    pub fn execute<'i, W>(
        &mut self,
        root: Root<'i>,
        out: &mut W,
    ) -> Result<Execution<'i>, std::io::Error>
    where
        W: std::io::Write,
    {
        let mut scopes: Vec<Scope<'i>> = self.scopes.clone();
        scopes.push(Scope::default());
        let mut eval = Eval {
            scopes,
            searcher: aho_corasick::AhoCorasick::new::<_, &&str>(&[]).unwrap(),
            conditionals: Vec::new(),
            errors: Vec::new(),
        };
        eval.generate_replacements();
        eval.execute(root, out)?;
        Ok(Execution {
            errors: eval.errors,
        })
    }
}

pub struct Execution<'i> {
    pub errors: Vec<ExecError<'i>>,
}

#[derive(Debug)]
struct Function<'i> {
    arguments: Vec<(Cow<'i, str>, Option<Span<'i>>)>,
    // body: Expression<'s>,
    body: FunctionBody<'i>,
    span: Option<Span<'i>>,
}

type NativeFunctionBody = Box<dyn for<'s> Fn(&mut Eval<'s>, Vec<ExprValue<'s>>) -> ExprValue<'s>>;

enum FunctionBody<'i> {
    Expression(Expression<'i>),
    Native(NativeFunctionBody),
}

impl std::fmt::Debug for FunctionBody<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FunctionBody::Expression(expr) => f
                .debug_tuple("FunctionBody::Expression")
                .field(expr)
                .finish(),
            FunctionBody::Native(_) => f
                .debug_tuple("FunctionBody::Native")
                .field(&"fn(...)")
                .finish(),
        }
    }
}

#[derive(Debug)]
struct Conditional<'s> {
    any_active: bool,
    current_active: bool,
    span: Span<'s>,
}

impl Conditional<'_> {
    fn is_active(&self) -> bool {
        self.current_active
    }
}

#[derive(Debug)]
pub struct Eval<'i> {
    scopes: Vec<Scope<'i>>,
    searcher: aho_corasick::AhoCorasick,
    conditionals: Vec<Conditional<'i>>,
    errors: Vec<ExecError<'i>>,
}

impl<'i> Eval<'i> {
    pub fn execute<W>(&mut self, root: Root<'i>, out: &mut W) -> Result<(), std::io::Error>
    where
        W: std::io::Write,
    {
        for child in root.children {
            match child {
                Item::Raw(raw) => self.output_raw(raw.as_str(), out)?,
                Item::RawPrefix(a, b, _) => {
                    self.output_raw(a.as_str(), out)?;
                    self.output_raw(b.as_str(), out)?;
                }
                Item::Directive(directive) => self.execute_directive(&directive, out)?,
            }
        }

        for conditional in &self.conditionals {
            self.errors
                .push(ExecError::unclosed_conditional(conditional.span));
        }

        Ok(())
    }

    fn generate_replacements(&mut self) {
        let replacement_strings = self
            .scopes
            .iter()
            .flat_map(|s| s.replacements.keys())
            .map(std::string::String::as_str);

        self.searcher = aho_corasick::AhoCorasick::new(replacement_strings)
            .expect("could not construct searcher");
    }

    fn find_replacement(&self, replacement: &str) -> Option<String> {
        self.scopes
            .iter()
            .find_map(|v| v.replacements.get(replacement))
            .map(|v| v.value.to_string())
    }

    fn last_scope_mut(&mut self) -> &mut Scope<'i> {
        self.scopes.last_mut().unwrap()
    }

    fn evaluate(&mut self, expression: &Expression<'i>) -> ExprValue<'i> {
        match expression {
            Expression::Parenthesized(v) => self.evaluate(&v.expression),
            Expression::Identifier(ident) => self.evaluate_identifier(*ident),
            Expression::String(s) => evaluate_string(*s),
            Expression::Number(n) => self.evaluate_number(*n),
            Expression::BinaryOperation(bin) => {
                let left = self.evaluate(&bin.left);
                let right = self.evaluate(&bin.right);
                perform_operation(self, bin.operator, Some(&left), &right, bin.span)
            }
            Expression::UnaryOperation(unop) => {
                let right = self.evaluate(&unop.operand);
                perform_operation(self, unop.operator, None, &right, unop.span)
            }
            Expression::Call(call) => self.evaluate_call(call),
        }
    }

    fn evaluate_identifier(&mut self, ident: Token<'i>) -> ExprValue<'i> {
        let given = self
            .scopes
            .iter()
            .find_map(|s| s.variables.get(ident.as_str()));
        if given.is_none() {
            self.errors.push(ExecError::unknown_variable(ident));
        }

        given
            .cloned()
            .unwrap_or_else(|| ExprValue::of(Value::Null))
            .with_source(ident.span)
    }

    fn evaluate_number(&mut self, number: Token<'i>) -> ExprValue<'i> {
        if number.kind == TokenKind::Float {
            match number.as_str().parse::<f64>() {
                Ok(v) => return ExprValue::of(Value::Float(v)).with_source(number.span),
                Err(e) => {
                    self.errors.push(ExecError::invalid_float(number, e));
                    return ExprValue::of(Value::Null).with_source(number.span);
                }
            }
        } else if let Some(number) = parse_prefix_number(self, number, "0b", 2) {
            return number;
        } else if let Some(number) = parse_prefix_number(self, number, "0x", 16) {
            return number;
        }
        match number.as_str().parse::<i64>() {
            Ok(v) => ExprValue::of(Value::Number(v)).with_source(number.span),
            Err(e) => {
                self.errors.push(ExecError::invalid_number(number, e));
                ExprValue::of(Value::Null).with_source(number.span)
            }
        }
    }

    fn evaluate_call(&mut self, call: &Call<'i>) -> ExprValue<'i> {
        let function = self
            .scopes
            .iter()
            .find_map(|s| s.functions.get(call.callee.as_str()));
        let function = match function {
            None => {
                self.errors
                    .push(ExecError::unknown_function(call.callee, call.span));
                return ExprValue::of(Value::Null).with_source(call.span);
            }
            Some(func) => func.clone(),
        };

        if function.arguments.len() != call.arguments.len() {
            self.errors.push(ExecError::invalid_argument_count(
                call.callee,
                function.arguments.len(),
                call.arguments.len(),
                call.span,
            ));

            if let Some(span) = function.span {
                self.errors
                    .push(ExecError::note_function_definition_here(call.callee, span));
            }
        }

        let mut arguments = Vec::new();
        for argument in &call.arguments {
            arguments.push(self.evaluate(argument));
        }
        if arguments.len() < function.arguments.len() {
            for _ in &function.arguments[arguments.len()..] {
                arguments.push(ExprValue::of(Value::Null));
            }
        }

        match function.body {
            FunctionBody::Expression(ref expr) => {
                self.scopes.push(Scope::default());
                for ((name, _), value) in function.arguments.iter().zip(arguments) {
                    self.last_scope_mut().variables.insert(name.clone(), value);
                }
                // let result = self.evaluate(&function.body);
                let result = self.evaluate(expr);
                self.scopes.pop();
                result
            }
            FunctionBody::Native(ref func) => func(self, arguments).with_source(call.span),
        }
    }

    fn execute_directive<W>(
        &mut self,
        directive: &Directive<'i>,
        out: &mut W,
    ) -> Result<(), std::io::Error> {
        self::directives::apply(self, directive, out)
    }

    fn output_raw<W>(&mut self, raw: &'i str, out: &mut W) -> Result<(), std::io::Error>
    where
        W: std::io::Write,
    {
        if self.conditionals.iter().any(|v| !v.is_active()) {
            return Ok(());
        }
        let end = self
            .searcher
            .find_iter(raw)
            .map(|m| m.range())
            .try_fold(0, |acc, el| {
                let start = el.start;
                let end = el.end;

                let before = &raw[acc..start];

                out.write_all(before.as_bytes()).and_then(|()| {
                    let expr = &raw[start..end];
                    match self.find_replacement(expr) {
                        Some(replacement) => out.write_all(replacement.as_bytes()),
                        None => out.write_all(expr.as_bytes()),
                    }
                    .map(|()| end)
                })
            })?;

        out.write_all(raw[end..].as_bytes())
    }
}

#[derive(Debug, Clone)]
struct ExprValue<'i> {
    value: Value<'i>,
    source: Option<Span<'i>>,
}

impl<'i> ExprValue<'i> {
    fn of(value: Value<'i>) -> Self {
        Self {
            value,
            source: None,
        }
    }

    fn with_source(self, span: Span<'i>) -> Self {
        self.copy_source(Some(span))
    }

    fn copy_source(self, span: Option<Span<'i>>) -> Self {
        Self {
            source: self.source.or(span),
            ..self
        }
    }

    fn force_bool(&self, eval: &mut Eval<'i>) -> bool {
        if let Value::Boolean(v) = self.value {
            return v;
        }

        if let Some(source) = self.source {
            eval.errors
                .push(ExecError::expected_boolean(self.value.kind(), source));
        }

        self.value.coerce_bool()
    }
}

static STRING_ESCAPE: once_cell::sync::Lazy<regex::Regex> = once_cell::sync::Lazy::new(|| {
    regex::Regex::new(r#"\\("|\\|/|b|f|n|r|t|u[0-9a-f]{4})"#).expect("regular expression is valid")
});

fn evaluate_string(string: Token<'_>) -> ExprValue<'_> {
    let value = string.as_str();
    let value = value.strip_prefix('"').unwrap_or(value);
    let value = value.strip_suffix('"').unwrap_or(value);
    let value = STRING_ESCAPE.replace_all(value, |cap: &regex::Captures<'_>| match &cap[1] {
        "\"" => Cow::Borrowed("\""),
        "\\" => Cow::Borrowed("\\"),
        "/" => Cow::Borrowed("/"),
        "b" => Cow::Borrowed("\u{0008}"),
        "n" => Cow::Borrowed("\n"),
        "r" => Cow::Borrowed("\r"),
        "t" => Cow::Borrowed("\t"),
        v => {
            let id = v
                .strip_prefix('b')
                .expect("we could not get here with a valid regex");
            let id = u32::from_str_radix(id, 16).expect("we could not get here with a valid regex");
            Cow::Owned(
                std::char::from_u32(id)
                    .unwrap_or(std::char::REPLACEMENT_CHARACTER)
                    .to_string(),
            )
        }
    });

    ExprValue::of(Value::String(value)).with_source(string.span)
}

fn parse_prefix_number<'i>(
    exec: &mut Eval<'i>,
    number: Token<'i>,
    prefix: &'static str,
    radix: u32,
) -> Option<ExprValue<'i>> {
    if let Some(value) = number.as_str().strip_prefix(prefix) {
        match i64::from_str_radix(value, radix) {
            Ok(v) => Some(ExprValue::of(Value::Number(v)).with_source(number.span)),
            Err(e) => {
                exec.errors.push(ExecError::invalid_number(number, e));
                Some(ExprValue::of(Value::Null).with_source(number.span))
            }
        }
    } else {
        None
    }
}

#[derive(Debug, Clone)]
pub enum Value<'i> {
    String(Cow<'i, str>),
    Number(i64),
    Float(f64),
    Boolean(bool),
    Null,
}

impl<'i> From<&'i str> for Value<'i> {
    fn from(v: &'i str) -> Self {
        Value::String(v.into())
    }
}

impl<'i> From<String> for Value<'i> {
    fn from(v: String) -> Self {
        Value::String(v.into())
    }
}

impl<'i> From<Cow<'i, str>> for Value<'i> {
    fn from(v: Cow<'i, str>) -> Self {
        Value::String(v)
    }
}

impl<'i> From<i64> for Value<'i> {
    fn from(v: i64) -> Self {
        Value::Number(v)
    }
}

impl<'i> From<f64> for Value<'i> {
    fn from(v: f64) -> Self {
        Value::Float(v)
    }
}

impl<'i> From<bool> for Value<'i> {
    fn from(v: bool) -> Self {
        Value::Boolean(v)
    }
}

impl<'i> From<()> for Value<'i> {
    fn from(_: ()) -> Self {
        Value::Null
    }
}

impl std::fmt::Display for Value<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::String(v) => write!(f, "{v}"),
            Value::Number(v) => write!(f, "{v}"),
            Value::Float(v) => write!(f, "{v}"),
            Value::Boolean(v) => write!(f, "{v}"),
            Value::Null => Ok(()),
        }
    }
}

impl Value<'_> {
    fn kind(&self) -> &'static str {
        match self {
            Value::String(_) => "string",
            Value::Number(_) => "number",
            Value::Float(_) => "float",
            Value::Boolean(_) => "boolean",
            Value::Null => "null",
        }
    }

    fn coerce_bool(&self) -> bool {
        match self {
            Value::Boolean(v) => *v,
            Value::Number(v) => *v != 0,
            Value::Float(v) => float_cmp::approx_eq!(f64, *v, 0.0),
            Value::String(v) => !v.is_empty(),
            Value::Null => false,
        }
    }

    fn mul(&self, rhs: &Self) -> Option<Self> {
        match (self, rhs) {
            (Value::Number(l), Value::Number(r)) => Some(Value::Number(l * r)),
            (Value::Float(l), Value::Float(r)) => Some(Value::Float(l * r)),
            (Value::String(str), Value::Number(count))
            | (Value::Number(count), Value::String(str)) => {
                let repeat = usize::try_from((*count).max(0)).expect("this should work."); // i64::MAX < usize::MAX
                if repeat == 0 {
                    Some(Value::String(Cow::Borrowed("")))
                } else if repeat == 1 {
                    Some(Value::String(str.clone()))
                } else {
                    Some(Value::String(str.repeat(repeat).into()))
                }
            }
            (_, Value::Null) | (Value::Null, _) => Some(Value::Null),
            _ => None,
        }
    }

    fn add(&self, rhs: &Self) -> Option<Self> {
        match (self, rhs) {
            (Value::Number(l), Value::Number(r)) => Some(Value::Number(l + r)),
            (Value::Float(l), Value::Float(r)) => Some(Value::Float(l + r)),
            (Value::String(l), Value::String(r)) => {
                let mut new = l.clone().into_owned();
                new.push_str(r.as_ref());
                Some(Value::String(new.into()))
            }
            (_, Value::Null) | (Value::Null, _) => Some(Value::Null),
            _ => None,
        }
    }

    fn sub(&self, rhs: &Self) -> Option<Self> {
        match (self, rhs) {
            (Value::Number(l), Value::Number(r)) => Some(Value::Number(l - r)),
            (Value::Float(l), Value::Float(r)) => Some(Value::Float(l - r)),
            (_, Value::Null) | (Value::Null, _) => Some(Value::Null),
            _ => None,
        }
    }

    fn div(&self, rhs: &Self) -> Option<Self> {
        match (self, rhs) {
            (Value::Number(l), Value::Number(r)) => Some(Value::Number(l / r)),
            (Value::Float(l), Value::Float(r)) => Some(Value::Float(l / r)),
            (_, Value::Null) | (Value::Null, _) => Some(Value::Null),
            _ => None,
        }
    }

    fn rem(&self, rhs: &Self) -> Option<Self> {
        match (self, rhs) {
            (Value::Number(l), Value::Number(r)) => Some(Value::Number(l % r)),
            (Value::Float(l), Value::Float(r)) => Some(Value::Float(l % r)),
            (_, Value::Null) | (Value::Null, _) => Some(Value::Null),
            _ => None,
        }
    }

    fn bitor(&self, rhs: &Self) -> Option<Self> {
        match (self, rhs) {
            (Value::Number(l), Value::Number(r)) => Some(Value::Number(l | r)),
            _ => None,
        }
    }

    fn bitand(&self, rhs: &Self) -> Option<Self> {
        match (self, rhs) {
            (Value::Number(l), Value::Number(r)) => Some(Value::Number(l & r)),
            _ => None,
        }
    }

    fn bitxor(&self, rhs: &Self) -> Option<Self> {
        match (self, rhs) {
            (Value::Number(l), Value::Number(r)) => Some(Value::Number(l ^ r)),
            (Value::Boolean(l), Value::Boolean(r)) => Some(Value::Boolean(l ^ r)),
            _ => None,
        }
    }

    fn binnot(&self) -> Option<Self> {
        match self {
            Value::Number(v) => Some(Value::Number(!v)),
            _ => None,
        }
    }

    fn logicnot(&self) -> Self {
        Self::Boolean(!self.coerce_bool())
    }

    fn negate(&self) -> Option<Self> {
        match self {
            Value::Number(v) => Some(Value::Number(-v)),
            Value::Float(v) => Some(Value::Float(-v)),
            _ => None,
        }
    }

    fn eq(&self, rhs: &Self) -> bool {
        self.cmp(rhs)
            .map_or(false, |v| v == std::cmp::Ordering::Equal)
    }

    fn cmp(&self, rhs: &Self) -> Option<std::cmp::Ordering> {
        match (self, rhs) {
            (Value::Number(l), Value::Number(r)) => l.partial_cmp(r),
            (Value::Float(l), Value::Float(r)) => l.partial_cmp(r),
            (Value::String(l), Value::String(r)) => l.partial_cmp(r),
            (Value::Boolean(l), Value::Boolean(r)) => l.partial_cmp(r),
            (Value::Null, Value::Null) => Some(std::cmp::Ordering::Equal),
            _ => None,
        }
    }
}

fn perform_operation<'i>(
    eval: &mut Eval<'i>,
    op: Token<'i>,
    left: Option<&ExprValue<'i>>,
    right: &ExprValue<'i>,
    span: Span<'i>,
) -> ExprValue<'i> {
    let value = match left {
        Some(left) => match op.kind {
            TokenKind::Plus => left.value.add(&right.value),
            TokenKind::Minus => left.value.sub(&right.value),
            TokenKind::Asterisk => left.value.mul(&right.value),
            TokenKind::Slash => left.value.div(&right.value),
            TokenKind::Percent => left.value.rem(&right.value),
            TokenKind::Pipe => left.value.bitor(&right.value),
            TokenKind::Ampersand => left.value.bitand(&right.value),
            TokenKind::Caret => left.value.bitxor(&right.value),
            TokenKind::Equals => Some(Value::Boolean(left.value.eq(&right.value))),
            TokenKind::NotEquals => Some(Value::Boolean(!left.value.eq(&right.value))),
            TokenKind::LessThan => left
                .value
                .cmp(&right.value)
                .map(std::cmp::Ordering::is_lt)
                .map(Value::Boolean),
            TokenKind::LessThanEqual => left
                .value
                .cmp(&right.value)
                .map(std::cmp::Ordering::is_le)
                .map(Value::Boolean),
            TokenKind::GreaterThan => left
                .value
                .cmp(&right.value)
                .map(std::cmp::Ordering::is_gt)
                .map(Value::Boolean),
            TokenKind::GreaterThanEqual => left
                .value
                .cmp(&right.value)
                .map(std::cmp::Ordering::is_ge)
                .map(Value::Boolean),
            TokenKind::And => Some(Value::Boolean(
                left.force_bool(eval) && right.force_bool(eval),
            )),
            TokenKind::Or => Some(Value::Boolean(
                left.force_bool(eval) || right.force_bool(eval),
            )),

            v => unreachable!("invalid operation {v}"),
        },
        None => match op.kind {
            TokenKind::Plus => Some(right.value.clone()),
            TokenKind::Minus => right.value.negate(),
            TokenKind::Tilde => right.value.binnot(),
            TokenKind::Exclamation => Some(right.value.logicnot()),
            _ => unreachable!("invalid operation"),
        },
    };

    let value = value.unwrap_or_else(|| {
        eval.errors.push(ExecError::invalid_operation(
            left.map(|v| v.value.to_string()),
            right.value.to_string(),
            op,
            span,
        ));

        Value::Null
    });

    ExprValue::of(value).with_source(span)
}
