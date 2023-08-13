use std::borrow::Cow;
use std::rc::Rc;

use super::{Conditional, Eval};
use crate::processor::error::ExecError;
use crate::processor::location::Span;
use crate::processor::parser::{Directive, Expression};

fn assert_minimum_parameter_count<'i>(
    eval: &mut Eval<'i>,
    directive: &Directive<'i>,
    count: usize,
) -> bool {
    if directive.arguments.len() < count {
        eval.errors.push(ExecError::expected_parameters(
            directive.name,
            count,
            directive.arguments.len(),
            directive.span,
        ));
        false
    } else {
        true
    }
}

fn assert_maximum_parameter_count<'i>(
    eval: &mut Eval<'i>,
    directive: &Directive<'i>,
    count: usize,
) -> bool {
    if directive.arguments.len() > count {
        eval.errors.push(ExecError::unexpected_parameters(
            directive.name,
            count,
            directive.arguments.len(),
            directive.span,
        ));
        false
    } else {
        true
    }
}

#[allow(clippy::unnecessary_wraps)]
pub(super) fn apply<'i, W>(
    eval: &mut Eval<'i>,
    directive: &Directive<'i>,
    _out: &mut W,
) -> Result<(), std::io::Error> {
    match directive.name.as_str() {
        "if" => apply_if(eval, directive),
        "elsif" => apply_elsif(eval, directive),
        "else" => apply_else(eval, directive),
        "endif" => apply_endif(eval, directive),
        "replace" => apply_replace(eval, directive),
        "unrep" => apply_unrep(eval, directive),
        "define" => apply_define(eval, directive),
        "error" => apply_error(eval, directive),

        _ => {
            eval.errors
                .push(ExecError::unknown_directive(directive.name));
        }
    }
    Ok(())
}

fn apply_define<'i>(eval: &mut Eval<'i>, directive: &Directive<'i>) {
    if !assert_minimum_parameter_count(eval, directive, 2) {
        return;
    }
    assert_maximum_parameter_count(eval, directive, 2);

    match &directive.arguments[0] {
        Expression::Identifier(ident) => {
            let value = eval.evaluate(&directive.arguments[1]);
            eval.last_scope_mut()
                .variables
                .insert(ident.as_str().into(), value);
        }
        Expression::Call(call) => {
            let mut args: Vec<(Cow<'i, str>, Option<Span<'i>>)> = Vec::new();
            for arg in &call.arguments {
                match arg {
                    Expression::Identifier(ident) => {
                        args.push((Cow::Borrowed((*ident).as_str()), Some(ident.span)));
                    }
                    e => {
                        eval.errors
                            .push(ExecError::expected_identifier(e.kind(), e.span()));
                        return;
                    }
                }
            }
            eval.last_scope_mut().functions.insert(
                call.callee.as_str().into(),
                Rc::new(super::Function {
                    arguments: args,
                    // body: directive.arguments[1].clone(),
                    body: super::FunctionBody::Expression(directive.arguments[1].clone()),
                    span: Some(directive.span),
                }),
            );
        }
        e => {
            eval.errors
                .push(ExecError::expected_identifier(e.kind(), e.span()));
        }
    }
}

fn apply_if<'i>(eval: &mut Eval<'i>, directive: &Directive<'i>) {
    if !assert_minimum_parameter_count(eval, directive, 1) {
        return;
    }
    assert_maximum_parameter_count(eval, directive, 1);
    let active = eval.evaluate(&directive.arguments[0]).force_bool(eval);

    eval.conditionals.push(Conditional {
        current_active: active,
        any_active: active,
        span: directive.span,
    });
}

fn apply_elsif<'i>(eval: &mut Eval<'i>, directive: &Directive<'i>) {
    if !assert_minimum_parameter_count(eval, directive, 1) {
        return;
    }
    assert_maximum_parameter_count(eval, directive, 1);
    let active = eval.evaluate(&directive.arguments[0]).force_bool(eval);

    if let Some(conditional) = eval.conditionals.pop() {
        let active = !conditional.any_active && active;
        let current_active = !conditional.any_active && active;
        eval.conditionals.push(Conditional {
            current_active,
            any_active: conditional.any_active || active,
            span: directive.span,
        });
    } else {
        eval.errors
            .push(ExecError::unexpected_else(directive.name, directive.span));
        eval.conditionals.push(Conditional {
            current_active: active,
            any_active: active,
            span: directive.span,
        });
    }
}

fn apply_else<'i>(eval: &mut Eval<'i>, directive: &Directive<'i>) {
    assert_maximum_parameter_count(eval, directive, 0);

    let active = if let Some(conditional) = eval.conditionals.pop() {
        !conditional.any_active
    } else {
        eval.errors
            .push(ExecError::unexpected_else(directive.name, directive.span));
        false
    };
    eval.conditionals.push(Conditional {
        current_active: active,
        any_active: true,
        span: directive.span,
    });
}

fn apply_endif<'i>(eval: &mut Eval<'i>, directive: &Directive<'i>) {
    assert_maximum_parameter_count(eval, directive, 0);

    if eval.conditionals.pop().is_none() {
        eval.errors
            .push(ExecError::unexpected_else(directive.name, directive.span));
    }
}

fn apply_replace<'i>(eval: &mut Eval<'i>, directive: &Directive<'i>) {
    if !assert_minimum_parameter_count(eval, directive, 1) {
        return;
    }
    assert_maximum_parameter_count(eval, directive, 2);

    let ident = match &directive.arguments[0] {
        Expression::Identifier(ident) => ident,
        e => {
            eval.errors
                .push(ExecError::expected_identifier(e.kind(), e.span()));
            return;
        }
    };

    let replacement = if directive.arguments.len() > 1 {
        eval.evaluate(&directive.arguments[1])
    } else {
        eval.evaluate(&directive.arguments[0])
    };

    eval.last_scope_mut()
        .replacements
        .insert(ident.as_str().to_owned(), replacement);
    eval.generate_replacements();
}

fn apply_unrep<'i>(eval: &mut Eval<'i>, directive: &Directive<'i>) {
    if !assert_minimum_parameter_count(eval, directive, 1) {
        return;
    }
    assert_maximum_parameter_count(eval, directive, 1);

    let ident = match &directive.arguments[0] {
        Expression::Identifier(ident) => ident,
        e => {
            eval.errors
                .push(ExecError::expected_identifier(e.kind(), e.span()));
            return;
        }
    };

    eval.last_scope_mut().replacements.remove(ident.as_str());
    eval.generate_replacements();
}

fn apply_error<'i>(eval: &mut Eval<'i>, directive: &Directive<'i>) {
    assert_maximum_parameter_count(eval, directive, 1);

    let message = directive.arguments.first().map_or_else(
        || "user error while processing file".to_string(),
        |e| eval.evaluate(e).value.to_string(),
    );

    eval.errors
        .push(ExecError::user_error(message, directive.span));
}
