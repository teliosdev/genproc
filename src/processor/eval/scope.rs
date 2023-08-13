use super::{ExprValue, Value};
use std::borrow::Cow;
use std::collections::HashMap;
use std::rc::Rc;

#[derive(Debug, Default, Clone)]
pub struct Scope<'i> {
    pub(super) functions: HashMap<Cow<'i, str>, Rc<super::Function<'i>>>,
    pub(super) variables: HashMap<Cow<'i, str>, super::ExprValue<'i>>,
    pub(super) replacements: HashMap<String, super::ExprValue<'i>>,
}

impl Scope<'static> {
    pub(super) fn std() -> Self {
        let mut functions = HashMap::new();
        let mut variables = HashMap::new();
        let replacements = HashMap::new();

        std_variables(&mut variables);
        std_functions(&mut functions);

        Scope {
            functions,
            variables,
            replacements,
        }
    }
}

fn std_variables(variables: &mut HashMap<Cow<'static, str>, ExprValue<'static>>) {
    let mut insert = |name: &'static str, value: Value<'static>| {
        variables.insert(name.into(), ExprValue::of(value));
    };

    insert("pi", Value::Float(std::f64::consts::PI));
    insert("e", Value::Float(std::f64::consts::E));
    insert("true", Value::Boolean(true));
    insert("false", Value::Boolean(false));
    insert("null", Value::Null);
}

struct FunctionMap<'f>(&'f mut HashMap<Cow<'static, str>, Rc<super::Function<'static>>>);
impl<'f> FunctionMap<'f> {
    fn insert(
        &mut self,
        name: &'static str,
        params: &[&'static str],
        f: impl for<'s> Fn(&mut super::Eval<'s>, Vec<super::ExprValue<'s>>) -> super::ExprValue<'s>
            + 'static,
    ) {
        let func = super::Function {
            arguments: params.iter().map(|p| (Cow::Borrowed(*p), None)).collect(),
            body: super::FunctionBody::Native(Box::new(f)),
            span: None,
        };

        self.0.insert(name.into(), Rc::new(func));
    }
}

fn std_functions(functions: &mut HashMap<Cow<'static, str>, Rc<super::Function<'static>>>) {
    let mut map = FunctionMap(functions);

    map.insert("bool", &["value"], |_eval, mut args| {
        let value = args
            .drain(..)
            .next_back()
            .unwrap_or(ExprValue::of(Value::Null));
        ExprValue::of(Value::from(value.value.coerce_bool())).copy_source(value.source)
    });

    map.insert("defined", &["value"], |eval, mut args| {
        let value = args
            .drain(..)
            .next_back()
            .unwrap_or(ExprValue::of(Value::Null));

        let errors = std::mem::take(&mut eval.errors);

        // This is so hacky.  So incredibly hacky.  Basically, we're looking
        // for any errors already issued for the variable we're checking.
        // We'll filter out any errors that would match; however, this doesn't
        // filter out anything else; if, for example, there is an expression
        // in place, this won't work properly.  (Though that's probably
        // intentional at that point.)
        eval.errors = errors
            .into_iter()
            .filter(|error| {
                !(error.is_unknown_variable()
                    && value.source.is_some_and(|source| source == error.span()))
            })
            .collect();

        let is_null = matches!(value.value, Value::Null);
        ExprValue::of(Value::Boolean(!is_null)).copy_source(value.source)
    });
}
