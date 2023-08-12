use super::{ExprValue, Value};
use std::borrow::Cow;
use std::collections::BTreeMap;
use std::rc::Rc;

#[derive(Debug, Default, Clone)]
pub struct Scope<'s> {
    pub(super) functions: BTreeMap<Cow<'s, str>, Rc<super::Function<'s>>>,
    pub(super) variables: BTreeMap<Cow<'s, str>, super::ExprValue<'s>>,
    pub(super) replacements: BTreeMap<String, super::ExprValue<'s>>,
}

impl Scope<'static> {
    pub(super) fn std() -> Self {
        let functions = BTreeMap::new();
        let mut variables = BTreeMap::new();
        let replacements = BTreeMap::new();

        std_variables(&mut variables);

        Scope {
            functions,
            variables,
            replacements,
        }
    }
}

fn std_variables(variables: &mut BTreeMap<Cow<'static, str>, ExprValue<'static>>) {
    let mut insert = |name: &'static str, value: Value<'static>| {
        variables.insert(name.into(), ExprValue::of(value));
    };

    insert("pi", Value::Float(std::f64::consts::PI));
    insert("e", Value::Float(std::f64::consts::E));
    insert("true", Value::Boolean(true));
    insert("false", Value::Boolean(false));
    insert("null", Value::Null);
}
