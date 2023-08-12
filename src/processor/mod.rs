mod error;
mod eval;
mod location;
pub mod parser;
mod tokens;

pub use self::error::ParseErrors;
pub use self::eval::Engine;
pub use self::parser::Root;
pub use self::tokens::is_bad_prefix;
pub use self::tokens::Tokenizer;

pub fn parse(tokenizer: Tokenizer<'_>) -> Result<Root<'_>, ParseErrors<'_>> {
    let mut token_stream = self::parser::TokenStream::new(tokenizer);
    Root::parse(&mut token_stream)
}
