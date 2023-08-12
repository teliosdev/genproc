#![warn(
    clippy::pedantic,
    clippy::all,
    missing_debug_implementations,
    rust_2018_idioms,
    rust_2021_compatibility,
    clippy::dbg_macro,
    clippy::print_stdout,
    clippy::print_stderr,
    clippy::unimplemented,
    clippy::todo,
    clippy::exhaustive_enums,
    clippy::impl_trait_in_params,
    clippy::map_err_ignore,
    clippy::mem_forget
)]
#![deny(clippy::correctness, unused_must_use)]
#![allow(clippy::missing_errors_doc, clippy::module_name_repetitions)]
#![forbid(unsafe_code)]

use self::processor::Engine;
use clap::Parser;
use clio::{ClioPath, InputPath, Output, OutputPath};
use owo_colors::OwoColorize;
use std::io::Read;
use std::path::Path;
use std::rc::Rc;

/// A simple preprocessor.
///
/// This is a simple preprocessor that can be used to preprocess files before
/// they are compiled. It is designed to be used in a pipeline.  As it is
/// designed to work with multiple languages, the default comment syntax is
/// `#`.  This can be changed with the `--comment` flag, or is auto-selected
/// based on the file extension.
///
/// The text is expected to be parsed as UTF-8.  If a line does not start with
/// the comment marker, the text is passed through (post substitution) to
/// the target file.  If a line starts with the comment marker, the line is
/// parsed as a directive.  Directives are of the form `#[name] [args]`.  (Note
/// the missing space between the name and the comment marker.)  The following
/// directives are supported:
///
/// - `#if <expr>`: If the expression evaluates to true, the following lines
///   are passed through.  Otherwise, they are ignored.
/// - `#elsif <expr>`: If all of the previous `#if` or `#elsif` evaluated to
///   false, and this expression evaluates to true, the following lines are
///   passed through.  Otherwise, they are ignored.
/// - `#else`: If all of the previous `#if` or `#elsif` evaluated to false,
///   the following lines are passed through.  Otherwise, they are ignored.
/// - `#endif`: Ends the previous `#if`, `#elsif`, or `#else` block.
/// - `#replace <name>`: Replaces all instances of `name` with the value of
///   the variable `name`.  If the variable is not defined, it is replaced
///   with the empty string.
/// - `#replace <name> <expr>`: Replaces all instances of `name` in the text
///   with the value of the expression `expr`.  If the expression cannot be
///   evaluated, it is replaced with the empty string.
/// - `#unrep <name>`: Stops substitution of `name` in the current scope.
/// - `#define <name> <expr>`: Defines the variable `name` to be the value
///   of the expression `expr`.  If the expression cannot be evaluated, the
///   variable is set to null.
/// - `#error <expr>`: Marks the current line as an error.  If the expression
///   cannot be evaluated, the error is marked as `null`.  This will cause
///   the preprocessor to exit with an error code, after processing the whole
///   file.
///
/// For certain expressions, you can continue them onto other lines; if this
/// happens, each successive line _must_ start with the directive prefix as
/// well, or it will be treated as a normal line.
///
/// Failure will result in an exit code of `2` if it is a result of a bad
/// input or a bad parameter.  Otherwise, the exit code will be `1`.
#[derive(clap::Parser, Debug)]
#[command(author, version, about, long_about)]
#[allow(clippy::struct_excessive_bools)]
struct Args {
    /// The input files.
    ///
    /// Each file is processed in order, and the output is written to the output.
    #[clap(value_parser)]
    inputs: Vec<InputPath>,
    /// The output file.
    ///
    /// Required if - and only if - there are multiple input files.  If there
    /// is only one input file and no output file is specified, the output is
    /// written to stdout.  Otherwise, if there is only one input file, then
    /// the output is written to the output file (unless `-d` is specified);
    /// if there is more than one input file, then the output is written to
    /// a file under the output directory with the same name as the input
    /// file.
    #[clap(short, long, value_parser)]
    output: Option<OutputPath>,
    /// Whether or not to interpret the output as a directory.
    ///
    /// If this is set, the output is interpreted as a directory, and the
    /// output file is placed underneath the directory with the same name as
    /// the input file.
    #[clap(short, long)]
    directory: bool,
    /// The comment marker.
    ///
    /// This is the marker that is used to indicate that a line is a directive.
    /// If not specified, it is auto-detected based on the file extension.
    /// If the file extension is not recognized, the default is `#`.
    #[clap(short, long)]
    comment: Option<String>,
    /// Definitions to use when processing the file.
    ///
    /// These are of the form `name=value`.  If the value is not specified,
    /// the variable is set to the empty string (_not_ null).  If the value
    /// is specified, it is treated as a string value.
    #[clap(short = 'D', long, value_delimiter = ';')]
    definitions: Vec<String>,
    /// Replacements to use when processing the file.
    ///
    /// These are of the form `name=value`.  If the value is not specified,
    /// the replacement acts as `#replace` would given no value - the name
    /// is parsed as an expression, and if it cannot be evaluated, it is
    /// replaced with the empty string.  If the value is specified, it is
    /// treated as a string value.
    #[clap(short = 'R', long, value_delimiter = ';')]
    replacements: Vec<String>,
    /// Whether or not to add the environment variables as definitions.
    ///
    /// If this is set, the environment variables are added as definitions
    /// before the file is processed.  This is not entirely recommended, as
    /// you can leak sensitive information this way.
    #[clap(long = "import-entire-environment")]
    import_entire_environment: bool,
    /// Whether or not to add the environment variables as replacements.
    ///
    /// If this is set, the environment variables are added as replacements
    /// before the file is processed.  This is not entirely recommended, as
    /// you can leak sensitive information this way.
    #[clap(long = "replace-entire-environment")]
    replace_entire_environment: bool,
    /// Import the given environment variables as definitions.
    ///
    /// This specifies which environmental variables are imported as a
    /// definition for access by the preprocessor.
    #[clap(short = 'e', long = "import-environment", value_delimiter = ';')]
    import_environment: Vec<String>,
    /// Import the given environment variables as replacements.
    ///
    /// This specifies which environmental variables are imported as a
    /// replacement for access by the preprocessor.
    #[clap(short = 'r', long = "replace-environment", value_delimiter = ';')]
    replace_environment: Vec<String>,
    /// Quiets errors.
    ///
    /// If this is set, errors are not printed to stderr.  This does not mean
    /// no errors are printed; errors that are arising from bad inputs or
    /// parameters will still be printed on stderr.  However, errors arising
    /// from a failure to parse or evaluate the file will not be printed.  The
    /// program will still exit with an error code, however.
    #[clap(short, long)]
    quiet: bool,
}

macro_rules! fatal {
    ($($arg:tt)*) => {
        eprintln!("{}: {}", "FATAL".red().bold(), format!($($arg)*));
        std::process::exit(2);
    }
}

macro_rules! warning {
    ($($arg:tt)*) => {
        eprintln!("{}: {}", "WARNING".yellow(), format!($($arg)*));
    }
}

mod processor;

#[allow(clippy::print_stderr)]
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = Args::parse();

    if args.inputs.is_empty() {
        args.inputs.push(InputPath::std());
    }

    let comment: Option<Rc<str>> = if let Some(comment) = &args.comment {
        if self::processor::is_bad_prefix(comment) {
            warning!("it is not a good idea to use '{}' as a comment marker, as it will conflate with expression tokens while parsing", comment);
        }

        Some(Rc::from(&**comment))
    } else {
        None
    };

    let mut output = OutputDirection::from(&args);
    let mut engine = Engine::new();
    let mut bad_exit = false;

    add_defines(&mut engine, &args);
    add_replacements(&mut engine, &args);

    for input in args.inputs {
        let mut content = String::new();
        let input_path = input.path().clone();
        input.open()?.read_to_string(&mut content)?;

        let mut local_output = output.for_input(&input_path)?;

        let comment_type = comment
            .clone()
            .unwrap_or_else(|| comment_type_for(input_path.path()));

        let tokenizer = self::processor::Tokenizer::new(&content, comment_type);
        let root = self::processor::parse(tokenizer);
        match root {
            Ok(root) => {
                let eval = engine.execute(root, &mut local_output)?;
                bad_exit |= !eval.errors.is_empty();
                if !args.quiet {
                    for error in eval.errors {
                        eprintln!("{error}", error = error.within_file(&input_path.display()));
                    }
                }
            }
            Err(errors) => {
                if !args.quiet {
                    for error in errors.errors {
                        eprintln!("{error}", error = error.within_file(&input_path.display()));
                    }
                }
            }
        }
    }

    if bad_exit {
        std::process::exit(1);
    }

    Ok(())
}

#[derive(Default)]
enum OutputDirection {
    #[default]
    Empty,
    Stdout(OutputPath),
    SingleFile(OutputPath),
    Directory(OutputPath),
}

impl OutputDirection {
    #[allow(clippy::print_stderr)]
    fn from(args: &Args) -> Self {
        let has_multiple_inputs = args.inputs.len() > 1;

        let output = args.output.clone().unwrap_or_else(OutputPath::std);

        if output.is_std() && (has_multiple_inputs || args.directory) {
            fatal!(
                "cannot output to stdout when there are multiple inputs or when -d is specified"
            );
        } else if has_multiple_inputs || args.directory {
            Self::Directory(output)
        } else if output.is_std() {
            Self::Stdout(output)
        } else {
            Self::SingleFile(output)
        }
    }

    fn for_input(&mut self, input: &Path) -> Result<Output, Box<dyn std::error::Error>> {
        match std::mem::take(self) {
            // We include this here as a sanity check; we always replace self
            // with `Empty` for stdout/singlefile to ensure that we don't
            // accidentally use it _again_.
            Self::Empty => unreachable!("output was somehow set to go to the same file?"),
            Self::Stdout(_) => Ok(Output::std()),
            Self::SingleFile(output) => output.create().map_err(Into::into),
            Self::Directory(output) => {
                let input = input.parent().map_or(input.as_ref(), |parent| {
                    input
                        .strip_prefix(parent)
                        .expect("input path is not a child of its parent")
                });
                assert!(input.is_relative());
                Output::new(ClioPath::local(output.path().join(input))).map_err(Into::into)
            }
        }
    }
}

static COMMENT_TYPE: phf::Map<&'static str, &'static str> = phf::phf_map! {
    "rs" => "//-",
    "c" => "//-",
    "cpp" => "//-",
    "h" => "//-",
    "hpp" => "//-",
    "sql" => "--!",
    "sh" => "#-",
    "bash" => "#-",
    "zsh" => "#-",
};

fn comment_type_for(path: &Path) -> Rc<str> {
    let extension = path.extension().and_then(std::ffi::OsStr::to_str);
    let extension = extension.unwrap_or("");

    COMMENT_TYPE
        .get(extension)
        .map_or_else(|| Rc::from("#"), |s| Rc::from(*s))
}

#[allow(clippy::print_stderr)]
fn add_defines(eval: &mut Engine, args: &Args) {
    eval.define_strings(args.definitions.iter().map(|s| {
        if let Some((before, after)) = s.split_once('=') {
            (before.to_owned(), after.to_owned())
        } else {
            fatal!("invalid definition {s}");
        }
    }));

    if args.import_entire_environment {
        eval.define_strings(std::env::vars());
    } else {
        eval.define_strings(
            args.import_environment
                .iter()
                .filter_map(|name| match std::env::var(name) {
                    Ok(value) => Some((name.clone(), value)),
                    Err(std::env::VarError::NotPresent) => {
                        warning!("environment variable {name} is not present");
                        None
                    }
                    Err(e) => {
                        fatal!("failed to import environment variable {name}: {e}");
                    }
                }),
        );
    }
}

#[allow(clippy::print_stderr)]
fn add_replacements(eval: &mut Engine, args: &Args) {
    eval.replace_strings(args.replacements.iter().map(|s| {
        if let Some((before, after)) = s.split_once('=') {
            (before.to_owned(), Some(after.to_owned()))
        } else {
            (s.clone(), None)
        }
    }));

    if args.replace_entire_environment {
        eval.replace_strings(std::env::vars().map(|(name, value)| (name, Some(value))));
    } else {
        eval.replace_strings(args.replace_environment.iter().filter_map(
            |name| match std::env::var(name) {
                Ok(value) => Some((name.clone(), Some(value))),
                Err(std::env::VarError::NotPresent) => {
                    warning!("environment variable {name} is not present");
                    None
                }
                Err(e) => {
                    fatal!("failed to import environment variable {name}: {e}");
                }
            },
        ));
    }
}
