use ariadne::{Color, Label, Report, ReportKind, Source};
use chumsky::{
    prelude::{Input, Rich},
    Parser,
};

pub mod ast;
pub mod hoas;
pub mod parser;

/// Parses a string into an [`ProofFile`].
///
/// [`ProofFile`]: [`ProofFile`]
pub fn parse(source: &str) -> ast::ProofFile {
    let filename = "terminal";

    let (tokens, lex_errors) = parser::lexer().parse(source).into_output_errors();
    let tokens = tokens.unwrap_or_default();
    let tokens = tokens
        .into_iter()
        .map(|span| (span.data, span.span))
        .collect::<Vec<_>>();
    let tokens = tokens
        .as_slice()
        .spanned((source.len()..source.len()).into());
    let (proof_file, errors) = parser::parser().parse(tokens).into_output_errors();

    // If there are no errors, return the parsed expression.
    if !errors.is_empty() || !lex_errors.is_empty() {
        // Combine the errors from the lexer and the parser.
        //
        // The lexer errors are converted to strings, and the
        // parser errors are converted to strings and the tokens
        // are converted to strings.

        report_ariadne_errors(
            filename,
            source,
            errors
                .into_iter()
                .map(|error| error.map_token(|c| c.to_string()))
                .chain(
                    lex_errors
                        .into_iter()
                        .map(|error| error.map_token(|token| token.to_string())),
                )
                .collect::<Vec<_>>(),
        );
    }

    // If the expression is not present, we return an error sentinel
    // value to avoid crashing.
    proof_file.unwrap_or_else(|| ast::ProofFile { statements: vec![] })
}

/// Reports the errors from the [`parse`] function.
///
/// [`parse`]: [`parse`]
pub fn report_ariadne_errors(filename: &str, source: &str, errors: Vec<Rich<'_, String>>) {
    type AriadneSpan = (String, std::ops::Range<usize>);

    // Defines the filename of the source. And it is used to
    // create the report.
    let filename: String = filename.into();

    for error in errors {
        Report::<AriadneSpan>::build(ReportKind::Error, filename.clone(), 0)
            .with_code(1)
            .with_message(error.to_string())
            .with_label(
                Label::new((filename.clone(), error.span().into_range()))
                    .with_message(error.reason().to_string())
                    .with_color(Color::Red),
            )
            .with_labels(error.contexts().map(|(label, span)| {
                Label::new((filename.clone(), span.into_range()))
                    .with_message(format!("in the context {}", label))
                    .with_color(Color::Yellow)
            }))
            .finish()
            .eprint((filename.to_string(), Source::from(source.to_string())))
            .unwrap();
    }
}

/// Parses a file into an [`ProofFile`].
pub fn unlines<const N: usize>(lines: [&str; N]) -> ast::ProofFile {
    let mut src = String::new();

    for line in lines {
        src.push_str(line);
        src.push('\n');
    }

    parse(&src)
}

fn main() {
    let ast = unlines([
        "// simple file",
        "data Bool : Type where",
        "  True  : Bool",
        ", False : Bool",
        "",
        "fun and : Bool -> Bool -> Bool",
        "        | True, True   = True",
        "        | _,    False  = False",
        "        | _,    _      = False",
        "        ;",
        "",
        "and True False;",
    ]);

    println!("{ast:#?}");
}
