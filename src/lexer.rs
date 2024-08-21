use std::{
    collections::HashMap,
    num::{IntErrorKind, ParseIntError},
    ops::Range,
};

use ariadne::{Color, Fmt, Label, Report, ReportKind, Source};
use chumsky::{prelude::*, Error};

use crate::assembler_core::*;

#[derive(Clone, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum DataWidth {
    Bytes1 = 1,
    Bytes2 = 2,
    Bytes4 = 4,
    Bytes8 = 8,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Token {
    Error,

    Num(u64),
    Reg(usize),
    BoolReg(usize),
    Iden(String),
    Op(Operation),
    UnsignedType(DataWidth),
    SignedType(DataWidth),
    Code,
    Data,

    Lsqr,
    Rsqr,
    Comma,
    SemiColon,
}

impl Token {
    pub fn spanned(self, span: Range<usize>) -> SpannedToken {
        SpannedToken { span, token: self }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpannedToken {
    pub span: Range<usize>,
    pub token: Token,
}

#[derive(Clone, Debug)]
pub enum IntegerLiteralType {
    Unsigned,
    Signed,
    Hex,
    Binary,
}

#[derive(Clone, Debug)]
pub enum LexerError {
    Internal(Range<usize>),
    ExpectedFound(Range<usize>, Vec<Option<char>>, Option<char>),
    InvalidCharacter(Range<usize>, char),
    InvalidIntegerLiteral(Range<usize>, IntegerLiteralType, ParseIntError),
}

impl LexerError {
    pub fn print(&self, input_path: &str, source: &str) {
        match self {
            LexerError::Internal(span) => Report::build(ReportKind::Error, input_path, span.start)
                .with_code(0)
                .with_message("Internal Error, this should not appear")
                .with_label(Label::new((input_path, span.clone())).with_message("Here").with_color(Color::Red))
                .finish()
                .print((input_path, Source::from(source)))
                .unwrap(),
            LexerError::ExpectedFound(span, expected, found) => Report::build(ReportKind::Error, input_path, span.start)
                .with_code(1)
                .with_message(format!(
                    "Expected {}, found {}",
                    expected
                        .iter()
                        .copied()
                        .map(|c| c.map(|c| format!("'{}'", c)).unwrap_or("EOF".into()))
                        .collect::<Vec<String>>()
                        .join(", "),
                    found.map(|c| format!("'{}'", c)).unwrap_or("EOF".into()),
                ))
                .with_label(Label::new((input_path, span.clone())).with_message("Here").with_color(Color::Red))
                .finish()
                .print((input_path, Source::from(source)))
                .unwrap(),
            LexerError::InvalidCharacter(span, character) => Report::build(ReportKind::Error, input_path, span.start)
                .with_code(1)
                .with_message(format!("Expected token, found '{}'", character))
                .with_label(Label::new((input_path, span.clone())).with_message("Here").with_color(Color::Red))
                .finish()
                .print((input_path, Source::from(source)))
                .unwrap(),
            LexerError::InvalidIntegerLiteral(span, integer_literal_type, parse_int_error) => {
                Report::build(ReportKind::Error, input_path, span.start)
                    .with_code(2)
                    .with_message(format!(
                        "Invalid {}",
                        match integer_literal_type {
                            IntegerLiteralType::Unsigned => "integer literal",
                            IntegerLiteralType::Signed => "integer literal",
                            IntegerLiteralType::Hex => "hexadecimal integer literal",
                            IntegerLiteralType::Binary => "binary integer literal",
                        }
                    ))
                    .with_label(
                        Label::new((input_path, span.clone()))
                            .with_message(format!(
                                "This literal {}",
                                match parse_int_error.kind() {
                                    IntErrorKind::PosOverflow => "positively overflows".fg(Color::Red),
                                    IntErrorKind::NegOverflow => "negatively overflows".fg(Color::Red),
                                    IntErrorKind::InvalidDigit => "has invalid digits".fg(Color::Red),
                                    _ => unreachable!(),
                                }
                            ))
                            .with_color(Color::Red),
                    )
                    .finish()
                    .print((input_path, Source::from(source)))
                    .unwrap()
            }

            _ => {}
        }
    }
}

impl Error<char> for LexerError {
    type Span = Range<usize>;

    type Label = ();

    fn expected_input_found<Iter: IntoIterator<Item = Option<char>>>(span: Self::Span, expected: Iter, found: Option<char>) -> Self {
        LexerError::ExpectedFound(span, expected.into_iter().collect(), found)
    }

    fn with_label(self, label: Self::Label) -> Self {
        self
    }

    fn merge(self, other: Self) -> Self {
        match (self, other) {
            (LexerError::ExpectedFound(span0, mut expected0, found0), LexerError::ExpectedFound(span1, expected1, found1)) => {
                assert_eq!(span0, span1);
                assert_eq!(found0, found1);
                expected0.extend(expected1.into_iter());
                LexerError::ExpectedFound(span0, expected0, found0)
            }
            (e0, e1) => e0,
        }
    }
}

const OPERATIONS: &[(&'static str, Operation)] = &[
    ("mov", Operation::Mov),
    ("and", Operation::Logic(LogicOperation::And)),
    ("or", Operation::Logic(LogicOperation::Or)),
    ("xor", Operation::Logic(LogicOperation::Xor)),
    ("shl", Operation::Logic(LogicOperation::Lshift)),
    ("shr", Operation::Logic(LogicOperation::Rshift)),
    ("rotl", Operation::Logic(LogicOperation::Lrotate)),
    ("rotr", Operation::Logic(LogicOperation::Rrotate)),
    ("sar", Operation::Logic(LogicOperation::Arithrshift)),
    ("add", Operation::Arithmetic(ArithmeticOperation::Add)),
    ("sub", Operation::Arithmetic(ArithmeticOperation::Sub)),
    ("adc", Operation::ArithmeticCarry(ArithmeticOperation::Add)),
    ("sbb", Operation::ArithmeticCarry(ArithmeticOperation::Sub)),
    ("eq", Operation::Compare(CompareOperation::Eq)),
    ("neq", Operation::Compare(CompareOperation::Neq)),
    ("sgt", Operation::Compare(CompareOperation::Sgt)),
    ("sgte", Operation::Compare(CompareOperation::Sgte)),
    ("slt", Operation::Compare(CompareOperation::Slt)),
    ("slte", Operation::Compare(CompareOperation::Slte)),
    ("ugt", Operation::Compare(CompareOperation::Ugt)),
    ("ugte", Operation::Compare(CompareOperation::Ugte)),
    ("ult", Operation::Compare(CompareOperation::Ult)),
    ("ulte", Operation::Compare(CompareOperation::Ulte)),
];

pub fn lexer() -> impl Parser<char, Vec<SpannedToken>, Error = LexerError> {
    let special_identififers: HashMap<String, Token> = OPERATIONS
        .iter()
        .copied()
        .map(|(name, op)| (name.into(), Token::Op(op)))
        .chain((0..16).map(|i| (format!("r{}", i), Token::Reg(i))))
        .chain((0..4).map(|i| (format!("b{}", i), Token::BoolReg(i))))
        .chain(std::iter::once(("rsp".into(), Token::Reg(15))))
        .collect();

    let main_token_parser = filter::<char, _, LexerError>(|c| c.is_alphanumeric() || *c == '_')
        .repeated()
        .at_least(1)
        .try_map(move |s: Vec<char>, span: Range<usize>| {
            if s[0] == '0' {
                match s.get(1) {
                    Some('b') => u64::from_str_radix(&s.iter().copied().skip(2).collect::<String>(), 2)
                        .map(|number| Token::Num(number).spanned(span.clone()))
                        .map_err(|parse_int_error| LexerError::InvalidIntegerLiteral(span, IntegerLiteralType::Binary, parse_int_error)),
                    Some('x') => u64::from_str_radix(&s.iter().copied().skip(2).collect::<String>(), 16)
                        .map(|number| Token::Num(number).spanned(span.clone()))
                        .map_err(|parse_int_error| LexerError::InvalidIntegerLiteral(span, IntegerLiteralType::Hex, parse_int_error)),
                    Some(&found) => Err(LexerError::ExpectedFound(
                        (span.start + 1)..(span.start + 2),
                        vec![Some('b'), Some('x')],
                        Some(found),
                    )),
                    None => Ok(Token::Num(0).spanned(span)),
                }
            } else if s[0].is_numeric() {
                s.iter()
                    .copied()
                    .collect::<String>()
                    .parse()
                    .map(|number| Token::Num(number).spanned(span.clone()))
                    .map_err(|parse_int_error| LexerError::InvalidIntegerLiteral(span, IntegerLiteralType::Unsigned, parse_int_error))
            } else {
                let string = s.iter().copied().collect::<String>();
                if let Some(token) = special_identififers.get(&string) {
                    Ok(token.clone().spanned(span))
                } else {
                    Ok(Token::Iden(string).spanned(span))
                }
            }
        })
        .recover_with(skip_parser(
            filter::<char, _, LexerError>(|c| c.is_alphanumeric() || *c == '_')
                .repeated()
                .at_least(1)
                .to(())
                .or(any().to(()))
                .try_map(|_, span| Ok(Token::Error.spanned(span))),
        ));

    let symbol_parser = select! {|span|
        '[' => Token::Lsqr.spanned(span),
        ']' => Token::Rsqr.spanned(span),
        ',' => Token::Comma.spanned(span),
        ';' => Token::SemiColon.spanned(span),
    };

    let single_comment_parser = just('/')
        .then_ignore(just('/'))
        .then_ignore(text::newline().or(end()).not().repeated())
        .then_ignore(text::newline().or(end()));

    let multiple_comment_parser = just('/')
        .then_ignore(just('*'))
        .then_ignore(just('*').ignore_then(just('/')).not().repeated())
        .then_ignore(just('*').ignore_then(just('/')));

    main_token_parser
        .or(symbol_parser)
        .or(any()
            .try_map(|c, span| Err(LexerError::InvalidCharacter(span, c)))
            .recover_with(skip_parser(any().try_map(|_, span| Ok(Token::Error.spanned(span))))))
        .padded()
        .padded_by(single_comment_parser.or(multiple_comment_parser).padded().repeated())
        .repeated()
        .then_ignore(end())
        .map(|optional_tokens| optional_tokens.into_iter().collect())
}
