use std::{collections::HashMap, num::ParseIntError, ops::Range};

use chumsky::{prelude::*, Error};

use crate::assembler_core::*;

#[derive(Clone, Debug)]
pub enum Token {
    Error,

    Num(u64),
    Reg(usize),
    BoolReg(usize),
    Iden(String),
    Op(Operation),

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

#[derive(Clone, Debug)]
pub struct SpannedToken {
    span: Range<usize>,
    token: Token,
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
    InvalidIntegerLiteral(Range<usize>, IntegerLiteralType, ParseIntError),
}

impl Error<char> for LexerError {
    type Span = Range<usize>;

    type Label = ();

    fn expected_input_found<Iter: IntoIterator<Item = Option<char>>>(span: Self::Span, expected: Iter, found: Option<char>) -> Self {
        todo!()
    }

    fn with_label(self, label: Self::Label) -> Self {
        self
    }

    fn merge(self, other: Self) -> Self {
        self
    }
}

const OPERATIONS: &[(&'static str, Operation)] = &[
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

pub fn lexer<'a>() -> impl Parser<char, Vec<SpannedToken>, Error = LexerError> + 'a {
    let ops_map: HashMap<&'static str, Operation> = OPERATIONS.iter().copied().collect();

    let unsigned_literal_parser = text::int(10).padded().try_map(|s: String, span: Range<usize>| {
        s.parse::<u64>()
            .map(|number| Token::Num(number).spanned(span.clone()))
            .map_err(|parse_int_error| LexerError::InvalidIntegerLiteral(span.clone(), IntegerLiteralType::Unsigned, parse_int_error))
    });

    let signed_literal_parser = just('-').chain(text::int(10)).padded().try_map(|s: Vec<char>, span: Range<usize>| {
        s.into_iter()
            .collect::<String>()
            .parse::<i64>()
            .map(|number| Token::Num(number as u64).spanned(span.clone()))
            .map_err(|parse_int_error| LexerError::InvalidIntegerLiteral(span.clone(), IntegerLiteralType::Signed, parse_int_error))
    });

    let hex_literal_parser = just('0')
        .ignore_then(just('x'))
        .ignore_then(text::int(16))
        .try_map(|s: String, span: Range<usize>| {
            u64::from_str_radix(&s, 16)
                .map(|number| Token::Num(number as u64).spanned(span.clone()))
                .map_err(|parse_int_error| LexerError::InvalidIntegerLiteral(span.clone(), IntegerLiteralType::Hex, parse_int_error))
        });

    let binary_literal_parser = just('0')
        .ignore_then(just('b'))
        .ignore_then(text::int(2))
        .try_map(|s: String, span: Range<usize>| {
            u64::from_str_radix(&s, 2)
                .map(|number| Token::Num(number as u64).spanned(span.clone()))
                .map_err(|parse_int_error| LexerError::InvalidIntegerLiteral(span.clone(), IntegerLiteralType::Binary, parse_int_error))
        });

    let register_parser = just('r').ignore_then(text::int(10)).try_map(|s: String, span: Range<usize>| {
        s.parse::<usize>()
            .map(|number| Token::Reg(number).spanned(span.clone()))
            .map_err(|_| LexerError::Internal(span.clone()))
    });

    let boolean_register_parser = just('b').ignore_then(text::int(10)).try_map(|s: String, span: Range<usize>| {
        s.parse::<usize>()
            .map(|number| Token::BoolReg(number).spanned(span.clone()))
            .map_err(|_| LexerError::Internal(span.clone()))
    });

    let iden_parser = text::ident().try_map(move |iden: String, span: Range<usize>| {
        Ok(ops_map
            .get(&(&iden[..]))
            .copied()
            .map(Token::Op)
            .unwrap_or(Token::Iden(iden))
            .spanned(span))
    });

    let symbol_parser = select! {|span|
        '[' => Token::Lsqr.spanned(span),
        ']' => Token::Rsqr.spanned(span),
        ',' => Token::Comma.spanned(span),
        ';' => Token::SemiColon.spanned(span),
    };

    let token_parser = unsigned_literal_parser
        .or(signed_literal_parser)
        .or(hex_literal_parser)
        .or(binary_literal_parser)
        .or(register_parser)
        .or(boolean_register_parser)
        .or(iden_parser)
        .or(symbol_parser);

    let comment_parser = just('/')
        .then_ignore(just('/'))
        .then_ignore(text::newline().or(end()).not().repeated())
        .then_ignore(text::newline().or(end()))
        .to(None);

    let block_comment_parser = just('/')
        .then_ignore(just('*'))
        .then_ignore(just('*').ignore_then(just('/')).not().repeated())
        .then_ignore(just('*').ignore_then(just('/')))
        .to(None);

    token_parser
        .map(Some)
        .or(comment_parser)
        .or(block_comment_parser)
        .repeated()
        .map(|optional_tokens| optional_tokens.into_iter().flatten().collect())
}
