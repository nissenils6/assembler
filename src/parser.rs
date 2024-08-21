/*
data {
label:
    u32 415;
    u16 78;
}

*/

use std::ops::Range;

use ariadne::{Color, Label, Report, ReportKind, Source};
use chumsky::{prelude::*, Error};

use crate::{
    lexer::{SpannedToken, Token},
    AssemblyInstruction, BooleanRegister, DataElement, Operation, Register, RegisterOrImmediate,
};

#[derive(Clone, Debug)]
pub enum ParserError {
    Internal(Range<usize>),
    ExpectedFound(Range<usize>, Vec<Option<char>>, Option<char>),
}

impl ParserError {
    pub fn print(&self, input_path: &str, source: &str) {
        match self {
            ParserError::Internal(span) => Report::build(ReportKind::Error, input_path, span.start)
                .with_code(0)
                .with_message("Internal Error, this should not appear")
                .with_label(Label::new((input_path, span.clone())).with_message("Here").with_color(Color::Red))
                .finish()
                .print((input_path, Source::from(source)))
                .unwrap(),
            ParserError::ExpectedFound(span, expected, found) => Report::build(ReportKind::Error, input_path, span.start)
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
        }
    }
}

impl Error<char> for ParserError {
    type Span = Range<usize>;

    type Label = ();

    fn expected_input_found<Iter: IntoIterator<Item = Option<char>>>(span: Self::Span, expected: Iter, found: Option<char>) -> Self {
        ParserError::ExpectedFound(span, expected.into_iter().collect(), found)
    }

    fn with_label(self, label: Self::Label) -> Self {
        self
    }

    fn merge(self, other: Self) -> Self {
        match (self, other) {
            (ParserError::ExpectedFound(span0, mut expected0, found0), ParserError::ExpectedFound(span1, expected1, found1)) => {
                assert_eq!(span0, span1);
                assert_eq!(found0, found1);
                expected0.extend(expected1.into_iter());
                ParserError::ExpectedFound(span0, expected0, found0)
            }
            (e0, e1) => e0,
        }
    }
}

pub fn parser() -> impl Parser<SpannedToken, AssemblyInstruction, Error = ParserError> {
    let token = |t| {
        select! {
            SpannedToken {span, token} if token == t => (),
        }
    };

    let register = select! {
        SpannedToken {span, token: Token::Reg(r)} => Register(r),
    };

    let boolean_register = select! {
        SpannedToken {span, token: Token::BoolReg(r)} => BooleanRegister(r),
    };

    let immediate = select! {
        SpannedToken {span, token: Token::Num(n)} => n,
    };

    let register_or_immediate = register
        .map(RegisterOrImmediate::Reg)
        .or(immediate.map(|n| n as u32).map(RegisterOrImmediate::Imm));

    let mov_isntruction = token(Token::Op(Operation::Mov))
        .ignore_then(register)
        .then_ignore(token(Token::Comma))
        .then(register_or_immediate)
        .map(|(dst, src)| AssemblyInstruction::Mov { dst, src });

    let logic_instruction = select! {
        SpannedToken {span, token: Token::Op(Operation::Logic(logic_operation))} => logic_operation,
    }
    .then(register)
    .then_ignore(token(Token::Comma))
    .then(register)
    .then_ignore(token(Token::Comma))
    .then(register_or_immediate)
    .map(|(((op, dst), a), b)| AssemblyInstruction::Logic { op, dst, a, b });

    let arithmetic_instruction = select! {
        SpannedToken {span, token: Token::Op(Operation::Arithmetic(arithmetic_operation))} => arithmetic_operation,
    }
    .then(register)
    .then_ignore(token(Token::Comma))
    .then(register)
    .then_ignore(token(Token::Comma))
    .then(register_or_immediate)
    .map(|(((op, dst), a), b)| AssemblyInstruction::Arith {
        op,
        carry_out: BooleanRegister(0),
        carry_in: BooleanRegister(0),
        dst,
        a,
        b,
    });

    let arithmetic_carry_instruction = select! {
        SpannedToken {span, token: Token::Op(Operation::ArithmeticCarry(arithmetic_operation))} => arithmetic_operation,
    }
    .then(
        token(Token::Lsqr)
            .ignore_then(boolean_register)
            .then(token(Token::Comma).ignore_then(boolean_register).or_not())
            .then_ignore(token(Token::Rsqr))
            .map(|(carry_out, carry_in)| (carry_out, carry_in.unwrap_or(carry_out))),
    )
    .then(register)
    .then_ignore(token(Token::Comma))
    .then(register)
    .then_ignore(token(Token::Comma))
    .then(register_or_immediate)
    .map(|((((op, (carry_out, carry_in)), dst), a), b)| AssemblyInstruction::Arith {
        op,
        carry_out,
        carry_in,
        dst,
        a,
        b,
    });

    let compare_instruction = select! {
        SpannedToken {span, token: Token::Op(Operation::Compare(compare_operation))} => compare_operation,
    }
    .then(boolean_register)
    .then_ignore(token(Token::Comma))
    .then(register)
    .then_ignore(token(Token::Comma))
    .then(register_or_immediate)
    .map(|(((op, dst), a), b)| AssemblyInstruction::Comp { op, dst, a, b });

    just::<_, _, ParserError>(end()).to((Vec::new(), Vec::new()))
}
