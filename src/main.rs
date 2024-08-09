use chumsky::prelude::*;

#[derive(Debug, Copy, Clone)]
struct Register(usize);

#[derive(Debug, Copy, Clone)]
enum RegisterOrImmediate {
    Reg(Register),
    Imm(usize),
}

#[derive(Debug, Copy, Clone)]
struct BooleanRegister(usize);

#[derive(Debug, Copy, Clone)]
#[repr(u32)]
enum LogicOperation {
    And = 0,
    Or,
    Xor,
    Lshift,
    Rshift,
    Lrotate,
    Rrotate,
    Arithrshift,
}

#[derive(Debug, Copy, Clone)]
#[repr(u32)]
enum ArithmeticOperation {
    Add = 0,
    Sub,
}

#[derive(Debug, Copy, Clone)]
enum CompareOperation {
    Eq,
    Neq,
    Sgt,
    Slt,
    Sgte,
    Slte,
    Ugt,
    Ult,
    Ugte,
    Ulte,
}

#[derive(Debug, Copy, Clone)]
enum AssemblyInstruction {
    Mov {
        dst: Register,
        src: RegisterOrImmediate,
    },
    Logic {
        op: LogicOperation,
        dst: Register,
        a: Register,
        b: RegisterOrImmediate,
    },
    Arith {
        op: ArithmeticOperation,
        carry_out: BooleanRegister,
        carry_in: BooleanRegister,
        dst: Register,
        a: Register,
        b: RegisterOrImmediate,
    },
    Comp {
        op: CompareOperation,
        dst: BooleanRegister,
        a: Register,
        b: RegisterOrImmediate,
    },
}

fn translate_instruction(instruction: AssemblyInstruction) -> u32 {
    match instruction {
        AssemblyInstruction::Mov { dst, src } => {
            todo!()
        }
        AssemblyInstruction::Logic {
            op,
            dst,
            a,
            b: RegisterOrImmediate::Reg(b),
        } => {
            let opcode: u32 = 0b00000000 << 24;
            let optype: u32 = (op as u32) << 16;
            let dst_binary: u32 = (dst.0 as u32) << 12;
            let a_binary: u32 = (a.0 as u32) << 8;
            let b_binary: u32 = (b.0 as u32) << 4;
            opcode | optype | dst_binary | a_binary | b_binary
        }
        AssemblyInstruction::Logic {
            op,
            dst,
            a,
            b: RegisterOrImmediate::Imm(b),
        } => {
            todo!()
        }
        AssemblyInstruction::Arith {
            op,
            carry_out,
            carry_in,
            dst,
            a,
            b,
        } => {
            todo!()
        }
        AssemblyInstruction::Comp { op, dst, a, b } => {
            todo!()
        }
    }
}

fn parser() -> impl Parser<char, Vec<AssemblyInstruction>, Error = Simple<char>> {
    let register_parser = just('r')
        .ignore_then(text::int(10))
        .padded()
        .map(|s| Register(s.parse().unwrap()));

    let immediate_parser = text::int(10).padded().map(|s: String| s.parse().unwrap());

    let register_or_immediate_parser = register_parser
        .map(RegisterOrImmediate::Reg)
        .or(immediate_parser.map(RegisterOrImmediate::Imm));

    let boolean_register_parser = just('b')
        .ignore_then(text::int(10))
        .padded()
        .map(|s| BooleanRegister(s.parse().unwrap()));

    let mov_parser = text::keyword("mov")
        .padded()
        .ignore_then(register_parser)
        .then_ignore(just(','))
        .then(register_or_immediate_parser)
        .then_ignore(just(';').padded())
        .map(|(dst, src)| AssemblyInstruction::Mov { dst, src });

    let arith_parser = |keyword: &'static str, op: ArithmeticOperation| {
        text::keyword(keyword)
            .padded()
            .ignore_then(register_parser)
            .then_ignore(just(','))
            .then(register_parser)
            .then_ignore(just(','))
            .then(register_or_immediate_parser)
            .then_ignore(just(';').padded())
            .map(move |((dst, a), b)| AssemblyInstruction::Arith {
                op,
                carry_out: BooleanRegister(0),
                carry_in: BooleanRegister(0),
                dst,
                a,
                b,
            })
    };

    let arith_with_carry_parser = |keyword: &'static str, op: ArithmeticOperation| {
        text::keyword(keyword)
            .padded()
            .then_ignore(just('['))
            .ignore_then(boolean_register_parser)
            .then_ignore(just(','))
            .then(boolean_register_parser.or_not())
            .map(|(carry_out, carry_in)| (carry_out, carry_in.unwrap_or(carry_out)))
            .then_ignore(just(']'))
            .then(register_parser)
            .then_ignore(just(','))
            .then(register_parser)
            .then_ignore(just(','))
            .then(register_or_immediate_parser)
            .then_ignore(just(';').padded())
            .map(
                move |((((carry_out, carry_in), dst), a), b)| AssemblyInstruction::Arith {
                    op,
                    carry_out,
                    carry_in,
                    dst,
                    a,
                    b,
                },
            )
    };

    let logic_parser = |keyword: &'static str, op: LogicOperation| {
        text::keyword(keyword)
            .padded()
            .ignore_then(register_parser)
            .then_ignore(just(','))
            .then(register_parser)
            .then_ignore(just(','))
            .then(register_or_immediate_parser)
            .then_ignore(just(';').padded())
            .map(move |((dst, a), b)| AssemblyInstruction::Logic { op, dst, a, b })
    };

    let comp_parser = |keyword: &'static str, op: CompareOperation| {
        text::keyword(keyword)
            .padded()
            .ignore_then(boolean_register_parser)
            .then_ignore(just(','))
            .then(register_parser)
            .then_ignore(just(','))
            .then(register_or_immediate_parser)
            .then_ignore(just(';').padded())
            .map(move |((dst, a), b)| AssemblyInstruction::Comp { op, dst, a, b })
    };

    let instruction_parser = mov_parser
        .or(arith_parser("add", ArithmeticOperation::Add))
        .or(arith_parser("sub", ArithmeticOperation::Sub))
        .or(arith_with_carry_parser("adc", ArithmeticOperation::Add))
        .or(arith_with_carry_parser("sbb", ArithmeticOperation::Sub))
        .or(logic_parser("and", LogicOperation::And))
        .or(logic_parser("or", LogicOperation::Or))
        .or(logic_parser("xor", LogicOperation::Xor))
        .or(logic_parser("shl", LogicOperation::Lshift))
        .or(logic_parser("shr", LogicOperation::Rshift))
        .or(logic_parser("rotl", LogicOperation::Lrotate))
        .or(logic_parser("rotr", LogicOperation::Rrotate))
        .or(logic_parser("sar", LogicOperation::Arithrshift))
        .or(comp_parser("eq", CompareOperation::Eq))
        .or(comp_parser("neq", CompareOperation::Neq))
        .or(comp_parser("sgt", CompareOperation::Sgt))
        .or(comp_parser("sgte", CompareOperation::Sgte))
        .or(comp_parser("slt", CompareOperation::Slt))
        .or(comp_parser("slte", CompareOperation::Slte))
        .or(comp_parser("ugt", CompareOperation::Ugt))
        .or(comp_parser("ugte", CompareOperation::Ugte))
        .or(comp_parser("ult", CompareOperation::Ult))
        .or(comp_parser("ulte", CompareOperation::Ulte));

    instruction_parser.repeated()
}

fn main() -> Result<(), String> {
    let input_path = std::env::args()
        .nth(1)
        .ok_or_else(|| "No input file path provided")?;

    let output_path = std::env::args()
        .nth(2)
        .ok_or_else(|| "No output file path provided")?;

    let parser = parser();

    let input = std::fs::read_to_string(&input_path)
        .map_err(|_| format!("Could not read from file '{}'", &input_path))?;

    let instructions = parser
        .parse(&*input)
        .map_err(|e| format!("Could not parse code: {:?}", e))?;

    println!("{:?}", &instructions);

    Ok(())
}
