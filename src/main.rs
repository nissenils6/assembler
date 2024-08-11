use chumsky::prelude::*;

#[derive(Debug, Copy, Clone)]
struct Register(usize);

#[derive(Debug, Copy, Clone)]
enum RegisterOrImmediate {
    Reg(Register),
    Imm(u32),
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
#[repr(u32)]
enum CompareOperation {
    // Special
    // Greater/Less
    // Ignore/Equal
    // Signed/Unsigned
    Sgt = 0b0000,
    Ugt = 0b0001,
    Sgte = 0b0010,
    Ugte = 0b0011,
    Slt = 0b0100,
    Ult = 0b0101,
    Slte = 0b0110,
    Ulte = 0b0111,
    Eq = 0b1000,
    Neq = 0b1001,
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
    Disp {
        display: u32,
        src: RegisterOrImmediate,
    },
}

fn validate_immediate(imm: u32) -> (u32, u32) {
    let b_imm: u32 = (imm & 0xFF) << 0;

    let extend = if (imm & 0xFFFFFF00) == 0xFFFFFF00 {
        (1 as u32) << 19
    } else if (imm & 0xFFFFFF00) == 0 {
        (0 as u32) << 19
    } else {
        panic!("Invalid Immediate")
    };

    (b_imm, extend)
}

fn validate_double_immediate(imm: u32) -> (u32, u32) {
    let b_imm: u32 = (imm & 0xFFFF) << 0;

    let extend = if (imm & 0xFFFF0000) == 0xFFFF0000 {
        (1 as u32) << 19
    } else if (imm & 0xFFFF0000) == 0 {
        (0 as u32) << 19
    } else {
        panic!("Invalid Double Immediate")
    };

    (b_imm, extend)
}

fn translate_instruction(instruction: AssemblyInstruction) -> u32 {
    match instruction {
        AssemblyInstruction::Mov {
            dst,
            src: RegisterOrImmediate::Reg(src),
        } => {
            // Logic Operation: 00000000 00000TTT DDDDAAAA BBBB0000
            let opcode: u32 = 0b00000000 << 24;
            let optype: u32 = (LogicOperation::Or as u32) << 16;
            let dst_reg: u32 = (dst.0 as u32) << 12;
            let a_reg: u32 = (Register(0).0 as u32) << 8;
            let b_reg: u32 = (src.0 as u32) << 4;
            opcode | optype | dst_reg | a_reg | b_reg
        }
        AssemblyInstruction::Mov {
            dst,
            src: RegisterOrImmediate::Imm(src),
        } => {
            // Logic Operation With Immediate: 00000001 0000ETTT DDDDAAAA IIIIIIII
            let opcode: u32 = 0b00000001 << 24;
            let optype: u32 = (LogicOperation::Or as u32) << 16;
            let dst_reg: u32 = (dst.0 as u32) << 12;
            let a_reg: u32 = (Register(0).0 as u32) << 8;

            let (b_imm, extend) = validate_immediate(src);

            opcode | extend | optype | dst_reg | a_reg | b_imm
        }
        AssemblyInstruction::Logic {
            op,
            dst,
            a,
            b: RegisterOrImmediate::Reg(b),
        } => {
            // Logic Operation: 00000000 00000TTT DDDDAAAA BBBB0000
            let opcode: u32 = 0b00000000 << 24;
            let optype: u32 = (op as u32) << 16;
            let dst_reg: u32 = (dst.0 as u32) << 12;
            let a_reg: u32 = (a.0 as u32) << 8;
            let b_reg: u32 = (b.0 as u32) << 4;

            opcode | optype | dst_reg | a_reg | b_reg
        }
        AssemblyInstruction::Logic {
            op,
            dst,
            a,
            b: RegisterOrImmediate::Imm(b),
        } => {
            // Logic Operation With Immediate: 00000001 0000ETTT DDDDAAAA IIIIIIII
            let opcode: u32 = 0b00000001 << 24;
            let optype: u32 = (op as u32) << 16;
            let dst_reg: u32 = (dst.0 as u32) << 12;
            let a_reg: u32 = (a.0 as u32) << 8;

            let (b_imm, extend) = validate_immediate(b);

            opcode | extend | optype | dst_reg | a_reg | b_imm
        }
        AssemblyInstruction::Arith {
            op,
            carry_out,
            carry_in,
            dst,
            a,
            b: RegisterOrImmediate::Reg(b),
        } => {
            // Arithmetic Operation: 00000010 PPQQ000T DDDDAAAA BBBB0000
            let opcode: u32 = 0b00000010 << 24;
            let carry_out: u32 = (carry_out.0 as u32) << 22;
            let carry_in: u32 = (carry_in.0 as u32) << 20;
            let optype: u32 = (op as u32) << 16;
            let dst_reg: u32 = (dst.0 as u32) << 12;
            let a_reg: u32 = (a.0 as u32) << 8;
            let b_reg: u32 = (b.0 as u32) << 4;

            opcode | carry_out | carry_in | optype | dst_reg | a_reg | b_reg
        }
        AssemblyInstruction::Arith {
            op,
            carry_out,
            carry_in,
            dst,
            a,
            b: RegisterOrImmediate::Imm(b),
        } => {
            // Arithmetic Operation With Immediate: 00000011 PPQQE00T DDDDAAAA IIIIIIII
            let opcode: u32 = 0b00000011 << 24;
            let carry_out: u32 = (carry_out.0 as u32) << 22;
            let carry_in: u32 = (carry_in.0 as u32) << 20;
            let optype: u32 = (op as u32) << 16;
            let dst_reg: u32 = (dst.0 as u32) << 12;
            let a_reg: u32 = (a.0 as u32) << 8;

            let (b_imm, extend) = validate_immediate(b);

            opcode | carry_out | carry_in | extend | optype | dst_reg | a_reg | b_imm
        }
        AssemblyInstruction::Comp {
            op,
            dst,
            a,
            b: RegisterOrImmediate::Reg(b),
        } => {
            // Compare Operation: 00000100 PP000000 TTTTAAAA BBBB0000

            // y = type % 4
            // t = type - type % 4
            // XX00XX
            let opcode: u32 = 0b00000100 << 24;
            let dst_reg: u32 = (dst.0 as u32) << 22;
            let optype: u32 = (op as u32) << 12;
            let a_reg: u32 = (a.0 as u32) << 8;
            let b_reg: u32 = (b.0 as u32) << 4;

            opcode | dst_reg | optype | a_reg | b_reg
        }
        AssemblyInstruction::Comp {
            op,
            dst,
            a,
            b: RegisterOrImmediate::Imm(b),
        } => {
            // Compare Operation With Immediate: 00000101 PP00E000 TTTTAAAA IIIIIIII

            // y = type % 4
            // t = type - type % 4
            // XX00XX
            let opcode: u32 = 0b00000101 << 24;
            let dst_reg: u32 = (dst.0 as u32) << 22;
            let optype: u32 = (op as u32) << 12;
            let a_reg: u32 = (a.0 as u32) << 8;

            let (b_imm, extend) = validate_immediate(b);

            opcode | dst_reg | optype | extend | a_reg | b_imm
        }
        AssemblyInstruction::Disp {
            display,
            src: RegisterOrImmediate::Reg(src),
        } => {
            // Display: 11111110 000000TT 00000000 BBBB0000
            assert!(display <= 3, "Invalid display index");

            let opcode: u32 = 0b11111110 << 24;
            let display: u32 = display << 16;
            let src: u32 = (src.0 as u32) << 4;

            opcode | display | src
        }
        AssemblyInstruction::Disp {
            display,
            src: RegisterOrImmediate::Imm(src),
        } => {
            // Display With Immediate: 11111111 0000E0TT JJJJJJJJ JJJJJJJJ
            assert!(display <= 3, "Invalid display index");

            let opcode: u32 = 0b11111111 << 24;
            let display: u32 = display << 16;
            let (src, extend) = validate_double_immediate(src);

            opcode | extend | display | src
        }
    }
}

fn parser() -> impl Parser<char, Vec<AssemblyInstruction>, Error = Simple<char>> {
    let register_parser = just('r')
        .ignore_then(text::int(10))
        .padded()
        .map(|s| Register(s.parse().unwrap()));

    let immediate_parser = text::int(10).padded().map(|s: String| s.parse().unwrap());

    let negative_immediate_parser = just('-').chain(text::int(10)).padded().map(|s: Vec<char>| {
        s.iter()
            .copied()
            .collect::<String>()
            .parse::<i32>()
            .unwrap() as u32
    });

    let register_or_immediate_parser = register_parser
        .map(RegisterOrImmediate::Reg)
        .or(immediate_parser.map(RegisterOrImmediate::Imm))
        .or(negative_immediate_parser.map(RegisterOrImmediate::Imm));

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

    let disp_parser = text::keyword("disp")
        .padded()
        .ignore_then(immediate_parser)
        .then_ignore(just(','))
        .then(register_or_immediate_parser)
        .then_ignore(just(';').padded())
        .map(move |(display, src)| AssemblyInstruction::Disp { display, src });

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
        .or(comp_parser("ulte", CompareOperation::Ulte))
        .or(disp_parser);

    instruction_parser.repeated()
}

fn main() -> Result<(), String> {
    let input_path = std::env::args()
        .nth(1)
        .ok_or_else(|| "No input file path provided.")?;

    let output_path = std::env::args()
        .nth(2)
        .ok_or_else(|| "No output file path provided.")?;

    let parser = parser();

    let input = std::fs::read_to_string(&input_path)
        .map_err(|_| format!("Could not read from file '{}'.", &input_path))?;

    let instructions = parser
        .parse(&*input)
        .map_err(|e| format!("Could not parse code: {:?}", e))?;

    /*
    File Header:
     - Program Size
     - Program Location
     - Start Location
     - Stack Location
         */

    let mut output = vec![instructions.len() as u32, 0, 0, 0];
    output.extend(instructions.iter().copied().map(translate_instruction));

    std::fs::write(
        &output_path,
        &output
            .iter()
            .copied()
            .flat_map(|n| n.to_le_bytes())
            .collect::<Vec<_>>(),
    )
    .map_err(|_| format!("Could not write to file '{}'.", &output_path))?;

    println!("Assembling successful! Generated file '{}'.", output_path);

    Ok(())
}
