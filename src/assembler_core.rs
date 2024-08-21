#[derive(Debug, Copy, Clone, PartialEq, Eq)]
#[repr(u32)]
pub enum LogicOperation {
    And = 0,
    Or,
    Xor,
    Lshift,
    Rshift,
    Lrotate,
    Rrotate,
    Arithrshift,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
#[repr(u32)]
pub enum ArithmeticOperation {
    Add = 0,
    Sub,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
#[repr(u32)]
pub enum CompareOperation {
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

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Operation {
    Mov,
    Logic(LogicOperation),
    Arithmetic(ArithmeticOperation),
    ArithmeticCarry(ArithmeticOperation),
    Compare(CompareOperation),
}

#[derive(Debug, Copy, Clone)]
pub struct Register(pub usize);

#[derive(Debug, Copy, Clone)]
pub enum RegisterOrImmediate {
    Reg(Register),
    Imm(u32),
}

#[derive(Debug, Copy, Clone)]
pub struct BooleanRegister(pub usize);

#[derive(Debug, Clone)]
pub enum AssemblyInstruction {
    None,
    Error,
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
    Label {
        label: String,
    },
}

#[derive(Debug, Clone)]
pub enum DataElement {
    Label(String),
    Data1(u8),
    Data2(u16),
    Data4(u32),
    Data8(u64),
}

pub struct AssemblyProgram {
    pub instructions: Vec<AssemblyInstruction>,
    pub data: Vec<DataElement>,
}
