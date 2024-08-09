use std::time::Instant;

use chumsky::prelude::*;
use smallvec::SmallVec;

type InstructionData = SmallVec<[u8; 24]>;

fn unsigned_list<'a, const N: usize>(
    keyword: &'a str,
    mapper: fn(u64) -> [u8; N],
) -> impl Parser<char, InstructionData, Error = Simple<char>> + 'a {
    let number = just('0')
        .ignore_then(
            just('x')
                .ignore_then(text::int(16))
                .map(|s: String| u64::from_str_radix(&s, 16).unwrap())
                .or(just('b')
                    .ignore_then(text::int(2))
                    .map(|s: String| u64::from_str_radix(&s, 2).unwrap())),
        )
        .or(text::int(10).map(|s: String| s.parse::<u64>().unwrap()))
        .padded();

    text::keyword(keyword)
        .ignore_then(
            number
                .map(mapper)
                .separated_by(just(',').padded())
                .map(|v| v.iter().flatten().copied().collect()),
        )
        .then_ignore(just(';'))
}

fn signed_list<'a, const N: usize>(
    keyword: &'a str,
    mapper: fn(i64) -> [u8; N],
) -> impl Parser<char, InstructionData, Error = Simple<char>> + 'a {
    let signed_number = filter::<_, _, Simple<char>>(|c: &char| c.is_ascii_digit() || *c == '-')
        .repeated()
        .map(|s: Vec<char>| s.into_iter().collect::<String>().parse::<i64>().unwrap())
        .padded();

    text::keyword(keyword)
        .ignore_then(
            signed_number
                .map(mapper)
                .separated_by(just(',').padded())
                .map(|v| v.iter().flatten().copied().collect()),
        )
        .then_ignore(just(';'))
}

fn parser() -> impl Parser<char, Vec<u8>, Error = Simple<char>> {
    let instruction_parser = unsigned_list("u8", |n| (n as u8).to_le_bytes())
        .or(unsigned_list("u16", |n| (n as u16).to_le_bytes()))
        .or(unsigned_list("u32", |n| (n as u32).to_le_bytes()))
        .or(unsigned_list("u64", |n| (n as u64).to_le_bytes()))
        .or(signed_list("i8", |n| (n as i8).to_le_bytes()))
        .or(signed_list("i16", |n| (n as i16).to_le_bytes()))
        .or(signed_list("i32", |n| (n as i32).to_le_bytes()))
        .or(signed_list("i64", |n| (n as i64).to_le_bytes()));

    instruction_parser
        .padded()
        .repeated()
        .map(|v: Vec<InstructionData>| v.iter().flatten().copied().collect())
        .then_ignore(end())
}

fn main() -> Result<(), String> {
    let start = Instant::now();

    let input_path = std::env::args()
        .nth(1)
        .ok_or_else(|| "No input file path provided")?;

    let output_path = std::env::args()
        .nth(2)
        .ok_or_else(|| "No output file path provided")?;

    let input = std::fs::read_to_string(&input_path)
        .map_err(|_| format!("Could not read from file '{}'", &input_path))?;

    let output = parser()
        .parse(&*input)
        .map_err(|e| format!("Could not parse input: {:?}", e))?;

    std::fs::write(&output_path, &output)
        .map_err(|_| format!("Could not write to file '{}'", &output_path))?;

    let end = Instant::now();

    println!(
        "Successfully generated binary file '{}' ({} bytes) in {} ms",
        &output_path,
        output.len(),
        ((end - start).as_nanos() as f64) / 1e6
    );

    Ok(())
}
