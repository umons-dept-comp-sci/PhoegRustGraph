use graph::format::from_g6;
use graph::nauty::orbits;
use graph::GraphNauty;
use nom::bytes::complete::{tag, take_while};
use nom::character::complete::{digit1, multispace0, multispace1};
use nom::combinator::{map, opt};
use nom::multi::separated_list0;
use nom::sequence::{delimited, preceded};
use nom::IResult;
use std::io::{self, BufRead, Read};

fn accepted_in_g6(c: char) -> bool {
    if c.is_ascii() {
        let v = c as u8;
        63 <= v && v <= 127
    } else {
        false
    }
}

fn parser<'a>(input: &'a str) -> IResult<&str, &str, ()> {
    let (i, g6) = take_while(accepted_in_g6)(input)?;
    let spaces = |x| delimited(multispace0, x, multispace0);
    let array_parser = delimited(
        spaces(tag("[")),
        separated_list0(
            spaces(tag(",")),
            map(digit1, |v: &str| v.parse::<u64>().unwrap()),
        ),
        spaces(tag("]")),
    );
    let super_array = delimited(
        spaces(tag("[")),
        separated_list0(spaces(tag(",")), array_parser),
        spaces(tag("]")),
    );
    let (v, r) = opt(preceded(multispace1, super_array))(i)?;
    let fixed = r.unwrap_or(vec![]);
    let g: GraphNauty = from_g6(g6).unwrap();
    let res = orbits(&g, &fixed);
    println!("{:?}", res);
    Ok(("", ""))
}

fn main() {
    let stdin = io::stdin();
    let reader = stdin.lock();
    for line in reader.lines() {
        let line = line.unwrap();
        let _ = parser(&line);
    }
}
