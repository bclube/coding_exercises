use itertools::{
    FoldWhile::{Continue, Done},
    Itertools,
};

use crate::{common::ascii::parse_digit, input_file_lines};

pub fn solve() -> u32 {
    input_file_lines!("day03.txt")
        .map(<str>::as_bytes)
        .tuple_windows()
        .flat_map(determine_gear_ratios)
        .sum()
}

type Lines<'a> = (&'a [u8], &'a [u8], &'a [u8]);

fn determine_gear_ratios<'a>(lines: Lines<'a>) -> impl Iterator<Item = u32> + 'a {
    let (_, middle_line, _) = lines;
    middle_line
        .iter()
        .enumerate()
        .filter_map(|(i, &c)| (c == b'*').then(|| i))
        .map(move |i| determine_gear_ratio(lines, i))
}

fn parse_part_numbers(line: &[u8], i: usize) -> impl Iterator<Item = u32> {
    match parse_part_number(line, i) {
        Some(r) => [Some(r), None],
        None => [
            parse_part_number(line, i - 1),
            parse_part_number(line, i + 1),
        ],
    }
    .into_iter()
    .filter_map(|v| v)
}

fn determine_gear_ratio<'a>(lines: Lines<'a>, i: usize) -> u32 {
    let (line_before, line, line_after) = lines;

    [line_before, line, line_after]
        .into_iter()
        .flat_map(|line| parse_part_numbers(line, i))
        .chain(std::iter::once(0)) // ensure that if there are fewer than two parts, the result is 0
        .take(2)
        .product()
}

fn parse_part_number(line: &[u8], col: usize) -> Option<u32> {
    let leading_digits = line[..=col]
        .iter()
        .rev()
        .take_while(|&c| c.is_ascii_digit())
        .count();

    if leading_digits == 0 {
        return None;
    }

    let start = col + 1 - leading_digits;
    line[start..]
        .iter()
        .fold_while(0, |acc, &c| {
            parse_digit(c).map_or_else(|| Done(acc), |d| Continue(acc * 10 + d as u32))
        })
        .into_inner()
        .into()
}
