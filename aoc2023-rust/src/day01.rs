use crate::common::ascii::parse_digit;
use crate::input_file_lines;
use anyhow::{anyhow, Result};

pub fn solve() -> Result<u32> {
    input_file_lines!("day01.txt")
        .map(|line| line.as_bytes())
        .try_fold(0, |sum, line| {
            let first = first_calibration_value(line)?;
            let last = last_calibration_value(line)?;
            Ok(sum + (first * 10 + last) as u32)
        })
}

const CALIBRATION_TABLE_VALUE: &[(&'static str, u8)] = &[
    ("zero", 0),
    ("one", 1),
    ("two", 2),
    ("three", 3),
    ("four", 4),
    ("five", 5),
    ("six", 6),
    ("seven", 7),
    ("eight", 8),
    ("nine", 9),
];

fn last_calibration_value(line: &[u8]) -> Result<u8> {
    (1..=line.len())
        .rev()
        .map(|i| &line[..i])
        .find_map(|s| {
            s.last()
                .and_then(|&c| parse_digit(c))
                .or_else(|| parse_calibration_value(|cv| s.ends_with(cv)))
        })
        .ok_or_else(|| anyhow!("No value found at end of line"))
}

fn first_calibration_value(line: &[u8]) -> Result<u8> {
    (0..line.len())
        .map(|i| &line[i..])
        .find_map(|s| {
            s.first()
                .and_then(|&c| parse_digit(c))
                .or_else(|| parse_calibration_value(|cv| s.starts_with(cv)))
        })
        .ok_or_else(|| anyhow!("No value found at start of line"))
}

fn parse_calibration_value<F>(match_fn: F) -> Option<u8>
where
    F: Fn(&[u8]) -> bool,
{
    CALIBRATION_TABLE_VALUE
        .iter()
        .find_map(|&(name, value)| match_fn(name.as_bytes()).then(|| value))
}
