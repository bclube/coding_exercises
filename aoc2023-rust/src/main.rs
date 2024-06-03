mod common;

use crate::common::file::lines_from_file;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let values = calibration_table_values();
    let mut sum = 0;
    for line in lines_from_file("day01.txt")? {
        sum += extract_calibration_values(line?, &values)?;
    }

    println!("{}", sum);

    Ok(())
}

fn calibration_table_values() -> CalibrationTable {
    vec![
        ("1", 1),
        ("2", 2),
        ("3", 3),
        ("4", 4),
        ("5", 5),
        ("6", 6),
        ("7", 7),
        ("8", 8),
        ("9", 9),
        ("0", 0),
        ("one", 1),
        ("two", 2),
        ("three", 3),
        ("four", 4),
        ("five", 5),
        ("six", 6),
        ("seven", 7),
        ("eight", 8),
        ("nine", 9),
        ("zero", 0),
    ]
}

fn extract_calibration_values(
    line: String,
    values: &[CalibrationTableValue],
) -> Result<i32, Box<dyn std::error::Error>> {
    let first = std::iter::successors(Some(&line[..]), |s| (!s.is_empty()).then(|| &s[1..]))
        .find_map(|s| {
            values
                .iter()
                .find_map(|&(name, value)| s.starts_with(name).then(|| value))
        })
        .ok_or("No value found")?;

    let last = std::iter::successors(Some(&line[..]), |s| {
        (!s.is_empty()).then(|| &s[..s.len() - 1])
    })
    .find_map(|s| {
        values
            .iter()
            .find_map(|&(name, value)| s.ends_with(name).then(|| value))
    })
    .ok_or("No value found")?;

    Ok(first * 10 + last)
}

type CalibrationTable = Vec<CalibrationTableValue>;
type CalibrationTableValue = (&'static str, i32);
