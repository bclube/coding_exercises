use std::fs::File;
use std::io::{BufRead, BufReader, Result};
use std::path::Path;

pub fn input_file_lines(filename: &str) -> Result<impl Iterator<Item = Result<String>>> {
    let path = Path::new("inputs").join(filename);
    let file = File::open(&path)?;
    let lines = BufReader::new(file).lines();

    Ok(lines)
}
