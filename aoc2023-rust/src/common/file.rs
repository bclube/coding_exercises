use std::fs::File;
use std::io::{self, BufRead, BufReader};
use std::path::Path;

pub struct LineIterator {
    reader: BufReader<File>,
}

impl Iterator for LineIterator {
    type Item = io::Result<String>;

    fn next(&mut self) -> Option<Self::Item> {
        let mut line = String::new();
        match self.reader.read_line(&mut line) {
            Ok(0) => None,
            Ok(_) => Some(Ok(line)),
            Err(e) => Some(Err(e)),
        }
    }
}

pub fn lines_from_file(filename: &str) -> io::Result<LineIterator> {
    let path = Path::new("inputs").join(filename);
    let file = File::open(&path)?;
    let reader = BufReader::new(file);

    Ok(LineIterator { reader })
}
