mod common;
mod day02;

use anyhow::Result;

fn main() -> Result<()> {
    let sum = day02::solve()?;

    println!("{}", sum);

    Ok(())
}
