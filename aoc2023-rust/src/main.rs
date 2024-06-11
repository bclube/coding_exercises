mod common;
mod day01;

use anyhow::Result;

fn main() -> Result<()> {
    let sum = day01::solve()?;

    println!("{}", sum);

    Ok(())
}
