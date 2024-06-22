mod common;
mod day03;

use anyhow::Result;

fn main() -> Result<()> {
    let result = day03::solve();

    println!("{}", result);

    Ok(())
}
