use crate::common::ascii::parse_int;
use crate::input_file_lines;
use anyhow::{anyhow, Result};

// Personal goals for this day 2 exercise:
// - Optimize performance by:
//   - Avoid allocating to the heap, where possible
//   - Prefer directly manipulating memory, vs by reference, when it can improve performance. E.g. updating the max value of a bucket.
// - Optimize readability by:
//   - Reducing nesting, where reasonable
//   - Chaining method calls, but not excessively. E.g. break out of a method chain to assign a value to a variable, if it improves readability.

pub fn solve() -> Result<u32> {
    input_file_lines!("day02.txt")
        .map(find_power_of_cube_game)
        .try_fold(0, |acc, b| Ok(b? + acc))
}

// This is probably an overuse of macros, but this is a learning exercise, so I'm trying things out :).
// Pros :
//  - It's a bit more readable than the equivalent code.
//  - It's a bit more DRY than the equivalent code.
//  - Slightly more performant, due to avoiding bucket manipulation via reference and/or function call overhead.
// Cons :
//  - It violates the first rule of macro club: "Don't use macros.
//    **(unless you really need to, but still, you should probably find another way.
//       **[No, but seriously, just because you _can_ do it, doesn't mean you _should_ do it.
//         **{Ok, if you're still reading this and still insist on using macros, then we can't stop you. Just __please__ be careful!! We love you and don't want you to get hurt!
//           **((Just remember that : "with great power comes great responsibility"))**
//             **<<Please, please, just don't; we implore you. Pretty please?>>**
//               **[[..., etc]]**
//          ))**
//        }**
//      ]**
//    ])**"
//  - The binary will likely be a bit larger than the equivalent code, but not by much.
macro_rules! update_max {
    ($bucket:expr, $n:expr) => {
        if $n > $bucket {
            $bucket = $n;
        }
    };
}

fn find_power_of_cube_game(line: &str) -> Result<u32> {
    let mut r = 0_u8;
    let mut g = 0_u8;
    let mut b = 0_u8;
    // Choosing to use a loop here, instead of `try_fold`, as it seems more readable.
    // Also, it's easier to use multiple buckets in a loop, vs a fold.
    for sample in parse_cube_game_results(line) {
        let (n, bucket) = sample?;
        match bucket {
            b'r' => update_max!(r, n),
            b'g' => update_max!(g, n),
            b'b' => update_max!(b, n),
            _ => return Err(anyhow!("Invalid bucket: {:#?}", bucket)),
        }
    }
    Ok(r as u32 * g as u32 * b as u32)
}

// Parses the cube game results from a line of text.
// Sample game results: "Game 15: 1 green, 19 red, 3 blue; 11 red, 3 blue; 20 red, 4 blue"
// Solution:
// - Convert to bytes, rather than using UTF8 string manipulation, since we know the input is ASCII. This is more performant.
// - Break the string into chunks, where each chunk:
//   - Starts with a digit or is at the beginning of the line.
//   - Ends with a whitespace character or is at the end of the line.
// - The first two chunks will be : "Game " and the game number (e.g. "15: "), so we ignore them.
// - This leaves us with chunks containing a sequence of digits, followed by the cube color, separated by a space character.
//   - We pass each bucket to a function to parse the cube results, and return an iterator to the parsed results.
// Notes:
// - Since we only need to find the minimum number of cubes of each color, we don't need to process games individually.
//   Instead, we can ignore the ';' character that separates each trial, and simply look at each result. The highest number
//   of cubes of each color will be the minimum number of cubes needed.
fn parse_cube_game_results(line: &str) -> impl Iterator<Item = Result<(u8, u8)>> + '_ {
    line.as_bytes()
        .chunk_by(|a, b| !a.is_ascii_whitespace() || !b.is_ascii_digit())
        .skip(2)
        .map(parse_cube_game_count)
}

fn parse_cube_game_count<'a>(line: &'a [u8]) -> Result<(u8, u8)> {
    let mut parts = line.splitn(2, |&c| c.is_ascii_whitespace());

    let count = parts
        .next()
        .ok_or_else(|| anyhow!("Invalid cube input: {:#?}", line))
        .map(|digits| parse_int::<u8>(digits))?
        .ok_or_else(|| anyhow!("Invalid count: {:#?}", line))?;

    let bucket = parts
        .next()
        .ok_or_else(|| anyhow!("Invalid cube input: {:#?}", line))?
        .first()
        .ok_or_else(|| anyhow!("Invalid bucket: {:#?}", line))?;

    Ok((count, *bucket))
}
