use std::fs::File;
use std::io::prelude::*;
use std::io::BufReader;
use std::str::FromStr;

use advent::Result;

fn main() -> Result<()> {
  let reader = BufReader::new(File::open("input/d2.txt")?);

  let mut part1 = 0;
  let mut part2 = 0;

  for line in reader.lines() {
    let line = line?;
    let bits = line.split(" ").collect::<Vec<_>>();
    let range = &bits[0];
    let lett = &bits[1].chars().nth(0).expect("no letter??");
    let pw = &bits[2];

    let nums = range
      .split("-")
      .filter_map(|n| usize::from_str(n).ok())
      .collect::<Vec<_>>();

    let left = nums[0];
    let right = nums[1];

    // part 1
    let count = pw.chars().filter(|c| c == lett).count();
    if left <= count && count <= right {
      part1 += 1;
    }

    // part 2
    let chars = pw.chars().collect::<Vec<_>>();
    let pos1 = if &chars[left - 1] == lett { 1 } else { 0 };
    let pos2 = if &chars[right - 1] == lett { 1 } else { 0 };
    if (pos1 + pos2) == 1 {
      part2 += 1;
    }
  }

  println!("part 1: {}", part1);
  println!("part 2: {}", part2);

  Ok(())
}
