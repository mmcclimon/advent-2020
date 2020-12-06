use std::collections::HashMap;
use std::fs::File;
use std::io::prelude::*;
use std::io::BufReader;

use advent::Result;

fn main() -> Result<()> {
  let reader = BufReader::new(File::open("input/d6.txt")?);

  let mut lines = reader.lines().map(|l| l.unwrap()).peekable();
  let mut hunks = vec![];

  while lines.peek().is_some() {
    hunks.push(
      lines
        .by_ref()
        .take_while(|l| !l.is_empty())
        .collect::<Vec<_>>(),
    );
  }

  let mut part1 = 0;
  let mut part2 = 0;

  for hunk in hunks {
    let mut chars = HashMap::new();
    for person in &hunk {
      for c in person.chars() {
        let count = chars.get(&c).unwrap_or(&0).clone();
        chars.insert(c, count + 1);
      }
    }

    // println!("{}, {:?}", chars.len(), hunk);
    part1 += chars.len();
    part2 += chars.values().filter(|v| **v == hunk.len()).count();
  }

  println!("part 1: {}", part1);
  println!("part 2: {}", part2);

  Ok(())
}
