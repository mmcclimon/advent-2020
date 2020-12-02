use std::fs::File;
use std::io::prelude::*;
use std::io::BufReader;
use std::str::FromStr;

use advent::{AdventError, Result};

#[derive(Debug)]
struct Line {
  a:    usize,
  b:    usize,
  want: char,
  pw:   String,
}

fn main() -> Result<()> {
  let reader = BufReader::new(File::open("input/d2.txt")?);

  let lines: Vec<Line> = reader
    .lines()
    .map(|l| l.expect("bad line!"))
    .map(|l| l.parse().expect("bad parse!"))
    .collect();

  let part1 = lines.iter().filter(|l| l.valid_part_1()).count();
  println!("part 1: {}", part1);

  let part2 = lines.iter().filter(|l| l.valid_part_2()).count();
  println!("part 2: {}", part2);

  Ok(())
}

impl FromStr for Line {
  type Err = AdventError;
  fn from_str(line: &str) -> Result<Self> {
    let mut bits = line.split(&['-', ' ', ':'][..]).filter(|s| !s.is_empty());
    let a: usize = bits.next()?.parse()?;
    let b: usize = bits.next()?.parse()?;
    let want = bits.next()?.chars().next()?;
    let pw = bits.next()?.to_string();

    Ok(Line { a, b, want, pw })
  }
}

impl Line {
  fn valid_part_1(&self) -> bool {
    let count = self.pw.chars().filter(|c| c == &self.want).count();
    (self.a..=self.b).contains(&count)
  }

  fn valid_part_2(&self) -> bool {
    let chars = self.pw.chars().collect::<Vec<_>>();
    let pos1 = chars[self.a - 1] == self.want;
    let pos2 = chars[self.b - 1] == self.want;
    pos1 ^ pos2
  }
}
