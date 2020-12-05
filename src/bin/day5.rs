use std::fs::File;
use std::io::prelude::*;
use std::io::BufReader;

use advent::Result;

fn main() -> Result<()> {
  let reader = BufReader::new(File::open("input/d5.txt")?);

  let mut ids = reader
    .lines()
    .map(|l| id_for_seat(&l.unwrap()))
    .collect::<Vec<_>>();

  ids.sort_unstable();

  println!("part 1: {}", ids[ids.len() - 1]);

  // find the seat with a gap after it, and the one we want is just after that
  let part2 = ids
    .iter()
    .enumerate()
    .find(|(idx, elem)| ids[idx + 1] - *elem > 1)
    .map(|pair| pair.1 + 1)
    .expect("no seat found");

  println!("part 2: {}", part2);

  Ok(())
}

fn id_for_seat(pass: &str) -> u16 {
  let (rows, cols) = pass.split_at(7);
  let row = binpart(rows, 128, 'F', 'B');
  let col = binpart(cols, 8, 'L', 'R');
  row * 8 + col
}

// there might be a better way to do this, but hey
fn binpart(instructions: &str, max: u16, low_char: char, high_char: char) -> u16 {
  let mut pair = (0, max);
  for c in instructions.chars() {
    match c {
      _ if c == low_char => pair.1 = (pair.0 + pair.1) / 2,
      _ if c == high_char => pair.0 = (pair.0 + pair.1) / 2,
      _ => unreachable!(),
    };
  }

  pair.1 - 1
}
