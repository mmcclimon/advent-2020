use std::fs::File;
use std::io::prelude::*;
use std::io::BufReader;

use advent::Result;

fn main() -> Result<()> {
  let reader = BufReader::new(File::open("input/d5.txt")?);

  let mut ids = reader
    .lines()
    .map(|l| l.unwrap())
    .map(|pass| {
      // munge into binary string
      pass
        .chars()
        .map(|c| match c {
          'F' | 'L' => "0",
          'B' | 'R' => "1",
          _ => unreachable!(),
        })
        .collect::<Vec<_>>()
        .join("")
    })
    .map(|s| u16::from_str_radix(&s, 2).expect("bad binary?"))
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
