use std::fs::File;
use std::io::prelude::*;
use std::io::BufReader;
use std::str::FromStr;

use std::collections::HashSet;

fn main() -> std::io::Result<()> {
  let mut nums = HashSet::new();
  let reader = BufReader::new(File::open("input/d1.txt")?);

  for line in reader.lines() {
    let num = i32::from_str(&line.unwrap()).unwrap();
    nums.insert(num);
  }

  // find two that add up to 2020
  for n in &nums {
    let complement = 2020 - n;
    if nums.contains(&complement) {
      println!("part 1: {} ({} and {})", n * complement, n, complement);
      break;
    }
  }

  // find three that add up to 2020
  'outer: for n in &nums {
    let target = 2020 - n;

    for m in &nums {
      let complement = target - m;
      if nums.contains(&complement) {
        println!(
          "part 2: {} ({}, {} and {})",
          m * n * complement,
          n,
          m,
          complement
        );
        break 'outer;
      }
    }
  }

  Ok(())
}
