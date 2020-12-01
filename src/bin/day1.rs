use std::collections::HashSet;
use std::fs::File;
use std::io::prelude::*;
use std::io::BufReader;
use std::str::FromStr;

fn main() -> std::io::Result<()> {
  let mut nums = HashSet::new();
  let reader = BufReader::new(File::open("input/d1.txt")?);

  for line in reader.lines() {
    let num = i32::from_str(&line.unwrap()).unwrap();
    nums.insert(num);
  }

  // find two that add up to 2020
  let found = look_for(2020, &nums).unwrap();
  output(1, found);

  // find three that add up to 2020
  for n in &nums {
    let got = look_for(2020 - n, &nums);

    if let Some(mut found) = got {
      found.push(*n);
      output(2, found);
      break;
    }
  }

  Ok(())
}

fn look_for(target: i32, nums: &HashSet<i32>) -> Option<Vec<i32>> {
  for n in nums {
    let complement = target - n;
    if nums.contains(&complement) {
      return Some(vec![*n, complement]);
    }
  }

  None
}

fn output(part: u8, mut nums: Vec<i32>) {
  nums.sort_unstable();
  let prod = nums.iter().fold(1, |acc, x| acc * x);
  println!("part {}: {} {:?}", part, prod, nums);
}
