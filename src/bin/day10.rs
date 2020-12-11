use std::collections::HashSet;
use std::fs::File;
use std::io::prelude::*;
use std::io::BufReader;

use advent::Result;

fn main() -> Result<()> {
  let reader = BufReader::new(File::open("input/d10.txt")?);

  let mut nums: Vec<usize> = reader
    .lines()
    .filter_map(|l| l.unwrap().parse().ok())
    .collect();

  nums.push(0);
  nums.sort_unstable();

  let max = nums.last().unwrap() + 3;
  nums.push(max);

  let diffs: Vec<usize> = nums
    .iter()
    .enumerate()
    .skip(1)
    .map(|(idx, el)| el - nums[idx - 1])
    .collect();

  let (ones, threes): (Vec<usize>, Vec<usize>) = diffs
    .iter()
    .filter(|&n| n != &1 || n != &3)
    .partition(|&n| n == &1);

  println!("part 1: {}", ones.len() * threes.len());

  // sigh, I spent like 3 hours trying to work this out by hand and being
  // totally stuck, so this is mostly pasted from the internet.
  let mut set = HashSet::new();
  for elem in &nums {
    set.insert(elem);
  }

  let mut steps: Vec<u64> = vec![0; max + 1];

  // base cases: 1, 2, 3
  if set.contains(&1) {
    steps[1] = 1;
  }

  if set.contains(&2) {
    steps[2] = steps[1] + 1;
  }

  if set.contains(&3) {
    steps[3] = steps[2] + steps[1] + 1;
  }

  for i in 4..=max {
    if set.contains(&i) {
      steps[i] = steps[i - 1] + steps[i - 2] + steps[i - 3];
    }
  }

  println!("part 2: {}", steps[max]);

  Ok(())
}
