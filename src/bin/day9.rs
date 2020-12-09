use std::cmp;
use std::fs::File;
use std::io::prelude::*;
use std::io::BufReader;

use advent::Result;

const SIZE: usize = 25;

fn main() -> Result<()> {
  let reader = BufReader::new(File::open("input/d9.txt")?);

  let nums = reader
    .lines()
    .filter_map(|l| l.unwrap().parse().ok())
    .collect();

  let part1 = invalid_part1(&nums).expect("no solution?");
  println!("part 1: {}", part1);

  let part2 = invalid_part2(&nums, part1).expect("no solution?");
  println!("part 2: {}", part2);

  Ok(())
}

fn invalid_part1(nums: &Vec<u64>) -> Option<u64> {
  'outer: for i in SIZE..nums.len() {
    let target = nums[i];

    for j in i - SIZE..i - 1 {
      for k in j..i {
        if nums[j] + nums[k] == target {
          continue 'outer;
        }
      }
    }

    return Some(target);
  }

  None
}

fn invalid_part2(nums: &Vec<u64>, target: u64) -> Option<u64> {
  'outer: for i in 0..nums.len() {
    let mut total = 0;
    let mut min = nums[i];
    let mut max = min;

    for j in i..nums.len() {
      total += nums[j];
      min = cmp::min(min, nums[j]);
      max = cmp::max(max, nums[j]);

      if total == target {
        return Some(min + max);
      }

      if total > target {
        continue 'outer;
      }
    }
  }

  None
}
