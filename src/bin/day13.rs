use std::fs::File;
use std::io::prelude::*;
use std::io::BufReader;

use advent::Result;

fn main() -> Result<()> {
  let reader = BufReader::new(File::open("input/d13.txt")?);

  let mut lines = reader.lines();
  let target = lines.next().unwrap()?.parse()?;
  let time_list = lines.next().unwrap()?;
  // let time_list = "17,x,13,19";
  let times = time_list.split(",").collect();

  println!("part 1: {}", do_part_1(target, &times));
  println!("part 2: {}", do_part_2(&times));

  Ok(())
}

fn do_part_1(target: usize, times: &Vec<&str>) -> usize {
  let buses: Vec<usize> = times
    .iter()
    .filter(|s| **s != "x")
    .map(|n| n.parse().unwrap())
    .collect();

  let mut smallest = usize::MAX;
  let mut winner = 0;

  for bus in buses {
    let time = (((target / bus) + 1) * bus) - target;
    if time < smallest {
      smallest = time;
      winner = bus;
    }
  }

  winner * smallest
}

// https://en.wikipedia.org/wiki/Chinese_remainder_theorem#Search_by_sieving
// this isn't the fastest way but mostly what I intuited to start
fn do_part_2(times: &Vec<&str>) -> usize {
  // munge this into a structure like
  // [ (modulus, remainder), (modulus, remainder), ... ]
  let mut list = times
    .iter()
    .enumerate()
    .filter(|(_, s)| **s != "x")
    .map(|(idx, n)| (idx, n.parse::<usize>().unwrap()))
    .map(|(idx, n)| {
      (
        n,
        (n as isize - idx as isize).rem_euclid(n as isize) as usize,
      )
    });

  let (mut to_add, mut t) = list.next().unwrap();

  for (next_mod, next_rem) in list {
    'inner: loop {
      if t % next_mod == next_rem {
        to_add *= next_mod;
        break 'inner;
      }

      t += to_add;
    }
  }

  t
}
