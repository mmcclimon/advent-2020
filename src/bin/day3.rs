use std::fs::File;
use std::io::prelude::*;
use std::io::BufReader;

use advent::Result;

fn main() -> Result<()> {
  let reader = BufReader::new(File::open("input/d3.txt")?);

  let map = reader
    .lines()
    .map(|l| l.unwrap().chars().collect::<Vec<_>>())
    .collect::<Vec<_>>();

  let part1 = check_slope(&map, (3, 1));

  let part2 = &[(1, 1), (5, 1), (7, 1), (1, 2)]
    .iter()
    .fold(part1, |acc, tup| acc * check_slope(&map, *tup));

  println!("part 1: {:?}", part1);
  println!("part 2: {:?}", part2);

  Ok(())
}

fn check_slope(map: &Vec<Vec<char>>, (x, y): (usize, usize)) -> usize {
  let mut xs = (0..x * map.len()).step_by(x);

  map.iter().step_by(y).fold(0, |acc, chars| {
    if chars[xs.next().unwrap() % chars.len()] == '#' {
      acc + 1
    } else {
      acc
    }
  })
}
