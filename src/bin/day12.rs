use std::fs::File;
use std::io::prelude::*;
use std::io::BufReader;

use advent::Result;

#[derive(Debug, Clone, PartialEq, Eq)]
enum Dir {
  North,
  South,
  East,
  West,
  Left,
  Right,
  Forward,
}

#[derive(Debug)]
struct Ship {
  x:        isize,
  y:        isize,
  facing:   Dir,
  waypoint: Waypoint,
}

#[derive(Debug)]
struct Waypoint {
  x: isize,
  y: isize,
}

fn main() -> Result<()> {
  let reader = BufReader::new(File::open("input/d12.txt")?);

  let mut ship1 = Ship::new();
  let mut ship2 = Ship::new();

  for line in reader.lines() {
    let (dir, amt) = parse_line(&line.unwrap())?;
    ship1.process_step_pt1(&dir, amt);
    ship2.process_step_pt2(&dir, amt);
  }

  println!("part 1: {}", ship1.manhattan_distance());
  println!("part 2: {}", ship2.manhattan_distance());

  Ok(())
}

fn parse_line(line: &str) -> Result<(Dir, isize)> {
  let (d, num) = line.split_at(1);

  let dir = match d {
    "N" => Dir::North,
    "S" => Dir::South,
    "E" => Dir::East,
    "W" => Dir::West,
    "L" => Dir::Left,
    "R" => Dir::Right,
    "F" => Dir::Forward,
    _ => unreachable!(),
  };

  let amount = num.parse()?;

  Ok((dir, amount))
}

impl Ship {
  fn new() -> Self {
    Self {
      x:        0,
      y:        0,
      facing:   Dir::East,
      waypoint: Waypoint { x: 10, y: 1 },
    }
  }

  fn manhattan_distance(&self) -> isize {
    self.x.abs() + self.y.abs()
  }

  fn convert_rotation(dir: &Dir, amount: isize) -> isize {
    if *dir == Dir::Left {
      (-1 * amount).rem_euclid(360)
    } else {
      amount
    }
  }

  fn process_step_pt1(&mut self, dir: &Dir, amount: isize) {
    let to_move = if *dir == Dir::Forward {
      self.facing.clone()
    } else {
      dir.clone()
    };

    let mut rotate = |dir: &Dir, amt: isize| {
      let mut amt = Self::convert_rotation(dir, amt);

      while amt > 0 {
        self.facing = match self.facing {
          Dir::North => Dir::East,
          Dir::East => Dir::South,
          Dir::South => Dir::West,
          Dir::West => Dir::North,
          _ => unreachable!(),
        };

        amt -= 90;
      }
    };

    match to_move {
      Dir::North => self.y += amount,
      Dir::South => self.y -= amount,
      Dir::East => self.x += amount,
      Dir::West => self.x -= amount,
      Dir::Left | Dir::Right => rotate(&to_move, amount),
      Dir::Forward => unreachable!(),
    };
  }

  fn process_step_pt2(&mut self, dir: &Dir, amount: isize) {
    let mut rotate = |dir: &Dir, amt: isize| {
      let mut amt = Self::convert_rotation(dir, amt);

      while amt > 0 {
        let x = self.waypoint.x;
        let y = self.waypoint.y;

        self.waypoint.x = y;
        self.waypoint.y = -x;

        amt -= 90;
      }
    };

    match *dir {
      Dir::North => self.waypoint.y += amount,
      Dir::South => self.waypoint.y -= amount,
      Dir::East => self.waypoint.x += amount,
      Dir::West => self.waypoint.x -= amount,
      Dir::Left | Dir::Right => rotate(dir, amount),
      Dir::Forward => {
        self.x += self.waypoint.x * amount;
        self.y += self.waypoint.y * amount;
      },
    };
  }
}
