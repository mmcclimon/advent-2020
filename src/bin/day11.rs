use std::fmt;
use std::fs::File;
use std::io::prelude::*;
use std::io::BufReader;

use advent::Result;

#[derive(Debug, Clone, PartialEq, Eq)]
enum Tile {
  Floor,
  Empty,
  Occupied,
}

#[derive(Debug, Clone)]
struct Grid(Vec<Vec<Tile>>);

fn main() -> Result<()> {
  let reader = BufReader::new(File::open("input/d11.txt")?);

  let raw = reader
    .lines()
    .map(|l| {
      l.unwrap()
        .chars()
        .map(|c| match c {
          'L' => Tile::Empty,
          '.' => Tile::Floor,
          '#' => Tile::Occupied,
          _ => unreachable!(),
        })
        .collect()
    })
    .collect();

  let grid = Grid(raw);

  println!("part 1: {}", grid.run_sim(true, 4));
  println!("part 2: {}", grid.run_sim(false, 5));

  Ok(())
}

impl Grid {
  fn get(&self, row: isize, col: isize) -> Option<&Tile> {
    let g = &self.0;

    if row < 0 || col < 0 || row >= g.len() as isize || col >= g[0].len() as isize
    {
      None
    } else {
      Some(&g[row as usize][col as usize])
    }
  }

  fn num_occupied(&self) -> usize {
    self
      .0
      .iter()
      .flat_map(|t| t)
      .filter(|t| **t == Tile::Occupied)
      .count()
  }

  fn run_sim(&self, adjacent_only: bool, threshold: u8) -> usize {
    let mut grid = self.clone();

    loop {
      let next = grid.do_round(adjacent_only, threshold);
      if next == grid {
        break;
      }

      grid = next;
    }

    grid.num_occupied()
  }

  fn do_round(&self, adjacent_only: bool, threshold: u8) -> Grid {
    // this is...maybe excessive
    Grid(
      self
        .0
        .iter()
        .enumerate()
        .map(|(r, row)| {
          row
            .iter()
            .enumerate()
            .map(move |(c, tile)| {
              (tile, self.first_occupied(r, c, adjacent_only))
            })
            .map(|(tile, n)| match tile {
              Tile::Empty if n == 0 => Tile::Occupied,
              Tile::Occupied if n >= threshold => Tile::Empty,
              _ => tile.clone(),
            })
            .collect()
        })
        .collect(),
    )
  }

  fn first_occupied(&self, row: usize, col: usize, adjacent_only: bool) -> u8 {
    let mut total = 0;

    // for every direction, keep going until you see something or it's off grid
    for xstep in -1..=1 {
      'dir: for ystep in -1..=1 {
        if (xstep, ystep) == (0, 0) {
          continue 'dir;
        }

        'factor: for factor in 1..self.0.len() {
          let x = row as isize + xstep * factor as isize;
          let y = col as isize + ystep * factor as isize;

          match self.get(x, y) {
            Some(Tile::Floor) => (),
            Some(Tile::Occupied) => {
              total += 1;
              continue 'dir;
            },
            _ => continue 'dir,
          }

          if adjacent_only {
            break 'factor;
          }
        }
      }
    }

    total
  }
}

impl fmt::Display for Grid {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let s = self
      .0
      .iter()
      .map(|row| {
        row
          .iter()
          .map(|c| match c {
            Tile::Empty => "L",
            Tile::Floor => ".",
            Tile::Occupied => "#",
          })
          .collect::<Vec<_>>()
          .join("")
      })
      .collect::<Vec<_>>()
      .join("\n");

    write!(f, "{}", s)
  }
}

impl Eq for Grid {}
impl PartialEq for Grid {
  fn eq(&self, other: &Self) -> bool {
    self.0 == other.0
  }
}
