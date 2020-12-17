use std::collections::HashMap;

use advent::Result;

type Coord3 = (isize, isize, isize);
type Coord4 = (isize, isize, isize, isize);

type Grid<T> = HashMap<T, bool>;

fn main() -> Result<()> {
  let lines = "\
#.#.##.#
#.####.#
...##...
#####.##
#....###
##..##..
#..####.
#...#.#.\
";

  let mut grid3: Grid<Coord3> = HashMap::new();
  let mut grid4: Grid<Coord4> = HashMap::new();
  let mut min = 0;
  let mut max = 0;

  for (y, line) in lines.lines().enumerate() {
    for (x, c) in line.chars().enumerate() {
      grid3.insert((x as isize, y as isize, 0), c == '#');
      grid4.insert((x as isize, y as isize, 0, 0), c == '#');
    }

    max = y as isize;
  }

  for i in 1..=6 {
    min -= 1;
    max += 1;
    grid3 = do_round_3d(grid3, min, max);
    grid4 = do_round_4d(grid4, min, max);

    println!("3d: after round {}: {}", i, num_active(&grid3));
    println!("4d: after round {}: {}", i, num_active(&grid4));
  }

  Ok(())
}

fn do_round_3d(grid: Grid<Coord3>, min: isize, max: isize) -> Grid<Coord3> {
  let mut next = HashMap::new();

  for x in min..=max {
    for y in min..=max {
      for z in min..=max {
        let coord = (x, y, z);
        let count = active_neighbors(&grid, coord);

        let is_active = grid.get(&coord).unwrap_or(&false);

        let state = if *is_active {
          count == 2 || count == 3
        } else {
          count == 3
        };

        next.insert(coord, state);
      }
    }
  }

  next
}

fn active_neighbors(grid: &Grid<Coord3>, point: Coord3) -> usize {
  let mut sum = 0;

  for x in (point.0 - 1)..=(point.0 + 1) {
    for y in (point.1 - 1)..=(point.1 + 1) {
      for z in (point.2 - 1)..=(point.2 + 1) {
        let coord = (x, y, z);
        if coord == point {
          continue;
        }

        if *(grid.get(&coord).unwrap_or(&false)) {
          sum += 1
        }
      }
    }
  }

  sum
}

fn do_round_4d(grid: Grid<Coord4>, min: isize, max: isize) -> Grid<Coord4> {
  let mut next = HashMap::new();

  for x in min..=max {
    for y in min..=max {
      for z in min..=max {
        for w in min..=max {
          let coord = (x, y, z, w);
          let count = active_neighbors_4d(&grid, coord);

          let is_active = grid.get(&coord).unwrap_or(&false);

          let state = if *is_active {
            count == 2 || count == 3
          } else {
            count == 3
          };

          next.insert(coord, state);
        }
      }
    }
  }

  next
}

fn active_neighbors_4d(grid: &Grid<Coord4>, point: Coord4) -> usize {
  let mut sum = 0;

  for x in (point.0 - 1)..=(point.0 + 1) {
    for y in (point.1 - 1)..=(point.1 + 1) {
      for z in (point.2 - 1)..=(point.2 + 1) {
        for w in (point.3 - 1)..=(point.3 + 1) {
          let coord = (x, y, z, w);
          if coord == point {
            continue;
          }

          if *(grid.get(&coord).unwrap_or(&false)) {
            // println!("  {:?}: neighbor {:?} was active", point, coord);
            sum += 1
          }
        }
      }
    }
  }

  sum
}

fn num_active<T>(grid: &Grid<T>) -> usize {
  grid.values().map(|val| if *val { 1 } else { 0 }).sum()
}
