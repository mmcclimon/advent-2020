use std::collections::HashMap;

use advent::Result;

fn main() -> Result<()> {
  let start = &[0, 1, 5, 10, 3, 12, 19];

  println!("part 1: {}", run_until(start, 2020));

  println!("part 2: {}", run_until(start, 30000000));

  Ok(())
}

fn run_until(start: &[usize], max: usize) -> usize {
  // digit: (round last spoken, round before that)
  let mut seen = HashMap::new();

  let mut turn = 1;
  let mut last_spoken = 0;

  for n in start {
    seen.insert(n.clone(), (turn, 0));
    turn += 1;
    last_spoken = *n;
  }

  while turn <= max {
    // Consider the most recently spoken number

    let (last_round, prior_round) = seen.get(&last_spoken).unwrap();

    // it was new if the prior round was 0
    last_spoken = if *prior_round == 0 {
      // - If that was the first time the number has been spoken, the current
      //   player says 0.
      0
    } else {
      // - Otherwise, the number had been spoken before; the current player
      //   announces how many turns apart the number is from when it was previously
      //   spoken.
      last_round - prior_round
    };

    let prior_round = if let Some((have_round, _)) = seen.get(&last_spoken) {
      have_round.clone()
    } else {
      0
    };

    seen.insert(last_spoken, (turn, prior_round));
    turn += 1;
  }

  last_spoken
}
