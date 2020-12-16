use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::io::prelude::*;
use std::io::BufReader;

use advent::Result;

fn main() -> Result<()> {
  let reader = BufReader::new(File::open("input/d16.txt")?);

  let _lines = "\
class: 0-1 or 4-19
row: 0-5 or 8-19
seat: 0-13 or 16-19

your ticket:
11,12,13

nearby tickets:
3,9,18
15,1,5
5,14,9\
";

  let mut lines = reader.lines().map(|l| l.unwrap()).peekable();
  // let mut lines = lines.lines().peekable();
  let mut hunks = vec![];

  while lines.peek().is_some() {
    hunks.push(
      lines
        .by_ref()
        .take_while(|l| !l.is_empty())
        .collect::<Vec<_>>(),
    );
  }

  let legend = hunks[0].clone();
  let mine: Vec<usize> = hunks[1][1]
    .clone()
    .split(",")
    .map(|n| n.parse().unwrap())
    .collect();

  let nearby = hunks[2][1..]
    .iter()
    .map(|s| s.to_string())
    .collect::<Vec<_>>();

  // build up valid list
  let mut validators = HashMap::new(); // key -> closure

  for line in &legend {
    let mut parts = line.split(": ");
    let desc = parts.next().unwrap();

    let mut conds = vec![];

    for bit in parts.next().unwrap().split(" or ") {
      let mut nums = bit.split('-');
      let low: usize = nums.next().unwrap().parse()?;
      let high: usize = nums.next().unwrap().parse()?;
      conds.push((low, high));
    }

    let c = move |n| {
      (conds[0].0..=conds[0].1).contains(&n)
        || (conds[1].0..=conds[1].1).contains(&n)
    };

    validators.insert(desc, c);
  }

  let mut invalid_digits = vec![];
  let mut valid_tickets = vec![];

  for ticket in &nearby {
    let nums: Vec<usize> =
      ticket.split(',').map(|n| n.parse().unwrap()).collect();

    let mut ticket_is_valid = true;

    for n in &nums {
      let mut is_valid = false;

      for validator in validators.values() {
        if validator(*n) {
          is_valid = true;
          break;
        }
      }

      if !is_valid {
        ticket_is_valid = false;
        invalid_digits.push(*n);
      }
    }

    if ticket_is_valid {
      valid_tickets.push(nums);
    }
  }

  println!("part 1: {}", invalid_digits.iter().sum::<usize>());

  // for every digit, in every ticket, compile a list of columns it could be
  let slot_len = valid_tickets[0].len();

  // slots starts off with every slot valid for everything
  let all_cols: HashSet<String> =
    validators.keys().map(|s| s.to_string()).collect();

  let mut slots: Vec<HashSet<String>> = vec![all_cols.clone(); slot_len];

  for idx in 0..slot_len {
    for ticket in &valid_tickets {
      let n = ticket[idx];
      for (name, validator) in validators.iter() {
        if validator(n) {
          // println!("{} at idx {} is valid for {}", n, idx, name);
          // slots[idx].insert(name.to_string());
        } else {
          // println!("{} at idx {} is not valid for {}", n, idx, name);
          slots[idx].remove(*name);
        }
      }
    }
  }

  // gotta postprcoess the slots
  while slots.iter().filter(|s| s.len() > 1).count() > 0 {
    let singles: Vec<_> = slots.iter().filter(|s| s.len() == 1).collect();

    let to_remove = singles
      .iter()
      .map(|s| s.iter().next().unwrap())
      .cloned()
      .collect::<Vec<_>>();

    for set in &mut slots {
      if set.len() == 1 {
        continue;
      }

      for el in &to_remove {
        set.remove(el);
      }
    }
  }

  let lookup: HashMap<_, _> = slots
    .iter()
    .enumerate()
    .map(|(idx, s)| (s.iter().next().unwrap(), idx))
    .collect();

  let part2: usize = lookup
    .iter()
    .filter(|(k, _)| k.starts_with("departure"))
    .map(|(_, idx)| mine[*idx])
    .product();

  println!("part 2: {:?}", part2);

  Ok(())
}
