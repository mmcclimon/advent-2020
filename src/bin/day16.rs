#![feature(type_alias_impl_trait)]

use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::io::prelude::*;
use std::io::BufReader;

use advent::Result;

type ValidatorMap = HashMap<String, impl Fn(usize) -> bool>;

fn main() -> Result<()> {
  let reader = BufReader::new(File::open("input/d16.txt")?);

  let mut lines = reader.lines().map(|l| l.unwrap()).peekable();
  let mut hunks = vec![];

  while lines.peek().is_some() {
    hunks.push(
      lines
        .by_ref()
        .take_while(|l| !l.is_empty())
        .collect::<Vec<_>>(),
    );
  }

  let validators = parse_legend(hunks[0].clone());

  let my_ticket = parse_ticket(&hunks[1][1]);

  let nearby = hunks[2]
    .iter()
    .skip(1)
    .map(|s| parse_ticket(s))
    .collect::<Vec<_>>();

  let mut part1 = 0;

  let valid_tickets: Vec<&Vec<usize>> = nearby
    .iter()
    .filter_map(|t| {
      let (is_valid, bad_digits) = validate_ticket(&validators, t);
      part1 += bad_digits.iter().sum::<usize>();

      if is_valid {
        Some(t)
      } else {
        None
      }
    })
    .collect();

  println!("part 1: {}", part1);

  let columns = calc_columns(&validators, &valid_tickets);

  let part2: usize = columns
    .iter()
    .filter(|(k, _)| k.starts_with("departure"))
    .map(|(_, idx)| my_ticket[*idx])
    .product();

  println!("part 2: {:?}", part2);

  Ok(())
}

fn parse_legend(lines: Vec<String>) -> ValidatorMap {
  let mut validators = HashMap::new(); // key -> closure

  for line in &lines {
    let mut parts = line.split(": ");
    let desc = parts.next().unwrap();

    let mut conds = vec![];

    for bit in parts.next().unwrap().split(" or ") {
      let mut nums = bit.split('-');
      let low: usize = nums.next().unwrap().parse().expect("bad parse");
      let high: usize = nums.next().unwrap().parse().expect("bad parse");
      conds.push((low, high));
    }

    let c = move |n| {
      (conds[0].0..=conds[0].1).contains(&n)
        || (conds[1].0..=conds[1].1).contains(&n)
    };

    validators.insert(desc.to_string(), c);
  }

  validators
}

fn parse_ticket(line: &str) -> Vec<usize> {
  line
    .clone()
    .split(",")
    .map(|n| n.parse().unwrap())
    .collect()
}

fn validate_ticket(
  validators: &ValidatorMap,
  ticket: &Vec<usize>,
) -> (bool, Vec<usize>) {
  let mut ticket_is_valid = true;
  let mut invalid_digits = vec![];

  for n in ticket {
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

  (ticket_is_valid, invalid_digits)
}

fn calc_columns(
  validators: &ValidatorMap,
  tickets: &Vec<&Vec<usize>>,
) -> HashMap<String, usize> {
  // for every digit, in every ticket, compile a list of columns it could be
  let ticket_len = tickets[0].len();

  // slots starts off with every slot valid for everything, and we'll slowly
  // reduce this as we go
  let all_cols: HashSet<String> =
    validators.keys().map(|s| s.to_string()).collect();

  let mut slots: Vec<HashSet<String>> = vec![all_cols.clone(); ticket_len];

  // all slot 0s, then all slot 1s, ...
  for idx in 0..ticket_len {
    for ticket in tickets {
      let n = ticket[idx];

      for (name, validator) in validators.iter() {
        if !validator(n) {
          slots[idx].remove(name);
        }
      }
    }
  }

  // Now, we have all possibilities for all slots. Some are ambiguous though, so
  // we need to find all the singles, then remove those from the other
  // possibilities, until all we're left with are singles

  // gotta postprcoess the slots
  while slots.iter().filter(|s| s.len() > 1).count() > 0 {
    let singles: Vec<_> = slots.iter().filter(|s| s.len() == 1).collect();

    let to_remove = singles
      .iter()
      .map(|s| s.iter().next().unwrap())
      .cloned()
      .collect::<Vec<_>>();

    for set in slots.iter_mut().filter(|s| s.len() > 1) {
      for el in &to_remove {
        set.remove(el);
      }
    }
  }

  slots
    .iter()
    .enumerate()
    .map(|(idx, s)| (s.iter().next().unwrap().clone(), idx))
    .collect()
}
