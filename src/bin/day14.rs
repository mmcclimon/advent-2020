#[allow(unused, dead_code)]
use std::collections::HashMap;
use std::fmt;
use std::fs::File;
use std::io::prelude::*;
use std::io::BufReader;
use std::str::FromStr;

use advent::{AdventError, Result};

struct Mask {
  on:  u64,
  off: u64,
  raw: Vec<u8>,
}

fn main() -> Result<()> {
  let reader = BufReader::new(File::open("input/d14.txt")?);

  let mut mem1 = HashMap::new();
  let mut mem2 = HashMap::new();
  let mut mask = Mask::new();

  for line in reader.lines().map(|l| l.unwrap()) {
    let mut hunks = line.split(" = ");
    let kind = hunks.next().unwrap();
    let val = hunks.next().unwrap();

    if kind == "mask" {
      mask = Mask::from_str(val)?;
    } else {
      // get the digits out
      let loc = &kind[4..kind.len() - 1];
      let key: u64 = loc.parse()?;
      let val: u64 = val.parse()?;

      mem1.insert(key, mask.apply_to(val));

      let all_pos = mask.apply_to_addr(key);
      for pos in all_pos {
        mem2.insert(pos, val);
      }
    }
  }

  let part1: u64 = mem1.values().sum();
  let part2: u64 = mem2.values().sum();

  println!("part 1: {}", part1);
  println!("part 2: {}", part2);

  Ok(())
}

fn addr_possibilities(mut prefix: Vec<u8>, remainder: &[u8]) -> Vec<String> {
  use std::str;

  // base case
  if remainder.len() == 0 {
    let s = str::from_utf8(&prefix).expect("bad bytes??").to_string();
    return vec![s];
  }

  let tail = &remainder[1..remainder.len()];

  match remainder[0] {
    b'0' | b'1' => {
      prefix.push(remainder[0]);
      addr_possibilities(prefix, tail)
    },
    b'X' => {
      let mut zpref = prefix.clone();
      zpref.push(b'0');
      prefix.push(b'1');

      // recur
      let mut ret = addr_possibilities(prefix, tail);
      ret.append(&mut addr_possibilities(zpref, tail));
      ret
    },
    _ => unreachable!(),
  }
}

impl FromStr for Mask {
  type Err = AdventError;

  fn from_str(s: &str) -> Result<Self> {
    let on = u64::from_str_radix(&s.replace("X", "0"), 2)?;
    let mut off = u64::from_str_radix(&s.replace("X", "1"), 2)?;

    // mask off the top 28 bits of the off mask, because we're dealing with
    // 36-bit numbers
    off &= u64::MAX >> 28;

    let raw = s.bytes().collect();
    Ok(Self { on, off, raw })
  }
}

impl Mask {
  fn new() -> Self {
    Self {
      on:  0,
      off: u64::MAX >> 28,
      raw: vec![],
    }
  }

  fn apply_to(&self, n: u64) -> u64 {
    (n | self.on) & self.off
  }

  fn apply_to_addr(&self, n: u64) -> Vec<u64> {
    // first apply to n to get possibilities, _then_ iter
    let mut to_mask: Vec<u8> = format!("{:0>36b}", n).bytes().collect();
    for i in 0..to_mask.len() {
      match self.raw[i] {
        b'0' => (),
        b'1' | b'X' => to_mask[i] = self.raw[i],
        _ => unreachable!(),
      };
    }

    addr_possibilities(vec![], &to_mask)
      .iter()
      .map(|s| Mask::from_str(s).expect("bad mask"))
      .map(|mask| mask.apply_to(n))
      .collect()
  }
}

impl fmt::Debug for Mask {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_struct("Mask")
      .field("on", &format!("{:0>36b}", self.on))
      .field("off", &format!("{:0>36b}", self.off))
      .finish()
  }
}
