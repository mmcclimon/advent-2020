use std::fs::File;
use std::io::prelude::*;
use std::io::BufReader;
use std::str::FromStr;

use advent::{AdventError, Result};

#[derive(Debug)]
struct Passport {
  byr: String,
  iyr: String,
  eyr: String,
  hgt: String,
  hcl: String,
  ecl: String,
  pid: String,
  cid: Option<String>,
}

fn main() -> Result<()> {
  let reader = BufReader::new(File::open("input/d4.txt")?);

  let lines = reader.lines().map(|l| l.unwrap()).collect::<Vec<_>>();
  let mut raw = vec![];

  // surely there's a better way to do this with take_while or something
  let mut i = 0;
  while i < lines.len() {
    let mut pp = vec![];

    while i < lines.len() && !lines[i].is_empty() {
      pp.push(lines[i].to_string());
      i += 1;
    }

    i += 1;

    raw.push(pp.join(" "));
  }

  let passports: Vec<Passport> =
    raw.iter().filter_map(|s| s.parse().ok()).collect();

  println!("part 1: {}", passports.len());

  let valid = passports
    .iter()
    .filter_map(|pp| pp.assert_valid().ok())
    .count();
  println!("part 2: {}", valid);

  Ok(())
}

impl FromStr for Passport {
  type Err = AdventError;

  fn from_str(s: &str) -> Result<Self> {
    let mut byr = None;
    let mut iyr = None;
    let mut eyr = None;
    let mut hgt = None;
    let mut hcl = None;
    let mut ecl = None;
    let mut pid = None;
    let mut cid = None;

    for hunk in s.split(" ") {
      let (field, val) = hunk.split_at(4);
      match field.trim_end_matches(':') {
        "byr" => byr = Some(val.to_string()),
        "iyr" => iyr = Some(val.to_string()),
        "eyr" => eyr = Some(val.to_string()),
        "hgt" => hgt = Some(val.to_string()),
        "hcl" => hcl = Some(val.to_string()),
        "ecl" => ecl = Some(val.to_string()),
        "pid" => pid = Some(val.to_string()),
        "cid" => cid = Some(val.to_string()),
        _ => return Err(AdventError::Generic("unknown key!".to_string())),
      }
    }

    Ok(Passport {
      byr: byr?,
      iyr: iyr?,
      eyr: eyr?,
      hgt: hgt?,
      hcl: hcl?,
      ecl: ecl?,
      pid: pid?,
      cid,
    })
  }
}

impl Passport {
  fn assert_valid(&self) -> Result<()> {
    let bad = |s| Err(AdventError::Generic(s));

    // birth year, 1920-2002
    let byr: usize = self.byr.parse()?;
    if !(1920..=2002).contains(&byr) {
      return bad(format!("bad birth year: {}", self.byr));
    }

    // issue year, 2010-2020
    let iyr: usize = self.iyr.parse()?;
    if !(2010..=2020).contains(&iyr) {
      return bad(format!("bad issue year: {}", self.iyr));
    }

    // expiration year, 2020-2030
    let eyr: usize = self.eyr.parse()?;
    if !(2020..=2030).contains(&eyr) {
      return bad(format!("bad exp year: {}", self.eyr));
    }

    // height: 150-193cm or 59-76in
    let height: usize = self
      .hgt
      .chars()
      .take_while(|c| c.is_digit(10))
      .collect::<String>()
      .parse()?;

    let height_ok = if self.hgt.ends_with("in") {
      (59..=76).contains(&height)
    } else if self.hgt.ends_with("cm") {
      (150..=193).contains(&height)
    } else {
      false
    };

    if !height_ok {
      return bad(format!("bad height : {}", self.hgt));
    }

    // hair color, # followed by 6 hex digits
    if self.hcl.len() != 7 || !self.hcl.chars().skip(1).all(|c| c.is_digit(16)) {
      return bad(format!("bad hair color: {}", self.hcl));
    }

    // eye color: gotta be on the list
    match self.ecl.as_str() {
      "amb" | "blu" | "brn" | "gry" | "grn" | "hzl" | "oth" => (),
      _ => return bad(format!("bad eye color: {}", self.ecl)),
    };

    // passport id: 9 digits, all numeric
    if self.pid.len() != 9 || !self.pid.chars().all(|c| c.is_digit(10)) {
      return bad(format!("bad passport id: {}", self.pid));
    }

    Ok(())
  }
}
