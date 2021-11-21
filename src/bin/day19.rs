// use std::fs::File;
// use std::io::prelude::*;
// use std::io::BufReader;
use std::collections::HashMap;

use advent::Result;

fn main() -> Result<()> {
  // let reader = BufReader::new(File::open("input/d18.txt")?);
  let lines = "\
0: 1 2
1: \"a\"
2: 1 3 | 3 1
3: \"b\"\
";

  let mut raw = HashMap::new();

  for line in lines.lines() {
    let mut chunks = line.split(": ");
    let label = chunks.next().unwrap();
    let rest = chunks.next().unwrap();

    raw.insert(label.to_string(), rest.to_string());
  }

  compile_rules(raw);

  Ok(())
}

/*
 * Every rule is one of three types:
 * 1. a literal ("a" or "b"); these are base cases
 * 2. a set of rules (1 2)
 * 3. a set of rules with pipe
 */
fn compile_rules(mut raw: HashMap<String, String>) {
  let mut compiled = HashMap::new();

  for (k, v) in raw.iter() {
    if v == r#""a""# {
      compiled.insert(k.clone(), "a");
    } else if v == r#""b""# {
      compiled.insert(k.clone(), "b");
    } else {
      println!("to do: {}", v);
    }
  }

  for k in compiled.keys() {
    raw.remove(&k.to_string());
  }

  println!("{:?}", raw);
  println!("{:?}", compiled);
}
