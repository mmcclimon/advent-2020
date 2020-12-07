use std::collections::{HashMap, HashSet, VecDeque};
use std::fs::File;
use std::io::prelude::*;
use std::io::BufReader;
use std::str::FromStr;

use advent::{AdventError, Result};

#[derive(Debug)]
struct Restriction {
  color: String,
  count: usize,
}

fn main() -> Result<()> {
  let reader = BufReader::new(File::open("input/d7.txt")?);

  let mut map = HashMap::new();

  for line in reader.lines().map(|l| l.unwrap()) {
    let words = line.split(" bags contain ").collect::<Vec<_>>();
    let color = words[0];
    let rest = words[1].trim_end_matches(".");

    let kinds: Vec<Restriction> = if rest == "no other bags" {
      // do nothing
      vec![]
    } else {
      rest
        .split(", ")
        .map(|kind| kind.parse().expect("bad parse"))
        .collect()
    };

    map.insert(color.to_string(), kinds);
  }

  let possibilities = count_possibilities(&map, "shiny gold");
  println!("part 1: {}", possibilities);

  let contains = count_inside(&map, "shiny gold");
  println!("part 2: {}", contains);

  Ok(())
}

fn reverse(
  graph: &HashMap<String, Vec<Restriction>>,
) -> HashMap<String, HashSet<String>> {
  let mut rev = HashMap::new();

  for (k, v) in graph.iter() {
    for r in v.iter() {
      let col = r.color.to_string();
      if !rev.contains_key(&col) {
        rev.insert(col, HashSet::new());
      }

      rev.get_mut(&r.color).unwrap().insert(k.to_string());
    }
  }

  rev
}

// pretty sure this is just BFS
fn count_possibilities(
  graph: &HashMap<String, Vec<Restriction>>,
  want: &str,
) -> usize {
  let rev = reverse(&graph);
  let mut seen = HashSet::new();
  let mut to_inspect = VecDeque::new();

  to_inspect.push_back(want);
  while to_inspect.len() > 0 {
    let k = to_inspect.pop_front().unwrap();
    seen.insert(k);

    let node = rev.get(k);
    if node.is_none() {
      continue;
    }

    let node = node.unwrap();

    for edge in node.iter() {
      if !seen.contains(edge.as_str()) {
        to_inspect.push_back(edge);
      }
    }
  }

  seen.remove(want);
  seen.len()
}

fn count_inside(graph: &HashMap<String, Vec<Restriction>>, want: &str) -> usize {
  let restrictions = graph.get(want).expect("no key found!");

  let mut sum = 0;
  for r in restrictions {
    sum += r.count + (r.count * count_inside(graph, &r.color));
  }

  sum
}

impl FromStr for Restriction {
  type Err = AdventError;
  fn from_str(s: &str) -> Result<Self> {
    let s = s.trim_end_matches("s").trim_end_matches(" bag");
    let mut words = s.split(' ');
    let n = words.next().unwrap();

    Ok(Restriction {
      count: n.parse()?,
      color: words.collect::<Vec<_>>().join(" "),
    })
  }
}
