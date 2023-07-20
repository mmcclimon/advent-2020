use std::collections::HashMap;
use std::fs::File;
use std::io::prelude::*;
use std::io::BufReader;

use advent::Result;

fn main() -> Result<()> {
  let reader = BufReader::new(File::open("input/d19.txt")?);

  let mut lines = reader.lines().map(|l| l.unwrap());

  let mut raw = HashMap::new();

  lines
    .by_ref()
    .take_while(|l| !l.is_empty())
    .for_each(|line| {
      let mut chunks = line.split(": ");
      let label = chunks.next().expect(&format!("bad line: {line}"));
      let rest = chunks.next().expect(&format!("bad line: {line}"));

      raw.insert(label.to_string(), rest.to_string());
    });

  let samples = lines.collect::<Vec<_>>();

  let rules_p1 = compile_rules(raw.clone());
  let rule0 = rules_p1.get("0").unwrap();

  let part1 = samples
    .iter()
    .filter(|line| rule0.matches_str(line))
    .count();

  println!("part 1: {part1}");

  Ok(())
}

#[derive(Debug, Clone)]
enum Rule {
  Literal(&'static str),
  Seq(Vec<Rule>),
  Alternation(Box<Rule>, Box<Rule>),
}

fn compile_rules(mut raw: HashMap<String, String>) -> HashMap<String, Rule> {
  let mut compiled = HashMap::new();

  while !raw.is_empty() {
    for (k, v) in raw.iter() {
      if let Some(rule) = compile(&mut compiled, v) {
        compiled.insert(k.to_string(), rule);
      }
    }

    raw.retain(|k, _| !compiled.contains_key(k));
  }

  compiled
}

fn compile(compiled: &HashMap<String, Rule>, raw: &str) -> Option<Rule> {
  if raw.starts_with('"') {
    return Some(match raw {
      r#""a""# => Rule::Literal("a"),
      r#""b""# => Rule::Literal("b"),
      _ => panic!("weird rule: {}", raw),
    });
  }

  if raw.contains('|') {
    let mut parts = raw.split(" | ");
    let left = compile(compiled, parts.next().expect("bad alternation 1"));
    let right = compile(compiled, parts.next().expect("bad alternation 2"));
    if left.is_some() && right.is_some() {
      return Some(Rule::Alternation(
        Box::new(left.unwrap()),
        Box::new(right.unwrap()),
      ));
    }

    return None;
  }

  // split, fetch
  let rules = raw
    .split_whitespace()
    .map(|key| compiled.get(key))
    .collect::<Vec<_>>();

  if rules.iter().all(|r| r.is_some()) {
    return Some(Rule::Seq(
      rules.iter().map(|r| r.unwrap().clone()).collect(),
    ));
  }

  None
}

impl Rule {
  fn matches_str(&self, s: &str) -> bool {
    let (ret, n) = self._matches_str(s);
    ret && n == s.len()
  }

  fn _matches_str(&self, s: &str) -> (bool, usize) {
    // println!("_matches_str: {:?}, {s}", self);

    if s == "" {
      return (false, 0);
    }

    match self {
      Rule::Literal(c) => (&&s[0..1] == c, 1),
      Rule::Alternation(left, right) => {
        let (lm, n) = left._matches_str(s);
        if lm {
          return (lm, n);
        }

        right._matches_str(s)
      },
      Rule::Seq(seq) => {
        let mut n = 0;

        for rule in seq {
          let (matches, consumed) = rule._matches_str(&s[n..]);
          // println!("{}: {matches}, {consumed}", &s[n..]);
          n += consumed;

          if !matches {
            // println!("returning (false, {n})");
            return (false, n);
          }
        }

        (true, n)
      },
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  const A: Rule = Rule::Literal("a");
  const B: Rule = Rule::Literal("b");

  #[test]
  fn literal() {
    assert!(A.matches_str("a"), "literal a matches");
    assert!(!A.matches_str("b"), "literal b does not match");
  }

  #[test]
  fn literal_lengths() {
    assert!(!A.matches_str("aa"), "aa does not match a");
    assert!(!A.matches_str(""), "empty string does not match a");
  }

  #[test]
  fn alternation() {
    let alt = Rule::Alternation(Box::new(A), Box::new(B));
    assert!(alt.matches_str("a"), "a =~ a|b");
    assert!(alt.matches_str("b"), "b =~ a|b");
    assert!(!alt.matches_str("c"), "c !~ a|b");
  }

  #[test]
  fn seq_literals() {
    let seq = Rule::Seq(vec![A, B]);
    assert!(seq.matches_str("ab"), "ab =~ ab");
    assert!(!seq.matches_str("abc"), "abc !~ ab");
    assert!(!seq.matches_str("a"), "a !~ ab");
  }

  #[test]
  fn seq_alternation() {
    let seq = Rule::Seq(vec![
      A,
      Rule::Alternation(
        Box::new(Rule::Seq(vec![A, B])),
        Box::new(Rule::Seq(vec![B, A])),
      ),
    ]);

    assert!(seq.matches_str("aba"), "aba =~ a(ab|ba)");
    assert!(seq.matches_str("aab"), "aab =~ a(ab|ba)");
    assert!(!seq.matches_str("baa"), "baa !~ a(ab|ba)");
    assert!(!seq.matches_str("aaa"), "aaa !~ a(ab|ba)");
    assert!(!seq.matches_str("abab"), "abab !~ a(ab|ba)");
    assert!(!seq.matches_str("ab"), "ab !~ a(ab|ba)");
  }
}
