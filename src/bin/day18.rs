use std::convert::TryFrom;
use std::fs::File;
use std::io::prelude::*;
use std::io::BufReader;

use advent::{AdventError, Result};

#[derive(Debug, PartialEq, Eq)]
enum Token {
  LeftParen,
  RightParen,
  Multiply,
  Add,
  Digit(usize),
}

fn main() -> Result<()> {
  let reader = BufReader::new(File::open("input/d18.txt")?);
  let (part1, part2): (usize, usize) = reader
    .lines()
    .map(|line| {
      let l = line.unwrap();
      (eval(parse(&l, false)), eval(parse(&l, true)))
    })
    .fold((0, 0), |(sum1, sum2), (p1, p2)| (sum1 + p1, sum2 + p2));

  println!("part 1: {}", part1);
  println!("part 2: {}", part2);

  Ok(())
}

fn parse(s: &str, use_precedence: bool) -> Vec<Token> {
  let mut output = vec![];
  let mut stack = vec![];

  for c in s.chars().filter(|&c| c != ' ') {
    let token = Token::try_from(c).unwrap();
    match token {
      Token::Digit(_) => output.push(token),
      Token::LeftParen => stack.push(token),
      Token::Multiply | Token::Add => {
        loop {
          if stack.len() == 0 || stack.last().unwrap() == &Token::LeftParen {
            stack.push(token);
            break;
          } else {
            let top = stack.last().unwrap();

            if use_precedence && token == Token::Add && top == &Token::Multiply {
              // 5. If the incoming symbol has higher precedence than the top of the
              //    stack, push it on the stack.
              stack.push(token);
              break;
            } else if !use_precedence || top == &token {
              // 6. If the incoming symbol has equal precedence with the top of the
              //    stack, use association. If the association is left to right, pop
              //    and print the top of the stack and then push the incoming
              //    operator. If the association is right to left, push the incoming
              //    operator.
              output.push(stack.pop().unwrap());
              stack.push(token);
              break;
            } else {
              // 7. If the incoming symbol has lower precedence than the symbol on
              //    the top of the stack, pop the stack and print the top operator.
              //    Then test the incoming operator against the new top of stack.
              output.push(stack.pop().unwrap());
            }
          }
        }
      },
      Token::RightParen => {
        while stack.len() > 0 {
          let op = stack.pop().unwrap();
          if op == Token::LeftParen {
            break;
          }
          output.push(op);
        }
      },
    };
  }

  while stack.len() > 0 {
    output.push(stack.pop().unwrap());
  }

  output
}

fn eval(expr: Vec<Token>) -> usize {
  let mut stack = vec![];

  for token in expr {
    match token {
      Token::Digit(n) => stack.push(n),
      Token::Multiply => {
        let a = stack.pop().expect("stack underflow");
        let b = stack.pop().expect("stack underflow");
        stack.push(a * b);
      },
      Token::Add => {
        let a = stack.pop().expect("stack underflow");
        let b = stack.pop().expect("stack underflow");
        stack.push(a + b);
      },
      _ => unreachable!(),
    }
  }

  stack.pop().expect("stack underflow")
}

impl TryFrom<char> for Token {
  type Error = AdventError;
  fn try_from(c: char) -> Result<Self> {
    match c {
      '0'..='9' => Ok(Token::Digit(c.to_string().parse()?)),
      '*' => Ok(Token::Multiply),
      '+' => Ok(Token::Add),
      '(' => Ok(Token::LeftParen),
      ')' => Ok(Token::RightParen),
      _ => Err(AdventError::Generic(format!("unparseable char {}", c))),
    }
  }
}
