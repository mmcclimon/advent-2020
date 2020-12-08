use std::collections::HashSet;
use std::fs::File;
use std::io::prelude::*;
use std::io::BufReader;
use std::str::FromStr;

use advent::{AdventError, Result};

#[derive(Debug, Clone, PartialEq)]
enum Op {
  NOP,
  ACC,
  JMP,
}

#[derive(Debug, Clone)]
struct Instruction {
  op:  Op,
  amt: isize,
}

#[derive(Debug)]
struct Cpu {
  code:       Vec<Instruction>,
  sp:         isize,
  acc:        isize,
  terminated: bool,
}

fn main() -> Result<()> {
  let reader = BufReader::new(File::open("input/d8.txt")?);

  let instructions: Vec<Instruction> = reader
    .lines()
    .map(|l| l.unwrap().parse().expect("bad line"))
    .collect();

  let mut cpu = Cpu::new(&instructions);

  cpu.run();
  println!("part 1: {}", cpu.acc);

  let fixed = Cpu::fix(&instructions);
  println!("part 2: {}", fixed.expect("no solution?").acc);

  Ok(())
}

impl FromStr for Instruction {
  type Err = AdventError;

  fn from_str(s: &str) -> Result<Self> {
    let (opstr, amtstr) = s.split_at(3);

    let op = match opstr {
      "nop" => Op::NOP,
      "acc" => Op::ACC,
      "jmp" => Op::JMP,
      _ => return Err(AdventError::Generic(format!("unknown op {}", opstr))),
    };

    Ok(Self {
      op,
      amt: amtstr.trim().parse()?,
    })
  }
}

impl Instruction {
  fn new(op: Op, amt: isize) -> Self {
    Self { op, amt }
  }
}

impl Cpu {
  fn new(code: &Vec<Instruction>) -> Self {
    Self {
      code:       code.clone(),
      sp:         0,
      acc:        0,
      terminated: false,
    }
  }

  fn run(&mut self) {
    let mut seen = HashSet::new();

    loop {
      // loop check
      if self.sp < 0
        || self.sp as usize >= self.code.len()
        || seen.contains(&self.sp)
      {
        break;
      }

      seen.insert(self.sp);

      let instr = &self.code[self.sp as usize];
      match instr.op {
        Op::NOP => self.sp += 1,
        Op::ACC => {
          self.acc += instr.amt;
          self.sp += 1;
        },
        Op::JMP => self.sp += instr.amt,
      };

      // are we done?
      if self.sp as usize == self.code.len() {
        self.terminated = true;
        break;
      }
    }
  }

  fn fix(code: &Vec<Instruction>) -> Option<Self> {
    // for every instruction, try swapping nop/jmp, run a simulation, check if
    // terminated
    for (idx, instr) in code.iter().enumerate() {
      if instr.op == Op::ACC {
        continue;
      }

      let mut dupe = code.clone();
      dupe[idx] = match instr.op {
        Op::NOP => Instruction::new(Op::JMP, instr.amt),
        Op::JMP => Instruction::new(Op::NOP, instr.amt),
        _ => unreachable!(),
      };

      let mut cpu = Cpu::new(&dupe);
      cpu.run();
      if cpu.terminated {
        return Some(cpu);
      }
    }

    None
  }
}
