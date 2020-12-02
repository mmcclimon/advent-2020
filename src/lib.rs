#![feature(try_trait)]

use std::fmt;
use std::io::Error as IoError;
use std::num::ParseIntError;
use std::option::NoneError;

#[derive(Debug)]
pub enum AdventError {
  Generic(String),
  Io(IoError),
  ParseInt(ParseIntError),
  Empty(NoneError),
}

type AE = AdventError;
pub type Result<T> = std::result::Result<T, AdventError>;

impl std::error::Error for AdventError {}

impl fmt::Display for AdventError {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      AE::Generic(err) => write!(f, "{}", err),
      AE::Io(err) => write!(f, "{:?}", err),
      AE::ParseInt(err) => write!(f, "{:?}", err),
      AE::Empty(err) => write!(f, "{:?}", err),
    }
  }
}

impl From<IoError> for AdventError {
  fn from(err: IoError) -> Self {
    AE::Io(err)
  }
}

impl From<ParseIntError> for AdventError {
  fn from(err: ParseIntError) -> Self {
    AE::ParseInt(err)
  }
}

impl From<NoneError> for AdventError {
  fn from(err: NoneError) -> Self {
    AE::Empty(err)
  }
}
