use std::error::Error;
use std::fmt;
use std::io;

#[derive(Debug)]
pub struct InvalidGraph6 {
    details: String,
}

impl InvalidGraph6 {
    pub fn new(msg: &str) -> InvalidGraph6 {
        InvalidGraph6 { details: msg.to_string() }
    }
}

impl fmt::Display for InvalidGraph6 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.details)
    }
}

impl Error for InvalidGraph6 {
    fn description(&self) -> &str {
        &self.details
    }
}

impl From<io::Error> for InvalidGraph6 {
    fn from(err: io::Error) -> Self {
        InvalidGraph6::new(err.description())
    }
}

#[derive(Debug)]
pub struct DisconnectedGraph {
    details: String,
}

impl DisconnectedGraph {
    pub fn new(msg: &str) -> DisconnectedGraph {
        DisconnectedGraph { details: msg.to_string() }
    }
}

impl fmt::Display for DisconnectedGraph {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.details)
    }
}

impl Error for DisconnectedGraph {
    fn description(&self) -> &str {
        &self.details
    }
}
