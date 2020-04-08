//! Module containing the different specific errors returned by the algorithms.
use std::error::Error;
use std::fmt;
use std::io;

/// Error returned by the functions charged with graph6 format handling when the given format is
/// incorrect.
#[repr(C)]
#[derive(Debug)]
pub struct InvalidGraph6 {
    details: String,
}

impl InvalidGraph6 {
    /// Returns a new `InvalidGraph6` error with the given error message.
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
        InvalidGraph6::new(&err.to_string())
    }
}

impl From<InvalidBinary> for InvalidGraph6 {
    fn from(err: InvalidBinary) -> Self {
        InvalidGraph6::new(&err.to_string())
    }
}

/// Error returned by the functions charged with binary format handling when the given format is
/// incorrect.
#[repr(C)]
#[derive(Debug)]
pub struct InvalidBinary {
    details: String,
}

impl InvalidBinary {
    /// Returns a new `InvalidBinary` error with the given error message.
    pub fn new(msg: &str) -> InvalidBinary {
        InvalidBinary { details: msg.to_string() }
    }
}

impl fmt::Display for InvalidBinary {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.details)
    }
}

impl Error for InvalidBinary {
    fn description(&self) -> &str {
        &self.details
    }
}

/// Error returned by algorithms supporting only connected graphs when they are given a
/// non-connected graph.
#[repr(C)]
#[derive(Debug)]
pub struct DisconnectedGraph {
    details: String,
}

impl DisconnectedGraph {
    /// Returns a new `DisconectedGraph` error with given error message.
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
