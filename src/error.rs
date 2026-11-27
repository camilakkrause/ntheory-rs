//! Error types for `ntheory-rs`.

use std::fmt;

/// Errors returned by number-theoretic functions when preconditions fail or no solution exists.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NTheoryError {
    /// Arguments are required to be coprime (`gcd(a, n) == 1`), e.g. `n_order` or `mod_inv`.
    NotCoprime,
    /// Modulus or argument must be prime (e.g. `legendre_symbol`, `nthroot_mod`).
    NotPrime,
    /// Invalid domain argument (e.g. `n == 0`, even modulus for Jacobi symbol, empty slice).
    InvalidArgument(&'static str),
    /// No mathematical solution exists (e.g. inconsistent CRT, non-residue square root, no discrete log).
    NoSolution,
    /// Result exceeds the capacity of the fixed-width integer type (`u64` / `u128`); use `big` module.
    Overflow,
}

impl fmt::Display for NTheoryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotCoprime => write!(f, "arguments are not coprime"),
            Self::NotPrime => write!(f, "argument must be prime"),
            Self::InvalidArgument(msg) => write!(f, "invalid argument: {}", msg),
            Self::NoSolution => write!(f, "no solution exists"),
            Self::Overflow => write!(f, "arithmetic overflow; consider using ntheory_rs::big"),
        }
    }
}

impl std::error::Error for NTheoryError {}
