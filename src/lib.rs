//! # `ntheory-rs` — Fast Zero-Dependency Computational Number Theory for Rust
//!
//! Inspired by Python's `sympy.ntheory`, `ntheory-rs` provides deterministic 64-bit algorithms,
//! 128-bit Montgomery arithmetic, and a built-in arbitrary-precision [`big::BigUint`] engine with
//! Pollard's Rho, Pollard $p - 1$, Montgomery ECM, and Self-Initializing Quadratic Sieve (SIQS).
//!
//! ## Quick Start
//!
//! ```rust
//! use ntheory_rs::{
//!     n_order, factorint, is_prime, next_prime, prime_pi,
//!     totient, primitive_root, sqrt_mod, crt, discrete_log,
//! };
//!
//! assert_eq!(n_order(10, 239).unwrap(), 7);
//! assert_eq!(n_order(10, 5_363_222_357).unwrap(), 17);
//! assert!(is_prime(18_371_524_594_609));
//! assert_eq!(next_prime(100), Some(101));
//! assert_eq!(prime_pi(1_000_000), 78_498);
//! assert_eq!(totient(36), 12);
//! assert_eq!(primitive_root(7), Some(3));
//! assert_eq!(sqrt_mod(2, 7).unwrap(), Some(3));
//! assert_eq!(crt(&[2, 3, 2], &[3, 5, 7]).unwrap(), Some((23, 105)));
//! assert_eq!(discrete_log(3, 13, 17).unwrap(), Some(4));
//!
//! let f = factorint(360);
//! assert_eq!(f[&2], 3);
//! assert_eq!(f[&3], 2);
//! assert_eq!(f[&5], 1);
//! ```
//!
//! ## Three Integer Tiers
//!
//! 1. **Crate root (`u64`)**: Zero-allocation, Montgomery-accelerated paths for all inputs `< 2^64`.
//! 2. **[`u128_ops`] (`u128`)**: Native 128-bit Montgomery arithmetic with automatic SIQS/ECM escalation for factoring.
//! 3. **[`big`] (`BigUint`)**: Built-in multi-limb `BigUint`, CIOS `BigMont`, Baillie-PSW, ECM, and SIQS for arbitrary-precision integers.

pub mod arith;
pub mod bigint;
pub mod cyclotomic;
pub mod error;
pub mod factor;
pub mod functions;
pub mod modular;
pub mod primality;
pub mod residues;
pub mod siqs;

pub use error::NTheoryError;

// Arithmetic & roots
pub use arith::{
    add_mod_u64, checked_lcm, egcd, gcd, integer_nthroot, is_square, isqrt, lcm, mod_inv, mul_mod,
    perfect_power, pow_mod, sub_mod_u64, Mont64,
};

// Primality & prime counting / generation
pub use primality::{
    is_prime, is_prime_power, isprime, next_prime, nextprime, nth_prime, prev_prime, prevprime,
    prime_pi, prime_range, primepi, primerange, primorial, primorial_upto, sieve_primes, PrimeIter,
};

// Factorization
pub use factor::{factorint, pollard_rho_u64};

// Arithmetic functions
pub use functions::{
    continued_fraction, convergents, divisor_count, divisor_sigma, divisors, is_squarefree,
    mertens, mobius, prime_big_omega, prime_factors, prime_omega, proper_divisors, radical,
    reduced_totient, smooth_numbers, totient,
};

// Modular group & congruences
pub use modular::{
    binomial_mod, crt, discrete_log, is_primitive_root, n_order, nthroot_mod, nthroot_mod_all,
    primitive_root, sqrt_mod, sqrt_mod_all, sqrt_mod_prime,
};

// Residues & symbols
pub use residues::{
    is_nthpow_residue, is_quad_residue, jacobi_symbol, kronecker_symbol, legendre_symbol,
    quadratic_residues,
};

// Cyclotomic
pub use cyclotomic::{aurifeuillean_split_base10, cyclotomic_eval, cyclotomic_poly};

/// Native `u128` computational number theory operations.
pub mod u128_ops {
    pub use crate::arith::{
        add_mod_u128, checked_lcm_u128, gcd_u128, is_square_u128, isqrt_u128, mod_inv_u128,
        mul_mod_u128, mul_wide_u128, pow_mod_u128, sub_mod_u128, Mont128,
    };
    pub use crate::factor::{factorint_u128, pollard_rho_u128};
    pub use crate::functions::{mobius_u128, reduced_totient_u128, totient_u128};
    pub use crate::modular::{
        crt_u128, discrete_log_u128, n_order_u128, primitive_root_u128, sqrt_mod_prime_u128,
    };
    pub use crate::primality::{is_prime_u128, next_prime_u128, prev_prime_u128};
}

/// Arbitrary-precision (`BigUint`) number theory operations.
pub mod big {
    pub use crate::bigint::{jacobi_big, jacobi_i64_big, BigMont, BigUint};
    pub use crate::cyclotomic::{aurifeuillean_split_base10, cyclotomic_eval};
    pub use crate::factor::{
        ecm_factor, factorint_big, factorint_big_with_config, pollard_pm1, pollard_rho_big,
        FactorConfig, FactorResult,
    };
    pub use crate::functions::{
        divisor_count_big, divisor_sigma_big, divisors_big, mobius_big, reduced_totient_big,
        totient_big,
    };
    pub use crate::modular::{crt_big, n_order_big, primitive_root_big, sqrt_mod_prime_big};
    pub use crate::primality::{is_prime_big, next_prime_big, prev_prime_big, primorial};
    pub use crate::residues::{jacobi_symbol_big, jacobi_symbol_big_uint};
    pub use crate::siqs::siqs_factor;
}
