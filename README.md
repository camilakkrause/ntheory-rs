# `ntheory-rs`

A fast, zero-dependency computational number theory library for Rust inspired by Python's `sympy.ntheory`.

## Installation

Add `ntheory-rs` directly from GitHub in your `Cargo.toml`:

```toml
[dependencies]
ntheory-rs = { git = "https://github.com/camilakkrause/ntheory-rs" }
```

Or, once published on [crates.io](https://crates.io):

```toml
[dependencies]
ntheory-rs = "0.1"
```

## Quick Start

```rust
use ntheory_rs::{n_order, factorint, is_prime, prime_pi, totient, crt, discrete_log};

fn main() {
    assert!(is_prime(18_371_524_594_609));
    assert_eq!(n_order(10, 5_363_222_357).unwrap(), 17);
    assert_eq!(prime_pi(1_000_000), 78_498);
    assert_eq!(totient(36), 12);
    assert_eq!(crt(&[2, 3, 2], &[3, 5, 7]).unwrap(), Some((23, 105)));
    assert_eq!(discrete_log(3, 13, 17).unwrap(), Some(4));

    let factors = factorint(360);
    assert_eq!(factors[&2], 3);
}
```

## Features

- **Zero external dependencies** — pure Rust (`std` only), compiles cleanly with `cargo build --release`.
- **Three integer tiers:**
  - **Root (`u64`)**: Hardware-speed 64-bit subtraction-REDC Montgomery arithmetic and deterministic 7-base Miller-Rabin.
  - **[`u128_ops`](src/lib.rs) (`u128`)**: Native 128-bit Montgomery arithmetic (`Mont128`), Baillie-PSW primality, and seamless ECM/SIQS escalation for factoring hard 38-digit semiprimes.
  - **[`big`](src/lib.rs) (`BigUint`)**: Built-in arbitrary-precision unsigned integers with Knuth Algorithm D division, Karatsuba multiplication, CIOS Montgomery (`BigMont`), Baillie-PSW primality, Brent-Pollard Rho, Pollard $p - 1$, Montgomery ECM (Suyama curves, Stage 1 + Stage 2 BSGS), and Self-Initializing Quadratic Sieve (SIQS).
- **Sublinear prime counting:** Meissel-Lehmer `prime_pi` / `primepi` and Dusart-bounded `nth_prime`, plus a lazy 32 KB segmented-sieve `PrimeIter` (`primerange`).
- **Complete modular toolkit:** `n_order`, `primitive_root`, `is_primitive_root`, `sqrt_mod` / `sqrt_mod_all` (for prime, prime-power, and composite moduli), generalized `crt`, `discrete_log` (Pohlig-Hellman + BSGS + Pollard Rho), `nthroot_mod_all`, and `binomial_mod`.

## SymPy (`sympy.ntheory`) API Mapping

| SymPy (`sympy.ntheory`) | `ntheory-rs` (`u64`) | `u128` / `BigUint` |
|---|---|---|
| `isprime(n)` | `is_prime(n)` / `isprime(n)` | `u128_ops::is_prime_u128`, `big::is_prime_big` |
| `nextprime(n)` / `prevprime(n)` | `next_prime(n)` / `prev_prime(n)` | `next_prime_u128`, `next_prime_big`, etc. |
| `primepi(n)` / `primerange(a, b)` | `prime_pi(n)` / `prime_range(a, b)` / `PrimeIter` | — |
| `prime(n)` | `nth_prime(n)` | — |
| `factorint(n)` | `factorint(n)` | `u128_ops::factorint_u128`, `big::factorint_big` |
| `n_order(a, n)` | `n_order(a, n)` | `u128_ops::n_order_u128`, `big::n_order_big` |
| `primitive_root(n)` / `is_primitive_root(a, n)` | `primitive_root(n)` / `is_primitive_root(a, n)` | `primitive_root_u128`, `primitive_root_big` |
| `totient(n)` / `reduced_totient(n)` | `totient(n)` / `reduced_totient(n)` | `totient_u128`, `totient_big`, etc. |
| `mobius(n)` / `divisors(n)` / `divisor_sigma(n, k)` | `mobius`, `divisors`, `divisor_sigma` | `mobius_big`, `divisors_big`, `divisor_sigma_big` |
| `legendre_symbol` / `jacobi_symbol` / `kronecker_symbol` | `legendre_symbol`, `jacobi_symbol`, `kronecker_symbol` | `big::jacobi_symbol_big` |
| `sqrt_mod(a, n, all_roots=...)` | `sqrt_mod(a, n)` / `sqrt_mod_all(a, n)` | `sqrt_mod_prime_u128`, `sqrt_mod_prime_big` |
| `crt(m, v)` | `crt(remainders, moduli)` | `u128_ops::crt_u128`, `big::crt_big` |
| `discrete_log(n, a, b)` | `discrete_log(base, target, modulus)` | `u128_ops::discrete_log_u128` |
| `nthroot_mod(a, n, p, all_roots=...)` | `nthroot_mod(a, r, p)` / `nthroot_mod_all(a, r, p)` | — |
| `cyclotomic_poly(n, x)` | `cyclotomic_poly(n)` / `cyclotomic_eval(k, x)` | `big::cyclotomic_eval(k, x)` |

## Build & Verify

```powershell
cargo test --release
cargo doc --no-deps
cargo run --release --example a243110_demo
cargo run --release --example sympy_comparison
```

## License

Licensed under either of

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE))
- MIT License ([LICENSE-MIT](LICENSE-MIT))

at your option.
