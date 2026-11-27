//! Showcase & quick benchmark of `sympy.ntheory`-equivalent functions across `u64`, `u128`, and `BigUint`.

use ntheory_rs::big::{cyclotomic_eval, factorint_big, is_prime_big, BigUint};
use ntheory_rs::u128_ops::{factorint_u128, n_order_u128};
use ntheory_rs::{
    continued_fraction, convergents, crt, discrete_log, divisor_sigma, divisors, factorint,
    kronecker_symbol, mertens, n_order, nth_prime, nthroot_mod_all, prime_pi, primitive_root,
    sqrt_mod_all, totient,
};
use std::time::Instant;

fn main() {
    println!("=== ntheory-rs Showcase ===");
    println!(
        "n_order(10, 5363222357) = {}",
        n_order(10, 5_363_222_357).unwrap()
    );
    println!("totient(360) = {}", totient(360));
    println!(
        "divisors(28) = {:?}, sigma_1(28) = {}",
        divisors(28),
        divisor_sigma(28, 1)
    );
    println!("primitive_root(65537) = {:?}", primitive_root(65537));
    println!("sqrt_mod_all(1, 15) = {:?}", sqrt_mod_all(1, 15).unwrap());
    println!(
        "nthroot_mod_all(1, 4, 13) = {:?}",
        nthroot_mod_all(1, 4, 13).unwrap()
    );
    println!(
        "crt([2,3,2], [3,5,7]) = {:?}",
        crt(&[2, 3, 2], &[3, 5, 7]).unwrap()
    );
    println!(
        "discrete_log(3, 13, 17) = {:?}",
        discrete_log(3, 13, 17).unwrap()
    );
    println!("kronecker_symbol(-1, 2) = {}", kronecker_symbol(-1, 2));
    println!("mertens(10000) = {}", mertens(10_000));
    let cf = continued_fraction(355, 113).unwrap();
    println!(
        "cf(355/113) = {:?}, convergents = {:?}",
        cf,
        convergents(&cf)
    );

    let t_pi = Instant::now();
    let pi_1e9 = prime_pi(1_000_000_000);
    println!(
        "\nprime_pi(10^9) = {} ({:.2} ms)",
        pi_1e9,
        t_pi.elapsed().as_secs_f64() * 1000.0
    );
    println!("nth_prime(10^6) = {:?}", nth_prime(1_000_000));

    let t_f64 = Instant::now();
    let fac64 = factorint(u64::MAX - 58);
    println!(
        "factorint(2^64 - 59) = {:?} ({:.3} ms)",
        fac64,
        t_f64.elapsed().as_secs_f64() * 1000.0
    );

    // 128-bit factorization of 2^127 - 1 (M127) and a 31-digit semiprime via SIQS/ECM
    let p = 1_000_000_000_000_037u128;
    let q = 1_000_000_000_000_091u128;
    let t_f128 = Instant::now();
    let fac128 = factorint_u128(p * q);
    println!(
        "factorint_u128(31-digit semiprime) = {:?} ({:.2} ms)",
        fac128,
        t_f128.elapsed().as_secs_f64() * 1000.0
    );
    println!(
        "n_order_u128(3, 2^127 - 1) = {}",
        n_order_u128(3, (1u128 << 127) - 1).unwrap()
    );

    // Arbitrary-precision cyclotomic factoring: Phi_43(10) (42 digits)
    let phi43 = cyclotomic_eval(43, 10);
    let t_big = Instant::now();
    let f_phi43 = factorint_big(&phi43);
    println!(
        "factorint_big(Phi_43(10)) [{} digits] = {:?} ({:.2} ms)",
        phi43.to_string().len(),
        f_phi43,
        t_big.elapsed().as_secs_f64() * 1000.0
    );
    let big_p = BigUint::from_str_radix10("11111111111111111111111").unwrap();
    println!("is_prime_big(R_23) = {}", is_prime_big(&big_p));
}
