//! Classical arithmetic functions: Euler's totient, Carmichael's lambda, Mobius, Mertens,
//! divisors, divisor sigma, prime omega functions, continued fractions, and smooth numbers.

use crate::arith::{checked_lcm_u128, lcm};
use crate::bigint::BigUint;
use crate::error::NTheoryError;
use crate::factor::{factorint, factorint_big, factorint_u128};
use crate::primality::sieve_primes;

/// Euler's totient function `phi(n)` for `u64` (`phi(0) == 0`, `phi(1) == 1`).
pub fn totient(n: u64) -> u64 {
    if n <= 1 {
        return n;
    }
    let mut res = n;
    for (p, _) in factorint(n) {
        res = res / p * (p - 1);
    }
    res
}

/// Euler's totient function `phi(n)` for `u128`.
pub fn totient_u128(n: u128) -> u128 {
    if n <= 1 {
        return n;
    }
    let mut res = n;
    for (p, _) in factorint_u128(n) {
        res = res / p * (p - 1);
    }
    res
}

/// Euler's totient function `phi(n)` for `BigUint`.
pub fn totient_big(n: &BigUint) -> BigUint {
    if n.is_zero() || n.is_one() {
        return n.clone();
    }
    let mut res = n.clone();
    for (p, _) in factorint_big(n) {
        let (q, _) = res.div_rem(&p);
        let mut pm1 = p;
        pm1.sub_u64_assign(1);
        res = q.mul(&pm1);
    }
    res
}

/// Carmichael's reduced totient function `lambda(n)` (`lambda(0) == 0`, `lambda(1) == 1`).
pub fn reduced_totient(n: u64) -> u64 {
    if n <= 1 {
        return n;
    }
    let mut lam = 1u64;
    for (p, e) in factorint(n) {
        let lp = if p == 2 {
            if e == 1 {
                1
            } else if e == 2 {
                2
            } else {
                1u64 << (e - 2)
            }
        } else {
            p.pow(e - 1) * (p - 1)
        };
        lam = lcm(lam, lp);
    }
    lam
}

/// Carmichael's reduced totient function `lambda(n)` for `u128`.
pub fn reduced_totient_u128(n: u128) -> u128 {
    if n <= 1 {
        return n;
    }
    let mut lam = 1u128;
    for (p, e) in factorint_u128(n) {
        let lp = if p == 2 {
            if e == 1 {
                1
            } else if e == 2 {
                2
            } else {
                1u128 << (e - 2)
            }
        } else {
            p.pow(e - 1) * (p - 1)
        };
        lam = checked_lcm_u128(lam, lp).expect("reduced_totient_u128 overflow");
    }
    lam
}

/// Carmichael's reduced totient function `lambda(n)` for `BigUint`.
pub fn reduced_totient_big(n: &BigUint) -> BigUint {
    if n.is_zero() || n.is_one() {
        return n.clone();
    }
    let mut lam = BigUint::one();
    let two = BigUint::from_u64(2);
    for (p, e) in factorint_big(n) {
        let lp = if p == two {
            if e == 1 {
                BigUint::one()
            } else if e == 2 {
                BigUint::from_u64(2)
            } else {
                BigUint::one().shl((e - 2) as usize)
            }
        } else {
            let mut pm1 = p.clone();
            pm1.sub_u64_assign(1);
            p.pow(e - 1).mul(&pm1)
        };
        lam = lam.lcm(&lp);
    }
    lam
}

/// Mobius function `mu(n)` (`mu(1) == 1`, `0` if not squarefree, `(-1)^k` for `k` distinct primes).
pub fn mobius(n: u64) -> i8 {
    if n == 0 {
        return 0;
    }
    if n == 1 {
        return 1;
    }
    let fac = factorint(n);
    for &e in fac.values() {
        if e > 1 {
            return 0;
        }
    }
    if fac.len() & 1 == 1 {
        -1
    } else {
        1
    }
}

/// Mobius function `mu(n)` for `u128`.
pub fn mobius_u128(n: u128) -> i8 {
    if n == 0 {
        return 0;
    }
    if n == 1 {
        return 1;
    }
    let fac = factorint_u128(n);
    for &e in fac.values() {
        if e > 1 {
            return 0;
        }
    }
    if fac.len() & 1 == 1 {
        -1
    } else {
        1
    }
}

/// Mobius function `mu(n)` for `BigUint`.
pub fn mobius_big(n: &BigUint) -> i8 {
    if n.is_zero() {
        return 0;
    }
    if n.is_one() {
        return 1;
    }
    let fac = factorint_big(n);
    for &e in fac.values() {
        if e > 1 {
            return 0;
        }
    }
    if fac.len() & 1 == 1 {
        -1
    } else {
        1
    }
}

/// Mertens function `M(n) = sum_{k=1..=n} mu(k)` computed via linear sieve.
pub fn mertens(n: usize) -> i64 {
    if n == 0 {
        return 0;
    }
    let mut mu = vec![0i8; n + 1];
    let mut is_comp = vec![false; n + 1];
    let mut primes = Vec::new();
    mu[1] = 1;
    let mut sum = 1i64;
    for i in 2..=n {
        if !is_comp[i] {
            primes.push(i);
            mu[i] = -1;
        }
        sum += mu[i] as i64;
        for &p in &primes {
            let ip = i * p;
            if ip > n {
                break;
            }
            is_comp[ip] = true;
            if i % p == 0 {
                mu[ip] = 0;
                break;
            } else {
                mu[ip] = -mu[i];
            }
        }
    }
    sum
}

/// All positive divisors of `n` in ascending order (`divisors(0) == []`).
pub fn divisors(n: u64) -> Vec<u64> {
    if n == 0 {
        return Vec::new();
    }
    let mut divs = vec![1u64];
    for (p, e) in factorint(n) {
        let cur_len = divs.len();
        let mut pk = p;
        for _ in 0..e {
            for i in 0..cur_len {
                divs.push(divs[i] * pk);
            }
            pk = pk.saturating_mul(p);
        }
    }
    divs.sort_unstable();
    divs
}

/// All proper positive divisors of `n` (all divisors `< n`) in ascending order.
pub fn proper_divisors(n: u64) -> Vec<u64> {
    let mut d = divisors(n);
    if !d.is_empty() {
        d.pop();
    }
    d
}

/// Number of positive divisors `tau(n) = d(n)`.
pub fn divisor_count(n: u64) -> u64 {
    if n == 0 {
        return 0;
    }
    factorint(n).values().map(|&e| (e as u64) + 1).product()
}

/// Sum of `k`-th powers of positive divisors `sigma_k(n) = sum_{d | n} d^k`.
pub fn divisor_sigma(n: u64, k: u32) -> u128 {
    if n == 0 {
        return 0;
    }
    if k == 0 {
        return divisor_count(n) as u128;
    }
    let mut res = 1u128;
    for (p, e) in factorint(n) {
        let pk = (p as u128).pow(k);
        let mut sum_p = 1u128;
        let mut term = 1u128;
        for _ in 0..e {
            term *= pk;
            sum_p += term;
        }
        res *= sum_p;
    }
    res
}

/// All positive divisors of `BigUint` `n` in ascending order.
pub fn divisors_big(n: &BigUint) -> Vec<BigUint> {
    if n.is_zero() {
        return Vec::new();
    }
    let mut divs = vec![BigUint::one()];
    for (p, e) in factorint_big(n) {
        let cur_len = divs.len();
        let mut pk = p.clone();
        for _ in 0..e {
            for i in 0..cur_len {
                divs.push(divs[i].mul(&pk));
            }
            pk = pk.mul(&p);
        }
    }
    divs.sort();
    divs
}

/// Number of positive divisors of `BigUint` `n`.
pub fn divisor_count_big(n: &BigUint) -> BigUint {
    if n.is_zero() {
        return BigUint::zero();
    }
    let mut res = BigUint::one();
    for &e in factorint_big(n).values() {
        res.mul_u64_assign((e as u64) + 1);
    }
    res
}

/// Sum of `k`-th powers of positive divisors `sigma_k(n)` for `BigUint`.
pub fn divisor_sigma_big(n: &BigUint, k: u32) -> BigUint {
    if n.is_zero() {
        return BigUint::zero();
    }
    if k == 0 {
        return divisor_count_big(n);
    }
    let mut res = BigUint::one();
    for (p, e) in factorint_big(n) {
        let pk = p.pow(k);
        let mut sum_p = BigUint::one();
        let mut term = BigUint::one();
        for _ in 0..e {
            term = term.mul(&pk);
            sum_p = sum_p.add(&term);
        }
        res = res.mul(&sum_p);
    }
    res
}

/// Sorted distinct prime factors of `n` (matching SymPy `primefactors(n)`).
pub fn prime_factors(n: u64) -> Vec<u64> {
    factorint(n).into_keys().collect()
}

/// Number of distinct prime factors `omega(n)` (`primefactors(n).len()`).
pub fn prime_omega(n: u64) -> u32 {
    factorint(n).len() as u32
}

/// Total number of prime factors counted with multiplicity `Omega(n)`.
pub fn prime_big_omega(n: u64) -> u32 {
    factorint(n).values().sum()
}

/// Radical of `n`: product of distinct prime divisors of `n` (`radical(0) == 0`, `radical(1) == 1`).
pub fn radical(n: u64) -> u64 {
    if n <= 1 {
        return n;
    }
    factorint(n).into_keys().product()
}

/// Returns `true` iff `n >= 1` is not divisible by the square of any prime.
pub fn is_squarefree(n: u64) -> bool {
    if n == 0 {
        return false;
    }
    factorint(n).values().all(|&e| e == 1)
}

/// Canonical continued fraction `[a_0; a_1, ..., a_m]` of rational `num / den` (`den != 0`).
pub fn continued_fraction(mut num: i64, mut den: i64) -> Result<Vec<i64>, NTheoryError> {
    if den == 0 {
        return Err(NTheoryError::InvalidArgument(
            "denominator must be non-zero",
        ));
    }
    if den < 0 {
        num = num.checked_neg().ok_or(NTheoryError::Overflow)?;
        den = den.checked_neg().ok_or(NTheoryError::Overflow)?;
    }
    let mut cf = Vec::new();
    while den != 0 {
        let q = num.div_euclid(den);
        let r = num.rem_euclid(den);
        cf.push(q);
        num = den;
        den = r;
    }
    Ok(cf)
}

/// Sequence of convergents `(p_k, q_k)` of a continued fraction `[a_0; a_1, ...]`.
pub fn convergents(cf: &[i64]) -> Vec<(i128, i128)> {
    let mut out = Vec::with_capacity(cf.len());
    let mut p_prev2 = 0i128;
    let mut p_prev1 = 1i128;
    let mut q_prev2 = 1i128;
    let mut q_prev1 = 0i128;
    for &a in cf {
        let ai = a as i128;
        let p = ai * p_prev1 + p_prev2;
        let q = ai * q_prev1 + q_prev2;
        out.push((p, q));
        p_prev2 = p_prev1;
        p_prev1 = p;
        q_prev2 = q_prev1;
        q_prev1 = q;
    }
    out
}

/// Generate all `max_prime`-smooth positive integers `<= limit`, sorted ascending.
pub fn smooth_numbers(max_prime: u64, limit: u64) -> Vec<u64> {
    if limit == 0 {
        return Vec::new();
    }
    let mut out = vec![1u64];
    if max_prime < 2 {
        return out;
    }
    let primes = sieve_primes(max_prime as usize);
    for p in primes {
        let len = out.len();
        for i in 0..len {
            let mut val = out[i];
            while let Some(next) = val.checked_mul(p) {
                if next > limit {
                    break;
                }
                out.push(next);
                val = next;
            }
        }
    }
    out.sort_unstable();
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_arith_functions() {
        assert_eq!(totient(36), 12);
        assert_eq!(reduced_totient(16), 4);
        assert_eq!(reduced_totient(36), 6);
        assert_eq!(mobius(30), -1);
        assert_eq!(mobius(12), 0);
        assert_eq!(mertens(100), 1);
        assert_eq!(divisors(28), vec![1, 2, 4, 7, 14, 28]);
        assert_eq!(divisor_sigma(28, 1), 56);
        assert_eq!(prime_omega(360), 3);
        assert_eq!(prime_big_omega(360), 6);
        assert_eq!(radical(360), 30);
        assert!(!is_squarefree(12));
        assert!(is_squarefree(30));

        // -7/3 = -3 + 1/(1 + 1/2) -> [-3, 1, 2]
        let cf = continued_fraction(-7, 3).unwrap();
        assert_eq!(cf, vec![-3, 1, 2]);
        assert_eq!(convergents(&cf).last(), Some(&(-7, 3)));
        assert_eq!(
            smooth_numbers(5, 16),
            vec![1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 16]
        );
    }
}
