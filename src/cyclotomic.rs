//! Cyclotomic polynomials `Phi_k(x)`, exact evaluation `Phi_k(x)` as `BigUint`,
//! and base-10 Aurifeuillean factorization splits.

use crate::bigint::{BigMont, BigUint};
use crate::functions::mobius;

/// Exact coefficients `[c_0, c_1, ..., c_d]` of the `n`-th cyclotomic polynomial `Phi_n(x)`
/// (so `Phi_n(x) = sum c_i * x^i`). Panics if `n == 0`.
pub fn cyclotomic_poly(n: usize) -> Vec<i64> {
    assert!(n >= 1, "cyclotomic polynomial index n must be >= 1");
    // Exact iterative division: start with x^n - 1 and divide by all Phi_d(x) for proper d | n.
    // Cache Phi_d for divisors d of n so any n computes cleanly without exponential recursion.
    let mut divs = Vec::new();
    let mut d = 1usize;
    while d * d <= n {
        if n % d == 0 {
            divs.push(d);
            if d * d != n {
                divs.push(n / d);
            }
        }
        d += 1;
    }
    divs.sort_unstable();

    let mut polys: Vec<(usize, Vec<i64>)> = Vec::with_capacity(divs.len());
    for &cur_n in &divs {
        // Numerator = x^cur_n - 1
        let mut num = vec![0i64; cur_n + 1];
        num[0] = -1;
        num[cur_n] = 1;

        for &(prev_d, ref phi_d) in &polys {
            if cur_n % prev_d == 0 {
                // Exact monic polynomial division: num /= phi_d
                let deg_d = phi_d.len() - 1;
                let deg_num = num.len() - 1;
                let mut q = vec![0i64; deg_num - deg_d + 1];
                for i in (deg_d..=deg_num).rev() {
                    let coeff = num[i];
                    if coeff != 0 {
                        q[i - deg_d] = coeff;
                        for j in 0..=deg_d {
                            num[i - deg_d + j] -= coeff * phi_d[j];
                        }
                    }
                }
                debug_assert!(num.iter().all(|&v| v == 0));
                num = q;
            }
        }
        polys.push((cur_n, num));
    }
    polys.pop().unwrap().1
}

/// Evaluate the `k`-th cyclotomic polynomial at integer base `x >= 2`:
/// `Phi_k(x) = prod_{d | k} (x^d - 1)^{mu(k / d)}`.
pub fn cyclotomic_eval(k: u64, x: u64) -> BigUint {
    assert!(k >= 1, "cyclotomic index k must be >= 1");
    if x == 0 {
        return if k == 1 {
            BigUint::zero()
        } else {
            BigUint::one()
        };
    }
    if x == 1 {
        // Phi_1(1) = 0; Phi_{p^a}(1) = p; else 1
        return BigUint::from_u64(if k == 1 {
            0
        } else {
            crate::primality::is_prime_power(k).map_or(1, |(p, _)| p)
        });
    }
    if k == 1 {
        return BigUint::from_u64(x - 1);
    }

    let mut divs = Vec::new();
    let mut d = 1u64;
    while d * d <= k {
        if k % d == 0 {
            divs.push(d);
            if d * d != k {
                divs.push(k / d);
            }
        }
        d += 1;
    }

    let x_big = BigUint::from_u64(x);
    let mut num = BigUint::one();
    let mut den = BigUint::one();
    for d in divs {
        let mu = mobius(k / d);
        if mu == 0 {
            continue;
        }
        let mut term = x_big.pow(d as u32);
        term.sub_u64_assign(1);
        if mu == 1 {
            num = num.mul(&term);
        } else {
            den = den.mul(&term);
        }
    }
    let (q, r) = num.div_rem(&den);
    debug_assert!(r.is_zero());
    q
}

/// Base-10 Aurifeuillean algebraic split for `n | Phi_k(10)` when `k == 20 (mod 40)`.
///
/// Uses the exact identity for `k = 20 * r` (`r` odd), `x = 10^r`, `s = 10^((r+1)/2)`:
/// `Phi_20(x) = (x^4 + 5x^3 + 7x^2 + 5x + 1)^2 - (s * (x^3 + 2x^2 + 2x + 1))^2`.
pub fn aurifeuillean_split_base10(k: u64, n: &BigUint) -> Option<(BigUint, BigUint)> {
    if k % 40 != 20 || n.is_even() || n <= &BigUint::one() {
        return None;
    }
    let r = k / 20;
    let ctx = BigMont::new(n.clone());
    let ten_m = ctx.to_mont_u64(10);
    let x = ctx.pow_mont_u64(&ten_m, r);
    let s = ctx.pow_mont_u64(&ten_m, r.div_ceil(2));
    let x2 = ctx.mul_limbs(&x, &x);
    let x3 = ctx.mul_limbs(&x2, &x);
    let x4 = ctx.mul_limbs(&x2, &x2);

    let one = ctx.r1.clone();
    let two_m = ctx.to_mont_u64(2);
    let five_m = ctx.to_mont_u64(5);
    let seven_m = ctx.to_mont_u64(7);

    let mut c = ctx.add_limbs(&x4, &ctx.mul_limbs(&five_m, &x3));
    c = ctx.add_limbs(&c, &ctx.mul_limbs(&seven_m, &x2));
    c = ctx.add_limbs(&c, &ctx.mul_limbs(&five_m, &x));
    c = ctx.add_limbs(&c, &one);

    let mut d = ctx.add_limbs(&x3, &ctx.mul_limbs(&two_m, &x2));
    d = ctx.add_limbs(&d, &ctx.mul_limbs(&two_m, &x));
    d = ctx.add_limbs(&d, &one);
    d = ctx.mul_limbs(&d, &s);

    let l_big = ctx.from_mont_limbs(&ctx.sub_limbs(&c, &d));
    let g = n.gcd(&l_big);
    if !g.is_zero() && !g.is_one() && &g < n {
        let (q, rem) = n.div_rem(&g);
        debug_assert!(rem.is_zero());
        return Some((g, q));
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cyclotomic() {
        assert_eq!(cyclotomic_poly(1), vec![-1, 1]);
        assert_eq!(cyclotomic_poly(6), vec![1, -1, 1]); // x^2 - x + 1
        assert_eq!(cyclotomic_poly(12), vec![1, 0, -1, 0, 1]); // x^4 - x^2 + 1
        assert_eq!(cyclotomic_eval(17, 10).to_string(), "11111111111111111");
        let phi60 = cyclotomic_eval(60, 10);
        let (a, b) = aurifeuillean_split_base10(60, &phi60).unwrap();
        assert_eq!(a.mul(&b), phi60);
    }
}
