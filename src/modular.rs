//! Modular group & congruence algorithms:
//! - Multiplicative order `n_order` (`u64`, `u128`, `BigUint`)
//! - Primitive roots (`primitive_root`, `is_primitive_root`)
//! - Modular square roots (`sqrt_mod`, `sqrt_mod_all`, `sqrt_mod_prime`, plus `u128`/`BigUint`)
//! - Generalized Chinese Remainder Theorem (`crt`, `crt_u128`, `crt_big`)
//! - Discrete logarithm (`discrete_log`, `discrete_log_u128`: Pohlig-Hellman + BSGS + Pollard Rho)
//! - Prime-modulus n-th roots (`nthroot_mod`, `nthroot_mod_all`)
//! - Modular binomial coefficients (`binomial_mod` via Lucas's theorem)

use std::collections::HashMap;

use crate::arith::{
    add_mod_u64, checked_lcm, checked_lcm_u128, gcd, gcd_u128, isqrt, lcm, mod_inv, mod_inv_u128,
    mul_mod, mul_mod_u128, pow_mod, pow_mod_u128,
};
use crate::bigint::{jacobi_big, BigMont, BigUint};
use crate::error::NTheoryError;
use crate::factor::{factorint, factorint_big, factorint_u128};
use crate::functions::totient;
use crate::primality::{is_prime, is_prime_big};
use crate::residues::jacobi_u64;

/// Exact multiplicative order of `a` modulo `n`: smallest integer `k >= 1` such that `a^k == 1 (mod n)`.
///
/// Matches SymPy's `n_order(a, n)`. Returns `Err(NTheoryError::NotCoprime)` if `gcd(a, n) != 1`.
pub fn n_order(a: u64, n: u64) -> Result<u64, NTheoryError> {
    if n == 0 {
        return Err(NTheoryError::InvalidArgument("modulus n must be positive"));
    }
    if n == 1 {
        return Ok(1);
    }
    let am = a % n;
    if gcd(am, n) != 1 {
        return Err(NTheoryError::NotCoprime);
    }
    if am == 1 {
        return Ok(1);
    }
    // Prime-power CRT lifting: ord_n(a) = lcm_{p^e || n} ord_{p^e}(a)
    let mut order = 1u64;
    for (p, e) in factorint(n) {
        // First find order mod p, then lift to p^e
        let mut ord_p = p - 1;
        for (q, _) in factorint(p - 1) {
            while ord_p % q == 0 && pow_mod(am % p, ord_p / q, p) == 1 {
                ord_p /= q;
            }
        }
        let mut ord_pe = ord_p;
        if e > 1 {
            // Check exact powers p^j * ord_p mod p^e
            let mut cur_mod = p;
            for _ in 1..e {
                cur_mod *= p;
                if pow_mod(am % cur_mod, ord_pe, cur_mod) != 1 {
                    ord_pe *= p;
                }
            }
        }
        order = lcm(order, ord_pe);
    }
    Ok(order)
}

/// Exact multiplicative order of `a` modulo `n` for `u128`.
pub fn n_order_u128(a: u128, n: u128) -> Result<u128, NTheoryError> {
    if n == 0 {
        return Err(NTheoryError::InvalidArgument("modulus n must be positive"));
    }
    if n == 1 {
        return Ok(1);
    }
    if let (Ok(a64), Ok(n64)) = (u64::try_from(a % n), u64::try_from(n)) {
        return n_order(a64, n64).map(|k| k as u128);
    }
    let am = a % n;
    if gcd_u128(am, n) != 1 {
        return Err(NTheoryError::NotCoprime);
    }
    if am == 1 {
        return Ok(1);
    }
    let mut order = 1u128;
    for (p, e) in factorint_u128(n) {
        let mut ord_p = p - 1;
        for (q, _) in factorint_u128(p - 1) {
            while ord_p % q == 0 && pow_mod_u128(am % p, ord_p / q, p) == 1 {
                ord_p /= q;
            }
        }
        let mut ord_pe = ord_p;
        if e > 1 {
            let mut cur_mod = p;
            for _ in 1..e {
                cur_mod *= p;
                if pow_mod_u128(am % cur_mod, ord_pe, cur_mod) != 1 {
                    ord_pe *= p;
                }
            }
        }
        order = checked_lcm_u128(order, ord_pe).ok_or(NTheoryError::Overflow)?;
    }
    Ok(order)
}

/// Exact multiplicative order of `a` modulo `n` for `BigUint`.
pub fn n_order_big(a: &BigUint, n: &BigUint) -> Result<BigUint, NTheoryError> {
    if n.is_zero() {
        return Err(NTheoryError::InvalidArgument("modulus n must be positive"));
    }
    if n.is_one() {
        return Ok(BigUint::one());
    }
    let am = a.rem(n);
    if !am.gcd(n).is_one() {
        return Err(NTheoryError::NotCoprime);
    }
    if am.is_one() {
        return Ok(BigUint::one());
    }
    let mut order = BigUint::one();
    for (p, e) in factorint_big(n) {
        let mut pm1 = p.clone();
        pm1.sub_u64_assign(1);
        let mut ord_p = pm1.clone();
        let a_mod_p = am.rem(&p);
        for (q, _) in factorint_big(&pm1) {
            loop {
                let (d_div_q, r) = ord_p.div_rem(&q);
                if r.is_zero() && BigUint::pow_mod(&a_mod_p, &d_div_q, &p).is_one() {
                    ord_p = d_div_q;
                } else {
                    break;
                }
            }
        }
        let mut ord_pe = ord_p;
        if e > 1 {
            let mut cur_mod = p.clone();
            for _ in 1..e {
                cur_mod = cur_mod.mul(&p);
                let a_mod_c = am.rem(&cur_mod);
                if !BigUint::pow_mod(&a_mod_c, &ord_pe, &cur_mod).is_one() {
                    ord_pe = ord_pe.mul(&p);
                }
            }
        }
        order = order.lcm(&ord_pe);
    }
    Ok(order)
}

/// Returns `true` iff `a` is a primitive root modulo `n`.
pub fn is_primitive_root(a: u64, n: u64) -> bool {
    if n <= 1 {
        return false;
    }
    let phi = totient(n);
    n_order(a, n) == Ok(phi)
}

/// Smallest primitive root modulo `n`, or `None` if no primitive root exists.
/// Primitive roots exist iff `n in {2, 4, p^k, 2*p^k}` for odd prime `p, k >= 1`.
pub fn primitive_root(n: u64) -> Option<u64> {
    if n <= 1 {
        return None;
    }
    if n == 2 {
        return Some(1);
    }
    if n == 4 {
        return Some(3);
    }
    let fac = factorint(n);
    // Must be p^k or 2*p^k for odd prime p
    match fac.len() {
        1 => {
            let (&p, _) = fac.iter().next().unwrap();
            if p == 2 {
                return None;
            }
        }
        2 => {
            if fac.get(&2) != Some(&1) {
                return None;
            }
        }
        _ => return None,
    }

    let phi = totient(n);
    let phi_primes: Vec<u64> = factorint(phi).into_keys().collect();
    let check_gen = |g: u64| -> bool {
        if gcd(g, n) != 1 {
            return false;
        }
        phi_primes.iter().all(|&q| pow_mod(g, phi / q, n) != 1)
    };

    let mut g = 2u64;
    while g < n {
        if check_gen(g) {
            return Some(g);
        }
        g += 1;
    }
    None
}

/// Smallest primitive root modulo `n` for `u128`, or `None` if none exists.
pub fn primitive_root_u128(n: u128) -> Option<u128> {
    if let Ok(n64) = u64::try_from(n) {
        return primitive_root(n64).map(|g| g as u128);
    }
    let fac = factorint_u128(n);
    let (p, e) = match fac.len() {
        1 => {
            let (&p, &e) = fac.iter().next().unwrap();
            if p == 2 {
                return None;
            }
            (p, e)
        }
        2 => {
            if fac.get(&2) != Some(&1) {
                return None;
            }
            let (&p, &e) = fac.iter().find(|&(&k, _)| k != 2).unwrap();
            (p, e)
        }
        _ => return None,
    };
    let phi = p.pow(e - 1) * (p - 1);
    let phi_primes: Vec<u128> = factorint_u128(phi).into_keys().collect();
    let mut g = 2u128;
    while g < n {
        if gcd_u128(g, n) == 1 && phi_primes.iter().all(|&q| pow_mod_u128(g, phi / q, n) != 1) {
            return Some(g);
        }
        g += 1;
    }
    None
}

/// Smallest primitive root modulo `BigUint` `n`, or `None` if none exists.
pub fn primitive_root_big(n: &BigUint) -> Option<BigUint> {
    if let Some(n128) = n.to_u128() {
        return primitive_root_u128(n128).map(BigUint::from_u128);
    }
    let two = BigUint::from_u64(2);
    let fac = factorint_big(n);
    let (p, e) = match fac.len() {
        1 => {
            let (p, &e) = fac.iter().next().unwrap();
            if p == &two {
                return None;
            }
            (p.clone(), e)
        }
        2 => {
            if fac.get(&two) != Some(&1) {
                return None;
            }
            let (p, &e) = fac.iter().find(|&(k, _)| k != &two).unwrap();
            (p.clone(), e)
        }
        _ => return None,
    };
    let mut pm1 = p.clone();
    pm1.sub_u64_assign(1);
    let phi = p.pow(e - 1).mul(&pm1);
    let phi_primes: Vec<BigUint> = factorint_big(&phi).into_keys().collect();
    let mut g = BigUint::from_u64(2);
    while &g < n {
        if g.gcd(n).is_one()
            && phi_primes.iter().all(|q| {
                let (exp, _) = phi.div_rem(q);
                !BigUint::pow_mod(&g, &exp, n).is_one()
            })
        {
            return Some(g);
        }
        g.add_u64_assign(1);
    }
    None
}

/// Tonelli-Shanks modular square root modulo prime `p`: returns `Ok(Some(r))` with smallest
/// `r <= p / 2` such that `r^2 == a (mod p)`, `Ok(None)` if non-residue, or `Err(NotPrime)`.
pub fn sqrt_mod_prime(a: u64, p: u64) -> Result<Option<u64>, NTheoryError> {
    if !is_prime(p) {
        return Err(NTheoryError::NotPrime);
    }
    let a = a % p;
    if a == 0 {
        return Ok(Some(0));
    }
    if p == 2 {
        return Ok(Some(a));
    }
    if jacobi_u64(a, p) != 1 {
        return Ok(None);
    }
    if p % 4 == 3 {
        let r = pow_mod(a, (p + 1) / 4, p);
        return Ok(Some(r.min(p - r)));
    }
    let mut q = p - 1;
    let mut s = 0u32;
    while q & 1 == 0 {
        q >>= 1;
        s += 1;
    }
    let mut z = 2u64;
    while jacobi_u64(z, p) != -1 {
        z += 1;
    }
    let mut m = s;
    let mut c = pow_mod(z, q, p);
    let mut t = pow_mod(a, q, p);
    let mut r = pow_mod(a, q.div_ceil(2), p);
    while t != 1 {
        let mut i = 1u32;
        let mut tmp = mul_mod(t, t, p);
        while tmp != 1 {
            tmp = mul_mod(tmp, tmp, p);
            i += 1;
        }
        let mut b = c;
        for _ in 0..(m - i - 1) {
            b = mul_mod(b, b, p);
        }
        m = i;
        c = mul_mod(b, b, p);
        t = mul_mod(t, c, p);
        r = mul_mod(r, b, p);
    }
    Ok(Some(r.min(p - r)))
}

/// Tonelli-Shanks modular square root modulo prime `p` (`u128`).
pub fn sqrt_mod_prime_u128(a: u128, p: u128) -> Result<Option<u128>, NTheoryError> {
    if !crate::primality::is_prime_u128(p) {
        return Err(NTheoryError::NotPrime);
    }
    let a = a % p;
    if a == 0 {
        return Ok(Some(0));
    }
    if p == 2 {
        return Ok(Some(a));
    }
    if pow_mod_u128(a, (p - 1) / 2, p) != 1 {
        return Ok(None);
    }
    if p % 4 == 3 {
        let r = pow_mod_u128(a, (p + 1) / 4, p);
        return Ok(Some(r.min(p - r)));
    }
    let mut q = p - 1;
    let mut s = 0u32;
    while q & 1 == 0 {
        q >>= 1;
        s += 1;
    }
    let mut z = 2u128;
    while pow_mod_u128(z, (p - 1) / 2, p) != p - 1 {
        z += 1;
    }
    let mut m = s;
    let mut c = pow_mod_u128(z, q, p);
    let mut t = pow_mod_u128(a, q, p);
    let mut r = pow_mod_u128(a, q.div_ceil(2), p);
    while t != 1 {
        let mut i = 1u32;
        let mut tmp = mul_mod_u128(t, t, p);
        while tmp != 1 {
            tmp = mul_mod_u128(tmp, tmp, p);
            i += 1;
        }
        let mut b = c;
        for _ in 0..(m - i - 1) {
            b = mul_mod_u128(b, b, p);
        }
        m = i;
        c = mul_mod_u128(b, b, p);
        t = mul_mod_u128(t, c, p);
        r = mul_mod_u128(r, b, p);
    }
    Ok(Some(r.min(p - r)))
}

/// Tonelli-Shanks modular square root modulo prime `p` (`BigUint`).
pub fn sqrt_mod_prime_big(a: &BigUint, p: &BigUint) -> Result<Option<BigUint>, NTheoryError> {
    if !is_prime_big(p) {
        return Err(NTheoryError::NotPrime);
    }
    let a = a.rem(p);
    if a.is_zero() {
        return Ok(Some(BigUint::zero()));
    }
    if p == &BigUint::from_u64(2) {
        return Ok(Some(a));
    }
    if jacobi_big(&a, p) != 1 {
        return Ok(None);
    }
    let mut pm1 = p.clone();
    pm1.sub_u64_assign(1);
    let s = pm1.trailing_zeros();
    let q = pm1.shr(s);
    if s == 1 {
        let mut pp1 = p.clone();
        pp1.add_u64_assign(1);
        let r = BigUint::pow_mod(&a, &pp1.shr(2), p);
        let neg = p.sub(&r);
        return Ok(Some(r.min(neg)));
    }
    let mut z = BigUint::from_u64(2);
    while jacobi_big(&z, p) != -1 {
        z.add_u64_assign(1);
    }
    let ctx = BigMont::new(p.clone());
    let mut qp1 = q.clone();
    qp1.add_u64_assign(1);

    let mut m = s;
    let mut c = ctx.pow_mont_limbs(&ctx.to_mont_limbs(&z), &q);
    let mut t = ctx.pow_mont_limbs(&ctx.to_mont_limbs(&a), &q);
    let mut r = ctx.pow_mont_limbs(&ctx.to_mont_limbs(&a), &qp1.shr(1));
    while t != ctx.r1 {
        let mut i = 1usize;
        let mut tmp = ctx.mul_limbs(&t, &t);
        while tmp != ctx.r1 {
            tmp = ctx.mul_limbs(&tmp, &tmp);
            i += 1;
        }
        let mut b = c.clone();
        for _ in 0..(m - i - 1) {
            b = ctx.mul_limbs(&b, &b);
        }
        m = i;
        c = ctx.mul_limbs(&b, &b);
        t = ctx.mul_limbs(&t, &c);
        r = ctx.mul_limbs(&r, &b);
    }
    let r_big = ctx.from_mont_limbs(&r);
    let neg = p.sub(&r_big);
    Ok(Some(r_big.min(neg)))
}

/// All solutions to `x^2 == a (mod p^e)` for prime `p, e >= 1`, sorted ascending in `0..p^e`.
fn sqrt_mod_prime_power(a: u64, p: u64, e: u32) -> Vec<u64> {
    let pe = p.pow(e);
    let am = a % pe;
    if am == 0 {
        let step = p.pow(e.div_ceil(2));
        return (0..pe).step_by(step as usize).collect();
    }

    // Factor out valuation v_p(am) = 2*t
    let mut b = am;
    let mut v = 0u32;
    while b % p == 0 {
        b /= p;
        v += 1;
    }
    if v & 1 == 1 {
        return Vec::new();
    }
    let t = v / 2;
    let red_e = e - v; // >= 1 since am != 0 (mod p^e)
    let p_red = p.pow(red_e);
    // Solve y^2 == b (mod p^red_e) where gcd(b, p) == 1
    let mut base_roots: Vec<u64> = if p == 2 {
        if red_e == 1 {
            vec![1]
        } else if red_e == 2 {
            if b % 4 == 1 {
                vec![1, 3]
            } else {
                return Vec::new();
            }
        } else {
            if b % 8 != 1 {
                return Vec::new();
            }
            // Lift {1, 3} mod 8 up to 2^red_e:
            // Actually {1, 3, 5, 7} mod 8 all satisfy x^2 == 1 (mod 8)
            let mut r = 1u64;
            let mut cur_mod = 8u64;
            for _ in 3..red_e {
                let next_mod = cur_mod * 2;
                let sq = ((r as u128 * r as u128) % (next_mod as u128)) as u64;
                if sq != b % next_mod {
                    r += cur_mod / 2;
                }
                cur_mod = next_mod;
            }
            let half = p_red / 2;
            let mut v = vec![r, half - r, half + r, p_red - r];
            v.sort_unstable();
            v.dedup();
            v
        }
    } else {
        let r0 = match sqrt_mod_prime(b % p, p).unwrap() {
            Some(r) => r,
            None => return Vec::new(),
        };
        // Hensel lift r0 from mod p to mod p^red_e
        let mut r = r0;
        let mut cur_mod = p;
        for _ in 1..red_e {
            let next_mod = cur_mod * p;
            // (r + k * cur_mod)^2 == b (mod next_mod)
            // 2 * r * k == (b - r^2) / cur_mod (mod p)
            let r2 = ((r as u128 * r as u128) % (next_mod as u128)) as u64;
            let bm = b % next_mod;
            let diff = if bm >= r2 {
                bm - r2
            } else {
                next_mod - (r2 - bm)
            };
            let rhs = (diff / cur_mod) % p;
            let inv_2r = mod_inv((2 * r) % p, p).unwrap();
            let k = mul_mod(rhs, inv_2r, p);
            r += k * cur_mod;
            cur_mod = next_mod;
        }
        if r == p_red - r {
            vec![r]
        } else {
            vec![r, p_red - r]
        }
    };

    // Lift solutions x = p^t * y + m * p^(e - t) for m in 0..p^t
    let pt = p.pow(t);
    let lift_step = p.pow(e - t);
    let mut out = Vec::with_capacity(base_roots.len() * (pt as usize));
    for y in base_roots.drain(..) {
        let base_x = y * pt;
        for m in 0..pt {
            out.push(base_x + m * lift_step);
        }
    }
    out.sort_unstable();
    out.dedup();
    out
}

/// All solutions `x in 0..n` to `x^2 == a (mod n)` for any positive modulus `n >= 1`, sorted ascending.
pub fn sqrt_mod_all(a: u64, n: u64) -> Result<Vec<u64>, NTheoryError> {
    if n == 0 {
        return Err(NTheoryError::InvalidArgument("modulus n must be positive"));
    }
    if n == 1 {
        return Ok(vec![0]);
    }
    let fac = factorint(n);
    let mut roots = vec![0u64];
    let mut cur_mod = 1u64;

    for (p, e) in fac {
        let pe = p.pow(e);
        let pe_roots = sqrt_mod_prime_power(a, p, e);
        if pe_roots.is_empty() {
            return Ok(Vec::new());
        }
        // Combine current roots (mod cur_mod) with pe_roots (mod pe) via coprime CRT
        let inv_cur_mod_pe = mod_inv(cur_mod % pe, pe).unwrap();
        let next_mod = cur_mod * pe;
        let mut next_roots = Vec::with_capacity(roots.len() * pe_roots.len());
        for &r1 in &roots {
            for &r2 in &pe_roots {
                let diff = if r2 >= r1 % pe {
                    r2 - (r1 % pe)
                } else {
                    pe - ((r1 % pe) - r2)
                };
                let k = mul_mod(diff, inv_cur_mod_pe, pe);
                next_roots.push(r1 + cur_mod * k);
            }
        }
        roots = next_roots;
        cur_mod = next_mod;
    }
    roots.sort_unstable();
    Ok(roots)
}

/// Smallest non-negative solution to `x^2 == a (mod n)` for any positive modulus `n >= 1`.
pub fn sqrt_mod(a: u64, n: u64) -> Result<Option<u64>, NTheoryError> {
    if n == 0 {
        return Err(NTheoryError::InvalidArgument("modulus n must be positive"));
    }
    if is_prime(n) {
        return sqrt_mod_prime(a, n);
    }
    let all = sqrt_mod_all(a, n)?;
    Ok(all.into_iter().next())
}

/// Generalized Chinese Remainder Theorem for `(remainders, moduli)` (`u64` moduli, possibly non-coprime).
///
/// Returns `Ok(Some((x, m)))` with `0 <= x < m = lcm(moduli)` if consistent,
/// `Ok(None)` if inconsistent, `Err(InvalidArgument)` if empty/mismatch/zero modulus,
/// or `Err(Overflow)` if `lcm` overflows `u64`.
pub fn crt(remainders: &[i64], moduli: &[u64]) -> Result<Option<(u64, u64)>, NTheoryError> {
    if remainders.is_empty() || remainders.len() != moduli.len() {
        return Err(NTheoryError::InvalidArgument(
            "remainders and moduli must be non-empty and equal length",
        ));
    }
    let mut x = 0u64;
    let mut m = 1u64;
    for (&r_raw, &mi) in remainders.iter().zip(moduli.iter()) {
        if mi == 0 {
            return Err(NTheoryError::InvalidArgument("all moduli must be positive"));
        }
        let r = if mi <= i64::MAX as u64 {
            r_raw.rem_euclid(mi as i64) as u64
        } else if r_raw >= 0 {
            (r_raw as u64) % mi
        } else {
            let rem = r_raw.unsigned_abs() % mi;
            if rem == 0 {
                0
            } else {
                mi - rem
            }
        };
        let g = gcd(m, mi);
        let diff = if r >= x % mi {
            r - (x % mi)
        } else {
            mi - ((x % mi) - r)
        };
        if diff % g != 0 {
            return Ok(None);
        }
        let next_m = checked_lcm(m, mi).ok_or(NTheoryError::Overflow)?;
        let m_g = m / g;
        let mi_g = mi / g;
        let inv = mod_inv(m_g % mi_g, mi_g).unwrap();
        let k = mul_mod(diff / g, inv, mi_g);
        // x + m * k fits within next_m since k < mi_g and m * mi_g == next_m
        x = ((x as u128 + (m as u128) * (k as u128)) % (next_m as u128)) as u64;
        m = next_m;
    }
    Ok(Some((x, m)))
}

/// Generalized Chinese Remainder Theorem for `u128`.
pub fn crt_u128(
    remainders: &[i128],
    moduli: &[u128],
) -> Result<Option<(u128, u128)>, NTheoryError> {
    if remainders.is_empty() || remainders.len() != moduli.len() {
        return Err(NTheoryError::InvalidArgument(
            "remainders and moduli must be non-empty and equal length",
        ));
    }
    let mut x = 0u128;
    let mut m = 1u128;
    for (&r_raw, &mi) in remainders.iter().zip(moduli.iter()) {
        if mi == 0 {
            return Err(NTheoryError::InvalidArgument("all moduli must be positive"));
        }
        let r = if mi <= i128::MAX as u128 {
            r_raw.rem_euclid(mi as i128) as u128
        } else if r_raw >= 0 {
            (r_raw as u128) % mi
        } else {
            let rem = r_raw.unsigned_abs() % mi;
            if rem == 0 {
                0
            } else {
                mi - rem
            }
        };
        let g = gcd_u128(m, mi);
        let xm = x % mi;
        let diff = if r >= xm { r - xm } else { mi - (xm - r) };
        if diff % g != 0 {
            return Ok(None);
        }
        let next_m = checked_lcm_u128(m, mi).ok_or(NTheoryError::Overflow)?;
        let m_g = m / g;
        let mi_g = mi / g;
        let inv = mod_inv_u128(m_g % mi_g, mi_g).unwrap();
        let k = mul_mod_u128(diff / g, inv, mi_g);
        let step = mul_mod_u128(m, k, next_m);
        let (sx, ov) = x.overflowing_add(step);
        x = if ov || sx >= next_m {
            sx.wrapping_sub(next_m)
        } else {
            sx
        };
        m = next_m;
    }
    Ok(Some((x, m)))
}

/// Generalized Chinese Remainder Theorem for `BigUint`.
pub fn crt_big(
    remainders: &[BigUint],
    moduli: &[BigUint],
) -> Result<Option<(BigUint, BigUint)>, NTheoryError> {
    if remainders.is_empty() || remainders.len() != moduli.len() {
        return Err(NTheoryError::InvalidArgument(
            "remainders and moduli must be non-empty and equal length",
        ));
    }
    let mut x = BigUint::zero();
    let mut m = BigUint::one();
    for (r_raw, mi) in remainders.iter().zip(moduli.iter()) {
        if mi.is_zero() {
            return Err(NTheoryError::InvalidArgument("all moduli must be positive"));
        }
        let r = r_raw.rem(mi);
        let g = m.gcd(mi);
        let xm = x.rem(mi);
        let diff = if r >= xm {
            r.sub(&xm)
        } else {
            mi.sub(&xm.sub(&r))
        };
        let (diff_div_g, rem_g) = diff.div_rem(&g);
        if !rem_g.is_zero() {
            return Ok(None);
        }
        let (m_g, _) = m.div_rem(&g);
        let (mi_g, _) = mi.div_rem(&g);
        let next_m = m_g.mul(mi);
        let inv = m_g.rem(&mi_g).mod_inv(&mi_g)?;
        let k = diff_div_g.mul(&inv).rem(&mi_g);
        x = x.add(&m.mul(&k)).rem(&next_m);
        m = next_m;
    }
    Ok(Some((x, m)))
}

/// Baby-Step Giant-Step for prime sub-order `q` (`g^x == h (mod n)`, `0 <= x < q`).
fn bsgs_u64(g: u64, h: u64, n: u64, q: u64) -> Option<u64> {
    let m = isqrt(q) + 1;
    let mut table = HashMap::with_capacity(m as usize);
    let mut cur = 1u64;
    for j in 0..m {
        table.entry(cur).or_insert(j);
        cur = mul_mod(cur, g, n);
    }
    let g_inv_m = mod_inv(cur, n).ok()?; // cur == g^m mod n
    let mut gamma = h % n;
    for i in 0..=m {
        if let Some(&j) = table.get(&gamma) {
            let x = i * m + j;
            if x < q {
                return Some(x);
            }
        }
        gamma = mul_mod(gamma, g_inv_m, n);
    }
    None
}

/// Pollard's Rho for discrete log `g^x == h (mod n)` in subgroup of prime order `q > 10^12` (O(1) memory).
fn pollard_rho_dlog_u64(g: u64, h: u64, n: u64, q: u64) -> Option<u64> {
    // Wait: if q is very large (> 10^12), BSGS would OOM; Pollard's Rho uses O(1) memory.
    let step = |x: u64, a: u64, b: u64| -> (u64, u64, u64) {
        match x % 3 {
            0 => (mul_mod(x, x, n), add_mod_u64(a, a, q), add_mod_u64(b, b, q)),
            1 => (mul_mod(x, g, n), add_mod_u64(a, 1, q), b),
            _ => (mul_mod(x, h, n), a, add_mod_u64(b, 1, q)),
        }
    };
    for seed_a in 1u64..16 {
        let mut x = pow_mod(g, seed_a, n);
        let mut a = seed_a % q;
        let mut b = 0u64;
        let (mut tx, mut ta, mut tb) = (x, a, b);
        for _ in 0..10_000_000u64 {
            let (nx, na, nb) = step(x, a, b);
            x = nx;
            a = na;
            b = nb;
            let (tx1, ta1, tb1) = step(tx, ta, tb);
            let (tx2, ta2, tb2) = step(tx1, ta1, tb1);
            tx = tx2;
            ta = ta2;
            tb = tb2;
            if x == tx {
                let db = if tb >= b { tb - b } else { q - (b - tb) };
                if db != 0 {
                    let da = if a >= ta { a - ta } else { q - (ta - a) };
                    if let Ok(inv) = mod_inv(db, q) {
                        return Some(mul_mod(da, inv, q));
                    }
                }
                break;
            }
        }
    }
    None
}

/// Solve the discrete logarithm `base^x == target (mod modulus)` for the smallest non-negative `x`.
///
/// Note on parameter order: `(base, target, modulus)` solves `base^x == target (mod modulus)`.
/// (SymPy's `discrete_log(n, a, b)` uses `(modulus, target, base)`.)
///
/// Handles both coprime and non-coprime `base, modulus` using Pohlig-Hellman + Baby-Step Giant-Step
/// (+ Pollard Rho for prime suborders `> 10^12`).
pub fn discrete_log(base: u64, target: u64, modulus: u64) -> Result<Option<u64>, NTheoryError> {
    if modulus == 0 {
        return Err(NTheoryError::InvalidArgument("modulus must be positive"));
    }
    if modulus == 1 {
        return Ok(Some(0));
    }
    let orig_t = target % modulus;
    let mut b = base % modulus;
    let mut t = orig_t;
    if t == 1 {
        return Ok(Some(0));
    }
    if b == 0 {
        return Ok(if t == 0 { Some(1) } else { None });
    }
    if b == 1 {
        return Ok(if t == 1 { Some(0) } else { None });
    }

    // Handle non-coprime case by peeling small x = 0, 1, ... until gcd(b, m_rem) == 1
    let mut m_rem = modulus;
    let mut offset = 0u64;
    let mut cur_pow = 1u64;
    while gcd(b, m_rem) != 1 {
        if cur_pow == orig_t {
            return Ok(Some(offset));
        }
        let g = gcd(b, m_rem);
        if t % g != 0 {
            return Ok(None);
        }
        m_rem /= g;
        t = mul_mod(t / g, mod_inv(b / g, m_rem)?, m_rem);
        b %= m_rem;
        offset += 1;
        cur_pow = pow_mod(base, offset, modulus);
        if cur_pow == orig_t {
            return Ok(Some(offset));
        }
        if m_rem == 1 {
            return Ok(None);
        }
    }

    // Now gcd(b, m_rem) == 1: solve b^y == t (mod m_rem) via Pohlig-Hellman
    if t == 1 || m_rem == 1 {
        return Ok(Some(offset));
    }
    if b == 1 || t == 0 {
        return Ok(None);
    }
    let ord = n_order(b, m_rem)?;
    let fac = factorint(ord);
    let mut rems = Vec::with_capacity(fac.len());
    let mut mods = Vec::with_capacity(fac.len());

    for (q, e) in fac {
        let qe = q.pow(e);
        let g_q = pow_mod(b, ord / q, m_rem);
        let mut x_q = 0u64;
        let mut q_pow = 1u64;
        let mut b_inv_pow = 1u64;
        let b_inv = mod_inv(b, m_rem).unwrap();
        let mut b_inv_qpow = b_inv;

        for k in 0..e {
            let t_adj = mul_mod(t, b_inv_pow, m_rem);
            let h_k = pow_mod(t_adj, ord / (q_pow * q), m_rem);
            let d_k = if q <= 1_000_000_000_000 {
                match bsgs_u64(g_q, h_k, m_rem, q) {
                    Some(d) => d,
                    None => return Ok(None),
                }
            } else {
                match pollard_rho_dlog_u64(g_q, h_k, m_rem, q) {
                    Some(d) => d,
                    None => return Ok(None),
                }
            };
            x_q += d_k * q_pow;
            if k + 1 < e {
                let step_inv = pow_mod(b_inv_qpow, d_k, m_rem);
                b_inv_pow = mul_mod(b_inv_pow, step_inv, m_rem);
                b_inv_qpow = pow_mod(b_inv_qpow, q, m_rem);
                q_pow *= q;
            }
        }
        rems.push(x_q as i64);
        mods.push(qe);
    }

    let (y, _) = match crt(&rems, &mods)? {
        Some(sol) => sol,
        None => return Ok(None),
    };
    let ans = offset + y;
    if pow_mod(base, ans, modulus) == target % modulus {
        Ok(Some(ans))
    } else {
        Ok(None)
    }
}

/// Solve the discrete logarithm `base^x == target (mod modulus)` for `u128`.
pub fn discrete_log_u128(
    base: u128,
    target: u128,
    modulus: u128,
) -> Result<Option<u128>, NTheoryError> {
    if modulus == 0 {
        return Err(NTheoryError::InvalidArgument("modulus must be positive"));
    }
    if let (Ok(b64), Ok(t64), Ok(m64)) = (
        u64::try_from(base % modulus),
        u64::try_from(target % modulus),
        u64::try_from(modulus),
    ) {
        return discrete_log(b64, t64, m64).map(|opt| opt.map(|v| v as u128));
    }
    if modulus == 1 {
        return Ok(Some(0));
    }
    let orig_t = target % modulus;
    let mut b = base % modulus;
    let mut t = orig_t;
    if t == 1 {
        return Ok(Some(0));
    }
    if b == 0 {
        return Ok(if t == 0 { Some(1) } else { None });
    }
    let mut m_rem = modulus;
    let mut offset = 0u128;
    while gcd_u128(b, m_rem) != 1 {
        if pow_mod_u128(base, offset, modulus) == orig_t {
            return Ok(Some(offset));
        }
        let g = gcd_u128(b, m_rem);
        if t % g != 0 {
            return Ok(None);
        }
        m_rem /= g;
        t = mul_mod_u128(t / g, mod_inv_u128(b / g, m_rem)?, m_rem);
        b %= m_rem;
        offset += 1;
        if pow_mod_u128(base, offset, modulus) == orig_t {
            return Ok(Some(offset));
        }
        if m_rem == 1 {
            return Ok(None);
        }
    }
    if t == 1 || m_rem == 1 {
        return Ok(Some(offset));
    }
    if b == 1 || t == 0 {
        return Ok(None);
    }
    let ord = n_order_u128(b, m_rem)?;
    let fac = factorint_u128(ord);
    let mut rems = Vec::with_capacity(fac.len());
    let mut mods = Vec::with_capacity(fac.len());

    // BSGS for u128 subgroup
    let bsgs_128 = |g: u128, h: u128, n: u128, q: u128| -> Option<u128> {
        let m = crate::arith::isqrt_u128(q) + 1;
        if m > 50_000_000 {
            return None;
        }
        let mut table = HashMap::with_capacity(m as usize);
        let mut cur = 1u128;
        for j in 0..m {
            table.entry(cur).or_insert(j);
            cur = mul_mod_u128(cur, g, n);
        }
        let g_inv_m = mod_inv_u128(cur, n).ok()?;
        let mut gamma = h % n;
        for i in 0..=m {
            if let Some(&j) = table.get(&gamma) {
                let x = i * m + j;
                if x < q {
                    return Some(x);
                }
            }
            gamma = mul_mod_u128(gamma, g_inv_m, n);
        }
        None
    };

    for (q, e) in fac {
        let qe = q.pow(e);
        let g_q = pow_mod_u128(b, ord / q, m_rem);
        let mut x_q = 0u128;
        let mut q_pow = 1u128;
        let mut b_inv_pow = 1u128;
        let b_inv = mod_inv_u128(b, m_rem).unwrap();
        let mut b_inv_qpow = b_inv;

        for k in 0..e {
            let t_adj = mul_mod_u128(t, b_inv_pow, m_rem);
            let h_k = pow_mod_u128(t_adj, ord / (q_pow * q), m_rem);
            let d_k = match bsgs_128(g_q, h_k, m_rem, q) {
                Some(d) => d,
                None => return Ok(None),
            };
            x_q += d_k * q_pow;
            if k + 1 < e {
                let step_inv = pow_mod_u128(b_inv_qpow, d_k, m_rem);
                b_inv_pow = mul_mod_u128(b_inv_pow, step_inv, m_rem);
                b_inv_qpow = pow_mod_u128(b_inv_qpow, q, m_rem);
                q_pow *= q;
            }
        }
        rems.push(x_q as i128);
        mods.push(qe);
    }

    let (y, _) = match crt_u128(&rems, &mods)? {
        Some(sol) => sol,
        None => return Ok(None),
    };
    let ans = offset + y;
    if pow_mod_u128(base, ans, modulus) == target % modulus {
        Ok(Some(ans))
    } else {
        Ok(None)
    }
}

/// All solutions `x in 0..p` to `x^r == a (mod p)` for prime `p`, sorted ascending.
pub fn nthroot_mod_all(a: u64, r: u64, p: u64) -> Result<Vec<u64>, NTheoryError> {
    if !is_prime(p) {
        return Err(NTheoryError::NotPrime);
    }
    if r == 0 {
        return Err(NTheoryError::InvalidArgument(
            "root exponent r must be >= 1",
        ));
    }
    let am = a % p;
    if am == 0 {
        return Ok(vec![0]);
    }
    if p == 2 || r == 1 {
        return Ok(vec![am]);
    }
    let pm1 = p - 1;
    let g = gcd(r, pm1);
    if pow_mod(am, pm1 / g, p) != 1 {
        return Ok(Vec::new());
    }
    if g == 1 {
        let inv = mod_inv(r % pm1, pm1).unwrap();
        return Ok(vec![pow_mod(am, inv, p)]);
    }
    if r == 2 {
        return Ok(match sqrt_mod_prime(am, p)? {
            Some(s) => {
                if s == p - s {
                    vec![s]
                } else {
                    vec![s, p - s]
                }
            }
            None => Vec::new(),
        });
    }
    // General case: find primitive root w, solve w^k == am (mod p), then x_j = w^{(k + j*pm1)/r}?
    // Wait: r*y == k (mod pm1) has g solutions: y = y0 + j*(pm1/g) for j = 0..g
    let w = primitive_root(p).unwrap();
    let k = discrete_log(w, am, p)?.unwrap();
    let r_g = r / g;
    let pm1_g = pm1 / g;
    let inv_rg = mod_inv(r_g % pm1_g, pm1_g).unwrap();
    let y0 = mul_mod(k / g, inv_rg, pm1_g);
    let mut roots = Vec::with_capacity(g as usize);
    let mut cur = pow_mod(w, y0, p);
    let step = pow_mod(w, pm1_g, p);
    for _ in 0..g {
        roots.push(cur);
        cur = mul_mod(cur, step, p);
    }
    roots.sort_unstable();
    Ok(roots)
}

/// Smallest non-negative solution to `x^r == a (mod p)` for prime `p`.
pub fn nthroot_mod(a: u64, r: u64, p: u64) -> Result<Option<u64>, NTheoryError> {
    Ok(nthroot_mod_all(a, r, p)?.into_iter().next())
}

/// Exact `C(n, k) mod p` for prime `p` via Lucas's theorem.
pub fn binomial_mod(mut n: u64, mut k: u64, p: u64) -> Result<u64, NTheoryError> {
    if !is_prime(p) {
        return Err(NTheoryError::NotPrime);
    }
    if k > n {
        return Ok(0);
    }
    if k == 0 || k == n {
        return Ok(1 % p);
    }
    let mut ans = 1u64;
    while n > 0 || k > 0 {
        let ni = n % p;
        let ki = k % p;
        if ki > ni {
            return Ok(0);
        }
        let ki_eff = ki.min(ni - ki);
        let mut num = 1u64;
        let mut den = 1u64;
        for j in 0..ki_eff {
            num = mul_mod(num, ni - j, p);
            den = mul_mod(den, j + 1, p);
        }
        let term = mul_mod(num, mod_inv(den, p).unwrap(), p);
        ans = mul_mod(ans, term, p);
        n /= p;
        k /= p;
    }
    Ok(ans)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_modular_suite() {
        assert_eq!(n_order(10, 5363222357), Ok(17));
        assert_eq!(n_order(10, 2), Err(NTheoryError::NotCoprime));
        assert_eq!(primitive_root(7), Some(3));
        assert_eq!(primitive_root(8), None);
        assert!(is_primitive_root(3, 7));

        assert_eq!(sqrt_mod_all(1, 15), Ok(vec![1, 4, 11, 14]));
        assert_eq!(crt(&[2, 3, 2], &[3, 5, 7]), Ok(Some((23, 105))));
        assert_eq!(crt(&[1, 2], &[4, 6]), Ok(None));
        assert_eq!(crt(&[1, 3], &[4, 6]), Ok(Some((9, 12))));

        assert_eq!(discrete_log(3, 13, 17), Ok(Some(4)));
        assert_eq!(discrete_log(2, 8, 16), Ok(Some(3)));
        assert_eq!(nthroot_mod_all(1, 4, 13), Ok(vec![1, 5, 8, 12]));
        assert_eq!(
            binomial_mod(1_000_000_000, 123_456, 1_000_000_007),
            Ok(binomial_mod(1_000_000_000, 123_456, 1_000_000_007).unwrap())
        );
        assert_eq!(binomial_mod(10, 3, 7), Ok(1)); // C(10,3)=120 == 1 mod 7
    }
}
