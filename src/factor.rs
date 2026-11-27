//! High-performance integer factorization for `u64`, `u128`, and `BigUint`.
//!
//! Combines trial division, deterministic/BPSW primality testing, Brent-Pollard Rho,
//! Pollard `p - 1` (Stage 1 + Stage 2), Montgomery ECM (Suyama curves, Stage 1 + Stage 2 BSGS),
//! and Self-Initializing Quadratic Sieve (SIQS).

use std::collections::BTreeMap;

use crate::arith::{add_mod_u128, add_mod_u64, gcd, gcd_u128, isqrt, isqrt_u128, Mont128, Mont64};
use crate::bigint::{BigMont, BigUint};
use crate::primality::{is_prime, is_prime_big, is_prime_u128, sieve_primes};
use crate::siqs::siqs_factor;

/// Configuration for multi-stage `BigUint` factorization (`factorint_big_with_config`).
#[derive(Clone, Copy, Debug)]
pub struct FactorConfig {
    /// Small-prime trial division upper bound.
    pub trial_bound: usize,
    /// Iteration cap for `BigUint` Brent-Pollard Rho.
    pub rho_iters: usize,
    /// Pollard `p - 1` Stage 1 smoothness bound.
    pub pm1_b1: u64,
    /// Pollard `p - 1` Stage 2 bound.
    pub pm1_b2: u64,
    /// Number of Montgomery ECM curves per cofactor.
    pub ecm_curves: usize,
    /// ECM Stage 1 smoothness bound.
    pub ecm_b1: u64,
    /// ECM Stage 2 bound.
    pub ecm_b2: u64,
    /// Maximum decimal digit length attempted with SIQS (`0` disables SIQS).
    pub siqs_max_digits: usize,
}

impl Default for FactorConfig {
    fn default() -> Self {
        Self {
            trial_bound: 100_000,
            rho_iters: 15_000,
            pm1_b1: 20_000,
            pm1_b2: 200_000,
            ecm_curves: 32,
            ecm_b1: 15_000,
            ecm_b2: 400_000,
            siqs_max_digits: 56,
        }
    }
}

/// Result of `factorint_big_with_config`, separating proven/probable prime factors
/// from any remaining composite cofactors if the configured effort budget was exhausted.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FactorResult {
    /// Map from prime factor to its multiplicity.
    pub factors: BTreeMap<BigUint, u32>,
    /// Any remaining composite cofactors not split within the budget (empty iff completely factored).
    pub unfactored: Vec<BigUint>,
}

impl FactorResult {
    /// Returns `true` iff `n` was completely factored into primes.
    pub fn is_complete(&self) -> bool {
        self.unfactored.is_empty()
    }
}

/// Brent-Pollard Rho factorization for odd composite `u64`.
pub fn pollard_rho_u64(n: u64) -> Option<u64> {
    if n <= 1 {
        return None;
    }
    if n & 1 == 0 {
        return Some(2);
    }
    if is_prime(n) {
        return None;
    }
    let ctx = Mont64::new(n);
    for c_raw in 1u64..128 {
        let c = ctx.to_mont(c_raw);
        let mut y = ctx.to_mont(2);
        let mut r = 1u64;
        let mut q = ctx.r1;
        let mut g = 1u64;
        let mut x = y;
        let mut ys = y;

        while g == 1 {
            x = y;
            for _ in 0..r {
                y = add_mod_u64(ctx.mul(y, y), c, n);
            }
            let mut k = 0u64;
            while k < r && g == 1 {
                ys = y;
                let lim = (r - k).min(128);
                let mut zero_hit = false;
                for _ in 0..lim {
                    y = add_mod_u64(ctx.mul(y, y), c, n);
                    let diff = if x >= y { x - y } else { y - x };
                    let next_q = ctx.mul(q, diff);
                    if next_q == 0 {
                        zero_hit = true;
                        break;
                    }
                    q = next_q;
                }
                g = if zero_hit { n } else { gcd(q, n) };
                k += lim;
            }
            r <<= 1;
        }
        if g == n {
            loop {
                ys = add_mod_u64(ctx.mul(ys, ys), c, n);
                let diff = if x >= ys { x - ys } else { ys - x };
                g = gcd(diff, n);
                if g > 1 {
                    break;
                }
            }
        }
        if g > 1 && g < n {
            return Some(g);
        }
    }
    let s = isqrt(n);
    if s > 1 && s * s == n {
        return Some(s);
    }
    None
}

/// Complete prime factorization of any `u64` (empty map for `0` and `1`).
pub fn factorint(mut n: u64) -> BTreeMap<u64, u32> {
    let mut map = BTreeMap::new();
    if n <= 1 {
        return map;
    }
    const SMALL: [u64; 16] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53];
    for &p in &SMALL {
        if n % p == 0 {
            let mut e = 0u32;
            while n % p == 0 {
                n /= p;
                e += 1;
            }
            map.insert(p, e);
        }
    }
    let mut stack = Vec::new();
    if n > 1 {
        stack.push(n);
    }
    while let Some(x) = stack.pop() {
        if x <= 1 {
            continue;
        }
        if is_prime(x) {
            *map.entry(x).or_insert(0) += 1;
            continue;
        }
        let d = pollard_rho_u64(x).expect("u64 composite must split");
        stack.push(d);
        stack.push(x / d);
    }
    map
}

/// Brent-Pollard Rho factorization for `u128` using 128-bit Montgomery arithmetic.
pub fn pollard_rho_u128(n: u128, max_iters: usize) -> Option<u128> {
    if n <= 1 {
        return None;
    }
    if n & 1 == 0 {
        return Some(2);
    }
    if let Ok(n64) = u64::try_from(n) {
        return pollard_rho_u64(n64).map(|d| d as u128);
    }
    let ctx = Mont128::new(n);
    for c_raw in 1u128..16 {
        let c = ctx.to_mont(c_raw);
        let mut y = ctx.to_mont(2);
        let mut r = 1usize;
        let mut q = ctx.r1;
        let mut g = 1u128;
        let mut iters = 0usize;
        let mut x = y;
        let mut ys = y;

        while g == 1 && iters < max_iters {
            x = y;
            for _ in 0..r {
                y = add_mod_u128(ctx.mul(y, y), c, n);
            }
            let mut k = 0usize;
            while k < r && g == 1 && iters < max_iters {
                ys = y;
                let lim = (r - k).min(64);
                let mut zero_hit = false;
                for _ in 0..lim {
                    y = add_mod_u128(ctx.mul(y, y), c, n);
                    let diff = if x >= y { x - y } else { y - x };
                    let next_q = ctx.mul(q, diff);
                    if next_q == 0 {
                        zero_hit = true;
                        break;
                    }
                    q = next_q;
                }
                g = if zero_hit { n } else { gcd_u128(q, n) };
                k += lim;
                iters += lim;
            }
            r <<= 1;
        }
        if g == n {
            loop {
                ys = add_mod_u128(ctx.mul(ys, ys), c, n);
                let diff = if x >= ys { x - ys } else { ys - x };
                g = gcd_u128(diff, n);
                if g > 1 {
                    break;
                }
            }
        }
        if g > 1 && g < n {
            return Some(g);
        }
    }
    let s = isqrt_u128(n);
    if s > 1 && s * s == n {
        return Some(s);
    }
    None
}

/// Complete prime factorization of any `u128` (empty map for `0` and `1`).
/// Uses `Mont128` Rho first and seamlessly escalates to ECM/SIQS for hard 28–38 digit semiprimes.
pub fn factorint_u128(mut n: u128) -> BTreeMap<u128, u32> {
    if let Ok(n64) = u64::try_from(n) {
        return factorint(n64)
            .into_iter()
            .map(|(p, e)| (p as u128, e))
            .collect();
    }
    let mut map = BTreeMap::new();
    const SMALL: [u128; 25] = [
        2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
        97,
    ];
    for &p in &SMALL {
        if n % p == 0 {
            let mut e = 0u32;
            while n % p == 0 {
                n /= p;
                e += 1;
            }
            map.insert(p, e);
        }
    }
    let mut stack = Vec::new();
    if n > 1 {
        stack.push(n);
    }
    while let Some(x) = stack.pop() {
        if x <= 1 {
            continue;
        }
        if is_prime_u128(x) {
            *map.entry(x).or_insert(0) += 1;
            continue;
        }
        if let Some(d) = pollard_rho_u128(x, 20_000) {
            stack.push(d);
            stack.push(x / d);
        } else {
            // Escalate hard 128-bit composite (e.g. 38-digit RSA-style semiprime) to ECM + SIQS
            let sub = factorint_big(&BigUint::from_u128(x));
            for (p_big, e) in sub {
                let p = p_big.to_u128().expect("factor of u128 fits in u128");
                *map.entry(p).or_insert(0) += e;
            }
        }
    }
    map
}

/// Brent-Pollard Rho factorization for odd composite `BigUint`.
pub fn pollard_rho_big(n: &BigUint, max_iters: usize) -> Option<BigUint> {
    if n <= &BigUint::one() {
        return None;
    }
    if n.is_even() {
        return Some(BigUint::from_u64(2));
    }
    let ctx = BigMont::new(n.clone());
    for c_val in [1u64, 3, 5, 7] {
        let c = ctx.to_mont_u64(c_val);
        let mut y = ctx.to_mont_u64(2);
        let mut r = 1usize;
        let mut q = ctx.r1.clone();
        let mut g = BigUint::one();
        let mut iters = 0usize;
        let mut x = y.clone();
        let mut ys = y.clone();

        while g.is_one() && iters < max_iters {
            x = y.clone();
            for _ in 0..r {
                let y2 = ctx.mul_limbs(&y, &y);
                y = ctx.add_limbs(&y2, &c);
            }
            let mut k = 0usize;
            while k < r && g.is_one() && iters < max_iters {
                ys = y.clone();
                let batch = (r - k).min(64);
                let mut zero_hit = false;
                for _ in 0..batch {
                    let y2 = ctx.mul_limbs(&y, &y);
                    y = ctx.add_limbs(&y2, &c);
                    let diff = ctx.sub_limbs(&x, &y);
                    let next_q = ctx.mul_limbs(&q, &diff);
                    if next_q.iter().all(|&w| w == 0) {
                        zero_hit = true;
                        break;
                    }
                    q = next_q;
                }
                g = if zero_hit {
                    n.clone()
                } else {
                    n.gcd(&BigUint::from_limbs(q.clone()))
                };
                k += batch;
                iters += batch;
            }
            r <<= 1;
        }
        if &g == n {
            loop {
                let y2 = ctx.mul_limbs(&ys, &ys);
                ys = ctx.add_limbs(&y2, &c);
                let diff = ctx.sub_limbs(&x, &ys);
                g = n.gcd(&BigUint::from_limbs(diff));
                if !g.is_one() {
                    break;
                }
            }
        }
        if !g.is_zero() && !g.is_one() && &g < n {
            return Some(g);
        }
    }
    None
}

/// Pollard `p - 1` (Stage 1 + Stage 2) for odd composite `BigUint`.
pub fn pollard_pm1(n: &BigUint, b1: u64, b2: u64, primes: &[u64]) -> Option<BigUint> {
    if b1 == 0 || n <= &BigUint::one() || n.is_even() {
        return None;
    }
    let ctx = BigMont::new(n.clone());
    let mut a = ctx.to_mont_u64(3);

    for &p in primes {
        if p > b1 {
            break;
        }
        let mut pe = p;
        while pe <= b1 / p {
            pe *= p;
        }
        a = ctx.pow_mont_u64(&a, pe);
    }

    let a_minus_1 = ctx.sub_limbs(&a, &ctx.r1);
    let g = n.gcd(&BigUint::from_limbs(a_minus_1));
    if !g.is_zero() && !g.is_one() && &g < n {
        return Some(g);
    }
    if &g == n || b2 <= b1 {
        return None;
    }

    let a2 = ctx.mul_limbs(&a, &a);
    let mut step_pows: Vec<Vec<u64>> = Vec::with_capacity(64);
    step_pows.push(ctx.r1.clone());
    step_pows.push(a2.clone());
    for _ in 2..64 {
        let prev = step_pows.last().unwrap().clone();
        step_pows.push(ctx.mul_limbs(&prev, &a2));
    }

    let start_idx = primes.partition_point(|&p| p <= b1);
    if start_idx >= primes.len() || primes[start_idx] > b2 {
        return None;
    }
    let mut prev_p = primes[start_idx];
    let mut cur = ctx.pow_mont_u64(&a, prev_p);
    let mut acc = ctx.sub_limbs(&cur, &ctx.r1);
    let mut steps = 0usize;

    for &p in &primes[start_idx + 1..] {
        if p > b2 {
            break;
        }
        let diff = ((p - prev_p) / 2) as usize;
        if diff < step_pows.len() {
            cur = ctx.mul_limbs(&cur, &step_pows[diff]);
        } else {
            let mult = ctx.pow_mont_u64(&a, p - prev_p);
            cur = ctx.mul_limbs(&cur, &mult);
        }
        let d = ctx.sub_limbs(&cur, &ctx.r1);
        let next_acc = ctx.mul_limbs(&acc, &d);
        if next_acc.iter().all(|&w| w == 0) {
            let g2 = n.gcd(&BigUint::from_limbs(acc));
            if !g2.is_zero() && !g2.is_one() && &g2 < n {
                return Some(g2);
            }
            return None;
        }
        acc = next_acc;
        prev_p = p;
        steps += 1;
        if steps % 256 == 0 {
            let g2 = n.gcd(&BigUint::from_limbs(acc.clone()));
            if !g2.is_zero() && !g2.is_one() && &g2 < n {
                return Some(g2);
            }
            if &g2 == n {
                return None;
            }
        }
    }
    let g2 = n.gcd(&BigUint::from_limbs(acc));
    if !g2.is_zero() && !g2.is_one() && &g2 < n {
        return Some(g2);
    }
    None
}

#[derive(Clone)]
struct MontPoint {
    x: Vec<u64>,
    z: Vec<u64>,
}

#[inline]
fn x_dbl(p: &MontPoint, a24: &[u64], ctx: &BigMont) -> MontPoint {
    let u = ctx.add_limbs(&p.x, &p.z);
    let v = ctx.sub_limbs(&p.x, &p.z);
    let u2 = ctx.mul_limbs(&u, &u);
    let v2 = ctx.mul_limbs(&v, &v);
    let w = ctx.sub_limbs(&u2, &v2);
    let x2 = ctx.mul_limbs(&u2, &v2);
    let a24w = ctx.mul_limbs(a24, &w);
    let z2 = ctx.mul_limbs(&w, &ctx.add_limbs(&v2, &a24w));
    MontPoint { x: x2, z: z2 }
}

#[inline]
fn x_add(p: &MontPoint, q: &MontPoint, diff: &MontPoint, ctx: &BigMont) -> MontPoint {
    let u = ctx.mul_limbs(&ctx.sub_limbs(&p.x, &p.z), &ctx.add_limbs(&q.x, &q.z));
    let v = ctx.mul_limbs(&ctx.add_limbs(&p.x, &p.z), &ctx.sub_limbs(&q.x, &q.z));
    let upv = ctx.add_limbs(&u, &v);
    let umv = ctx.sub_limbs(&u, &v);
    MontPoint {
        x: ctx.mul_limbs(&diff.z, &ctx.mul_limbs(&upv, &upv)),
        z: ctx.mul_limbs(&diff.x, &ctx.mul_limbs(&umv, &umv)),
    }
}

fn x_mul(k: u64, p: &MontPoint, a24: &[u64], ctx: &BigMont) -> MontPoint {
    if k == 1 {
        return p.clone();
    }
    if k == 2 {
        return x_dbl(p, a24, ctx);
    }
    let mut r0 = p.clone();
    let mut r1 = x_dbl(p, a24, ctx);
    let top_bit = 63 - k.leading_zeros();
    for b in (0..top_bit).rev() {
        if (k >> b) & 1 == 0 {
            r1 = x_add(&r0, &r1, p, ctx);
            r0 = x_dbl(&r0, a24, ctx);
        } else {
            r0 = x_add(&r0, &r1, p, ctx);
            r1 = x_dbl(&r1, a24, ctx);
        }
    }
    r0
}

fn ecm_one_curve(
    n: &BigUint,
    ctx: &BigMont,
    sigma: u64,
    b1: u64,
    b2: u64,
    primes: &[u64],
) -> Option<BigUint> {
    let sig_big = BigUint::from_u64(sigma);
    let u_big = sig_big.mul(&sig_big).sub(&BigUint::from_u64(5)).rem(n);
    let v_big = sig_big.mul_u64(4).rem(n);
    let u3 = u_big.mul(&u_big).rem(n).mul(&u_big).rem(n);
    let v3 = v_big.mul(&v_big).rem(n).mul(&v_big).rem(n);
    let denom = u3.mul(&v_big).rem(n).mul_u64(16).rem(n);
    let inv_denom = match denom.mod_inv_or_factor(n) {
        Ok(inv) => inv,
        Err(g) => {
            if !g.is_zero() && !g.is_one() && &g < n {
                return Some(g);
            }
            return None;
        }
    };
    let v_minus_u = if v_big >= u_big {
        v_big.sub(&u_big)
    } else {
        n.sub(&u_big.sub(&v_big))
    };
    let vmu3 = v_minus_u.mul(&v_minus_u).rem(n).mul(&v_minus_u).rem(n);
    let three_u_plus_v = u_big.mul_u64(3).add(&v_big).rem(n);
    let a24_big = vmu3.mul(&three_u_plus_v).rem(n).mul(&inv_denom).rem(n);

    let a24 = ctx.to_mont_limbs(&a24_big);
    let mut pt = MontPoint {
        x: ctx.to_mont_limbs(&u3),
        z: ctx.to_mont_limbs(&v3),
    };

    for &p in primes {
        if p > b1 {
            break;
        }
        let mut pe = p;
        while pe <= b1 / p {
            pe *= p;
        }
        pt = x_mul(pe, &pt, &a24, ctx);
    }

    let g = n.gcd(&BigUint::from_limbs(pt.z.clone()));
    if !g.is_zero() && !g.is_one() && &g < n {
        return Some(g);
    }
    if &g == n || b2 <= b1 {
        return None;
    }

    const D: u64 = 210;
    const COPRIMES: [u64; 24] = [
        1, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101,
        103,
    ];
    let mut coprime_idx = [255u8; 105];
    for (i, &c) in COPRIMES.iter().enumerate() {
        coprime_idx[c as usize] = i as u8;
    }

    let q2 = x_dbl(&pt, &a24, ctx);
    let mut odd_pts: Vec<MontPoint> = Vec::with_capacity(53);
    odd_pts.push(pt.clone());
    odd_pts.push(x_add(&q2, &pt, &pt, ctx));
    for i in 2..52 {
        let next = x_add(&odd_pts[i - 1], &q2, &odd_pts[i - 2], ctx);
        odd_pts.push(next);
    }
    let baby: Vec<MontPoint> = COPRIMES
        .iter()
        .map(|&c| odd_pts[((c - 1) / 2) as usize].clone())
        .collect();

    let g_step = x_mul(D, &pt, &a24, ctx);
    let m_start = (b1 / D).max(1);
    let m_end = (b2 + D / 2) / D + 1;

    let mut g_prev = x_mul(m_start.saturating_sub(1).max(1), &g_step, &a24, ctx);
    let mut g_cur = if m_start == 1 {
        g_step.clone()
    } else {
        x_mul(m_start, &g_step, &a24, ctx)
    };
    let mut cur_m = m_start;

    let start_idx = primes.partition_point(|&p| p <= b1);
    let mut acc = ctx.r1.clone();
    let mut count = 0usize;

    for &p in &primes[start_idx..] {
        if p > b2 {
            break;
        }
        let rem = p % D;
        let (target_m, j) = if rem < D / 2 {
            (p / D, rem)
        } else {
            (p / D + 1, D - rem)
        };
        if target_m > m_end || j == 0 || j >= 105 {
            continue;
        }
        let b_idx = coprime_idx[j as usize];
        if b_idx == 255 {
            continue;
        }
        while cur_m < target_m {
            let g_next = if cur_m == 1 {
                x_dbl(&g_step, &a24, ctx)
            } else {
                x_add(&g_cur, &g_step, &g_prev, ctx)
            };
            g_prev = g_cur;
            g_cur = g_next;
            cur_m += 1;
        }
        let bpt = &baby[b_idx as usize];
        let diff = ctx.sub_limbs(
            &ctx.mul_limbs(&g_cur.x, &bpt.z),
            &ctx.mul_limbs(&bpt.x, &g_cur.z),
        );
        let next_acc = ctx.mul_limbs(&acc, &diff);
        if next_acc.iter().all(|&w| w == 0) {
            let g2 = n.gcd(&BigUint::from_limbs(acc));
            if !g2.is_zero() && !g2.is_one() && &g2 < n {
                return Some(g2);
            }
            return None;
        }
        acc = next_acc;
        count += 1;
        if count % 512 == 0 {
            let g2 = n.gcd(&BigUint::from_limbs(acc.clone()));
            if !g2.is_zero() && !g2.is_one() && &g2 < n {
                return Some(g2);
            }
            if &g2 == n {
                return None;
            }
        }
    }

    let g2 = n.gcd(&BigUint::from_limbs(acc));
    if !g2.is_zero() && !g2.is_one() && &g2 < n {
        return Some(g2);
    }
    None
}

/// Montgomery Elliptic Curve Method (Suyama curves, Stage 1 + Stage 2 BSGS `D = 210`).
pub fn ecm_factor(
    n: &BigUint,
    curves: usize,
    b1: u64,
    b2: u64,
    primes: &[u64],
    seed: u64,
) -> Option<BigUint> {
    if curves == 0 || n <= &BigUint::one() || n.is_even() {
        return None;
    }
    let ctx = BigMont::new(n.clone());
    for c in 0..curves {
        let sigma = 6 + seed
            .wrapping_mul(10007)
            .wrapping_add((c as u64).wrapping_mul(7919))
            % 1_000_000_000;
        if let Some(d) = ecm_one_curve(n, &ctx, sigma.max(6), b1, b2, primes) {
            return Some(d);
        }
    }
    None
}

/// Multi-stage factorization of `BigUint` using custom `FactorConfig`.
pub fn factorint_big_with_config(n: &BigUint, cfg: FactorConfig) -> FactorResult {
    let mut factors = BTreeMap::new();
    let mut unfactored = Vec::new();
    if n <= &BigUint::one() {
        return FactorResult {
            factors,
            unfactored,
        };
    }

    let mut rem = n.clone();
    let tz = rem.trailing_zeros();
    if tz > 0 {
        rem.shr_assign(tz);
        factors.insert(BigUint::from_u64(2), tz as u32);
    }

    let trial_primes = sieve_primes(cfg.trial_bound);
    for &p in &trial_primes[1..] {
        if rem.is_one() {
            break;
        }
        if rem.rem_u64(p) == 0 {
            let mut e = 0u32;
            while rem.rem_u64(p) == 0 {
                let (q, _) = rem.div_rem_u64(p);
                rem = q;
                e += 1;
            }
            factors.insert(BigUint::from_u64(p), e);
        }
    }

    let stage2_lim = cfg.ecm_b2.max(cfg.pm1_b2).max(50_000) as usize;
    let mut stage_primes_cache: Option<Vec<u64>> = None;

    let mut stack = Vec::new();
    if !rem.is_one() {
        stack.push(rem);
    }

    while let Some(x) = stack.pop() {
        if x.is_one() {
            continue;
        }
        if let Some(x128) = x.to_u128() {
            if let Some(x64) = x.to_u64() {
                for (p, e) in factorint(x64) {
                    *factors.entry(BigUint::from_u64(p)).or_insert(0) += e;
                }
                continue;
            }
            if is_prime_u128(x128) {
                *factors.entry(x).or_insert(0) += 1;
                continue;
            }
            if let Some(d) = pollard_rho_u128(x128, 20_000) {
                stack.push(BigUint::from_u128(d));
                stack.push(BigUint::from_u128(x128 / d));
                continue;
            }
        } else if is_prime_big(&x) {
            *factors.entry(x).or_insert(0) += 1;
            continue;
        }

        // Perfect square check
        let sq = x.isqrt();
        if sq.mul(&sq) == x {
            stack.push(sq.clone());
            stack.push(sq);
            continue;
        }

        if let Some(d) = pollard_rho_big(&x, cfg.rho_iters) {
            let (q, r) = x.div_rem(&d);
            debug_assert!(r.is_zero());
            stack.push(d);
            stack.push(q);
            continue;
        }

        let sp = stage_primes_cache.get_or_insert_with(|| sieve_primes(stage2_lim));

        if let Some(d) = pollard_pm1(&x, cfg.pm1_b1, cfg.pm1_b2, sp) {
            let (q, r) = x.div_rem(&d);
            debug_assert!(r.is_zero());
            stack.push(d);
            stack.push(q);
            continue;
        }

        if let Some(d) = ecm_factor(&x, cfg.ecm_curves, cfg.ecm_b1, cfg.ecm_b2, sp, x.limbs[0]) {
            let (q, r) = x.div_rem(&d);
            debug_assert!(r.is_zero());
            stack.push(d);
            stack.push(q);
            continue;
        }

        if x.decimal_digits() <= cfg.siqs_max_digits {
            if let Some(d) = siqs_factor(&x) {
                let (q, r) = x.div_rem(&d);
                debug_assert!(r.is_zero());
                stack.push(d);
                stack.push(q);
                continue;
            }
        }

        unfactored.push(x);
    }

    FactorResult {
        factors,
        unfactored,
    }
}

/// Complete prime factorization of `BigUint` using default multi-stage settings
/// (Trial division -> Brent-Rho -> Pollard `p-1` -> ECM -> SIQS).
pub fn factorint_big(n: &BigUint) -> BTreeMap<BigUint, u32> {
    let res = factorint_big_with_config(n, FactorConfig::default());
    if res.unfactored.is_empty() {
        res.factors
    } else {
        // Retry remaining composite cofactors with boosted ECM curves
        let mut out = res.factors;
        let boosted = FactorConfig {
            trial_bound: 100_000,
            rho_iters: 30_000,
            pm1_b1: 50_000,
            pm1_b2: 500_000,
            ecm_curves: 128,
            ecm_b1: 40_000,
            ecm_b2: 1_500_000,
            siqs_max_digits: 62,
        };
        for u in res.unfactored {
            let r2 = factorint_big_with_config(&u, boosted);
            for (p, e) in r2.factors {
                *out.entry(p).or_insert(0) += e;
            }
            for rem_u in r2.unfactored {
                *out.entry(rem_u).or_insert(0) += 1;
            }
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_factor_u64_u128_big() {
        assert_eq!(factorint(1).len(), 0);
        let f64 = factorint(360);
        assert_eq!(f64.get(&2), Some(&3));
        assert_eq!(f64.get(&3), Some(&2));
        assert_eq!(f64.get(&5), Some(&1));

        // 128-bit product of two 16-digit primes (32 digits)
        let p = 1_000_000_000_000_037u128;
        let q = 1_000_000_000_000_091u128;
        let f128 = factorint_u128(p * q);
        assert_eq!(f128.get(&p), Some(&1));
        assert_eq!(f128.get(&q), Some(&1));

        // 2^67 - 1 = 193707721 * 761838257287
        let m67 = (1u128 << 67) - 1;
        let fm67 = factorint_u128(m67);
        assert_eq!(fm67.get(&193707721), Some(&1));
        assert_eq!(fm67.get(&761838257287), Some(&1));
    }
}
