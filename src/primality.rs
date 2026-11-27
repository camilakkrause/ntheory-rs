//! Primality testing (deterministic 64-bit Miller-Rabin, 128-bit & BigUint Baillie-PSW),
//! segmented prime sieves, lazy `PrimeIter`, sublinear Meissel-Lehmer `prime_pi`, `nth_prime`,
//! and primorials.

use std::collections::HashMap;

use crate::arith::{
    add_mod_u128, is_square_u128, isqrt, perfect_power, sub_mod_u128, Mont128, Mont64,
};
use crate::bigint::{jacobi_i64_big, BigMont, BigUint};

/// 100% deterministic Miller-Rabin primality test for ALL `u64`.
/// Uses Sinclair's proven 7-base set `{2, 325, 9375, 28178, 450775, 9780504, 1795265022}`.
pub fn is_prime(n: u64) -> bool {
    if n < 2 {
        return false;
    }
    const SMALL: [u64; 12] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37];
    for &p in &SMALL {
        if n == p {
            return true;
        }
        if n % p == 0 {
            return false;
        }
    }
    if n < 37 * 37 {
        return true;
    }

    let s = (n - 1).trailing_zeros();
    let d = (n - 1) >> s;
    let ctx = Mont64::new(n);
    let one = ctx.r1;
    let neg_one = n - one;

    const BASES: [u64; 7] = [2, 325, 9375, 28178, 450775, 9780504, 1795265022];
    'witness: for &a in &BASES {
        let a_mod = a % n;
        if a_mod == 0 {
            continue;
        }
        let mut x = ctx.pow_mont(ctx.to_mont(a_mod), d);
        if x == one || x == neg_one {
            continue;
        }
        for _ in 1..s {
            x = ctx.mul(x, x);
            if x == neg_one {
                continue 'witness;
            }
        }
        return false;
    }
    true
}

/// SymPy-style alias for [`is_prime`].
#[inline]
pub fn isprime(n: u64) -> bool {
    is_prime(n)
}

/// Jacobi symbol `(a / n)` for `i64` `a` and odd positive `u128` `n`.
fn jacobi_i64_u128(a: i64, n: u128) -> i8 {
    if n == 1 {
        return 1;
    }
    let mut neg = false;
    let ua: u128 = if a < 0 {
        if (n & 3) == 3 {
            neg = !neg;
        }
        a.unsigned_abs() as u128
    } else {
        a as u128
    };
    if ua == 0 {
        return 0;
    }
    let mut x = ua % n;
    let mut y = n;
    while x != 0 {
        let tz = x.trailing_zeros();
        if tz & 1 == 1 {
            let m8 = y & 7;
            if m8 == 3 || m8 == 5 {
                neg = !neg;
            }
        }
        x >>= tz;
        if (x & 3) == 3 && (y & 3) == 3 {
            neg = !neg;
        }
        let tmp = y % x;
        y = x;
        x = tmp;
    }
    if y != 1 {
        0
    } else if neg {
        -1
    } else {
        1
    }
}

/// Strong Lucas probable prime test (Selfridge Method A) in `Mont128`.
fn strong_lucas_prp_u128(n: u128, ctx: &Mont128) -> bool {
    if is_square_u128(n) {
        return false;
    }
    let mut d: i64 = 5;
    let mut sign: i64 = 1;
    loop {
        let cur_d = d * sign;
        let j = jacobi_i64_u128(cur_d, n);
        if j == 0 {
            let ad = d as u128;
            if n % ad == 0 && n != ad {
                return false;
            }
        }
        if j == -1 {
            d = cur_d;
            break;
        }
        d += 2;
        sign = -sign;
    }
    let q_mod = if (1 - d) / 4 >= 0 {
        ctx.to_mont(((1 - d) / 4) as u128)
    } else {
        n - ctx.to_mont((-(1 - d) / 4) as u128)
    };
    let d_mod = if d >= 0 {
        ctx.to_mont(d as u128)
    } else {
        n - ctx.to_mont((-d) as u128)
    };
    // inv2 = (n + 1) / 2 in Montgomery domain
    let inv2_raw = (n >> 1) + 1;
    let inv2_m = ctx.to_mont(inv2_raw);

    // Note: if n == u128::MAX, n is composite (2^128 - 1), filtered by MR; safe to add 1
    let np1 = n + 1;
    let s = np1.trailing_zeros();
    let d_exp = np1 >> s;

    let mut u = ctx.r1;
    let mut v = ctx.r1;
    let mut qk = q_mod;

    let bits = 128 - d_exp.leading_zeros();
    for i in (0..bits - 1).rev() {
        u = ctx.mul(u, v);
        let v2 = ctx.mul(v, v);
        let qk2 = add_mod_u128(qk, qk, n);
        v = sub_mod_u128(v2, qk2, n);
        qk = ctx.mul(qk, qk);

        if (d_exp >> i) & 1 != 0 {
            let upv = add_mod_u128(u, v, n);
            let du = ctx.mul(d_mod, u);
            let dupv = add_mod_u128(du, v, n);
            u = ctx.mul(upv, inv2_m);
            v = ctx.mul(dupv, inv2_m);
            qk = ctx.mul(qk, q_mod);
        }
    }

    if u == 0 || v == 0 {
        return true;
    }
    for _ in 1..s {
        let v2 = ctx.mul(v, v);
        let qk2 = add_mod_u128(qk, qk, n);
        v = sub_mod_u128(v2, qk2, n);
        if v == 0 {
            return true;
        }
        qk = ctx.mul(qk, qk);
    }
    false
}

/// Primality test for `u128`: deterministic for `n <= u64::MAX`, Baillie-PSW + 12-base MR above.
pub fn is_prime_u128(n: u128) -> bool {
    if let Ok(v) = u64::try_from(n) {
        return is_prime(v);
    }
    if n & 1 == 0 {
        return false;
    }
    const SMALL: [u128; 25] = [
        3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
        97, 101,
    ];
    for &p in &SMALL {
        if n % p == 0 {
            return false;
        }
    }
    let ctx = Mont128::new(n);
    let s = (n - 1).trailing_zeros();
    let d = (n - 1) >> s;
    let one = ctx.r1;
    let neg_one = n - one;

    const BASES: [u128; 12] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37];
    'witness: for &a in &BASES {
        let mut x = ctx.pow_mont(ctx.to_mont(a), d);
        if x == one || x == neg_one {
            continue;
        }
        for _ in 1..s {
            x = ctx.mul(x, x);
            if x == neg_one {
                continue 'witness;
            }
        }
        return false;
    }
    strong_lucas_prp_u128(n, &ctx)
}

/// Strong Lucas probable prime test (Selfridge Method A) for `BigUint`.
fn strong_lucas_prp_big(n: &BigUint, ctx: &BigMont) -> bool {
    if n.is_square() {
        return false;
    }
    let mut d: i64 = 5;
    let mut sign: i64 = 1;
    loop {
        let cur_d = d * sign;
        let j = jacobi_i64_big(cur_d, n);
        if j == 0 {
            let ad = d as u64;
            if n.rem_u64(ad) == 0 && n != &BigUint::from_u64(ad) {
                return false;
            }
        }
        if j == -1 {
            d = cur_d;
            break;
        }
        d += 2;
        sign = -sign;
    }
    let q_i64 = (1 - d) / 4;
    let q_mod = if q_i64 >= 0 {
        ctx.to_mont_u64(q_i64 as u64)
    } else {
        let pos = ctx.to_mont_u64((-q_i64) as u64);
        ctx.sub_limbs(&vec![0u64; ctx.k], &pos)
    };
    let d_mod = if d >= 0 {
        ctx.to_mont_u64(d as u64)
    } else {
        let pos = ctx.to_mont_u64((-d) as u64);
        ctx.sub_limbs(&vec![0u64; ctx.k], &pos)
    };
    let zero = vec![0u64; ctx.k];
    let mut np1 = n.clone();
    np1.add_u64_assign(1);
    let inv2_m = ctx.to_mont_limbs(&np1.shr(1));
    let s = np1.trailing_zeros();
    let d_exp = np1.shr(s);

    let mut u = ctx.r1.clone();
    let mut v = ctx.r1.clone();
    let mut qk = q_mod.clone();

    let bits = d_exp.bit_len();
    for i in (0..bits - 1).rev() {
        u = ctx.mul_limbs(&u, &v);
        let v2 = ctx.mul_limbs(&v, &v);
        let qk2 = ctx.add_limbs(&qk, &qk);
        v = ctx.sub_limbs(&v2, &qk2);
        qk = ctx.mul_limbs(&qk, &qk);
        if d_exp.bit(i) {
            let u_plus_v = ctx.add_limbs(&u, &v);
            let du_plus_v = ctx.add_limbs(&ctx.mul_limbs(&d_mod, &u), &v);
            u = ctx.mul_limbs(&u_plus_v, &inv2_m);
            v = ctx.mul_limbs(&du_plus_v, &inv2_m);
            qk = ctx.mul_limbs(&qk, &q_mod);
        }
    }

    if u == zero || v == zero {
        return true;
    }
    for _ in 1..s {
        let v2 = ctx.mul_limbs(&v, &v);
        let qk2 = ctx.add_limbs(&qk, &qk);
        v = ctx.sub_limbs(&v2, &qk2);
        if v == zero {
            return true;
        }
        qk = ctx.mul_limbs(&qk, &qk);
    }
    false
}

/// Primality test for `BigUint`: deterministic for `< 2^64`, Baillie-PSW + 12-base MR above.
pub fn is_prime_big(n: &BigUint) -> bool {
    if let Some(v) = n.to_u128() {
        return is_prime_u128(v);
    }
    if n.is_even() {
        return false;
    }
    const SMALL: [u64; 25] = [
        3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
        97, 101,
    ];
    for &p in &SMALL {
        if n.rem_u64(p) == 0 {
            return false;
        }
    }
    let ctx = BigMont::new(n.clone());
    let mut nm1 = n.clone();
    nm1.sub_u64_assign(1);
    let s = nm1.trailing_zeros();
    let d = nm1.shr(s);
    let one = ctx.r1.clone();
    let neg_one = ctx.sub_limbs(&vec![0u64; ctx.k], &one);

    const BASES: [u64; 12] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37];
    'witness: for &a in &BASES {
        let am = ctx.to_mont_u64(a);
        let mut x = ctx.pow_mont_limbs(&am, &d);
        if x == one || x == neg_one {
            continue;
        }
        for _ in 1..s {
            x = ctx.mul_limbs(&x, &x);
            if x == neg_one {
                continue 'witness;
            }
        }
        return false;
    }
    strong_lucas_prp_big(n, &ctx)
}

/// If `n` is a prime power `p^k` (`k >= 1`, `p` prime), returns `Some((p, k))`; else `None`.
pub fn is_prime_power(n: u64) -> Option<(u64, u32)> {
    if n < 2 {
        return None;
    }
    if is_prime(n) {
        return Some((n, 1));
    }
    let (base, exp) = perfect_power(n)?;
    if is_prime(base) {
        Some((base, exp))
    } else {
        None
    }
}

/// Next prime strictly greater than `n` (`None` on `u64` overflow).
pub fn next_prime(n: u64) -> Option<u64> {
    if n < 2 {
        return Some(2);
    }
    if n < 3 {
        return Some(3);
    }
    if n < 5 {
        return Some(5);
    }
    let mut c = n.checked_add(1)?;
    // Advance to mod-30 coprime candidate
    loop {
        if c % 2 != 0 && c % 3 != 0 && c % 5 != 0 {
            break;
        }
        c = c.checked_add(1)?;
    }
    // Mod-30 wheel steps from residue class
    const GAPS: [u64; 8] = [6, 4, 2, 4, 2, 4, 6, 2];
    let mut idx = match c % 30 {
        1 => 0,
        7 => 1,
        11 => 2,
        13 => 3,
        17 => 4,
        19 => 5,
        23 => 6,
        29 => 7,
        _ => unreachable!(),
    };
    loop {
        if is_prime(c) {
            return Some(c);
        }
        c = c.checked_add(GAPS[idx])?;
        idx = (idx + 1) & 7;
    }
}

/// SymPy-style alias for [`next_prime`].
#[inline]
pub fn nextprime(n: u64) -> Option<u64> {
    next_prime(n)
}

/// Largest prime strictly less than `n` (`None` if `n <= 2`).
pub fn prev_prime(n: u64) -> Option<u64> {
    if n <= 2 {
        return None;
    }
    if n == 3 {
        return Some(2);
    }
    if n <= 5 {
        return Some(3);
    }
    let mut c = n - 1;
    if c & 1 == 0 {
        c -= 1;
    }
    while c >= 5 {
        if is_prime(c) {
            return Some(c);
        }
        c -= 2;
    }
    Some(3)
}

/// SymPy-style alias for [`prev_prime`].
#[inline]
pub fn prevprime(n: u64) -> Option<u64> {
    prev_prime(n)
}

/// Next prime strictly greater than `n` (`u128`).
pub fn next_prime_u128(n: u128) -> Option<u128> {
    if n < 2 {
        return Some(2);
    }
    let mut c = n.checked_add(1)?;
    if c & 1 == 0 {
        c = c.checked_add(1)?;
    }
    loop {
        if is_prime_u128(c) {
            return Some(c);
        }
        c = c.checked_add(2)?;
    }
}

/// Largest prime strictly less than `n` (`u128`).
pub fn prev_prime_u128(n: u128) -> Option<u128> {
    if n <= 2 {
        return None;
    }
    if n == 3 {
        return Some(2);
    }
    let mut c = (n - 1) | 1;
    while c >= 3 {
        if is_prime_u128(c) {
            return Some(c);
        }
        c -= 2;
    }
    Some(2)
}

/// Next probable prime strictly greater than `n` (`BigUint`).
pub fn next_prime_big(n: &BigUint) -> BigUint {
    if n < &BigUint::from_u64(2) {
        return BigUint::from_u64(2);
    }
    let mut c = n.clone();
    c.add_u64_assign(1);
    if c.is_even() {
        c.add_u64_assign(1);
    }
    while !is_prime_big(&c) {
        c.add_u64_assign(2);
    }
    c
}

/// Largest probable prime strictly less than `n` (`BigUint`).
pub fn prev_prime_big(n: &BigUint) -> Option<BigUint> {
    if n <= &BigUint::from_u64(2) {
        return None;
    }
    if n == &BigUint::from_u64(3) {
        return Some(BigUint::from_u64(2));
    }
    let mut c = n.clone();
    c.sub_u64_assign(1);
    if c.is_even() {
        c.sub_u64_assign(1);
    }
    while c >= BigUint::from_u64(3) {
        if is_prime_big(&c) {
            return Some(c);
        }
        c.sub_u64_assign(2);
    }
    Some(BigUint::from_u64(2))
}

/// Fast odd-only bit-packed Sieve of Eratosthenes returning all primes `<= limit`.
pub fn sieve_primes(limit: usize) -> Vec<u64> {
    if limit < 2 {
        return Vec::new();
    }
    if limit == 2 {
        return vec![2];
    }
    let odd_count = (limit - 1) / 2; // odd numbers 3, 5, ..., <= limit; index i -> 2*i + 3
    let words = odd_count.div_ceil(64);
    let mut is_comp = vec![0u64; words];
    let sqrt_lim = isqrt(limit as u64) as usize;
    let max_i = if sqrt_lim >= 3 {
        (sqrt_lim - 3) / 2 + 1
    } else {
        0
    };

    for i in 0..max_i {
        if (is_comp[i >> 6] >> (i & 63)) & 1 == 0 {
            let p = 2 * i + 3;
            let mut j = (p * p - 3) / 2;
            while j < odd_count {
                is_comp[j >> 6] |= 1u64 << (j & 63);
                j += p;
            }
        }
    }

    let approx = ((limit as f64) / (limit as f64).ln().max(1.0) * 1.15) as usize + 16;
    let mut primes = Vec::with_capacity(approx);
    primes.push(2);
    for (w, &comp_word) in is_comp.iter().enumerate().take(words) {
        let mut valid = !comp_word;
        if w + 1 == words && (odd_count & 63) != 0 {
            valid &= (1u64 << (odd_count & 63)) - 1;
        }
        let base = 2 * (w * 64) + 3;
        while valid != 0 {
            let tz = valid.trailing_zeros() as usize;
            primes.push((base + 2 * tz) as u64);
            valid &= valid - 1;
        }
    }
    primes
}

/// Lazy segmented-sieve iterator yielding all primes in half-open `[lo, hi)`.
pub struct PrimeIter {
    hi_excl: u64,
    base_primes: Vec<u64>,
    offsets: Vec<u64>,
    seg_lo: u64,
    seg_bits: Vec<u64>,
    seg_words: usize,
    cur_word: usize,
    cur_word_bits: u64,
    emit_two: bool,
    done: bool,
}

impl PrimeIter {
    /// Create a lazy segmented-sieve iterator over `[lo, hi)` (matching SymPy `primerange(lo, hi)`).
    pub fn new(lo: u64, hi: u64) -> Self {
        if hi <= 2 || lo >= hi {
            return Self {
                hi_excl: hi,
                base_primes: Vec::new(),
                offsets: Vec::new(),
                seg_lo: 0,
                seg_bits: Vec::new(),
                seg_words: 0,
                cur_word: 0,
                cur_word_bits: 0,
                emit_two: false,
                done: true,
            };
        }
        let emit_two = lo <= 2 && hi > 2;
        let odd_lo = if lo <= 3 {
            3
        } else if lo & 1 == 0 {
            lo + 1
        } else {
            lo
        };
        let sqrt_hi = isqrt(hi - 1) as usize;
        let base_primes: Vec<u64> = sieve_primes(sqrt_hi)
            .into_iter()
            .filter(|&p| p >= 3)
            .collect();

        let offsets: Vec<u64> = base_primes
            .iter()
            .map(|&p| {
                let pp = p * p;
                let first_mult = if pp >= odd_lo {
                    pp
                } else {
                    let rem = odd_lo % p;
                    let mut m = if rem == 0 { odd_lo } else { odd_lo + (p - rem) };
                    if m & 1 == 0 {
                        m += p;
                    }
                    m
                };
                (first_mult - odd_lo) >> 1
            })
            .collect();

        const SEG_WORDS: usize = 4096; // 32 KB -> 262,144 odd slots = range of 524,288
        let mut iter = Self {
            hi_excl: hi,
            base_primes,
            offsets,
            seg_lo: odd_lo,
            seg_bits: vec![0u64; SEG_WORDS],
            seg_words: 0,
            cur_word: 0,
            cur_word_bits: 0,
            emit_two,
            done: odd_lo >= hi,
        };
        if !iter.done {
            iter.refill_segment();
        }
        iter
    }

    fn refill_segment(&mut self) {
        if self.seg_lo >= self.hi_excl {
            self.done = true;
            return;
        }
        const SEG_SLOTS: u64 = 4096 * 64;
        let total_slots = ((self.hi_excl - 1 - self.seg_lo) / 2 + 1).min(SEG_SLOTS) as usize;
        let words = (total_slots + 63) >> 6;
        self.seg_bits[..words].fill(u64::MAX);
        if (total_slots & 63) != 0 {
            self.seg_bits[words - 1] = (1u64 << (total_slots & 63)) - 1;
        }

        for (i, &p) in self.base_primes.iter().enumerate() {
            let pu = p as usize;
            let mut pos = self.offsets[i] as usize;
            while pos < total_slots {
                self.seg_bits[pos >> 6] &= !(1u64 << (pos & 63));
                pos += pu;
            }
            self.offsets[i] = (pos - total_slots) as u64;
        }

        self.seg_words = words;
        self.cur_word = 0;
        self.cur_word_bits = self.seg_bits[0];
    }
}

impl Iterator for PrimeIter {
    type Item = u64;

    fn next(&mut self) -> Option<u64> {
        if self.emit_two {
            self.emit_two = false;
            return Some(2);
        }
        if self.done {
            return None;
        }
        loop {
            if self.cur_word_bits != 0 {
                let tz = self.cur_word_bits.trailing_zeros() as u64;
                self.cur_word_bits &= self.cur_word_bits - 1;
                return Some(self.seg_lo + 2 * (((self.cur_word as u64) << 6) + tz));
            }
            self.cur_word += 1;
            if self.cur_word < self.seg_words {
                self.cur_word_bits = self.seg_bits[self.cur_word];
                continue;
            }
            // Advance to next segment
            let seg_range = (self.seg_words as u64) * 128;
            match self.seg_lo.checked_add(seg_range) {
                Some(next_lo) if next_lo < self.hi_excl => {
                    self.seg_lo = next_lo;
                    self.refill_segment();
                }
                _ => {
                    self.done = true;
                    return None;
                }
            }
        }
    }
}

/// Return all primes in half-open `[lo, hi)` (matching SymPy `primerange(lo, hi)`).
pub fn prime_range(lo: u64, hi: u64) -> Vec<u64> {
    PrimeIter::new(lo, hi).collect()
}

/// SymPy-style alias for [`prime_range`].
#[inline]
pub fn primerange(lo: u64, hi: u64) -> Vec<u64> {
    prime_range(lo, hi)
}

/// Exact integer `k`-th root floor helper for Meissel-Lehmer.
fn icbrt(n: u64) -> u64 {
    let mut x = (n as f64).cbrt() as u64;
    while (x as u128) * (x as u128) * (x as u128) > (n as u128) {
        x -= 1;
    }
    while ((x as u128) + 1) * ((x as u128) + 1) * ((x as u128) + 1) <= (n as u128) {
        x += 1;
    }
    x
}

fn iroot4(n: u64) -> u64 {
    isqrt(isqrt(n))
}

/// Precomputed Meissel-Lehmer context with fast `O(1)` small `pi(x)` and `phi(x, 7)` wheel.
struct PiContext {
    primes: Vec<u64>,   // 0-indexed: primes[0] = 2
    pi_small: Vec<u32>, // pi_small[v] = pi(v) for v < pi_small.len()
    phi_cache: HashMap<(u64, usize), u64>,
    pi_cache: HashMap<u64, u64>,
}

/// Precomputed exact wheel for `phi(x, 7)` (first 7 primes: 2, 3, 5, 7, 11, 13, 17, period 510_510).
/// Wait: 510_510 fits in ~2 MB if u32, or 510_510 bytes if we only store delta or use period 30_030 (`a = 6`: 2,3,5,7,11,13)!
/// Period `M = 30_030` (`a = 6`, totient = 5760) is only 30 KB (fits in L1 cache!).
const WHEEL6_MOD: usize = 30_030;
const WHEEL6_PHI: u64 = 5_760;

fn build_wheel6() -> Vec<u16> {
    let mut coprime = vec![true; WHEEL6_MOD];
    for &p in &[2usize, 3, 5, 7, 11, 13] {
        let mut j = 0;
        while j < WHEEL6_MOD {
            coprime[j] = false;
            j += p;
        }
    }
    let mut pref = vec![0u16; WHEEL6_MOD + 1];
    let mut acc = 0u16;
    for i in 1..=WHEEL6_MOD {
        if coprime[i % WHEEL6_MOD] {
            acc += 1;
        }
        pref[i] = acc;
    }
    pref
}

impl PiContext {
    fn new(sieve_lim: usize) -> Self {
        let primes = sieve_primes(sieve_lim);
        let mut pi_small = vec![0u32; sieve_lim + 1];
        let mut count = 0u32;
        let mut p_idx = 0usize;
        for (v, slot) in pi_small.iter_mut().enumerate().take(sieve_lim + 1) {
            while p_idx < primes.len() && primes[p_idx] as usize == v {
                count += 1;
                p_idx += 1;
            }
            *slot = count;
        }
        Self {
            primes,
            pi_small,
            phi_cache: HashMap::new(),
            pi_cache: HashMap::new(),
        }
    }

    #[inline]
    fn pi_le_lim(&self, x: u64) -> u64 {
        self.pi_small[x as usize] as u64
    }

    fn phi(&mut self, x: u64, a: usize, wheel6: &[u16]) -> u64 {
        if a == 0 {
            return x;
        }
        if x == 0 {
            return 0;
        }
        if a == 6 {
            let full = x / (WHEEL6_MOD as u64);
            let rem = (x % (WHEEL6_MOD as u64)) as usize;
            return full * WHEEL6_PHI + (wheel6[rem] as u64);
        }
        if a < 6 {
            // Fast tiny recursion down to a == 0
            if a == 1 {
                return (x + 1) >> 1;
            }
            if x < self.primes[a - 1] {
                return 1;
            }
            return self.phi(x, a - 1, wheel6) - self.phi(x / self.primes[a - 1], a - 1, wheel6);
        }
        let p_a = self.primes[a - 1];
        if x < p_a {
            return 1;
        }
        if (x as usize) < self.pi_small.len() && x < p_a * p_a {
            return self.pi_le_lim(x) - (a as u64) + 1;
        }
        if let Some(&cached) = self.phi_cache.get(&(x, a)) {
            return cached;
        }
        let res = self.phi(x, a - 1, wheel6) - self.phi(x / p_a, a - 1, wheel6);
        if x < 10_000_000 {
            self.phi_cache.insert((x, a), res);
        }
        res
    }

    fn pi(&mut self, x: u64, wheel6: &[u16]) -> u64 {
        if (x as usize) < self.pi_small.len() {
            return self.pi_le_lim(x);
        }
        if let Some(&cached) = self.pi_cache.get(&x) {
            return cached;
        }
        let a = self.pi_le_lim(iroot4(x)) as usize;
        let b = self.pi_le_lim(isqrt(x)) as usize;
        let c = self.pi_le_lim(icbrt(x)) as usize;

        let mut sum = self.phi(x, a, wheel6) + (((b + a - 2) * (b - a + 1)) / 2) as u64;
        for i in (a + 1)..=b {
            let p_i = self.primes[i - 1];
            let w = x / p_i;
            sum -= self.pi(w, wheel6);
            if i <= c {
                let b_i = self.pi_le_lim(isqrt(w)) as usize;
                for j in i..=b_i {
                    let p_j = self.primes[j - 1];
                    sum -= self.pi(w / p_j, wheel6) - ((j - 1) as u64);
                }
            }
        }
        self.pi_cache.insert(x, sum);
        sum
    }
}

/// Exact prime-counting function `pi(x)`: number of primes `<= x` (sublinear Meissel-Lehmer).
pub fn prime_pi(x: u64) -> u64 {
    if x < 2 {
        return 0;
    }
    if x <= 100_000 {
        return sieve_primes(x as usize).len() as u64;
    }
    // Sieve up to max(isqrt(x) + 1, min(x^(2/3), 8_000_000)) so almost all P2/P3 lookups are O(1)!
    let sx = (isqrt(x) as usize) + 1;
    let x23 = ((x as f64).powf(2.0 / 3.0) as usize).min(8_000_000);
    let sieve_lim = sx.max(x23);
    let wheel6 = build_wheel6();
    let mut ctx = PiContext::new(sieve_lim);
    ctx.pi(x, &wheel6)
}

/// SymPy-style alias for [`prime_pi`].
#[inline]
pub fn primepi(x: u64) -> u64 {
    prime_pi(x)
}

/// 1-indexed `n`-th prime (`nth_prime(1) == Some(2)`, `nth_prime(0) == None`, `None` on overflow).
pub fn nth_prime(n: u64) -> Option<u64> {
    if n == 0 {
        return None;
    }
    if n <= 6 {
        return Some([2, 3, 5, 7, 11, 13][(n - 1) as usize]);
    }
    let nf = n as f64;
    let lnn = nf.ln();
    let lnlnn = lnn.ln();
    // Rosser-Schoenfeld / Dusart tight bounds for n >= 6
    let lo_est = (nf * (lnn + lnlnn - 1.0 + (lnlnn - 2.1) / lnn))
        .floor()
        .max(13.0) as u64;
    let hi_est = (nf * (lnn + lnlnn - 0.9 + (lnlnn - 1.9) / lnn)).ceil() as u64;

    // Refine with binary search using prime_pi until interval is small (<= 500_000)
    let mut lo = lo_est;
    let mut hi = hi_est.max(lo + 64);
    while prime_pi(hi) < n {
        hi = hi.checked_mul(2)?;
    }
    while hi - lo > 400_000 {
        let mid = lo + (hi - lo) / 2;
        if prime_pi(mid) < n {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    let count_before = if lo > 0 { prime_pi(lo - 1) } else { 0 };
    let target_offset = (n - count_before - 1) as usize;
    PrimeIter::new(lo, hi.saturating_add(1)).nth(target_offset)
}

/// Product of the first `n` primes (`primorial(0) == 1`, `primorial(3) == 30`).
pub fn primorial(n: usize) -> BigUint {
    if n == 0 {
        return BigUint::one();
    }
    // Upper bound for p_n
    let bound = if n < 6 {
        15
    } else {
        let nf = n as f64;
        (nf * (nf.ln() + nf.ln().ln()) + 16.0) as usize
    };
    let ps = sieve_primes(bound);
    let mut prod = BigUint::one();
    for &p in ps.iter().take(n) {
        prod.mul_u64_assign(p);
    }
    prod
}

/// Product of all primes `<= x` (`x#`).
pub fn primorial_upto(x: u64) -> BigUint {
    let mut prod = BigUint::one();
    for p in PrimeIter::new(2, x.saturating_add(1)) {
        prod.mul_u64_assign(p);
    }
    prod
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_primality_and_pi() {
        assert!(is_prime(2) && is_prime(5363222357));
        assert!(!is_prime(1) && !is_prime(561) && !is_prime(341550071728321));
        assert!(is_prime_u128(
            170_141_183_460_469_231_731_687_303_715_884_105_727
        )); // M127
        assert!(!is_prime_u128(
            170_141_183_460_469_231_731_687_303_715_884_105_729
        ));
        assert_eq!(is_prime_power(243), Some((3, 5)));
        assert_eq!(is_prime_power(36), None);

        // Boundary around 100_000 + powers of 10
        assert_eq!(prime_pi(100_000), 9_592);
        assert_eq!(prime_pi(100_001), 9_592);
        assert_eq!(prime_pi(100_003), 9_593);
        assert_eq!(prime_pi(1_000_000), 78_498);
        assert_eq!(prime_pi(10_000_000), 664_579);
        assert_eq!(nth_prime(1), Some(2));
        assert_eq!(nth_prime(10_000), Some(104_729));
    }
}
