//! Fast 64-bit and 128-bit core arithmetic, subtraction-REDC Montgomery multiplication,
//! GCD/extended GCD, modular inversion, and integer roots/perfect-power detection.

use crate::error::NTheoryError;

/// 128-entry lookup table for `n^(-1) mod 256` indexed by `(n >> 1) & 127` (for odd `n`).
const INV_MOD_256: [u8; 128] = {
    let mut tab = [0u8; 128];
    let mut i = 0usize;
    while i < 128 {
        let n = (2 * i + 1) as u8;
        let mut x = n.wrapping_mul(3) ^ 2;
        x = x.wrapping_mul(2u8.wrapping_sub(n.wrapping_mul(x)));
        tab[i] = x;
        i += 1;
    }
    tab
};

/// Compute `n^(-1) mod 2^64` for odd `n`.
#[inline(always)]
pub fn inv_mod_2_64(n: u64) -> u64 {
    debug_assert!(n & 1 == 1);
    let mut x = INV_MOD_256[((n >> 1) & 127) as usize] as u64;
    x = x.wrapping_mul(2u64.wrapping_sub(n.wrapping_mul(x)));
    x = x.wrapping_mul(2u64.wrapping_sub(n.wrapping_mul(x)));
    x = x.wrapping_mul(2u64.wrapping_sub(n.wrapping_mul(x)));
    x
}

/// Compute `n^(-1) mod 2^128` for odd `n`.
#[inline(always)]
pub fn inv_mod_2_128(n: u128) -> u128 {
    debug_assert!(n & 1 == 1);
    let mut x = inv_mod_2_64(n as u64) as u128;
    x = x.wrapping_mul(2u128.wrapping_sub(n.wrapping_mul(x)));
    x
}

/// Subtraction-REDC 64-bit Montgomery multiplication: `a * b * 2^(-64) mod n`.
/// Valid for ALL odd `n < 2^64` and `a, b < n`.
#[inline(always)]
pub fn mont_mul_64(a: u64, b: u64, n: u64, n_inv: u64) -> u64 {
    let t = (a as u128) * (b as u128);
    let t_lo = t as u64;
    let t_hi = (t >> 64) as u64;
    let m = t_lo.wrapping_mul(n_inv);
    let u_hi = (((m as u128) * (n as u128)) >> 64) as u64;
    let (diff, borrow) = t_hi.overflowing_sub(u_hi);
    if borrow {
        diff.wrapping_add(n)
    } else {
        diff
    }
}

/// Modular addition `(a + b) mod n` for `a, b < n` (safe for all `n <= u64::MAX`).
#[inline(always)]
pub fn add_mod_u64(a: u64, b: u64, n: u64) -> u64 {
    let (s, ov) = a.overflowing_add(b);
    if ov || s >= n {
        s.wrapping_sub(n)
    } else {
        s
    }
}

/// Modular subtraction `(a - b) mod n` for `a, b < n`.
#[inline(always)]
pub fn sub_mod_u64(a: u64, b: u64, n: u64) -> u64 {
    if a >= b {
        a - b
    } else {
        a.wrapping_add(n).wrapping_sub(b)
    }
}

/// Exact 256-bit product `(lo, hi)` of two `u128` integers.
#[inline(always)]
pub fn mul_wide_u128(a: u128, b: u128) -> (u128, u128) {
    let a_lo = a as u64 as u128;
    let a_hi = (a >> 64) as u64 as u128;
    let b_lo = b as u64 as u128;
    let b_hi = (b >> 64) as u64 as u128;

    let p0 = a_lo * b_lo;
    let p1 = a_lo * b_hi;
    let p2 = a_hi * b_lo;
    let p3 = a_hi * b_hi;

    let mid = (p0 >> 64) + (p1 as u64 as u128) + (p2 as u64 as u128);
    let lo = (p0 as u64 as u128) | ((mid as u64 as u128) << 64);
    let hi = p3 + (p1 >> 64) + (p2 >> 64) + (mid >> 64);
    (lo, hi)
}

/// Subtraction-REDC 128-bit Montgomery multiplication: `a * b * 2^(-128) mod n`.
/// Valid for ALL odd `n < 2^128` and `a, b < n`.
#[inline(always)]
pub fn mont_mul_128(a: u128, b: u128, n: u128, n_inv: u128) -> u128 {
    let (t_lo, t_hi) = mul_wide_u128(a, b);
    let m = t_lo.wrapping_mul(n_inv);
    let (_, u_hi) = mul_wide_u128(m, n);
    let (diff, borrow) = t_hi.overflowing_sub(u_hi);
    if borrow {
        diff.wrapping_add(n)
    } else {
        diff
    }
}

/// Modular addition `(a + b) mod n` for `a, b < n` (`u128`).
#[inline(always)]
pub fn add_mod_u128(a: u128, b: u128, n: u128) -> u128 {
    let (s, ov) = a.overflowing_add(b);
    if ov || s >= n {
        s.wrapping_sub(n)
    } else {
        s
    }
}

/// Modular subtraction `(a - b) mod n` for `a, b < n` (`u128`).
#[inline(always)]
pub fn sub_mod_u128(a: u128, b: u128, n: u128) -> u128 {
    if a >= b {
        a - b
    } else {
        a.wrapping_add(n).wrapping_sub(b)
    }
}

/// Fast 64-bit Montgomery context for odd moduli `n > 1`.
#[derive(Clone, Copy, Debug)]
pub struct Mont64 {
    pub n: u64,
    pub n_inv: u64,
    pub r1: u64, // 2^64 mod n
    pub r2: u64, // 2^128 mod n
}

impl Mont64 {
    #[inline(always)]
    pub fn new(n: u64) -> Self {
        debug_assert!(n & 1 == 1 && n > 1);
        let n_inv = inv_mod_2_64(n);
        let r1 = 0u64.wrapping_sub(n) % n;
        let r2 = ((r1 as u128 * r1 as u128) % (n as u128)) as u64;
        Self { n, n_inv, r1, r2 }
    }

    #[inline(always)]
    pub fn to_mont(&self, a: u64) -> u64 {
        mont_mul_64(a % self.n, self.r2, self.n, self.n_inv)
    }

    #[inline(always)]
    pub fn from_mont(&self, a: u64) -> u64 {
        mont_mul_64(a, 1, self.n, self.n_inv)
    }

    #[inline(always)]
    pub fn mul(&self, a: u64, b: u64) -> u64 {
        mont_mul_64(a, b, self.n, self.n_inv)
    }

    #[inline(always)]
    pub fn pow_mont(&self, mut base: u64, mut exp: u64) -> u64 {
        let mut res = self.r1;
        while exp > 0 {
            if exp & 1 != 0 {
                res = self.mul(res, base);
            }
            exp >>= 1;
            if exp > 0 {
                base = self.mul(base, base);
            }
        }
        res
    }

    #[inline(always)]
    pub fn pow(&self, base: u64, exp: u64) -> u64 {
        self.from_mont(self.pow_mont(self.to_mont(base), exp))
    }
}

/// Fast 128-bit Montgomery context for odd moduli `n > 1`.
#[derive(Clone, Copy, Debug)]
pub struct Mont128 {
    pub n: u128,
    pub n_inv: u128,
    pub r1: u128, // 2^128 mod n
    pub r2: u128, // 2^256 mod n
}

impl Mont128 {
    #[inline]
    pub fn new(n: u128) -> Self {
        debug_assert!(n & 1 == 1 && n > 1);
        let n_inv = inv_mod_2_128(n);
        let r1 = 0u128.wrapping_sub(n) % n;
        let r2 = mul_mod_u128_generic(r1, r1, n);
        Self { n, n_inv, r1, r2 }
    }

    #[inline(always)]
    pub fn to_mont(&self, a: u128) -> u128 {
        mont_mul_128(a % self.n, self.r2, self.n, self.n_inv)
    }

    #[inline(always)]
    pub fn from_mont(&self, a: u128) -> u128 {
        mont_mul_128(a, 1, self.n, self.n_inv)
    }

    #[inline(always)]
    pub fn mul(&self, a: u128, b: u128) -> u128 {
        mont_mul_128(a, b, self.n, self.n_inv)
    }

    #[inline(always)]
    pub fn pow_mont(&self, mut base: u128, mut exp: u128) -> u128 {
        let mut res = self.r1;
        while exp > 0 {
            if exp & 1 != 0 {
                res = self.mul(res, base);
            }
            exp >>= 1;
            if exp > 0 {
                base = self.mul(base, base);
            }
        }
        res
    }

    #[inline(always)]
    pub fn pow(&self, base: u128, exp: u128) -> u128 {
        self.from_mont(self.pow_mont(self.to_mont(base), exp))
    }
}

/// Compute `(a * b) % m` for `u64` without overflow.
#[inline(always)]
pub fn mul_mod(a: u64, b: u64, m: u64) -> u64 {
    assert!(m > 0, "modulus must be non-zero");
    ((a as u128 * b as u128) % (m as u128)) as u64
}

/// Compute `base^exp % m` for `u64`.
#[inline]
pub fn pow_mod(base: u64, exp: u64, m: u64) -> u64 {
    assert!(m > 0, "modulus must be non-zero");
    if m == 1 {
        return 0;
    }
    if m & 1 == 1 {
        return Mont64::new(m).pow(base, exp);
    }
    let mut res = 1u64;
    let mut b = base % m;
    let mut e = exp;
    while e > 0 {
        if e & 1 != 0 {
            res = mul_mod(res, b, m);
        }
        e >>= 1;
        if e > 0 {
            b = mul_mod(b, b, m);
        }
    }
    res
}

/// Overflow-safe `(a * b) % m` for arbitrary `u128` (works for all `m <= u128::MAX`).
pub fn mul_mod_u128_generic(mut a: u128, mut b: u128, m: u128) -> u128 {
    assert!(m > 0, "modulus must be non-zero");
    if m == 1 {
        return 0;
    }
    a %= m;
    b %= m;
    if let Some(p) = a.checked_mul(b) {
        return p % m;
    }
    let mut res = 0u128;
    while b > 0 {
        if b & 1 != 0 {
            res = add_mod_u128(res, a, m);
        }
        a = add_mod_u128(a, a, m);
        b >>= 1;
    }
    res
}

/// Fast `(a * b) % m` for `u128`.
#[inline]
pub fn mul_mod_u128(a: u128, b: u128, m: u128) -> u128 {
    assert!(m > 0, "modulus must be non-zero");
    if m <= (u64::MAX as u128) {
        return ((a % m) * (b % m)) % m;
    }
    mul_mod_u128_generic(a, b, m)
}

/// Fast `base^exp % m` for `u128` (uses 128-bit Montgomery for odd `m`).
pub fn pow_mod_u128(base: u128, exp: u128, m: u128) -> u128 {
    assert!(m > 0, "modulus must be non-zero");
    if m == 1 {
        return 0;
    }
    if let Ok(m64) = u64::try_from(m) {
        if let Ok(e64) = u64::try_from(exp) {
            return pow_mod((base % m) as u64, e64, m64) as u128;
        }
    }
    if m & 1 == 1 {
        return Mont128::new(m).pow(base, exp);
    }
    let mut res = 1u128;
    let mut b = base % m;
    let mut e = exp;
    while e > 0 {
        if e & 1 != 0 {
            res = mul_mod_u128_generic(res, b, m);
        }
        e >>= 1;
        if e > 0 {
            b = mul_mod_u128_generic(b, b, m);
        }
    }
    res
}

/// Binary GCD for `u64`.
#[inline]
pub fn gcd(mut a: u64, mut b: u64) -> u64 {
    if a == 0 {
        return b;
    }
    if b == 0 {
        return a;
    }
    let shift = (a | b).trailing_zeros();
    a >>= a.trailing_zeros();
    loop {
        b >>= b.trailing_zeros();
        if a > b {
            std::mem::swap(&mut a, &mut b);
        }
        b -= a;
        if b == 0 {
            return a << shift;
        }
    }
}

/// Binary GCD for `u128`.
#[inline]
pub fn gcd_u128(mut a: u128, mut b: u128) -> u128 {
    if a == 0 {
        return b;
    }
    if b == 0 {
        return a;
    }
    let shift = (a | b).trailing_zeros();
    a >>= a.trailing_zeros();
    loop {
        b >>= b.trailing_zeros();
        if a > b {
            std::mem::swap(&mut a, &mut b);
        }
        b -= a;
        if b == 0 {
            return a << shift;
        }
    }
}

/// Least common multiple for `u64`, returning `None` on overflow.
#[inline]
pub fn checked_lcm(a: u64, b: u64) -> Option<u64> {
    if a == 0 || b == 0 {
        return Some(0);
    }
    (a / gcd(a, b)).checked_mul(b)
}

/// Least common multiple for `u64` (panics on overflow).
#[inline]
pub fn lcm(a: u64, b: u64) -> u64 {
    checked_lcm(a, b).expect("lcm overflow")
}

/// Least common multiple for `u128`, returning `None` on overflow.
#[inline]
pub fn checked_lcm_u128(a: u128, b: u128) -> Option<u128> {
    if a == 0 || b == 0 {
        return Some(0);
    }
    (a / gcd_u128(a, b)).checked_mul(b)
}

/// Extended Euclidean algorithm: returns `(g, x, y)` such that `a * x + b * y == g >= 0`.
pub fn egcd(a: i128, b: i128) -> (i128, i128, i128) {
    let mut old_r = a;
    let mut r = b;
    let mut old_s = 1i128;
    let mut s = 0i128;
    let mut old_t = 0i128;
    let mut t = 1i128;
    while r != 0 {
        let q = old_r / r;
        let nr = old_r - q * r;
        old_r = r;
        r = nr;
        let ns = old_s - q * s;
        old_s = s;
        s = ns;
        let nt = old_t - q * t;
        old_t = t;
        t = nt;
    }
    if old_r < 0 {
        (-old_r, -old_s, -old_t)
    } else {
        (old_r, old_s, old_t)
    }
}

/// Modular inverse `a^(-1) mod m` for `u64`, returning `Err(NTheoryError::NotCoprime)` if `gcd(a, m) != 1`.
pub fn mod_inv(a: u64, m: u64) -> Result<u64, NTheoryError> {
    if m == 0 {
        return Err(NTheoryError::InvalidArgument("modulus must be positive"));
    }
    if m == 1 {
        return Ok(0);
    }
    let (g, x, _) = egcd((a % m) as i128, m as i128);
    if g != 1 {
        return Err(NTheoryError::NotCoprime);
    }
    Ok(x.rem_euclid(m as i128) as u64)
}

/// Modular inverse `a^(-1) mod m` for `u128` (safe for all `m <= u128::MAX`).
pub fn mod_inv_u128(a: u128, m: u128) -> Result<u128, NTheoryError> {
    if m == 0 {
        return Err(NTheoryError::InvalidArgument("modulus must be positive"));
    }
    if m == 1 {
        return Ok(0);
    }
    let mut r0 = m;
    let mut r1 = a % m;
    let mut t0 = 0u128;
    let mut t1 = 1u128;
    let mut neg0 = false;
    let mut neg1 = false;
    while r1 != 0 {
        let q = r0 / r1;
        let r2 = r0 - q * r1;
        let qt1 = q.wrapping_mul(t1);
        let (t2, neg2) = if neg0 != neg1 {
            (t0.wrapping_add(qt1), neg0)
        } else if t0 >= qt1 {
            (t0 - qt1, neg0)
        } else {
            (qt1 - t0, !neg1)
        };
        r0 = r1;
        r1 = r2;
        t0 = t1;
        neg0 = neg1;
        t1 = t2;
        neg1 = neg2;
    }
    if r0 != 1 {
        return Err(NTheoryError::NotCoprime);
    }
    let tm = t0 % m;
    if neg0 && tm != 0 {
        Ok(m - tm)
    } else {
        Ok(tm)
    }
}

/// Exact integer square root `floor(sqrt(n))` for `u64`.
#[inline]
pub fn isqrt(n: u64) -> u64 {
    if n < 2 {
        return n;
    }
    let mut x = (n as f64).sqrt() as u64;
    while (x as u128) * (x as u128) > (n as u128) {
        x -= 1;
    }
    while ((x as u128) + 1) * ((x as u128) + 1) <= (n as u128) {
        x += 1;
    }
    x
}

/// Exact integer square root `floor(sqrt(n))` for `u128`.
pub fn isqrt_u128(n: u128) -> u128 {
    if n < 2 {
        return n;
    }
    let shift = (128 - n.leading_zeros()).div_ceil(2);
    let mut x = 1u128 << shift;
    loop {
        let next = (x + n / x) >> 1;
        if next >= x {
            return x;
        }
        x = next;
    }
}

/// Returns `true` iff `n` is a perfect square (`u128`).
#[inline]
pub fn is_square_u128(n: u128) -> bool {
    const MASK64: u64 = 0x0202_0212_0203_0213;
    if (MASK64 >> ((n as u64) & 63)) & 1 == 0 {
        return false;
    }
    let r = isqrt_u128(n);
    r * r == n
}

/// Exact integer `k`-th root `(floor(n^(1/k)), exact)` for `u64`.
pub fn integer_nthroot(n: u64, k: u32) -> (u64, bool) {
    assert!(k >= 1, "root exponent k must be >= 1");
    if k == 1 || n <= 1 {
        return (n, true);
    }
    if k == 2 {
        let r = isqrt(n);
        return (r, r * r == n);
    }
    if k >= 64 {
        return (1, n == 1);
    }
    let mut x = (n as f64).powf(1.0 / (k as f64)).round() as u64;
    if x == 0 {
        x = 1;
    }
    let pow_checked = |base: u64| -> Option<u64> { base.checked_pow(k) };
    while pow_checked(x).map_or(true, |p| p > n) {
        x -= 1;
    }
    while let Some(p) = pow_checked(x + 1) {
        if p <= n {
            x += 1;
        } else {
            break;
        }
    }
    (x, pow_checked(x) == Some(n))
}

/// Returns `true` iff `n` is a perfect square.
#[inline]
pub fn is_square(n: u64) -> bool {
    const MASK64: u64 = 0x0202_0212_0203_0213;
    if (MASK64 >> (n & 63)) & 1 == 0 {
        return false;
    }
    let r = isqrt(n);
    r * r == n
}

/// Detect whether `n >= 2` is a perfect power `b^e` with `e >= 2`.
/// Returns `Some((b, e))` with maximal `e` (matching SymPy's `perfect_power`), or `None`.
pub fn perfect_power(n: u64) -> Option<(u64, u32)> {
    if n < 4 {
        return None;
    }
    let max_e = 63 - n.leading_zeros();
    for e in (2..=max_e).rev() {
        let (r, exact) = integer_nthroot(n, e);
        if exact {
            return Some((r, e));
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mont128_and_inv() {
        let n: u128 = 170_141_183_460_469_231_731_687_303_715_884_105_727; // M127
        let ctx = Mont128::new(n);
        assert_eq!(ctx.pow(2, n - 1), 1);
        assert_eq!(ctx.pow(10, n - 1), 1);
        let val = 12345678901234567890123456789u128;
        let inv = mod_inv_u128(val, n).unwrap();
        assert_eq!(mul_mod_u128(val, inv, n), 1);
        // Near-MAX modulus test (m >= 2^127)
        let m2 = (1u128 << 127) + 15;
        let inv2 = mod_inv_u128(7, m2).unwrap();
        assert_eq!(mul_mod_u128(7, inv2, m2), 1);
    }

    #[test]
    fn test_roots_and_powers() {
        assert_eq!(isqrt(u64::MAX), 4_294_967_295);
        assert_eq!(perfect_power(64), Some((2, 6)));
        assert_eq!(perfect_power(1000), Some((10, 3)));
        assert_eq!(perfect_power(999), None);
        assert!(is_square(1_000_000_000_000));
        assert!(!is_square(1_000_000_000_001));
    }
}
