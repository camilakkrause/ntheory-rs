//! Arbitrary-precision unsigned integers (`BigUint`), CIOS Montgomery arithmetic (`BigMont`),
//! and arbitrary-precision Jacobi symbol.

use std::cmp::Ordering;
use std::fmt;
use std::str::FromStr;

use crate::arith::{inv_mod_2_64, isqrt_u128};
use crate::error::NTheoryError;

/// Arbitrary-precision unsigned integer stored as little-endian base-$2^{64}$ limbs.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct BigUint {
    /// Little-endian base-`2^64` limbs, normalized with no trailing zero limbs.
    pub limbs: Vec<u64>,
}

impl BigUint {
    /// Returns `0`.
    #[inline]
    pub fn zero() -> Self {
        Self { limbs: Vec::new() }
    }

    /// Returns `1`.
    #[inline]
    pub fn one() -> Self {
        Self { limbs: vec![1] }
    }

    /// Construct from little-endian base-`2^64` limbs, normalizing trailing zeros.
    #[inline]
    pub fn from_limbs(limbs: Vec<u64>) -> Self {
        let mut r = Self { limbs };
        r.trim();
        r
    }

    /// Construct from a `u64`.
    #[inline]
    pub fn from_u64(v: u64) -> Self {
        if v == 0 {
            Self::zero()
        } else {
            Self { limbs: vec![v] }
        }
    }

    /// Construct from a `u128`.
    #[inline]
    pub fn from_u128(v: u128) -> Self {
        let lo = v as u64;
        let hi = (v >> 64) as u64;
        if hi != 0 {
            Self {
                limbs: vec![lo, hi],
            }
        } else if lo != 0 {
            Self { limbs: vec![lo] }
        } else {
            Self::zero()
        }
    }

    /// Parse a decimal string (allowing `_` visual separators).
    pub fn from_str_radix10(s: &str) -> Option<Self> {
        let trimmed = s.trim();
        if trimmed.is_empty() {
            return None;
        }
        let mut res = Self::zero();
        let mut saw_digit = false;
        for b in trimmed.bytes() {
            if b == b'_' {
                continue;
            }
            if !b.is_ascii_digit() {
                return None;
            }
            saw_digit = true;
            res.mul_u64_assign(10);
            res.add_u64_assign((b - b'0') as u64);
        }
        if saw_digit {
            Some(res)
        } else {
            None
        }
    }

    #[inline]
    pub fn trim(&mut self) {
        while let Some(&0) = self.limbs.last() {
            self.limbs.pop();
        }
    }

    #[inline]
    pub fn is_zero(&self) -> bool {
        self.limbs.is_empty()
    }

    #[inline]
    pub fn is_one(&self) -> bool {
        self.limbs.len() == 1 && self.limbs[0] == 1
    }

    #[inline]
    pub fn is_even(&self) -> bool {
        self.limbs.is_empty() || (self.limbs[0] & 1) == 0
    }

    #[inline]
    pub fn to_u64(&self) -> Option<u64> {
        match self.limbs.len() {
            0 => Some(0),
            1 => Some(self.limbs[0]),
            _ => None,
        }
    }

    #[inline]
    pub fn to_u128(&self) -> Option<u128> {
        match self.limbs.len() {
            0 => Some(0),
            1 => Some(self.limbs[0] as u128),
            2 => Some((self.limbs[0] as u128) | ((self.limbs[1] as u128) << 64)),
            _ => None,
        }
    }

    #[inline]
    pub fn bit_len(&self) -> usize {
        match self.limbs.last() {
            None => 0,
            Some(&top) => (self.limbs.len() - 1) * 64 + (64 - top.leading_zeros() as usize),
        }
    }

    #[inline]
    pub fn bit(&self, idx: usize) -> bool {
        let w = idx >> 6;
        if w >= self.limbs.len() {
            false
        } else {
            ((self.limbs[w] >> (idx & 63)) & 1) != 0
        }
    }

    #[inline]
    pub fn trailing_zeros(&self) -> usize {
        for (i, &w) in self.limbs.iter().enumerate() {
            if w != 0 {
                return i * 64 + w.trailing_zeros() as usize;
            }
        }
        0
    }

    /// Approximate number of decimal digits (within ±1 for quick heuristics).
    pub fn decimal_digits(&self) -> usize {
        if self.is_zero() {
            return 1;
        }
        let approx = ((self.bit_len() as f64) * std::f64::consts::LOG10_2) as usize;
        approx + 1
    }

    pub fn add_u64_assign(&mut self, v: u64) {
        if v == 0 {
            return;
        }
        let mut carry = v as u128;
        for limb in &mut self.limbs {
            let s = (*limb as u128) + carry;
            *limb = s as u64;
            carry = s >> 64;
            if carry == 0 {
                return;
            }
        }
        if carry > 0 {
            self.limbs.push(carry as u64);
        }
    }

    pub fn sub_u64_assign(&mut self, v: u64) {
        if v == 0 {
            return;
        }
        let mut borrow = v as u128;
        for limb in &mut self.limbs {
            let lv = *limb as u128;
            if lv >= borrow {
                *limb = (lv - borrow) as u64;
                borrow = 0;
                break;
            } else {
                *limb = ((1u128 << 64) + lv - borrow) as u64;
                borrow = 1;
            }
        }
        assert!(borrow == 0, "BigUint subtraction underflow");
        self.trim();
    }

    pub fn add(&self, other: &Self) -> Self {
        let n = self.limbs.len().max(other.limbs.len());
        let mut out = Vec::with_capacity(n + 1);
        let mut carry = 0u128;
        for i in 0..n {
            let a = self.limbs.get(i).copied().unwrap_or(0) as u128;
            let b = other.limbs.get(i).copied().unwrap_or(0) as u128;
            let s = a + b + carry;
            out.push(s as u64);
            carry = s >> 64;
        }
        if carry > 0 {
            out.push(carry as u64);
        }
        Self::from_limbs(out)
    }

    pub fn sub(&self, other: &Self) -> Self {
        assert!(self >= other, "BigUint subtraction underflow");
        let mut out = Vec::with_capacity(self.limbs.len());
        let mut borrow = 0i128;
        for i in 0..self.limbs.len() {
            let a = self.limbs[i] as i128;
            let b = other.limbs.get(i).copied().unwrap_or(0) as i128;
            let d = a - b - borrow;
            if d < 0 {
                out.push((d + (1i128 << 64)) as u64);
                borrow = 1;
            } else {
                out.push(d as u64);
                borrow = 0;
            }
        }
        debug_assert!(borrow == 0);
        Self::from_limbs(out)
    }

    pub fn shl(&self, shift: usize) -> Self {
        if self.is_zero() || shift == 0 {
            return self.clone();
        }
        let word_shift = shift / 64;
        let bit_shift = shift % 64;
        let mut out = vec![0u64; self.limbs.len() + word_shift + 1];
        if bit_shift == 0 {
            out[word_shift..word_shift + self.limbs.len()].copy_from_slice(&self.limbs);
        } else {
            let mut carry = 0u64;
            for (i, &w) in self.limbs.iter().enumerate() {
                out[i + word_shift] = (w << bit_shift) | carry;
                carry = w >> (64 - bit_shift);
            }
            out[self.limbs.len() + word_shift] = carry;
        }
        Self::from_limbs(out)
    }

    pub fn shr(&self, shift: usize) -> Self {
        if self.is_zero() || shift == 0 {
            return self.clone();
        }
        let word_shift = shift / 64;
        let bit_shift = shift % 64;
        if word_shift >= self.limbs.len() {
            return Self::zero();
        }
        let new_len = self.limbs.len() - word_shift;
        let mut out = vec![0u64; new_len];
        if bit_shift == 0 {
            out.copy_from_slice(&self.limbs[word_shift..]);
        } else {
            for (i, out_slot) in out.iter_mut().enumerate().take(new_len) {
                let lo = self.limbs[i + word_shift] >> bit_shift;
                let hi = if i + word_shift + 1 < self.limbs.len() {
                    self.limbs[i + word_shift + 1] << (64 - bit_shift)
                } else {
                    0
                };
                *out_slot = lo | hi;
            }
        }
        Self::from_limbs(out)
    }

    pub fn shr_assign(&mut self, shift: usize) {
        if self.is_zero() || shift == 0 {
            return;
        }
        let word_shift = shift / 64;
        let bit_shift = shift % 64;
        if word_shift >= self.limbs.len() {
            self.limbs.clear();
            return;
        }
        let new_len = self.limbs.len() - word_shift;
        if bit_shift == 0 {
            self.limbs.drain(0..word_shift);
        } else {
            for i in 0..new_len {
                let lo = self.limbs[i + word_shift] >> bit_shift;
                let hi = if i + word_shift + 1 < self.limbs.len() {
                    self.limbs[i + word_shift + 1] << (64 - bit_shift)
                } else {
                    0
                };
                self.limbs[i] = lo | hi;
            }
            self.limbs.truncate(new_len);
            self.trim();
        }
    }

    pub fn mul_u64_assign(&mut self, rhs: u64) {
        if rhs == 0 || self.is_zero() {
            self.limbs.clear();
            return;
        }
        if rhs == 1 {
            return;
        }
        let mut carry = 0u128;
        let r = rhs as u128;
        for limb in &mut self.limbs {
            let p = (*limb as u128) * r + carry;
            *limb = p as u64;
            carry = p >> 64;
        }
        if carry > 0 {
            self.limbs.push(carry as u64);
        }
    }

    pub fn mul_u64(&self, rhs: u64) -> Self {
        let mut r = self.clone();
        r.mul_u64_assign(rhs);
        r
    }

    pub fn mul(&self, other: &Self) -> Self {
        if self.is_zero() || other.is_zero() {
            return Self::zero();
        }
        let n = self.limbs.len();
        let m = other.limbs.len();
        if n >= 32 && m >= 32 {
            return self.mul_karatsuba(other);
        }
        let mut out = vec![0u64; n + m];
        for i in 0..n {
            let a = self.limbs[i] as u128;
            let mut carry = 0u128;
            for j in 0..m {
                let p = a * (other.limbs[j] as u128) + (out[i + j] as u128) + carry;
                out[i + j] = p as u64;
                carry = p >> 64;
            }
            out[i + m] = carry as u64;
        }
        Self::from_limbs(out)
    }

    fn mul_karatsuba(&self, other: &Self) -> Self {
        let half = self.limbs.len().max(other.limbs.len()) / 2;
        let split = |v: &Self| -> (Self, Self) {
            if v.limbs.len() <= half {
                (v.clone(), Self::zero())
            } else {
                (
                    Self::from_limbs(v.limbs[..half].to_vec()),
                    Self::from_limbs(v.limbs[half..].to_vec()),
                )
            }
        };
        let (a0, a1) = split(self);
        let (b0, b1) = split(other);
        let z0 = a0.mul(&b0);
        let z2 = a1.mul(&b1);
        let z1 = a0.add(&a1).mul(&b0.add(&b1)).sub(&z0).sub(&z2);
        let mut res = z0;
        let add_shifted = |acc: &mut Self, term: &Self, word_off: usize| {
            if term.is_zero() {
                return;
            }
            let need = word_off + term.limbs.len();
            if acc.limbs.len() < need {
                acc.limbs.resize(need, 0);
            }
            let mut carry = 0u128;
            for i in 0..term.limbs.len() {
                let s = (acc.limbs[word_off + i] as u128) + (term.limbs[i] as u128) + carry;
                acc.limbs[word_off + i] = s as u64;
                carry = s >> 64;
            }
            let mut idx = word_off + term.limbs.len();
            while carry > 0 {
                if idx >= acc.limbs.len() {
                    acc.limbs.push(carry as u64);
                    break;
                }
                let s = (acc.limbs[idx] as u128) + carry;
                acc.limbs[idx] = s as u64;
                carry = s >> 64;
                idx += 1;
            }
        };
        add_shifted(&mut res, &z1, half);
        add_shifted(&mut res, &z2, 2 * half);
        res.trim();
        res
    }

    pub fn rem_u64(&self, d: u64) -> u64 {
        assert!(d > 0, "BigUint modulo by zero");
        let mut rem = 0u128;
        let dm = d as u128;
        for &w in self.limbs.iter().rev() {
            rem = ((rem << 64) | (w as u128)) % dm;
        }
        rem as u64
    }

    pub fn div_rem_u64(&self, d: u64) -> (Self, u64) {
        assert!(d > 0, "BigUint division by zero");
        let mut q = vec![0u64; self.limbs.len()];
        let mut rem = 0u128;
        let dm = d as u128;
        for i in (0..self.limbs.len()).rev() {
            let cur = (rem << 64) | (self.limbs[i] as u128);
            q[i] = (cur / dm) as u64;
            rem = cur % dm;
        }
        (Self::from_limbs(q), rem as u64)
    }

    /// Knuth Algorithm D division: returns `(quotient, remainder)`.
    pub fn div_rem(&self, d: &Self) -> (Self, Self) {
        assert!(!d.is_zero(), "BigUint division by zero");
        if self < d {
            return (Self::zero(), self.clone());
        }
        if d.limbs.len() == 1 {
            let (q, r) = self.div_rem_u64(d.limbs[0]);
            return (q, Self::from_u64(r));
        }

        let n = d.limbs.len();
        let m = self.limbs.len() - n;
        let shift = d.limbs[n - 1].leading_zeros() as usize;

        let vn = d.shl(shift);
        let mut un = self.shl(shift);
        if un.limbs.len() <= m + n {
            un.limbs.resize(m + n + 1, 0);
        }

        let mut q = vec![0u64; m + 1];
        let v_hi = vn.limbs[n - 1] as u128;
        let v_lo = vn.limbs[n - 2] as u128;

        for j in (0..=m).rev() {
            let u_hi = un.limbs[j + n] as u128;
            let u_mid = un.limbs[j + n - 1] as u128;
            let u_lo = un.limbs[j + n - 2] as u128;
            let num = (u_hi << 64) | u_mid;
            let mut qhat = num / v_hi;
            let mut rhat = num % v_hi;
            if qhat >= (1u128 << 64) {
                qhat = (1u128 << 64) - 1;
                rhat = num - qhat * v_hi;
            }
            while rhat < (1u128 << 64) && qhat * v_lo > ((rhat << 64) | u_lo) {
                qhat -= 1;
                rhat += v_hi;
            }

            let mut borrow = 0i128;
            let mut carry = 0u128;
            for i in 0..n {
                let p = qhat * (vn.limbs[i] as u128) + carry;
                carry = p >> 64;
                let p_lo = p as u64 as i128;
                let diff = (un.limbs[j + i] as i128) - p_lo - borrow;
                if diff < 0 {
                    un.limbs[j + i] = (diff + (1i128 << 64)) as u64;
                    borrow = 1;
                } else {
                    un.limbs[j + i] = diff as u64;
                    borrow = 0;
                }
            }
            let diff_top = (un.limbs[j + n] as i128) - (carry as i128) - borrow;
            if diff_top < 0 {
                qhat -= 1;
                let mut add_carry = 0u128;
                for i in 0..n {
                    let s = (un.limbs[j + i] as u128) + (vn.limbs[i] as u128) + add_carry;
                    un.limbs[j + i] = s as u64;
                    add_carry = s >> 64;
                }
                un.limbs[j + n] = ((diff_top + (1i128 << 64)) as u128 + add_carry) as u64;
            } else {
                un.limbs[j + n] = diff_top as u64;
            }
            q[j] = qhat as u64;
        }

        un.limbs.truncate(n);
        un.trim();
        let rem = un.shr(shift);
        (Self::from_limbs(q), rem)
    }

    pub fn rem(&self, d: &Self) -> Self {
        self.div_rem(d).1
    }

    /// Integer exponentiation `self^exp`.
    pub fn pow(&self, mut exp: u32) -> Self {
        let mut res = Self::one();
        let mut base = self.clone();
        while exp > 0 {
            if exp & 1 != 0 {
                res = res.mul(&base);
            }
            exp >>= 1;
            if exp > 0 {
                base = base.mul(&base);
            }
        }
        res
    }

    /// Power of 10: `10^exp`.
    pub fn pow10(exp: usize) -> Self {
        let mut res = Self::one();
        let mut base = Self::from_u64(10);
        let mut e = exp;
        while e > 0 {
            if e & 1 != 0 {
                res = res.mul(&base);
            }
            e >>= 1;
            if e > 0 {
                base = base.mul(&base);
            }
        }
        res
    }

    /// Integer square root `floor(sqrt(self))`.
    pub fn isqrt(&self) -> Self {
        if let Some(v) = self.to_u128() {
            return Self::from_u128(isqrt_u128(v));
        }
        let bits = self.bit_len();
        let mut x = Self::one().shl(bits.div_ceil(2));
        loop {
            let (q, _) = self.div_rem(&x);
            let next = x.add(&q).shr(1);
            if next >= x {
                return x;
            }
            x = next;
        }
    }

    /// Returns `true` iff `self` is a perfect square.
    pub fn is_square(&self) -> bool {
        if self.is_zero() {
            return true;
        }
        const MASK64: u64 = 0x0202_0212_0203_0213;
        if (MASK64 >> (self.limbs[0] & 63)) & 1 == 0 {
            return false;
        }
        let sq = self.isqrt();
        &sq.mul(&sq) == self
    }

    /// Exact integer `k`-th root `(floor(self^(1/k)), exact)`.
    pub fn integer_nthroot(&self, k: u32) -> (Self, bool) {
        assert!(k >= 1, "root exponent k must be >= 1");
        if k == 1 || self.is_zero() || self.is_one() {
            return (self.clone(), true);
        }
        if k == 2 {
            let r = self.isqrt();
            let exact = &r.mul(&r) == self;
            return (r, exact);
        }
        let bits = self.bit_len();
        if (k as usize) > bits {
            return (Self::one(), self.is_one());
        }
        let approx_bits = bits.div_ceil(k as usize);
        let mut x = Self::one().shl(approx_bits);
        let k_big = Self::from_u64(k as u64);
        let km1 = k - 1;
        loop {
            let x_km1 = x.pow(km1);
            let (q, _) = self.div_rem(&x_km1);
            let numer = x.mul_u64(km1 as u64).add(&q);
            let (next, _) = numer.div_rem(&k_big);
            if next >= x {
                let exact = &x.pow(k) == self;
                return (x, exact);
            }
            x = next;
        }
    }

    /// Detect whether `self >= 2` is a perfect power `b^e` with `e >= 2` (maximal `e`).
    pub fn perfect_power(&self) -> Option<(Self, u32)> {
        if self.bit_len() < 3 {
            return None;
        }
        let max_e = (self.bit_len() - 1) as u32;
        for e in (2..=max_e).rev() {
            let (r, exact) = self.integer_nthroot(e);
            if exact {
                return Some((r, e));
            }
        }
        None
    }

    /// Binary GCD for `BigUint`.
    pub fn gcd(&self, other: &Self) -> Self {
        if self.is_zero() {
            return other.clone();
        }
        if other.is_zero() {
            return self.clone();
        }
        let mut a = self.clone();
        let mut b = other.clone();
        let az = a.trailing_zeros();
        let bz = b.trailing_zeros();
        let shift = az.min(bz);
        a.shr_assign(az);
        b.shr_assign(bz);
        loop {
            match a.cmp(&b) {
                Ordering::Equal => return a.shl(shift),
                Ordering::Greater => {
                    a = a.sub(&b);
                    let tz = a.trailing_zeros();
                    a.shr_assign(tz);
                }
                Ordering::Less => {
                    b = b.sub(&a);
                    let tz = b.trailing_zeros();
                    b.shr_assign(tz);
                }
            }
        }
    }

    /// Least common multiple for `BigUint`.
    pub fn lcm(&self, other: &Self) -> Self {
        if self.is_zero() || other.is_zero() {
            return Self::zero();
        }
        let g = self.gcd(other);
        let (q, _) = self.div_rem(&g);
        q.mul(other)
    }

    /// Extended GCD modular inverse: returns `Ok(inv)` with `self * inv == 1 (mod m)`,
    /// or `Err(g)` where `g = gcd(self, m) > 1` (useful in ECM!).
    pub fn mod_inv_or_factor(&self, m: &Self) -> Result<Self, Self> {
        if m.is_zero() {
            return Err(m.clone());
        }
        if m.is_one() {
            return Ok(Self::zero());
        }
        if self.is_zero() {
            return Err(m.clone());
        }
        let mut r0 = m.clone();
        let mut r1 = self.rem(m);
        let mut t0_neg = false;
        let mut t0_mag = Self::zero();
        let mut t1_neg = false;
        let mut t1_mag = Self::one();

        while !r1.is_zero() {
            let (q, r2) = r0.div_rem(&r1);
            let qt1 = q.mul(&t1_mag);
            let (t2_neg, t2_mag) = if t0_neg != t1_neg {
                (t0_neg, t0_mag.add(&qt1))
            } else if t0_mag >= qt1 {
                (t0_neg, t0_mag.sub(&qt1))
            } else {
                (!t1_neg, qt1.sub(&t0_mag))
            };
            r0 = r1;
            r1 = r2;
            t0_neg = t1_neg;
            t0_mag = t1_mag;
            t1_neg = t2_neg;
            t1_mag = t2_mag;
        }

        if !r0.is_one() {
            return Err(r0);
        }
        let t_mod = t0_mag.rem(m);
        if t0_neg && !t_mod.is_zero() {
            Ok(m.sub(&t_mod))
        } else {
            Ok(t_mod)
        }
    }

    /// Modular inverse `self^(-1) mod m`.
    pub fn mod_inv(&self, m: &Self) -> Result<Self, NTheoryError> {
        if m.is_zero() {
            return Err(NTheoryError::InvalidArgument("modulus must be positive"));
        }
        self.mod_inv_or_factor(m)
            .map_err(|_| NTheoryError::NotCoprime)
    }

    /// Modular exponentiation `base^exp mod m`.
    pub fn pow_mod(base: &Self, exp: &Self, m: &Self) -> Self {
        assert!(!m.is_zero(), "modulus must be positive");
        if m.is_one() {
            return Self::zero();
        }
        if !m.is_even() {
            let ctx = BigMont::new(m.clone());
            let bm = ctx.to_mont(&base.rem(m));
            return ctx.from_mont(&ctx.pow_mont(&bm, exp));
        }
        let mut res = Self::one();
        let mut b = base.rem(m);
        for i in 0..exp.bit_len() {
            if exp.bit(i) {
                res = res.mul(&b).rem(m);
            }
            b = b.mul(&b).rem(m);
        }
        res
    }
}

impl From<u64> for BigUint {
    fn from(v: u64) -> Self {
        Self::from_u64(v)
    }
}

impl From<u128> for BigUint {
    fn from(v: u128) -> Self {
        Self::from_u128(v)
    }
}

impl FromStr for BigUint {
    type Err = NTheoryError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::from_str_radix10(s).ok_or(NTheoryError::InvalidArgument("invalid decimal BigUint"))
    }
}

impl Ord for BigUint {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.limbs.len().cmp(&other.limbs.len()) {
            Ordering::Equal => {
                for i in (0..self.limbs.len()).rev() {
                    match self.limbs[i].cmp(&other.limbs[i]) {
                        Ordering::Equal => continue,
                        ord => return ord,
                    }
                }
                Ordering::Equal
            }
            ord => ord,
        }
    }
}

impl PartialOrd for BigUint {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Display for BigUint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_zero() {
            return write!(f, "0");
        }
        let mut cur = self.clone();
        let mut chunks = Vec::new();
        const BASE: u64 = 1_000_000_000_000_000_000; // 10^18
        while !cur.is_zero() {
            let (q, r) = cur.div_rem_u64(BASE);
            chunks.push(r);
            cur = q;
        }
        let top = chunks.pop().unwrap();
        write!(f, "{}", top)?;
        for &c in chunks.iter().rev() {
            write!(f, "{:018}", c)?;
        }
        Ok(())
    }
}

impl fmt::Debug for BigUint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

/// Multi-limb CIOS Montgomery arithmetic context for odd `BigUint` moduli.
#[derive(Clone)]
pub struct BigMont {
    pub n: BigUint,
    pub k: usize,
    pub n_inv_neg: u64,
    pub r1: Vec<u64>,
    pub r2: Vec<u64>,
}

impl BigMont {
    pub fn new(n: BigUint) -> Self {
        assert!(
            !n.is_zero() && !n.is_even(),
            "BigMont modulus must be odd and positive"
        );
        let k = n.limbs.len();
        let n_inv_neg = 0u64.wrapping_sub(inv_mod_2_64(n.limbs[0]));
        let r1_big = BigUint::one().shl(64 * k).rem(&n);
        let r2_big = r1_big.mul(&r1_big).rem(&n);
        let mut r1 = vec![0u64; k];
        let mut r2 = vec![0u64; k];
        r1[..r1_big.limbs.len()].copy_from_slice(&r1_big.limbs);
        r2[..r2_big.limbs.len()].copy_from_slice(&r2_big.limbs);
        Self {
            n,
            k,
            n_inv_neg,
            r1,
            r2,
        }
    }

    #[inline]
    pub fn to_mont_limbs(&self, a: &BigUint) -> Vec<u64> {
        let mut al = vec![0u64; self.k];
        let am = if a >= &self.n {
            a.rem(&self.n)
        } else {
            a.clone()
        };
        al[..am.limbs.len()].copy_from_slice(&am.limbs);
        self.mul_limbs(&al, &self.r2)
    }

    #[inline]
    pub fn to_mont_u64(&self, v: u64) -> Vec<u64> {
        self.to_mont_limbs(&BigUint::from_u64(v))
    }

    #[inline]
    pub fn to_mont(&self, a: &BigUint) -> BigUint {
        BigUint::from_limbs(self.to_mont_limbs(a))
    }

    #[inline]
    pub fn from_mont_limbs(&self, a: &[u64]) -> BigUint {
        let mut one = vec![0u64; self.k];
        one[0] = 1;
        BigUint::from_limbs(self.mul_limbs(a, &one))
    }

    #[inline]
    pub fn from_mont(&self, a: &BigUint) -> BigUint {
        let mut al = vec![0u64; self.k];
        al[..a.limbs.len()].copy_from_slice(&a.limbs);
        self.from_mont_limbs(&al)
    }

    /// CIOS Montgomery multiplication: `a * b * R^(-1) mod n`.
    pub fn mul_limbs(&self, a: &[u64], b: &[u64]) -> Vec<u64> {
        let k = self.k;
        let nl = &self.n.limbs;
        let mut t = vec![0u64; k + 2];
        for &ai_u64 in a.iter().take(k) {
            let ai = ai_u64 as u128;
            let mut c = 0u128;
            for j in 0..k {
                let s = (t[j] as u128) + ai * (b[j] as u128) + c;
                t[j] = s as u64;
                c = s >> 64;
            }
            let s = (t[k] as u128) + c;
            t[k] = s as u64;
            t[k + 1] = (s >> 64) as u64;

            let m = t[0].wrapping_mul(self.n_inv_neg) as u128;
            let s0 = (t[0] as u128) + m * (nl[0] as u128);
            let mut c2 = s0 >> 64;
            for j in 1..k {
                let s = (t[j] as u128) + m * (nl[j] as u128) + c2;
                t[j - 1] = s as u64;
                c2 = s >> 64;
            }
            let s_k = (t[k] as u128) + c2;
            t[k - 1] = s_k as u64;
            t[k] = t[k + 1] + ((s_k >> 64) as u64);
            t[k + 1] = 0;
        }
        let ge = if t[k] != 0 {
            true
        } else {
            let mut g = true;
            for i in (0..k).rev() {
                if t[i] != nl[i] {
                    g = t[i] > nl[i];
                    break;
                }
            }
            g
        };
        if ge {
            let mut borrow = 0i128;
            for i in 0..k {
                let d = (t[i] as i128) - (nl[i] as i128) - borrow;
                if d < 0 {
                    t[i] = (d + (1i128 << 64)) as u64;
                    borrow = 1;
                } else {
                    t[i] = d as u64;
                    borrow = 0;
                }
            }
        }
        t.truncate(k);
        t
    }

    pub fn add_limbs(&self, a: &[u64], b: &[u64]) -> Vec<u64> {
        let k = self.k;
        let nl = &self.n.limbs;
        let mut out = vec![0u64; k];
        let mut carry = 0u128;
        for i in 0..k {
            let s = (a[i] as u128) + (b[i] as u128) + carry;
            out[i] = s as u64;
            carry = s >> 64;
        }
        let ge = if carry != 0 {
            true
        } else {
            let mut g = true;
            for i in (0..k).rev() {
                if out[i] != nl[i] {
                    g = out[i] > nl[i];
                    break;
                }
            }
            g
        };
        if ge {
            let mut borrow = 0i128;
            for i in 0..k {
                let d = (out[i] as i128) - (nl[i] as i128) - borrow;
                if d < 0 {
                    out[i] = (d + (1i128 << 64)) as u64;
                    borrow = 1;
                } else {
                    out[i] = d as u64;
                    borrow = 0;
                }
            }
        }
        out
    }

    pub fn sub_limbs(&self, a: &[u64], b: &[u64]) -> Vec<u64> {
        let k = self.k;
        let nl = &self.n.limbs;
        let mut out = vec![0u64; k];
        let mut borrow = 0i128;
        for i in 0..k {
            let d = (a[i] as i128) - (b[i] as i128) - borrow;
            if d < 0 {
                out[i] = (d + (1i128 << 64)) as u64;
                borrow = 1;
            } else {
                out[i] = d as u64;
                borrow = 0;
            }
        }
        if borrow != 0 {
            let mut carry = 0u128;
            for i in 0..k {
                let s = (out[i] as u128) + (nl[i] as u128) + carry;
                out[i] = s as u64;
                carry = s >> 64;
            }
        }
        out
    }

    pub fn pow_mont_limbs(&self, base: &[u64], exp: &BigUint) -> Vec<u64> {
        let mut res = self.r1.clone();
        let bits = exp.bit_len();
        if bits == 0 {
            return res;
        }
        for i in (0..bits).rev() {
            res = self.mul_limbs(&res, &res);
            if exp.bit(i) {
                res = self.mul_limbs(&res, base);
            }
        }
        res
    }

    pub fn pow_mont(&self, base: &BigUint, exp: &BigUint) -> BigUint {
        let mut bl = vec![0u64; self.k];
        bl[..base.limbs.len()].copy_from_slice(&base.limbs);
        BigUint::from_limbs(self.pow_mont_limbs(&bl, exp))
    }

    pub fn pow_mont_u64(&self, base: &[u64], mut exp: u64) -> Vec<u64> {
        let mut res = self.r1.clone();
        let mut b = base.to_vec();
        while exp > 0 {
            if exp & 1 != 0 {
                res = self.mul_limbs(&res, &b);
            }
            exp >>= 1;
            if exp > 0 {
                b = self.mul_limbs(&b, &b);
            }
        }
        res
    }
}

/// Jacobi symbol `(a / n)` for signed `i64` `a` and odd positive `BigUint` `n`.
pub fn jacobi_i64_big(a: i64, n: &BigUint) -> i8 {
    debug_assert!(!n.is_zero() && !n.is_even());
    if n.is_one() {
        return 1;
    }
    let mut neg = false;
    let ua: u64 = if a < 0 {
        if (n.limbs[0] & 3) == 3 {
            neg = !neg;
        }
        a.unsigned_abs()
    } else {
        a as u64
    };
    if ua == 0 {
        return 0;
    }
    let j = jacobi_big(&BigUint::from_u64(ua), n);
    if j == 0 {
        0
    } else if neg {
        -j
    } else {
        j
    }
}

/// Binary Jacobi symbol `(a / n)` for `BigUint` `a` and odd positive `BigUint` `n`.
pub fn jacobi_big(a: &BigUint, n: &BigUint) -> i8 {
    debug_assert!(!n.is_zero() && !n.is_even());
    if n.is_one() {
        return 1;
    }
    let mut x = a.rem(n);
    let mut y = n.clone();
    let mut neg = false;
    while !x.is_zero() {
        let tz = x.trailing_zeros();
        if tz & 1 == 1 {
            let m8 = y.limbs[0] & 7;
            if m8 == 3 || m8 == 5 {
                neg = !neg;
            }
        }
        x.shr_assign(tz);
        if (x.limbs[0] & 3) == 3 && (y.limbs[0] & 3) == 3 {
            neg = !neg;
        }
        let next = y.rem(&x);
        y = x;
        x = next;
    }
    if !y.is_one() {
        return 0;
    }
    if neg {
        -1
    } else {
        1
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_biguint_ops_and_roots() {
        let a = BigUint::pow10(40);
        let b = BigUint::pow10(19).add(&BigUint::from_u64(42));
        let (q, r) = a.div_rem(&b);
        assert_eq!(q.mul(&b).add(&r), a);

        let p3 = BigUint::from_str("1234567890123456789").unwrap().pow(3);
        assert_eq!(p3.perfect_power().unwrap().1, 3);
        assert!(p3.integer_nthroot(3).1);
    }
}
