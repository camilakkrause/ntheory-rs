//! Quadratic & n-th power residues, Legendre, Jacobi, and Kronecker symbols.

use crate::arith::{gcd, mul_mod, pow_mod};
use crate::bigint::{jacobi_big, jacobi_i64_big, BigUint};
use crate::error::NTheoryError;
use crate::factor::factorint;
use crate::primality::is_prime;

/// Binary Jacobi symbol `(a / n)` for `u64` `a` and odd positive `n`.
pub fn jacobi_u64(a: u64, mut n: u64) -> i8 {
    debug_assert!(n > 0 && n & 1 == 1);
    if n == 1 {
        return 1;
    }
    let mut x = a % n;
    let mut neg = false;
    while x != 0 {
        let tz = x.trailing_zeros();
        if tz & 1 == 1 {
            let m8 = n & 7;
            if m8 == 3 || m8 == 5 {
                neg = !neg;
            }
        }
        x >>= tz;
        if (x & 3) == 3 && (n & 3) == 3 {
            neg = !neg;
        }
        let tmp = n % x;
        n = x;
        x = tmp;
    }
    if n != 1 {
        0
    } else if neg {
        -1
    } else {
        1
    }
}

/// Jacobi symbol `(a / n)` for signed `a` and odd positive `n`.
pub fn jacobi_symbol(a: i64, n: u64) -> Result<i8, NTheoryError> {
    if n == 0 || n & 1 == 0 {
        return Err(NTheoryError::InvalidArgument(
            "Jacobi modulus n must be odd and positive",
        ));
    }
    if n == 1 {
        return Ok(1);
    }
    let a_u64 = if n <= i64::MAX as u64 {
        a.rem_euclid(n as i64) as u64
    } else if a >= 0 {
        (a as u64) % n
    } else {
        let rem = a.unsigned_abs() % n;
        if rem == 0 {
            0
        } else {
            n - rem
        }
    };
    Ok(jacobi_u64(a_u64, n))
}

/// Legendre symbol `(a / p)` for odd prime `p`.
pub fn legendre_symbol(a: i64, p: u64) -> Result<i8, NTheoryError> {
    if !is_prime(p) {
        return Err(NTheoryError::NotPrime);
    }
    if p == 2 {
        return Err(NTheoryError::InvalidArgument(
            "Legendre symbol requires an odd prime",
        ));
    }
    jacobi_symbol(a, p)
}

/// Kronecker symbol `(a / n)` defined for ALL integers `(a, n) in Z x Z`.
pub fn kronecker_symbol(a: i64, n: i64) -> i8 {
    if n == 0 {
        return if a == 1 || a == -1 { 1 } else { 0 };
    }
    if n == 1 {
        return 1;
    }
    let mut neg = false;
    let mut un: u64 = if n < 0 {
        if a < 0 {
            neg = !neg;
        }
        n.unsigned_abs()
    } else {
        n as u64
    };

    let tz = un.trailing_zeros();
    if tz > 0 {
        if a & 1 == 0 {
            return 0;
        }
        if tz & 1 == 1 {
            let m8 = a.rem_euclid(8);
            if m8 == 3 || m8 == 5 {
                neg = !neg;
            }
        }
        un >>= tz;
    }
    if un == 1 {
        return if neg { -1 } else { 1 };
    }
    let a_mod = if a >= 0 {
        (a as u64) % un
    } else {
        let r = a.unsigned_abs() % un;
        if r == 0 {
            0
        } else {
            un - r
        }
    };
    let j = jacobi_u64(a_mod, un);
    if j == 0 {
        0
    } else if neg {
        -j
    } else {
        j
    }
}

/// Returns `true` iff `x^2 == a (mod n)` has at least one solution (`n >= 1`).
pub fn is_quad_residue(a: u64, n: u64) -> bool {
    if n == 0 {
        return false;
    }
    if n == 1 || a % n == 0 {
        return true;
    }
    let fac = factorint(n);
    for (p, e) in fac {
        let pe = p.pow(e);
        let mut ap = a % pe;
        if ap == 0 {
            continue;
        }
        let mut v = 0u32;
        while ap % p == 0 {
            ap /= p;
            v += 1;
        }
        if v & 1 == 1 {
            return false;
        }
        let rem_e = e - v;
        if p == 2 {
            if rem_e == 2 && ap % 4 != 1 {
                return false;
            }
            if rem_e >= 3 && ap % 8 != 1 {
                return false;
            }
        } else if jacobi_u64(ap % p, p) != 1 {
            return false;
        }
    }
    true
}

/// Return all quadratic residues modulo `n` in ascending order (`0..n`).
pub fn quadratic_residues(n: u64) -> Vec<u64> {
    if n == 0 {
        return Vec::new();
    }
    let mut seen = vec![false; n as usize];
    for x in 0..=n / 2 {
        let sq = mul_mod(x, x, n);
        seen[sq as usize] = true;
    }
    (0..n).filter(|&i| seen[i as usize]).collect()
}

/// Euler's criterion: returns `true` iff `x^r == a (mod p)` has a solution for prime `p`.
pub fn is_nthpow_residue(a: u64, r: u64, p: u64) -> Result<bool, NTheoryError> {
    if !is_prime(p) {
        return Err(NTheoryError::NotPrime);
    }
    let am = a % p;
    if r == 0 {
        return Ok(am == 1);
    }
    if am == 0 || p == 2 {
        return Ok(true);
    }
    let g = gcd(r, p - 1);
    Ok(pow_mod(am, (p - 1) / g, p) == 1)
}

/// Jacobi symbol `(a / n)` for `i64` `a` and odd positive `BigUint` `n`.
pub fn jacobi_symbol_big(a: i64, n: &BigUint) -> Result<i8, NTheoryError> {
    if n.is_zero() || n.is_even() {
        return Err(NTheoryError::InvalidArgument(
            "Jacobi modulus n must be odd and positive",
        ));
    }
    Ok(jacobi_i64_big(a, n))
}

/// Jacobi symbol `(a / n)` for `BigUint` `a` and odd positive `BigUint` `n`.
pub fn jacobi_symbol_big_uint(a: &BigUint, n: &BigUint) -> Result<i8, NTheoryError> {
    if n.is_zero() || n.is_even() {
        return Err(NTheoryError::InvalidArgument(
            "Jacobi modulus n must be odd and positive",
        ));
    }
    Ok(jacobi_big(a, n))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_symbols_and_residues() {
        assert_eq!(legendre_symbol(2, 7), Ok(1));
        assert_eq!(legendre_symbol(3, 7), Ok(-1));
        assert_eq!(legendre_symbol(7, 7), Ok(0));
        assert_eq!(
            legendre_symbol(1, 2),
            Err(NTheoryError::InvalidArgument(
                "Legendre symbol requires an odd prime"
            ))
        );
        assert_eq!(legendre_symbol(1, 9), Err(NTheoryError::NotPrime));

        assert_eq!(kronecker_symbol(-1, -1), -1);
        assert_eq!(kronecker_symbol(5, 0), 0);
        assert_eq!(kronecker_symbol(-1, 0), 1);
        assert_eq!(kronecker_symbol(3, 2), -1);
        assert_eq!(kronecker_symbol(7, 2), 1);

        assert_eq!(quadratic_residues(12), vec![0, 1, 4, 9]);
        assert!(is_quad_residue(4, 12));
        assert!(!is_quad_residue(7, 12));
        assert_eq!(is_nthpow_residue(2, 3, 7), Ok(false));
        assert_eq!(is_nthpow_residue(6, 3, 7), Ok(true));
    }
}
