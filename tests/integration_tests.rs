//! Exhaustive brute-force verification and large-scale integration tests for `ntheory-rs`.

use std::str::FromStr;

use ntheory_rs::big::{
    crt_big, cyclotomic_eval, factorint_big, is_prime_big, n_order_big, BigUint,
};
use ntheory_rs::u128_ops::{
    crt_u128, discrete_log_u128, factorint_u128, is_prime_u128, n_order_u128,
};
use ntheory_rs::{
    binomial_mod, continued_fraction, convergents, discrete_log, divisor_count, divisor_sigma,
    divisors, factorint, gcd, is_nthpow_residue, is_primitive_root, is_quad_residue, jacobi_symbol,
    kronecker_symbol, legendre_symbol, mertens, mobius, n_order, nth_prime, nthroot_mod_all,
    pow_mod, prime_pi, prime_range, primitive_root, quadratic_residues, reduced_totient,
    smooth_numbers, sqrt_mod_all, totient,
};

#[test]
fn test_exhaustive_small_moduli_orders_totients_primitive_roots() {
    for n in 1u64..=120 {
        // Brute-force totient & reduced_totient & n_order
        let mut coprimes = Vec::new();
        for a in 1..=n {
            if gcd(a, n) == 1 {
                coprimes.push(a);
            }
        }
        assert_eq!(
            totient(n),
            coprimes.len() as u64,
            "totient mismatch at n={}",
            n
        );

        let mut max_ord = 1u64;
        let mut group_exp = 1u64;
        for &a in &coprimes {
            let mut k = 1u64;
            let mut cur = a % n;
            while cur != 1 % n {
                cur = (cur * (a % n)) % n;
                k += 1;
            }
            assert_eq!(n_order(a, n), Ok(k), "n_order({}, {}) mismatch", a, n);
            max_ord = max_ord.max(k);
            group_exp = ntheory_rs::lcm(group_exp, k);
        }
        assert_eq!(max_ord, group_exp, "max order mismatch at n={}", n);
        assert_eq!(
            reduced_totient(n),
            group_exp,
            "reduced_totient mismatch at n={}",
            n
        );

        // Primitive root check
        let phi = coprimes.len() as u64;
        let pr = primitive_root(n);
        if n == 1 {
            assert_eq!(pr, None);
        } else if let Some(g) = pr {
            assert!(is_primitive_root(g, n));
            assert_eq!(n_order(g, n), Ok(phi));
            // Verify g is the smallest primitive root
            for x in 1..g {
                assert!(!is_primitive_root(x, n));
            }
        } else {
            for &a in &coprimes {
                assert!(!is_primitive_root(a, n));
            }
        }
    }
}

#[test]
fn test_exhaustive_sqrt_mod_and_quad_residues() {
    for n in 1u64..=120 {
        let mut brute: Vec<Vec<u64>> = vec![Vec::new(); n as usize];
        for x in 0..n {
            brute[((x * x) % n) as usize].push(x);
        }
        let expected_qrs: Vec<u64> = (0..n).filter(|&a| !brute[a as usize].is_empty()).collect();
        assert_eq!(
            quadratic_residues(n),
            expected_qrs,
            "quadratic_residues({})",
            n
        );

        for (a_idx, roots) in brute.iter().enumerate() {
            let a = a_idx as u64;
            assert_eq!(
                is_quad_residue(a, n),
                !roots.is_empty(),
                "is_quad_residue({}, {})",
                a,
                n
            );
            assert_eq!(
                sqrt_mod_all(a, n),
                Ok(roots.clone()),
                "sqrt_mod_all({}, {})",
                a,
                n
            );
        }
    }
}

#[test]
fn test_exhaustive_discrete_log_and_nthroot() {
    for n in 2u64..=55 {
        for base in 0..n {
            let mut first_pow: Vec<Option<u64>> = vec![None; n as usize];
            let mut cur = 1 % n;
            for x in 0..=n {
                if first_pow[cur as usize].is_none() {
                    first_pow[cur as usize] = Some(x);
                }
                cur = (cur * base) % n;
            }
            for (target_idx, &expected) in first_pow.iter().enumerate() {
                let target = target_idx as u64;
                assert_eq!(
                    discrete_log(base, target, n),
                    Ok(expected),
                    "discrete_log({}, {}, {})",
                    base,
                    target,
                    n
                );
            }
        }
    }

    for p in [2u64, 3, 5, 7, 11, 13, 17, 29, 31] {
        for r in 1u64..=8 {
            for a in 0..p {
                let brute: Vec<u64> = (0..p).filter(|&x| pow_mod(x, r, p) == a).collect();
                assert_eq!(nthroot_mod_all(a, r, p), Ok(brute.clone()));
                assert_eq!(is_nthpow_residue(a, r, p), Ok(!brute.is_empty()));
            }
        }
    }
}

#[test]
fn test_prime_pi_and_nth_prime_powers_of_10() {
    let expected = [
        (10u64, 4u64),
        (100, 25),
        (1_000, 168),
        (10_000, 1_229),
        (100_000, 9_592),
        (100_001, 9_592),
        (1_000_000, 78_498),
        (10_000_000, 664_579),
        (100_000_000, 5_761_455),
        (1_000_000_000, 50_847_534),
    ];
    for &(x, pi) in &expected {
        assert_eq!(prime_pi(x), pi, "prime_pi({}) mismatch", x);
    }

    assert_eq!(nth_prime(1), Some(2));
    assert_eq!(nth_prime(100), Some(541));
    assert_eq!(nth_prime(10_000), Some(104_729));
    assert_eq!(nth_prime(100_000), Some(1_299_709));
    assert_eq!(nth_prime(1_000_000), Some(15_485_863));

    // Check prime_range around 10^9
    let r = prime_range(1_000_000_000, 1_000_000_100);
    assert_eq!(
        r,
        vec![
            1_000_000_007,
            1_000_000_009,
            1_000_000_021,
            1_000_000_033,
            1_000_000_087,
            1_000_000_093,
            1_000_000_097
        ]
    );
}

#[test]
fn test_symbols_crt_functions_and_big() {
    // Symbols
    assert_eq!(legendre_symbol(5, 11), Ok(1));
    assert_eq!(jacobi_symbol(1001, 9907), Ok(-1));
    for n in -20i64..=20 {
        for a in -20i64..=20 {
            let k = kronecker_symbol(a, n);
            assert!(matches!(k, -1..=1));
            if n > 0 && n % 2 == 1 {
                assert_eq!(k, jacobi_symbol(a, n as u64).unwrap());
            }
        }
    }

    // Mertens & Mobius consistency
    let mut m_acc = 0i64;
    for k in 1..=300 {
        m_acc += mobius(k) as i64;
    }
    assert_eq!(mertens(300), m_acc);
    assert_eq!(divisors(72).len() as u64, divisor_count(72));
    assert_eq!(divisor_sigma(12, 2), 1 + 4 + 9 + 16 + 36 + 144);
    assert_eq!(binomial_mod(1000, 300, 997), Ok(0));
    assert_eq!(binomial_mod(1000, 3, 997), Ok(1));

    // Continued fraction reconstruction
    for den in 1..=25 {
        for num in -30..=30 {
            let cf = continued_fraction(num, den).unwrap();
            let g = gcd(num.unsigned_abs(), den as u64) as i128;
            let last = *convergents(&cf).last().unwrap();
            assert_eq!(last, ((num as i128) / g, (den as i128) / g));
        }
    }
    assert_eq!(smooth_numbers(3, 20), vec![1, 2, 3, 4, 6, 8, 9, 12, 16, 18]);

    // 128-bit & BigUint checks
    let m127 = (1u128 << 127) - 1;
    assert!(is_prime_u128(m127));
    assert_eq!(factorint_u128(m127).get(&m127), Some(&1));
    assert_eq!(
        crt_u128(&[1, 2], &[1_000_000_007, 1_000_000_009])
            .unwrap()
            .unwrap()
            .1,
        1_000_000_007 * 1_000_000_009
    );
    assert_eq!(n_order_u128(2, m127), Ok(127));
    assert_eq!(
        discrete_log_u128(
            3,
            pow_mod_u128_helper(3, 1234567, 1u128 << 100),
            1u128 << 100
        ),
        Ok(Some(1234567))
    );

    // BigUint Phi_43(10) complete factorization & order verification
    let phi43 = cyclotomic_eval(43, 10);
    let f43 = factorint_big(&phi43);
    let mut prod = BigUint::one();
    for (p, &e) in &f43 {
        assert!(is_prime_big(p));
        assert_eq!(
            n_order_big(&BigUint::from_u64(10), p),
            Ok(BigUint::from_u64(43))
        );
        prod = prod.mul(&p.pow(e));
    }
    assert_eq!(prod, phi43);
    assert!(factorint(0).is_empty());
    assert_eq!(
        BigUint::from_str("123_456").unwrap(),
        BigUint::from_u64(123_456)
    );

    // Regression tests: largest 128-bit prime (>= 2^127, exercises add_mod_u128/sub_mod_u128 in strong Lucas)
    assert!(is_prime_u128(u128::MAX - 158)); // 2^128 - 159 is prime
    assert!(!is_prime_u128(u128::MAX));
    assert!(!is_prime_u128(u128::MAX - 156));
    assert!(!is_prime_u128((1u128 << 127) + 1));
    let sq_big = ((1u128 << 63) + 123).pow(2);
    assert!(!is_prime_u128(sq_big));

    // Regression tests: crt_big when one modulus divides another (mi_g == 1, m_g % mi_g == 0)
    assert_eq!(
        crt_big(
            &[BigUint::from_u64(1), BigUint::from_u64(1)],
            &[BigUint::from_u64(6), BigUint::from_u64(3)]
        ),
        Ok(Some((BigUint::from_u64(1), BigUint::from_u64(6))))
    );
    assert_eq!(
        crt_big(
            &[BigUint::from_u64(1), BigUint::from_u64(2)],
            &[BigUint::from_u64(6), BigUint::from_u64(3)]
        ),
        Ok(None)
    );
}

fn pow_mod_u128_helper(a: u128, e: u128, m: u128) -> u128 {
    ntheory_rs::u128_ops::pow_mod_u128(a, e, m)
}
