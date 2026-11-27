//! Self-Initializing Quadratic Sieve (SIQS) with Single Large Prime (SLP) variation.
//!
//! Optimized for odd composites of 25–62 decimal digits (~85–205 bits).

use std::collections::HashMap;

use crate::arith::{mod_inv, mul_mod, pow_mod};
use crate::bigint::BigUint;
use crate::primality::{is_prime, sieve_primes};

/// Tonelli-Shanks: find `r` with `r^2 == a (mod p)` for odd prime `p` (assuming Legendre(a, p) == 1).
fn sqrt_mod_p_internal(a_in: u64, p: u64) -> u64 {
    let a = a_in % p;
    if a == 0 {
        return 0;
    }
    if p == 2 {
        return a;
    }
    if p % 4 == 3 {
        return pow_mod(a, (p + 1) / 4, p);
    }
    let mut q = p - 1;
    let mut s = 0u32;
    while q & 1 == 0 {
        q >>= 1;
        s += 1;
    }
    let mut z = 2u64;
    while pow_mod(z, (p - 1) / 2, p) != p - 1 {
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
    r
}

/// Choose Knuth-Schroeppel multiplier `k` for `n` to maximize small-prime density in factor base.
fn choose_multiplier(n: &BigUint, small_primes: &[u64]) -> u64 {
    const CANDIDATES: [u64; 18] = [
        1, 2, 3, 5, 6, 7, 10, 11, 13, 14, 15, 17, 19, 21, 23, 29, 31, 37,
    ];
    let mut best_k = 1u64;
    let mut best_score = f64::NEG_INFINITY;
    let check_primes = &small_primes[1..small_primes.len().min(60)];

    for &k in &CANDIDATES {
        let kn = n.mul_u64(k);
        let mut score = -0.5 * (k as f64).ln();
        let m8 = kn.limbs[0] & 7;
        if m8 == 1 {
            score += 2.0 * 2.0f64.ln();
        } else if m8 == 5 {
            score += 1.0 * 2.0f64.ln();
        } else if m8 == 3 || m8 == 7 {
            score += 0.5 * 2.0f64.ln();
        }
        for &p in check_primes {
            let r = kn.rem_u64(p);
            if r == 0 {
                score += (p as f64).ln() / (p as f64);
            } else if pow_mod(r, (p - 1) / 2, p) == 1 {
                score += 2.0 * (p as f64).ln() / ((p - 1) as f64);
            }
        }
        if score > best_score {
            best_score = score;
            best_k = k;
        }
    }
    best_k
}

struct FbPrime {
    p: u64,
    sqrt_n: u64,
    log_p: u16,
}

#[derive(Clone)]
struct FullRelation {
    x_mod_n: BigUint,
    extra_y: BigUint,
    exps: Vec<(usize, u32)>,
}

#[derive(Clone)]
struct PartialRelation {
    x_mod_n: BigUint,
    exps: Vec<(usize, u32)>,
}

#[derive(Clone)]
struct SBig {
    neg: bool,
    mag: BigUint,
}

impl SBig {
    fn from_big(mag: BigUint, neg: bool) -> Self {
        if mag.is_zero() {
            Self { neg: false, mag }
        } else {
            Self { neg, mag }
        }
    }

    fn from_i64(v: i64) -> Self {
        if v < 0 {
            Self {
                neg: true,
                mag: BigUint::from_u64(v.unsigned_abs()),
            }
        } else {
            Self {
                neg: false,
                mag: BigUint::from_u64(v as u64),
            }
        }
    }

    fn add(&self, other: &Self) -> Self {
        if self.neg == other.neg {
            Self::from_big(self.mag.add(&other.mag), self.neg)
        } else if self.mag >= other.mag {
            Self::from_big(self.mag.sub(&other.mag), self.neg)
        } else {
            Self::from_big(other.mag.sub(&self.mag), other.neg)
        }
    }

    fn mul(&self, other: &Self) -> Self {
        Self::from_big(self.mag.mul(&other.mag), self.neg ^ other.neg)
    }

    fn rem_mod_big(&self, n: &BigUint) -> BigUint {
        let r = self.mag.rem(n);
        if r.is_zero() || !self.neg {
            r
        } else {
            n.sub(&r)
        }
    }
}

/// Attempt to find a non-trivial factor of odd composite `n` using the Self-Initializing Quadratic Sieve (SIQS).
pub fn siqs_factor(n: &BigUint) -> Option<BigUint> {
    if n.is_zero() || n.is_one() || n.is_even() {
        return None;
    }
    let sq = n.isqrt();
    if &sq.mul(&sq) == n {
        return Some(sq);
    }
    let digits = n.decimal_digits();

    let (fb_bound, sieve_m, min_sieve_prime, lp_mult, target_extra): (
        usize,
        usize,
        u64,
        u64,
        usize,
    ) = if digits <= 26 {
        (1_500, 16_384, 11, 50, 20)
    } else if digits <= 32 {
        (3_500, 32_768, 13, 60, 24)
    } else if digits <= 38 {
        (7_500, 49_152, 17, 80, 28)
    } else if digits <= 44 {
        (15_000, 65_536, 19, 100, 32)
    } else if digits <= 50 {
        (28_000, 98_304, 23, 100, 36)
    } else if digits <= 56 {
        (55_000, 131_072, 29, 100, 40)
    } else {
        (95_000, 196_608, 31, 100, 48)
    };

    let all_primes = sieve_primes(fb_bound);
    let mult = choose_multiplier(n, &all_primes);
    let kn = n.mul_u64(mult);

    let mut fb: Vec<FbPrime> = Vec::new();
    fb.push(FbPrime {
        p: 2,
        sqrt_n: kn.limbs[0] & 1,
        log_p: 16,
    });
    for &p in &all_primes[1..] {
        let r = kn.rem_u64(p);
        if r == 0 {
            if n.rem_u64(p) == 0 && n != &BigUint::from_u64(p) {
                return Some(BigUint::from_u64(p));
            }
            fb.push(FbPrime {
                p,
                sqrt_n: 0,
                log_p: ((p as f64).log2() * 16.0).round() as u16,
            });
            continue;
        }
        if pow_mod(r, (p - 1) / 2, p) == 1 {
            let t = sqrt_mod_p_internal(r, p);
            fb.push(FbPrime {
                p,
                sqrt_n: t,
                log_p: ((p as f64).log2() * 16.0).round() as u16,
            });
        }
    }

    let fb_len = fb.len();
    let max_fb_p = fb.last()?.p;
    let lp_bound = max_fb_p.saturating_mul(lp_mult).min(1u64 << 34);
    let lp_log_u16 = ((lp_bound as f64).log2() * 16.0).round() as u16;
    let need_rels = fb_len + 1 + target_extra;

    let two_kn_sqrt = kn.mul_u64(2).isqrt();
    let (target_a_big, _) = two_kn_sqrt.div_rem_u64(sieve_m as u64);
    let target_a_f64 = (target_a_big.bit_len() as f64) * std::f64::consts::LN_2;

    let mut s = ((target_a_f64 / 7.2).round() as usize).clamp(3, 12);
    let ideal_q = (target_a_f64 / (s as f64))
        .exp()
        .clamp(150.0, (max_fb_p as f64) * 0.5);
    while s > 3 && ideal_q < 120.0 {
        s -= 1;
    }

    let ideal_q = (target_a_f64 / (s as f64))
        .exp()
        .clamp(100.0, (max_fb_p as f64) * 0.6);
    let q_lo_p = (ideal_q * 0.35).max(53.0) as u64;
    let q_hi_p = (ideal_q * 2.8).min(max_fb_p as f64) as u64;
    let q_pool: Vec<usize> = (1..fb_len)
        .filter(|&idx| fb[idx].sqrt_n != 0 && fb[idx].p >= q_lo_p && fb[idx].p <= q_hi_p)
        .collect();
    if q_pool.len() < s + 2 {
        return None;
    }

    let mut skip_idx = 0usize;
    let mut small_slack_f64 = 0.0f64;
    while skip_idx < fb_len && fb[skip_idx].p < min_sieve_prime {
        let p = fb[skip_idx].p as f64;
        small_slack_f64 += 2.0 * p.log2() / (p - 1.0);
        skip_idx += 1;
    }
    let small_slack = (small_slack_f64 * 16.0).round() as u16 + 40;

    let q_bits_scaled =
        (((sieve_m as f64).log2() + 0.5 * (kn.bit_len() as f64) - 0.5) * 16.0) as i32;
    let threshold = (q_bits_scaled - (lp_log_u16 as i32) - (small_slack as i32)).max(64) as u16;

    let mut full_rels: Vec<FullRelation> = Vec::with_capacity(need_rels + 32);
    let mut partials: HashMap<u64, PartialRelation> = HashMap::new();
    let mut sieve = vec![0u16; 2 * sieve_m];
    let mut rng_state: u64 =
        0x9E37_79B9_7F4A_7C15 ^ (n.limbs[0].wrapping_mul(0xBF58_476D_1CE4_E5B9));

    let next_rand = |st: &mut u64| -> u64 {
        let mut x = *st;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        *st = x;
        x
    };

    let mut poly_groups_tried = 0usize;
    let max_poly_groups = 12_000usize;

    let mut is_in_a = vec![false; fb_len];
    let mut soln1 = vec![0u64; fb_len];
    let mut soln2 = vec![0u64; fb_len];
    let mut bainv2: Vec<Vec<u64>> = vec![vec![0u64; fb_len]; s];

    'outer: while full_rels.len() < need_rels && poly_groups_tried < max_poly_groups {
        poly_groups_tried += 1;

        let mut chosen = Vec::with_capacity(s);
        let mut best_diff = f64::INFINITY;
        let mut best_chosen = Vec::new();
        for _ in 0..8 {
            chosen.clear();
            let mut log_prod = 0.0f64;
            let mut tries = 0;
            while chosen.len() < s - 1 && tries < 64 {
                tries += 1;
                let idx = q_pool[(next_rand(&mut rng_state) as usize) % q_pool.len()];
                if !chosen.contains(&idx) {
                    chosen.push(idx);
                    log_prod += (fb[idx].p as f64).ln();
                }
            }
            if chosen.len() < s - 1 {
                continue;
            }
            let want_p = (target_a_f64 - log_prod).exp();
            let mut last_idx = None;
            let mut last_err = f64::INFINITY;
            for &idx in &q_pool {
                if chosen.contains(&idx) {
                    continue;
                }
                let err = ((fb[idx].p as f64) - want_p).abs();
                if err < last_err {
                    last_err = err;
                    last_idx = Some(idx);
                }
            }
            if let Some(li) = last_idx {
                chosen.push(li);
                let total_log = log_prod + (fb[li].p as f64).ln();
                let diff = (total_log - target_a_f64).abs();
                if diff < best_diff {
                    best_diff = diff;
                    best_chosen = chosen.clone();
                }
            }
        }
        if best_chosen.len() != s {
            continue;
        }
        best_chosen.sort_unstable();

        let mut a_big = BigUint::one();
        for &idx in &best_chosen {
            is_in_a[idx] = true;
            a_big.mul_u64_assign(fb[idx].p);
        }

        let mut b_terms: Vec<BigUint> = Vec::with_capacity(s);
        for &idx in &best_chosen {
            let q = fb[idx].p;
            let (a_div_q, _) = a_big.div_rem_u64(q);
            let a_div_q_mod_q = a_div_q.rem_u64(q);
            let inv = match mod_inv(a_div_q_mod_q, q) {
                Ok(v) => v,
                Err(_) => {
                    for &ci in &best_chosen {
                        is_in_a[ci] = false;
                    }
                    continue 'outer;
                }
            };
            let mut gamma = mul_mod(fb[idx].sqrt_n, inv, q);
            if gamma > q / 2 {
                gamma = q - gamma;
            }
            b_terms.push(a_div_q.mul_u64(gamma));
        }

        let mut b_big = SBig::from_i64(0);
        for bt in &b_terms {
            b_big = b_big.add(&SBig::from_big(bt.clone(), false));
        }

        for idx in 1..fb_len {
            if is_in_a[idx] {
                continue;
            }
            let p = fb[idx].p;
            let a_mod_p = a_big.rem_u64(p);
            if a_mod_p == 0 {
                continue;
            }
            let ai = match mod_inv(a_mod_p, p) {
                Ok(v) => v,
                Err(_) => continue,
            };
            for l in 0..s {
                let b2 = mul_mod(2 % p, b_terms[l].rem_u64(p), p);
                bainv2[l][idx] = mul_mod(b2, ai, p);
            }
            let b_mod_p = if b_big.neg {
                let r = b_big.mag.rem_u64(p);
                if r == 0 {
                    0
                } else {
                    p - r
                }
            } else {
                b_big.mag.rem_u64(p)
            };
            let t = fb[idx].sqrt_n;
            let d1 = if t >= b_mod_p {
                t - b_mod_p
            } else {
                t + p - b_mod_p
            };
            let neg_t = if t == 0 { 0 } else { p - t };
            let d2 = if neg_t >= b_mod_p {
                neg_t - b_mod_p
            } else {
                neg_t + p - b_mod_p
            };
            soln1[idx] = mul_mod(d1, ai, p);
            soln2[idx] = mul_mod(d2, ai, p);
        }

        let num_polys = 1usize << (s - 1);
        let mut signs = vec![1i8; s];

        for poly_i in 1..=num_polys {
            sieve.fill(0);
            let m_u64 = sieve_m as u64;
            let len = 2 * sieve_m;

            for idx in skip_idx..fb_len {
                if is_in_a[idx] {
                    continue;
                }
                let p = fb[idx].p;
                let lp = fb[idx].log_p;
                let p_usize = p as usize;
                let m_mod_p = m_u64 % p;

                let mut pos1 = ((soln1[idx] + m_mod_p) % p) as usize;
                let mut pos2 = ((soln2[idx] + m_mod_p) % p) as usize;
                if pos1 == pos2 {
                    while pos1 < len {
                        sieve[pos1] += lp;
                        pos1 += p_usize;
                    }
                } else {
                    while pos1 < len {
                        sieve[pos1] += lp;
                        pos1 += p_usize;
                    }
                    while pos2 < len {
                        sieve[pos2] += lp;
                        pos2 += p_usize;
                    }
                }
            }

            let b2 = b_big.mag.mul(&b_big.mag);
            let (c_neg, c_mag) = if b2 >= kn {
                let (q, r) = b2.sub(&kn).div_rem(&a_big);
                debug_assert!(r.is_zero());
                (false, q)
            } else {
                let (q, r) = kn.sub(&b2).div_rem(&a_big);
                debug_assert!(r.is_zero());
                (true, q)
            };
            let c_sbig = SBig::from_big(c_mag, c_neg);
            let two_b = SBig::from_big(b_big.mag.mul_u64(2), b_big.neg);
            let a_sbig = SBig::from_big(a_big.clone(), false);

            for (pos, &sval) in sieve.iter().enumerate().take(len) {
                if sval < threshold {
                    continue;
                }
                let x_i64 = (pos as i64) - (sieve_m as i64);
                let x_sbig = SBig::from_i64(x_i64);
                let qx = a_sbig.mul(&x_sbig).add(&two_b).mul(&x_sbig).add(&c_sbig);
                if qx.mag.is_zero() {
                    continue;
                }

                let mut rem = qx.mag;
                let mut exps: Vec<(usize, u32)> = Vec::new();
                if qx.neg {
                    exps.push((0, 1));
                }
                for &a_idx in &best_chosen {
                    exps.push((a_idx + 1, 1));
                }

                let tz = rem.trailing_zeros();
                if tz > 0 {
                    rem.shr_assign(tz);
                    exps.push((1, tz as u32));
                }

                for idx in 1..fb_len {
                    let p = fb[idx].p;
                    let mut hit = is_in_a[idx] || fb[idx].sqrt_n == 0;
                    if !hit {
                        let xm = x_i64.rem_euclid(p as i64) as u64;
                        hit = xm == soln1[idx] || xm == soln2[idx];
                    }
                    if hit {
                        let mut cnt = 0u32;
                        while rem.rem_u64(p) == 0 {
                            let (q_next, _) = rem.div_rem_u64(p);
                            rem = q_next;
                            cnt += 1;
                        }
                        if cnt > 0 {
                            if let Some(entry) = exps.iter_mut().find(|e| e.0 == idx + 1) {
                                entry.1 += cnt;
                            } else {
                                exps.push((idx + 1, cnt));
                            }
                        }
                    }
                }

                if rem.is_one() {
                    let ax_plus_b = a_sbig.mul(&x_sbig).add(&b_big);
                    full_rels.push(FullRelation {
                        x_mod_n: ax_plus_b.rem_mod_big(n),
                        extra_y: BigUint::one(),
                        exps,
                    });
                    if full_rels.len() >= need_rels {
                        break;
                    }
                } else if let Some(lp) = rem.to_u64() {
                    if lp <= lp_bound && is_prime(lp) {
                        if n.rem_u64(lp) == 0 && n != &BigUint::from_u64(lp) {
                            return Some(BigUint::from_u64(lp));
                        }
                        let ax_plus_b = a_sbig.mul(&x_sbig).add(&b_big).rem_mod_big(n);
                        if let Some(prev) = partials.get(&lp) {
                            let x_comb = prev.x_mod_n.mul(&ax_plus_b).rem(n);
                            let mut merged = prev.exps.clone();
                            for (col, e) in exps {
                                if let Some(entry) = merged.iter_mut().find(|x| x.0 == col) {
                                    entry.1 += e;
                                } else {
                                    merged.push((col, e));
                                }
                            }
                            full_rels.push(FullRelation {
                                x_mod_n: x_comb,
                                extra_y: BigUint::from_u64(lp),
                                exps: merged,
                            });
                            if full_rels.len() >= need_rels {
                                break;
                            }
                        } else {
                            partials.insert(
                                lp,
                                PartialRelation {
                                    x_mod_n: ax_plus_b,
                                    exps,
                                },
                            );
                        }
                    }
                }
            }

            if full_rels.len() >= need_rels {
                break;
            }
            if poly_i == num_polys {
                break;
            }

            let v = (2 * poly_i).trailing_zeros() as usize;
            let old_sign = signs[v];
            signs[v] = -old_sign;
            let delta_b = SBig::from_big(b_terms[v].mul_u64(2), old_sign > 0);
            b_big = b_big.add(&delta_b);
            let add_root = old_sign > 0;
            for idx in 1..fb_len {
                if is_in_a[idx] {
                    continue;
                }
                let p = fb[idx].p;
                let step = bainv2[v][idx];
                if add_root {
                    let s1 = soln1[idx] + step;
                    soln1[idx] = if s1 >= p { s1 - p } else { s1 };
                    let s2 = soln2[idx] + step;
                    soln2[idx] = if s2 >= p { s2 - p } else { s2 };
                } else {
                    soln1[idx] = if soln1[idx] >= step {
                        soln1[idx] - step
                    } else {
                        soln1[idx] + p - step
                    };
                    soln2[idx] = if soln2[idx] >= step {
                        soln2[idx] - step
                    } else {
                        soln2[idx] + p - step
                    };
                }
            }
        }

        for &idx in &best_chosen {
            is_in_a[idx] = false;
        }
    }

    if full_rels.len() <= fb_len + 1 {
        return None;
    }

    let nrows = full_rels.len();
    let ncols = fb_len + 1;
    let col_words = ncols.div_ceil(64);
    let row_words = nrows.div_ceil(64);

    let mut mat: Vec<Vec<u64>> = vec![vec![0u64; col_words]; nrows];
    let mut hist: Vec<Vec<u64>> = vec![vec![0u64; row_words]; nrows];
    for (r, rel) in full_rels.iter().enumerate() {
        hist[r][r >> 6] = 1u64 << (r & 63);
        for &(col, e) in &rel.exps {
            if e & 1 == 1 {
                mat[r][col >> 6] ^= 1u64 << (col & 63);
            }
        }
    }

    let mut pivot_row_for_col: Vec<Option<usize>> = vec![None; ncols];
    let mut null_vecs: Vec<Vec<usize>> = Vec::new();

    for r in 0..nrows {
        for (c, piv) in pivot_row_for_col.iter_mut().enumerate().take(ncols) {
            if (mat[r][c >> 6] >> (c & 63)) & 1 == 0 {
                continue;
            }
            if let Some(pr) = *piv {
                for w in 0..col_words {
                    mat[r][w] ^= mat[pr][w];
                }
                for w in 0..row_words {
                    hist[r][w] ^= hist[pr][w];
                }
            } else {
                *piv = Some(r);
                break;
            }
        }
        if mat[r].iter().all(|&w| w == 0) {
            let mut dep = Vec::new();
            for (w, &word) in hist[r].iter().enumerate() {
                let mut bits = word;
                while bits != 0 {
                    let tz = bits.trailing_zeros() as usize;
                    dep.push((w << 6) + tz);
                    bits &= bits - 1;
                }
            }
            if !dep.is_empty() {
                null_vecs.push(dep);
            }
        }
    }

    let mut total_exp = vec![0u64; ncols];
    for dep in &null_vecs {
        total_exp.fill(0);
        let mut x_prod = BigUint::one();
        let mut y_prod = BigUint::one();
        for &r in dep {
            let rel = &full_rels[r];
            x_prod = x_prod.mul(&rel.x_mod_n).rem(n);
            if !rel.extra_y.is_one() {
                y_prod = y_prod.mul(&rel.extra_y).rem(n);
            }
            for &(col, e) in &rel.exps {
                total_exp[col] += e as u64;
            }
        }
        for col in 1..ncols {
            let half = total_exp[col] / 2;
            if half > 0 {
                let p_big = BigUint::from_u64(fb[col - 1].p);
                let pe = BigUint::pow_mod(&p_big, &BigUint::from_u64(half), n);
                y_prod = y_prod.mul(&pe).rem(n);
            }
        }
        let diff = if x_prod >= y_prod {
            x_prod.sub(&y_prod)
        } else {
            y_prod.sub(&x_prod)
        };
        let g = n.gcd(&diff);
        if !g.is_zero() && !g.is_one() && &g < n {
            return Some(g);
        }
        let sum = x_prod.add(&y_prod).rem(n);
        let g2 = n.gcd(&sum);
        if !g2.is_zero() && !g2.is_one() && &g2 < n {
            return Some(g2);
        }
    }

    None
}
