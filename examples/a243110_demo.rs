//! Demonstrates `ntheory_rs::n_order` on all 49 proven terms of OEIS A243110,
//! reproducing OEIS A359446 (decimal periods of 1/A243110(n)) in milliseconds.

use ntheory_rs::{is_prime, n_order};
use std::time::Instant;

const A243110: [u64; 49] = [
    3,
    11,
    37,
    101,
    239,
    271,
    1933,
    3191,
    3541,
    4093,
    4649,
    9091,
    21649,
    52579,
    123551,
    210631,
    238681,
    329401,
    333667,
    513239,
    909091,
    2071723,
    2906161,
    5882353,
    10838689,
    35121409,
    52986961,
    70541929,
    83251631,
    99990001,
    121499449,
    247629013,
    265371653,
    1052788969,
    1056689261,
    1058313049,
    5363222357,
    21993833369,
    66554101249,
    77843839397,
    182521213001,
    908191467191,
    999999000001,
    2559647034361,
    7370364319027,
    8119594779271,
    8985695684401,
    14103673319201,
    18371524594609,
];

const A359446: [u64; 49] = [
    1, 2, 3, 4, 7, 5, 21, 29, 20, 22, 7, 10, 11, 18, 35, 51, 45, 61, 9, 11, 14, 17, 15, 16, 21, 47,
    51, 54, 55, 24, 28, 37, 13, 44, 44, 26, 17, 34, 96, 29, 25, 113, 36, 59, 131, 85, 90, 100, 92,
];

fn main() {
    let t0 = Instant::now();
    let mut prev_m = 0u64;
    for (idx, (&p, &expected_k)) in A243110.iter().zip(A359446.iter()).enumerate() {
        assert!(is_prime(p));
        let k = n_order(10, p).unwrap();
        assert_eq!(k, expected_k);
        let m = (p - 1) / k;
        assert!(m > prev_m);
        prev_m = m;
        println!(
            "a({:2}) = {:15} | period = {:3} | m = {:13}",
            idx + 1,
            p,
            k,
            m
        );
    }
    println!(
        "\nVerified all 49 terms of A243110 & A359446 in {:.3} ms!",
        t0.elapsed().as_secs_f64() * 1000.0
    );
}
