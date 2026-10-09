//! A tiny deterministic PRNG (SplitMix64, Steele–Lea–Flood 2014). The algebra only uses it for
//! random splitting polynomials in Cantor–Zassenhaus, where any sequence is correct and a fixed
//! seed keeps runs reproducible; the tests and the differential-test generator use it too.

#[derive(Clone, Debug)]
pub struct SplitMix64 {
    state: u64,
}

impl SplitMix64 {
    pub fn new(seed: u64) -> SplitMix64 {
        SplitMix64 { state: seed }
    }

    pub fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// Uniform in `[0, n)` (`n > 0`), by rejection.
    pub fn below(&mut self, n: u64) -> u64 {
        assert!(n > 0);
        let zone = u64::MAX - u64::MAX % n;
        loop {
            let x = self.next_u64();
            if x < zone {
                return x % n;
            }
        }
    }

    /// Uniform in `[lo, hi]`.
    pub fn range(&mut self, lo: i64, hi: i64) -> i64 {
        assert!(lo <= hi);
        lo + self.below((hi - lo) as u64 + 1) as i64
    }

    /// `true` with probability `num/den`.
    pub fn chance(&mut self, num: u64, den: u64) -> bool {
        self.below(den) < num
    }
}
