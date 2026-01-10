//! Deterministic RNG for simulation
//!
//! TigerStyle: ChaCha20-based RNG for reproducibility.

use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha20Rng;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};

/// Deterministic random number generator
///
/// Uses ChaCha20 for cryptographic-quality randomness with reproducibility.
/// Given the same seed, will produce the same sequence of random values.
#[derive(Debug, Clone)]
pub struct DeterministicRng {
    /// The original seed (for logging/reproduction)
    seed: u64,
    /// The underlying RNG
    rng: Arc<Mutex<ChaCha20Rng>>,
    /// Counter for forking
    fork_counter: Arc<AtomicU64>,
}

impl DeterministicRng {
    /// Create a new deterministic RNG with the given seed
    pub fn new(seed: u64) -> Self {
        let rng = ChaCha20Rng::seed_from_u64(seed);
        Self {
            seed,
            rng: Arc::new(Mutex::new(rng)),
            fork_counter: Arc::new(AtomicU64::new(0)),
        }
    }

    /// Create from environment variable DST_SEED or generate random seed
    ///
    /// Always logs the seed for reproducibility.
    pub fn from_env_or_random() -> Self {
        let seed = std::env::var("DST_SEED")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or_else(rand::random);

        tracing::info!(seed = seed, "DST seed (set DST_SEED={} to replay)", seed);

        Self::new(seed)
    }

    /// Get the seed used to create this RNG
    pub fn seed(&self) -> u64 {
        self.seed
    }

    /// Generate a random u64
    pub fn next_u64(&self) -> u64 {
        self.rng.lock().unwrap().gen()
    }

    /// Generate a random u32
    pub fn next_u32(&self) -> u32 {
        self.rng.lock().unwrap().gen()
    }

    /// Generate a random f64 in [0, 1)
    pub fn next_f64(&self) -> f64 {
        self.rng.lock().unwrap().gen()
    }

    /// Generate a random bool with given probability of true
    pub fn next_bool(&self, probability: f64) -> bool {
        debug_assert!(
            (0.0..=1.0).contains(&probability),
            "probability must be in [0, 1]"
        );
        self.next_f64() < probability
    }

    /// Generate a random value in the given range [min, max)
    pub fn next_range(&self, min: u64, max: u64) -> u64 {
        debug_assert!(min < max, "min must be less than max");
        let range = max - min;
        min + (self.next_u64() % range)
    }

    /// Generate a random index for a slice of given length
    pub fn next_index(&self, len: usize) -> usize {
        debug_assert!(len > 0, "length must be positive");
        (self.next_u64() as usize) % len
    }

    /// Shuffle a slice in place
    pub fn shuffle<T>(&self, slice: &mut [T]) {
        let mut rng = self.rng.lock().unwrap();
        for i in (1..slice.len()).rev() {
            let j = rng.gen_range(0..=i);
            slice.swap(i, j);
        }
    }

    /// Choose a random element from a slice
    pub fn choose<'a, T>(&self, slice: &'a [T]) -> Option<&'a T> {
        if slice.is_empty() {
            None
        } else {
            Some(&slice[self.next_index(slice.len())])
        }
    }

    /// Fork the RNG to create an independent stream
    ///
    /// The forked RNG is seeded deterministically from the parent.
    pub fn fork(&self) -> Self {
        let fork_id = self.fork_counter.fetch_add(1, Ordering::SeqCst);
        let fork_seed = self
            .seed
            .wrapping_add(fork_id)
            .wrapping_mul(0x9E3779B97F4A7C15);

        Self {
            seed: fork_seed,
            rng: Arc::new(Mutex::new(ChaCha20Rng::seed_from_u64(fork_seed))),
            fork_counter: Arc::new(AtomicU64::new(0)),
        }
    }

    /// Generate random bytes
    pub fn fill_bytes(&self, dest: &mut [u8]) {
        self.rng.lock().unwrap().fill(dest);
    }
}

impl Default for DeterministicRng {
    fn default() -> Self {
        Self::new(0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rng_reproducibility() {
        let rng1 = DeterministicRng::new(12345);
        let rng2 = DeterministicRng::new(12345);

        for _ in 0..100 {
            assert_eq!(rng1.next_u64(), rng2.next_u64());
        }
    }

    #[test]
    fn test_rng_different_seeds() {
        let rng1 = DeterministicRng::new(12345);
        let rng2 = DeterministicRng::new(54321);

        // Different seeds should produce different sequences
        let seq1: Vec<_> = (0..10).map(|_| rng1.next_u64()).collect();
        let seq2: Vec<_> = (0..10).map(|_| rng2.next_u64()).collect();

        assert_ne!(seq1, seq2);
    }

    #[test]
    fn test_rng_bool() {
        let rng = DeterministicRng::new(42);

        // With probability 0, should never be true
        for _ in 0..100 {
            assert!(!rng.next_bool(0.0));
        }

        // With probability 1, should always be true
        for _ in 0..100 {
            assert!(rng.next_bool(1.0));
        }
    }

    #[test]
    fn test_rng_range() {
        let rng = DeterministicRng::new(42);

        for _ in 0..100 {
            let value = rng.next_range(10, 20);
            assert!((10..20).contains(&value));
        }
    }

    #[test]
    fn test_rng_fork() {
        let rng = DeterministicRng::new(12345);

        // Fork should be deterministic
        let fork1a = rng.fork();
        let fork1b_seed = {
            let rng2 = DeterministicRng::new(12345);
            rng2.fork().seed()
        };

        assert_eq!(fork1a.seed(), fork1b_seed);
    }

    #[test]
    fn test_rng_shuffle() {
        let rng = DeterministicRng::new(42);
        let mut data1 = vec![1, 2, 3, 4, 5];
        let mut data2 = vec![1, 2, 3, 4, 5];

        let rng2 = DeterministicRng::new(42);
        rng.shuffle(&mut data1);
        rng2.shuffle(&mut data2);

        // Same seed should produce same shuffle
        assert_eq!(data1, data2);
    }

    #[test]
    fn test_rng_choose() {
        let rng = DeterministicRng::new(42);
        let data = vec!["a", "b", "c"];

        let choice = rng.choose(&data);
        assert!(choice.is_some());
        assert!(data.contains(choice.unwrap()));

        // Empty slice returns None
        let empty: Vec<i32> = vec![];
        assert!(rng.choose(&empty).is_none());
    }
}
