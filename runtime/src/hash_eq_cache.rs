//! Collision-safe hash-bucket cache keyed by `Hash + Eq` values.
//!
//! This avoids cloning full keys into the top-level map while still verifying
//! equality on collisions.

use std::collections::HashMap;
use std::hash::{Hash, Hasher};

/// Generic hash-bucket cache with equality checks inside hash buckets.
#[derive(Debug, Clone)]
pub struct HashEqCache<K, V>
where
    K: Clone + Eq + Hash,
    V: Clone,
{
    buckets: HashMap<u64, Vec<(K, V)>>,
    max_buckets: usize,
}

impl<K, V> Default for HashEqCache<K, V>
where
    K: Clone + Eq + Hash,
    V: Clone,
{
    fn default() -> Self {
        Self {
            buckets: HashMap::new(),
            max_buckets: 256,
        }
    }
}

impl<K, V> HashEqCache<K, V>
where
    K: Clone + Eq + Hash,
    V: Clone,
{
    /// Create a cache with a specific maximum number of hash buckets before
    /// coarse eviction (`clear`) is applied.
    pub fn with_max_buckets(max_buckets: usize) -> Self {
        Self { buckets: HashMap::new(), max_buckets }
    }

    fn key_hash(key: &K) -> u64 {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        key.hash(&mut hasher);
        hasher.finish()
    }

    /// Lookup by key, returning a cloned cached value when present.
    pub fn get(&self, key: &K) -> Option<V> {
        let hash = Self::key_hash(key);
        self.buckets.get(&hash).and_then(|bucket| {
            bucket.iter().find_map(|(cached_key, cached_value)| {
                if cached_key == key {
                    Some(cached_value.clone())
                } else {
                    None
                }
            })
        })
    }

    /// Insert or replace a key/value entry.
    pub fn insert(&mut self, key: K, value: V) {
        if self.buckets.len() >= self.max_buckets {
            self.buckets.clear();
        }
        let hash = Self::key_hash(&key);
        let bucket = self.buckets.entry(hash).or_default();
        if let Some((_, cached_value)) =
            bucket.iter_mut().find(|(cached_key, _)| cached_key == &key)
        {
            *cached_value = value;
        } else {
            bucket.push((key, value));
        }
    }

    /// Lookup first; otherwise compute, insert, and return.
    pub fn get_or_insert_with<F>(&mut self, key: &K, compute: F) -> V
    where
        F: FnOnce() -> V,
    {
        if let Some(hit) = self.get(key) {
            return hit;
        }
        let built = compute();
        self.insert(key.clone(), built.clone());
        built
    }
}

#[cfg(test)]
mod tests {
    use super::HashEqCache;
    use std::hash::{Hash, Hasher};

    #[derive(Debug, Clone, Eq, PartialEq)]
    struct CollisionKey(u64);

    impl Hash for CollisionKey {
        fn hash<H: Hasher>(&self, state: &mut H) {
            // Force all keys into one hash bucket to validate equality checks.
            0u8.hash(state);
        }
    }

    #[test]
    fn collision_bucket_is_equality_safe() {
        let mut cache = HashEqCache::<CollisionKey, String>::default();
        cache.insert(CollisionKey(1), "one".to_string());
        cache.insert(CollisionKey(2), "two".to_string());
        assert_eq!(cache.get(&CollisionKey(1)).as_deref(), Some("one"));
        assert_eq!(cache.get(&CollisionKey(2)).as_deref(), Some("two"));
        assert_eq!(cache.get(&CollisionKey(3)), None);
    }

    #[test]
    fn insert_replaces_existing_key() {
        let mut cache = HashEqCache::<CollisionKey, i32>::default();
        cache.insert(CollisionKey(7), 10);
        cache.insert(CollisionKey(7), 11);
        assert_eq!(cache.get(&CollisionKey(7)), Some(11));
    }

    #[test]
    fn get_or_insert_with_reuses_hits() {
        let mut cache = HashEqCache::<CollisionKey, i32>::default();
        let first = cache.get_or_insert_with(&CollisionKey(9), || 42);
        let second = cache.get_or_insert_with(&CollisionKey(9), || 99);
        assert_eq!(first, 42);
        assert_eq!(second, 42);
    }
}
