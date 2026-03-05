//! Shared immutable vector wrapper with lazy-cloning iteration.
//!
//! Generated language helpers often need `IntoIterator<Item = T>` but may also
//! perform cheap existence checks (`next().is_none()`). This wrapper avoids
//! cloning the full vector for those checks by cloning items lazily during
//! iteration.

use std::sync::Arc;

#[derive(Debug, Clone)]
pub struct SharedVec<T> {
    data: Arc<Vec<T>>,
}

impl<T> SharedVec<T> {
    pub fn from_arc(data: Arc<Vec<T>>) -> Self {
        Self { data }
    }

    pub fn from_vec(data: Vec<T>) -> Self {
        Self { data: Arc::new(data) }
    }

    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }

    pub fn as_slice(&self) -> &[T] {
        self.data.as_slice()
    }
}

pub struct SharedVecIntoIter<T> {
    data: Arc<Vec<T>>,
    idx: usize,
}

impl<T: Clone> Iterator for SharedVecIntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        let out = self.data.get(self.idx).cloned();
        if out.is_some() {
            self.idx = self.idx.saturating_add(1);
        }
        out
    }
}

impl<T: Clone> IntoIterator for SharedVec<T> {
    type Item = T;
    type IntoIter = SharedVecIntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        SharedVecIntoIter { data: self.data, idx: 0 }
    }
}

#[cfg(test)]
mod tests {
    use super::SharedVec;
    use std::sync::Arc;

    #[test]
    fn lazy_iter_supports_exists_and_full_walk() {
        let shared = SharedVec::from_arc(Arc::new(vec![1, 2, 3]));
        assert_eq!(shared.clone().into_iter().next(), Some(1));
        let collected: Vec<_> = shared.into_iter().collect();
        assert_eq!(collected, vec![1, 2, 3]);
    }
}
