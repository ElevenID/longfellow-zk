// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

pub struct Tableau<T> {
    data: Vec<T>,
    width: usize,
    height: usize,
    wipe: Option<fn(&mut [T])>,
}

impl<T> Tableau<T> {
    pub fn new(height: usize, width: usize, default: T) -> Self
    where
        T: Clone,
    {
        Self {
            data: vec![default; height * width],
            width,
            height,
            wipe: None,
        }
    }

    pub fn new_zeroizing(height: usize, width: usize, default: T) -> Self
    where
        T: Clone + zeroize::Zeroize,
    {
        fn wipe<T: zeroize::Zeroize>(values: &mut [T]) {
            for value in values {
                zeroize::Zeroize::zeroize(value);
            }
        }

        Self {
            data: vec![default; height * width],
            width,
            height,
            wipe: Some(wipe::<T>),
        }
    }

    #[must_use]
    pub fn row(&self, r: usize) -> &[T] {
        assert!(r < self.height);
        &self.data[r * self.width..(r + 1) * self.width]
    }

    pub fn row_mut(&mut self, r: usize) -> &mut [T] {
        assert!(r < self.height);
        &mut self.data[r * self.width..(r + 1) * self.width]
    }

    #[cfg(feature = "prover")]
    pub(crate) fn guard_vec(&self, data: Vec<T>) -> GuardedVec<T> {
        GuardedVec {
            data,
            wipe: self.wipe,
        }
    }
}

#[cfg(feature = "prover")]
pub(crate) struct GuardedVec<T> {
    data: Vec<T>,
    wipe: Option<fn(&mut [T])>,
}

#[cfg(feature = "prover")]
impl<T> std::ops::Deref for GuardedVec<T> {
    type Target = Vec<T>;

    fn deref(&self) -> &Self::Target {
        &self.data
    }
}

#[cfg(feature = "prover")]
impl<T> std::ops::DerefMut for GuardedVec<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.data
    }
}

#[cfg(feature = "prover")]
impl<T> Drop for GuardedVec<T> {
    fn drop(&mut self) {
        if let Some(wipe) = self.wipe {
            wipe(&mut self.data);
        }
    }
}

impl<T> Drop for Tableau<T> {
    fn drop(&mut self) {
        if let Some(wipe) = self.wipe {
            wipe(&mut self.data);
        }
    }
}

impl<T> std::ops::Index<(usize, usize)> for Tableau<T> {
    type Output = T;

    fn index(&self, index: (usize, usize)) -> &Self::Output {
        let (r, c) = index;
        assert!(r < self.height && c < self.width);
        &self.data[r * self.width + c]
    }
}

impl<T> std::ops::IndexMut<(usize, usize)> for Tableau<T> {
    fn index_mut(&mut self, index: (usize, usize)) -> &mut Self::Output {
        let (r, c) = index;
        assert!(r < self.height && c < self.width);
        &mut self.data[r * self.width + c]
    }
}

#[cfg(test)]
mod tests {
    use std::sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    };

    use super::Tableau;
    use zeroize::Zeroize;

    #[derive(Clone)]
    struct Tracked(Arc<AtomicUsize>);

    impl Zeroize for Tracked {
        fn zeroize(&mut self) {
            self.0.fetch_add(1, Ordering::SeqCst);
        }
    }

    #[test]
    fn drop_zeroizes_every_tableau_element() {
        let zeroized = Arc::new(AtomicUsize::new(0));
        {
            let _tableau = Tableau::new_zeroizing(3, 4, Tracked(Arc::clone(&zeroized)));
        }
        assert_eq!(zeroized.load(Ordering::SeqCst), 12);
    }
}
