#[cfg(test)]
#[macro_use]
extern crate proptest;

use std::cmp::{self, Ordering};
use std::collections::BinaryHeap;
use std::mem;

#[cfg(test)]
mod tests;

/// A trait used to implement inverted-index-style fast intersection.
/// It differs from Iterator in two main ways:
/// - Items are yielded in sorted order.
/// - Given an item, we can efficiently skip forward to it.
pub trait SkippingSearch {
    type Item : Ord;

    /// Returns the smallest value for which
    /// `find_and_advance` *may* return true.
    /// For efficiency reasons, making sure the value
    /// is one for which `find_and_advance` *will*
    /// return true is preferred, when possible.
    #[inline]
    fn suggest_next(&self) -> Option<Self::Item>;

    /// Returns whether this contains the passed-in value.
    /// Also mutates the receiver to forget about any values
    /// smaller than or equal to the item.
    #[inline]
    fn find_and_advance(&mut self, item : &Self::Item) -> bool;

    /// Returns a lower/upper bound on the number of values
    /// that can be obtained by using `self.find_and_advance(self.suggest_next())`
    /// repeatedly.
    /// `(0, None)` is a valid, minimally constraining answer.
    /// `(n, Some(n))` is a maximally constraining answer.
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>);
}

/// Turns a `SkippingSearch` implementor into a standard iterator.
pub struct SkippingIterator<S>(S) where S : SkippingSearch;

impl<S> SkippingIterator<S> where S : SkippingSearch {
    pub fn new(s : S) -> Self {
        SkippingIterator(s)
    }
}

impl<S> Iterator for SkippingIterator<S> where S : SkippingSearch {
    type Item = S::Item;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(item) = self.0.suggest_next() {
            if self.0.find_and_advance(&item) {
                return Some(item);
            }
        }
        None
    }
}

/// A cmp function that treats None as larger than anything else
/// This is useful here because None is what you get past the end of an array
fn none_largest_cmp<T>(item1 : &Option<T>, item2 : &Option<T>) -> Ordering where T : Ord {
    match (item1, item2) {
        (None, None) => Ordering::Equal,
        (None, _) => Ordering::Greater,
        (_, None) => Ordering::Less,
        (Some(v1), Some(v2)) => v1.cmp(v2),
    }
}

/// A struct that's exactly like Option, except None > Some(_)
#[derive(Debug, PartialEq, Eq)]
struct NoneLargest<V>(Option<V>) where V : Ord;

impl<V> PartialOrd for NoneLargest<V> where V : Ord {
    fn partial_cmp(&self, other : &Self) -> Option<Ordering> {
        Some(none_largest_cmp(&self.0, &other.0))
    }
}

impl<V> Ord for NoneLargest<V> where V : Ord {
    fn cmp(&self, other : &Self) -> Ordering {
        none_largest_cmp(&self.0, &other.0)
    }
}

/// Finds `item` in a sorted `slice` by doing exponential search
/// returns `Ok(remaining_slice)`, where `remaining_slice` starts right past index at which `item` was found.
/// If `item` is present multiple times, `i` may be the index of any of them.
/// This takes `O(log(i))` time.
/// # Errors
/// If `item` is not in the array, this will return `Err(remaining_slice)`
/// where remaining_slice contains all elements strictly greater than `item`.
/// This takes `O(log(j))` time, where `j` is the index of the first such element.
#[inline]
fn exponential_search<'a, T>(slice : &'a[T], item : &T) -> Result<&'a[T], &'a[T]> where T : Ord {
    let mut search_index = 1;
    let bin_search_result = loop {
        match slice.get(search_index - 1).map(|element|{item.cmp(element)}) {
            Some(Ordering::Equal) => return Ok(&slice[search_index..]),
            Some(Ordering::Greater) => {
                search_index *= 2;
            },
            Some(Ordering::Less) => break slice[search_index/2..search_index-1].binary_search(item),
            None => break slice[search_index/2..].binary_search(item),
        }
    };
    bin_search_result.map(|idx|{
        &slice[search_index/2+idx+1..]
    }).map_err(|idx|{
        &slice[search_index/2+idx..]
    })
}

/// Sorted slices are the basic building block of `SkippingSearch`.
/// TODO: Decide whether a wrapper type that `debug_asserts!` sortedness is
/// appropriate to use here, and whether we should allow selection of search method,
/// like linear/binary_search/exponential_search.
impl<'a, T> SkippingSearch for &'a [T] where T : Ord + 'a {
    type Item = &'a T;

    fn suggest_next(&self) -> Option<&'a T> {
        self.first()
    }

    fn find_and_advance(&mut self, item : &&'a T) -> bool {
        let result = exponential_search(self, item);
        let found = result.is_ok();
        *self = result.unwrap_or_else(|s|{s});
        found
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }
}

/// Combines two `SkippingSearch` objects and only returns their pair-wise intersection.
/// If you're going to combine more than 2 of the same type at once, consider `MultiIntersection` instead.
pub struct PairIntersection<Left, Right> where Left : SkippingSearch, Right : SkippingSearch<Item=Left::Item> {
    left : Left,
    right : Right,
}

impl<Left, Right> PairIntersection<Left, Right> where Left : SkippingSearch, Right : SkippingSearch<Item=Left::Item> {
    pub fn new(left : Left, right : Right) -> Self {
        Self {
            left,
            right,
        }
    }
}

impl<Left, Right> SkippingSearch for PairIntersection<Left, Right> where Left : SkippingSearch, Right : SkippingSearch<Item=Left::Item> {
    type Item = Left::Item;

    fn suggest_next(&self) -> Option<Self::Item> {
        // The larger value is the only one that has a chance of being output.
        cmp::max(
            NoneLargest(self.left.suggest_next()),
            NoneLargest(self.right.suggest_next()),
        ).0
    }

    fn find_and_advance(&mut self, item : &Self::Item) -> bool {
        self.left.find_and_advance(item) &&
        self.right.find_and_advance(item)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (_, left_max) = self.left.size_hint();
        let (_, right_max) = self.right.size_hint();
        (
            0,
            cmp::min(
                NoneLargest(left_max),
                NoneLargest(right_max),
            ).0,
        )
    }
}

/// Combines an arbitrary number of `SkippingSearch` objects, and returns only the items present in all of them.
pub struct MultiIntersection<S> where S : SkippingSearch {
    sub_searches : Vec<S>,
}

impl<S> MultiIntersection<S> where S : SkippingSearch {
    pub fn new(mut sub_searches : Vec<S>) -> Self {
        assert!(sub_searches.len() > 0);
        sub_searches.sort_by_key(|s|{
            NoneLargest(s.size_hint().1)
        });
        Self {
            sub_searches,
        }
    }
}

impl<S> SkippingSearch for MultiIntersection<S> where S : SkippingSearch {
    type Item = S::Item;

    fn suggest_next(&self) -> Option<Self::Item> {
        self.sub_searches.iter().map(|s|{
            NoneLargest(s.suggest_next())
        }).max().and_then(|o|{o.0})
    }

    fn find_and_advance(&mut self, item : &Self::Item) -> bool {
        self.sub_searches.iter_mut().all(|s|{
            s.find_and_advance(item)
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let max = self.sub_searches.iter().map(|s|{
            NoneLargest(s.size_hint().1)
        }).max().expect("We ensured there was at least one sub search").0;
        (0, max)
    }
}

/// Combines an arbitrary number of `SkippingSearch` objects,
/// and returns only the items present in at least `target_count` of them.
/// Having `target_count == sub_searches.len()` or `target_count == 1` is valid but discouraged.
/// Instead use dedicated intersection/union constructs.
pub struct CountingIntersection<S> where S : SkippingSearch {
    sub_searches : Vec<S>,
    allowed_failures : usize,
}

impl<S> CountingIntersection<S> where S : SkippingSearch {
    pub fn new(mut sub_searches : Vec<S>, target_count : usize) -> Self {
        assert!(target_count > 0);
        assert!(sub_searches.len() >= target_count);
        sub_searches.sort_by_key(|s|{
            NoneLargest(s.size_hint().1)
        });
        let allowed_failures = sub_searches.len() - target_count;
        Self {
            sub_searches,
            allowed_failures,
        }
    }
}

impl<S> SkippingSearch for CountingIntersection<S> where S : SkippingSearch {
    type Item = S::Item;

    fn suggest_next(&self) -> Option<Self::Item> {
        // With n allowable failures, the nth-largest (0-indexed) value is what we want.
        // So we keep only the n+1 largest values as we scan, then take the minimum of that.
        let capacity = self.allowed_failures + 1;
        let mut n_largest = BinaryHeap::with_capacity(capacity);
        self.sub_searches.iter().map(|s|{cmp::Reverse(NoneLargest(s.suggest_next()))}).for_each(|candidate|{
            if n_largest.len() < capacity {
                n_largest.push(candidate);
            } else {
                let mut smallest_of_largest = n_largest.peek_mut().expect("len() >= capacity > 0");
                if candidate.0 > smallest_of_largest.0 {
                    mem::replace(&mut *smallest_of_largest, candidate);
                }
            }
        });
        n_largest.into_iter().map(|r|{r.0}).min().expect("len() == capacity > 0").0
    }

    fn find_and_advance(&mut self, item : &Self::Item) -> bool {
        let mut failures_left = self.allowed_failures;
        self.sub_searches.iter_mut().all(|s|{
            s.find_and_advance(item) || if failures_left > 0 {
                failures_left -= 1;
                true
            } else {
                false
            }
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let capacity = self.allowed_failures + 1;
        let mut n_smallest_maxes = BinaryHeap::with_capacity(capacity);

        self.sub_searches.iter().map(|s|{
            let (_, max) = s.size_hint();
            NoneLargest(max)
        }).for_each(|max| {
            if n_smallest_maxes.len() < capacity {
                n_smallest_maxes.push(max);
            } else {
                let mut largest_of_smallest = n_smallest_maxes.peek_mut().expect("len() >= capacity > 0");
                if max < *largest_of_smallest {
                    mem::replace(&mut *largest_of_smallest, max);
                }
            }
        });

        (
            0,
            n_smallest_maxes.into_iter().max().expect("len() == capacity > 0").0,
        )
    }
}
