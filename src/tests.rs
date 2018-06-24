// Copyright 2018 Christophe Biocca.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use ::{
    SkippingIterator,
    PairIntersection,
    MultiIntersection,
    CountingIntersection,
};
use proptest::strategy::{Strategy, ValueTree};
use proptest::test_runner::{TestRunner, Config};
use std::ops::Range;

fn runner() -> TestRunner {
    TestRunner::new(
        Config::with_source_file(file!()),
    )
}

fn four_strictly_increasing_ints(range : Range<i32>) -> impl Strategy<Value=impl ValueTree<Value=(i32, i32, i32, i32)>> {
    let start = range.start;
    let end = range.end;
    ((start + 2)..(end - 1)).prop_flat_map(move |midpoint|{
        (
            (start + 1)..midpoint,
            (midpoint + 1)..end,
        ).prop_flat_map(move |(left_midpoint, right_midpoint)|{
            (
                start..left_midpoint,
                left_midpoint..midpoint,
                midpoint..right_midpoint,
                right_midpoint..end,
            )
        })
    })
}

#[test]
fn test_pair_intersection_empty_for_non_overlapping_slices() {
    runner().run(
        &four_strictly_increasing_ints(-1_000..1_000),
        |&(a, b, c, d)|{
            // a..b and c..d are guaranteed disjoint.
            let lesser_slice = (a..b).into_iter().collect::<Vec<_>>();
            let greater_slice = (c..d).into_iter().collect::<Vec<_>>();

            prop_assert_eq!(
                SkippingIterator::new(
                    PairIntersection::new(
                        &lesser_slice[..],
                        &greater_slice[..],
                    ),
                ).count(),
                0
            );
            Ok(())
        },
    ).unwrap()
}

#[test]
fn test_multi_intersection_empty_for_non_mutually_overlapping_slices() {
    runner().run(
        &four_strictly_increasing_ints(-1_000..1_000),
        |&(a, b, c, d)|{
            // a..c, b..d and (a..b).chain(c..d) are pairwise intersecting,
            // but are mutually disjoint.
            let left_slice = (a..c).into_iter().collect::<Vec<_>>();
            let right_slice = (b..d).into_iter().collect::<Vec<_>>();
            let all_but_middle = (a..b).into_iter().chain(c..d).collect::<Vec<_>>();

            prop_assert_eq!(
                SkippingIterator::new(
                    MultiIntersection::new(
                        vec![
                            &left_slice[..],
                            &right_slice[..],
                            &all_but_middle[..],
                        ],
                    ),
                ).count(),
                0
            );
            Ok(())
        },
    ).unwrap()
}

#[test]
fn test_counting_intersection_empty_for_insufficiently_overlapping_slices() {
    runner().run(
        &four_strictly_increasing_ints(-1_000..1_000),
        |&(a, b, c, d)|{
            // For each point along a..d 2/4 slices contain it.
            // We're going to ask for 3.
            let lesser_slice = (a..b).into_iter().collect::<Vec<_>>();
            let left_slice = (a..c).into_iter().collect::<Vec<_>>();
            let right_slice = (b..d).into_iter().collect::<Vec<_>>();
            let greater_slice = (c..d).into_iter().collect::<Vec<_>>();

            prop_assert_eq!(
                SkippingIterator::new(
                    CountingIntersection::new(
                        vec![
                            &lesser_slice[..],
                            &left_slice[..],
                            &right_slice[..],
                            &greater_slice[..],
                        ],
                        3,
                    ),
                ).count(),
                0
            );
            Ok(())
        },
    ).unwrap()
}

#[test]
fn test_pair_intersection_results_for_overlapping_slices() {
    runner().run(
        &four_strictly_increasing_ints(-1_000..1_000),
        |&(a, b, c, d)|{
            // These are the small slices and don't overlap with each other.
            let lesser_slice = (a..b).into_iter().collect::<Vec<_>>();
            let middle_slice = (b..c).into_iter().collect::<Vec<_>>();
            let greater_slice = (c..d).into_iter().collect::<Vec<_>>();

            // These are medium-sized and overlap each other over b..c
            let left_slice = (a..c).into_iter().collect::<Vec<_>>();
            let right_slice = (b..d).into_iter().collect::<Vec<_>>();

            // This one overlaps all other slices.
            let big_slice = (a..d).into_iter().collect::<Vec<_>>();

            fn check_intersect(left : &[i32], right : &[i32], target : &[i32]) -> bool {
                SkippingIterator::new(
                    PairIntersection::new(
                        left,
                        right,
                    ),
                ).eq(
                    target.iter(),
                )
            }

            for any_slice in vec![
                &lesser_slice,
                &middle_slice,
                &greater_slice,
                &left_slice,
                &right_slice,
                &big_slice,
            ] {
                prop_assert!(
                    check_intersect(any_slice, any_slice, any_slice)
                );
            }

            for big_slice_subslice in vec![&lesser_slice, &middle_slice, &greater_slice, &left_slice, &right_slice] {
                prop_assert!(
                    check_intersect(big_slice_subslice, &big_slice, big_slice_subslice)
                );
            }

            for left_slice_subslice in vec![&lesser_slice, &middle_slice] {
                prop_assert!(
                    check_intersect(left_slice_subslice, &left_slice, left_slice_subslice)
                );
            }

            for right_slice_subslice in vec![&middle_slice, &greater_slice] {
                prop_assert!(
                    check_intersect(right_slice_subslice, &right_slice, right_slice_subslice)
                );
            }

            prop_assert!(
                check_intersect(&left_slice, &right_slice, &middle_slice)
            );

            Ok(())
        },
    ).unwrap()
}

#[test]
fn test_multi_intersection_results_for_overlapping_slices() {
    runner().run(
        &four_strictly_increasing_ints(-1_000..1_000),
        |&(a, b, c, d)|{
            // These are the small slices and don't overlap with each other.
            let lesser_slice = (a..b).into_iter().collect::<Vec<_>>();
            let middle_slice = (b..c).into_iter().collect::<Vec<_>>();
            let greater_slice = (c..d).into_iter().collect::<Vec<_>>();

            // These are medium-sized and overlap each other over b..c
            let left_slice = (a..c).into_iter().collect::<Vec<_>>();
            let right_slice = (b..d).into_iter().collect::<Vec<_>>();

            // This one overlaps all other slices.
            let big_slice = (a..d).into_iter().collect::<Vec<_>>();

            fn check_intersect(slices : Vec<&[i32]>, target : &[i32]) -> bool {
                SkippingIterator::new(
                    MultiIntersection::new(
                        slices,
                    ),
                ).eq(
                    target.iter(),
                )
            }

            prop_assert!(
                check_intersect(
                    vec![&lesser_slice, &left_slice, &big_slice],
                    &lesser_slice,
                )
            );

            prop_assert!(
                check_intersect(
                    vec![&left_slice, &right_slice, &big_slice],
                    &middle_slice,
                )
            );

            prop_assert!(
                check_intersect(
                    vec![&middle_slice, &left_slice, &right_slice, &big_slice],
                    &middle_slice,
                )
            );

            prop_assert!(
                check_intersect(
                    vec![&greater_slice, &right_slice, &big_slice],
                    &greater_slice,
                )
            );

            Ok(())
        },
    ).unwrap()
}

#[test]
fn test_counting_intersection_results_for_sufficiently_overlapping_slices() {
    runner().run(
        &four_strictly_increasing_ints(-1_000..1_000),
        |&(a, b, c, d)|{
            // These are the small slices and don't overlap with each other.
            let lesser_slice = (a..b).into_iter().collect::<Vec<_>>();
            let middle_slice = (b..c).into_iter().collect::<Vec<_>>();
            let greater_slice = (c..d).into_iter().collect::<Vec<_>>();

            // These are medium-sized and overlap each other over b..c
            let left_slice = (a..c).into_iter().collect::<Vec<_>>();
            let right_slice = (b..d).into_iter().collect::<Vec<_>>();

            // This one overlaps all other slices.
            let big_slice = (a..d).into_iter().collect::<Vec<_>>();

            fn check_intersect(slices : Vec<&[i32]>, target_count : usize, target : &[i32]) -> bool {
                SkippingIterator::new(
                    CountingIntersection::new(
                        slices.clone(),
                        target_count,
                    ),
                ).eq(target)
            }

            prop_assert!(
                check_intersect(
                    vec![
                        &lesser_slice,
                        &middle_slice,
                        &greater_slice,
                    ],
                    1,
                    &big_slice,
                )
            );

            prop_assert!(
                check_intersect(
                    vec![
                        &left_slice,
                        &right_slice,
                        &middle_slice,
                    ],
                    1,
                    &big_slice,
                )
            );

            prop_assert!(
                check_intersect(
                    vec![
                        &left_slice,
                        &right_slice,
                    ],
                    2,
                    &middle_slice,
                )
            );

            prop_assert!(
                check_intersect(
                    vec![
                        &lesser_slice,
                        &left_slice,
                        &right_slice,
                        &greater_slice,
                    ],
                    2,
                    &big_slice,
                )
            );

            prop_assert!(
                check_intersect(
                    vec![
                        &lesser_slice,
                        &left_slice,
                        &middle_slice,
                        &right_slice,
                        &greater_slice,
                        &big_slice,
                    ],
                    3,
                    &big_slice,
                )
            );

            prop_assert!(
                check_intersect(
                    vec![
                        &lesser_slice,
                        &left_slice,
                        &middle_slice,
                        &right_slice,
                        &greater_slice,
                        &big_slice,
                    ],
                    4,
                    &middle_slice,
                )
            );

            Ok(())
        },
    ).unwrap()
}
