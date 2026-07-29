/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

/* Context: CRLite system consists of 2 directories /known and /revoked, collected
* by crlite-fetch service. Each CRLite key contains information about a certificate
* issued by different CA.
* */

/* This module determines the partition to a single issuer file. */
use std::cmp::Reverse;
use std::collections::BinaryHeap;

type Timestamp = u64;
const META_SIZE: u64 = 80 * 8;
pub type Partition = Vec<u64>;

/* A partition index is encoded in one byte, so an issuer can have at most 256
* partitions, i.e. at most 255 partition points. */
const MAX_PARTITION_POINTS: usize = 255;

/* Number of local refinement passes made after the merge phase. Each pass is
* O(records), and passes after the second rarely change anything. */
const REFINEMENT_PASSES: usize = 3;

/* Information needed for per-issuer partition */
#[derive(Clone, Debug)]
pub struct PartitionRecord {
    pub time: Timestamp, /* notAfter time, truncated by hour */
    pub n: u64,
    pub r: u64,
}

impl PartitionRecord {
    pub fn new(time: Timestamp, n: u64, r: u64) -> Self {
        PartitionRecord { time, n, r }
    }
}

pub fn log2(num: f64) -> f64 {
    if num == 0.0 { 0.0 } else { num.log2() }
}

pub fn cost(r: u64, n: u64) -> u64 {
    let r = r.min(n - r);
    if r == 0 {
        return META_SIZE;
    }

    let rank = if 2 * r < n {
        log2((n - r) as f64 / r as f64).floor() as u64
    } else {
        0
    };

    r * rank + r + ((n - r) >> rank) + META_SIZE
}

/* Cumulative sums of the (n, r) columns, so that the cost of any range of
* records can be evaluated in constant time. */
struct Prefix {
    n: Vec<u64>,
    r: Vec<u64>,
}

impl Prefix {
    fn new(records: &[PartitionRecord]) -> Self {
        let mut n = Vec::with_capacity(records.len() + 1);
        let mut r = Vec::with_capacity(records.len() + 1);
        n.push(0);
        r.push(0);
        for record in records {
            n.push(n[n.len() - 1] + record.n);
            r.push(r[r.len() - 1] + record.r);
        }
        Prefix { n, r }
    }

    /* Cost of encoding the records in [start, end) as a single partition. */
    fn cost(&self, start: usize, end: usize) -> u64 {
        cost(self.r[end] - self.r[start], self.n[end] - self.n[start])
    }
}

/* Doubly linked list of partitions, used by the merge phase below. Partitions
* are identified by the index of their first record, which never changes as
* neighbors are merged into them. */
struct Partitions {
    prev: Vec<usize>,
    next: Vec<usize>,
    /* end[i] is one past the last record of the partition starting at i. */
    end: Vec<usize>,
    /* Number of times partition i has been merged with a neighbor. Used to
     * discard stale entries in the merge heap. */
    version: Vec<u32>,
    live: Vec<bool>,
    count: usize,
}

impl Partitions {
    /* One partition per record. */
    fn new(len: usize) -> Self {
        Partitions {
            prev: (0..len).map(|i| i.wrapping_sub(1)).collect(),
            next: (0..len).map(|i| i + 1).collect(),
            end: (0..len).map(|i| i + 1).collect(),
            version: vec![0; len],
            live: vec![true; len],
            count: len,
        }
    }

    fn is_first(&self, i: usize) -> bool {
        self.prev[i] == usize::MAX
    }

    fn is_last(&self, i: usize) -> bool {
        self.next[i] == self.end.len()
    }

    /* Absorb the partition following i into i. */
    fn merge_with_next(&mut self, i: usize) {
        let j = self.next[i];
        self.end[i] = self.end[j];
        self.next[i] = self.next[j];
        if !self.is_last(i) {
            self.prev[self.next[i]] = i;
        }
        self.live[j] = false;
        self.version[i] += 1;
        self.count -= 1;
    }

    fn starts(&self) -> Vec<usize> {
        (0..self.live.len()).filter(|&i| self.live[i]).collect()
    }
}

/* Candidate merge of the partition starting at `left` with its successor. The
* fields are ordered so that a max-heap yields the most profitable merge first,
* with ties broken by position to make the output deterministic. */
#[derive(PartialEq, Eq, PartialOrd, Ord)]
struct Merge {
    savings: i64,
    left: Reverse<usize>,
    left_version: u32,
    right_version: u32,
}

/* Choose partition points by agglomerative merging.
*
* Starting from one partition per record, we repeatedly merge the adjacent pair
* whose merge saves the most bits. A merge always saves the META_SIZE overhead
* of one partition, but it costs bits whenever the two partitions have
* different revocation densities, so merging stops once no adjacent pair is
* profitable. Merging continues past that point only if we still have more
* partitions than we can index, in which case the least expensive merges are
* taken. */
fn merge_partitions(records: &[PartitionRecord], prefix: &Prefix) -> Partitions {
    let mut partitions = Partitions::new(records.len());

    let savings = |partitions: &Partitions, i: usize| -> i64 {
        let j = partitions.next[i];
        let (start, mid, end) = (i, j, partitions.end[j]);
        let separate = prefix.cost(start, mid) as i64 + prefix.cost(mid, end) as i64;
        separate - prefix.cost(start, end) as i64
    };

    let candidate = |partitions: &Partitions, i: usize| -> Merge {
        let j = partitions.next[i];
        Merge {
            savings: savings(partitions, i),
            left: Reverse(i),
            left_version: partitions.version[i],
            right_version: partitions.version[j],
        }
    };

    let mut heap: BinaryHeap<Merge> = (0..records.len())
        .filter(|&i| !partitions.is_last(i))
        .map(|i| candidate(&partitions, i))
        .collect();

    while let Some(merge) = heap.pop() {
        if merge.savings <= 0 && partitions.count <= MAX_PARTITION_POINTS + 1 {
            break;
        }
        /* Discard entries that describe a pair that no longer exists. */
        let i = merge.left.0;
        if !partitions.live[i] || partitions.version[i] != merge.left_version {
            continue;
        }
        let j = partitions.next[i];
        if !partitions.live[j] || partitions.version[j] != merge.right_version {
            continue;
        }

        partitions.merge_with_next(i);

        if !partitions.is_first(i) {
            let candidate = candidate(&partitions, partitions.prev[i]);
            heap.push(candidate);
        }
        if !partitions.is_last(i) {
            let candidate = candidate(&partitions, i);
            heap.push(candidate);
        }
    }

    partitions
}

/* Merging is greedy, so it can stop at a set of partition points where no
* single merge is profitable even though merging a longer run of partitions
* would be. This runs the exact dynamic program over the partitions produced by
* the merge phase, treating each of them as indivisible, which finds the
* cheapest way to merge runs of them. There are far fewer partitions than
* records at this point, so the quadratic cost is not a concern.
*
* `atoms` holds the first record of each partition; the return value is a
* subsequence of it. */
fn merge_runs_of_partitions(atoms: &[usize], len: usize, prefix: &Prefix) -> Vec<usize> {
    /* best[i] is the cost of encoding atoms[..=i], and predecessor[i] is the
     * first atom of the last partition in the cheapest such encoding. */
    let end_of = |i: usize| atoms.get(i + 1).copied().unwrap_or(len);
    let mut best = Vec::with_capacity(atoms.len());
    let mut predecessor = Vec::with_capacity(atoms.len());
    for i in 0..atoms.len() {
        let mut best_cost = u64::MAX;
        let mut best_start = 0;
        for j in (0..=i).rev() {
            let cost = prefix.cost(atoms[j], end_of(i)) + if j > 0 { best[j - 1] } else { 0 };
            if cost < best_cost {
                best_cost = cost;
                best_start = j;
            }
        }
        best.push(best_cost);
        predecessor.push(best_start);
    }

    let mut points = vec![];
    let mut atom = predecessor[atoms.len() - 1];
    while atom != 0 {
        points.push(atoms[atom]);
        atom = predecessor[atom - 1];
    }
    points.reverse();

    points
}

/* Improve a set of partition points by (1) dropping any point that no longer
* pays for itself, and (2) moving each point to the cheapest position between
* its neighbors. Each pass visits every record a constant number of times. */
fn refine_partition_points(mut points: Vec<usize>, len: usize, prefix: &Prefix) -> Vec<usize> {
    for _ in 0..REFINEMENT_PASSES {
        let mut changed = false;

        let mut i = 0;
        while i < points.len() {
            let start = if i > 0 { points[i - 1] } else { 0 };
            let end = points.get(i + 1).copied().unwrap_or(len);
            if prefix.cost(start, end)
                <= prefix.cost(start, points[i]) + prefix.cost(points[i], end)
            {
                points.remove(i);
                changed = true;
            } else {
                i += 1;
            }
        }

        for i in 0..points.len() {
            let start = if i > 0 { points[i - 1] } else { 0 };
            let end = points.get(i + 1).copied().unwrap_or(len);
            let best = (start + 1..end)
                .min_by_key(|&mid| prefix.cost(start, mid) + prefix.cost(mid, end))
                .unwrap_or(points[i]);
            if best != points[i] {
                points[i] = best;
                changed = true;
            }
        }

        if !changed {
            break;
        }
    }

    points
}

/* S: the set of revoked certificates we want to encode
*  Universe: all certificates in the range [timestamp, timestamp] where the time
*  stamp is the issued time of certificate.
*
* Returns the notAfter timestamps at which a new partition starts, along with
* the approximate size, in bits, of the resulting filter.
*
* The partition is chosen by merging adjacent records bottom-up, repairing the
* local minima that greedy merging can get stuck in, and then adjusting the
* partition points locally. This is a heuristic, but it matches the partition
* found by an exact dynamic program on the CRLite data we have looked at, and
* it stays within a few hundredths of a percent of it on synthetic data. It
* runs in O(records * log(records)) time, where the exact dynamic program takes
* O(records^2). */
pub fn partition_metadata(records: Vec<PartitionRecord>) -> (Vec<u64>, u64) {
    if records.is_empty() {
        return (Vec::new(), 0);
    }

    let prefix = Prefix::new(&records);
    let partitions = merge_partitions(&records, &prefix);
    let points = merge_runs_of_partitions(&partitions.starts(), records.len(), &prefix);
    let points = refine_partition_points(points, records.len(), &prefix);

    let mut approx_size = 0;
    let mut start = 0;
    for &end in points.iter().chain(std::iter::once(&records.len())) {
        approx_size += prefix.cost(start, end);
        start = end;
    }

    (
        points.into_iter().map(|i| records[i].time).collect(),
        approx_size,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    /* Exact O(records^2) dynamic program, used as a reference for the
     * heuristic in partition_metadata(). */
    fn partition_metadata_exact(records: &[PartitionRecord]) -> (Vec<u64>, u64) {
        let len = records.len();
        if records.is_empty() {
            return (Vec::new(), 0);
        }
        let mut dp = vec![(0, 0); len];

        dp[0] = (cost(records[0].r, records[0].n), 0);
        for i in 1..len {
            dp[i] = (u64::MAX, 0);
            let mut r = 0;
            let mut n = 0;
            for j in (0..=i).rev() {
                r += records[j].r;
                n += records[j].n;
                let new_cost = if j > 0 {
                    cost(r, n) + dp[j - 1].0
                } else {
                    cost(r, n)
                };
                if new_cost < dp[i].0 {
                    dp[i] = (new_cost, j);
                }
            }
        }

        let mut partition_meta = Vec::<u64>::new();
        let mut left_partition_point = dp[len - 1].1;
        while left_partition_point != 0 {
            partition_meta.push(records[left_partition_point].time);
            left_partition_point = dp[left_partition_point - 1].1;
        }
        partition_meta.reverse();

        (partition_meta, dp[len - 1].0)
    }

    /* A deterministic xorshift generator, so that the tests below do not need
     * a dependency on rand. */
    struct Rng(u64);

    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }

        fn below(&mut self, bound: u64) -> u64 {
            self.next() % bound
        }
    }

    /* Records with `len` hourly buckets, each holding roughly `n` certificates,
     * of which a fraction given by `densities` is revoked. The densities are
     * applied to equal-length runs of buckets. */
    fn records(len: usize, n: u64, densities: &[f64], seed: u64) -> Vec<PartitionRecord> {
        let mut rng = Rng(seed);
        let mut records = Vec::with_capacity(len);
        for i in 0..len {
            let density = densities[i * densities.len() / len];
            let n = n / 2 + rng.below(n);
            let expected = density * n as f64;
            /* Jitter the revocation count by up to one standard deviation. */
            let jitter = expected.sqrt() * (rng.below(200) as f64 / 100.0 - 1.0);
            let r = (expected + jitter).max(0.0).round() as u64;
            records.push(PartitionRecord::new(
                1729926000 + 3600 * i as u64,
                n,
                r.min(n),
            ));
        }
        records
    }

    fn total_cost(records: &[PartitionRecord], points: &[u64]) -> u64 {
        let prefix = Prefix::new(records);
        let mut starts: Vec<usize> = vec![0];
        starts.extend(points.iter().map(|&time| {
            records
                .iter()
                .position(|record| record.time == time)
                .expect("partition point is not a record timestamp")
        }));
        starts
            .iter()
            .zip(starts[1..].iter().chain(std::iter::once(&records.len())))
            .map(|(&start, &end)| prefix.cost(start, end))
            .sum()
    }

    fn assert_near_optimal(records: Vec<PartitionRecord>, tolerance: f64, label: &str) {
        let (optimal_points, optimal) = partition_metadata_exact(&records);
        let (points, approx_size) = partition_metadata(records.clone());

        assert!(points.is_sorted());
        assert!(points.len() <= MAX_PARTITION_POINTS);
        assert_eq!(approx_size, total_cost(&records, &points));
        assert!(
            approx_size as f64 <= optimal as f64 * (1.0 + tolerance),
            "{label}: heuristic cost {approx_size} ({} partitions) exceeds optimal cost \
             {optimal} ({} partitions) by more than {:.2}%",
            points.len() + 1,
            optimal_points.len() + 1,
            100.0 * tolerance,
        );
    }

    #[test]
    fn test_partition_metadata_empty() {
        assert_eq!(partition_metadata(vec![]), (Vec::new(), 0));
    }

    #[test]
    fn test_partition_metadata_single_record() {
        let records = vec![PartitionRecord::new(1729926000, 1000, 10)];
        assert_eq!(partition_metadata(records), (Vec::new(), cost(10, 1000)));
    }

    #[test]
    fn test_partition_metadata_no_revocations() {
        /* Nothing to encode, so one partition is enough. */
        let records = records(2160, 50000, &[0.0], 1);
        assert_eq!(partition_metadata(records), (Vec::new(), META_SIZE));
    }

    #[test]
    fn test_partition_metadata_uniform_density() {
        /* No density variation to exploit, so one partition is enough. */
        let (points, _) = partition_metadata(records(2160, 50000, &[1e-4], 2));
        assert_eq!(points, Vec::<u64>::new());
    }

    #[test]
    fn test_partition_metadata_splits_dense_run() {
        /* A run of mass revocations should be partitioned off from its
         * neighbors. */
        let records = records(300, 50000, &[1e-6, 1e-6, 1e-6, 5e-2, 1e-6, 1e-6], 3);
        let (points, approx_size) = partition_metadata(records.clone());

        assert_eq!(points, vec![records[150].time, records[200].time]);
        /* Confining the mass revocations to their own partition lets the rest
         * of the universe be encoded at a much lower density. */
        let unpartitioned = total_cost(&records, &[]);
        assert!(
            approx_size < 4 * unpartitioned / 5,
            "partitioning saved only {} of {unpartitioned} bits",
            unpartitioned - approx_size
        );
    }

    #[test]
    fn test_partition_metadata_respects_partition_limit() {
        /* A partition index has to fit in a byte, so we cannot emit more than
         * MAX_PARTITION_POINTS partition points no matter how much the
         * revocation density varies. */
        let mut rng = Rng(9);
        let densities: Vec<f64> = (0..3000)
            .map(|_| 10f64.powf(-7.0 + 6.5 * rng.below(1000) as f64 / 1000.0))
            .collect();
        let records = records(3000, 50000, &densities, 10);

        let (points, approx_size) = partition_metadata(records.clone());

        assert_eq!(points.len(), MAX_PARTITION_POINTS);
        assert!(approx_size < total_cost(&records, &[]));
    }

    #[test]
    fn test_partition_metadata_is_near_optimal() {
        /* Densities that vary smoothly are the hardest case for the
         * heuristic, since the choice of partition points is least obvious. */
        let smooth: Vec<f64> = (0..40).map(|i| 1e-6 * 1.2f64.powi(i)).collect();
        let cases: Vec<(&str, Vec<PartitionRecord>)> = vec![
            ("two densities", records(2160, 50000, &[1e-3, 1e-6], 4)),
            (
                "five densities",
                records(2160, 50000, &[1e-3, 1e-5, 3e-4, 1e-6, 2e-3], 5),
            ),
            ("brief spike", records(2160, 50000, &[1e-5, 1e-1, 1e-5], 6)),
            ("smooth ramp", records(2160, 50000, &smooth, 7)),
            ("small universe", records(2160, 100, &smooth, 8)),
        ];
        for (label, records) in cases {
            assert_near_optimal(records, 0.005, label);
        }
    }
}
