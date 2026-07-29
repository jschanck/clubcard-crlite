/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

/* This module takes the inputs <revoked_dir> and <known_dir> that a filter is
* built from, and chooses how to partition each issuer's certificates by
* notAfter date. The result is a PartitionIndex, which a builder consults to
* find the block that a certificate belongs to, and which is shipped in the
* filter so that queries can do the same. */

use crate::partition_metadata::{Partition, PartitionRecord, partition_metadata};
use base64::Engine;
use clubcard::ApproximateSizeOf;
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::ffi::OsString;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::path::{Path, PathBuf};

type IssuerSPKIHash = [u8; 32];
#[derive(Default, Serialize, Deserialize)]
pub struct PartitionIndex(pub HashMap<IssuerSPKIHash, Partition>);

impl From<()> for PartitionIndex {
    fn from(_: ()) -> Self {
        Default::default()
    }
}

impl PartitionIndex {
    /// Find the partition index associated with given issuer, returns None if issuer
    /// is not valid.
    ///
    /// * `issuer`: SHA256 issuer hash
    /// * `not_after`: expiry date of certificate
    pub fn partition_index(&self, issuer: &[u8; 32], not_after: u64) -> Option<usize> {
        let partition = self.0.get(issuer)?;

        // should be equivalent to upper_bound in C++
        Some(
            partition
                .binary_search_by(|&some_not_after| {
                    if some_not_after > not_after {
                        std::cmp::Ordering::Greater
                    } else {
                        std::cmp::Ordering::Less
                    }
                })
                .unwrap_or_else(|idx| idx),
        )
    }
}

impl ApproximateSizeOf for PartitionIndex {
    fn approximate_size_of(&self) -> usize {
        size_of::<Self>()
    }
}

const REASON_UNSPECIFIED: u8 = 0;
const REASON_KEY_COMPROMISE: u8 = 1;
const REASON_CA_COMPROMISE: u8 = 2;
const REASON_AFFILIATION_CHANGED: u8 = 3;
const REASON_SUPERSEDED: u8 = 4;
const REASON_CESSATION_OF_OPERATION: u8 = 5;
const REASON_CERTIFICATE_HOLD: u8 = 6;
//              -- value 7 is not used
const REASON_REMOVE_FROM_CRL: u8 = 8;
const REASON_PRIVILEGE_WITHDRAWN: u8 = 9;
const REASON_AA_COMPROMISE: u8 = 10;

#[derive(clap::ValueEnum, Copy, Clone)]
pub enum ReasonSet {
    All,
    Specified,
    Priority,
}

impl ReasonSet {
    /// Whether a filter for this reason set encodes revocations with this reason.
    fn includes(&self, reason: Reason) -> bool {
        match self {
            ReasonSet::All => true,
            ReasonSet::Specified => reason != Reason::Unspecified,
            ReasonSet::Priority => matches!(
                reason,
                Reason::KeyCompromise | Reason::CessationOfOperation | Reason::PrivilegeWithdrawn
            ),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
enum Reason {
    Unspecified = REASON_UNSPECIFIED,
    KeyCompromise = REASON_KEY_COMPROMISE,
    CACompromise = REASON_CA_COMPROMISE,
    AffilitationChanged = REASON_AFFILIATION_CHANGED,
    Superseded = REASON_SUPERSEDED,
    CessationOfOperation = REASON_CESSATION_OF_OPERATION,
    CertificateHold = REASON_CERTIFICATE_HOLD,
    RemoveFromCRL = REASON_REMOVE_FROM_CRL,
    PrivilegeWithdrawn = REASON_PRIVILEGE_WITHDRAWN,
    AACompromise = REASON_AA_COMPROMISE,
}

impl From<u8> for Reason {
    fn from(reason_code: u8) -> Reason {
        match reason_code {
            REASON_UNSPECIFIED => Reason::Unspecified,
            REASON_KEY_COMPROMISE => Reason::KeyCompromise,
            REASON_CA_COMPROMISE => Reason::CACompromise,
            REASON_AFFILIATION_CHANGED => Reason::AffilitationChanged,
            REASON_SUPERSEDED => Reason::Superseded,
            REASON_CESSATION_OF_OPERATION => Reason::CessationOfOperation,
            REASON_CERTIFICATE_HOLD => Reason::CertificateHold,
            REASON_REMOVE_FROM_CRL => Reason::RemoveFromCRL,
            REASON_PRIVILEGE_WITHDRAWN => Reason::PrivilegeWithdrawn,
            REASON_AA_COMPROMISE => Reason::AACompromise,
            _ => Reason::Unspecified,
        }
    }
}

fn decode_reason(hex_reason: &[u8]) -> Reason {
    let hex_reason = std::str::from_utf8(hex_reason).expect("invalid hex encoding: not ascii");
    u8::from_str_radix(hex_reason, 16)
        .expect("invalid hex encoding")
        .into()
}

fn decode_issuer(s: &str) -> [u8; 32] {
    base64::prelude::BASE64_URL_SAFE
        .decode(s)
        .expect("found invalid issuer id: not url-safe base64.")
        .try_into()
        .expect("found invalid issuer id: not 32 bytes.")
}

/// Read the lines of a file, without their line terminators, into `handle`.
fn for_each_line(path: &Path, mut handle: impl FnMut(&[u8])) {
    let mut reader = BufReader::with_capacity(1 << 22, File::open(path).expect("cannot open file"));
    let mut line = Vec::new();
    while reader.read_until(b'\n', &mut line).expect("IO error") > 0 {
        while let Some(b'\n' | b'\r') = line.last() {
            line.pop();
        }
        if !line.is_empty() {
            handle(&line);
        }
        line.clear();
    }
}

/// The serial numbers in `revoked_file` that a filter for `reason_set` encodes.
///
/// Serial numbers are kept in the ascii hex encoding used by the input files,
/// as that is how a builder matches them against the known file.
///
/// * `revoked_file`: list of certificates revoked by an issuer, each line contains an ascii
///   hex encoded serial number prefixed by an ascii hex encoded revocation reason code. The
///   reason codes are one byte.
fn read_revoked_serials(revoked_file: &Path, reason_set: ReasonSet) -> HashSet<Vec<u8>> {
    let mut serials = HashSet::new();
    for_each_line(revoked_file, |line| {
        let (reason, serial) = line.split_at(2);
        if reason_set.includes(decode_reason(reason)) {
            serials.insert(serial.to_vec());
        }
    });
    serials
}

/// Count the certificates issued by an issuer, and the revoked ones among them,
/// per notAfter date.
///
/// The counts match the ones a builder arrives at: a certificate contributes to
/// the universe once per appearance in the known file, and a revoked
/// certificate is counted once, at its first appearance.
///
/// * `known_file`: list of certificates issued by an issuer, each line contains
///     1. an ascii hex encoded 64 bit unix timestamp prefixed by "@", or
///     2. an ascii hex encoded certificate serial number.
/// * `revoked_serials`: the serial numbers to count as revoked. Emptied as they are counted.
fn count_by_not_after(
    known_file: &Path,
    revoked_serials: &mut HashSet<Vec<u8>>,
) -> Vec<PartitionRecord> {
    let mut counts = BTreeMap::<u64, (u64, u64)>::new();
    /* Counts for the timestamp we are reading, flushed into `counts` when the
     * next timestamp appears. */
    let mut not_after = 0;
    let mut n = 0;
    let mut r = 0;
    for_each_line(known_file, |line| {
        if let [b'@', timestamp @ ..] = line {
            let entry = counts.entry(not_after).or_default();
            entry.0 += n;
            entry.1 += r;
            (n, r) = (0, 0);
            let timestamp = std::str::from_utf8(timestamp).expect("malformed date: not ascii");
            not_after = u64::from_str_radix(timestamp, 16).expect("malformed date");
        } else {
            n += 1;
            if !revoked_serials.is_empty() && revoked_serials.remove(line) {
                r += 1;
            }
        }
    });
    let entry = counts.entry(not_after).or_default();
    entry.0 += n;
    entry.1 += r;

    counts
        .into_iter()
        .filter(|(_, (n, _))| *n > 0)
        .map(|(not_after, (n, r))| PartitionRecord::new(not_after, n, r))
        .collect()
}

pub struct PartitionBuilder {
    revoked_dir: PathBuf,
    known_dir: PathBuf,
    reason_set: ReasonSet,
}

impl PartitionBuilder {
    /// * `revoked_dir`, `known_dir`: the inputs the filter will be built from.
    /// * `reason_set`: the revocation reasons the filter will encode. Revocations
    ///   that the filter will not encode must not influence the partition.
    pub fn new(revoked_dir: &Path, known_dir: &Path, reason_set: ReasonSet) -> Self {
        Self {
            revoked_dir: revoked_dir.to_path_buf(),
            known_dir: known_dir.to_path_buf(),
            reason_set,
        }
    }

    pub fn list_issuer_file_pairs(&self) -> Vec<(OsString, Option<PathBuf>, PathBuf)> {
        let known_files = Path::read_dir(&self.known_dir).unwrap();
        let known_issuers: Vec<OsString> = known_files
            .filter_map(|x| x.ok())
            .map(|x| x.file_name())
            .collect();

        let mut pairs = vec![];
        for issuer in known_issuers {
            let k_file = self.known_dir.join(&issuer);
            let r_file = self.revoked_dir.join(&issuer);
            if r_file.exists() {
                pairs.push((issuer, Some(r_file), k_file));
            } else {
                pairs.push((issuer, None, k_file));
            }
        }

        pairs
    }

    /// Partition the universe consisting of all certificates of an issuer based on
    /// notAfter timestamps.
    ///
    /// Returns the notAfter timestamps at which a new partition starts, which is
    /// empty if the issuer is best encoded in a single partition, along with the
    /// approximate size in bits of the blocks that the issuer contributes to the
    /// filter.
    fn partition_issuer(
        &self,
        maybe_revoked_file: &Option<PathBuf>,
        known_file: &Path,
    ) -> (Partition, u64) {
        /* With nothing to encode there is nothing to gain by partitioning, so
         * we can skip the known file altogether. */
        let Some(revoked_file) = maybe_revoked_file else {
            return (Partition::new(), 0);
        };

        let mut revoked_serials = read_revoked_serials(revoked_file, self.reason_set);
        let records = count_by_not_after(known_file, &mut revoked_serials);

        partition_metadata(records)
    }

    /// Choose a partition for each issuer in the known directory.
    pub fn build(self) -> PartitionIndex {
        let pairs = self.list_issuer_file_pairs();

        let partitions: Vec<(&OsString, Partition, u64)> = pairs
            .par_iter()
            .map(|(issuer, maybe_revoked_file, known_file)| {
                let (partition, approx_size) =
                    self.partition_issuer(maybe_revoked_file, known_file);
                (issuer, partition, approx_size)
            })
            .collect();

        let mut index = PartitionIndex::default();
        let mut total_approx_size = 0;
        for (issuer, partition, approx_size) in partitions {
            total_approx_size += approx_size;
            /* Issuers in a single partition are left out of the index. A
             * builder and a query both take the absence of an issuer to mean
             * that its block is identified by the issuer alone. */
            if !partition.is_empty() {
                index
                    .0
                    .insert(decode_issuer(issuer.to_str().unwrap()), partition);
            }
        }

        println!(
            "Approximate size of the partitioned filter is {} bytes",
            total_approx_size / 8
        );
        index
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;

    #[test]
    fn test_partition_index() {
        let issuer = [0u8; 32];
        let partition = vec![1, 10, 50, 200, 1000, 2000];
        let mut partition_index = PartitionIndex::default();
        partition_index.0.insert(issuer, partition);

        assert_eq!(partition_index.partition_index(&issuer, 200).unwrap(), 4);
        assert_eq!(partition_index.partition_index(&issuer, 199).unwrap(), 3);
        assert_eq!(partition_index.partition_index(&issuer, 0).unwrap(), 0);
        assert_eq!(partition_index.partition_index(&issuer, 1).unwrap(), 1);
        assert_eq!(partition_index.partition_index(&issuer, 1000).unwrap(), 5);
        assert_eq!(partition_index.partition_index(&issuer, 1999).unwrap(), 5);
        assert_eq!(partition_index.partition_index(&issuer, 2000).unwrap(), 6);
        assert_eq!(partition_index.partition_index(&issuer, 3000).unwrap(), 6);
    }

    /// A revoked and a known directory holding one issuer, in a temporary
    /// directory that is removed when the Input is dropped.
    struct Input {
        dir: PathBuf,
        issuer: [u8; 32],
    }

    impl Input {
        /// Writes `revoked` as an issuer's revoked file, and `hours` as its
        /// known file, where each entry of `hours` gives the serial numbers
        /// with notAfter in one hour.
        fn new(name: &str, revoked: &[(u8, u64)], hours: &[Vec<u64>]) -> Self {
            let dir = std::env::temp_dir().join(format!("clubcard-crlite-{name}"));
            let _ = std::fs::remove_dir_all(&dir);
            std::fs::create_dir_all(dir.join("revoked")).unwrap();
            std::fs::create_dir_all(dir.join("known")).unwrap();

            let issuer = [7u8; 32];
            let name = base64::prelude::BASE64_URL_SAFE.encode(issuer);

            let mut revoked_file = File::create(dir.join("revoked").join(&name)).unwrap();
            for (reason, serial) in revoked {
                writeln!(revoked_file, "{reason:02x}{serial:016x}").unwrap();
            }

            let mut known_file = File::create(dir.join("known").join(&name)).unwrap();
            for (hour, serials) in hours.iter().enumerate() {
                writeln!(known_file, "@{:016x}", Self::not_after(hour)).unwrap();
                for serial in serials {
                    writeln!(known_file, "{serial:016x}").unwrap();
                }
            }

            Input { dir, issuer }
        }

        fn not_after(hour: usize) -> u64 {
            1729926000 + 3600 * hour as u64
        }

        fn build(&self, reason_set: ReasonSet) -> PartitionIndex {
            PartitionBuilder::new(
                &self.dir.join("revoked"),
                &self.dir.join("known"),
                reason_set,
            )
            .build()
        }
    }

    impl Drop for Input {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.dir);
        }
    }

    /// Serial numbers for `n` certificates with notAfter in the given hour, of
    /// which the first `r` are revoked.
    fn hour(hour: u64, n: u64, r: u64) -> (Vec<u64>, Vec<(u8, u64)>) {
        let serials: Vec<u64> = (0..n).map(|i| (hour << 32) + i).collect();
        let revoked = serials[..r as usize]
            .iter()
            .map(|serial| (REASON_SUPERSEDED, *serial))
            .collect();
        (serials, revoked)
    }

    #[test]
    fn test_build_partitions_dense_hours() {
        /* Revocations in the last quarter of the issuer's notAfter range, at a
         * density that is worth separating from the rest. */
        let (mut known, mut revoked) = (vec![], vec![]);
        for h in 0..40u64 {
            let (serials, mut revocations) = hour(h, 1000, if h >= 30 { 200 } else { 0 });
            known.push(serials);
            revoked.append(&mut revocations);
        }
        let input = Input::new("dense-hours", &revoked, &known);

        let index = input.build(ReasonSet::All);

        assert_eq!(index.0.len(), 1);
        assert_eq!(index.0[&input.issuer], vec![Input::not_after(30)]);
        /* The hour at the partition point belongs to the second partition. */
        assert_eq!(
            index.partition_index(&input.issuer, Input::not_after(29)),
            Some(0)
        );
        assert_eq!(
            index.partition_index(&input.issuer, Input::not_after(30)),
            Some(1)
        );
    }

    #[test]
    fn test_build_leaves_uniform_issuer_unpartitioned() {
        let (mut known, mut revoked) = (vec![], vec![]);
        for h in 0..40u64 {
            let (serials, mut revocations) = hour(h, 1000, 20);
            known.push(serials);
            revoked.append(&mut revocations);
        }
        let input = Input::new("uniform", &revoked, &known);

        assert!(input.build(ReasonSet::All).0.is_empty());
    }

    #[test]
    fn test_build_ignores_issuer_with_no_revoked_file() {
        let input = Input::new("no-revocations", &[], &[vec![1, 2, 3]]);
        std::fs::remove_file(
            input
                .dir
                .join("revoked")
                .join(base64::prelude::BASE64_URL_SAFE.encode(input.issuer)),
        )
        .unwrap();

        assert!(input.build(ReasonSet::All).0.is_empty());
    }

    #[test]
    fn test_build_counts_only_revocations_in_the_reason_set() {
        /* The dense hours are only dense if superseded revocations count. */
        let (mut known, mut revoked) = (vec![], vec![]);
        for h in 0..40u64 {
            let (serials, mut revocations) = hour(h, 1000, if h >= 30 { 200 } else { 0 });
            known.push(serials);
            revoked.append(&mut revocations);
        }
        let input = Input::new("reason-set", &revoked, &known);

        assert_eq!(input.build(ReasonSet::All).0.len(), 1);
        /* ReasonSet::Priority excludes REASON_SUPERSEDED, so there is nothing
         * left to partition around. */
        assert!(input.build(ReasonSet::Priority).0.is_empty());
    }

    #[test]
    fn test_build_counts_revoked_serials_once() {
        /* A serial number listed in two hours contributes to the universe
         * twice, but is only counted as revoked in the first of them, which is
         * how a builder counts it. */
        let mut revoked = vec![];
        let mut known = vec![];
        for h in 0..40u64 {
            let (serials, mut revocations) = hour(h, 1000, if h >= 30 { 200 } else { 0 });
            known.push(serials);
            revoked.append(&mut revocations);
        }
        /* Repeat the dense hours' serials in an hour that would otherwise be
         * sparse. If they were counted again there, the partition would move. */
        let repeated = known[35].clone();
        known[10].extend(repeated);
        let input = Input::new("repeated-serials", &revoked, &known);

        let index = input.build(ReasonSet::All);

        assert_eq!(index.0[&input.issuer], vec![Input::not_after(30)]);
    }
}
