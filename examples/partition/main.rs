/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

/* This program takes a revoked directory path and a known directory path, then
* chooses a partition of each issuer's certificates by notAfter date and
* outputs the serialized partition metadata.
* */

use clubcard_crlite::partition::{PartitionBuilder, ReasonSet};
use std::env::{args, current_dir};
use std::fs::File;
use std::io::Write;
use std::path::PathBuf;
use std::process::ExitCode;

fn main() -> std::process::ExitCode {
    let mut args = args();
    let program_path = args.next().unwrap();

    let Some(revoked_dir) = args.next().map(PathBuf::from) else {
        eprintln!("Usage: {program_path} <revoked dir> <known dir> [reason set] [meta file]");
        eprintln!("       reason set is one of all (the default), specified, or priority");
        return ExitCode::FAILURE;
    };
    let known_dir = PathBuf::from(args.next().expect("Expect known directory path"));
    let reason_set = match args.next().as_deref() {
        None | Some("all") => ReasonSet::All,
        Some("specified") => ReasonSet::Specified,
        Some("priority") => ReasonSet::Priority,
        Some(other) => {
            eprintln!("Unknown reason set {other:?}");
            return ExitCode::FAILURE;
        }
    };
    let meta_path = if let Some(path) = args.next() {
        PathBuf::from(path)
    } else {
        current_dir()
            .expect("Expect current directory")
            .join("serialized_meta")
    };
    let mut meta_file = File::create(&meta_path).unwrap();

    let partition_builder = PartitionBuilder::new(&revoked_dir, &known_dir, reason_set);
    let partition_metadata = partition_builder.build();
    let bytes = meta_file
        .write(&bincode::serialize(&partition_metadata).unwrap())
        .unwrap();

    println!("Write {bytes} meta data to {meta_path:?}");

    ExitCode::SUCCESS
}
