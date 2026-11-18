//! Digests: the revision of a package is the digest of its files, so that a
//! result names the content that it is about.

use sha2::{Digest, Sha256};
use std::fs;
use std::path::PathBuf;

/// The SHA-256 digest of some bytes, in hexadecimal.
pub fn hex(bytes: impl AsRef<[u8]>) -> String {
    Sha256::digest(bytes).iter().map(|b| format!("{b:02x}")).collect()
}

/// The digest of the contents of some files, one after another. A file that
/// cannot be read counts as empty.
pub fn hash_files(files: impl Iterator<Item = PathBuf>) -> String {
    let mut all = Vec::new();
    for file in files {
        all.extend(fs::read(&file).unwrap_or_default());
    }
    hex(all)
}
