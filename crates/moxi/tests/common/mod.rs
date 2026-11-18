//! Shared helpers of the integration tests: locating and running the
//! reference tool.

#![allow(dead_code)]

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

pub mod generate;

/// The commit of moxi-mc-flow the differential tests were written against.
pub const MCFLOW_COMMIT: &str = "b61c98188d246e157a6f5f759b012749855b8fbc";

/// The repository root.
pub fn repository() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// The moxi-mc-flow directory: `MOXI_MC_FLOW`, else `.tools/moxi-mc-flow`.
/// Panics (failing the test that asked for it) when the directory has no
/// `src/parse_moxi.py`: the differential tests are ignored by default, so
/// one that runs was asked for and must not pass without the tool.
pub fn mcflow() -> PathBuf {
    let dir = std::env::var_os("MOXI_MC_FLOW").map(PathBuf::from).unwrap_or_else(|| repository().join(".tools/moxi-mc-flow"));
    assert!(dir.join("src/parse_moxi.py").is_file(), "moxi-mc-flow (commit {MCFLOW_COMMIT}) is not at {}; install it there or set MOXI_MC_FLOW", dir.display());
    dir
}

/// Runs the reference sort checker of moxi-mc-flow on the file `path`;
/// returns whether it accepts, and its output.
///
/// `sortcheck.py` imports a JSON validator that needs the `jsonschema`
/// package even for `.moxi` input, so the test drives the same two steps
/// `sortcheck.py` takes for a `.moxi` file — `src.parse_moxi.parse` and
/// `src.moxi.sort_check` — and prints whether both succeed without an
/// error message. Its verdict
/// therefore covers MoXI's grammar and its static semantics (sorts,
/// declarations, scoping) as moxi-mc-flow implements them. Python runs
/// isolated (`-I`); the tool's directory is the only addition to its
/// module path, and every path is passed as an argument.
pub fn sortcheck(path: &Path) -> (bool, String) {
    let driver = "import sys, pathlib\nsys.path.insert(0, sys.argv[1])\nfrom src import parse_moxi, moxi\nprogram = parse_moxi.parse(pathlib.Path(sys.argv[2]))\nprint('ACCEPT' if program is not None and moxi.sort_check(program)[0] else 'REJECT')\n";
    let output = Command::new("python3").arg("-I").arg("-c").arg(driver).arg(mcflow()).arg(path).output().expect("python3 runs");
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    // The tool's lexer reports an illegal character as an ERROR, skips it
    // and goes on; a run that reports any ERROR counts as a rejection.
    let output_text = format!("{stdout}{stderr}");
    (output.status.success() && stdout.trim_end().ends_with("ACCEPT") && !output_text.contains("ERROR"), output_text)
}

/// Runs `sortcheck` on `text`, written to a `.moxi` file in a directory of
/// its own, which is removed afterwards.
pub fn sortcheck_text(text: &str, name: &str) -> (bool, String) {
    static COUNTER: AtomicUsize = AtomicUsize::new(0);
    let dir = std::env::temp_dir().join(format!("moxi-crate-test-{}-{}", std::process::id(), COUNTER.fetch_add(1, Ordering::Relaxed)));
    std::fs::create_dir_all(&dir).expect("temp dir");
    let path = dir.join(format!("{name}.moxi"));
    std::fs::write(&path, text).expect("write temp file");
    let result = sortcheck(&path);
    std::fs::remove_dir_all(&dir).expect("remove the temp dir");
    result
}
