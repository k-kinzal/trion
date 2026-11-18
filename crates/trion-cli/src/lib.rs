//! The library behind the `trion` command.
//!
//! [`run`] is the command: it converts a package into its MMT form, with
//! the contracts and the proof obligations of the package, and into its
//! documents. It proves nothing; `trioc prove` proves the obligations of the
//! MMT form. The project loader is that of `trioc`.

#![warn(unreachable_pub)]

mod checks;
mod command;
mod convert;
mod doc;
mod figure;
mod markdown;

pub use command::run;
pub use convert::{findings, Findings};
pub use trioc_cli::project;
pub(crate) use trioc_cli::sources;
