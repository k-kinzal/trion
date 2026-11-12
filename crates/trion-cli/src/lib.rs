//! The library behind the `trion` command.
//!
//! [`run`] is the command: `verify` verifies a package, `doc` writes a
//! verified package as a document, and `lsp` serves editors. The modules
//! that are public beside it are the parts that tests drive without a
//! process: the project loader and the language server.

#![warn(unreachable_pub)]

mod command;
mod digest;
mod doc;
mod figure;
pub mod lsp;
pub mod project;
mod sources;
mod verify;

pub use command::run;
