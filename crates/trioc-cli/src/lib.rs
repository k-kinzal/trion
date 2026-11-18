//! The library behind the `trioc` command.
//!
//! [`run`] is the command: `prove` reads the MMT form that `trion` writes,
//! proves each proof obligation that it states and issues the certificates
//! of each proved one. `trioc` reads no package: what it proves is what the
//! MMT form states. The modules beside it are what the other commands of
//! trion share with this one: the project loader, the sources of the
//! statements, the digests, how a finding is written, and the MMT form.

#![warn(unreachable_pub)]

pub mod check;
mod command;
pub mod digest;
pub mod mmt;
pub mod project;
pub mod prove;
pub mod sources;

pub use command::run;
