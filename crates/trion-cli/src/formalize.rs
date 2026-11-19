use clap::Args;
use std::path::PathBuf;
use trion_cnl::formalize_bytes;

#[derive(Args)]
pub(crate) struct Options {
    source: PathBuf,
    #[arg(long)]
    grammar: Option<String>,
    /// Print the canonical CNL spelling instead of the accepted artifact.
    #[arg(long)]
    canonical: bool,
}

pub(crate) fn run(args: Options) -> Result<bool, Box<dyn std::error::Error>> {
    let source = std::fs::read(args.source)?;
    match formalize_bytes(&source, args.grammar.as_deref()) {
        Ok(accepted) => {
            if args.canonical {
                print!("{}", accepted.canonical_cnl());
            } else {
                println!("{}", serde_json::to_string(&accepted)?);
            }
            Ok(true)
        }
        Err(rejected) => {
            println!("{}", serde_json::to_string(&rejected)?);
            Ok(false)
        }
    }
}
