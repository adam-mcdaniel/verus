use crate::*;
use anyhow::{bail, Result};
use clap::Parser;
use tracing::*;

pub const LOGO: &str = r#"

 █████ █████  ██████  ████████  █████ ████  █████      
░░███ ░░███  ███░░███░░███░░███░░███ ░███  ███░░       
 ░███  ░███ ░███████  ░███ ░░░  ░███ ░███ ░░█████      
 ░░███ ███  ░███░░░   ░███      ░███ ░███  ░░░░███     
  ░░█████   ░░██████  █████     ░░████████ ██████      
   ░░░░░     ░░░░░░  ░░░░░       ░░░░░░░░ ░░░░░░       
"#;

#[derive(Debug, Parser)]
#[clap(author, version, about, long_about = Some(LOGO))]
struct Args {
    /// The input file to typecheck and evaluate
    input_file: Option<String>,
    args: Vec<String>,
}

pub fn cli() -> Result<()> {
    let args = Args::parse();
    init_logging("info");
    // debug!("Parsed args: {:?}", args);
    if let Some(input_file) = args.input_file {
        let input = std::fs::read_to_string(input_file)?;

        match parse(&input) {
            Ok(expr) => {
                // debug!("Parsed expression: {:#?}", expr);
                let expr = Library::stdlib().import(expr);

                if let Err(e) = check(expr.clone()) {
                    bail!("Failed to check expression: {e}");
                }

                match eval(expr.clone()) {
                    Ok(result) => {
                        info!("Result: {}", result);
                    }
                    Err(e) => {
                        bail!("Failed to evaluate expression: {e}");
                    }
                }
            }
            Err(e) => {
                bail!("Failed to parse program:\n{e}");
            }
        }
    } else {
        bail!("No input file provided");
    }
    Ok(())
}
