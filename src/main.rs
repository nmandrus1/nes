use std::fs;

use anyhow;
use log::{debug, error, info, trace, warn};

mod cpu;

fn main() -> anyhow::Result<()> {
    env_logger::init();
    debug!("NES Emulator starting");

    let args = std::env::args().collect::<Vec<String>>();

    let rom = std::fs::read(std::path::Path::new(&args[1]))?;

    Ok(())
}
