use anyhow;
use log::{debug, error, info, trace, warn};

mod cpu;

fn main() -> anyhow::Result<()> {
    env_logger::init();
    debug!("NES Emulator starting");

    Ok(())
}
