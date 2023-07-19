use std::fs;

use anyhow;
use log::{debug, error, info, trace, warn};

use nes_lib::NES;

const USAGE: &str = "nes <ROM> <START ADDR>";

fn main() -> anyhow::Result<()> {
    env_logger::init();
    debug!("NES Emulator starting");

    let args = std::env::args().collect::<Vec<String>>();

    if args.len() != 2 {
        eprintln!("Error with arguments\n");
        println!("{USAGE}")
    }

    let rom = std::fs::read(std::path::Path::new(&args[1]))?;
    let start = args[2].parse::<u16>()?;

    let mut nes = NES::default();
    nes.load_rom(&rom, start)?;
    nes.start();

    Ok(())
}
