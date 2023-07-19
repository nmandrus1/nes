use nes_lib::NES;

// This source code for this 6502 CPU test is from https://github.com/Klaus2m5/6502_65C02_functional_tests
//
// I downloaded the binary for the compiled 6502_functional_tests.a65 file from the link above
// and placed it in the /tests/res folder.

#[test]
fn functional_test() -> anyhow::Result<()> {
    env_logger::builder().is_test(true).try_init()?;

    let rom = std::fs::read(format!(
        "{}/tests/res/functional_test.bin",
        env!("CARGO_MANIFEST_DIR")
    ))?;

    println!("{}", rom.len());

    let start = 0x0400;

    let mut nes = NES::default();
    nes.load_rom(&rom, start)?;
    nes.start();

    Ok(())
}
