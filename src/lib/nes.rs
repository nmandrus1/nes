use super::CPU;

#[derive(Default)]
pub struct NES {
    cpu: CPU,
}

impl NES {
    /// Try to load memory into RAM, start is the memory address of the start of the program
    pub fn load_rom(&mut self, rom: &[u8], start: u16) -> anyhow::Result<()> {
        if rom.len() - 1 > self.cpu.mem.len() {
            anyhow::bail!("ROM doesn't fit into RAM");
        }

        // load the ROM into memory
        self.cpu.mem[0..rom.len() - 1].copy_from_slice(&rom[0..rom.len() - 1]);
        self.cpu.pc = start;
        Ok(())
    }

    pub fn start(&mut self) {
        self.cpu.run()
    }
}
