use log::{debug, error, info, trace, warn};

pub struct CPU {
    /// program counter, 16 bytes
    pcounter: usize,

    /// stack pointer, can only access 256 bytes from 0x0100-0x01FF
    stack_ptr: usize,

    /// the X and Y registers
    x: u8,
    y: u8,

    /// Accumulator
    acc: u8,

    /// processor status
    // 7  bit  0
    // ---- ----
    // NVss DIZC
    // |||| ||||
    // |||| |||+- Carry
    // |||| ||+-- Zero
    // |||| |+--- Interrupt Disable
    // |||| +---- Decimal
    // ||++------ No CPU effect, see: the B flag
    // |+-------- Overflow
    // +--------- Negative
    status: u8,

    mem: [u8; 0xFFFF],
}

impl Default for CPU {
    fn default() -> Self {
        // default state of CPU after powering on
        Self {
            pcounter: 0,
            stack_ptr: 0xFD,
            x: 0,
            y: 0,
            acc: 0,
            status: 0x34,
            mem: [0; 0xFFFF],
        }
    }
}

impl CPU {
    /// Try to load memory into RAM
    pub fn load_rom(&mut self, rom: &[u8]) -> anyhow::Result<()> {
        if rom.len() > self.mem.len() {
            anyhow::bail!("ROM doesn't fit into RAM");
        }

        // load the ROM into memory
        for (i, byte) in rom.iter().enumerate() {
            self.mem[i] = *byte;
        }

        Ok(())
    }

    /// Read the opcode at the current program counter's location
    fn read_opcode(&self) -> u16 {
        let byte1 = self.mem[self.pcounter] as u16;
        let byte2 = self.mem[self.pcounter + 1] as u16;

        (byte1 << 8) | byte2
    }

    fn carry_bit(&self) -> u8 {
        self.status
    }

    pub fn run(&mut self) {
        // main loop of reading opcode and executing instruction
        loop {
            let opcode = self.read_opcode();
            info!("OPCODE: {:#06x}", opcode);

            // split up instruction and arguments
            let op = opcode >> 8;
            let arg = opcode & 0xFF;

            debug!("OP:  {:#04x}", op);
            debug!("ARG: {:#04x}", arg);

            match op {
                // Add with Carry (ADC)   // Addressing Mode
                0x69 => unimplemented!(), // Immediate
                0x65 => unimplemented!(), // Zero Page
                0x75 => unimplemented!(), // Zero Page, X
                0x6D => unimplemented!(), // Absolute
                0x7D => unimplemented!(), // Absolute, X
                0x79 => unimplemented!(), // Absolute, Y
                0x61 => unimplemented!(), // Indirect, X
                0x71 => unimplemented!(), // Indirect, Y

                _ => unreachable!(),
            }
        }
    }

    fn add_with_carry_immediate(&mut self, arg: u8) {
        // add and detect overflow
        let carry_bit = self.status & 1;
        let (result, carry) = self

        // if result overflowed set carry flag
        if carry {}
    }
}

#[cfg(test)]
mod test {

    #[test]
    fn test_adc_immediate() {}
}
