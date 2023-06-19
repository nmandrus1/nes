use log::{debug, error, info, trace, warn};

#[repr(u8)]
enum StatusFlag {
    Carry = 0,
    Zero = 1,
    InterruptDisable = 2,
    Decimal = 3,
    Overflow = 6,
    Negative = 7,
}

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

    fn flag_status(&self, flag: StatusFlag) -> bool {
        (self.status >> flag as u8) & 1 == 1
    }

    fn flag_set(&mut self, flag: StatusFlag) {
        self.status |= 1 << flag as u8;
    }

    fn flag_clear(&mut self, flag: StatusFlag) {
        self.status &= !(1 << flag as u8)
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

    /// Add operand to Accumulator
    ///
    /// Flags Affected:
    ///     Carry
    ///     Overflow
    ///     Negative
    ///     Zero
    fn adc(&mut self, operand: u8) {
        // A + M + C
        let result =
            self.acc as u16 + operand as u16 + u16::from(self.flag_status(StatusFlag::Carry));

        // store the lowest 8 bits of the result in A
        self.acc = result as u8;

        // determine carry flag status
        if result > 0xFF {
            self.flag_set(StatusFlag::Carry);
        } else {
            self.flag_clear(StatusFlag::Carry);
        }

        // determine overflow flag status
        let overflow_happened = ()
        if (!(self.acc ^ operand) as u16 & (self.acc as u16 ^ result) & 0x80) != 0 {
            self.flag_set(StatusFlag::Overflow);
        } else {
            self.flag_clear(StatusFlag::Overflow);
        }

        // determine negative flag status
        if result & 0x80 != 0 {
            self.flag_set(StatusFlag::Negative);
        } else {
            // clear negative flag
            self.flag_clear(StatusFlag::Negative);
        }
    }
}

enum Instruction {
    ADC(AddressingMode),
    AND(AddressingMode),
    ASL(AddressingMode),
    BCC(AddressingMode),
    BCS(AddressingMode),
    BEQ(AddressingMode),
    BIT(AddressingMode),
    BMI(AddressingMode),
    BNE(AddressingMode),
    BPL(AddressingMode),
    BRK,
    BVC(AddressingMode),
    BVS(AddressingMode),
    CLC,
    CLD,
    CLI,
    CLV,
    CMP(AddressingMode),
    CPX(AddressingMode),
    CPY(AddressingMode),
    DEC(AddressingMode),
    DEX,
    DEY,
    EOR(AddressingMode),
    INC(AddressingMode),
    INX,
    INY,
    JMP(AddressingMode),
    JSR(AddressingMode),
    LDA(AddressingMode),
    LDX(AddressingMode),
    LDY(AddressingMode),
    LSR(AddressingMode),
    NOP,
    ORA(AddressingMode),
    PHA,
    PHP,
    PLA,
    PLP,
    ROL(AddressingMode),
    ROR(AddressingMode),
    RTI,
    RTS,
    SBC(AddressingMode),
    SEC,
    SED,
    SEI,
    STA(AddressingMode),
    STX(AddressingMode),
    STY(AddressingMode),
    TAX,
    TAY,
    TSX,
    TXA,
    TXS,
    TYA,
}

pub enum AddressingMode {
    Accumulator,
    Immediate(u8),
    ZeroPage(u8),
    ZeroPageX(u8),
    ZeroPageY(u8),
    Absolute(u16),
    AbsoluteX(u16),
    AbsoluteY(u16),
    IndirectX(u8),
    IndirectY(u8),
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_flag_status() {
        let mut cpu = CPU::default();

        // Set Overflow and Negative flags
        cpu.status = 0b1100_0000;

        assert_eq!(cpu.flag_status(StatusFlag::Overflow), true);
        assert_eq!(cpu.flag_status(StatusFlag::Negative), true);
        assert_eq!(cpu.flag_status(StatusFlag::Carry), false);
        assert_eq!(cpu.flag_status(StatusFlag::Zero), false);
    }

    #[test]
    fn test_flag_set() {
        let mut cpu = CPU::default();

        cpu.flag_set(StatusFlag::Carry);
        cpu.flag_set(StatusFlag::Zero);

        assert_eq!(cpu.flag_status(StatusFlag::Carry), true);
        assert_eq!(cpu.flag_status(StatusFlag::Zero), true);
        assert_eq!(cpu.flag_status(StatusFlag::Overflow), false);
        assert_eq!(cpu.flag_status(StatusFlag::Negative), false);
    }

    #[test]
    fn test_flag_clear() {
        let mut cpu = CPU::default();

        // Set all flags
        cpu.status = 0b1111_1111;

        cpu.flag_clear(StatusFlag::Overflow);
        cpu.flag_clear(StatusFlag::Negative);

        assert_eq!(cpu.flag_status(StatusFlag::Overflow), false);
        assert_eq!(cpu.flag_status(StatusFlag::Negative), false);
        assert_eq!(cpu.flag_status(StatusFlag::Carry), true);
        assert_eq!(cpu.flag_status(StatusFlag::Zero), true);
    }
}
