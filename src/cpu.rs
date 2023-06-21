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

    /// Reads the bit of the passed flag
    fn flag_status(&self, flag: StatusFlag) -> bool {
        (self.status >> flag as u8) & 1 == 1
    }

    /// Sets the bit of the passed flag
    fn flag_set(&mut self, flag: StatusFlag) {
        self.status |= 1 << flag as u8;
    }

    /// Clears the bit of the passed flag
    fn flag_clear(&mut self, flag: StatusFlag) {
        self.status &= !(1 << flag as u8)
    }

    /// Checks if the passed byte is 0 and negative and updates the relevant flags
    fn update_zero_and_negative_flags(&mut self, result: u8) {
        if result == 0 {
            self.flag_set(StatusFlag::Zero);
        } else {
            self.flag_clear(StatusFlag::Zero);
        }

        // check for negative flag
        if result & 0x80 != 0 {
            self.flag_set(StatusFlag::Negative);
        } else {
            self.flag_clear(StatusFlag::Negative);
        }
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
        let overflow_occurred = (self.acc ^ operand) & (self.acc ^ (result as u8)) & 0x80 != 0;
        if overflow_occurred {
            self.flag_set(StatusFlag::Overflow);
        } else {
            self.flag_clear(StatusFlag::Overflow);
        }

        // determine negative and zero flag status
        self.update_zero_and_negative_flags(self.acc);
    }

    /// perform a logical and bit by bit on the accumulator and the operand
    fn and(&mut self, operand: u8) {
        self.acc &= operand;

        // determine negative and zero flag status
        self.update_zero_and_negative_flags(self.acc);
    }

    /// shift the bits of the accumulator left 1 and place the MSB in the Carry bit
    fn asl(&mut self, operand: u8) {
        let msb = self.acc >> 7;

        self.acc <<= 1;

        if msb != 0 {
            self.flag_set(StatusFlag::Carry)
        } else {
            self.flag_clear(StatusFlag::Carry)
        }

        // determine negative and zero flag status
        self.update_zero_and_negative_flags(self.acc);
    }

    /// if the carry flag is clear (0)
    /// add the operand (an i8) to the program counter
    fn bcc(&mut self, operand: u8) {
        let offset = operand as i8;

        if !self.flag_status(StatusFlag::Carry) {
            self.pcounter = (self.pcounter as isize + offset as isize) as usize;
        }
    }

    /// if the carry flag is set (1)
    /// adds the operand (an i8) to the program counter
    fn bcs(&mut self, operand: u8) {
        let offset = operand as i8;

        if self.flag_status(StatusFlag::Carry) {
            self.pcounter = (self.pcounter as isize + offset as isize) as usize;
        }
    }

    /// if the zero flag is set (1)
    /// adds the operand (an i8) to the program counter
    fn beq(&mut self, operand: u8) {
        let offset = operand as i8;

        if self.flag_status(StatusFlag::Zero) {
            self.pcounter = (self.pcounter as isize + offset as isize) as usize;
        }
    }

    /// Logical AND of accumulator and operand, storing bits 6 and 7 of the result
    /// in the overflow and negative flags
    fn bit(&mut self, operand: u8) {
        let result = self.acc & operand;

        if result == 0 {
            self.flag_set(StatusFlag::Zero);
        } else {
            self.flag_clear(StatusFlag::Zero);
        }

        if (operand >> 6) & 1 == 1 {
            self.flag_set(StatusFlag::Overflow);
        } else {
            self.flag_clear(StatusFlag::Overflow);
        }

        if (operand >> 7) & 1 == 1 {
            self.flag_set(StatusFlag::Negative);
        } else {
            self.flag_clear(StatusFlag::Negative);
        }
    }

    /// if the negative flag is set (1)
    /// adds the operand (an i8) to the program counter
    fn bmi(&mut self, operand: u8) {
        let offset = operand as i8;

        if self.flag_status(StatusFlag::Negative) {
            self.pcounter = (self.pcounter as isize + offset as isize) as usize;
        }
    }

    /// if the zero flag is clear (0)
    /// adds the operand (an i8) to the program counter
    fn bne(&mut self, operand: u8) {
        let offset = operand as i8;

        if !self.flag_status(StatusFlag::Zero) {
            self.pcounter = (self.pcounter as isize + offset as isize) as usize;
        }
    }

    /// if the negative flag is clear (0)
    /// adds the operand (an i8) to the program counter
    fn bpl(&mut self, operand: u8) {
        let offset = operand as i8;

        if !self.flag_status(StatusFlag::Negative) {
            self.pcounter = (self.pcounter as isize + offset as isize) as usize;
        }
    }

    fn brk(&self, operand: u8) {
        // https://www.nesdev.org/obelisk-6502-guide/reference.html#BRK
        todo!()
    }

    /// if the overflow flag is clear (0)
    /// adds the operand (an i8) to the program counter
    fn bvc(&mut self, operand: u8) {
        let offset = operand as i8;

        if !self.flag_status(StatusFlag::Overflow) {
            self.pcounter = (self.pcounter as isize + offset as isize) as usize;
        }
    }

    /// if the overflow flag is set (1)
    /// adds the operand (an i8) to the program counter
    fn bvs(&mut self, operand: u8) {
        let offset = operand as i8;

        if self.flag_status(StatusFlag::Overflow) {
            self.pcounter = (self.pcounter as isize + offset as isize) as usize;
        }
    }

    /// Clear the carry flag to zero
    fn clc(&mut self) {
        self.flag_clear(StatusFlag::Carry);
    }

    /// Clear the Decimal flag to zero
    fn cld(&mut self) {
        self.flag_clear(StatusFlag::Decimal);
    }

    /// Clear the Interrupt Disable flag to zero
    fn cli(&mut self) {
        self.flag_clear(StatusFlag::InterruptDisable);
    }

    /// Clear the Overflow flag to zero
    fn clv(&mut self) {
        self.flag_clear(StatusFlag::Overflow);
    }

    /// Compare accumulator with operand
    fn cmp(&mut self, operand: u8) {
        let result = self.acc - operand;

        // Determine Carry flag status
        if self.acc >= operand {
            self.flag_set(StatusFlag::Carry);
        } else {
            self.flag_clear(StatusFlag::Carry);
        }

        self.update_zero_and_negative_flags(result as u8);
    }
}

enum Instruction {
    ADC(AddressingMode),
    AND(AddressingMode),
    ASL(AddressingMode),
    BCC,
    BCS,
    BEQ,
    BIT(AddressingMode),
    BMI,
    BNE,
    BPL,
    BRK,
    BVC,
    BVS,
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

    #[test]
    fn test_adc() {
        let mut cpu = CPU::default();
        cpu.acc = 5;
        cpu.adc(10);
        assert_eq!(cpu.acc, 15);
        assert_eq!(cpu.flag_status(StatusFlag::Carry), false);
        assert_eq!(cpu.flag_status(StatusFlag::Overflow), false);
        assert_eq!(cpu.flag_status(StatusFlag::Zero), false);
        assert_eq!(cpu.flag_status(StatusFlag::Negative), false);
    }

    #[test]
    fn test_and() {
        let mut cpu = CPU::default();
        cpu.acc = 0b00001111;
        cpu.and(0b11110000);
        assert_eq!(cpu.acc, 0);
        assert_eq!(cpu.flag_status(StatusFlag::Zero), true);
        assert_eq!(cpu.flag_status(StatusFlag::Negative), false);
    }

    #[test]
    fn test_asl() {
        let mut cpu = CPU::default();
        cpu.acc = 0b10001111;
        cpu.asl(cpu.acc);
        assert_eq!(cpu.acc, 0b00011110);
        assert_eq!(cpu.flag_status(StatusFlag::Carry), true);
        assert_eq!(cpu.flag_status(StatusFlag::Zero), false);
        assert_eq!(cpu.flag_status(StatusFlag::Negative), false);
    }

    #[test]
    fn test_bcc_with_carry_clear() {
        let mut cpu = CPU::default();
        cpu.pcounter = 10;
        cpu.flag_clear(StatusFlag::Carry);
        cpu.bcc(5);
        assert_eq!(cpu.pcounter, 15);
    }

    #[test]
    fn test_bcc_with_carry_set() {
        let mut cpu = CPU::default();
        cpu.pcounter = 10;
        cpu.flag_set(StatusFlag::Carry);
        cpu.bcc(5);
        assert_eq!(cpu.pcounter, 10);
    }

    #[test]
    fn test_bcs_carry_set() {
        let mut cpu = CPU::default();
        cpu.pcounter = 10;
        cpu.flag_set(StatusFlag::Carry);
        cpu.bcs(5);
        assert_eq!(cpu.pcounter, 15);
    }

    #[test]
    fn test_bcs_carry_clear() {
        let mut cpu = CPU::default();
        cpu.pcounter = 10;
        cpu.flag_clear(StatusFlag::Carry);
        cpu.bcs(5);
        assert_eq!(cpu.pcounter, 10);
    }

    #[test]
    fn test_beq_zero_set() {
        let mut cpu = CPU::default();
        cpu.pcounter = 10;
        cpu.flag_set(StatusFlag::Zero);
        cpu.beq(5);
        assert_eq!(cpu.pcounter, 15);
    }

    #[test]
    fn test_beq_zero_clear() {
        let mut cpu = CPU::default();
        cpu.pcounter = 10;
        cpu.flag_clear(StatusFlag::Zero);
        cpu.beq(5);
        assert_eq!(cpu.pcounter, 10);
    }

    #[test]
    fn test_bit_zero_result() {
        let mut cpu = CPU::default();
        cpu.acc = 0b00001111;
        cpu.bit(0b11110000);
        assert_eq!(cpu.flag_status(StatusFlag::Zero), true);
        assert_eq!(cpu.flag_status(StatusFlag::Overflow), true);
        assert_eq!(cpu.flag_status(StatusFlag::Negative), true);
    }

    #[test]
    fn test_bit_nonzero_result() {
        let mut cpu = CPU::default();
        cpu.acc = 0b00001111;
        cpu.bit(0b00001111);
        assert_eq!(cpu.flag_status(StatusFlag::Zero), false);
        assert_eq!(cpu.flag_status(StatusFlag::Overflow), false);
        assert_eq!(cpu.flag_status(StatusFlag::Negative), false);
    }

    #[test]
    fn test_bmi_negative_set() {
        let mut cpu = CPU::default();
        cpu.pcounter = 10;
        cpu.flag_set(StatusFlag::Negative);
        cpu.bmi(5);
        assert_eq!(cpu.pcounter, 15);
    }

    #[test]
    fn test_bmi_negative_clear() {
        let mut cpu = CPU::default();
        cpu.pcounter = 10;
        cpu.flag_clear(StatusFlag::Negative);
        cpu.bmi(5);
        assert_eq!(cpu.pcounter, 10);
    }

    #[test]
    fn test_bne_zero_set() {
        let mut cpu = CPU::default();
        cpu.pcounter = 10;
        cpu.flag_set(StatusFlag::Zero);
        cpu.bne(5);
        assert_eq!(cpu.pcounter, 10);
    }

    #[test]
    fn test_bne_zero_clear() {
        let mut cpu = CPU::default();
        cpu.pcounter = 10;
        cpu.flag_clear(StatusFlag::Zero);
        cpu.bne(5);
        assert_eq!(cpu.pcounter, 15);
    }

    #[test]
    fn test_bpl_negative_set() {
        let mut cpu = CPU::default();
        cpu.pcounter = 10;
        cpu.flag_set(StatusFlag::Negative);
        cpu.bpl(5);
        assert_eq!(cpu.pcounter, 10);
    }

    #[test]
    fn test_bpl_negative_clear() {
        let mut cpu = CPU::default();
        cpu.pcounter = 10;
        cpu.flag_clear(StatusFlag::Negative);
        cpu.bpl(5);
        assert_eq!(cpu.pcounter, 15);
    }
}
