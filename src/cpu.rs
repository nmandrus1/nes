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
    /// program counter, 16 bits
    pc: u16,

    /// stack pointer, can only access 256 bytes from 0x0100-0x01FF
    stack_ptr: u8,

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
            pc: 0,
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
    fn read_opcode(&mut self) -> u8 {
        self.read(self.pc)
    }

    fn get_address(&mut self, mode: AddrMode) -> u16 {
        match mode {
            AddrMode::Immediate => {
                let address = self.pc;
                self.pc += 1;
                address as u16
            }

            AddrMode::ZeroPage => {
                let address = self.read(self.pc) as u16;
                self.pc += 1;
                address
            }

            AddrMode::ZeroPageX => {
                let address = (self.read(self.pc).wrapping_add(self.x)) as u16;
                self.pc += 1;
                address
            }

            AddrMode::ZeroPageY => {
                let address = (self.read(self.pc).wrapping_add(self.y)) as u16;
                self.pc += 1;
                address
            }

            AddrMode::Absolute => {
                let lo = self.read(self.pc) as u16;
                let hi = self.read(self.pc + 1) as u16;
                self.pc += 2;
                hi << 8 | lo
            }

            AddrMode::AbsoluteX => {
                let lo = self.read(self.pc) as u16;
                let hi = self.read(self.pc + 1) as u16;
                self.pc += 2;
                (hi << 8 | lo) + self.x as u16
            }

            AddrMode::AbsoluteY => {
                let lo = self.read(self.pc) as u16;
                let hi = self.read(self.pc + 1) as u16;
                self.pc += 2;
                (hi << 8 | lo) + self.y as u16
            }

            AddrMode::IndirectX => {
                let addr = self.read(self.pc).wrapping_add(self.x) as u16;
                let lo = self.read(addr) as u16;
                let hi = self.read(addr + 1) as u16;
                self.pc += 1;
                hi << 8 | lo
            }

            AddrMode::IndirectY => {
                let addr = self.read(self.pc) as u16;
                let lo = self.read(addr) as u16;
                let hi = self.read(addr + 1) as u16;
                self.pc += 1;
                (hi << 8 | lo).wrapping_add(self.y.into())
            }
        }
    }

    /// Decode the opcode to an Instruction
    fn decode(&mut self, opcode: u8) -> Instruction {
        match opcode {
            // Add with Carry (ADC)   // Addressing Mode
            0x69 => Instruction::ADC(AddrMode::Immediate), // Immediate
            0x65 => Instruction::ADC(AddrMode::ZeroPage),  // Zero Page
            0x75 => Instruction::ADC(AddrMode::ZeroPageX), // Zero Page, X
            0x6D => Instruction::ADC(AddrMode::Absolute),  // Absolute
            0x7D => Instruction::ADC(AddrMode::AbsoluteX), // Absolute, X
            0x79 => Instruction::ADC(AddrMode::AbsoluteY), // Absolute, Y
            0x61 => Instruction::ADC(AddrMode::IndirectX), // Indirect, X
            0x71 => Instruction::ADC(AddrMode::IndirectY), // Indirect, Y

            _ => panic!("Fatal Error: Instruction not implemented"),
        }
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

    /// Reads the byte at an address in memory
    fn read(&self, address: u16) -> u8 {
        self.mem[address as usize]
    }

    /// Writes a byte of memory to the specified memory address
    fn write(&mut self, address: u16, value: u8) {
        self.mem[address as usize] = value;
    }

    /// Pushes a byte onto the stack
    fn stack_push(&mut self, value: u8) {
        let stack_addr = 0x0100 + self.stack_ptr as u16;
        self.write(stack_addr, value);
        match self.stack_ptr.checked_sub(1) {
            Some(s) => self.stack_ptr = s,
            None => panic!("Fatal Error: Stack Overflow"),
        }
    }

    /// Pops a byte off the stack
    fn stack_pop(&mut self) -> u8 {
        let result = self.read(0x0100 + self.stack_ptr as u16);
        match self.stack_ptr.checked_add(1) {
            Some(s) => self.stack_ptr = s,
            None => panic!("Fatal Error: Stack Underflow"),
        }

        return result;
    }

    fn execute(&mut self, instr: Instruction) {
        match instr {
            Instruction::ADC(mode) => {
                let address = self.get_address(mode);
                let operand = self.read(address);
                self.adc(operand);
            }
            Instruction::ADC(mode) => {}
            Instruction::AND(mode) => {}
            Instruction::ASL(mode) => {}
            Instruction::BCC => {}
            Instruction::BCS => {}
            Instruction::BEQ => {}
            Instruction::BIT(mode) => {}
            Instruction::BMI => {}
            Instruction::BNE => {}
            Instruction::BPL => {}
            Instruction::BRK => {}
            Instruction::BVC => {}
            Instruction::BVS => {}
            Instruction::CLC => {}
            Instruction::CLD => {}
            Instruction::CLI => {}
            Instruction::CLV => {}
            Instruction::CMP(mode) => {}
            Instruction::CPX(mode) => {}
            Instruction::CPY(mode) => {}
            Instruction::DEC(mode) => {}
            Instruction::DEX => {}
            Instruction::DEY => {}
            Instruction::EOR(mode) => {}
            Instruction::INC(mode) => {}
            Instruction::INX => {}
            Instruction::INY => {}
            Instruction::JMP(mode) => {}
            Instruction::JSR(mode) => {}
            Instruction::LDA(mode) => {}
            Instruction::LDX(mode) => {}
            Instruction::LDY(mode) => {}
            Instruction::LSR(mode) => {}
            Instruction::NOP => {}
            Instruction::ORA(mode) => {}
            Instruction::PHA => {}
            Instruction::PHP => {}
            Instruction::PLA => {}
            Instruction::PLP => {}
            Instruction::ROL(mode) => {}
            Instruction::ROR(mode) => {}
            Instruction::RTI => {}
            Instruction::RTS => {}
            Instruction::SBC(mode) => {}
            Instruction::SEC => {}
            Instruction::SED => {}
            Instruction::SEI => {}
            Instruction::STA(mode) => {}
            Instruction::STX(mode) => {}
            Instruction::STY(mode) => {}
            Instruction::TAX => {}
            Instruction::TAY => {}
            Instruction::TSX => {}
            Instruction::TXA => {}
            Instruction::TXS => {}
            Instruction::TYA => {}
        }
    }

    pub fn run(&mut self) {
        // main loop of reading opcode and executing instruction
        loop {
            // read opcode and increment program counter
            let opcode = self.read(self.pc);
            self.pc += 1;

            info!("OPCODE: 0x{:X}", opcode);

            // decode instruction
            let instr = self.decode(opcode);

            // execute
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

    /// shift the bits of the operand left 1 and place the MSB in the Carry bit
    fn asl(&mut self, operand: &mut u8) {
        let msb = *operand >> 7;
        *operand <<= 1;

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
            self.pc = (self.pc as i16 + offset as i16) as u16;
        }
    }

    /// if the carry flag is set (1)
    /// adds the operand (an i8) to the program counter
    fn bcs(&mut self, operand: u8) {
        let offset = operand as i8;

        if self.flag_status(StatusFlag::Carry) {
            self.pc = (self.pc as i16 + offset as i16) as u16;
        }
    }

    /// if the zero flag is set (1)
    /// adds the operand (an i8) to the program counter
    fn beq(&mut self, operand: u8) {
        let offset = operand as i8;

        if self.flag_status(StatusFlag::Zero) {
            self.pc = (self.pc as i16 + offset as i16) as u16;
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
            self.pc = (self.pc as i16 + offset as i16) as u16;
        }
    }

    /// if the zero flag is clear (0)
    /// adds the operand (an i8) to the program counter
    fn bne(&mut self, operand: u8) {
        let offset = operand as i8;

        if !self.flag_status(StatusFlag::Zero) {
            self.pc = (self.pc as i16 + offset as i16) as u16;
        }
    }

    /// if the negative flag is clear (0)
    /// adds the operand (an i8) to the program counter
    fn bpl(&mut self, operand: u8) {
        let offset = operand as i8;

        if !self.flag_status(StatusFlag::Negative) {
            self.pc = (self.pc as i16 + offset as i16) as u16;
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
            self.pc = (self.pc as i16 + offset as i16) as u16;
        }
    }

    /// if the overflow flag is set (1)
    /// adds the operand (an i8) to the program counter
    fn bvs(&mut self, operand: u8) {
        let offset = operand as i8;

        if self.flag_status(StatusFlag::Overflow) {
            self.pc = (self.pc as i16 + offset as i16) as u16;
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
    fn byte_cmp(&mut self, rhs: u8, lhs: u8) {
        let result = rhs.wrapping_sub(lhs) >> 7;
        match rhs.cmp(&lhs) {
            std::cmp::Ordering::Less => {
                self.flag_clear(StatusFlag::Zero);
                self.flag_clear(StatusFlag::Carry);
                if result == 1 {
                    self.flag_set(StatusFlag::Negative);
                } else {
                    self.flag_clear(StatusFlag::Zero);
                }
            }
            std::cmp::Ordering::Equal => {
                self.flag_clear(StatusFlag::Negative);
                self.flag_set(StatusFlag::Zero);
                self.flag_set(StatusFlag::Carry);
            }
            std::cmp::Ordering::Greater => {
                self.flag_clear(StatusFlag::Zero);
                self.flag_set(StatusFlag::Carry);
                if result == 1 {
                    self.flag_set(StatusFlag::Negative);
                } else {
                    self.flag_clear(StatusFlag::Zero);
                }
            }
        }
    }

    /// Compare the accumulator with operand
    fn cmp(&mut self, operand: u8) {
        self.byte_cmp(self.acc, operand);
    }

    /// Compare X register with operand
    fn cpx(&mut self, operand: u8) {
        self.byte_cmp(self.x, operand);
    }

    /// Compare Y register with operand
    fn cpy(&mut self, operand: u8) {
        self.byte_cmp(self.y, operand);
    }

    /// Decrement whatever value is held at the memory location of the operand
    fn dec(&mut self, address: u16) {
        self.write(address, self.read(address).wrapping_sub(1));
        self.update_zero_and_negative_flags(self.read(address))
    }

    /// Decrement value in the X register
    fn dex(&mut self) {
        self.x = self.x.wrapping_sub(1);
        self.update_zero_and_negative_flags(self.x);
    }

    /// Decrement value in the Y register
    fn dey(&mut self) {
        self.y = self.y.wrapping_sub(1);
        self.update_zero_and_negative_flags(self.y);
    }

    /// performs an XOR on the accumulator and the operand
    fn eor(&mut self, operand: u8) {
        self.acc ^= operand;
        self.update_zero_and_negative_flags(self.acc)
    }

    /// Increment value in memory at operand
    fn inc(&mut self, address: u16) {
        self.write(address, self.read(address).wrapping_add(1));
        self.update_zero_and_negative_flags(self.read(address));
    }

    /// Increment the X register by 1
    fn inx(&mut self) {
        self.x = self.x.wrapping_add(1);
        self.update_zero_and_negative_flags(self.x);
    }

    /// Increment the Y register by 1
    fn iny(&mut self) {
        self.y = self.y.wrapping_add(1);
        self.update_zero_and_negative_flags(self.y);
    }

    /// Set the program counter equal to the address specified by the operand
    fn jmp(&mut self, operand: u16) {
        self.pc = operand;

        // Bug-for-bug Indirect Addressing Code
        //
        // let lsb = self.read(operand);
        // let msb: u8;
        //
        // if (operand & 0xFF == 0xFF) {
        //     msb = self.read(operand & 0xFF00);
        // } else {
        //     msb = self.read(operand + 1);
        // }
        //
        // self.pcounter = (((msb as u16) << 8) | lsb as u16) as usize;
    }

    /// Pushes return address onto stack and sets pcounter to passed address
    fn jsr(&mut self, address: u16) {
        let ra = (self.pc - 1) as u16;
        self.stack_push((ra >> 8) as u8);
        self.stack_push((ra & 0x00FF) as u8);

        self.pc = address;
    }

    /// Store a value in the accumulator
    fn lda(&mut self, operand: u8) {
        self.acc = operand;
        self.update_zero_and_negative_flags(self.acc);
    }

    /// Store a value in the X register
    fn ldx(&mut self, operand: u8) {
        self.x = operand;
        self.update_zero_and_negative_flags(self.x);
    }

    /// Store a value in the Y register
    fn ldy(&mut self, operand: u8) {
        self.y = operand;
        self.update_zero_and_negative_flags(self.y);
    }

    fn lsr(&mut self, operand: u8, address: Option<u16>) {}
}

enum Instruction {
    ADC(AddrMode),
    AND(AddrMode),
    ASL(AddrMode),
    BCC,
    BCS,
    BEQ,
    BIT(AddrMode),
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
    CMP(AddrMode),
    CPX(AddrMode),
    CPY(AddrMode),
    DEC(AddrMode),
    DEX,
    DEY,
    EOR(AddrMode),
    INC(AddrMode),
    INX,
    INY,
    JMP(AddrMode),
    JSR(AddrMode),
    LDA(AddrMode),
    LDX(AddrMode),
    LDY(AddrMode),
    LSR(AddrMode),
    NOP,
    ORA(AddrMode),
    PHA,
    PHP,
    PLA,
    PLP,
    ROL(AddrMode),
    ROR(AddrMode),
    RTI,
    RTS,
    SBC(AddrMode),
    SEC,
    SED,
    SEI,
    STA(AddrMode),
    STX(AddrMode),
    STY(AddrMode),
    TAX,
    TAY,
    TSX,
    TXA,
    TXS,
    TYA,
}

pub enum AddrMode {
    Immediate,
    ZeroPage,
    ZeroPageX,
    ZeroPageY,
    Absolute,
    AbsoluteX,
    AbsoluteY,
    IndirectX,
    IndirectY,
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
        cpu.pc = 10;
        cpu.flag_clear(StatusFlag::Carry);
        cpu.bcc(5);
        assert_eq!(cpu.pc, 15);
    }

    #[test]
    fn test_bcc_with_carry_set() {
        let mut cpu = CPU::default();
        cpu.pc = 10;
        cpu.flag_set(StatusFlag::Carry);
        cpu.bcc(5);
        assert_eq!(cpu.pc, 10);
    }

    #[test]
    fn test_bcs_carry_set() {
        let mut cpu = CPU::default();
        cpu.pc = 10;
        cpu.flag_set(StatusFlag::Carry);
        cpu.bcs(5);
        assert_eq!(cpu.pc, 15);
    }

    #[test]
    fn test_bcs_carry_clear() {
        let mut cpu = CPU::default();
        cpu.pc = 10;
        cpu.flag_clear(StatusFlag::Carry);
        cpu.bcs(5);
        assert_eq!(cpu.pc, 10);
    }

    #[test]
    fn test_beq_zero_set() {
        let mut cpu = CPU::default();
        cpu.pc = 10;
        cpu.flag_set(StatusFlag::Zero);
        cpu.beq(5);
        assert_eq!(cpu.pc, 15);
    }

    #[test]
    fn test_beq_zero_clear() {
        let mut cpu = CPU::default();
        cpu.pc = 10;
        cpu.flag_clear(StatusFlag::Zero);
        cpu.beq(5);
        assert_eq!(cpu.pc, 10);
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
        cpu.pc = 10;
        cpu.flag_set(StatusFlag::Negative);
        cpu.bmi(5);
        assert_eq!(cpu.pc, 15);
    }

    #[test]
    fn test_bmi_negative_clear() {
        let mut cpu = CPU::default();
        cpu.pc = 10;
        cpu.flag_clear(StatusFlag::Negative);
        cpu.bmi(5);
        assert_eq!(cpu.pc, 10);
    }

    #[test]
    fn test_bne_zero_set() {
        let mut cpu = CPU::default();
        cpu.pc = 10;
        cpu.flag_set(StatusFlag::Zero);
        cpu.bne(5);
        assert_eq!(cpu.pc, 10);
    }

    #[test]
    fn test_bne_zero_clear() {
        let mut cpu = CPU::default();
        cpu.pc = 10;
        cpu.flag_clear(StatusFlag::Zero);
        cpu.bne(5);
        assert_eq!(cpu.pc, 15);
    }

    #[test]
    fn test_bpl_negative_set() {
        let mut cpu = CPU::default();
        cpu.pc = 10;
        cpu.flag_set(StatusFlag::Negative);
        cpu.bpl(5);
        assert_eq!(cpu.pc, 10);
    }

    #[test]
    fn test_bpl_negative_clear() {
        let mut cpu = CPU::default();
        cpu.pc = 10;
        cpu.flag_clear(StatusFlag::Negative);
        cpu.bpl(5);
        assert_eq!(cpu.pc, 15);
    }

    // CMP - Compare accumulator
    #[test]
    fn test_cmp_equal() {
        let mut cpu = CPU::default();
        cpu.acc = 0x42;
        cpu.cmp(0x42);
        assert_eq!(cpu.flag_status(StatusFlag::Carry), true);
        assert_eq!(cpu.flag_status(StatusFlag::Zero), true);
        assert_eq!(cpu.flag_status(StatusFlag::Negative), false);
    }

    #[test]
    fn test_cmp_less() {
        let mut cpu = CPU::default();
        cpu.acc = 0x30;
        cpu.cmp(0x42);
        assert_eq!(cpu.flag_status(StatusFlag::Carry), false);
        assert_eq!(cpu.flag_status(StatusFlag::Zero), false);
        assert_eq!(cpu.flag_status(StatusFlag::Negative), true);
    }

    #[test]
    fn test_cmp_more() {
        let mut cpu = CPU::default();
        cpu.acc = 0x50;
        cpu.cmp(0x42);
        assert_eq!(cpu.flag_status(StatusFlag::Carry), true);
        assert_eq!(cpu.flag_status(StatusFlag::Zero), false);
        assert_eq!(cpu.flag_status(StatusFlag::Negative), false);
    }

    // CPX - Compare X Register
    #[test]
    fn test_cpx_equal() {
        let mut cpu = CPU::default();
        cpu.x = 0x42;
        cpu.cpx(0x42);
        assert_eq!(cpu.flag_status(StatusFlag::Carry), true);
        assert_eq!(cpu.flag_status(StatusFlag::Zero), true);
        assert_eq!(cpu.flag_status(StatusFlag::Negative), false);
    }

    #[test]
    fn test_cpx_less() {
        let mut cpu = CPU::default();
        cpu.x = 0x30;
        cpu.cpx(0x42);
        assert_eq!(cpu.flag_status(StatusFlag::Carry), false);
        assert_eq!(cpu.flag_status(StatusFlag::Zero), false);
        assert_eq!(cpu.flag_status(StatusFlag::Negative), true);
    }

    #[test]
    fn test_cpx_more() {
        let mut cpu = CPU::default();
        cpu.x = 0x50;
        cpu.cpx(0x42);
        assert_eq!(cpu.flag_status(StatusFlag::Carry), true);
        assert_eq!(cpu.flag_status(StatusFlag::Zero), false);
        assert_eq!(cpu.flag_status(StatusFlag::Negative), false);
    }

    // CPY - Compare Y Register
    #[test]
    fn test_cpy_equal() {
        let mut cpu = CPU::default();
        cpu.y = 0x42;
        cpu.cpy(0x42);
        assert_eq!(cpu.flag_status(StatusFlag::Carry), true);
        assert_eq!(cpu.flag_status(StatusFlag::Zero), true);
        assert_eq!(cpu.flag_status(StatusFlag::Negative), false);
    }

    #[test]
    fn test_cpy_less() {
        let mut cpu = CPU::default();
        cpu.y = 0x30;
        cpu.cpy(0x42);
        assert_eq!(cpu.flag_status(StatusFlag::Carry), false);
        assert_eq!(cpu.flag_status(StatusFlag::Zero), false);
        assert_eq!(cpu.flag_status(StatusFlag::Negative), true);
    }

    #[test]
    fn test_cpy_more() {
        let mut cpu = CPU::default();
        cpu.y = 0x50;
        cpu.cpy(0x42);
        assert_eq!(cpu.flag_status(StatusFlag::Carry), true);
        assert_eq!(cpu.flag_status(StatusFlag::Zero), false);
        assert_eq!(cpu.flag_status(StatusFlag::Negative), false);
    }

    // DEC - Decrement Memory
    #[test]
    fn test_dec_zero() {
        let mut cpu = CPU::default();
        cpu.mem[0x42] = 1;
        cpu.dec(0x42);
        assert_eq!(cpu.mem[0x42], 0);
        assert_eq!(cpu.flag_status(StatusFlag::Zero), true);
        assert_eq!(cpu.flag_status(StatusFlag::Negative), false);
    }

    #[test]
    fn test_dec_negative() {
        let mut cpu = CPU::default();
        cpu.mem[0x42] = 0;
        cpu.dec(0x42);
        assert_eq!(cpu.mem[0x42], 0xFF);
        assert_eq!(cpu.flag_status(StatusFlag::Zero), false);
        assert_eq!(cpu.flag_status(StatusFlag::Negative), true);
    }

    #[test]
    fn test_dec_positive() {
        let mut cpu = CPU::default();
        cpu.mem[0x42] = 0x43;
        cpu.dec(0x42);
        assert_eq!(cpu.mem[0x42], 0x42);
        assert_eq!(cpu.flag_status(StatusFlag::Zero), false);
        assert_eq!(cpu.flag_status(StatusFlag::Negative), false);
    }

    // DEX - Decrement X Register
    #[test]
    fn test_dex() {
        let mut cpu = CPU::default();
        cpu.x = 0x42;
        cpu.dex();
        assert_eq!(cpu.x, 0x41);
    }

    #[test]
    fn test_dex_zero() {
        let mut cpu = CPU::default();
        cpu.x = 0x01;
        cpu.dex();
        assert_eq!(cpu.x, 0x00);
    }

    #[test]
    fn test_dex_underflow() {
        let mut cpu = CPU::default();
        cpu.x = 0x00;
        cpu.dex();
        assert_eq!(cpu.x, 0xFF);
    }

    // DEY - Decrement Y Register
    #[test]
    fn test_dey() {
        let mut cpu = CPU::default();
        cpu.y = 0x42;
        cpu.dey();
        assert_eq!(cpu.y, 0x41);
    }

    #[test]
    fn test_dey_zero() {
        let mut cpu = CPU::default();
        cpu.y = 0x01;
        cpu.dey();
        assert_eq!(cpu.y, 0x00);
    }

    #[test]
    fn test_dey_underflow() {
        let mut cpu = CPU::default();
        cpu.y = 0x00;
        cpu.dey();
        assert_eq!(cpu.y, 0xFF);
    }

    // EOR - Exclusive OR
    #[test]
    fn test_eor() {
        let mut cpu = CPU::default();
        cpu.acc = 0x42;
        cpu.eor(0x24);
        assert_eq!(cpu.acc, 0x66);
    }

    #[test]
    fn test_eor_zero() {
        let mut cpu = CPU::default();
        cpu.acc = 0x42;
        cpu.eor(0x42);
        assert_eq!(cpu.acc, 0x00);
    }

    #[test]
    fn test_eor_same() {
        let mut cpu = CPU::default();
        cpu.acc = 0x00;
        cpu.eor(0x00);
        assert_eq!(cpu.acc, 0x00);
    }

    // INC - Increment Memory
    #[test]
    fn test_inc() {
        let mut cpu = CPU::default();
        cpu.mem[0x2000] = 0x42;
        cpu.inc(0x2000);
        assert_eq!(cpu.mem[0x2000], 0x43);
    }

    #[test]
    fn test_inc_overflow() {
        let mut cpu = CPU::default();
        cpu.mem[0x2000] = 0xFF;
        cpu.inc(0x2000);
        assert_eq!(cpu.mem[0x2000], 0x00);
    }

    #[test]
    fn test_inc_zero() {
        let mut cpu = CPU::default();
        cpu.mem[0x2000] = 0x00;
        cpu.inc(0x2000);
        assert_eq!(cpu.mem[0x2000], 0x01);
    }

    // INX - Increment X Register
    #[test]
    fn test_inx() {
        let mut cpu = CPU::default();
        cpu.x = 0x42;
        cpu.inx();
        assert_eq!(cpu.x, 0x43);
    }

    #[test]
    fn test_inx_overflow() {
        let mut cpu = CPU::default();
        cpu.x = 0xFF;
        cpu.inx();
        assert_eq!(cpu.x, 0x00);
    }

    #[test]
    fn test_inx_zero() {
        let mut cpu = CPU::default();
        cpu.x = 0x00;
        cpu.inx();
        assert_eq!(cpu.x, 0x01);
    }

    // INY - Increment Y Register
    #[test]
    fn test_iny() {
        let mut cpu = CPU::default();
        cpu.y = 0x42;
        cpu.iny();
        assert_eq!(cpu.y, 0x43);
    }

    #[test]
    fn test_iny_overflow() {
        let mut cpu = CPU::default();
        cpu.y = 0xFF;
        cpu.iny();
        assert_eq!(cpu.y, 0x00);
    }

    #[test]
    fn test_iny_zero() {
        let mut cpu = CPU::default();
        cpu.y = 0x00;
        cpu.iny();
        assert_eq!(cpu.y, 0x01);
    }
}
