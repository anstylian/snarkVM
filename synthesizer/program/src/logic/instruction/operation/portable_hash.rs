// Copyright 2024 Aleo Network Foundation
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:

// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::{
    Opcode,
    Operand,
    traits::{RegistersLoad, RegistersLoadCircuit, RegistersStore, RegistersStoreCircuit, StackMatches, StackProgram},
};
use console::{
    network::prelude::*,
    program::{Literal, LiteralType, Plaintext, PlaintextType, Register, RegisterType, Value},
    types::Boolean,
};
use circuit::traits::ToBits;

const EXPECTED_OPERANDS: usize = 1;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct PortableHashKeccak256<N: Network> {
    /// The operand as `input`.
    operands: Vec<Operand<N>>,
    /// The destination register.
    destination: Register<N>,
    /// The destination register type.
    destination_type: PlaintextType<N>,
}

impl<N: Network> PortableHashKeccak256<N> {
    /// Returns the opcode as a string.
    #[inline]
    pub const fn opcode() -> Opcode {
        Opcode::PortableHash("hash.portable.keccak256")
    }

    /// Returns the operands in the operation.
    #[inline]
    pub fn operands(&self) -> &[Operand<N>] {
        // Sanity check that the operands is the correct length.
        debug_assert!(EXPECTED_OPERANDS == self.operands.len(), "Invalid number of operands for '{}'", Self::opcode());
        // Return the operand.
        &self.operands
    }

    /// Returns the destination register.
    #[inline]
    pub fn destinations(&self) -> Vec<Register<N>> {
        vec![self.destination.clone()]
    }

    /// Returns the destination register type.
    #[inline]
    pub const fn destination_type(&self) -> &PlaintextType<N> {
        &self.destination_type
    }
}

impl<N: Network> PortableHashKeccak256<N> {
    /// Evaluates the instruction.
    #[inline]
    pub fn evaluate(
        &self,
        stack: &(impl StackMatches<N> + StackProgram<N>),
        registers: &mut (impl RegistersLoad<N> + RegistersStore<N>),
    ) -> Result<()> {
        todo!()
    }

    /// Executes the instruction.
    #[inline]
    pub fn execute<A: circuit::Aleo<Network = N>>(
        &self,
        stack: &(impl StackMatches<N> + StackProgram<N>),
        registers: &mut (impl RegistersLoadCircuit<N, A> + RegistersStoreCircuit<N, A>),
    ) -> Result<()> {

        let input = registers.load_circuit(stack, &self.operands[0])?;
        println!("input: {:?}", input.data_to_bits_le());
        // let output = circuit::Literal::U8(circuit::U8::from_str("8u8").unwrap());
        // // Convert the output to a stack value.
        // let output = circuit::Value::Plaintext(circuit::Plaintext::Literal(output, Default::default()));

        let v1 = circuit::Literal::U8(circuit::U8::from_str("8u8").unwrap());
        let v1 = circuit::Plaintext::Literal(v1, Default::default());
        let output = circuit::Value::Plaintext(circuit::Plaintext::Array(vec![v1], Default::default()));

        // Store the output.
        registers.store_circuit(stack, &self.destination, output)
    }

    /// Finalizes the instruction.
    #[inline]
    pub fn finalize(
        &self,
        stack: &(impl StackMatches<N> + StackProgram<N>),
        registers: &mut (impl RegistersLoad<N> + RegistersStore<N>),
    ) -> Result<()> {
        todo!()
        // self.evaluate(stack, registers)
    }

    /// Returns the output type from the given program and input types.
    #[inline]
    pub fn output_types(
        &self,
        _stack: &impl StackProgram<N>,
        input_types: &[RegisterType<N>],
    ) -> Result<Vec<RegisterType<N>>> {
        // // Ensure the number of input types is correct.
        // check_number_of_operands(VARIANT, Self::opcode(), input_types.len())?;
        // // Ensure the number of operands is correct.
        // check_number_of_operands(VARIANT, Self::opcode(), self.operands.len())?;
        // // Ensure the destination type is valid.
        // ensure!(is_valid_destination_type(&self.destination_type), "Invalid destination type in 'hash' instruction");

        // TODO (howardwu): If the operation is Pedersen, check that it is within the number of bits.
        Ok(vec![RegisterType::Plaintext(self.destination_type.clone())])
    }
}

impl<N: Network> Parser for PortableHashKeccak256<N> {
    /// Parses a string into an operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        /// Parse the operands from the string.
        fn parse_operands<N: Network>(string: &str, num_operands: usize) -> ParserResult<Vec<Operand<N>>> {
            let mut operands = Vec::with_capacity(num_operands);
            let mut string = string;

            for _ in 0..num_operands {
                // Parse the whitespace from the string.
                let (next_string, _) = Sanitizer::parse_whitespaces(string)?;
                // Parse the operand from the string.
                let (next_string, operand) = Operand::parse(next_string)?;
                // Update the string.
                string = next_string;
                // Push the operand.
                operands.push(operand);
            }

            Ok((string, operands))
        }

        // Parse the opcode from the string.
        let (string, _) = tag(*Self::opcode())(string)?;
        // Parse the operands from the string.
        let (string, operands) = parse_operands(string, EXPECTED_OPERANDS)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the "into" from the string.
        let (string, _) = tag("into")(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the destination register from the string.
        let (string, destination) = Register::parse(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the "as" from the string.
        let (string, _) = tag("as")(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the destination register type from the string.
        let (string, destination_type) = PlaintextType::parse(string)?;
        // Ensure the destination type is allowed.
        match destination_type {
            PlaintextType::Literal(LiteralType::Boolean) | PlaintextType::Literal(LiteralType::String) => {
                map_res(fail, |_: ParserResult<Self>| {
                    Err(error(format!("Failed to parse 'hash': '{destination_type}' is invalid")))
                })(string)
            }
            _ => Ok((string, Self { operands, destination, destination_type })),
        }
    }
}

impl<N: Network> FromStr for PortableHashKeccak256<N> {
    type Err = Error;

    /// Parses a string into an operation.
    #[inline]
    fn from_str(string: &str) -> Result<Self> {
        match Self::parse(string) {
            Ok((remainder, object)) => {
                // Ensure the remainder is empty.
                ensure!(remainder.is_empty(), "Failed to parse string. Found invalid character in: \"{remainder}\"");
                // Return the object.
                Ok(object)
            }
            Err(error) => bail!("Failed to parse string. {error}"),
        }
    }
}

impl<N: Network> Debug for PortableHashKeccak256<N> {
    /// Prints the operation as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for PortableHashKeccak256<N> {
    /// Prints the operation to a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // Ensure the number of operands is correct.
        // check_number_of_operands(VARIANT, Self::opcode(), self.operands.len()).map_err(|_| fmt::Error)?;
        if self.operands.len() != EXPECTED_OPERANDS {
            return Err(fmt::Error);
        }
        // Print the operation.
        write!(f, "{} ", Self::opcode())?;
        self.operands.iter().try_for_each(|operand| write!(f, "{operand} "))?;
        write!(f, "into {} as {}", self.destination, self.destination_type)
    }
}

impl<N: Network> FromBytes for PortableHashKeccak256<N> {
    /// Reads the operation from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Prepare the number of operands.
        // Read the operands.
        let operands = (0..EXPECTED_OPERANDS).map(|_| Operand::read_le(&mut reader)).collect::<Result<_, _>>()?;
        // Read the destination register.
        let destination = Register::read_le(&mut reader)?;
        // Read the destination register type.
        let destination_type = PlaintextType::read_le(&mut reader)?;
        // Return the operation.
        Ok(Self { operands, destination, destination_type })
    }
}

impl<N: Network> ToBytes for PortableHashKeccak256<N> {
    /// Writes the operation to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Ensure the number of operands is correct.
        // check_number_of_operands(VARIANT, Self::opcode(), self.operands.len()).map_err(|e| error(format!("{e}")))?;
        if self.operands.len() != EXPECTED_OPERANDS {
            return Err(error(format!(
                "Failed to serialize an operation: expected {EXPECTED_OPERANDS} operands, found {}",
                self.operands.len()
            )));
        }
        // Write the operands.
        self.operands.iter().try_for_each(|operand| operand.write_le(&mut writer))?;
        // Write the destination register.
        self.destination.write_le(&mut writer)?;
        // Write the destination register type.
        self.destination_type.write_le(&mut writer)
    }
}
