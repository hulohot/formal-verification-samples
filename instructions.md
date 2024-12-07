# Formal Verification Learning Examples

This repository contains a collection of SystemVerilog designs specifically created for learning formal verification techniques. Each design is crafted to demonstrate different aspects of hardware design and various verification challenges.

## Design Categories

### 1. Arithmetic Circuits
- **Simple Adder** (`designs/adder.v`): Parameterized N-bit adder with carry in/out
- **Multiplier** (`designs/multiplier.v`): Sequential multiplier using shift-and-add algorithm
- **ALU** (`designs/alu.v`): Basic ALU with add, subtract, AND, OR, XOR operations

### 2. Data Buffers
- **FIFO** (`designs/fifo.v`): Synchronous FIFO with configurable depth and width
- **Shift Register** (`designs/shift_register.v`): Parameterized shift register with parallel load
- **Ring Counter** (`designs/ring_counter.v`): Simple ring counter with one-hot encoding

### 3. Finite State Machines
- **Traffic Light Controller** (`designs/traffic_light.v`): Basic traffic light system
- **Vending Machine** (`designs/vending_machine.v`): Simple vending machine with coin input and product output
- **Sequence Detector** (`designs/sequence_detector.v`): Detects specific bit patterns in input stream

### 4. Additional Designs
- **Arbiter** (`designs/arbiter.v`): Round-robin arbiter for resource sharing
- **Memory Controller** (`designs/memory_controller.v`): Simple memory controller with read/write operations

## Verification Challenges

Each design presents unique verification challenges:

1. **Arithmetic Circuits**
   - Overflow detection
   - Timing constraints
   - Corner cases in operations

2. **Data Buffers**
   - Full/Empty conditions
   - Data integrity
   - Race conditions

3. **FSMs**
   - State reachability
   - Deadlock detection
   - Invalid state transitions

4. **Additional Designs**
   - Resource contention
   - Protocol compliance
   - Fairness properties

## Getting Started

1. Each design file contains:
   - Module implementation
   - Parameters for configuration
   - Port descriptions
   - Behavioral logic

2. Suggested verification properties are included as comments in each file

3. Recommended verification approach:
   - Start with simple safety properties
   - Progress to liveness properties
   - Explore corner cases
   - Verify timing constraints 