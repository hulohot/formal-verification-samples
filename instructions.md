# Formal Verification Learning Examples

This repository contains a collection of SystemVerilog designs specifically created for learning formal verification techniques. Each design is crafted to demonstrate different aspects of hardware design and various verification challenges.

## Project Organization

```
formal-verification-samples/
├── designs/          # RTL design files
├── formal/          # Formal verification files
│   ├── adder/      # Verification for adder
│   ├── alu/        # Verification for ALU
│   └── ...
├── tests/          # Traditional simulation testbenches
└── scripts/        # Utility scripts
```

## Design Categories

### 1. Arithmetic Circuits
- **Simple Adder** (`designs/adder.v`)
  - Parameterized N-bit adder with carry in/out
  - Verification Properties:
    - Result correctness
    - Overflow detection
    - Carry propagation

- **Multiplier** (`designs/multiplier.v`)
  - Sequential multiplier using shift-and-add algorithm
  - Verification Properties:
    - Result correctness
    - Operation completion
    - Busy flag consistency
    - Reset behavior

- **ALU** (`designs/alu.v`)
  - Basic ALU with arithmetic and logical operations
  - Verification Properties:
    - Operation correctness
    - Flag accuracy (zero, negative, overflow)
    - Invalid operation handling

### 2. Data Buffers
- **FIFO** (`designs/fifo.v`)
  - Synchronous FIFO with configurable depth
  - Verification Properties:
    - Full/Empty flag correctness
    - Data integrity
    - No data loss
    - Pointer wraparound

### 3. Finite State Machines
- **Traffic Light Controller** (`designs/traffic_light.v`)
  - Traffic light system with emergency override
  - Verification Properties:
    - Safety (no conflicting signals)
    - Liveness (each direction eventually served)
    - Timing constraints
    - Emergency response

- **Sequence Detector** (`designs/sequence_detector.v`)
  - Pattern detector for serial bit streams
  - Verification Properties:
    - Pattern detection correctness
    - No false positives
    - Overlapping sequences
    - Reset behavior

### 4. Resource Management
- **Arbiter** (`designs/arbiter.v`)
  - Round-robin arbiter for multiple requestors
  - Verification Properties:
    - Mutual exclusion
    - Fairness
    - No deadlock
    - Priority handling

## Formal Verification Approach

### 1. Safety Properties
Safety properties ensure that "bad things never happen". Examples:
- No conflicting outputs
- No buffer overflow/underflow
- Valid state transitions only

### 2. Liveness Properties
Liveness properties ensure that "good things eventually happen". Examples:
- Every request eventually gets served
- Operations complete in finite time
- Deadlock freedom

### 3. Cover Properties
Cover properties demonstrate reachability. Examples:
- All states are reachable
- Key scenarios can occur
- Corner cases are possible

### 4. Auxiliary Verification
Additional verification techniques:
- Assumptions for constraining inputs
- Assertions for checking invariants
- Witnesses for demonstrating behavior

## Using SymbiYosys

Each design has a corresponding `.sby` file in its formal verification directory. The file specifies:
1. Verification tasks (prove, cover)
2. Verification engine (usually smtbmc)
3. Source files and top module
4. Verification options and settings

Example `.sby` file structure:
```
[tasks]
prove
cover

[options]
prove: mode prove
cover: mode cover

[engines]
smtbmc z3

[script]
read -formal design.v
prep -top module_name

[files]
design.v
```

## Getting Started

1. Choose a design to verify
2. Review its formal properties in the source file
3. Examine the `.sby` configuration
4. Run verification using the Makefile:
   ```bash
   make formal_<design_name>
   ```
5. Analyze the results in the formal/<design_name> directory

## Common Verification Patterns

1. **Reset Verification**
   ```systemverilog
   property reset_check;
      @(posedge clk) !rst_n |-> output == '0;
   endproperty
   ```

2. **State Transition Safety**
   ```systemverilog
   property valid_transition;
      @(posedge clk) disable iff (!rst_n)
         current_state == STATE_A |=> 
         current_state inside {STATE_B, STATE_C};
   endproperty
   ```

3. **Request-Grant Properties**
   ```systemverilog
   property request_to_grant;
      @(posedge clk) disable iff (!rst_n)
         request |-> ##[0:3] grant;
   endproperty
   ```

4. **Mutual Exclusion**
   ```systemverilog
   property mutual_exclusion;
      @(posedge clk) disable iff (!rst_n)
         $onehot0(grant);
   endproperty
   ```