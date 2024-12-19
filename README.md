# Formal Verification Learning Examples

This repository contains a collection of SystemVerilog designs specifically created for learning formal verification techniques using [SymbiYosys](https://github.com/YosysHQ/sby).

## Project Structure

```
formal-verification-samples/
├── designs/            # RTL design files
├── formal/            # Formal verification files
│   ├── adder/        # Verification for adder
│   ├── alu/          # Verification for ALU
│   ├── arbiter/      # Verification for arbiter
│   └── ...
├── tests/            # Traditional simulation testbenches
├── scripts/          # Utility scripts
└── Makefile          # Build system
```

## Prerequisites

- [Yosys](https://github.com/YosysHQ/yosys)
- [SymbiYosys](https://github.com/YosysHQ/sby)
- [Z3 Prover](https://github.com/Z3Prover/z3)
- [Verilator](https://www.veripool.org/verilator/) (optional, for simulation)

## Getting Started

1. Clone the repository:
   ```bash
   git clone https://github.com/yourusername/formal-verification-samples.git
   cd formal-verification-samples
   ```

2. Run formal verification on all designs:
   ```bash
   make formal
   ```

3. Run formal verification on a specific design:
   ```bash
   make formal_adder    # Verify adder
   make formal_alu      # Verify ALU
   make formal_arbiter  # Verify arbiter
   # etc...
   ```

4. Run simulation tests (if available):
   ```bash
   make sim
   ```

5. Clean build artifacts:
   ```bash
   make clean
   ```

## Formal Verification Examples

Each design in the `designs/` directory has corresponding formal verification files in the `formal/` directory. The verification files include:

- `.sby` configuration files
- Formal properties and assertions
- Cover statements for checking reachability
- Auxiliary verification logic

For example, to verify the adder:
bash
cd formal/adder
sby -f adder.sby
```

## Available Designs

See [instructions.md](instructions.md) for a complete list of designs and their verification challenges.

## Contributing

1. Fork the repository
2. Create your feature branch (`git checkout -b feature/amazing-verification`)
3. Commit your changes (`git commit -am 'Add some amazing verification'`)
4. Push to the branch (`git push origin feature/amazing-verification`)
5. Create a new Pull Request

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.
```