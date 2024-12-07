# Gentle Introduction to Formal Verification

These are my notes from the blog post [Gentle Introduction to Formal Verification](https://www.systemverilog.io/verification/gentle-introduction-to-formal-verification/).


# Key Points About Formal Verification

## What is Formal Verification?
- Alternative to functional simulation for finding bugs
- Uses SystemVerilog Assertions (SVA) for testbench, constraints, checkers and coverage
- Tool does mathematical analysis rather than simulation

## Formal vs Functional Simulation

### Functional Simulation:
- Manual testbench creation required:
  - Test cases for stimulus
  - Drivers/BFMs for injection
  - Monitors for output
  - Reference model
  - Checkers/scoreboard
- Tests one specific code path at a time
- Tool just simulates clock-by-clock

### Formal Verification:
- No drivers/monitors/test cases needed
- Uses:
  - SVA assume for input constraints
  - SVA assert for output checks
  - SVA cover for coverage
  - Minimal modeling code as needed
- Tool converts design to math equations and explores all paths
- Provides counter-examples for failures

## When to Use Formal Verification
- Best for sub-chip level verification
- Good candidates:
  - Critical/complex logic (caches, arbiters, state machines)
  - High-risk code sections needing extra verification
- Limited by design size - large state spaces may not converge

## Learning Resources
1. SystemVerilog Assertions Basics
2. Blueprint for Formal Verification
3. Textbook: "Formal Verification" by Erik Seligman
4. Paper: "Guidelines for Creating Formal Verification Testplan"
5. Paper: "Design Guidelines for Formal Verification"
6. Paper: "Sign-off with Bounded Formal Verification Proofs"
7. Textbook: "Applied Formal Verification" by Perry and Foster

## Getting Started
1. Start with small modules
2. Build simple formal testbench
3. Write cover properties
4. Practice with assertions
5. Study counter-examples
6. Progress to formal abstraction techniques