**Summary of Formal Verification for Verilog**

From the Youtube video [Very Basic Introduction to Formal Verification](https://www.youtube.com/watch?v=9e7F1XhjhKw).

Formal verification mathematically proves the correctness of a hardware design. Here are the key concepts:

1. Bounded Model Checking (BMC)
   - Verifies a design within a limited number of clock cycles.
   - Checks if the design's behavior aligns with specified properties in all possible input combinations within that limit.

2. Proving (Induction)
   - Proves a property holds inductively by assuming it's true at some point and then proving it remains true for all subsequent states.
   - Requires defining assumptions and induction steps to guide the prover.

3. Covering
   - Identifies a specific state and finds input sequences that lead to that state.
   - Useful for testing complex designs with multiple possible paths.

4. Implementation
   - Use open-source tools like Yosys and Symbiosis for free verification.
   - Define assertions to specify desired properties within the formal module.
   - Include signal connections and configure the verification task in a configuration file.

**Example: Binary Counter Verification**

Verify a 64-bit subtractor using BMC, asserting that the output is equal to A minus B.
Include a cover statement to find input sequences that result in a specific output state.

**Example: Clocked Register Verification**

Verify a clock-driven register using induction, asserting that the register value remains valid on each positive clock edge.
Use the past valid mechanism to ensure past values are appropriately initialized.

**Additional Resources**

- ZipCPU blog on Formal Verification
- Yosys and Symbiosis One Pager

**Summary in Bullet Points**

- 📝 Verify Hardware Correctness: Mathematically prove that a hardware design meets specifications.
- ✅ Bounded Model Checking: Ensure design behaves as expected within a limited number of clock cycles.
- 🔄 Proving (Induction): Inductively prove a property holds in all states.
- 🎯 Covering: Find input sequences that lead to specific states.
- 🛠️ Open-Source Tools: Use Yosys and Symbiosis for free verification.
- 🤔 Example: Binary Counter: Verify a subtractor using BMC and cover.
- ⏰ Example: Clocked Register: Verify a register using induction.