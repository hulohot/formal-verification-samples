`default_nettype none
`timescale 1ns/1ps

module adder #(
    parameter WIDTH = 8
) (
    input  logic [WIDTH-1:0] a,
    input  logic [WIDTH-1:0] b,
    input  logic            cin,
    output logic [WIDTH-1:0] sum,
    output logic            cout
);

    logic [WIDTH:0] temp;  // Extra bit for carry
    
    assign temp = a + b + cin;
    assign sum  = temp[WIDTH-1:0];
    assign cout = temp[WIDTH];

`ifdef FORMAL
    // Past value tracking for cover properties
    reg first_cycle = 1'b1;
    always @(*) begin
        if ($initstate)
            first_cycle <= 1'b1;
        else
            first_cycle <= 1'b0;
    end

    // Basic correctness properties
    always @(*) begin
        // Addition correctness
        assert(temp == {cout, sum});
        assert({cout, sum} == a + b + cin);
    end

    // Overflow detection
    wire overflow = (a[WIDTH-1] == b[WIDTH-1]) && (sum[WIDTH-1] != a[WIDTH-1]);
    
    // Carry propagation properties
    always @(*) begin
        // Carry out is 1 if and only if the true sum exceeds maximum value
        assert(cout == ((a + b + cin) > {WIDTH{1'b1}}));
    end

    // Corner case properties
    always @(*) begin
        // Maximum value cases
        if (a == {WIDTH{1'b1}} && b == {WIDTH{1'b1}} && cin == 1'b1) begin
            assert(cout == 1'b1);
            assert(sum == {WIDTH{1'b1}});
        end
        
        // Zero cases
        if (a == 0 && b == 0 && cin == 0) begin
            assert(cout == 1'b0);
            assert(sum == 0);
        end
    end

    // Cover properties to verify interesting scenarios
    always @(*) begin
        // Cover normal addition
        cover(!first_cycle && !cout && !overflow);
        
        // Cover carry out generation
        cover(!first_cycle && cout);
        
        // Cover overflow condition
        cover(!first_cycle && overflow);
        
        // Cover maximum value addition
        cover(!first_cycle && a == {WIDTH{1'b1}} && b == {WIDTH{1'b1}});
        
        // Cover zero addition
        cover(!first_cycle && a == 0 && b == 0 && cin == 0);
        
        // Cover interesting patterns
        cover(!first_cycle && a == b);  // Adding same numbers
        cover(!first_cycle && sum == 0 && (a != 0 || b != 0 || cin != 0));  // Result zero but inputs non-zero
    end

    // Assumptions about inputs
    always @(*) begin
        // No assumptions needed for basic adder
        // But you might want to add constraints for specific verification scenarios
        assume(WIDTH > 1);  // Ensure meaningful width
    end

`endif

endmodule

// A binary adder is a digital circuit that performs addition of binary numbers. 
// It is a fundamental building block in digital design. 
// The carry-in (cin) and carry-out (cout) signals are used to chain multiple adders together to add numbers larger than the adder's width.