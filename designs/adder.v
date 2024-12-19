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
    // Basic correctness properties
    always @(*) begin
        // The sum and carry out should match the full addition
        assert(temp == {cout, sum});
        
        // Carry out should be set when sum overflows
        assert(cout == ((a + b + cin) >= (1 << WIDTH)));
        
        // Zero input case
        if (a == 0 && b == 0 && cin == 0) begin
            assert(sum == 0);
            assert(cout == 0);
        end
    end

    // Cover properties for interesting cases
    always @(*) begin
        // Cover a basic addition without carry
        cover(cout == 0);
        
        // Cover a case that generates carry
        cover(cout == 1);
        
        // Cover zero case
        cover(a == 0 && b == 0 && cin == 0);
        
        // Cover maximum value case
        cover(a == {WIDTH{1'b1}} && b == {WIDTH{1'b1}});
    end

`endif

endmodule
