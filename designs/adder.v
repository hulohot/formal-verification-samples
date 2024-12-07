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

endmodule
