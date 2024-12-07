// Arithmetic Logic Unit (ALU)
// Formal Verification Properties to consider:
// 1. Operation correctness
// 2. Overflow detection
// 3. Zero flag accuracy
// 4. Negative flag accuracy
// 5. Invalid operation handling
// 6. Timing constraints

module alu #(
    parameter WIDTH = 32
) (
    input  logic                    clk,
    input  logic                    rst_n,
    input  logic [WIDTH-1:0]        a,
    input  logic [WIDTH-1:0]        b,
    input  logic [3:0]              op_code,
    output logic [WIDTH-1:0]        result,
    output logic                    zero_flag,
    output logic                    negative_flag,
    output logic                    overflow_flag,
    output logic                    error_flag
);

    // Operation codes
    localparam ADD  = 4'b0000;
    localparam SUB  = 4'b0001;
    localparam AND  = 4'b0010;
    localparam OR   = 4'b0011;
    localparam XOR  = 4'b0100;
    localparam SLL  = 4'b0101;  // Shift left logical
    localparam SRL  = 4'b0110;  // Shift right logical
    localparam SRA  = 4'b0111;  // Shift right arithmetic
    localparam MULT = 4'b1000;
    localparam DIV  = 4'b1001;
    
    // Internal signals
    logic [WIDTH-1:0]   add_sub_result;
    logic [WIDTH-1:0]   logic_result;
    logic [WIDTH-1:0]   shift_result;
    logic [2*WIDTH-1:0] mult_result;
    logic [WIDTH-1:0]   div_result;
    logic               div_by_zero;
    logic               add_overflow;
    logic               sub_overflow;
    
    // Addition/Subtraction with overflow detection
    always_comb begin
        // Two's complement overflow detection
        if (op_code == SUB) begin
            add_sub_result = a - b;
            sub_overflow = (a[WIDTH-1] != b[WIDTH-1]) && 
                          (add_sub_result[WIDTH-1] == b[WIDTH-1]);
        end else begin
            add_sub_result = a + b;
            add_overflow = (a[WIDTH-1] == b[WIDTH-1]) && 
                          (add_sub_result[WIDTH-1] != a[WIDTH-1]);
        end
    end
    
    // Logical operations
    always_comb begin
        case (op_code)
            AND: logic_result = a & b;
            OR:  logic_result = a | b;
            XOR: logic_result = a ^ b;
            default: logic_result = '0;
        endcase
    end
    
    // Shift operations
    always_comb begin
        case (op_code)
            SLL: shift_result = a << b[4:0];  // Use only 5 bits for 32-bit shifts
            SRL: shift_result = a >> b[4:0];
            SRA: shift_result = $signed(a) >>> b[4:0];
            default: shift_result = '0;
        endcase
    end
    
    // Multiplication
    assign mult_result = a * b;
    
    // Division
    assign div_by_zero = (op_code == DIV) && (b == '0);
    assign div_result = div_by_zero ? '1 : a / b;
    
    // Result multiplexing and flag generation
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            result <= '0;
            zero_flag <= 1'b0;
            negative_flag <= 1'b0;
            overflow_flag <= 1'b0;
            error_flag <= 1'b0;
        end else begin
            // Default error condition
            error_flag <= div_by_zero;
            
            // Result selection
            case (op_code)
                ADD, SUB: begin
                    result <= add_sub_result;
                    overflow_flag <= (op_code == ADD) ? add_overflow : sub_overflow;
                end
                
                AND, OR, XOR: begin
                    result <= logic_result;
                    overflow_flag <= 1'b0;
                end
                
                SLL, SRL, SRA: begin
                    result <= shift_result;
                    overflow_flag <= 1'b0;
                end
                
                MULT: begin
                    result <= mult_result[WIDTH-1:0];
                    overflow_flag <= |mult_result[2*WIDTH-1:WIDTH];
                end
                
                DIV: begin
                    result <= div_by_zero ? '1 : div_result;
                    overflow_flag <= 1'b0;
                end
                
                default: begin
                    result <= '0;
                    overflow_flag <= 1'b0;
                    error_flag <= 1'b1;  // Invalid op_code
                end
            endcase
            
            // Flag updates
            zero_flag <= (result == '0);
            negative_flag <= result[WIDTH-1];
        end
    end

    // Verification Properties
    // These are commented out but would be used in formal verification
    /*
    // Arithmetic operation correctness
    property add_correct;
        @(posedge clk) disable iff (!rst_n)
            (op_code == ADD) && !overflow_flag |-> 
            ##1 (result == $past(a) + $past(b));
    endproperty
    
    // Zero flag correctness
    property zero_flag_correct;
        @(posedge clk) disable iff (!rst_n)
            ##1 zero_flag == (result == '0);
    endproperty
    
    // Negative flag correctness
    property negative_flag_correct;
        @(posedge clk) disable iff (!rst_n)
            ##1 negative_flag == result[WIDTH-1];
    endproperty
    
    // Division by zero detection
    property div_by_zero_check;
        @(posedge clk) disable iff (!rst_n)
            (op_code == DIV) && ($past(b) == '0) |-> ##1 error_flag;
    endproperty
    */

endmodule 