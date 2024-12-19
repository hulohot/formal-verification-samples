// Arithmetic Logic Unit (ALU)
module alu #(
    parameter WIDTH = 32
) (
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
    localparam SLL  = 4'b0101;
    localparam SRL  = 4'b0110;
    localparam SRA  = 4'b0111;
    localparam MULT = 4'b1000;
    localparam DIV  = 4'b1001;
    
    // Internal signals for flag generation
    logic               add_overflow;
    logic               sub_overflow;
    logic               div_by_zero;
    logic [2*WIDTH-1:0] mult_temp;
    
    // Multiplication result
    assign mult_temp = a * b;
    
    // Combinational result calculation
    always_comb begin
        // Default values
        result = '0;
        add_overflow = 1'b0;
        sub_overflow = 1'b0;
        div_by_zero = (op_code == DIV) && (b == '0);
        
        case (op_code)
            ADD: begin
                result = a + b;
                add_overflow = (a[WIDTH-1] == b[WIDTH-1]) && 
                              (result[WIDTH-1] != a[WIDTH-1]);
            end
            SUB: begin
                result = a - b;
                sub_overflow = (a[WIDTH-1] != b[WIDTH-1]) && 
                              (result[WIDTH-1] == b[WIDTH-1]);
            end
            AND: result = a & b;
            OR:  result = a | b;
            XOR: result = a ^ b;
            SLL: result = a << b[4:0];
            SRL: result = a >> b[4:0];
            SRA: result = $signed(a) >>> b[4:0];
            MULT: result = mult_temp[WIDTH-1:0];
            DIV: result = div_by_zero ? {WIDTH{1'b1}} : a / b;
            default: result = '0;
        endcase
    end
    
    // Combinational flag updates
    always_comb begin
        // Update flags based on current result and operation
        zero_flag = (result == '0);
        negative_flag = result[WIDTH-1];
        
        case (op_code)
            ADD:  overflow_flag = add_overflow;
            SUB:  overflow_flag = sub_overflow;
            MULT: overflow_flag = |mult_temp[2*WIDTH-1:WIDTH];
            default: overflow_flag = 1'b0;
        endcase
        
        error_flag = (op_code == DIV && div_by_zero) || 
                     (op_code > DIV);  // Invalid opcode
    end

`ifdef FORMAL
    // Combinational operation verification
    always_comb begin
        case (op_code)
            ADD: begin
                assert(result == a + b);
                assert(add_overflow == ((a[WIDTH-1] == b[WIDTH-1]) && 
                                      (result[WIDTH-1] != a[WIDTH-1])));
            end
            SUB: begin
                assert(result == a - b);
                assert(sub_overflow == ((a[WIDTH-1] != b[WIDTH-1]) && 
                                      (result[WIDTH-1] == b[WIDTH-1])));
            end
            AND: assert(result == (a & b));
            OR:  assert(result == (a | b));
            XOR: assert(result == (a ^ b));
            SLL: assert(result == (a << b[4:0]));
            SRL: assert(result == (a >> b[4:0]));
            MULT: assert(result == mult_temp[WIDTH-1:0]);
            DIV: begin
                assert(div_by_zero == (b == 0));
                if (!div_by_zero) begin
                    assert(result == a / b);
                end else begin
                    assert(result == {WIDTH{1'b1}});
                end
            end
        endcase
    end

    // Flag verification
    always_comb begin
        // Flag correctness
        assert(zero_flag == (result == 0));
        assert(negative_flag == result[WIDTH-1]);
        
        case (op_code)
            ADD: assert(overflow_flag == add_overflow);
            SUB: assert(overflow_flag == sub_overflow);
            MULT: assert(overflow_flag == |mult_temp[2*WIDTH-1:WIDTH]);
            DIV: assert(error_flag == div_by_zero);
            default: begin
                assert(!overflow_flag);
                if (op_code > DIV) begin
                    assert(error_flag);
                end
            end
        endcase
    end

    // Cover properties
    always_comb begin
        // Basic operations
        cover(op_code == ADD && !add_overflow);
        cover(op_code == SUB && !sub_overflow);
        cover(op_code == AND);
        cover(op_code == OR);
        cover(op_code == XOR);
        cover(op_code == MULT && !overflow_flag);
        cover(op_code == DIV && !div_by_zero);
        
        // Error conditions
        cover(op_code == DIV && div_by_zero);
        cover(op_code > DIV);  // Invalid opcode
    end
`endif

endmodule 