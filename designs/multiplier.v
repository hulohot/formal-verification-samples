// Sequential Multiplier using shift-and-add algorithm
// Formal Verification Properties to consider:
// 1. Result correctness: product == multiplicand * multiplier
// 2. Overflow detection
// 3. Operation completion timing
// 4. Reset behavior
// 5. Busy flag consistency

module multiplier #(
    parameter WIDTH = 8
) (
    input  logic                clk,
    input  logic                rst_n,
    input  logic                start,      // Start multiplication
    input  logic [WIDTH-1:0]    a,          // Multiplicand
    input  logic [WIDTH-1:0]    b,          // Multiplier
    output logic [2*WIDTH-1:0]  product,    // Final product
    output logic                busy,       // Multiplication in progress
    output logic                done        // Multiplication complete
);

    // Internal registers
    logic [WIDTH-1:0]     multiplicand;
    logic [WIDTH-1:0]     multiplier;
    logic [2*WIDTH-1:0]   acc;
    logic [$clog2(WIDTH)-1:0] count;

    // State definitions
    typedef enum logic [1:0] {
        IDLE    = 2'b00,
        CALC    = 2'b01,
        FINISH  = 2'b10
    } state_t;

    state_t state, next_state;

    // State machine and datapath
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            multiplicand <= '0;
            multiplier <= '0;
            acc <= '0;
            count <= '0;
            product <= '0;
            busy <= 1'b0;
            done <= 1'b0;
        end else begin
            state <= next_state;
            
            case (state)
                IDLE: begin
                    if (start) begin
                        multiplicand <= a;
                        multiplier <= b;
                        acc <= '0;
                        count <= '0;
                        busy <= 1'b1;
                        done <= 1'b0;
                    end
                end

                CALC: begin
                    if (multiplier[0]) begin
                        acc <= acc + (multiplicand << count);
                    end
                    multiplier <= multiplier >> 1;
                    count <= count + 1;
                end

                FINISH: begin
                    product <= acc;
                    busy <= 1'b0;
                    done <= 1'b1;
                end

                default: begin
                    state <= IDLE;
                end
            endcase
        end
    end

    // Next state logic
    always_comb begin
        next_state = state;
        
        case (state)
            IDLE: begin
                if (start) next_state = CALC;
            end
            
            CALC: begin
                if (count == WIDTH-1) next_state = FINISH;
            end
            
            FINISH: begin
                next_state = IDLE;
            end
            
            default: next_state = IDLE;
        endcase
    end

endmodule 