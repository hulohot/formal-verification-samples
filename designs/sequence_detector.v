// Sequence Detector FSM
// Detects the pattern "1011" in a serial input stream
// Formal Verification Properties to consider:
// 1. Pattern detection correctness
// 2. No false positives
// 3. Overlapping sequence handling
// 4. Reset behavior
// 5. State reachability
// 6. Timing of detection signal

module sequence_detector (
    input  logic clk,
    input  logic rst_n,
    input  logic data_in,      // Serial input data
    input  logic valid_in,     // Input data valid signal
    output logic pattern_detected,
    output logic [2:0] current_state_out  // For debugging/verification
);

    // State definitions
    typedef enum logic [2:0] {
        IDLE    = 3'b000,  // Waiting for first '1'
        GOT_1   = 3'b001,  // Received first '1'
        GOT_10  = 3'b010,  // Received '10'
        GOT_101 = 3'b011,  // Received '101'
        FOUND   = 3'b100   // Found complete pattern
    } state_t;
    
    // State registers
    state_t current_state, next_state;
    
    // Output current state for verification
    assign current_state_out = current_state;
    
    // State machine sequential logic
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            current_state <= IDLE;
            pattern_detected <= 1'b0;
        end else begin
            if (valid_in) begin
                current_state <= next_state;
                pattern_detected <= (next_state == FOUND);
            end
        end
    end
    
    // Next state combinational logic
    always_comb begin
        next_state = current_state;
        
        if (valid_in) begin
            case (current_state)
                IDLE: begin
                    if (data_in) begin
                        next_state = GOT_1;
                    end
                end
                
                GOT_1: begin
                    if (!data_in) begin
                        next_state = GOT_10;
                    end else begin
                        next_state = GOT_1;  // Stay in GOT_1 for overlapping sequences
                    end
                end
                
                GOT_10: begin
                    if (data_in) begin
                        next_state = GOT_101;
                    end else begin
                        next_state = IDLE;
                    end
                end
                
                GOT_101: begin
                    if (data_in) begin
                        next_state = FOUND;
                    end else begin
                        next_state = GOT_10;  // Potential overlap case
                    end
                end
                
                FOUND: begin
                    if (data_in) begin
                        next_state = GOT_1;
                    end else begin
                        next_state = IDLE;
                    end
                end
                
                default: next_state = IDLE;
            endcase
        end
    end

    // Verification Properties
    // These are commented out but would be used in formal verification
    /*
    // Safety: pattern_detected should only be high when pattern is found
    property pattern_detected_valid;
        @(posedge clk) disable iff (!rst_n)
            pattern_detected |-> (current_state == FOUND);
    endproperty
    
    // Liveness: pattern should eventually be detected if present
    property pattern_eventually_detected;
        @(posedge clk) disable iff (!rst_n)
            (data_in && valid_in) ##1 (!data_in && valid_in) ##1 
            (data_in && valid_in) ##1 (data_in && valid_in)
            |-> ##[0:1] pattern_detected;
    endproperty
    
    // Reset behavior
    property reset_behavior;
        @(posedge clk)
            !rst_n |-> (current_state == IDLE && !pattern_detected);
    endproperty
    */

endmodule 