// Traffic Light Controller FSM
// Formal Verification Properties to consider:
// 1. Safety: No conflicting green signals
// 2. Liveness: Each direction eventually gets green
// 3. Timing constraints adherence
// 4. Emergency override behavior
// 5. Reset behavior
// 6. No invalid state transitions

module traffic_light #(
    parameter CLOCK_FREQ = 100000000,  // 100 MHz
    parameter NS_GREEN_TIME = 30,      // 30 seconds
    parameter NS_YELLOW_TIME = 5,      // 5 seconds
    parameter EW_GREEN_TIME = 25,      // 25 seconds
    parameter EW_YELLOW_TIME = 5       // 5 seconds
) (
    input  logic clk,
    input  logic rst_n,
    input  logic emergency_vehicle,    // Emergency vehicle override
    
    // North-South signals
    output logic ns_red,
    output logic ns_yellow,
    output logic ns_green,
    
    // East-West signals
    output logic ew_red,
    output logic ew_yellow,
    output logic ew_green
);

    // Timing constants (clock cycles)
    localparam NS_GREEN_CYCLES  = NS_GREEN_TIME * CLOCK_FREQ;
    localparam NS_YELLOW_CYCLES = NS_YELLOW_TIME * CLOCK_FREQ;
    localparam EW_GREEN_CYCLES  = EW_GREEN_TIME * CLOCK_FREQ;
    localparam EW_YELLOW_CYCLES = EW_YELLOW_TIME * CLOCK_FREQ;
    
    // State definitions
    typedef enum logic [2:0] {
        NS_GREEN_STATE  = 3'b000,
        NS_YELLOW_STATE = 3'b001,
        NS_RED_STATE    = 3'b010,
        EW_GREEN_STATE  = 3'b011,
        EW_YELLOW_STATE = 3'b100,
        EW_RED_STATE    = 3'b101,
        EMERGENCY_STATE = 3'b110
    } state_t;
    
    // State registers
    state_t current_state, next_state;
    logic [$clog2($max(NS_GREEN_CYCLES, EW_GREEN_CYCLES))-1:0] timer;
    
    // State machine
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            current_state <= NS_RED_STATE;
            timer <= '0;
        end else begin
            current_state <= next_state;
            
            // Timer logic
            if (next_state != current_state) begin
                timer <= '0;
            end else begin
                timer <= timer + 1;
            end
        end
    end
    
    // Next state logic
    always_comb begin
        next_state = current_state;
        
        if (emergency_vehicle && current_state != EMERGENCY_STATE) begin
            next_state = EMERGENCY_STATE;
        end else begin
            case (current_state)
                NS_GREEN_STATE: begin
                    if (timer >= NS_GREEN_CYCLES) begin
                        next_state = NS_YELLOW_STATE;
                    end
                end
                
                NS_YELLOW_STATE: begin
                    if (timer >= NS_YELLOW_CYCLES) begin
                        next_state = NS_RED_STATE;
                    end
                end
                
                NS_RED_STATE: begin
                    next_state = EW_GREEN_STATE;
                end
                
                EW_GREEN_STATE: begin
                    if (timer >= EW_GREEN_CYCLES) begin
                        next_state = EW_YELLOW_STATE;
                    end
                end
                
                EW_YELLOW_STATE: begin
                    if (timer >= EW_YELLOW_CYCLES) begin
                        next_state = EW_RED_STATE;
                    end
                end
                
                EW_RED_STATE: begin
                    next_state = NS_GREEN_STATE;
                end
                
                EMERGENCY_STATE: begin
                    if (!emergency_vehicle) begin
                        next_state = NS_RED_STATE;
                    end
                end
                
                default: next_state = NS_RED_STATE;
            endcase
        end
    end
    
    // Output logic
    always_comb begin
        // Default all lights to red
        ns_red = 1'b1;
        ns_yellow = 1'b0;
        ns_green = 1'b0;
        ew_red = 1'b1;
        ew_yellow = 1'b0;
        ew_green = 1'b0;
        
        case (current_state)
            NS_GREEN_STATE: begin
                ns_red = 1'b0;
                ns_green = 1'b1;
            end
            
            NS_YELLOW_STATE: begin
                ns_red = 1'b0;
                ns_yellow = 1'b1;
            end
            
            EW_GREEN_STATE: begin
                ew_red = 1'b0;
                ew_green = 1'b1;
            end
            
            EW_YELLOW_STATE: begin
                ew_red = 1'b0;
                ew_yellow = 1'b1;
            end
            
            EMERGENCY_STATE: begin
                ns_red = 1'b0;
                ns_green = 1'b1;
            end
            
            default: begin
                // All reds (already set above)
            end
        endcase
    end

endmodule 