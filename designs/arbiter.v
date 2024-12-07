// Round-Robin Arbiter
// Formal Verification Properties to consider:
// 1. Mutual exclusion: Only one grant active at a time
// 2. Fairness: Each requester eventually gets served
// 3. No deadlock or livelock
// 4. Priority handling
// 5. Reset behavior
// 6. Response timing

module arbiter #(
    parameter NUM_PORTS = 4
) (
    input  logic clk,
    input  logic rst_n,
    input  logic [NUM_PORTS-1:0] request,  // Request signals from clients
    output logic [NUM_PORTS-1:0] grant,    // Grant signals to clients
    output logic [$clog2(NUM_PORTS)-1:0] grant_id, // ID of currently granted request
    output logic valid_grant              // Indicates active grant
);

    // Internal registers
    logic [NUM_PORTS-1:0] priority_mask;  // Mask for round-robin priority
    logic [$clog2(NUM_PORTS)-1:0] last_grant;  // Last granted port
    
    // Masked requests for priority handling
    logic [NUM_PORTS-1:0] masked_request;
    logic [NUM_PORTS-1:0] masked_grant;
    logic [NUM_PORTS-1:0] unmasked_grant;
    
    // Compute masked requests
    assign masked_request = request & priority_mask;
    
    // Generate grant signals using priority encoder logic
    always_comb begin
        masked_grant = '0;
        unmasked_grant = '0;
        
        // First try masked requests (higher priority)
        if (|masked_request) begin
            for (int i = 0; i < NUM_PORTS; i++) begin
                if (masked_request[i]) begin
                    masked_grant[i] = 1'b1;
                    break;
                end
            end
        end
        // If no masked requests, try unmasked requests
        else if (|request) begin
            for (int i = 0; i < NUM_PORTS; i++) begin
                if (request[i]) begin
                    unmasked_grant[i] = 1'b1;
                    break;
                end
            end
        end
    end
    
    // Combine masked and unmasked grants
    assign grant = masked_grant | unmasked_grant;
    assign valid_grant = |grant;
    
    // Generate grant_id
    always_comb begin
        grant_id = '0;
        for (int i = 0; i < NUM_PORTS; i++) begin
            if (grant[i]) begin
                grant_id = i[$clog2(NUM_PORTS)-1:0];
            end
        end
    end
    
    // Update priority mask for round-robin behavior
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            priority_mask <= '1;  // All ports equal priority after reset
            last_grant <= '0;
        end else if (valid_grant) begin
            // Update last grant
            last_grant <= grant_id;
            
            // Generate new priority mask
            for (int i = 0; i < NUM_PORTS; i++) begin
                priority_mask[i] <= (i > last_grant) ? 1'b1 : 1'b0;
            end
        end else if (!(|request)) begin
            // If no requests, reset priority mask
            priority_mask <= '1;
        end
    end

    // Verification Properties
    // These are commented out but would be used in formal verification
    /*
    // Mutual exclusion: only one grant can be active
    property mutual_exclusion;
        @(posedge clk) disable iff (!rst_n)
            $onehot0(grant);
    endproperty
    
    // Fairness: a continuous request must eventually be granted
    property fairness;
        @(posedge clk) disable iff (!rst_n)
            for (int i = 0; i < NUM_PORTS; i++)
                request[i] |-> ##[0:NUM_PORTS] grant[i];
    endproperty
    
    // Valid grant implies request was active
    property grant_implies_request;
        @(posedge clk) disable iff (!rst_n)
            for (int i = 0; i < NUM_PORTS; i++)
                grant[i] |-> request[i];
    endproperty
    
    // Reset behavior
    property reset_behavior;
        @(posedge clk)
            !rst_n |-> (!valid_grant && (priority_mask == '1));
    endproperty
    */

endmodule 