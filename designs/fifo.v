// Synchronous FIFO with configurable depth and width
// Formal Verification Properties to consider:
// 1. Full/Empty flags correctness
// 2. Data integrity: First-In-First-Out behavior
// 3. No data loss during simultaneous read/write
// 4. Reset behavior
// 5. Overflow/Underflow protection
// 6. Gray code pointer crossing

module fifo #(
    parameter WIDTH = 8,
    parameter DEPTH = 16,
    parameter ALMOST_FULL_THRESHOLD = DEPTH - 2,
    parameter ALMOST_EMPTY_THRESHOLD = 2
) (
    input  logic              clk,
    input  logic              rst_n,
    
    // Write interface
    input  logic              wr_en,
    input  logic [WIDTH-1:0]  wr_data,
    output logic              full,
    output logic              almost_full,
    
    // Read interface
    input  logic              rd_en,
    output logic [WIDTH-1:0]  rd_data,
    output logic              empty,
    output logic              almost_empty,
    
    // Status
    output logic [$clog2(DEPTH):0] fill_level
);

    // Local parameters
    localparam ADDR_WIDTH = $clog2(DEPTH);
    
    // Internal signals
    logic [WIDTH-1:0]      mem [DEPTH-1:0];
    logic [ADDR_WIDTH:0]   wr_ptr;      // One extra bit for full/empty detection
    logic [ADDR_WIDTH:0]   rd_ptr;      // One extra bit for full/empty detection
    logic [ADDR_WIDTH-1:0] wr_addr;
    logic [ADDR_WIDTH-1:0] rd_addr;
    
    // Derived signals
    assign wr_addr = wr_ptr[ADDR_WIDTH-1:0];
    assign rd_addr = rd_ptr[ADDR_WIDTH-1:0];
    
    // Status flags
    assign empty = (wr_ptr == rd_ptr);
    assign full  = (wr_ptr[ADDR_WIDTH-1:0] == rd_ptr[ADDR_WIDTH-1:0]) && 
                  (wr_ptr[ADDR_WIDTH] != rd_ptr[ADDR_WIDTH]);
    
    // Fill level calculation
    always_comb begin
        if (wr_ptr[ADDR_WIDTH] == rd_ptr[ADDR_WIDTH]) begin
            fill_level = wr_ptr[ADDR_WIDTH-1:0] - rd_ptr[ADDR_WIDTH-1:0];
        end else begin
            fill_level = DEPTH - (rd_ptr[ADDR_WIDTH-1:0] - wr_ptr[ADDR_WIDTH-1:0]);
        end
    end
    
    // Almost full/empty flags
    assign almost_full  = (fill_level >= ALMOST_FULL_THRESHOLD);
    assign almost_empty = (fill_level <= ALMOST_EMPTY_THRESHOLD);
    
    // Write logic
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            wr_ptr <= '0;
        end else if (wr_en && !full) begin
            mem[wr_addr] <= wr_data;
            wr_ptr <= wr_ptr + 1;
        end
    end
    
    // Read logic
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rd_ptr <= '0;
            rd_data <= '0;
        end else if (rd_en && !empty) begin
            rd_data <= mem[rd_addr];
            rd_ptr <= rd_ptr + 1;
        end
    end

endmodule 