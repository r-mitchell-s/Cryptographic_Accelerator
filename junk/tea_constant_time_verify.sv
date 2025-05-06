module tea_constant_time_verify(
    input logic i_clk,
    input logic i_rst
);
    // Declare signals to connect to the DUT
    logic [127:0] key;
    logic axis_valid_s;
    logic axis_ready_s;
    logic [63:0] axis_data_s;
    logic axis_valid_m;
    logic axis_ready_m;
    logic [63:0] axis_data_m;
    
    // Instantiate the TEA accelerator
    tea_accelerator dut (
        .i_clk(i_clk),
        .i_rst(i_rst),
        .i_key(key),
        .i_axis_valid_s(axis_valid_s),
        .o_axis_ready_s(axis_ready_s),
        .i_axis_data_s(axis_data_s),
        .o_axis_valid_m(axis_valid_m),
        .i_axis_ready_m(axis_ready_m),
        .o_axis_data_m(axis_data_m)
    );
    
    // Connect to design signals
    wire [1:0] state;
    wire [4:0] round_counter;
    
    assign state = dut.state;
    assign round_counter = dut.round_counter;
    
    // Fixed test inputs
    assign key = 128'h00000000_00000000_00000000_00000001;
    assign axis_data_s = 64'h0000000000000001;
    
    // Control signals to ensure proper execution
    always_ff @(posedge i_clk) begin
        if (i_rst) begin
            axis_valid_s <= 1;
            axis_ready_m <= 0;
        end
        else begin
            // Once output is valid, accept it
            if (axis_valid_m)
                axis_ready_m <= 1;
                
            // Once data is accepted by the DUT, stop sending new data
            if (!axis_ready_s)
                axis_valid_s <= 0;
        end
    end
    
    // State transition tracking to verify constant time
    logic processing_started;
    logic [5:0] processing_cycles;
    
    always_ff @(posedge i_clk) begin
        if (i_rst) begin
            processing_started <= 0;
            processing_cycles <= 0;
        end
        else if (state == dut.PROCESSING) begin
            processing_started <= 1;
            processing_cycles <= processing_cycles + 1;
        end
        else if (state == dut.DONE && processing_started) begin
            // Verification point 1: PROCESSING took exactly 32 cycles
            assert(processing_cycles == 32);
            processing_started <= 0;
            processing_cycles <= 0;
        end
    end
    
    // Track the expected round counter value
    logic [4:0] expected_counter;
    
    always_ff @(posedge i_clk) begin
        if (i_rst) begin
            expected_counter <= 0;
        end
        else if (state == dut.LOADING) begin
            // Reset counter when entering PROCESSING state
            expected_counter <= 0;
        end
        else if (state == dut.PROCESSING) begin
            expected_counter <= expected_counter + 1;
        end
    end
    
    // Verification 1: Round counter increases deterministically
    // Allow for initialization cycle difference
    assert property(@(posedge i_clk) disable iff (i_rst)
        (state == dut.PROCESSING && expected_counter > 0) -> 
        (round_counter == expected_counter));
    
    // Verification 2: Processing state only transitions to DONE after 32 rounds
    assert property(@(posedge i_clk) disable iff (i_rst)
        (state == dut.DONE && processing_started) -> 
        (processing_cycles == 32));
    
    // Cover property to ensure design reaches completion
    cover property(@(posedge i_clk) state == dut.DONE);
endmodule