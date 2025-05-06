module tea_properties(
    input logic i_clk,
    input logic i_rst,
    input logic [1:0] state,
    input logic [1:0] next_state,
    input logic [4:0] round_counter,
    input logic i_axis_valid_s,
    input logic o_axis_ready_s,
    input logic o_axis_valid_m,
    input logic i_axis_ready_m
);
    // State definitions for readability
    localparam IDLE = 2'b00;
    localparam LOADING = 2'b01;
    localparam PROCESSING = 2'b10;
    localparam DONE = 2'b11;
    
    // Property 1: Fixed state transition sequence
    property fixed_state_sequence;
        @(posedge i_clk) disable iff (i_rst)
        (state == IDLE && i_axis_valid_s && o_axis_ready_s) |-> 
        ##1 (state == LOADING) ##1 (state == PROCESSING)[*32] ##1 (state == DONE);
    endproperty
    assert property (fixed_state_sequence);
    
    // Property 2: Data-independent processing state transitions
    property data_independent_state_transition;
        @(posedge i_clk) disable iff (i_rst)
        (state == PROCESSING) |-> (next_state == ((round_counter >= 31) ? DONE : PROCESSING));
    endproperty
    assert property (data_independent_state_transition);
    
    // Property 3: Consistent processing rounds
    property fixed_round_count;
        @(posedge i_clk) disable iff (i_rst)
        (state == LOADING) |-> 
        ##1 (round_counter == 0) ##32 (round_counter == 31) ##1 (state == DONE);
    endproperty
    assert property (fixed_round_count);

endmodule