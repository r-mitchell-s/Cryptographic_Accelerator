// - - - - - DATA INDEPENDENT CONTROL FLOW SUBPROPERTY - - - - - //

module tb_formal_data_independent_control_flow;

  // state parameters 
  localparam IDLE      = 2'b00;
  localparam LOADING   = 2'b01;
  localparam PROCESSING = 2'b10;
  localparam DONE      = 2'b11;

  // DUT interface
  logic i_clk, i_rst;
  logic [127:0] i_key;
  logic i_axis_valid_s;
  logic o_axis_ready_s;
  logic [63:0] i_axis_data_s;
  logic o_axis_valid_m;
  logic i_axis_ready_m;
  logic [63:0] o_axis_data_m;

  // DUT instantuation
  tea_accelerator dut (
    .i_clk(i_clk), 
    .i_rst(i_rst),
    .i_key(i_key),
    .i_axis_valid_s(i_axis_valid_s), 
    .o_axis_ready_s(o_axis_ready_s),
    .i_axis_data_s(i_axis_data_s),
    .o_axis_valid_m(o_axis_valid_m), 
    .i_axis_ready_m(i_axis_ready_m),
    .o_axis_data_m(o_axis_data_m)
  );

	property idle_transition_data_independent;
	  @(posedge i_clk) disable iff(i_rst)
  	  (dut.state == IDLE) |-> 
    	  (dut.next_state == ((i_axis_valid_s && o_axis_ready_s) ? LOADING : IDLE));
	endproperty
	assert property(idle_transition_data_independent);

	property loading_transition_data_independent;
		@(posedge i_clk) disable iff(i_rst)
			(dut.state == LOADING) |-> (dut.next_state == PROCESSING);
	endproperty
	assert property(loading_transition_data_independent);

	property processing_transitions_data_independent;
  @(posedge i_clk) disable iff(i_rst)
    (dut.state == PROCESSING) |-> 
      (dut.next_state == (dut.round_counter >= 31 ? DONE : PROCESSING));
	endproperty
	assert property(processing_transitions_data_independent);

	property done_transition_data_independent;
		@(posedge i_clk) disable iff(i_rst)
			(dut.state == DONE) |-> 
				(dut.next_state == ((o_axis_valid_m && i_axis_ready_m) ? IDLE : DONE));
	endproperty
	assert property(done_transition_data_independent);
endmodule