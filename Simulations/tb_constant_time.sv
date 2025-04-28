module tea_constant_time;
  
  localparam DONE = 2'b11;
  localparam IDLE = 2'b00;
  
  // Declare clock, reset, and DUT interface signals.
  // For formal verification, the clock is left unconstrained.
  logic i_clk, i_rst;
  logic [127:0] i_key;
  logic i_axis_valid_s;
  logic o_axis_ready_s;
  logic [63:0] i_axis_data_s;
  logic o_axis_valid_m;
  logic i_axis_ready_m;
  logic [63:0] o_axis_data_m;
  
  // Instantiate the accelerator DUT.
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
  
  // ---- Assumptions for the Environment ----
  // (1) Downstream is always ready.
  // (2) Whenever the DUT is in IDLE, the upstream always provides a valid input.
  //     This forces the design to leave IDLE and execute a full encryption run.
  assume property (@(posedge i_clk) disable iff(i_rst)
    (dut.state == IDLE) |-> (i_axis_valid_s == 1)
  );

  // Optionally, you could also assume that o_axis_ready_s remains high to ensure acceptance.
  assume property (@(posedge i_clk) disable iff(i_rst)
    o_axis_ready_s == 1
  );
  
  // ---- Input Stimulus ----
  // In a formal setting, leaving i_key and i_axis_data_s unconstrained
  // forces the tool to consider all possible secret inputs.
  // We do drive i_axis_valid_s in an always block according to the DUT state:
  always @(posedge i_clk) begin
    if (dut.state == IDLE)
      i_axis_valid_s <= 1;
    else
      i_axis_valid_s <= 0;
  end
  
  // Downstream is assumed always ready.
  // (This could alternatively be an assumption if left unconstrained.)
  initial begin
    i_axis_ready_m = 1;
  end
  
  // Reset and initial signal settings.
  initial begin
    i_rst = 1;
    // Let i_key and i_axis_data_s remain unconstrained for formal analysis.
    i_axis_valid_s = 0;
    #20;
    i_rst = 0;
  end
  
  // ---- Constant-Time Property ----
  // We want to prove that every encryption run requires exactly 32 processing cycles.
  // Since the accelerator resets round_counter to 0 in IDLE and then
  // increments it in each cycle of the PROCESSING state,
  // when the accelerator reaches DONE the round_counter should be 31.
  property constant_time_property;
    @(posedge i_clk) disable iff (i_rst)
      (dut.state == DONE) |-> (dut.round_counter == 31);
  endproperty

  // Assert the property.
  assert property (constant_time_property);
  
endmodule
