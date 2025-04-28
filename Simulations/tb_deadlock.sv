module tb_deadlock;
  
  localparam IDLE = 2'b00;
  localparam DONE = 2'b11;
  
  // Interface signals for the DUT.
  logic i_clk;
  logic i_rst;
  logic [127:0] i_key;
  logic i_axis_valid_s;
  logic o_axis_ready_s;
  logic [63:0] i_axis_data_s;
  logic o_axis_valid_m;
  logic i_axis_ready_m;
  logic [63:0] o_axis_data_m;
  
  // DUT instantiation 
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

  // Property 1: Every encryption request (when DUT is in IDLE with i_axis_valid_s asserted)
  // must complete within 40 cycles by eventually reaching the DONE state.
  property complete_run;
    @(posedge i_clk) disable iff (i_rst)
      (dut.state == IDLE && i_axis_valid_s) |-> ##[1:40] (dut.state == DONE);
  endproperty
  assert property (complete_run);
  
  // Property 2: Once the accelerator reaches DONE, it should return to IDLE within 40 cycles.
  property reset_run;
    @(posedge i_clk) disable iff (i_rst)
      (dut.state == DONE) |-> ##[1:40] (dut.state == IDLE);
  endproperty
  assert property (reset_run);
  
endmodule
