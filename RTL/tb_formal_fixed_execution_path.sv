// - - - - - STATE TRANSITION ORDERING SUBPROPERTY - - - - - //

// The following testbench unboundeldly verifies the fixed execution path subproperty (covering staet transitions)
// in the RTL accelerator. Making the proper exceptions for reset states and backpressure due to incomplete 
// handshaking, the properties in this testbench assert that given a current state, the transition to the next
// is determined in a fixed order that does not change as a result of the secret inputs (plaintext and key)
// of course state transition reording due to system reset is allowed.

module tb_formal_fixed_execution_path;

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

  // Property 1: when the DUT is in IDLE, the following state must be IDLE if no handshake, and LOADING if a successful handshake occurs
  property idle_to_loading;
    @(posedge i_clk) disable iff (i_rst)
      (dut.state == IDLE) |-> ((i_axis_valid_s && o_axis_ready_s)
                                ? (dut.next_state == LOADING)
                                : (dut.next_state == IDLE));
  endproperty
  assert property (idle_to_loading);

  // Property 2: when the DUT is in LOADING, next_state must always become PROCESSING, except when interrupted by reset
  property loading_to_processing;
    @(posedge i_clk) disable iff (i_rst)
      (dut.state == LOADING) |-> (dut.next_state == PROCESSING);
  endproperty
  assert property (loading_to_processing);

  // Property 3: In PROCESSING, the DUT should remain in PROCESSING until enough rounds have been executed.
  // That is, if round_counter < 31, then next_state remains PROCESSING.
  // Once round_counter is at least 31, next_state should be DONE.
  property processing_to_done;
    @(posedge i_clk) disable iff (i_rst)
      (dut.state == PROCESSING) |-> ((dut.round_counter >= 31)
                                       ? (dut.next_state == DONE)
                                       : (dut.next_state == PROCESSING));
  endproperty
  assert property (processing_to_done);

  // Property 4: In DONE, if the handshake indicates output is accepted (o_axis_valid_m && i_axis_ready_m),
  // then next_state should be IDLE; otherwise, remain in DONE.
  property done_to_idle;
    @(posedge i_clk) disable iff (i_rst)
      (dut.state == DONE) |-> ((o_axis_valid_m && i_axis_ready_m)
                                ? (dut.next_state == IDLE)
                                : (dut.next_state == DONE));
  endproperty
  assert property (done_to_idle);

endmodule