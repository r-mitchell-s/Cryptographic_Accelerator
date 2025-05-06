// - - - - - FIXED OPERATION COUNT SUBPROPERTY - - - - - //

module tb_formal_fixed_operation_count;

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

  // auxiliary signals to track previous values for property 2
  logic [1:0] prev_state;
  logic [4:0] prev_counter;
  
  // track previous values
  always @(posedge i_clk) begin
    if (i_rst) begin
      prev_state <= IDLE;
      prev_counter <= 0;
    end else begin
      prev_state <= dut.state;
      prev_counter <= dut.round_counter;
    end
  end

	// Property 1: Round counter always reaches exactly 32 (same number of operations every time)
  property always_32_rounds;
    @(posedge i_clk) disable iff(i_rst)
      ((dut.state == PROCESSING) && (dut.next_state == DONE)) |-> 
        (dut.round_counter == 31);
  endproperty
  assert property(always_32_rounds);

  // Property 2: Round counter should always increment from cycle to cycle (rewritten without ##1 or $past)
  property always_increments;
    @(posedge i_clk) disable iff(i_rst)
      (dut.state == PROCESSING && prev_state == PROCESSING && prev_counter < 31) |-> 
        (dut.round_counter == prev_counter + 1);
  endproperty
  assert property(always_increments);
endmodule