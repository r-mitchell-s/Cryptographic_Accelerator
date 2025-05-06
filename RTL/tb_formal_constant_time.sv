// - - - - - CONSTANT TIME - - - - - //
// 
// We had chat GPT coalesce all of the properties
// tb_formal_constant_time.sv - Combined testbench for constant-time verification

module tb_formal_constant_time;
  // State parameters 
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
  
  // Auxiliary signals for tracking previous values (needed since EBMC doesn't support $past)
  logic [1:0] prev_state;
  logic [4:0] prev_counter;
  
  // Track previous values
  always @(posedge i_clk) begin
    if (i_rst) begin
      prev_state <= IDLE;
      prev_counter <= 0;
    end else begin
      prev_state <= dut.state;
      prev_counter <= dut.round_counter;
    end
  end
  
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
  
  // ======== FIXED OPERATION COUNT PROPERTIES ========
  
  // Property 1: Round counter always reaches exactly 32 (same number of operations every time)
  property always_32_rounds;
    @(posedge i_clk) disable iff(i_rst)
      ((dut.state == PROCESSING) && (dut.next_state == DONE)) |-> 
        (dut.round_counter == 31);
  endproperty
  assert property(always_32_rounds);
  
  // Property 2: Round counter should always increment from cycle to cycle
  property always_increments;
    @(posedge i_clk) disable iff(i_rst)
      (dut.state == PROCESSING && prev_state == PROCESSING && prev_counter < 31) |-> 
        (dut.round_counter == prev_counter + 1);
  endproperty
  assert property(always_increments);
  
  // ======== FIXED EXECUTION PATH PROPERTIES ========
  
  // Property 3: IDLE to LOADING transition based on handshake
  property idle_to_loading;
    @(posedge i_clk) disable iff (i_rst)
      (dut.state == IDLE) |-> ((i_axis_valid_s && o_axis_ready_s)
                                ? (dut.next_state == LOADING)
                                : (dut.next_state == IDLE));
  endproperty
  assert property (idle_to_loading);
  
  // Property 4: LOADING always transitions to PROCESSING
  property loading_to_processing;
    @(posedge i_clk) disable iff (i_rst)
      (dut.state == LOADING) |-> (dut.next_state == PROCESSING);
  endproperty
  assert property (loading_to_processing);
  
  // Property 5: PROCESSING transitions based only on round counter
  property processing_to_done;
    @(posedge i_clk) disable iff (i_rst)
      (dut.state == PROCESSING) |-> ((dut.round_counter >= 31)
                                       ? (dut.next_state == DONE)
                                       : (dut.next_state == PROCESSING));
  endproperty
  assert property (processing_to_done);
  
  // Property 6: DONE transitions based on output handshake
  property done_to_idle;
    @(posedge i_clk) disable iff (i_rst)
      (dut.state == DONE) |-> ((o_axis_valid_m && i_axis_ready_m)
                                ? (dut.next_state == IDLE)
                                : (dut.next_state == DONE));
  endproperty
  assert property (done_to_idle);
  
  // ======== DATA INDEPENDENT CONTROL FLOW PROPERTIES ========
  
  // Property 7: IDLE transition depends only on handshake signals
  property idle_transition_data_independent;
    @(posedge i_clk) disable iff(i_rst)
      (dut.state == IDLE) |-> 
        (dut.next_state == ((i_axis_valid_s && o_axis_ready_s) ? LOADING : IDLE));
  endproperty
  assert property(idle_transition_data_independent);
  
  // Property 8: LOADING transition is unconditional to PROCESSING
  property loading_transition_data_independent;
    @(posedge i_clk) disable iff(i_rst)
      (dut.state == LOADING) |-> (dut.next_state == PROCESSING);
  endproperty
  assert property(loading_transition_data_independent);
  
  // Property 9: PROCESSING transitions depend only on round counter
  property processing_transitions_data_independent;
    @(posedge i_clk) disable iff(i_rst)
      (dut.state == PROCESSING) |-> 
        (dut.next_state == (dut.round_counter >= 31 ? DONE : PROCESSING));
  endproperty
  assert property(processing_transitions_data_independent);
  
  // Property 10: DONE transition depends only on handshake signals
  property done_transition_data_independent;
    @(posedge i_clk) disable iff(i_rst)
      (dut.state == DONE) |-> 
        (dut.next_state == ((o_axis_valid_m && i_axis_ready_m) ? IDLE : DONE));
  endproperty
  assert property(done_transition_data_independent);
  
endmodule