// - - - - - INPUT INJECTIVITY - - - - - //
// 
// Input injectivity demands that for any two plaintexts, the ciphertext that is produced by the
// algorithm will be unique. TEA like, like other block ciphers, satisfies this property.
// Verifying this property for the TEA accelerator would serve to futher demonstrate that the
// hardware implementation matches the formal specification we have set out to achieve

module tb_formal_input_injectivity;
  
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

  // we will need to store two different traces for comparison
  logic [63:0] plaintext1, plaintext2;
  logic [63:0] ciphertext1, ciphertext2;

	// track the completeness of encryptions
	logic encryption1_done, encryption2_done;
  
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

	// start from the assumption of unique plaintexts
  assume property (@(posedge i_clk) 
		plaintext1 != plaintext2);

	// use a fixed key to further constrain out definition of injectivity (in case key1+in1 and key2_in2 yield the same out)
	assume property (@(posedge i_clk)
		i_key == 128'hFEDCB19876143210FE1CB19876543210);

	// capture and store the outputs associated with each plaintext
	always @(posedge i_clk) begin
		if (i_rst) begin
			encryption1_done <= 0;
			encryption2_done <= 0;

		// if the necessary conditions for a first encryption are satisfied
		end else if (dut.state == DONE && i_axis_ready_m && o_axis_valid_m && !encryption1_done) begin
			ciphertext1 <= o_axis_data_m;
			encryption1_done <= 1;
		
		// handle the completion of the second encryption completing
		end else if (dut.state == DONE && i_axis_ready_m && o_axis_valid_m && !encryption2_done) begin
			ciphertext2 <= o_axis_data_m;
			encryption2_done <= 1;
		end 
	end

	// property: injectivity means different inputs should produce unique ciphertexts
	property input_injectivity;
		@(posedge i_clk) disable iff (i_rst)
		((dut.state == DONE) && (plaintext1 != plaintext2) && (encryption1_done && encryption2_done)) |-> 
			(ciphertext1 != ciphertext2);
	endproperty
	assert property(input_injectivity); 

endmodule