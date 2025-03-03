// Author: Mitchell Sharum
// Date Created: 3/2/2025
// Purpose: The TEA accekerator itself, the topmost level due to the limited size of the harware

module tea_accel(
    
    input logic i_clk,                      // synchronizing clock
    input logic i_rst,                      // synchronous active-high reset

    input logic [127:0] i_key               // 128-bit encryption key
    
    input logic i_axis_valid_s,             // asserted by upstream circuit when it is ready to transmit the input block
    output logic o_axis_ready_s,            // asserted to request input block fromt he upstream circuit
    input logic [63:0] i_axis_data_s        // the input block to be encrypted  

    output logic o_axis_valid_m,            // asserted to inform downstream circuit that data is ready
    input logic i_axis_ready_m,             // asserted by downstream circuit to rquest encrypted data
    output logic [63:0] o_axis_data_m       // the encrypted output
)

    // register declarations
    logic [1:0] state, next_state;
    logic [4:0] round_counter; 
    logic [31:0] v0, v1;
    logic [31:0] k0, k1, k2, k3;
    logic [63:0] output_data_reg = 0;

    // delta constant apparently adds non-linearity
    localparam DELTA = 32'h9E3779B9;

    // split the key and input into registers for operating rounds
    assign v0 = i_axis_data_s[31:0];
    assign v1 = i_axis_data_s[63:32];
    assign k0 = i_key[31:0];
    assign k1 = i_key[63:32];
    assign k2 = i_key[95:64];
    assign k3 = i_key[127:96];
    
    // sequential block for computing rounds
    always @(posedge i_clk) begin
        
        // reset handling
        if (i_rst) begin
            state <= IDLE;
            round_counter <= 0;
            output_data_reg <= 0;
            o_axis_ready_s <= 0;
            o_axis_valid_m <= 0;
            o_axis_data_m <= 0;
        
        // 
        end else if () begin
        
        end
    end

    // - - - - - STAGE 1 - - - - - //
    // 
endmodule