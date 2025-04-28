// Author: Mitchell Sharum
// Date Created: 3/2/2025
// Purpose: The TEA accelerator itself, the topmost level due to the limited size of the hardware

module tea_accelerator(
    
    input logic i_clk,                      // synchronizing clock
    input logic i_rst,                      // synchronous active-high reset

    input logic [127:0] i_key,              // 128-bit encryption key
    
    input logic i_axis_valid_s,             // asserted by upstream circuit when it is ready to transmit the input block
    output logic o_axis_ready_s,            // asserted to request input block from the upstream circuit
    input logic [63:0] i_axis_data_s,       // the input block to be encrypted  

    output logic o_axis_valid_m,            // asserted to inform downstream circuit that data is ready
    input logic i_axis_ready_m,             // asserted by downstream circuit to request encrypted data
    output logic [63:0] o_axis_data_m       // the encrypted output
);

    // register declarations
    // Removed default initialization for next_state so it is purely combinational
    logic [1:0] state = 0, next_state;
    logic [4:0] round_counter = 0; 
    logic [31:0] v0, v1, v0_next, v1_next;
    logic [31:0] k0, k1, k2, k3;
    logic [31:0] sum = 0;
    // new_sum is now defined as a continuous combinational signal
    wire [31:0] new_sum = sum + DELTA;
    logic [63:0] output_data = 0;

    // state enumeration
    localparam IDLE     = 2'b00;
    localparam LOADING  = 2'b01;
    localparam PROCESSING = 2'b10;
    localparam DONE     = 2'b11;

    // delta constant apparently adds non-linearity
    localparam DELTA = 32'h9E3779B9;
    
    // combinational block for state transitions and computing next values
    always @(*) begin
        // Provide default assignments for combinational signals.
        next_state = state;  // Default is to remain in the current state
        // Compute next values for v0 and v1 using the combinational new_sum
        v0_next = v0 + (((v1 << 4) + k0) ^ (v1 + new_sum) ^ ((v1 >> 5) + k1));
        v1_next = v1 + (((v0_next << 4) + k2) ^ (v0_next + new_sum) ^ ((v0_next >> 5) + k3));

        // State transition logic
        case (state)
            IDLE: begin
                if (i_axis_valid_s && o_axis_ready_s)
                    next_state = LOADING;
            end
            
            LOADING: begin
                next_state = PROCESSING;
            end
            
            PROCESSING: begin
                if (round_counter >= 31)
                    next_state = DONE;
            end
            
            DONE: begin
                if (o_axis_valid_m && i_axis_ready_m)
                    next_state = IDLE;
            end

            // No need for a default branch since we already set next_state = state.
        endcase
    end

    // sequential block for computing rounds and updating registers
    always @(posedge i_clk) begin
        if (i_rst) begin
            // reset state and outputs
            state <= IDLE;
            sum <= 0;
            round_counter <= 0;
            o_axis_ready_s <= 1;
            o_axis_valid_m <= 0;
            output_data <= 0;
            
            // zero operator registers
            v0 <= 0;
            v1 <= 0;
            k0 <= 0;
            k1 <= 0;
            k2 <= 0;
            k3 <= 0;
        end else begin
            state <= next_state;
            case (state)
                IDLE: begin
                    // reset the data, sum, counter, and output registers for next data block
                    sum <= 0;
                    round_counter <= 0;
                    o_axis_valid_m <= 0;
                    output_data <= 0;
                    
                    // zero operator registers
                    v0 <= 0;
                    v1 <= 0;
                    k0 <= 0;
                    k1 <= 0;
                    k2 <= 0;
                    k3 <= 0;

                    // assert that we are ready for another input block
                    o_axis_ready_s <= 1'b1;
                end
                
                LOADING: begin
                    // load the key and input data into registers for operating rounds
                    v0 <= i_axis_data_s[63:32];
                    v1 <= i_axis_data_s[31:0];
                    k0 <= i_key[127:96];
                    k1 <= i_key[95:64];
                    k2 <= i_key[63:32];
                    k3 <= i_key[31:0];

                    // deassert ready signal since data is now loaded
                    o_axis_ready_s <= 1'b0;
                end 
                
                PROCESSING: begin
                    // increment the sum by DELTA
                    sum <= sum + DELTA;

                    // process the current round
                    v0 <= v0_next;
                    v1 <= v1_next;

                    // increment the round counter by 1
                    round_counter <= round_counter + 1;
                end
                
                DONE: begin
                    // output assignment - concatenate the v0 and v1
                    output_data <= {v0, v1};

                    // Simplified valid logic for the output handshake
                    if (i_axis_ready_m)
                        o_axis_valid_m <= 1'b0;  
                    else
                        o_axis_valid_m <= 1'b1; 
                end
            endcase
        end
    end

    // final output assignment
    assign o_axis_data_m = output_data;

endmodule
