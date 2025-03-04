// Author: Mitchell Sharum
// Date Created: 3/2/2025
// Purpose: The TEA accekerator itself, the topmost level due to the limited size of the harware

module tea_accel(
    
    input logic i_clk,                      // synchronizing clock
    input logic i_rst,                      // synchronous active-high reset

    input logic [127:0] i_key,              // 128-bit encryption key
    
    input logic i_axis_valid_s,             // asserted by upstream circuit when it is ready to transmit the input block
    output logic o_axis_ready_s,            // asserted to request input block fromt he upstream circuit
    input logic [63:0] i_axis_data_s,       // the input block to be encrypted  

    output logic o_axis_valid_m,            // asserted to inform downstream circuit that data is ready
    input logic i_axis_ready_m,             // asserted by downstream circuit to rquest encrypted data
    output logic [63:0] o_axis_data_m       // the encrypted output
);

    // register declarations
    logic [1:0] state, next_state;
    logic [4:0] round_counter; 
    logic [31:0] v0, v1;
    logic [31:0] k0, k1, k2, k3;
    logic [31:0] sum = 0;
    logic [63:0] output_data = 0;

    // state enumeration
    localparam IDLE = 2'b00;
    localparam LOADING = 2'b01;
    localparam PROCESSING = 2'b10;
    localparam DONE = 2'b11;

    // delta constant apparently adds non-linearity
    localparam DELTA = 32'h9E3779B9;
    
    // combinatorial block for state transitions
    always @(*) begin
        case (state)
            
            // when module ready to accept a data word and the upstream module is ready to provide, then move into LOADING state 
            IDLE: 
                if (i_axis_valid_s && o_axis_ready_s) begin
                    next_state = LOADING;
                end

            // load the inoput data into corresponding registers
            LOADING:
                next_state = PROCESSING;
            
            // process 32 rounds before output
            PROCESSING:
                if (round_counter >= 31) begin
                    next_state = DONE;
                end
            
            // if the downstream module is ready to receive, output encrypted data and return to IDLE       
            DONE:
                if (o_axis_valid_m && i_axis_ready_m) begin
                    next_state = IDLE;
                end
            
            // default case, remain in the same state
            default: 
                next_state = state;
        endcase
    end

    // sequential block for computing rounds
    always @(posedge i_clk) begin
        
        // transition to the next state
        state <= next_state;

        // reset handling
        if (i_rst) begin
            
            // reset state and outputs
            state <= IDLE;
            sum <= 0;
            round_counter <= 0;
            o_axis_ready_s <= 0;
            o_axis_valid_m <= 0;
            o_axis_data_m <= 0;
            
            // zero operator registers
            v0 <= 0;
            v1 <= 0;
            k0 <= 0;
            k1 <= 0;
            k2 <= 0;
            k3 <= 0;

        // IDLE handling
        end else if (state == IDLE) begin
        
            // reset the data, sum, counter, and output registers for next data block
            sum <= 0;
            round_counter <= 0;
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
        
        // LOADING handling
        end else if (state == LOADING) begin
            
            // load the key and input data into registers for operating rounds
            v0 <= i_axis_data_s[31:0];
            v1 <= i_axis_data_s[63:32];
            k0 <= i_key[31:0];
            k1 <= i_key[63:32];
            k2 <= i_key[95:64];
            k3 <= i_key[127:96];

            // assert we are no longer ready to receive
            o_axis_ready_s <= 1'b0;
        
        // PROCESSING handling
        end else if (state == PROCESSING) begin

            // increent the sum by DELTA
            sum <= sum + DELTA;

            // process v0 and v1 rounds respectively
            v0 <= v0 + (((v1 << 4) + k0) ^ (v1 + sum) ^ ((v1 >> 5) + k1));
            v1 <= v1 + (((v0 << 4) + k2) ^ (v0 + sum) ^ ((v0 >> 5) + k3));

            // increment the round counter by 1
            round_counter <= round_counter + 1;
        
        // DONE handling
        end else if (state == DONE) begin
        
            // output assignment - concatenate the v0 and v1
            output_data <= {v0,v1};

            // tell downstream module we are ready to transmit
            o_axis_valid_m <= 1'b1;
        end
    end

    // final output assignment
    assign o_axis_data_m = output_data;

endmodule