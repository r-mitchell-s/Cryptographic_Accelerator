// Author: Mitchell Sharum
// Date Created: 3/18/2025
// Purpose: Early simulations of TEA accelrator to make sure that we are getting outputs and proper dataflow for simple cases
// will later integrate the golden model

module tb_tea_accelerator;

    // signal declarations - testbench module interface to the DUT
    logic i_clk = 0;                      
    logic i_rst;             
    logic [127:0] i_key;
    logic i_axis_valid_s;             
    logic o_axis_ready_s;           
    logic [63:0] i_axis_data_s;       
    logic o_axis_valid_m;           
    logic i_axis_ready_m;            
    logic [63:0] o_axis_data_m; 

    // DUT instantiation
    tea_accelerator dut(
        .i_clk(i_clk), 
        .i_rst(i_rst),
        .i_key(i_key),
        .i_axis_valid_s(i_axis_valid_s),
        .o_axis_ready_s(o_axis_ready_s),
        .i_axis_data_s(i_axis_data_s), 
        .o_axis_valid_m(o_axis_valid_m), 
        .i_axis_ready_m(i_axis_ready_m), 
        .o_axis_data_m(o_axis_data_m));
    
    // clock generation
    initial begin
        forever begin
            i_clk <= ~i_clk;
            #5;
        end
    end
    
    // test stimulus
    initial begin

        // dump the wavedate into a .vcd
        $dumpfile("sim_tea_accelerator.vcd");
        $dumpvars(0, tb_tea_accelerator);

        // signal initialization
        i_clk = 0;
        i_rst = 0;
        i_key = 0;
        i_axis_ready_m = 0;
        i_axis_valid_s = 0;
        i_axis_data_s = 0;
        #5;

        // test vectors
        i_rst = 1;
        #5;

        // deassert reset and supply vector
        i_rst = 0;
        i_axis_ready_m = 1;
        i_axis_valid_s = 1;
        i_key = 128'h0;
        i_axis_data_s = 64'h0;
        #5;

        // leave sim runnig until the ouput waveform can be viewed
        #2500;

        // end the simulation
        $finish;

    end
endmodule