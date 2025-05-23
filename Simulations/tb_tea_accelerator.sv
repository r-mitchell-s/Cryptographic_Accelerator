// Author: Mitchell Sharum
// Date Created: 3/18/2025
// Purpose: Early simulations of TEA accelrator to make sure that we are getting outputs and proper dataflow for simple cases
// will later integrate the golden model
// 
// Conceptual Note: In RTL code the DUT (device under test) is the circuit design that we described in the tea_accelerator
// module, and the testbench is the simulation module we hook the DUT to to provide a stimulus -a series of test vectors in the form
// of signal changes at the input of the DUT interface. We can declare a test signal internal to the teztbench module, and then pull in the
// binary string (or preferable hex lol) output of the software model, creating a simulated correct signal to compare the circuit output with

module tb_tea_accelerator;

    // - - - - - INTERFACE SETUP - - - - - //

    // signal declarations - these signals will be used to drive the DUT
    logic i_clk = 0;                      
    logic i_rst;             
    logic [127:0] i_key;
    logic i_axis_valid_s;             
    logic o_axis_ready_s;           
    logic [63:0] i_axis_data_s;       
    logic o_axis_valid_m;           
    logic i_axis_ready_m;            
    logic [63:0] o_axis_data_m; 

    // DUT (device under test) instantiation
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
    
    // coverage tracking variables
    integer test_count = 0;
    integer pass_count = 0;
    integer fail_count = 0;

    // file handle for CSV file
    integer test_file;

    // temporary variables to hold CSV values
    integer csv_key0, csv_key1, csv_key2, csv_key3;
    integer csv_input0, csv_input1;
    integer csv_exp0, csv_exp1;
    logic [127:0] key;
    logic [63:0]  input_data;
    logic [63:0]  expected_output;
    logic [63:0]  dut_output;
 
    // - - - - -  DRIVING LOGIC - - - - - //

    // clock generation block
    initial begin
        forever begin
            i_clk <= ~i_clk;
            #5;
        end
    end
    
    // test stimulus
    initial begin

        // dump the wavedata into a .vcd
        $dumpfile("sim_tea_accelerator.vcd");
        $dumpvars(0, tb_tea_accelerator);

        // open test vectors file
        test_file = $fopen("test.csv", "r");
        if (!test_file) begin
            $display("Error: Could not open test.csv");
            $finish;
        end
        
        // signal initialization
        i_clk = 0;
        i_rst = 0;
        i_key = 0;
        i_axis_ready_m = 0;
        i_axis_valid_s = 0;
        i_axis_data_s = 0;
        #5;

        // reset the circuit to initialize registers
        i_rst = 1;
        #5;

        // deassert reset
        i_rst = 0;
        #5;

   
        // process each test vector in the input file
        while (!$feof(test_file)) begin
            integer status;
            
            // four key words, two input words, and two expected output words.
            status = $fscanf(test_file, "%d,%d,%d,%d,%d,%d,%d,%d", 
                    csv_key0, csv_key1, csv_key2, csv_key3,
                    csv_input0, csv_input1, csv_exp0, csv_exp1);
               
            // if the read successfully gets key and data, then proceed
            if (status == 8) begin 
                // combine key and input sections
                key = {csv_key0, csv_key1, csv_key2, csv_key3};
                input_data = {csv_input0, csv_input1};
                expected_output = {csv_exp0, csv_exp1};

                // load key and input
                i_key = key;
                i_axis_data_s = input_data;
                
                // wait until DUT is ready to semd input stimulus
                wait(o_axis_ready_s);
                i_axis_valid_s = 1;
                @(posedge i_clk);
                i_axis_valid_s = 0;

                // Wait for output to be valid and capture it in the vriable to be compared
                wait(o_axis_valid_m);
                dut_output = o_axis_data_m; // ?
                
                // run golden model to get expected output for the same test vector
                //run_golden_model(key, input_data, expected_output);
                
                // compare outputs
                compare_outputs(dut_output, expected_output);
                
                // signal ready for next cycle
                i_axis_ready_m = 1;
                @(posedge i_clk);
                i_axis_ready_m = 0;
                
            // error handling
            end else if (!$feof(test_file)) begin
                $display("Error: Invalid test vector format");
                $finish;
            end
        end
        
        // close all files
        $fclose(test_file);
        
        // print test summary
        $display("\n=== Test Summary ===");
        $display("Total tests: %0d", test_count);
        $display("Passed: %0d (%0.2f%%)", pass_count, 100.0*pass_count/test_count);
        $display("Failed: %0d (%0.2f%%)", fail_count, 100.0*fail_count/test_count);
        
        // end the simulation
        $display("\nSimulation completed.");
        $finish;
    end
    
    //task to compare golden output to the DUT output
    task compare_outputs(input [63:0] dut_out, input [63:0] golden_out);

        //  increment the test count    
        test_count++;
        
        // do the actual comparison
        if (dut_out === golden_out) begin
            pass_count++;
            $display("[PASS] Test %0d: DUT=0x%h, Golden=0x%h", test_count, dut_out, golden_out);
        end else begin
            fail_count++;
            $display("[FAIL] Test %0d: DUT=0x%h, Golden=0x%h", test_count, dut_out, golden_out);
        end
        
        // print result to console
        $display("%0d,%h,%h,%s", test_count, dut_out, golden_out, (dut_out === golden_out) ? "PASS" : "FAIL");
    endtask

endmodule
