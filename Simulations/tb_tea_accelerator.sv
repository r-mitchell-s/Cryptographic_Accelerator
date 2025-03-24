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
    integer test_count;
    integer pass_count;
    integer fail_count;

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
        test_vectors_file = $fopen("test_vectors.txt", "r");
        if (!test_vectors_file) begin
            $display("Error: Could not open test_vectors.txt");
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
        while (!$feof(test_vectors_file)) begin
            logic [127:0] key;
            logic [63:0] input_data;
            logic [63:0] expected_output;
            integer status;
            
            // read test vector from file
            status = $fscanf(test_vectors_file, "%h %h", key, input_data);
        
            // if the read successfully gets key and data, then proceed
            if (status == 2) begin 

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
                logic [63:0] dut_output = o_axis_data_m;
                
                // run golden model to get expected output for the same test vector
                run_golden_model(key, input_data, expected_output);
                
                // compare outputs
                compare_outputs(dut_output, expected_output);
                
                // signal ready for next cycle
                i_axis_ready_m = 1;
                @(posedge i_clk);
                
            // error handling
            end else if (!$feof(test_vectors_file)) begin
                $display("Error: Invalid test vector format");
                break;
            end
        end
        
        // close all files
        $fclose(test_vectors_file);
        
        // print test summary
        $display("\n=== Test Summary ===");
        $display("Total tests: %0d", test_count);
        $display("Passed: %0d (%0.2f%%)", pass_count, 100.0*pass_count/test_count);
        $display("Failed: %0d (%0.2f%%)", fail_count, 100.0*fail_count/test_count);
        
        // end the simulation
        $display("\nSimulation completed.");
        $finish;
    end

    // task to run the golden model. Will probably need to be changed
    task run_golden_model(input [127:0] key, input [63:0] data, output [63:0] result);
        integer status;
        string command;
        integer model_output_file;
        
        // execute the cpp model using the stimulus from the testbench
        status = $system("./tea_golden_model %h %h", key, data);
        
        // error handling for cpp execution
        if (status != 0) begin
            $display("Error: Golden model execution failed with status %d", status);
            result = 64'hx; // set result to unknown on error so we def won't pass test
        end else begin

            // read the result from the temporary output file created by the C++ model
            model_output_file = $fopen("model_output.tmp", "r");
            
            // error handling (again)
            if (!model_output_file) begin
                $display("Error: Could not open model output file");
                result = 64'hx;
            
            // actual read logic to extract the output from golden model
            end else begin
                status = $fscanf(model_output_file, "%h", result);
                $fclose(model_output_file);
                
                // more error handling yay
                if (status != 1) begin
                    $display("Error: Failed to read golden model output");
                    result = 64'hx;
                end
            end
        end
    endtask
    
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
        $fdisplay("%0d,%h,%h,%s", test_count, dut_out, golden_out, (dut_out === golden_out) ? "PASS" : "FAIL");
    endtask

endmodule