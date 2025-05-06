// - - - - - HELPFUL COMMANDS FOR SIMULATION/VERIFICATION - - - - - //

// to run the docker-based EBMC instance on the accelerator with an SVA tb:
./run-ebmc.sh tea_accelerator_mod.sv FORMAL_TB.sv --module FORMAL_TB

// sub-property 1: fixed execution path
./run-ebmc.sh tea_accelerator_mod.sv tb_formal_fixed_execution_path.sv --module tb_formal_fixed_execution_path

// sub-property 2: fixed operations count
./run-ebmc.sh tea_accelerator_mod.sv tb_formal_fixed_operation_count.sv --module tb_formal_fixed_operation_count

// sub-property 3: data independent control flow
./run-ebmc.sh tea_accelerator_mod.sv tb_formal_data_independent_control_flow.sv --module tb_formal_data_independent_control_flow

// composite property: constant time
./run-ebmc.sh tea_accelerator_mod.sv tb_formal_constant_time.sv --module tb_formal_constant_time

// TEA guaruntees input injectivity (different key and data will produce unique outputs): 
./run-ebmc.sh tea_accelerator_mod.sv tb_formal_input_injectivity.sv --module tb_formal_input_injectivity

// TEA does not satisfy related-key resistance (small changes to keys can cause predicatble changes to the ciphertext):
./run-ebmc.sh tea_accelerator_mod.sv tb_formal_related_key.sv --module tb_formal_related_key