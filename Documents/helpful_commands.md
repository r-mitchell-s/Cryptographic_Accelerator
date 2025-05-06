// - - - - - HELPFUL COMMANDS FOR SIMULATION/VERIFICATION - - - - - //

// to run the docker-based EBMC instance on the accelerator with an SVA tb:
./run-ebmc.sh tea_accelerator_mod.sv FORMAL_TB.sv --module FORMAL_TB

// for each of the formal subproperties
./run-ebmc.sh tea_accelerator_mod.sv tb_formal_fixed_execution_path.sv --module tb_formal_fixed_execution_path

./run-ebmc.sh tea_accelerator_mod.sv tb_formal_fixed_operation_count.sv --module tb_formal_fixed_operation_count

./run-ebmc.sh tea_accelerator_mod.sv tb_formal_data_independent_control_flow.sv --module tb_formal_data_independent_control_flow

./run-ebmc.sh tea_accelerator_mod.sv tb_formal_constant_time.sv --module tb_formal_constant_time