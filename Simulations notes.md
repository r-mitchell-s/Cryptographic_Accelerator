i ran
iverilog -g2012 -o Simulations/sim RTL/tea_accelerator.sv Simulations/tb_tea_accelerator.sv
in the top-level to compile, and
vvp sim
in Simulations/ to run.

test.csv is copied from software_model, except the header is removed
