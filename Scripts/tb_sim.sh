#!/bin/bash
# Author: Mitchell Sharum
# Date Created: 3/18/2025
# Purpose: Bash script to simulate the first testbench for the accelerator

# declare the directories used
RTL_DIR="../RTL"
SIM_DIR="../Simulations"

# define the filepaths used
RTL_FILE="$RTL_DIR/tea_accelerator.sv"
TB_FILE="$SIM_DIR/tb_tea_accelerator.sv"

# print that we are starting
echo "Compiling DUT and TB"

# compile with to vvp with Icarus verilog
iverilog -g2012 -o out.vvp $RTL_FILE $TB_FILE

# check if the compilation succeeded
if [ $? -eq 0 ]; then

    # report compilation status
    echo "Compilation successful, running vvp..."

    # run the vvp
    vvp out.vvp

else
    # report compilation status
    echo "Compilation failed"
    exit 1
fi

if [ $? -eq 0 ]; then

    # runt he wave viewer
    gtkwave sim_tea_accelerator.vcd
fi