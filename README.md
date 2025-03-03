# Cryptographic_Accelerator
Project underway for Harvard's CS2540 (Formal Methods in Computer Security), consisting of the design and functional verification of a TEA (Tiny Encryption Algorithm) accelerator. After functional verification, the hyperproperty of constant time will be enforced on the accelerator in order to safeguard the encryption against timing-based attacks.

# Background
Used primarily for reseearch and educational purposes, TEA is a lightweight encryption algorithm fit for hardware implementation. Side channel attacks posed a threat to the security of hardware based encryption accelerators, as the number of clock cycles that it takes to encrypt the data could convey key information about it. In order to protect against this insecurity, cryptographic accelerator will compute all outputs across the same number of clock cycles.

# High Level Description


# Directory Structure
At the top level there are six directories that make up this project. RTL contains the HDL that constitute the accelerator itself. Scripts contains any Bash, Python, or Tcl script used to automate the build process, simulations, or other yet to be determined functions of the project. Documentation contains schematics, the project report, and other informative files, and Simaulation contains testbench files, along with waveforms and other simulation materials, along with the golden software model used to verify the behavior of the circuit.

# Usage
