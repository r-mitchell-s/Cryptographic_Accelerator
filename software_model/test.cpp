#include <iostream>
#include <fstream>
#include <cstdint>
#include <random>

// Declaration of the TEA encryption function implemented in tea.cpp
void tea_encrypt(uint32_t v[2], const uint32_t key[4]);

int main() {
    // Open CSV file for output
    std::ofstream csv("test.csv");
    
    // Write CSV header: key words, plaintext inputs, and ciphertext outputs
    csv << "Key0,Key1,Key2,Key3,Input0,Input1,Output0,Output1\n";

    // Set up a C++11 random number generator for 32-bit unsigned integers
    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_int_distribution<uint32_t> dis(0, 0xFFFFFFFF);

    // Generate 10,000 test cases
    for (uint32_t i = 0; i < 10000; ++i) {
        // Randomly generate a 128-bit key (four 32-bit values)
        uint32_t key[4] = { dis(gen), dis(gen), dis(gen), dis(gen) };
        
        // Randomly generate a 64-bit input (two 32-bit values)
        uint32_t v[2] = { dis(gen), dis(gen) };

        // Preserve the original plaintext values for CSV output
        uint32_t orig0 = v[0];
        uint32_t orig1 = v[1];

        // Encrypt the block using TEA with the randomly generated key
        tea_encrypt(v, key);

        // Write the key, original plaintext, and ciphertext to CSV
        csv << key[0] << "," << key[1] << "," << key[2] << "," << key[3] << ",";
        csv << orig0 << "," << orig1 << ",";
        csv << v[0] << "," << v[1] << "\n";
    }

    csv.close();
    return 0;
}
