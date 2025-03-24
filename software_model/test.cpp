#include <iostream>
#include <fstream>
#include <cstdint>
#include <random>

void tea_encrypt(uint32_t v[2], const uint32_t key[4]);

int main() {
    // open csv, write header
    std::ofstream csv("test.csv");
    csv << "Key0,Key1,Key2,Key3,Input0,Input1,Output0,Output1\n";

    // rng
    //std::random_device rd;
    std::mt19937 gen(77777);
    std::uniform_int_distribution<uint32_t> dis(0, 0xFFFFFFFF);

    // 10,000 test cases
    for (uint32_t i = 0; i < 10000; ++i) {
        // Randomly generate key + input 
        uint32_t key[4] = { dis(gen), dis(gen), dis(gen), dis(gen) };
        uint32_t v[2] = { dis(gen), dis(gen) };

        // save for csv
        uint32_t orig0 = v[0];
        uint32_t orig1 = v[1];

        // encrypt
        tea_encrypt(v, key);

        // write to csv
        csv << key[0] << "," << key[1] << "," << key[2] << "," << key[3] << ",";
        csv << orig0 << "," << orig1 << ",";
        csv << v[0] << "," << v[1] << "\n";
    }

    csv.close();
    return 0;
}

