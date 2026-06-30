// Ryu oracle dumper for differential testing.
//
// Reads decimal uint64 bit patterns (one per line) from stdin; for each,
// reconstructs the binary64 and prints "<bits> <std::to_chars output>".
// std::to_chars(double) on libstdc++ is the Ryu/Schubfach shortest-decimal
// implementation — the reference oracle we differentially test our verified
// Lean Schubfach printer against (see benches/difftest_ryu.py).
//
// Build: g++ -O2 -std=c++20 -o benches/difftest_ryu benches/difftest_ryu.cpp
#include <bit>
#include <charconv>
#include <cstdint>
#include <cstdio>
#include <string>
#include <iostream>

int main() {
    std::string line;
    char buf[64];
    while (std::getline(std::cin, line)) {
        if (line.empty()) continue;
        uint64_t bits = std::strtoull(line.c_str(), nullptr, 10);
        double f = std::bit_cast<double>(bits);
        auto [p, ec] = std::to_chars(buf, buf + sizeof(buf), f);
        *p = '\0';
        printf("%llu %s\n", (unsigned long long)bits, buf);
    }
    return 0;
}
