// Reference C++ float-to-string benches: std::to_chars (Ryu/Grisu) + snprintf.
//
// Usage: ./bench_ref <impl> <corpus>
//   impl   = chars     (std::to_chars — Ryu/Schubfach on libstdc++; reused buffer)
//          | chars_str (std::to_chars + std::string per call; allocation-matched
//                       to the Lean/Java/Python harnesses, which return a fresh
//                       heap string from every call)
//          | snprintf  (libc %.17g)
//   corpus = adversarial | nice | uniform
//
// Inputs come from benches/corpora/<corpus>.u64 (written by `lake exe
// genCorpora`), guaranteeing bit-identical inputs across the harnesses.
//
// Build (manual): g++ -O3 -std=c++20 -march=native -o bench_ref bench_ref.cpp
// Build (script): see benches/run.sh
#include <algorithm>
#include <bit>
#include <charconv>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <string>
#include <vector>

// The corpora are written by `lake exe genCorpora` (benches/GenCorpora.lean),
// one decimal IEEE-754 word per line.
static std::vector<double> load_corpus(const char *label) {
    std::string path = std::string("benches/corpora/") + label + ".u64";
    std::ifstream in(path);
    if (!in) {
        fprintf(stderr, "cannot open %s (run `lake exe genCorpora` from the repository root)\n",
                path.c_str());
        exit(1);
    }
    std::vector<double> xs;
    unsigned long long u;
    while (in >> u) xs.push_back(std::bit_cast<double>((uint64_t)u));
    return xs;
}

using namespace std::chrono;

// Compiler barrier: the value behind p is "observed", so the conversion and
// any buffer/string it wrote cannot be dead-code-eliminated.
static inline void clobber(const void *p) {
    __asm__ volatile("" : : "g"(p) : "memory");
}

static uint64_t corpus_checksum(const std::vector<double> &xs) {
    uint64_t s = 0;
    for (double f : xs) {
        s += std::bit_cast<uint64_t>(f);
    }
    return s;
}

int main(int argc, char **argv) {
    if (argc < 3) {
        fprintf(stderr,
                "usage: %s <chars|chars_str|snprintf|from_chars|strtod> <adversarial|nice|uniform> [--checksum]\n",
                argv[0]);
        return 1;
    }
    enum Mode { CHARS, CHARS_STR, SNPRINTF, FROM_CHARS, STRTOD };
    Mode mode = (strcmp(argv[1], "chars_str") == 0)  ? CHARS_STR
              : (strcmp(argv[1], "snprintf") == 0)   ? SNPRINTF
              : (strcmp(argv[1], "from_chars") == 0) ? FROM_CHARS
              : (strcmp(argv[1], "strtod") == 0)     ? STRTOD
                                                     : CHARS;
    const char *label = argv[2];
    if (strcmp(label, "nice") != 0 && strcmp(label, "uniform") != 0) label = "adversarial";
    const std::vector<double> corpus = load_corpus(label);
    const std::vector<double> *xs = &corpus;

    bool checksumOnly = (argc >= 4 && strcmp(argv[3], "--checksum") == 0);
    if (checksumOnly) {
        printf("%s: n=%zu sum_bits=%llu\n", label, xs->size(),
               (unsigned long long)corpus_checksum(*xs));
        return 0;
    }

    const int N = 1000;
    const int M = 5;
    char buf[64];

    // Parsing modes: the shortest decimal text of each double, parsed back.
    // The Lean reader takes a lexed Decimal, so this also pays for lexing.
    std::vector<std::string> texts;
    if (mode == FROM_CHARS || mode == STRTOD) {
        for (double f : *xs) {
            auto [p, ec] = std::to_chars(buf, buf + sizeof(buf), f);
            texts.emplace_back(buf, (size_t)(p - buf));
        }
        uint64_t sink = 0;
        for (int j = 0; j < 50; j++)
            for (const std::string &t : texts) {
                double v = 0;
                if (mode == FROM_CHARS) std::from_chars(t.data(), t.data() + t.size(), v);
                else v = strtod(t.c_str(), nullptr);
                sink ^= std::bit_cast<uint64_t>(v);
            }
        long long times[M];
        for (int r = 0; r < M; r++) {
            auto t0 = steady_clock::now();
            for (int i = 0; i < N; i++)
                for (const std::string &t : texts) {
                    double v = 0;
                    if (mode == FROM_CHARS) std::from_chars(t.data(), t.data() + t.size(), v);
                    else v = strtod(t.c_str(), nullptr);
                    sink ^= std::bit_cast<uint64_t>(v);
                }
            auto t1 = steady_clock::now();
            times[r] = duration_cast<nanoseconds>(t1 - t0).count() / ((long long)N * (long long)texts.size());
        }
        std::sort(times, times + M);
        if (sink == 12345) printf("\n");
        printf("%s/%s: median = %lld ns/call (runs: %lld %lld %lld %lld %lld)\n",
               mode == FROM_CHARS ? "from_chars" : "strtod", label, times[M / 2],
               times[0], times[1], times[2], times[3], times[4]);
        return 0;
    }

    auto convert = [&](double f) -> size_t {
        switch (mode) {
        case CHARS: {
            auto [p, ec] = std::to_chars(buf, buf + sizeof(buf), f);
            clobber(buf);
            return (size_t)(p - buf);
        }
        case CHARS_STR: {
            auto [p, ec] = std::to_chars(buf, buf + sizeof(buf), f);
            std::string s(buf, (size_t)(p - buf));
            clobber(s.data());
            return s.size();
        }
        default: {
            int len = snprintf(buf, sizeof(buf), "%.17g", f);
            clobber(buf);
            return (size_t)len;
        }
        }
    };

    for (int j = 0; j < 50; j++)
        for (double f : *xs)
            convert(f);

    long long times[M];
    for (int run = 0; run < M; run++) {
        auto t0 = steady_clock::now();
        size_t sink = 0;
        for (int j = 0; j < N; j++)
            for (double f : *xs)
                sink ^= convert(f);
        auto t1 = steady_clock::now();
        long long ns = duration_cast<nanoseconds>(t1 - t0).count();
        times[run] = ns / (long long)N / (long long)xs->size();
        if (sink == 12345) printf("");
    }
    std::sort(times, times + M);
    printf("%s/%s: median = %lld ns/call (runs:", argv[1], argv[2], times[M / 2]);
    for (int i = 0; i < M; i++) printf(" %lld", times[i]);
    printf(")\n");
    return 0;
}
