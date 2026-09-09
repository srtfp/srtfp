# Build the library by default. Tests and benchmark helpers are explicit targets.
# Lake owns Lean builds; Make also builds the C++ and Java benchmark helpers.

.PHONY: all lean test check benchmarks bench-lean cpp java clean

all: lean

lean:
	lake build

test:
	lake test

check: test

benchmarks: bench-lean cpp java

bench-lean:
	lake build benchToDecimal benchDecimalToFloat benchFloatToString diffDump genCorpora

cpp:
	g++ -O3 -std=c++20 -march=native -o benches/bench_ref benches/bench_ref.cpp
	g++ -O2 -std=c++20 -o benches/difftest_ryu benches/difftest_ryu.cpp

java:
	@if command -v javac >/dev/null 2>&1; then \
		javac -d benches/bench_java benches/bench_java/Bench.java benches/bench_java/Corpora.java; \
	else echo "javac not found; skipping JDK bench (only needed for a full plot re-time)"; fi

clean:
	lake clean
	rm -f benches/bench_ref benches/difftest_ryu benches/bench_java/*.class
