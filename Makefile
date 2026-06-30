# Build everything the benchmarks and the Ryu differential test need.
# Lean targets go through lake; the C++ and Java helpers (which lake cannot
# build) live here. `make` rebuilds all of them.

.PHONY: all lean cpp java clean

all: lean cpp java

lean:
	lake build benchFloatToString diffDump

cpp:
	g++ -O3 -std=c++20 -march=native -o benches/bench_ref benches/bench_ref.cpp benches/corpora.cpp
	g++ -O2 -std=c++20 -o benches/difftest_ryu benches/difftest_ryu.cpp

java:
	@if command -v javac >/dev/null 2>&1; then \
		javac -d benches/bench_java benches/bench_java/Bench.java benches/bench_java/Corpora.java; \
	else echo "javac not found; skipping JDK bench (only needed for a full plot re-time)"; fi

clean:
	rm -f benches/bench_ref benches/difftest_ryu benches/bench_java/*.class
