// Reference Schubfach bench: JDK's Double.toString.
//
// Since JDK 19 (JDK-4511638), Double.toString uses Raffaello Giulietti's
// Schubfach algorithm — the same shortest-round-trip decimal algorithm this
// repo implements in Lean. So this measures the canonical reference Schubfach.
//
// Inputs are the shared corpora (benches/gen_corpora.py -> Corpora.java),
// reconstructed from u64 bit patterns, guaranteeing bit-identical inputs
// across the Lean / C++ / Python / Java harnesses.
//
//   javac benches/bench_java/*.java -d benches/bench_java
//   java -cp benches/bench_java Bench <adversarial|nice|uniform> [--checksum]
import java.util.Arrays;

public final class Bench {
  public static void main(String[] args) {
    String label = args.length > 0 ? args[0] : "adversarial";
    double[] xs = Corpora.get(label);

    if (args.length > 1 && args[1].equals("--checksum")) {
      long s = 0;                       // long arithmetic wraps mod 2^64
      for (double f : xs) s += Double.doubleToRawLongBits(f);
      System.out.printf("%s: n=%d sum_bits=%s%n",
                        label, xs.length, Long.toUnsignedString(s));
      return;
    }

    // JIT warmup — Java needs far more than the others before steady state.
    long sink = 0;
    for (int w = 0; w < 1000; w++)
      for (double f : xs) sink ^= Double.toString(f).length();

    final int N = 1000, M = 5;
    long[] times = new long[M];
    for (int r = 0; r < M; r++) {
      sink = 0;
      long t0 = System.nanoTime();
      for (int i = 0; i < N; i++)
        for (double f : xs) sink ^= Double.toString(f).length();
      long t1 = System.nanoTime();
      times[r] = (t1 - t0) / ((long) N * xs.length);
      if (sink == 12345L) System.out.println();   // defeat dead-code elim
    }
    Arrays.sort(times);
    System.out.printf("java/%s: median = %d ns/call (runs: %s)%n",
                      label, times[M / 2], Arrays.toString(times));
  }
}
