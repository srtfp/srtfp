// Reference Schubfach bench: JDK's Double.toString.
//
// Since JDK 19 (JDK-4511638), Double.toString uses Raffaello Giulietti's
// Schubfach algorithm — the same shortest-round-trip decimal algorithm this
// repo implements in Lean. So this measures the canonical reference Schubfach.
//
// Inputs are the shared corpora (benches/corpora/<corpus>.u64, written by
// `lake exe genCorpora`), reconstructed from u64 bit patterns, guaranteeing
// bit-identical inputs across the Lean / C++ / Python / Java harnesses.
//
//   javac benches/bench_java/*.java -d benches/bench_java
//   java -cp benches/bench_java Bench <adversarial|nice|uniform> [--checksum]
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.Arrays;

public final class Bench {
  private static double[] load(String label) throws IOException {
    return Files.lines(Paths.get("benches", "corpora", label + ".u64"))
        .filter(l -> !l.isBlank())
        .mapToDouble(l -> Double.longBitsToDouble(Long.parseUnsignedLong(l.trim())))
        .toArray();
  }

  public static void main(String[] args) throws IOException {
    String label = args.length > 0 ? args[0] : "adversarial";
    if (!label.equals("nice") && !label.equals("uniform")) label = "adversarial";
    double[] xs = load(label);

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
