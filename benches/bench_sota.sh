#!/usr/bin/env bash
# Build benches/bench_sota (state-of-the-art C++ baselines: std::to_chars,
# Ryu, Dragonbox) against the shared corpora. Ryu and Dragonbox are fetched
# into $SOTA_DIR (default: benches/sota-deps, gitignored) if absent.
#
#   benches/bench_sota.sh            # build
#   benches/bench_sota <impl> <corpus>
set -euo pipefail
cd "$(dirname "$0")/.."
SOTA_DIR="${SOTA_DIR:-benches/sota-deps}"
mkdir -p "$SOTA_DIR"
[ -d "$SOTA_DIR/ryu" ]       || git clone --depth 1 https://github.com/ulfjack/ryu "$SOTA_DIR/ryu"
[ -d "$SOTA_DIR/dragonbox" ] || git clone --depth 1 https://github.com/jk-jeon/dragonbox "$SOTA_DIR/dragonbox"

# Ryu keeps its Float->Decimal half (d2d) static; append an exported wrapper
# that mirrors d2s_buffered_n minus the digit emission, so the decimal-only
# cost can be measured like Printer.toDecimal.
cat "$SOTA_DIR/ryu/ryu/d2s.c" - > "$SOTA_DIR/ryu_d2s_patched.c" <<'EOF'

int ryu_d2dec(double f, uint64_t *mant, int32_t *exp) {
  const uint64_t bits = double_to_bits(f);
  const bool ieeeSign = ((bits >> (DOUBLE_MANTISSA_BITS + DOUBLE_EXPONENT_BITS)) & 1) != 0;
  const uint64_t ieeeMantissa = bits & ((1ull << DOUBLE_MANTISSA_BITS) - 1);
  const uint32_t ieeeExponent = (uint32_t) ((bits >> DOUBLE_MANTISSA_BITS) & ((1u << DOUBLE_EXPONENT_BITS) - 1));
  if (ieeeExponent == ((1u << DOUBLE_EXPONENT_BITS) - 1u) || (ieeeExponent == 0 && ieeeMantissa == 0)) {
    *mant = 0; *exp = 0; return ieeeSign;
  }
  floating_decimal_64 v;
  const bool isSmallInt = d2d_small_int(ieeeMantissa, ieeeExponent, &v);
  if (isSmallInt) {
    for (;;) {
      const uint64_t q = div10(v.mantissa);
      const uint32_t r = ((uint32_t) v.mantissa) - 10 * ((uint32_t) q);
      if (r != 0) break;
      v.mantissa = q;
      ++v.exponent;
    }
  } else {
    v = d2d(ieeeMantissa, ieeeExponent);
  }
  *mant = v.mantissa; *exp = v.exponent;
  return ieeeSign;
}
EOF

CXX="${CXX:-g++}"
CC="${CC:-gcc}"
FLAGS="-O3 -march=native -DNDEBUG"
$CC  $FLAGS -std=c11 -I"$SOTA_DIR/ryu" -c -o "$SOTA_DIR/ryu_d2s.o" "$SOTA_DIR/ryu_d2s_patched.c"
$CXX $FLAGS -std=c++20 -I"$SOTA_DIR/dragonbox/include" -c -o "$SOTA_DIR/dragonbox_to_chars.o" \
     "$SOTA_DIR/dragonbox/source/dragonbox_to_chars.cpp"
$CXX $FLAGS -std=c++20 -I"$SOTA_DIR/ryu" -I"$SOTA_DIR/dragonbox/include" \
     -o benches/bench_sota benches/bench_sota.cpp benches/corpora.cpp \
     "$SOTA_DIR/ryu_d2s.o" "$SOTA_DIR/dragonbox_to_chars.o"
echo "built benches/bench_sota ($($CXX --version | head -1))"
