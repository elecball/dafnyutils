# nl separator bytes and blank padding

Status: verified for separator functions, regression and the complete supported nl closure.
Verified date: 2026-10-23. Baseline: `09309b7d078f555ea57060d781fd70f7e25c457f`
with the two-function nl separator patch in `fix/nl-utf8-separator`.
Originating plan: [Correct nl separator UTF-8 semantics](../plan/2026-10-23-nl-unicode.md).

`NlCmd.separator` is text; `BenchWorld.Bytes` is a sequence of characters whose
code points are below 256. Append `Utf8Semantics.Encode(cmd.separator)` to the
number field. Appending raw text requires an invalid byte-domain restriction on
arbitrary Unicode separators.

GNU `coreutils/src/nl.c` at pinned revision
`2cf491412c199e2211880ec3f4ba387026638a33` prints `separator_str` using the line
number format at line 300. Its unnumbered-line buffer at lines 618-621 contains
`lineno_width + strlen(separator_str)` spaces. Under the model's external UTF-8
text semantics, the six-column number field therefore contributes six spaces
plus the encoded separator's byte count. Character count and display width are
not the relevant quantities. The empty separator remains valid.

`bench/utils/nl/NlSpec.dfy` owns `LineNumberText`, `BlankPrefix` and `LinePrefix`.
`NlCore.RenderLineMethod` already reuses `Spec.LinePrefix`, so the specification
fix also repairs executable output without copying the encoding algorithm.
`tests/core/nl_utf8_separator.dfy` proves the prefix law for arbitrary separator
text and checks exact rendered bytes for empty, ASCII, Latin, CJK, non-BMP and
mixed separators, with blank widths and number formats. Concrete constant
proofs use bounded local fuel for the existing recursive helpers.

Evidence is retained locally in `/workspace/tmp/leanutils-port/nl-unicode/`:
`dafny-spec2.log` verifies both changed function obligations (2 assertions,
0 errors), and `dafny-focused4.log` verifies the complete bounded regression
(226 verified, 0 errors). Both exit 0 with Dafny
`4.11.1+5fa47c6e949dad736db25e02b5edad95d0b0be1a`, seed 42 and 30-second assertion
limits. The shared core sources remain the repository's explicit library
boundary. This evidence does not verify native IO adapters or establish a new
termination claim. See the plan for full commands, failed attempts and closure
verification status.

The supported `PYTHONPATH=/workspace/tmp/leanutils-port/nl-unicode-dafny/src make
-C bench/utils/nl verify` also passed all 40 entry/Core/Proof declarations with
`DAFNY_VERIFICATION_RESULT total=1010 failed=0`, exit 0 (`dafny-full.log`). This
retains the original direct entry `RunCore ==> Spec` obligation. Parent review
reported no findings. These are proof results, not native differential-test or
fuzzing results; the existing `decreases *` does not establish termination.
