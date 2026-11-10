/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Twenty windows of the 1..10^9 range in one file

Windows 60 to 79, the top of the range `X1_Range1e9` covers, so their divisor counts sit
close to `X2_One`'s and the two differ mainly in how many share a file. -/

namespace PrimeCert.SegTune.X3_Twenty

run_sieve 10000000

run_segment 754974721 4194304 9234 8192 10000000

run_segment 767557633 4194304 9309 8192 10000000

run_segment 780140545 4194304 9384 8192 10000000

run_segment 792723457 4194304 9458 8192 10000000

run_segment 805306369 4194304 9532 8192 10000000

run_segment 817889281 4194304 9605 8192 10000000

run_segment 830472193 4194304 9678 8192 10000000

run_segment 843055105 4194304 9750 8192 10000000

run_segment 855638017 4194304 9821 8192 10000000

run_segment 868220929 4194304 9892 8192 10000000

run_segment 880803841 4194304 9962 8192 10000000

run_segment 893386753 4194304 10032 8192 10000000

run_segment 905969665 4194304 10102 8192 10000000

run_segment 918552577 4194304 10171 8192 10000000

run_segment 931135489 4194304 10239 8192 10000000

run_segment 943718401 4194304 10307 8192 10000000

run_segment 956301313 4194304 10375 8192 10000000

run_segment 968884225 4194304 10442 8192 10000000

run_segment 981467137 4194304 10509 8192 10000000

run_segment 994050049 4194304 10575 8192 10000000

end PrimeCert.SegTune.X3_Twenty
