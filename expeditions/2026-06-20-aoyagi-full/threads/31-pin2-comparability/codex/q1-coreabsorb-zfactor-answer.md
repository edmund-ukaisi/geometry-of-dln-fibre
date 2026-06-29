**A.** From the stated definition,
`schurCorrection p s = -(readZ p s) * (1 + readX p s)^{-1} * (readY p s)`.
So the Z-factor is the bare coordinate read `readZ p s`, not `deepBlkZ0 + readZ p s`. The full-layer-block reading is an extra definition not present in what you quoted.

**B.** `D(schurCorrection_s)(0) = 0`. Writing `Z = readZ`, `X = readX`, `Y = readY`, and `A = (1 + X)⁻¹`, Leibniz gives
`D[-ZAY]_0[h] = -(DZ_0[h] A(0) Y(0) + Z(0) DA_0[h] Y(0) + Z(0) A(0) DY_0[h])`.
Since `Z(0)=0` and `Y(0)=0`, every term vanishes.

**C.** Yes, the `deepBlkZ0 != 0` claim is measuring a different basis/split than the reads. The reads live in the framed `r ⊕ (· - r)` split used by `regGaugeSlotEquiv` and `fromBlocks`, where the deepest layer is `fromBlocks 1 0 0 0`, so its lower-left block is zero. A nonzero `toBlocks21` of the raw deepest matrix in the standard basis is not the `readZ` coordinate used by `schurCorrection`.

**D.** For `coreShearHomeo(shift)` to fix the origin, one needs `shift(0)=0`. Under the stated definition this holds because `schurCorrection(0)=0`, hence the core shift vanishes at the deepest/origin point. A shift value carrying a nonzero `deepBlkZ0 * deepBlkY0` term would be incompatible with fixing the origin unless some additional, unstated cancellation or conjugation were present.

Verdict: `D(schurCorrection)(0) = 0`; the bare-read interpretation matches the definitions as given.