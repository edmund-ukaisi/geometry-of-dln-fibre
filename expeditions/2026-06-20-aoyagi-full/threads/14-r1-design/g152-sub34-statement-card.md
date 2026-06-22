# Statement card — #44c / #54 matrix-core comparability (sub-34)

**Status: ABSTRACT COMPARABILITY sorry-free (GREEN). The geometric instantiation into sub-3's
`loss_squeeze` is gated on crux2's #58 coreEmbed structure fix.**

## Module
`lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeBlocks.lean` (pinned `fm2/deepest-gauge-chart-sub34` @19b62a7)

## Delivered (4 lemmas, 0 sorry, axioms = {propext, Classical.choice, Quot.sound})

### `twofactor_block_product`
`(fromBlocks (1+X₁) Y₁ Z₁ T₁) * (fromBlocks (1+X₂) Y₂ Z₂ T₂) = fromBlocks (…) (…) (…) (Z₁Y₂+T₁T₂)`.
The 2-factor gauge-sliced product blocks (`fromBlocks_multiply`). g150 cert's gauge slice.

### `schur_P11_decomp`
`P11 = (P11 − P10·Ainv·P01) + P10·Ainv·P01`. The Schur split: `R := P11 − P10·Ainv·P01` (the
gauge-normalized T̃ core), leak `:= P10·Ainv·P01` (regular×regular). Pure ring algebra.

### `frobenius_fromBlocks`
`∑ᵢⱼ f((fromBlocks E00 E01 E10 E11)ᵢⱼ) = (∑f(E00)+∑f(E01))+(∑f(E10)+∑f(E11))`. The block-Frobenius
split (`f = (·²)` ⟹ `loss = ∑E² + ‖P11‖²`). `Fintype.sum_sum_type` regrouping.

### `core_comparability_squeeze` (THE load-bearing #54)
Given `P11 j = leak j + Rcore j` (`hsplit`) and `∑ leak² ≤ t²·∑ E²` (`hleak`, leak ∈ ideal(reg)):
```
(2(1+t²))⁻¹·(∑E²+‖Rcore‖²) ≤ ∑E²+‖P11‖² ≤ (2+2t²)·(∑E²+‖Rcore‖²)
```
The thin specialisation of `squeeze_bounds_abstract` (`p = leak`, `s = Rcore`, `p+s = P11`).

## English gloss
At a rank-`r`-exact deepest point, the gauge-sliced loss `= ∑E² + ‖P11‖²`; the `(1,1)` block `P11`
splits as the gauge-normalized Schur core `R` (the T̃ chain) plus a regular×regular leak; since the
leak is charged to the regular block (`∑leak² ≤ t²∑E²`, `t = ‖pivot‖ → 0` at `w0`), the loss is
two-sidedly comparable to `∑E² + ‖R‖²` — the squeeze datum sub-5/6 consume.

## g153 (the refutation this dodges)
The naive RAW-`∏T` core is FALSE: `C1C2C3 = blockdiag[1,−ε⁴]` has `∑E²=0`, raw `∏T=0` (interior
`T2=0`), `P11=−ε⁴` ⟹ `loss=ε⁸ > c₂·Φ_raw=0`. The Schur core `R` (not raw `∏T`) is load-bearing; the
leak (which the raw form mis-assigned to the core) is correctly charged to `∑E²` here.

## Numeric checks (PASS)
- `nReg = r(H₀+H_last−r)` = residual Jacobian rank at `w0` (3-layer fold).
- `flatDim H = nReg + flatDim M + nGauge` exact (8=3+2+3, 18=8+2+8, 27=5+12+10).
- `‖leak‖²/∑E² → 0` as deviation→0 (leak reg×reg, charged to ∑E²).
- `nGauge = 0` for ALL L=1 (⟹ MP-split exact-germ impossible at L=1; coreEmbed route needed).

## Remaining (gated on crux2 #58)
Geometric instantiation: identify E/P11/leak/R from the gauge-sliced `dlnLoss` via `block_elimination`
units; the leak bound; `R = dlnLoss M 0(coreEmbed core)`; MP split reindex; assembly into `loss_squeeze`.
The current structure hardcodes the raw `(paramsEquivFlat M).symm` core (g153-false); crux2 owns the
coreEmbed reshape (#58). pp2's #56 general-v cert cross-checks the same T̃/R core.
