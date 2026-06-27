# Statement card — #44c sub-3 (the matrix-core comparability + the construction, sub-34)

**Status: the matrix-algebra toolkit is sorry-free (GREEN, reviewer SURVIVED). The geometric
construction (`split` + `coreAbsorb` maps) is the remaining XL piece; the assembly shape is validated.**

## Modules (pinned `fm2/deepest-gauge-chart-sub34`)
- `lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeBlocks.lean` — 5 matrix lemmas (GREEN, clean-three).
- `lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean` — `deepest_gauge_chart_construct`
  (assembly GREEN vs design D) over `deepest_gauge_construction` (1 bundled honest sorry).

## Delivered — `DeepestGaugeBlocks` (5 lemmas, 0 sorry, axioms = {propext, Classical.choice, Quot.sound})
- `twofactor_block_product` — the 2-factor gauge-sliced product blocks (`fromBlocks_multiply`).
- `schur_P11_decomp` — `P11 = (P11 − P10·Ainv·P01) + P10·Ainv·P01` (the full-product Schur split).
- `frobenius_fromBlocks` — `∑ᵢⱼ f((fromBlocks …)ᵢⱼ) = block sums` (⟹ `loss = ∑E² + ‖P11‖²`).
- `core_comparability_squeeze` — the load-bearing SQUEEZE: given `P11 = leak + R` and
  `∑leak² ≤ t²·∑E²`, `c₁(∑E²+‖R‖²) ≤ ∑E²+‖P11‖² ≤ c₂(∑E²+‖R‖²)`, `c₁=(2(1+t²))⁻¹`, `c₂=2+2t²`.
- `layer_schur_blockDiag` — the per-layer Schur block-diagonalization
  `L·C·R = blockdiag[(1+X), S]`, `S = T − Z·⅟(1+X)·Y` (the #61-corrected per-layer Schur complement).

## The findings chain (decorrelated: exact-numeric + Codex xhigh; all accepted into the cert)
1. **g152** — drove the R-squeeze re-shape (chart/Dchart/jac_unit DROPPED; controller-confirmed).
2. **g153** — the raw-`∏T` core is FALSE (`C1C2C3 = blockdiag[1,−ε⁴]`: ∑E²=0, ∏T=0, P11=−ε⁴).
3. **g154** — the MP-split exact germ is impossible at L=1 (`nGauge=0`); the `coreAbsorb` route is right.
4. **g156** — the per-layer core is the SCHUR complement `S_s = T_s − Z_s(I+X_s)⁻¹Y_s` (NOT the unit
   `T_s·(I−V_sY_s)⁻¹`, which is 0 at `T=0`). **Accepted as #61 CORRECTION, 3-way aligned.**
5. **g157** — `coreAbsorb` = (a) per-layer Schur SHEAR (`T→S`, additive, det=1, **MP** — free) + (b) the
   non-MP inter-layer unit. The loss core is the FULL-product Schur `R`, NOT `∏S_s` (which = `R|{E=0}`
   only — `Schur(C₁C₂) = S₁(I+…)⁻¹S₂`).
6. **exact-vs-squeeze** — in raw block coords the germ is a genuine SQUEEZE (`loss − (∑E²+‖R‖²)` =
   nonzero cross-terms `2⟨R,leak⟩+‖leak‖²`; ratio band →{1} at w0 but ≠1 finitely). The EXACT germ
   (c₁=c₂=1) is achievable only via an analytic Morse/splitting c-o-v (completing the square) — TRUE
   but not what the Lean builds. The formalized datum is the squeeze (`core_comparability_squeeze`);
   `ofExactGerm` (c₁=c₂=1) is dischargeable only via the harder Morse c-o-v, unnecessary for the RLCT.

## Remaining (#59, the geometric construction)
`deepest_gauge_construction` (one bundled sorry): the concrete `split` (gauge-slice MP reindex —
heaviest, flagged for crux2 pairing) + `coreAbsorb` (core-output = full Schur `R` via the MP shear +
the inter-layer unit) + `loss_squeeze` (wired from `core_comparability_squeeze`). The algebra is banked;
the remainder is measure/coordinate geometry.

## Pinned commit
`fm2/deepest-gauge-chart-sub34` (5 GREEN lemmas + the construction skeleton; reviewer SURVIVED on the
comparability).
