**Route Choice**

Use **B, but not as “pure Noether”**. The clean route is:

`Noether rank of image` + `Jacobian/algebraic-independence generic rank` + `orbit-map constant rank` + `dμ_e = δ⁰`.

The red-team issue: Noether normalization alone does not see `δ⁰`. A pointwise differential bound is false for a general image map: `t ↦ t²` has image dimension `1` but differential rank `0` at `0`. So the missing orbit-specific fact is that the orbit map has constant rank and its rank at the identity is `finrank range δ⁰`.

**A vs B**

- **A/Kähler route:** valid in principle, but too expensive at Mathlib v4.29. It needs both missing global bridges:
  - **MISSING:** `ringKrullDim A = trdeg k Frac(A)` for f.g. domains.
  - **MISSING:** `rank Ω[L/k] = trdeg k L` for char-zero/separably generated field extensions.
  - **MISSING:** generic differential rank of the image equals the identity differential rank for this orbit map.

- **B/Noether route:** cheaper. It avoids the full `trdeg = rank Ω` theorem and can avoid a reusable general `ringKrullDim = trdeg` theorem. But it still needs a char-zero **Jacobian criterion**: algebraically independent image coordinates give generically independent differentials. That is Kähler-adjacent, not Kähler-free.

**Status Of Key Claims**

- **KNOWN-local:** `ringKrullDim_quotient_eq_noetherRank` for `R/p`.
- **KNOWN-local:** first-isomorphism transport `R/ker μ ≃ₐ[k] range μ`.
- **KNOWN-Mathlib:** `Algebra.trdeg`, `trdeg_lt_aleph0`, `trdeg_le_of_injective/surjective`, `MvPolynomial.trdeg_of_isDomain`.
- **KNOWN-Mathlib:** integral/algebraic transfer for algebraic independence exists, e.g. `Algebra.IsIntegral.algebraicIndependent_iff`.
- **KNOWN-Mathlib:** `PerfectField.ofCharZero`; char zero gives the separability/perfectness input.
- **MISSING-Mathlib:** packaged `ringKrullDim = trdeg` for f.g. domains.
- **INFER:** quotient/range-specific `ringKrullDim = trdeg/noetherRank` is a one-module build from the landed Noether engine, not the hard part.
- **MISSING-Mathlib:** field-extension Kähler rank theorem `rank Ω[L/k] = trdeg`.
- **MISSING-local:** orbit-map differential/constant-rank bridge tying generic rank to `finrank range δ⁰`.

**Hardest Lemma Ranking**

1. **(iii) Differential-rank bound**: hardest. It must prove the orbit map’s generic rank is the identity rank and identify the identity differential with `deformationδ M M`.
2. **(ii) `trdeg = rank Ω` in char zero**: hard, broad, absent, but avoidable via B.
3. **(i) `ringKrullDim = trdeg`**: comparatively easiest here. With the landed Noether engine, the quotient/range version is a contained module.

**Honest Module Count**

I would **confirm 4 remaining modules** for the cheapest route, if B is understood as the Jacobian-Noether route:

1. `AffineNoetherRank`: package image/range Noether-rank dimension API.
2. `JacobianIndependence`: char-zero algebraic independence ⇒ generic Jacobian rank.
3. `OrbitDifferentialRank`: explicit `dμ_e = deformationδ M M` and constant rank under the group action.
4. `OrbitImageDimensionBound`: assemble `ringKrullDim(range μ) ≤ finrank range δ⁰`.

If you count the already-landed `OrbitPullbackDim` as part of route-c, then the route-c total is **5 files**, with **4 still missing**.

**CharZero**

Yes, `CharZero` genuinely buys the separability/perfectness needed for the Jacobian/Kähler independence step. It is not needed for first-iso, primeness/domain, Noether normalization dimension, or the explicit matrix formula for `dμ_e`. In this route, char zero is the bottleneck exactly at “algebraic independence is detected by differentials/generic Jacobian rank.”

Cheapest route: **B**, corrected as above. Module count: **4 remaining**.