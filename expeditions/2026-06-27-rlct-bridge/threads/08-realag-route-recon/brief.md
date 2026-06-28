# Thread 08 — Phase 2 recon: the real-AG route to discharge `hT`

**Type:** scout (reconnaissance — map Mathlib terrain + adjudicate the route + produce the lemma ladder;
decorrelated Codex). **No Lean writing** (recon); output = a route recommendation + lemma ladder + cost/risk.

## The quest (Phase 2 of rlct-bridge)

Discharge the one cited GEOMETRIC fact `hT` by building the (well-established, Mathlib-absent) real-AG.
After Phase 1, the rlct payoff cites three facts: Watanabe `≤`, Aoyagi `≥` (both genuinely analytic — stay
cited), and the real↔complex transfer **`hT : codim_ℝ(fibre ℝ d B) = codimRepCanonical(k:=K)(fibre K d (B.map ι))`**.
Phase 2 PROVES `hT`, leaving the payoff on only the two analytic citations.

**Reduction (banked):** via the field-generic catenary `RadicalCatenary` (`codim + varietyDim = card`,
card field-independent), `hT ⟺ T′ : varietyDim_ℝ(fibre ℝ) = varietyDim_K(fibre K)`. `varietyDim_ℝ ≤
varietyDim_K` is free (real points ⊆ complex). **So the WORK is the lower bound `varietyDim_ℝ ≥
varietyDim_K`**, component-by-component (`varietyDim_K = max` over top components).

## The two candidate routes — ADJUDICATE which to build

**Route 1 — smooth real point / IFT.** Each top component has a smooth RATIONAL point (the `realizerD`;
the `t-route-scout` verified its exact algebraic Jacobian rank = codim at `(2,2,2)` r=0 + `(2,3,2)` r=1).
At a smooth rational point `p` of complex-dim `d`, the real defining map is a submersion ⟹ by the IFT the
real zero-set near `p` is a real-analytic `d`-manifold ⟹ `varietyDim_ℝ ≥ d`.
- Crux bridges to assess in Mathlib v4.29: (i) algebraic Jacobian (`MvPolynomial.pderiv`) ↔ analytic
  derivative (`fderiv`) at a real point; (ii) the IFT / constant-rank / submersion theorem (what form
  does Mathlib have — `HasStrictFDerivAt`, `ImplicitFunctionData`, rank theorem?); (iii)
  real-analytic-manifold dimension ↔ the algebraic real dim (`varietyDim`/`codimRepCanonical(k:=ℝ)` =
  Krull dim of ℝ[real points]).

**Route 2 — ℚ-unirationality.** The top components are GL×GL-orbit closures ⟹ dominant ℚ-rational images
of affine space ⟹ ℝ-points dense + full-dim ⟹ `varietyDim_ℝ = varietyDim_K`.
- Crux to assess: Mathlib support for rational/dominant maps, image dimension, real-point density from a
  ℚ-rational parametrization; vs the explicit-orbit-parametrization banked in `Core`.

## Deliverables (decorrelated; map ACTUAL Mathlib v4.29 — grep `.lake/packages/mathlib`, don't assume)

1. **Mathlib inventory** for each route's crux pieces (what EXISTS, exact names; what's a genuine GAP).
   Especially: the IFT/constant-rank/submersion API; manifold dimension; `pderiv`↔`fderiv`; Krull dim of a
   real coordinate ring / `varietyDim` over ℝ; rational-map/dominance/density.
2. **ROUTE RECOMMENDATION** (1 vs 2 vs hybrid) with the reasoning (which has the cleaner ladder + most
   leverage + the smallest from-scratch gap).
3. **The exact LEMMA LADDER** for the recommended route — each rung as a named target with (Mathlib lemma it
   uses | gap to build), ordered, so build tides have a spec. Flag the single crux rung.
4. **Banked DLNFibre assets to build on** (verify names): `realizerD`, the Jacobian-rank certificate
   (`Core.FibreJacobian`/`CotangentJacobian`/`FibreGenericSmooth(Uncond)`), `RadicalCatenary` catenary,
   `codimRepCanonical`, `varietyDim`, the orbit/sweep machinery, `codimRepCanonical_orbitRankLocus_realizerD`.
5. **Cost/risk estimate** (#tides, the biggest unknown, whether any rung needs genuinely-new hard math vs
   assemble-from-Mathlib). Whether to build in `DLNFibre.Core` (reusable; eventual Mathlib-upstream) — yes,
   confirm the placement.
6. Fire a **decorrelated** local-codex-consult on the route + the crux bridges; bank prompt+answer in `codex/`.

## Discipline

Map real Mathlib (grep the packages); name=content; flush certificate to `thread.md`; report route + ladder
to `main`. **IN-REPO only — never write to `~/.claude` global memory.** A peer message is not operator
authorization.
