# Thread 31 — route-(c) rung-1 non-circularity verdict (the make-or-break de-risk)

*Controller-mandated checkpoint: is the SET-LEVEL/`varietyDim` single-chart trivialization
NON-CIRCULAR (does radical-insensitivity dodge the R2-3b-4 reducedness circularity)? Settle FIRST.*

## VERDICT: YES — non-circular. Proceed with route (c).

Both my independent reading and a decorrelated xhigh Codex concur, and the formal linchpin is
LANDED (builds green, axiom-clean):

> `DLNFibre.Core.VarietyDimRadical.ringKrullDim_quotient_radical` :
> `ringKrullDim (R ⧸ I) = ringKrullDim (R ⧸ I.radical)` (+ the `eq_of_radical_eq` form).
> Proof: `ringKrullDim_quotient` ×2 + `PrimeSpectrum.zeroLocus_radical` (2 lines).

## Why the circularity is dodged

- **R2-3b-4 was circular FOR REDUCEDNESS**: it built a *scheme/ring* iso `e : S ≃ₐ R ⊗ F_E` whose
  forward map needed the strict inclusion `sigmaIdeal ≤ ker(comorphism)` — available only as `≤
  radical(ker)`. Establishing the strict inclusion *is* reducedness of the cut, the thing `e` was
  meant to prove.
- **`hSweep` is a `varietyDim` (= `ringKrullDim` of the coordinate ring) statement**, and
  `varietyDim Z := (ringKrullDim (R ⧸ vanishingIdeal Z)).unbotD 0` reads `Z` only through
  `vanishingIdeal Z`, which is **radical by construction**. Krull dim is radical-insensitive
  (`ringKrullDim_quotient_radical`), so the whole dimension build works on the **reduced/closed-set**
  structure and NEVER needs `fibreGenIdeal` to be radical or the inclusion `sigmaIdeal ≤ ker`. The
  only pullback containment used is the **tautological** one ("a polynomial vanishing on the target
  pulls back to one vanishing on the source"), already non-circular and already in the engine
  (`deepBaseComap_sigmaIdeal_le`-style).

## Codex's load-bearing refinement (folded in)

A *bare set* bijection does NOT preserve `varietyDim` — rung 1 must be a **regular** (algebraic)
isomorphism of the chart varieties, not just a set bijection. The engine's gauge `nEquiv d P`
(`EndpointNormalization`, an `AlgEquiv` of coordinate rings = regular iso) + the sweep set-identity
(`EndBaseChangeSweep`) + `aeval_gaugeSub_multPoly` (gauge transports `mult` algebraically) supply
exactly this. Non-circular, reachable.

## Route-(c) decomposition + per-rung cost (honest)

1. **[de-risk LANDED]** Radical-insensitivity (`VarietyDimRadical`). ~30 LoC. DONE.
2. **Single-chart regular trivialization** `mult⁻¹(U_P) ∩ Σ^r ≅_reg U_P × F` on one pivot chart `U_P
   ⊆ Mat^{=r}`. Reuses the LANDED gauge `nEquiv` + sweep + `multComap`. NON-CIRCULAR. New but
   reachable. ~2-3 modules (the regular map + inverse on the principal open; localization
   coordinates).
3. **Product-dimension** `varietyDim (U × F) = varietyDim U + varietyDim F` over alg-closed `k`,
   ALLOWING REDUCIBLE `F`. **THE DOMINANT NEW COST and the real Mathlib gap**: neither `ringKrullDim
   (A ⊗_k B) = dim A + dim B` NOR `trdeg` of a tensor product is in Mathlib v4.29 (`trdeg_add_eq` is
   tower additivity, not the product theorem). Reducibility handled by `max_{i,j}(dim Xᵢ + dim Yⱼ) =
   max dim Xᵢ + max dim Yⱼ`. ~3-5 modules (the trdeg-of-tensor product theorem + reducible max
   bookkeeping). This is where route (c)'s weight sits.
4. **Per-chart dim** `varietyDim(chart) = δ + varietyDim F` (combine 2+3, base `varietyDim U_P = δ`
   LANDED). ~1 module.
5. **Finite-pivot-cover glue** `varietyDim(⋃ᵢ Zᵢ) = maxᵢ varietyDim Zᵢ` (Spec-level union facts
   present: `PrimeSpectrum.vanishingIdeal_iUnion`/`zeroLocus_inf`; the `varietyDim` max-form is new;
   mind `varietyDim ∅ = 0`). + the open-chart↔closure bridge (`varietyDim` is closure dim). ~2-3
   modules.
6. **Assemble `hSweep`** → feed LANDED `RouteCAssembly._of_sweep'`. ~1 module.

**Total ≈ 9-13 modules** (matches the SPECIFY estimate). Risk relocated from "reducedness
circularity" (DODGED) to "product-dimension + finite-glue infrastructure" (standard CA, Mathlib-
absent, non-circular). No route step re-enters R2-3b-4.

## Reachability

HIGH on non-circularity (settled + linchpin landed). MEDIUM on the product-dimension rung (rung 3) —
it is the genuine from-scratch piece; if `trdeg`-of-tensor proves harder than ~3-5 modules at v4.29,
that is the next checkpoint, not a wall. The trivialization (rung 2) is mostly LANDED-reuse.

## Evidence

- `codex/noncirc-setlevel-{prompt,answer}.md` — decorrelated xhigh Codex: clean YES on
  non-circularity; product-dim + finite-glue are the real new work, not reducedness.
- `DLNFibre/Core/VarietyDimRadical.lean` — the linchpin, green + axiom-clean + non-vacuity witness.
- Mathlib greps: `trdeg`/`ringKrullDim` of a tensor product both ABSENT; `ringKrullDim_quotient` +
  `PrimeSpectrum.zeroLocus_radical` PRESENT (radical-insensitivity reachable).
