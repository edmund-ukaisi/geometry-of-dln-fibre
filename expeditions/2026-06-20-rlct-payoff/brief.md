# Expedition brief — `rlct-payoff`

## Central question

Formalise, in honest Lean, the **RLCT payoff** of the paper — the destination "DLNs are mildly
singular" — as the *complete* learning coefficient **`(C/2, θ)`**, built on the geometry of the
rank-`r` product locus `Σ^r`:

> The real log-canonical threshold of the square-Frobenius loss of a deep linear network is `C/2`,
> with multiplicity `θ`, where `C` is the geometric codimension (LANDED: Voigt discharge) and `θ` is
> the number of top-dimensional irreducible components of `Σ^r`.

This bundles the two directions that are, in SLT, **one result**: Watanabe's free energy is
`F_n ≈ nL₀ + λ log n − (m−1) log log n + …` with `λ` the RLCT and `m` its multiplicity; for the DLN
`λ = C/2` and `m = θ`. So `θ` is not a separable nicety — it is the multiplicity half of the very
payoff. Both rest on `Σ^r` as an actual variety.

## Closing criterion

The `(C/2, θ)` payoff formalised, green / 0-sorry / axiom-clean:
- **`Σ^r` geometry** (new content, zero-cited): `Σ^r` defined as a variety; the orbit-stratification
  `Σ^r = ⋃ Ō_M`; irreducible components = maximal `Ō_M`.
- **`θ`-geometric** (new content, zero-cited): top-dimensional components = min-codim orbits (via the
  LANDED per-orbit Voigt codim); `numTop = θ` = their count.
- **DLN application** (`DLNFibre.DLN`): `Rep_d`, `mult`, the fibres `mult⁻¹(B)`, the square-Frobenius
  loss; the loss landscape's geometry identified with `Σ^r`.
- **The payoff**: `rlct = (C/2, θ)`, with the `rlct ≤ ½·codim` analytic bound **Cited**
  (Aoyagi/Watanabe, per project policy — named next to the claim, not smuggled).

Refuted / refined / a scope-surprise (e.g. RLCT-definition machinery is a multi-month analytic
sub-library) is also a valid close — surface with a sized verdict.

## Provisional ladder (RE-SCOPED BY THE SIZING RECON — do not build before it returns)

- **Phase G — `Σ^r` geometry.** G1 `Σ^r`-as-variety (the rank-`r` corner locus `{A : rank(A_N⋯A_1) ≤ r}`,
  or the zero-product locus for `r=0`). G2 the stratification `Σ^r = ⋃ Ō_M` over the relevant Kostant
  partitions (the hard structural piece). G3 irreducible components of `Σ^r` = maximal `Ō_M`.
- **Phase θ — component count.** θ1 top-dimensional = min-codim (consume the LANDED
  `Core.VoigtDischarge.codimRep_orbitRankLocus_eq_orbitLinearCodim` + `Core.CThetaGeometric`). θ2
  `numTop = θ` = #top-dimensional components.
- **Phase D — DLN application** (`DLNFibre.DLN`, currently a stub). D1 `Rep_d`/`mult`/fibres; D2 the
  square-Frobenius loss; D3 loss geometry = `Σ^r`.
- **Phase R — the RLCT payoff.** R1 the rlct definition / interface (SLT machinery — **the big
  feasibility unknown**). R2 `rlct = (C/2, θ)` with `≤ ½·codim` Cited.

## What is already LANDED (consumable bricks, on `dev`)

- **Geometric codimension `C`** (Voigt discharge, merged PR #4): per-orbit
  `codimRep(orbitRankLocus M) = orbitLinearCodim M` (`[IsAlgClosed k][CharZero k]`); the combinatorial
  `(C,θ)` engine (`Core.CTheta`); the per-orbit geometric reading (`Core.CThetaGeometric`:
  `cCodim_eq_inf_geomCodim`); orbit closures irreducible + prime (`Core.OrbitClosure`); Abeasis–Del Fra
  Thm 3.8 (`orbitRankLocus M = Ō_M`); the dim theory / Nullstellensatz / smooth⟹regular layers.

## Scope / boundary

- Geometric content (`Σ^r`, `θ`): aim zero-cited, `[IsAlgClosed k][CharZero k]` (the over-ℂ setting).
- `rlct ≤ ½·codim`: **Cited** (Aoyagi/Watanabe) — project policy; the geometric `(C,θ)` is the new content.
- The rlct *definition* itself: feasibility TBD by the sizing recon (build vs Cited interface).

## Operating mode

Controller drives autonomously (operator: "drive this autonomously even if large; scaffold tightly;
focus on executive function"). Surface to the operator only at completion or a genuine
blocker/scope-surprise. Controller runs from this worktree ⟹ teammate isolation collapses ⟹ **serial
Lean-writers** (one active editor), parallel doc/recon seats. Sizing-recon FIRST (the discipline that
saved sub-libraries all through voigt-discharge).
