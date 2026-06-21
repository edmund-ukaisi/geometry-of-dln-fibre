# Expedition brief — `rlct-payoff`

## Central question

Formalise, in honest Lean, two coupled results that complete the geometric side of the paper's
destination, both built on the geometry of the rank-`r` product locus `Σ^r`:

1. **`Σ^r` geometry + `θ`** (new content, zero-cited): the orbit-stratification `Σ̄^r = ⋃ Ō_M`, its
   irreducible components (= the maximal `Ō_M`), and the number **`θ`** of top-dimensional components —
   closing the `Σ^r`-aggregate roadmap that `Core.CThetaGeometric` left open.
2. **The RLCT payoff** "DLNs are mildly singular": `rlct(K^DLN_B) = C/2`, with `C` the geometric
   codimension (LANDED: Voigt discharge). The rlct **value is Cited** (Aoyagi/Watanabe); our contribution
   is the geometric `C` feeding it.

> **CORRECTION (recon, verified against source — `θ` is NOT the RLCT multiplicity).** The bundling was
> initially justified by "the payoff is the pair `(C/2, θ)`, `θ` the multiplicity half" — this is
> **false per the paper** (Rem. after the Aoyagi theorem: no simple relationship between the rlct
> multiplicity `m` and the component count `θ = k`). `θ` is delivered as a **geometric invariant in its
> own right**, not as the rlct multiplicity. The bundle stays coherent — `Σ^r`-as-variety underpins both
> `θ` (its components) and the loss landscape (whose codim is `C`) — but the deliverable is **two
> results** (`rlct = C/2` Cited; `θ` geometric), not one learning-coefficient pair.

## Closing criterion

The `(C/2, θ)` payoff formalised, green / 0-sorry / axiom-clean:
- **`Σ^r` geometry** (new content, zero-cited): `Σ^r` defined as a variety; the orbit-stratification
  `Σ^r = ⋃ Ō_M`; irreducible components = maximal `Ō_M`.
- **`θ`-geometric** (new content, zero-cited): top-dimensional components = min-codim orbits (via the
  LANDED per-orbit Voigt codim); `numTop = θ` = their count.
- **DLN application** (`DLNFibre.DLN`): `Rep_d`, `mult`, the fibres `mult⁻¹(B)`, the square-Frobenius
  loss; the loss landscape's geometry identified with `Σ^r`.
- **The payoff**: `rlct(K^DLN_B) = C/2` stated against a `Cited`-tagged rlct interface (Aoyagi/Watanabe
  supply the analytic rlct value; our geometric `C` is plugged in — named next to the claim, not smuggled).
  `θ` is delivered separately as the geometric component count, NOT as the rlct multiplicity.

Refuted / refined / a scope-surprise (e.g. RLCT-definition machinery is a multi-month analytic
sub-library) is also a valid close — surface with a sized verdict.

## Ladder (SIZED by the recon, 2026-06-20 — threads 01 scout + 02 pen-and-paper, Codex-convergent)

Verdict: **Phases G/θ/D BOUNDED — build (zero-cited, ~5–6 modules total); Phase R = Cited interface
(Mathlib has no SLT machinery — from-scratch is multi-month).** Architecture: define the aggregate
codim on `PrimeSpectrum` via `⨅` of orbit ideals (`height = ⨅ minimalPrimes` by `rfl`); keep
point↔Spec a thin bridge (the one flagged risk = `Ideal.height` transport under the coordinate change —
spike it first). Build `Σ̄^r = {rk ≤ r}` (`productRankLocusLE`; the paper's `≥` at line 758 is a typo).

- **Phase G — `Σ^r` geometry.** G1 `Σ^r`-as-variety (the rank-`r` corner locus `{A : rank(A_N⋯A_1) ≤ r}`,
  or the zero-product locus for `r=0`). G2 the stratification `Σ^r = ⋃ Ō_M` over the relevant Kostant
  partitions (the hard structural piece). G3 irreducible components of `Σ^r` = maximal `Ō_M`.
- **Phase θ — component count.** θ1 top-dimensional = min-codim (consume the LANDED
  `Core.VoigtDischarge.codimRep_orbitRankLocus_eq_orbitLinearCodim` + `Core.CThetaGeometric`). θ2
  `numTop = θ` = #top-dimensional components.
- **Phase D — DLN application** (`DLNFibre.DLN`, currently a stub). D1 `Rep_d`/`mult`/fibres; D2 the
  square-Frobenius loss; D3 loss geometry = `Σ^r`.
- **Phase R — the RLCT payoff (Cited interface, ~50–150 LoC).** R1 a `Cited`-tagged `RlctInterface`
  (the rlct value/definition — Mathlib has none; from-scratch is a multi-month analytic sub-library, so
  interface, don't build). R2 `rlct(K^DLN_B) = C/2` via the interface + the geometric `C`. `θ` is NOT
  here (it is a separate geometric result in Phase θ).

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
