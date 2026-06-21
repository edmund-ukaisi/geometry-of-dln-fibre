# Thread 10 — L4a build sub-ladder recon (pen-and-paper, 2026-06-19)

## VERDICT: L4a is BOUNDED — ~3 small modules, NOT a multi-week sub-library.
Via the **étale-over-affine-space route** (Codex route (c)), NOT the complete-intersection/regular-sequence
route (route (a)) the synthesis brief sketched. Route (a) balloons: "Jacobian unit ⟹ relations are a regular
sequence of height c" is a complete-intersection sub-library Mathlib lacks (Krull height gives only `≤ c`).
The étale route avoids regular sequences entirely. Codex (decorrelated, xhigh) independently chose route (c),
flagged route (a)'s balloon, named the identical load-bearing lemma + proof, sized at ~3 modules.

## Chosen route — `ringKrullDim (AtPrime m) = rank Ω`, NON-CIRCULAR
`A` finite-type over field `k`, `m` maximal, `IsSmoothAt k m`; `A_m := Localization.AtPrime m`. `[IsAlgClosed k]`.
1. `IsSmoothAt` + `FinitePresentation` ⟹ `∃ f∉m, IsStandardSmooth k (Localization.Away f =: S)`
   [`IsSmoothAt.exists_notMem_isStandardSmooth`]; `S_q ≅ A_m` [`localizationLocalizationAtPrimeIsoLocalization`].
2. `n := P.dimension`; `rank Ω[S⁄k] = n` [`IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential`],
   transport to `rank Ω[A_m⁄k] = n`. **rank Ω side — no dimension/cotangent identity used.**
3. `exists_etale_mvPolynomial` ⟹ `S` étale over `B := k[x_1..x_n]` via `g`.
4. `p := q.comap g` maximal (κ(m)=k under `[IsAlgClosed k]`) ⟹ `p.height = n` [our `height_add_ringKrullDim_quotient_eq` on `B`, `B/p` a field].
5. **Height preservation** `q.height = p.height = n`: étale ⟹ flat ⟹ `HasGoingDown`; going-down additivity
   `q.height = p.height + fibre`; fibre `= 0` (étale ⟹ quasi-finite ⟹ Artinian fibre ⟹ minimal). **One new lemma.**
6. `ringKrullDim A_m = ringKrullDim S_q = q.height = n` [`AtPrime.ringKrullDim_eq_height`, `ringKrullDim_eq_of_ringEquiv`].
7. **Independent equality** `ringKrullDim A_m = n = rank Ω`.
8. Cotangent comparison `finrank (CotangentSpace A_m) = n` (companion; overlaps L2).
9. `finrank cotangent = n = ringKrullDim` ⟹ `IsRegularLocalRing` [`iff_finrank_cotangentSpace.mpr` — packaging only].

## The one load-bearing NEW general-CA lemma (bounded — one module)
`Ideal.height_eq_under_of_flat_quasiFiniteAt` : `[IsNoetherianRing S] [Module.Flat R S]`, `Q` prime,
`[QuasiFiniteAt R Q]` ⟹ `Q.height = (Q.under R).height`. Proof: `Flat ⟹ HasGoingDown` →
`height_eq_height_add_of_liesOver_of_hasGoingDown` → second summand `0` (Artinian fibre under `QuasiFiniteAt`
+ `primeHeight_eq_zero_iff`; `WeaklyQuasiFiniteAt.eq_of_le_of_under_eq` fallback) + an `_of_etale` corollary.
Codex named this exact lemma + skeleton independently.

## Build sub-ladder (~3 modules)
- **M1 `Core/FlatQuasiFiniteHeight.lean`** — [new] `height_eq_under_of_flat_quasiFiniteAt` + `_of_etale`
  (reuse going-down additivity + fibre-height-0). Self-contained general CA; **build FIRST (de-risks the route)**.
- **M2 `Core/SmoothLocalRelativeDimension.lean`** — [reuse] smooth-at ⟹ standard-smooth `A_f`, `rank Ω = n`,
  rank transport, `exists_etale_mvPolynomial`; [new] `p` maximal ⟹ `p.height = n` (our catenary); [new] assemble
  via M1 ⟹ `ringKrullDim A_m = n`. **The independent dimension bridge.**
- **M3 `Core/SmoothPointRegular.lean`** — [new] cotangent comparison `finrank(m/m²) = rank Ω = n` (scope JOINTLY
  with L2, which already identifies `m/m²` with the Zariski tangent = `range δ⁰`); [reuse]
  `iff_finrank_cotangentSpace.mpr` ⟹ `IsRegularLocalRing` (target `smooth_point_isRegularLocalRing`).

## Hardest two; kill-condition
Hardest: (1) `height_eq_under_of_flat_quasiFiniteAt` (fibre-height-0 reconciliation); (2) cotangent comparison
`finrank(m/m²) = rank Ω` (Kähler base-change; overlaps L2). **Kill-condition:** L4a balloons only if fibre-
prime-height-0 fails to assemble from the present quasi-finite API — judged NOT to fire (both Artinian-fibre and
`QuasiFiniteAt.eq_of_le_of_under_eq` paths present; Codex concurs). Build M1 first to settle it.

## Scope note
M3 cotangent comparison overlaps **L2** (Zariski tangent = `range δ⁰`) — build the `m/m²` identification ONCE.
If L2 gives `finrank(CotangentSpace A_m) = finrank(range δ⁰)` and M2 gives `ringKrullDim A_m = n = rank Ω`, the
residual for regularity is `finrank(range δ⁰) = n` — the geometric content L2/L3 deliver.

Codex artefacts: `threads/10-L4a-recon/codex/route-{prompt,answer}.md`.
