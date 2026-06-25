# Seam-E round-trips (Lean 4 + Mathlib v4.29, DLNFibre)

Both halves of a localized chart AlgEquiv are now DONE sorry-free; I need the two round-trips to glue
them via `AlgEquiv.ofAlgHom`.

## The two homs (LANDED, sorry-free)

- `chartPsiLoc : Localization.Away dsig →ₐ[k] Localization.Away gF`
- `chartPhiLoc : Localization.Away gF →ₐ[k] Localization.Away dsig`

where (all over an alg-closed char-0 field `k`; `d : Fin (N+2) → ℕ`; `q = d 0`, `p = d last`):
- `Away dsig` localizes `O(Σ) = MvPolynomial (RepCoord d) k ⧸ vanishingIdeal Σ^r` at `dsig = mk ΔPdeep`.
- `Away gF` localizes `P = MvPolynomial SchurVar O(F)` at `gF = map (algebraMap k O(F)) detSchurS`,
  where `O(F) = MvPolynomial (RepCoord d) k ⧸ vanishingIdeal F`.

Construction of each (both are `IsLocalization.liftAlgHom` of a descended `aeval`/`aevalTower`):
- `chartPsiLoc` lifts `chartPsiQuot : O(Σ) →ₐ[k] Away gF`, the descent of
  `chartPsiAeval = aeval chartPsiSub`, `chartPsiSub x = chartPsiTower (gaugeSub d endpointGauge⁻¹ x)`,
  `chartPsiTower = aevalTower schurToGfib fibCoordT`. (`fibCoordT x = algebraMap O(F) (Away gF) (mk_F (X x))`;
  `schurToGfib : SchurLoc →ₐ[k] Away gF` lifts `mapAlgHom (ofId k O(F))` at detSchurS.)
- `chartPhiLoc` lifts `chartPhiAeval = aevalTower chartPhiCoeff chartPhiVarSub` (descended), where
  `chartPhiCoeff : O(F) →ₐ[k] Away dsig` descends `chartPhiFibAeval = aeval chartPhiFibSub`,
  `chartPhiFibSub x = chartPhiTower (gaugeSub d endpointGauge x)` (FORWARD gauge),
  `chartPhiTower = aevalTower schurToDsig sigmaCoordT`. (`sigmaCoordT x = algebraMap O(Σ) (Away dsig) (mk_Σ (X x))`;
  `schurToDsig : SchurLoc →ₐ[k] Away dsig` lifts `chartPhiSchurAeval = aeval chartPhiVarSub` at detSchurS;
  `chartPhiVarSub : SchurVar → Away dsig` reads SchurVar off the product blocks of M.)

`endpointGauge` is the SchurLoc-valued gauge (H at vertex 0, L⁻¹ at last). LANDED gauge group law:
`aeval_gaugeSub_gaugeSub d P Q x : aeval (gaugeSub d P) (gaugeSub d Q x) = baseChange (liftGauge d (Q*P)) (genericTuple d) x.1 x.2.1 x.2.2`
over `MvPolynomial (RepCoord d) R` for any base ring R; specialized to Q*P = 1 it gives `X x`. And
`gaugeEquiv d P` is the AlgEquiv `aeval (gaugeSub d P)` with inverse `aeval (gaugeSub d P⁻¹)`.

## The targets (sorry)

```lean
chartPhiLoc.comp chartPsiLoc = AlgHom.id k (Away dsig)   -- h2
chartPsiLoc.comp chartPhiLoc = AlgHom.id k (Away gF)     -- h1
```

By `Localization.algHom_ext` + `Ideal.Quotient` + `MvPolynomial.algHom_ext`:
- h2 reduces to: `∀ x : RepCoord d, chartPhiLoc (chartPsiSub x) = algebraMap O(Σ) (Away dsig) (mk_Σ (X x))`,
  i.e. `chartPhiLoc (chartPsiSub x) = sigmaCoordT x`.
- h1 reduces to (P-generators): `∀ s : SchurVar, chartPsiLoc (chartPhiVarSub s) = algebraMap (X s)`
  AND (O(F)-coeffs) `∀ x : RepCoord d, chartPsiLoc (chartPhiCoeff (mk_F (X x))) = fibCoordT x`.

## QUESTIONS

(A) The CROSS-RING obstruction: `chartPsiSub x ∈ Away gF` is a value in the OTHER localization, and to
apply `chartPhiLoc` to it I must push `chartPhiLoc` through `chartPsiSub x`'s structure (`chartPsiTower`
of a `gaugeSub` poly, then the `Away gF` localization). What is the cleanest mechanism? Specifically:
`chartPsiSub x = chartPsiTower (gaugeSub eg⁻¹ x)` where `chartPsiTower = aevalTower schurToGfib fibCoordT`
maps `MvPolynomial (RepCoord d) SchurLoc → Away gF`. To compute `chartPhiLoc (chartPsiTower (...))` I'd
want a lemma `chartPhiLoc ∘ chartPsiTower = (some aevalTower into Away dsig)` — does the composition of
an `aevalTower` with a `liftAlgHom`-of-`aevalTower` collapse cleanly via `MvPolynomial.algHom_ext'`?

(B) The load-bearing identity you sketched earlier:
```lean
aevalTower_gaugeSub_gaugeSub (χ : SchurLoc →ₐ[k] T) (v : RepCoord d → T)
    (P Q : BaseChangeGroup (SchurLoc) d) (x : RepCoord d) :
  aevalTower χ (fun y ↦ aevalTower χ v (gaugeSub d P y)) (gaugeSub d Q x)
    = aevalTower χ v (gaugeSub d (Q * P) x)
```
Is this the right shape, and how does it reduce to the LANDED `aeval_gaugeSub_gaugeSub` (which is over a
SINGLE ring `MvPolynomial (RepCoord d) R`, with `aeval` not `aevalTower`)? The Ψ/Φ towers have DIFFERENT
coefficient connecting maps (`schurToGfib` vs `schurToDsig`) AND different variable legs (`fibCoordT` vs
`sigmaCoordT`) — so `χ`, `v` are NOT the same on the two sides. How do P=eg⁻¹ (Ψ) and Q=eg (Φ) compose to
1 when the two towers route through different targets? Is the round-trip actually
`chartPhiLoc ∘ chartPsiLoc` collapsing via `eg⁻¹ * eg = 1` AT THE `MvPolynomial (RepCoord d) SchurLoc`
LEVEL, with both `schurToGfib`/`schurToDsig` and `fibCoordT`/`sigmaCoordT` "cancelling" because the
composite lands back in the SAME ring `Away dsig`?

(C) Concretely for h2 at generator `x`: trace `chartPhiLoc (chartPsiSub x)` step by step to
`sigmaCoordT x`. I suspect: `chartPsiSub x = chartPsiTower (gaugeSub eg⁻¹ x)`; apply `chartPhiLoc`;
the key is `chartPhiLoc ∘ schurToGfib = schurToDsig` (coeff legs match through chartPhiLoc?) and
`chartPhiLoc ∘ fibCoordT = chartPhiCoeff ∘ mk_F = chartPhiFibSub`?? then the two gaugeSubs compose. Is
there a clean intermediate lemma `chartPhiLoc ∘ chartPsiTower = aevalTower schurToDsig chartPhiFibSub`
(or similar) that makes `chartPhiLoc (chartPsiSub x) = aeval (gaugeSub eg) ... (gaugeSub eg⁻¹ x)`
collapse to `sigmaCoordT x` via `aeval_gaugeSub_gaugeSub` at `eg⁻¹ * eg = 1`?

(D) Most-likely-to-break step + the cleanest Mathlib v4.29 API. Be concrete and Lean-shaped.
