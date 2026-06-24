# Codex consult — route choice for the relative-fibre-dimension rung (Lean 4 / Mathlib v4.29)

I am formalising one dimension identity in Lean 4 + Mathlib v4.29 (a research engine for the geometry
of deep-linear-network multiplication-map fibres). I need to pick the cheapest reachable route and
know the TRUE cost. Be adversarial about cost.

## The exact target (`hSweep`)

```
varietyDim (Σ^r)  =  δ  +  varietyDim F
```
where, concretely in the engine (all set-level over an algebraically closed field `k`, char 0):
- `varietyDim Z := (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal Z)).unbotD 0` — the
  Krull dim of the coordinate ring of a subset `Z` of affine space `RepCoord d → k`.
- `Σ^r = productRankLocus d r = {A : rank(mult A) = r}` — the EXACT-rank locus (tuples of composable
  matrices whose product has rank exactly `r`).
- `F = fibre d B = mult⁻¹(B)` for a fixed rank-`r` target `B`.
- `δ = r·(d_N + d_0 − r)` = `varietyDim(Mat^{=r})`, the determinantal stratum dim (LANDED).

## What is already LANDED in the engine (reuse these)

1. **The sweep identity (set form):** `Σ^r = ⋃_{P ∈ H} (P • ·) '' F`, where `H = GL_{d_N} × GL_{d_0}`
   (the endpoint base-change group `BaseChangeGroup`). I.e. `Σ^r = H · F` (one group-sweep of a single
   fibre). PROVED: `productRankLocus_eq_iUnion_smul_fibre`.
2. **Homogeneity (G1):** all rank-`r` fibres are isomorphic; `codimRepCanonical (fibre B') =
   codimRepCanonical (fibre B)` for any rank-`r` `B'`. So every `H`-translate of `F` has the same
   codim/dim. PROVED.
3. **`varietyDim = trdeg` for an f.g. domain coordinate ring:** the engine computes `varietyDim Z =
   ringKrullDim (R ⧸ ker(pullback)) = ringKrullDim((pullback).range) = trdeg_k(range)` for a
   parametrization pullback (`OrbitPullbackDim`, `AffineNoetherRank`:
   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
   (tower additivity, Stacks 030H) is in Mathlib and the engine uses it.
4. **The comorphism `O(Mat^{=r}) → O(Σ^r)`:** `multComap d := aeval multPoly` IS built
   (`MultComorphism`); the fibre coordinate ring is `R_total ⧸ m_B · R_total` (the comorphism +
   `Ideal.map`). So there IS an abstract ring map `R = O(base) → S = O(total)` at the ideal level.
5. **Generic freeness (module case), JUST LANDED (rung 1):** for a Noetherian domain `R` and a
   FINITE `R`-module `M`, `M[1/r]` is free/flat over `R[1/r]` for some nonzero `r`. The
   algebra-finite-type (relative dim > 0) version is Mathlib-ABSENT.
6. **Determinantal base stratum dim = δ** (LANDED). **Going-down height-additivity**
   `Ideal.height_eq_under_of_flat_quasiFiniteAt` + `Algebra.HasGoingDown.of_flat` (LANDED in
   `FlatQuasiFiniteHeight`).

## The crux

The chart map `R = O(Mat^{=r}) → S = O(Σ^r)` has POSITIVE relative dimension (`dim F = card−C−δ >
0`), so it is NOT module-finite — rung-1 (module-case generic freeness) does NOT directly apply.

## Two candidate routes — assess reachability + TRUE cost of each at v4.29

**Route (a) — transcendence-degree / tower additivity.** `Σ^r` and `F` are f.g. domains over `k`
(are they? `Σ^r` is the exact-rank locus — irreducible? `F` may be reducible — see below). If I can
show `varietyDim Σ^r = trdeg_k O(Σ^r)`, `varietyDim F = trdeg_k O(F)`, `δ = trdeg_k O(Mat^{=r})`, and
the tower `k ⊆ Frac O(Mat^{=r}) ⊆ Frac O(Σ^r)` gives `trdeg_k O(Σ^r) = trdeg_k O(Mat^{=r}) +
trdeg_{Frac O(Mat^{=r})} Frac O(Σ^r)` (tower additivity `trdeg_add_eq`), and the relative trdeg
`trdeg_{Frac R} Frac S = dim(generic fibre) = dim F` (via homogeneity G1, all fibres iso). Does this
close WITHOUT generic flatness? What is the precise missing lemma — is it "relative trdeg = generic
fibre dim" or "generic fibre dim = special fibre dim (F at B)"? The reducibility of `F`/`Σ^r` (F has
components of dims 10,9,9 on the (3,3,3) r=1 anchor; Σ^r has comps 15,14,14) — does the trdeg/tower
route survive non-irreducibility (trdeg is about a domain = irreducible; for reducible we take the
max component, i.e. `ringKrullDim`)? Is `ringKrullDim`-additivity over a sweep even true without
flatness, given reducibility?

**Route (b) — algebra-case generic freeness (EGA IV 6.9.1).** Relative Noether normalization `R →
R[X_1..X_d] → S` (module-finite generically) + rung-1 (module case on the finite part) + polynomial
flatness + composition ⟹ flatness on a dense-open of `Spec R` ⟹ going-down ⟹ relative-dim formula.
The NEW Mathlib-side piece is **relative Noether normalization** (over a domain `R`, not a field).
Mathlib has Noether normalization over a FIELD. Is the relative/over-a-domain version present at
v4.29? If absent, that is a from-scratch build — how large?

## My questions

1. Which route is cheaper/more reachable at v4.29 given the LANDED pieces, AND given the engine is
   SET-LEVEL `varietyDim` (Krull dim of a coordinate ring of a subSET of affine space), NOT scheme/
   `Spec`-level? The going-down machinery (b) wants `Ideal.height`/`HasGoingDown` on RING MAPS — does
   bridging set-level `varietyDim` to the comorphism `multComap`'s going-down add a whole layer?
2. Route (a): is "`dim(H·F) = dim(H·E) + dim F`" (sweep/orbit-dimension additivity) provable from
   trdeg tower additivity + homogeneity WITHOUT a flatness/generic-freeness input? Group sweeps `G·F`
   classically have `dim(G·F) = dim F + dim(G·E)` when the map `G × F → G·F` is dominant with generic
   fibre dim `= dim(stabilizer)`. Is there a clean trdeg argument, or does it secretly need fibre-dim
   semicontinuity (a flatness-flavoured input)?
3. Is there a THIRD route I am missing — e.g. directly: `Σ^r → Mat^{=r}` is a `H`-equivariant
   surjection, `Mat^{=r} = H·E` is a single H-orbit (homogeneous space!), so `Σ^r → Mat^{=r}` is a
   FIBRE BUNDLE (locally trivial in the Zariski/étale topology since `H` is a group), hence
   `dim Σ^r = dim Mat^{=r} + dim F` is the bundle dimension formula — no generic flatness needed,
   just local triviality of a `H`-bundle over a homogeneous space. Is THAT reachable at v4.29 (does
   Mathlib have homogeneous-space / principal-bundle dimension)? This feels like the real structure.
4. If ALL routes hit a Mathlib-absent theorem, say so plainly — that is a recalibration point.

Give me: the route ranking, the precise missing lemma(s) for the top route, a module-count estimate,
and whether any route avoids a from-scratch sub-library. Be honest if this rung is genuinely
sub-expedition-scale.
