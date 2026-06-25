# Sweep-dim reachability adjudication (thread 28) — VERDICT: MATHLIB-ABSENT

*Read-only recon. Decisive question: is Step B (`varietyDim Σ^r = δ + varietyDim F`) Lean-reachable
from the engine's existing dimension-proof method, or does it need a Mathlib-absent general theorem?
Tie-break between thread 27's "cheap orbit-dimension count" read and the route-c formaliser's Codex
"WALL" read.*

## VERDICT (one line)

**(b) MATHLIB-ABSENT.** Step B is **not** reachable from the engine's existing orbit-dimension /
catenary machinery with small lemmas. The engine's dimension method is built for a **single
`G_d`-orbit closure** (an irreducible variety, via `trdeg` of a pullback into the **group's**
coordinate ring `O(G_d)`); the sweep `Σ^r = H·F` is the associated bundle `H ×^{Stab} F` over a
positive-dimensional **reducible** `F`, for which that method gives nothing. The genuinely-needed
input is a relative/product/fibre-dimension theorem (equivalently the exact-rank chart trivialization
+ flatness), which is the **same wall** the engine already names `cited_bundle_shift`. A decorrelated
`gpt-5.5`-xhigh Codex consult concurs independently. **Recommendation: Step B should remain the named
Cited residual** unless the controller commits to the ~8–12-module exact-rank chart-trivialization
build (no smaller than the wall it replaces).

This adjudicates **for** the route-c formaliser's Codex and **against** thread 27's read.

---

## How the engine actually proves a dimension (the crux, file:line)

The engine computes `varietyDim` exactly ONE way, and it is special to a single orbit. Chain:

1. **`varietyDim Z := (ringKrullDim (R ⧸ vanishingIdeal Z)).unbotD 0`**
   (`NullstellensatzCodim.lean:139`). Reads `Z` only through its vanishing ideal.
2. **Single-orbit pullback identity** (`OrbitPullbackDim.lean:74`,
   `varietyDim_eq_ringKrullDim_range_orbitPullback`): for the closure of ONE `G_d`-orbit `Z_M =
   orbitRankLocus M`, `varietyDim Z_M = ringKrullDim((orbitPullback M).range)`. Here
   `orbitPullback M : R →ₐ[k] groupRing d` is the pullback of the orbit-parametrisation map `μ_M :
   G_d → Rep_d`, `P ↦ P•M` (`OrbitVariety.lean:167`), and **`groupRing d = O(G_d) = Localization.Away
   Δ`** — the coordinate ring of the **GROUP** (`OrbitVariety.lean:96`). Proof: `vanishingIdeal O_M =
   ker μ_M^*` (orbit↔kernel, `OrbitVariety.lean:320`) + 1st iso theorem.
3. **`ringKrullDim = trdeg`** (`AffineNoetherRank.lean:81`): the range is an f.g. **domain** (a
   subalgebra of the domain `O(G_d)`, `OrbitPullbackDim.lean:42`); Noether-normalisation rank `s`
   forces both `ringKrullDim = s` and `trdeg = s` via the tower `trdeg_add_eq`
   (`AffineNoetherRank.lean:40`). **`trdeg_add_eq` is tower additivity only — NOT `trdeg(A⊗_k B) =
   trdeg A + trdeg B`.**
4. **Voigt squeeze to orbit-stabilizer** (`VoigtDischarge.lean:38`): `varietyDim Z_M =
   finrank(range δ⁰)` = `dim G_d − dim Stab_{G_d}(M)` (char 0, alg-closed), via a char-0 differential
   criterion (`JacobianTrdeg.lean`, formal smoothness of the fraction field of `O(G_d)`).

So the engine's reusable dimension lemma is: **`varietyDim(closure of ONE `G_d`-orbit) = trdeg of
the range of that orbit's parametrisation-pullback into `O(G_d)` = dim G_d − dim Stab`.** Every
ingredient (domain-ness, the fraction field, the differential criterion) requires the object to be
**a single orbit** parametrised by **the group**.

## The catenary bridge requires irreducibility (the second lever, and why it also fails)

`varietyDim` and `codimRepCanonical` are linked by the catenary `height + varietyDim = card`, but the
bridge is **PRIME-gated**:

- `height_vanishingIdeal_add_varietyDim_eq_card` (`NullstellensatzCodim.lean:147`) and
  `codimRepCanonical_eq_card_sub_varietyDim` (`:201`) both take `hp : (vanishingIdeal Z).IsPrime`.
- The δ thermometer `varietyDim Mat^{≤r} = δ` (`DeterminantalStratumDim.lean:229`) works **only
  because `Mat^{≤r}` is irreducible** — for `N=1` it IS a single orbit closure, prime ideal
  (`:198`), so the catenary applies. This is exactly the lever that does **not** extend.

`Σ^r`, `Σ̄^r`, and `F` are all **reducible** (cert §1.1: `(3,3,3) r=1` fibre has components of dims
`10,9,9`). So:
- **`varietyDim Σ̄^r = card − C` (thread.md Step D) is NOT landed.** The engine has only
  `codimRepCanonical Σ̄^r = C` (`SigmaCodim.lean:136`), proved as a **height = min over orbit-closure
  components** — NOT via `card − varietyDim`. Converting it to `varietyDim Σ̄^r = card − C` needs a
  reducible-locus catenary (min-over-components for height, dual max for dim), which the engine does
  not have. This is a **second gap** beyond Step B.
- The conditional assembly `FibreCodimSweepAssembly.lean:51` already isolates BOTH gaps as named
  hypotheses: `hSweepDim : varietyDim F = card − C − δ` (= Steps B+C+D bundled) and `hFcat :
  codim F + varietyDim F = card` (the reducible catenary for F). Everything around them is
  machine-checked. The reachability question reduces exactly to discharging `hSweepDim`/`hFcat`.

## What route c HAS landed (the reachable structural part)

- **The set-level sweep `Σ^r = ⋃_P (P•·)''F`** (`EndBaseChangeSweep.lean:81`,
  `productRankLocus_eq_iUnion_smul_fibre`, sorry-free). A union over the **whole** `BaseChangeGroup`,
  not a `Stab`-quotient.
- **H-equivariance + rank-preservation + G1 codim-constancy of translates**
  (`EndBaseChangeSweep.lean:45,95`; `mult_smul`, `exists_baseChange_of_rank_eq`,
  `codimRepCanonical_fibre_eq_of_rank_eq` in `FibreNormalForm`/`BaseChange`). These transport
  *codimension* between rank-`r` fibres — they do **not** compute the common value.

The `EndBaseChangeSweep.lean:16-19` docstring already states the dimension consequence is "the one
genuinely hard rung … whether it is buildable … or needs a Mathlib-absent base-change/product-dimension
theorem is **under adjudication**." This recon resolves that adjudication: **needs the absent theorem.**

## Why the orbit-stabilizer machinery does NOT extend (the three concrete attempts)

**(a) Present `Σ^r = H·F` as one orbit closure?** No. `F` is positive-dimensional and reducible, so
`H·F` is a *family* of H-orbits (one per point of `F`), not a single orbit. The engine's chain 2–4 is
parametrised by a single point `M` and the group `G_d`; there is no point `M` and group `G` with
`closure(G·M) = Σ^r`. Chain 2–4 yields nothing.

**(b) Pull back the action map `α : H × F → Σ^r`?** The analogous object is `α^* : R → O(H×F) =
O(H) ⊗_k O(F)`. To get `dim Σ^r = trdeg(α^*.range) = δ + trdeg(O F)` you need
`trdeg(O(H) ⊗_k O(F)) = trdeg O(H) + trdeg O(F)` (product/tensor trdeg). The engine's `trdeg_add_eq`
is **tower** additivity, not product additivity — it gives nothing here. And `O(F)` is **not a
domain** (`F` reducible), so `trdeg O(F)` is not even the right invariant; it must be a
componentwise/height object. Product/tensor trdeg is **absent from Mathlib v4.29** (Codex grep + my
read: the only `trdeg_add_eq` use is the Noether tower at `AffineNoetherRank.lean:37).

**(c) Catenary/height nested route (`codim_{Σ̄^r} F = δ` directly)?** This needs "the generic fibre
of mult|_{Σ̄^r} over the δ-dim'l homogeneous base has codim = dim base" WITHOUT flatness/Chevalley.
Homogeneity gives all fibres over `Mat^{=r}` are H-isomorphic — but that transports codimension
between fibres (already landed, G1), it does **not** compute the common value. The hard inequality is
exactly the no-jump/generic-flatness point the engine already names as the wall
(`FibreCodim.lean:16`, `FibreDimFibration.lean:17`: "mult is **not flat** — the fibre dimension
*jumps* as the rank drops", `Algebra.HasGoingDown` fails).

## The smallest missing piece, named precisely

The honest minimal theorem is an **affine locally-trivial fibration / associated-bundle dimension
theorem** specialised to this situation:

> `mult⁻¹(Mat^{=r}) ≃_loc Mat^{=r} × F_E`  ⟹  `varietyDim Σ^r = r(d_0+d_N−r) + varietyDim F_E`.

In codimension form this **IS** the engine's already-named Cited residual
`BundleShiftInterface.cited_bundle_shift` (`DLN/RlctPayoffGeneral.lean:87`):
`codimRepCanonical(fibre d B) = codimRepCanonical(productRankLocusLE d r) + δ`. Route c's "one new
rung" is, after the reductions, **logically equal to the wall it set out to avoid.**

**Rough module cost to build (Codex estimate, concur):** ~8–12 modules via explicit exact-rank pivot
charts + Schur/endpoint trivialization `R_total ≃ R_base ⊗_k F_E` + flatness + going-down (the
`ChartFlatnessProbe`/`FibreReducedTrivialization` lineage — threads 09/14/20 stalled here). A general
tensor/Krull product-dim theorem for reducible f.g. algebras is **≥ comparable (10–18 modules)** and
*still* would not handle the `Stab`-quotient/image step. The Step-C closure/density
(`dim Σ^r = dim Σ̄^r`) is downstream-useful but **not the crux** and cannot replace the
fibre-dimension theorem.

## The two failure modes if someone formalises Step B anyway (kill-conditions)

1. **Off-by-`dim Stab_H(E)`.** `α : H × F → Σ^r` is **not** generically finite — its fibres are
   `Stab_H(E)`-cosets of dim `dim Stab = dim H − δ`. Naively `dim Σ^r = dim H + dim F` (forgetting the
   quotient) is **wrong** by exactly `dim H − δ`. Any proof that does not explicitly produce
   `dim Stab` is suspect. (Both Codex consults flagged this as the top risk.)
2. **Treating `O(F)` as a domain / trdeg object.** `F` is reducible; the dimension must be the
   **max over components** (and codim the **min**), height-based — not a single `trdeg`. The engine's
   entire trdeg chain (domain-ness, fraction field, differential criterion) silently assumes
   irreducibility and is unsound applied to `F`.

## Bottom line for build-vs-name

- **Engine-reachable now:** the set sweep + codim-constancy of translates (LANDED). Nothing more from
  the orbit-dimension method.
- **The dimension value `δ + dim F`:** Mathlib- and engine-absent. It equals `cited_bundle_shift`.
- **Recommendation:** keep Step B (= `cited_bundle_shift`) as the **named Cited residual**. Route c
  did **not** find a cheaper path — its "orbit-dimension count" is the bundle-dimension theorem in
  disguise. If the controller wants it unconditional, it is the ~8–12-module chart-trivialization
  build (route c does not shorten it; it only re-frames the same wall through `α`'s `Stab`-cosets).

*Artefacts: `codex/sweepdim-orbitstab-{prompt,answer}.md` (decorrelated gpt-5.5 xhigh).*
