# Thread 31 — orbit-dimension route to `hSweep`: reachability adjudication

*Seat: pen-and-paper, witness direction (try HARDEST to construct a Lean-v4.29-reachable route to
`hSweep` through the engine's LANDED orbit-dimension machinery; if none, report the precise
obstruction). Read-only — no Lean writes, no builds. Decorrelated xhigh Codex fired independently.*

## VERDICT (one line)

**WALL CONFIRMED.** The orbit-dimension route ALSO needs a Mathlib-absent theorem — the
**reducible affine relative/image fibre-dimension theorem** `X` = "for a dominant finite-type
morphism `f : V → W` of (possibly reducible) affine `k`-varieties with all fibres of uniform
dimension `e`, `varietyDim V = varietyDim W + e`" — and the orbit-pullback machinery's
load-bearing precondition (**the pullback range is a DOMAIN**) FAILS for the sweep map, because
`Σ^r` and `F` are reducible. The landed `OrbitPullbackDim`/`OrbitImageDim`/`JacobianTrdeg` chain is
a SINGLE-IRREDUCIBLE-ORBIT method (`O(G_d)` is a domain, `dim = trdeg`); it does **not** transport
to the `H`-sweep of a reducible fibre. Sub-library estimate ~12-20 modules (abstract `X`), the same
*class* of missing infrastructure (product-dimension + reducible-component/minimal-prime + relative
fibre-dimension) as the chart route's wall — not cheaper, not genuinely decorrelated from it.

---

## The decisive structural asymmetry (the crux)

The landed orbit-dimension method (`OrbitPullbackDim.varietyDim_eq_ringKrullDim_range_orbitPullback`)
computes the dimension of **ONE irreducible `G_d`-orbit closure** `Z_M = canonicalCoord '' orbitRankLocus M`:

```
varietyDim Z_M = (ringKrullDim (orbitPullback M).range).unbotD 0           -- LANDED
```

It works because (verified in `OrbitVariety.lean`, `OrbitPullbackDim.lean`):

- `orbitPullback M = μ_M^* = aeval (genericOrbitCoord M)` lands in `groupRing d = O(G_d) =
  Localization.Away Δ` of `MvPolynomial (GroupCoord d) k`, which is a **DOMAIN**
  (`groupRing_isDomain`, `OrbitVariety.lean:100`).
- Hence `(orbitPullback M).range` is a subalgebra of a domain, so a **DOMAIN**
  (`isDomain_range_orbitPullback`, `OrbitPullbackDim.lean:42`).
- A domain ⟹ `ringKrullDim = trdeg` (`JacobianTrdeg`, the whole `genericDifferentialRank` /
  `DiffIndepCriterion` machinery is stated `[IsDomain B]` and uses `FractionRing B` —
  `JacobianTrdeg.lean:50,79,118`).
- `Z_M` irreducible ⟸ `vanishingIdeal Z_M = ker μ_M^*` is **prime** (kernel into a domain,
  `isPrime_vanishingIdeal_orbitSet`, `OrbitVariety.lean:372`).

**`Σ^r` and `F` are NOT single irreducible `G_d`-orbit closures.** They are swept by the
*endpoint* group `H = GL_{d_N} × GL_{d_0}` (inner units telescope away in `mult`,
`FibreNormalForm.mult_smul`), and:

- `Σ̄^r = productRankLocusLE d r = ⋃_M Ō_M` is a union of **multiple** orbit closures, one per
  corner-`≤ r` rank pattern (`SigmaStratification`, `SigmaComponents` G3). Its top-dimensional
  components number `θ = numTop d r` — generically `θ > 1` (the WHOLE POINT of the `(C,θ)` paper).
  `Σ̄^r` is genuinely **reducible**.
- `F = fibre d B` is reducible: the (3,3,3), `r=1` anchor has `F`-components of dims `10, 9, 9`
  (thread 29 `flatness_probe.sing`); `Σ̄^r` there `15, 14, 14`. Both NON-equidimensional.

The analogous "sweep pullback" `α^* : O(Σ^r) → O(H × F)` lands in `O(H) ⊗_k O(F)`. Because `F` is
reducible, `O(F)` has **zero divisors**, so `O(H) ⊗_k O(F)` is **NOT a domain** — and neither is
`(α^*).range ≃ O(Σ^r)` (since `Σ^r` reducible). The domain hypothesis that the ENTIRE landed
`trdeg = ringKrullDim` chain rests on **fails at the first step**. There is no `varietyDim Σ^r =
trdeg(range α^*)` to invoke.

---

## The sharp questions, answered

### Q1. Does `varietyDim Σ^r = ringKrullDim(range α^*)` hold, and is `range α^*` a domain?

- The **set-level** identity `O(Σ^r) ≃ (α^*).range` is plausibly reachable (identify `ker α^* =
  vanishingIdeal Σ^r` by a tautological-pullback + dense-image argument, parallel to
  `vanishingIdeal_range_orbitMap_eq_ker`). So `varietyDim Σ^r = ringKrullDim((α^*).range)` is itself
  fine — it is the SET-level definition of `varietyDim` and radical-insensitive
  (`VarietyDimRadical`, landed).
- But `range α^*` is **NOT a domain** (Q1 the decisive part): `Σ^r` is reducible, so
  `O(Σ^r) = MvPolynomial / vanishingIdeal(Σ^r)` has zero divisors. **FACT** (from the engine's own
  `SigmaComponents`/`SigmaStratification` + the thread-29 reducibility anchor). Therefore the
  `ringKrullDim = trdeg` bridge — the engine's only route from `ringKrullDim(range)` to a computable
  number — **does not fire**. The landed machinery stops here.

### Q2. Is the additive split `δ ⊕ dim F` obtainable from trdeg additivity / the orbit structure?

No. The additive split needs the relative/fibre-dimension identity
`varietyDim Σ^r = varietyDim(H×F) − varietyDim(fibre of α) = (dim H + dim F) − (dim H − δ) = δ + dim F`.
Turning the **certified** uniform-fibre-dimension fact (the `α`-fibres are `Stab_H(E)`-cosets, all
of dim `dim H − δ`, by homogeneity — NO flatness) into the dimension equation is exactly a
**relative-dimension theorem for a dominant morphism**. The four candidate Mathlib hooks all fail:

- **(a) determinantal-ideal-generation theorem** — NOT directly needed by this route (the
  set-level pullback dodges the "`sigmaIdeal` = minor-ideal" step). Codex concurs.
- **(b) reducible-component / minimal-prime correspondence** — **NEEDED**: to even state
  `varietyDim = max over components` and to relate the `θ` orbit-closure components of `Σ̄^r` to the
  `H`-sweep components of `Σ^r`. This is part of the reducible wall.
- **(c) product iso `O(Σ^r) ≅ O(base) ⊗ O(F)`** (= the R2-3b-4 wall) — the chart route's wall; the
  orbit route does NOT take this literal step, but `O(H×F) = O(H) ⊗ O(F)` and its dimension
  `dim H + dim F` is the same Mathlib-absent **tensor-product Krull-dim** theorem
  (`ringKrullDim (A ⊗[k] B) = dim A + dim B`, ABSENT at v4.29).
- **(d) general relative/fibre-dimension theorem** — **THE unavoidable one**. This is `X` (below).

So the route is forced through **(b) + (d)** (and (c)'s tensor-dim sub-fact), the reducible
infrastructure — NOT avoided.

### Q3 (decisive). Is the orbit-dim route genuinely DIFFERENT in its absent dependency, or does it secretly need the SAME machinery?

**It secretly needs the SAME CLASS of machinery, hidden in the "uniform fibre dimension" step.**
The homogeneity argument supplies the fibre *dimension* of `α` (the `Stab`-coset count) cheaply and
non-circularly — that is genuine. But the implication

> uniform fibre dimension `e` of a dominant `f : V → W`  ⟹  `dim V = dim W + e`

is, for **reducible** `V`/`W`, precisely a **Chevalley / relative-dimension theorem** that Mathlib
v4.29 does not have, in ANY form (no `dim image`, no fibre-dimension semicontinuity, no
constructible-image dimension). The reducibility of `F` (and of `Σ^r`) **leaks in** through:
(i) `O(H×F)` is not a domain; (ii) `varietyDim` is `max` over components, so the fibre-dim ⟹
total-dim implication must be proven component-by-component AND the component bookkeeping (which
component of `H×F` maps onto which top component of `Σ^r`, with what fibre) supplied — the
minimal-prime correspondence. This is the same reducible-component wall the chart route hit, just
relocated from "the localized ideal splits up to radical" to "the relative-dimension theorem holds
for reducible source/target." **Not decorrelated; not cheaper.** Codex (decorrelated) reaches the
identical conclusion independently: *"it replaces explicit chart algebra with a broad
Chevalley/fibre-dimension/product/component sublibrary … it avoids the chart theorem only by
assuming a larger absent theorem."*

### Q4. Does reducing to ONE top component `F_0`, forming `H·F_0`, dodge the reducibility wall?

**Partially dodges reducibility — but lands on a DIFFERENT Mathlib-absent theorem, and re-incurs
the component correspondence.** Two residual gaps:

1. **The image-dimension equality is still absent.** With `F_0` a top irreducible component of `F`,
   `H × F_0` is irreducible and `Z_0 = closure(H·F_0)` is irreducible, so `O(Z_0)` IS a domain and
   the *philosophy* of the orbit-pullback method applies. BUT `H·F_0` is a **family sweep, not a
   single `G`-orbit**, so the residual is NOT the single-point orbit formula `dim(G·x) = dim G −
   dim Stab(x)` — it is the irreducible **fibre-dimension / constructible-image dimension theorem**

   ```
   dim closure(H·F_0) = dim(H × F_0) − dim Stab_H(E) = δ + dim F_0.
   ```

   **FACT: this is not in Mathlib v4.29.** Even the landed `OrbitImageDim` only proves a one-sided
   **inequality** `(ringKrullDim (orbitPullback M).range).unbotD 0 ≤ finrank (range δ⁰)`
   (`OrbitImageDim.lean:79` — every theorem there is `_le_`), conditional on the differential-rank
   bound `hA43_le`. The engine has **no landed `dim(orbit) = dim G − dim Stab` equality** even for a
   single orbit — it computes orbit dim via the determinantal-set identification
   `codimRepCanonical_orbitRankLocus_eq_codimForm` (`CThetaGeometric`), i.e. through Voigt + the
   box-move closure theorem L6.4, NOT through a stabilizer-dimension count. So the "single-orbit
   formula" the bypass would want is itself not a landed equality.

   Moreover, to USE the orbit-pullback equality for `Z_0`, one would need to exhibit `Z_0` as an
   `orbitRankLocus M` (a `G_d`-orbit closure / determinantal set) — but `closure(H·F_0)` is an
   `H`-sweep closure, and there is **no engine bridge** from `H`-sweep components to `G_d`-orbit
   closures (searched: none exists). Establishing `closure(H·F_0) = Ō_M` would itself be new
   determinantal/closure theory.

2. **The component correspondence returns.** To conclude `varietyDim Σ^r = varietyDim Z_0`, the
   bypass needs `Σ^r = ⋃_i H·F_i` and `varietyDim(finite union) = max_i varietyDim(H·F_i)` with
   `Z_0` attaining the max — i.e. the **finite irreducible-component decomposition + dim-of-union =
   max** facts, exactly the reducible-component infrastructure (the `varietyDim` max-over-union is
   reachable via `RadicalCatenary`-style minimal-prime algebra, ~2-3 modules, but it IS the wall's
   bookkeeping, not a dodge).

So Q4 trades the reducible-`O(F)` problem for the **irreducible image-dimension theorem** (gap 1,
the genuine new Mathlib-absent AG package) **plus** the component bookkeeping (gap 2). Net: no
dodge.

---

## The precise absent theorem(s) and whether they coincide with the chart route's

**Chart route's two walls** (from `plan.md` / the tide's SPECIFY):
1. determinantal-ideal-generation (`sigmaIdeal` IS the minor-generated ideal) — ABSENT;
2. reducible-component / minimal-prime correspondence (equal-height+radical ⇏ equal radical ideals
   for reducible loci) — ABSENT; plus the product-dimension `O(Σ^r) ≅ O(SchurLoc) ⊗ O(FibreAlg)`.

**Orbit route's wall** — the single tightest absent theorem:

> **`X` (reducible relative/image fibre-dimension):** for a dominant finite-type morphism
> `f : V → W` of affine `k`-varieties (possibly reducible) all of whose fibres have dimension `e`,
> `varietyDim V = varietyDim W + e`. Equivalently the irreducible specialisation
> `dim closure(image of irreducible V_0) = dim V_0 − (uniform fibre dim)`.

**Coincidence:** `X` is **not literally** the chart route's determinantal-ideal theorem (wall 1) —
the orbit route's set-level pullback genuinely dodges that. But `X`'s PROOF in Lean requires the
SAME underlying gaps as the chart route's wall 2 + product-dim: the **tensor-product Krull-dim**
theorem (`ringKrullDim (A ⊗[k] B) = dim A + dim B`, ABSENT; this is `O(H×F)`'s dimension), the
**reducible-component / minimal-prime correspondence** (to handle `max` over components — chart wall
2), and a Chevalley-style relative-dimension statement that has no v4.29 home at all. So the two
routes share the reducible-infrastructure wall; the orbit route merely repackages it as one broad
AG theorem `X` instead of the chart route's two explicit ones.

**Honest sub-library estimate:** abstract `X` ~12-20 modules (Codex's count; matches the SPECIFY's
"route (b) generic-freeness ~14-22" ballpark, since `X` is essentially the EGA-IV fibre-dimension
package). A chart-local replacement is ~7-12 modules but re-incurs product-dimension + finite-cover
gluing + localized determinantal ideal control — i.e. the chart route again. **No route ≤ a single
rung; all are sub-libraries of the same reducible-AG class.**

---

## Engine handles VERIFIED (file + name)

PRESENT (read and confirmed):
- `OrbitPullbackDim.varietyDim_eq_ringKrullDim_range_orbitPullback` — the orbit-dim EQUALITY, but
  **only for the irreducible `Z_M`** (range is a domain). `OrbitPullbackDim.lean:74`.
- `OrbitPullbackDim.isDomain_range_orbitPullback` — the domain instance, the load-bearing
  precondition that FAILS for the sweep. `OrbitPullbackDim.lean:42`.
- `OrbitImageDim.*` — all `_le_` (one-sided inequality `varietyDim ≤ finrank(range δ⁰)`), conditional
  on `hA43_le`; NO orbit-dimension equality. `OrbitImageDim.lean:79,95,134,154`.
- `JacobianTrdeg.{genericDifferentialRank, DiffIndepCriterion, trdeg_adjoin_le_genericDifferentialRank}`
  — all stated `[IsDomain B]`, via `FractionRing B`. Inapplicable to reducible `O(F)`.
  `JacobianTrdeg.lean:50,79,201`.
- `EndBaseChangeSweep.{mem_productRankLocus_iff_mem_sweep, productRankLocus_eq_iUnion_smul_fibre}` —
  the sweep SET identity `Σ^r = ⋃_P (P•)''F`. `EndBaseChangeSweep.lean:64,81`.
- `FibreNormalForm.{mult_smul, exists_baseChange_of_rank_eq, codimRepCanonical_fibre_eq_of_rank_eq}`
  — H-equivariance, `Mat^{=r}` is one H-orbit, G1 codim-constancy. `FibreNormalForm.lean:77,279,322`.
- `SigmaStratification` / `SigmaComponents` — `Σ̄^r = ⋃_M Ō_M`, `θ` top components (reducibility).
- `DeterminantalStratumDim.varietyDim_productRankLocusLE_stratum` — `dim Mat^{≤r} = δ`, via the
  `N=1` SINGLE-orbit specialisation (where `Σ̄^r` IS one irreducible `orbitRankLocus M₀`) —
  confirms the orbit-dim method works ONLY when the locus is a single orbit closure.
  `DeterminantalStratumDim.lean:17` ("the orbit-image dimension route did NOT need a new orbit map"
  — precisely because `N=1` rank-`≤r` is irreducible).
- `RouteCAssembly.codimRepCanonical_fibre_eq_cCodim_add_shift_of_sweep` — consumes `hSweep` as a
  named hypothesis. `RouteCAssembly.lean:47`.
- `VarietyDimRadical.*`, `RadicalCatenary.*` — radical-insensitivity shield + reducible catenary
  (`codim = card − dim`); the `max`-over-components bookkeeping the bypass's gap 2 would build on.

SEARCHED AND ABSENT (in engine + Mathlib v4.29):
- Any `dim(orbit) = dim G − dim Stab` EQUALITY (stabilizer-dimension orbit formula). Engine computes
  orbit dim via determinantal-set Voigt, not stabilizers.
- Any `H`-sweep-component ↔ `G_d`-orbit-closure bridge.
- `ringKrullDim (A ⊗[k] B) = dim A + dim B`; `trdeg` of a tensor product.
- Any relative/fibre-dimension (Chevalley) theorem for a dominant morphism, reducible or irreducible.

---

## Decorrelated Codex (xhigh, gpt-5.x) — independent read

Fired with hypothesis WITHHELD (frame + facts + the four questions only). Codex's VERDICT
independently matches: *"ORBIT-DIM ROUTE ALSO WALLED: it needs a reducible affine
fibre-dimension/image-dimension theorem … it avoids the chart theorem only by assuming a larger
absent theorem."* On Q1 it independently flagged the **domain-failure** (`(α*).range` not a domain
when `Σ^r` reducible) as the breakpoint of the landed `ringKrullDim = trdeg` chain. On Q4 it
independently flagged that the residual is the **irreducible fibre-dimension / constructible-image
dimension theorem**, NOT the single-point orbit formula, and that the component correspondence
returns. Cost ~12-20 modules (abstract) / ~7-12 (chart-local). Transcript:
`codex/orbit-dim-route-{prompt,answer}.md`. **Agree** with the adjudication on every load-bearing
point; the decorrelated read found no route I missed.

---

## Close

- **Firmest result:** the orbit-dimension route is WALLED by the same reducible-AG infrastructure as
  the chart route. The landed orbit-pullback method is a single-irreducible-orbit `ringKrullDim =
  trdeg` machine whose **domain precondition fails** for the `H`-sweep of the reducible `F`; the
  residual is the Mathlib-absent reducible relative/image fibre-dimension theorem `X`.
- **Most likely thing to break this verdict:** if a sufficiently weak form of `X` is reachable
  cheaply by routing through the engine's LANDED per-component pieces — specifically, the Q4 bypass
  via ONE top component `F_0`, IF one can (i) cheaply realise `closure(H·F_0)` as an irreducible set
  whose `varietyDim` the engine computes, and (ii) supply only the `varietyDim(union) = max` +
  per-component-onto bookkeeping (the `RadicalCatenary` direction, ~2-3 modules) rather than the
  full Chevalley package. The break point is whether `dim closure(H·F_0) = δ + dim F_0` (an
  IRREDUCIBLE image-dimension equality) is reachable without the general fibre-dimension theorem —
  e.g. by an explicit transcendence-basis / dominant-map trdeg argument on the irreducible `H·F_0`
  (where `O(closure(H·F_0))` IS a domain, so `dim = trdeg` is back in play).
- **Next construction/consult that would settle the open part:** a focused SPECIFY on the Q4
  irreducible bypass — does `dim closure(H·F_0) = δ + dim F_0` follow from `trdeg` additivity
  (`trdeg_add_eq`, Stacks 030H, which DOES apply now that the top ring `O(closure(H·F_0))` is a
  domain) applied to the tower `k ⊆ O(Mat^{=r}) ⊆ O(closure(H·F_0))` (image of the dominant
  `mult|`)? That is the one place the reducibility wall genuinely lifts (single irreducible
  component ⟹ domain ⟹ `trdeg_add_eq` fires); the residual is then NOT a Chevalley theorem but the
  identification of `relative_trdeg = dim F_0` at the generic point — the no-jump statement, which
  on an IRREDUCIBLE total space over an IRREDUCIBLE base may be reachable by generic flatness
  (`GenericFreeness`, partially landed). That sub-question is the highest-value follow-up; this
  dispatch did not have a Lean-write mandate to test it.
