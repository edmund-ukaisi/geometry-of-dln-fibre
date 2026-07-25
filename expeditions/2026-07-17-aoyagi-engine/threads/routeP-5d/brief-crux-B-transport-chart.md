# (B)-lane brief — RUNG 5d crux (B): generic `transport_chart` + the (3,3,4) K-orbit leaf-Chart family

**Lane:** fresh `lean-formaliser`, off routeP HEAD (`cee38f4ab` or later), branch
`expedition/aoyagi-engine-5d-transport`. **Owner:** controller-spawned; supervised by routeP-p1.
**Frame:** provenance-verified DETAIL-AT-SCALE (the general-`d` cover core), NOT a monument. Bounded +
templated (the `#86(B)` K-transport / pnp-hcover 5-lemma template). Sorry-free, `#print axioms`
clean-three `[propext, Classical.choice, Quot.sound]`.

## Where this sits (the (i)/(ii)/(B) split)

Rung 5d assembles the concrete (3,3,4) `Resolution (coreGen dvec eWrap) 0` + `AtlasRealizesExponents`.
Banked already (routeP):
- **5a** `Corank2Realize334` — the realization seam; `resolution334_of_ballCover_ofValues` (the
  per-chart, fan-invariant assembly) is the WIRING TARGET.
- **5d part-1** `Corank2Chart334` — the complete canonical chart `chart334 : Chart (coreGen dvec eWrap) 0`
  (the K-orbit REPRESENTATIVE), + `gWrap_eq_pathMap` (crux A, gWrap is a fanOfSteps leaf).
- **(ii)** [decomp-5b, SEPARATE] — the K-orbit COVER `ball 0 ρ ⊆ ⋃ c, (charts c).g '' (charts c).dom`
  (the `orbit_covers` residual; the box-inflation brick `shearH_covers`, `f = r + 2r²`). NOT this lane.

**This lane (B):** produce the θ-sized leaf-Chart FAMILY `charts : Fin numC → Chart (coreGen dvec eWrap) 0`
— the K-orbit of `chart334` — each a full certified `Chart`, with per-chart binding data feeding
`resolution334_of_ballCover_ofValues`'s `hval`/`hmin`. The cover charts (ii) and the certified charts (B)
MUST be the SAME family, so coordinate with decomp-5b on the orbit indexing.

## Deliverable

### 1. `transport_chart` (GENERIC — the reusable core)
Given `chart : Chart F x₀`, a coordinate permutation `σ : Equiv.Perm (Fin D)`, and the **equivariance**
of the family `F` under `σ` (the load-bearing hypothesis — see §Guards), produce
`Chart F x₀'` for the transported map `g' = permOf σ⁻¹ ∘ chart.g ∘ permOf σ` (exact conjugation TBD with
the K-action; `permOf σ w = w ∘ σ`). Transport the 5 field-groups (the 5-lemma template):
1. **hg0 / hg_cont / hg_analytic** — perm is a linear homeo; composition preserves continuity/analyticity;
   `g' 0 = 0` from `chart.hg0` + `permOf σ 0 = 0`.
2. **hjac** — `|jacDet g' u| = |jacDet chart.g (permOf σ u)|` (perm jacDet `= ±1`, absorbed by `|·|` —
   reuse `abs_jacDet_permCoord` from `Corank2ChartJac`); the jac exponent vector is `chart.jac ∘ σ`
   (values PRESERVED, axes permuted — the fan-invariance).
3. **hg_inj / hexcep** — `excep' = (permOf σ) ⁻¹' chart.excep`; null + measurable transport under the
   perm (measure-preserving linear iso); `InjOn` transports along the bijection.
4. **hideal_fwd / hideal_bwd** — `RegionRepresents` transports along `σ` using the equivariance of `F`
   (this is where `F`-equivariance is consumed: `F i ∘ g' = (F (σ·i) ∘ chart.g) ∘ permOf σ` up to the
   perm, so the cofactors conjugate). The **crux of (B)** — the coupled ideal identity is what makes the
   transport non-trivial; the perm is unimodular so ideals are preserved, but the RegionRepresents
   plumbing (continuous cofactors, `.comp` with the perm homeo) is the real work.
5. **bexp / k₀ / hchain / hbind / hunit_mult** — `bexp' = chart.bexp ∘ (σ on the axis)`; binding axes
   permute; VALUES preserved (so `hbind`/`hunit_mult`/`hchain` transport).

### 2. The (3,3,4) K-orbit application
- Pin the coordinate-permutation subgroup `K ≤ Equiv.Perm (Fin 21)` under which `coreGen dvec eWrap` is
  equivariant (the row/col symmetries of the (3,3,4) product; coordinate with routeP-p1 — I hold the
  gWrap / K-action context). The orbit of `chart334` under `K` is the leaf family.
- Emit `charts : Fin numC → Chart (coreGen dvec eWrap) 0` (numC = orbit size ≈ θ), `hne`, and the
  per-chart binding data: `hval : ∀ c a binding, (charts c).jac a + 1 = 8 ∨ = 9`,
  `hmin : ∃ c a binding, (charts c).jac a + 1 = 8` — FAN-INVARIANT (jac values preserved under σ), so
  they follow uniformly from `chart334`'s `{8,9}` binding via the transport.
- Feed `resolution334_of_ballCover_ofValues numC charts hne ρ hρ hcov hval hmin` (with decomp-5b's `hcov`)
  → `∃ res, AtlasRealizesExponents dvec res` = the (3,3,4) instance of `exists_coreResolution`'s :311.

## Guards / kill-conditions
- **`F`-equivariance is the load-bearing hypothesis** — PROVE `coreGen dvec eWrap` is `K`-equivariant
  (do NOT assume it). If the intended `K` does not fix `coreGen` (up to index perm), the transport of
  `hideal` fails — STOP + report (this is the real gate for (B)).
- **`orbit_covers` is NOT this lane** — the cover (`ball ⊆ ⋃ orbit images`) is decomp-5b's (ii). If
  decomp-5b finds the orbit doesn't cover, that re-opens the provenance residual — flag, don't build
  around it.
- Sorry-free; clean-three (force-elab `#print axioms`, delete olean); do NOT edit `DLNFibre.lean`.
- Base = `chart334` + `abs_jacDet_permCoord` (banked); reuse, don't re-derive the canonical chart.

## Estimate (line-count, no wall-clock)
`transport_chart` (generic): ~150–250 LoC (the 5 field-groups; `hideal` RegionRepresents-along-perm is
the bulk). K-action def + equivariance of `coreGen`: ~50–100 LoC. Orbit family + binding data + wiring:
~50–100 LoC. Sub-tasks: (1) `permOf`/perm-homeo lemmas (jacDet, measure-preserving, analytic); (2)
`RegionRepresents.comp_perm` transport; (3) `transport_chart` assembly; (4) `coreGen` `K`-equivariance;
(5) orbit family + `resolution334_of_ballCover_ofValues` wiring.
