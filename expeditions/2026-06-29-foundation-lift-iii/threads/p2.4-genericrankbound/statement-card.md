# Statement card — P2.4 B1 `GenericRankBound` (A4.3) on `AffineGVarietyDeformation`

The squeeze's **submersion (≤) bound** lifted to the abstract deformation carrier, with the
Maurer–Cartan factorisation (H1) as a **named hypothesis** the DLN matrix-tuple discharges. The DLN
keystone `genericDifferentialRank_genericOrbitCoord_le_finrank_range_deformationδ` is re-derived from
the abstract B1 (signature unchanged; all consumers green).

**CRUX outcome:** the **forward** (H1) signature in the P2.0 report §3 / the brief steps (1)/(3)
(`span_K {D f_x} ≤ range (L ∘ δ.baseChange K)`, `δ : C0 → C1`) is **NOT dischargeable** by the DLN
model. The dischargeable shape is the **transpose/adjoint** factorisation (an abstract adjoint
`δAdj : C1 → C0` + a rank-tie `finrank (range δAdj) = finrank (range δ)`). Both established by the
GUARD scratch (uncommitted): the transpose discharge built sorry-free; the forward one stalls exactly
at the predicted spot. **This signature change feeds the controller-routed decorrelated review.**

---

## (0) Deformation carrier extension

> **Claim.** The base carrier `AffineGVariety` extends with deformation data `(C0, C1, δ : C0 → C1)`.
>
> - **Lean:** `AlgebraicGeometry.Group.Orbit.AffineGVarietyDeformation`
>   (`lean/DLNFibre/Core/AlgebraicGeometry/Group/Orbit/Deformation.lean`)
> - **Gloss.** `structure AffineGVarietyDeformation (k) [Field k] extends AffineGVariety k where`
>   `(C0 C1 : Type u) [AddCommGroup·] [Module k ·] [FiniteDimensional k ·]` `(δ : C0 →ₗ[k] C1)`.
> - **Proved.** Data only; `[FiniteDimensional k C0/C1]` are carrier fields (the deformation spaces
>   are finite-dimensional — `finrank` meaningful, base-change preserves rank). `[Finite ρ]` is NOT on
>   the carrier (P2.3 discipline) — carried on the rank lemma where the finite family is needed.
> - **Status.** sorry-free, axiom-clean.

## (1) (H1) — the (transpose) Maurer–Cartan factorisation hypothesis

> **Claim.** A `Prop` on `(δAdj : C1 → C0, L : K ⊗ C0 → Ω)`, `K = Frac G.R`, `Ω = Ω[K⁄k]`:
> `span_K {D_k(algebraMap (f_x))} ≤ range (L ∘ (δAdj.baseChange K))`.
>
> - **Lean:** `AlgebraicGeometry.Group.Orbit.AffineGVarietyDeformation.DifferentialFactors`
>   (`…/Orbit/Deformation.lean`)
> - **Gloss.** `def DifferentialFactors (δAdj : G.C1 →ₗ[k] G.C0) (L : (Frac G.R ⊗[k] G.C0) →ₗ[Frac G.R]`
>   `Ω[Frac G.R⁄k]) : Prop := Submodule.span (Frac G.R) (Set.range fun x => D k (Frac G.R)`
>   `(algebraMap G.R (Frac G.R) (G.fρ x))) ≤ LinearMap.range (L.comp (δAdj.baseChange (Frac G.R)))`.
> - **name = content.** It is the transpose Maurer–Cartan factorisation **when** `G.fρ` is an
>   orbit-map pullback — an abstract **input**, NOT an assertion of any action/orbit structure on a
>   bare carrier (conditional docstring). The forward form (`L ∘ δ.baseChange`) is recorded in the
>   module docstring as the de-risked non-viable shape.
> - **Status.** definition; sorry-free.

## (3) Abstract B1 — the submersion rank bound (A4.3)

> **Claim.** For finite `G.ρ`, with (H1) `DifferentialFactors G δAdj L` and the rank-tie
> `finrank (range δAdj) = finrank (range G.δ)`:
> `genericDifferentialRank k G.R G.fρ ≤ finrank k (range G.δ)`.
>
> - **Lean:** `AlgebraicGeometry.Group.Orbit.AffineGVarietyDeformation.genericRankBound`
>   (`…/Orbit/Deformation.lean`)
> - **Gloss.** `[Fintype G.ρ] (δAdj) (L) (hMC : G.DifferentialFactors δAdj L)`
>   `(hRank : finrank k (range δAdj) = finrank k (range G.δ)) :`
>   `DLNFibre.Core.genericDifferentialRank k G.R G.fρ ≤ finrank k (range G.δ)`.
> - **Proved.** Char-free route, **no `deltaT`/`dualMap` inside B1**: `genericDifferentialRank =`
>   `finrank_K (span_K {D f_x}) ≤[hMC, Submodule.finrank_mono] finrank_K (range (L ∘ δAdj.bc))`
>   `≤[range_comp + Submodule.finrank_map_le] finrank_K (range (δAdj.bc))`
>   `=[finrank_range_baseChange, V2] finrank_k (range δAdj) =[hRank] finrank_k (range δ)`.
> - **Assumed.** `[Fintype G.ρ]` (the `genericDifferentialRank` finite family); (H1) + the rank-tie as
>   hypotheses. No char hypothesis (char-0 A4.2 lives in the *trdeg* wrapper one layer up).
> - **Cited.** none new. Uses Phase-1 `finrank_range_baseChange` (V2) + Mathlib `finrank_mono`/
>   `finrank_map_le`/`finiteDimensional_range`.
> - **Status.** sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`.

## (2) DLN discharge of (H1)

> **Claim.** The DLN deformation instance `dlnOrbitDef M` satisfies (H1) with adjoint `deltaT M`,
> transport `(pairMC M).liftBaseChange K`.
>
> - **Lean:** `DLNFibre.Core.dlnOrbitDef` (the instance) + `DLNFibre.Core.dlnOrbitDef_differentialFactors`
>   (the discharge) + `DLNFibre.Core.pairMC` (the transport) (`lean/DLNFibre/Core/OrbitDifferentialRank.lean`)
> - **Gloss.** `dlnOrbitDef M : AffineGVarietyDeformation k` with `toAffineGVariety := dlnOrbit M`,
>   `C0 := cochain0 d d`, `C1 := cochain1 d d`, `δ := deformationδ M M` (the `R`, `fρ`, `δ` are the DLN
>   ones by `rfl`). `dlnOrbitDef_differentialFactors M : (dlnOrbitDef M).DifferentialFactors (deltaT M)`
>   `((pairMC M).liftBaseChange (Frac (groupRing d)))`.
> - **Proved.** Exactly the old keystone's `hbr`/`hgen`/`hSW` span-containment: each `D(f_x)` is the
>   conjugated Maurer–Cartan bracket (`D_genericOrbitCoord_eq` + `D_orbit_conj`), a `K`-combination of
>   single-entry brackets `bracketG (mcΘ M)`, each hit by `(pairMC ∘ deltaT)(single)` via
>   `pair_deltaT_eq_pair_deformationδ`; `range_liftBaseChange` + `(pairMC.lift) ∘ (deltaT.bc) =`
>   `(pairMC ∘ deltaT).lift` close it. The rank-tie is `finrank_range_deltaT` (trace self-duality;
>   the matrix-specific dual transport stays the DLN detail).
> - **Status.** sorry-free, axiom-clean.

## (4) DLN keystone re-derivation

> **Claim.** `genericDifferentialRank_genericOrbitCoord_le_finrank_range_deformationδ` —
> **signature unchanged** — re-derived from abstract B1 + the discharge.
>
> - **Lean:** `DLNFibre.Core.genericDifferentialRank_genericOrbitCoord_le_finrank_range_deformationδ`
>   (`lean/DLNFibre/Core/OrbitDifferentialRank.lean`)
> - **Proved.** `genericRankBound (dlnOrbitDef M) (deltaT M) ((pairMC M).liftBaseChange K)`
>   `(dlnOrbitDef_differentialFactors M) (finrank_range_deltaT M)` (one `haveI : Fintype (dlnOrbitDef`
>   `M).ρ` from `Fintype (RepCoord d)`, then `exact`). The old ~70-line monolithic proof is **collapsed**
>   into the abstract engine + the discharge.
> - **Consumers (sweep).** `ringKrullDim_range_orbitPullback_le_finrank_range_deformationδ_unconditional`
>   and `varietyDim_orbitRankLocus_le_finrank_range_deformationδ_unconditional` (same file) and
>   `VoigtDischarge` consume it unchanged; full aggregator build green (3826 jobs). `deltaT`/`traceEquiv`/
>   `finrank_range_deltaT` stay DLN-instance details (still confined to `OrbitDifferentialRank.lean`).
> - **Status.** sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`.

---

## Files

- NEW `lean/DLNFibre/Core/AlgebraicGeometry/Group/Orbit/Deformation.lean` — the carrier extension +
  (H1) `DifferentialFactors` (transpose form) + abstract B1 `genericRankBound`. Bare Mathlib-mirror
  namespace `AlgebraicGeometry.Group.Orbit` (L7). Wired into the aggregator transitively via
  `OrbitDifferentialRank` (which now imports it).
- EDIT `lean/DLNFibre/Core/OrbitDifferentialRank.lean` — import the carrier; add `pairMC` (top-level,
  was a local `set`), `dlnOrbitDef`, `dlnOrbitDef_differentialFactors`; collapse the keystone to the
  B1 transport; module + theorem docstrings updated. Keystone signature unchanged.

## Gates

- Full aggregator build `scripts/lb DLNFibre` — green, **3826 jobs**.
- `scripts/sorries` — **0** sorry / 0 axiom / 0 native_decide / 0 #exit.
- `#print axioms` = `[propext, Classical.choice, Quot.sound]` on: abstract B1 `genericRankBound`; the
  discharge `dlnOrbitDef_differentialFactors`; the re-derived keystone; the downstream
  `varietyDim_orbitRankLocus_le_finrank_range_deformationδ_unconditional`.
- L7 (bare namespace), L4 (codepoint long-line: my region clean; pre-existing >100cp lines in
  `OrbitDifferentialRank` untouched).

## CRUX FINDING + signature concern feeding P2.5 (flag for decorrelated review)

**The forward (H1) is not dischargeable.** Forward `span_K {D f_x} ≤ range (L ∘ δ.baseChange K)`
(`δ : C0 → C1`): `range (L ∘ δ.bc) = L(range (δ.bc)) = L(K ⊗ range δ)`, so `L` only ever sees the
*coboundary image* `range δ ⊊ C1`. But the orbit-coordinate differentials are `D(f_x) =`
`pairBracket(single_x)` — pairings of the Maurer–Cartan bracket against **single** `C1` entries, which
are NOT in `range δ`. So no `L` recovers them from `range (δ.bc)` (a single `L` of `range (δ.bc)` has
the right *dimension* but the construction would need the bound it is trying to prove — circular).
GUARD scratch: the forward discharge stalls at `bracketG (mcΘ) i a b ∈ range (L ∘ δ.bc)`.

**The transpose (H1) discharges.** Carry an abstract adjoint `δAdj : C1 → C0` + rank-tie
`finrank (range δAdj) = finrank (range δ)`; assert `span ≤ range (L ∘ δAdj.bc)`, `L : K ⊗ C0 → Ω`.
DLN: `δAdj := deltaT M`, `L := pairMC.lift`, rank-tie `= finrank_range_deltaT`. This IS the old
keystone proof, recast — GUARD scratch built it sorry-free. This is the P2.0 report §1-(iii)-blessed
"carry `δAdj` with `rank δAdj = rank δ`" option; the brief step (3) hope of "no deltaT/dualMap" holds
for **B1 itself** (B1's body uses neither) but NOT for the (H1) carrier (the adjoint + rank-tie carry
the transpose; the matrix self-duality is the DLN detail). name = content is preserved: `δAdj` and its
rank-tie are abstract inputs.

**Feeds P2.5:** the same forward-vs-transpose asymmetry is the live question for (H2)
(infinitesimal-action) and the cotangent injection — whether the dual-number ideal-killing packages as
a forward map or needs an adjoint/transport carrier. P2.5 should pin its (H2) carrier with the same
GUARD-first discipline (write the concrete DLN discharge before fixing the abstract signature).
