# Thread 31 — rung-3 chart freeness: the route-A make-or-break adjudication

*Seat: pen-and-paper, witness direction. MAKE-OR-BREAK of the primary set-level route to `hSweep`.
Read-only — no Lean writes, no builds. Decorrelated xhigh Codex fired independently. Exact-algebra
certificates on (2,2,2) r=1, deep N=3 (2,2,2,2) r=1, and (3,3,3) r=2.*

## VERDICT (one line)

**rung-3 HOLDS.** On the Schur chart `U = {detΔ ≠ 0}`, the δ off-diagonal/pivot coordinates
(`Δ, B12, B21` entries — the entries of `mult(A)` read in block form) are **FREE polynomial
generators over the fibre coordinate ring** `FibreAlg = O(F)`, with `B22` *Schur-determined* (not
free). The presentation is

> `O(Σ^r ∩ U) ≅ O(F)[Δ_ij, (B12)_iβ, (B21)_αj]_{detΔ}`  — a localized FREE polynomial extension,

so the `+δ` comes from the **LANDED** `MvPolynomial.ringKrullDim_of_isNoetherianRing` (any Noetherian
base, no domain hypothesis — `FibreAlg` reducible is fine). The route does **NOT** re-incur the absent
tensor theorem. Route A is **~7-10 modules total** (the dominant cost is *packaging* the iso as a
coordinate-ring `AlgEquiv` + the localization-no-drop + finite-cover glue, NOT the freeness). My
exact-algebra reading and a decorrelated xhigh Codex independently construct the **same** section,
the **same** δ free generators, and the **same** free presentation.

This **resolves the conflict** between the two peer adjudications: the `orbit-dim-route` doc's
"chart route hits the absent tensor theorem" verdict was about the *orbit-pullback/trdeg* machinery
(which needs `O(·)` to be a DOMAIN, and that fails for reducible `Σ^r`/`F`). The set-level chart
route uses **neither trdeg nor a domain** — it uses the free-polynomial-extension Krull-dim lemma,
which has no domain hypothesis. Reducibility of `F`/`Σ^r` does **not** obstruct the chart freeness,
because the section is built from the **Schur data of the single product matrix** `M = mult(A)`,
defined uniformly on the whole chart `U` regardless of which (of the θ) components a point lies on.

---

## The make-or-break, settled (exact algebra)

### The free presentation, in engine vocabulary

`M = mult(A) = [[Δ, B12], [B21, B22]]` (block sizes `r | (d_N−r)` × `r | (d_0−r)`). On `U = {detΔ≠0}`:

- **`rank M ≤ r ⟺ B22 = B21 Δ⁻¹ B12`** (Schur). FACT, via the determinant identity
  `det M = det(Δ) · det(Schur complement)` — verified at (3,3,3) r=2: `det M == det(Δ)·Schur`
  symbolically. The matrix heart is the LANDED `SchurGauge.schurComplement_normal_form`.
- **The δ = `r(d_N+d_0−r)` free base coordinates are exactly the entries of `Δ, B12, B21`.** FACT:
  `#Δ + #B12 + #B21 = r² + r(d_0−r) + (d_N−r)r = r(d_N+d_0−r) = δ`. The `B22` entries (the remaining
  `(d_N−r)(d_0−r)`) are Schur-determined, **not** free.

### The regular section/retraction giving the product structure (the certificate)

There is a regular section `s(M) = (P_N, P_0) ∈ H = GL_{d_N}×GL_{d_0}`, **localized only at `detΔ`**,
with `P_N E₀ P_0⁻¹ = M` for the normal-form target `E₀ = [[I_r,0],[0,0]]`:

> `P_N = [[Δ, 0],[B21, I]]`,  `P_0⁻¹ = [[I, Δ⁻¹B12],[0, I]]`  (Codex's form; equiv. to `endpointGauge`).

This is exactly the `SchurGauge.endpointGauge` structure (`H` at vertex 0, `L⁻¹` at vertex `last N`,
`1` interior). The retraction `φ(A) = s(mult A)⁻¹ · A` is regular (localized at `detΔ`) and is a
genuine **retraction onto F** (identity on F — verified). Hence a regular ISO of varieties

> `Φ : Σ^r ∩ U  ≅  S_U × F`,   `S_U` = the rank-`r` matrix Schur chart (dim δ).

**Round-trip VERIFIED both directions** at (2,2,2) r=1 (sympy, exact):
- `Φ: A ↦ (base=(u,v,w), fibre=(A₁ᶠ, A₂ᶠ))` with `u=M₁₁, v=M₁₂, w=M₂₁`,
  `A₁ᶠ=[[a, b−av/u],[c, d−cv/u]]`, `A₂ᶠ=[[e/u, f/u],[g−we/u, h−wf/u]]`.
- `A₂ᶠ A₁ᶠ = E₀` **exactly on `Σ^1∩U`**: the off-diagonal `(A₂ᶠA₁ᶠ)₁₁ = det(M)/u`, and
  `det M = det(A₁)·det(A₂)` vanishes on rank-1 (`(A₂ᶠA₁ᶠ)₁₁ · u = det M`, verified). So `φ` lands in
  `F` **because of the defining rank relation** — this is the only place the locus equation enters.
- `Ψ: (u,v,w; A₁ᶠ,A₂ᶠ) ↦ (A₁ᶠ[[1,v/u],[0,1]], [[u,0],[w,1]]A₂ᶠ)` reconstructs `(A₁,A₂)` exactly
  (`Ψ∘Φ = id`), and `mult(Ψ(...)) = M` recovers `(u,v,w)` exactly (`Φ∘Ψ = id` on the base).

### Why this is FREE, not a coupled tensor

The decisive subtlety the brief flagged: `O(Rep) = k[TUPLE entries]`, and `Δ,B12,B21,B22` are
*polynomial functions of the tuple*, **not** free coordinates. Resolution: after the retraction,
the tuple is re-coordinatized as `(base=(Δ,B12,B21), fibre = φ(A) ∈ F)`, and `Ψ` shows this
coordinate change is a regular iso localized at `detΔ`. In the new coordinates the base δ-vars are
**algebraically independent over `O(F)`** (they are literally adjoined polynomial generators in the
`Ψ` formula, with no relation back into the fibre coordinates). So the extension is
`O(F)[δ vars]_{detΔ}` — a localized polynomial ring over `O(F)`, **one factor free**, NOT a tensor
`O(base)⊗_k O(F)` of two constrained rings. `ringKrullDim_of_isNoetherianRing` applies directly.

### Deep / higher-rank robustness (the brief's central worry)

- **Deep N=3 `(2,2,2,2)` r=1**: the section touches only the END factors (`A_1` on the right,
  `A_last` on the left), interior `A_2` untouched — exactly `endpointGauge`. `det M = ∏ᵢ det(Aᵢ)`
  factors into N pieces (so `Σ̄^1` has N components, genuinely reducible), and `(φ)₁₁·u = det M`
  vanishes on the locus identically. **Reducibility does not obstruct the section.** FACT (sympy).
- **`(3,3,3)` r=2**: `det M = det(Δ)·Schur`, δ = 8 = `#Δ(4)+#B12(2)+#B21(2)`, `B22(1)`
  Schur-determined. FACT (sympy).

---

## Localization-no-drop + Q4 density (the two coupled sub-checks)

- **Q4 density (chart meets every top component): RESOLVED by construction, ~0 extra modules.** The
  chart `U = {detΔ ≠ 0}` pulled back to the tuple is `{detΔ(mult A) ≠ 0}`. Every point of `Σ^r`
  (exact rank `r`) has `rank(mult A) = r`, so SOME `r×r` minor of `mult A` is nonzero; the *pivot*
  chart is the union over pivot choices, and after the endpoint gauge the top-left minor is the
  generic one. More directly: `Σ^r = ⋃_P P·F` (LANDED sweep) and the chart is `H`-saturated, so
  every point of `Σ^r` lies in *some* gauge translate of the top-left-pivot chart — the finite pivot
  cover of `Σ^r` by Schur charts is the standard rank-stratification cover. The density that each top
  component MEETS `U` is automatic since `U` is dense in each component (a principal open by a single
  minor, nonzero generically on a rank-`r` locus). **Reachable; the residual is the finite-cover
  glue, not density per se.**
- **Localization-no-drop (`detΔ≠0` doesn't drop top dimension): reachable, ~1-2 modules.** The chart
  is a **non-empty** principal open of `Σ^r` (the retraction shows it is non-empty whenever `F` is,
  and `F` is non-empty for a realizable rank). Peer's closed-point-height route
  (`height_eq_ringKrullDim_of_isMaximal_fintype` + `IsLocalization.orderIsoOfPrime`) is the right
  brick; alternatively the product presentation `O(F)[δ]_{detΔ}` *is* the localized ring, so the
  no-drop is folded into the freeness lemma (the localization is at one variable's image, harmless
  for the polynomial-extension Krull dim). I lean on the latter: once `O(Σ^r∩U) ≅ O(F)[δ vars]_{detΔ}`
  is in hand, `ringKrullDim` of that localized polynomial ring is computed directly, no separate
  no-drop needed *for the chart itself* — the no-drop is only needed to relate `dim(Σ^r∩U)` back to
  `dim Σ^r` (the finite-cover step), where it is the "open meets every top component" fact above.

---

## FIRM module estimate for route A (the operator's build-vs-bank number)

| Rung | Content | Cost | Status |
|---|---|---|---|
| 1 | Chart membership iff `rank M ≤ r ⟺ Schur block = 0` on `detΔ≠0` | ~1-2 | LANDED heart `schurComplement_normal_form` + rank-iff |
| 2 | The regular product iso `Φ/Ψ : Σ^r∩U ≅ S_U × F` as a coordinate-ring `AlgEquiv` (the gauge `endpointGauge` + retraction; feed `varietyDim_eq_of_coordRingAlgEquiv`, LANDED) | **~3-4** | the genuine new work — packaging the section/retraction as an `AlgEquiv`, localized at `detΔ` |
| 3 | `+δ` via free-poly presentation `O(F)[δ vars]_{detΔ}` + `ringKrullDim_of_isNoetherianRing` (LANDED) | ~1-2 | freeness CONFIRMED; the localized-poly Krull-dim is landed Mathlib |
| 4 | Finite-pivot-cover glue + density (`varietyDim(⋃)=max`, chart dense in each top component) | ~1-2 | density automatic; union-max from minimal-prime algebra |
| 5 | Assemble `hSweep` → feed LANDED `RouteCAssembly._of_sweep'` | ~1 | LANDED consumer |

**Total ≈ 7-10 modules**, ALL non-circular. The dominant cost shifts from "the freeness" (settled,
cheap once stated) to **rung 2: packaging the explicit section/retraction as a coordinate-ring
`AlgEquiv`** — that is the real grind, and it is reachable (the maps are explicit, regular, localized
at one element; the engine has the gauge `endpointGauge` + the `AlgEquiv`-transport linchpin
`varietyDim_eq_of_coordRingAlgEquiv` LANDED).

---

## The single biggest residual risk

**Rung 2 packaging, not the freeness.** The freeness is settled (round-trip verified, deep + higher
rank robust, Codex-concurred). The risk is that turning the *explicit regular iso* `Φ/Ψ` into a Lean
**coordinate-ring `AlgEquiv`** `O(Σ^r∩U) ≃ₐ[k] O(F)[δ vars]_{detΔ}` requires identifying
`vanishingIdeal(Σ^r∩U)` with the kernel of the presentation map — and *if* one tries to do that via
a **generator-ideal equality** (the `fibreGenIdeal = …` strict inclusion), it re-incurs the R2-3b-4
reducedness wall. **Mitigation (the route's whole point):** stay at the `vanishingIdeal`/`varietyDim`
level — `Φ` is an `AlgEquiv` of *coordinate rings* (regular iso of closed sets) transported by the
gauge automorphism's `comap` (LANDED `vanishingIdeal_image_smul` + `varietyDim_eq_of_coordRingAlgEquiv`),
which is radical-insensitive and bijective, so **no strict ideal inclusion is ever needed**. The
residual risk is purely the *bookkeeping volume* of expressing `S_U × F`'s coordinate ring as the
localized polynomial extension and matching it to the gauge-transported `vanishingIdeal` — a grind,
not a wall. If rung 2 exceeds ~4 modules, the fallback is option B (cite `hSweep`), but the explicit
verified `Φ/Ψ` make that unlikely.

---

## Decorrelated Codex (xhigh, gpt-5.x) — independent read

Fired with the hypothesis WITHHELD (the freeness question + the tuple-vs-product-matrix subtlety +
the (2,2,2) anchor + the absent-tensor / present-poly-extension Mathlib facts; I did NOT tell it my
tentative "FREE"). Codex VERDICT independently matches: **"FREE polynomial extension, but only after
choosing the Schur-chart section/retraction."** It independently:
- constructed the SAME section `P_N=[[Δ,0],[B21,I]]`, `P_0⁻¹=[[I,Δ⁻¹B12],[0,I]]`;
- named the SAME δ free generators (entries of `Δ,B12,B21`), `B22` Schur-determined;
- gave the SAME presentation `O(Σ^r∩U) ≅ O(F)[Δ_ij,(B12),(B21)]_{detΔ}`;
- worked the (2,2,2) r=1 anchor with the explicit retracted fibre coords (`A₁ᶠ,A₂ᶠ`) and explicit
  inverse, confirming `dim Σ^1 = δ + dim F = 3 + 4 = 7`;
- flagged the one caveat I also flag: the freeness is **section-dependent** — "if `O(F) ⊂ O(Σ^r∩U)`
  is meant via a naive original-tuple-coordinate inclusion, that inclusion is not canonical." This is
  exactly the rung-2 packaging risk (use the *retracted* fibre subalgebra from the Schur section, not
  a naive inclusion).

Transcript: `codex/rung3-freeness-{prompt,answer}.md`. **Agree** on every load-bearing point; the
decorrelated read converged on the identical section, generators, presentation, and caveat.

---

## Engine handles VERIFIED (file + name)

PRESENT (read and confirmed):
- `SchurGauge.{schurComplement_normal_form (:168), endpointGauge (:132), Lmat/Hmat, isUnit_Lmat/_Hmat,
  schurΔLoc, schurB12Loc, schurB21Loc}` — the section `P_N`/`P_0⁻¹` and the Schur normal form (the
  rung-1 heart + the rung-2 gauge), all over `SchurLoc = Localization.Away detSchurS`.
- `FibreNormalForm.{mult_smul (:77), image_smul_fibre (:87), vanishingIdeal_image_smul (:111),
  codimRep_baseChange_image (:141)}` — H-equivariance + the automorphism `vanishingIdeal` comap
  transport (the radical-insensitive, bijective bridge for rung 2).
- `EndBaseChangeSweep.productRankLocus_eq_iUnion_smul_fibre (:81)` — `Σ^r = ⋃_P P·F` (the cover).
- `VarietyDimRadical.{varietyDim_eq_of_coordRingAlgEquiv (:57), ringKrullDim_quotient_comap_ringEquiv
  (:80), ringKrullDim_quotient_radical}` — the coordinate-ring `AlgEquiv` → `varietyDim` linchpin
  (rung 2/3) + radical shield.
- `ClosureBridge.varietyDim_productRankLocus_eq_productRankLocusLE` — `hClosure` LANDED (so the chart
  route uses `productRankLocus`, exact rank, and bridges to the closure for free).
- `RouteCAssembly.codimRepCanonical_fibre_eq_cCodim_add_shift_of_sweep'` — consumes `hSweep`; the
  rung-5 LANDED consumer.
- **Mathlib** `MvPolynomial.ringKrullDim_of_isNoetherianRing` (`KrullDimension/Polynomial.lean:119`)
  — `dim(MvPolynomial ι R) = dim R + card ι`, finite `ι`, **any Noetherian `R`** (reducible OK). THE
  `+δ` brick.

SEARCHED AND ABSENT (NOT needed by this route):
- `ringKrullDim (A ⊗_k B) = dim A + dim B` (absent — **avoided**, the presentation is a free poly
  extension, not a tensor of two constrained rings).
- trdeg-of-tensor / Chevalley relative-dimension (absent — **avoided**, no trdeg, no domain).

---

## Close

- **Firmest result:** rung-3 **HOLDS** — the δ Schur/off-diagonal coordinates are FREE polynomial
  generators over `FibreAlg` on the chart `U = {detΔ≠0}`, presentation
  `O(Σ^r∩U) ≅ O(F)[Δ,B12,B21]_{detΔ}`, `+δ` via the LANDED `ringKrullDim_of_isNoetherianRing`. The
  regular product iso `Φ/Ψ` is explicit and round-trip-verified (both directions) on (2,2,2) r=1,
  robust at deep N=3 and higher rank (3,3,3) r=2. **Reducibility of `F`/`Σ^r` does NOT couple the
  δ vars** — the section reads only the Schur data of `mult(A)`. Route A ≈ **7-10 modules**.
- **Most likely thing to break it:** NOT the freeness (settled) but **rung-2 packaging** — turning
  the explicit `Φ/Ψ` into a coordinate-ring `AlgEquiv` `O(Σ^r∩U) ≃ₐ O(F)[δ]_{detΔ}` WITHOUT slipping
  back into a generator-ideal strict inclusion (the R2-3b-4 wall). Mitigation: ride the gauge
  automorphism's `comap` (LANDED, bijective, radical-insensitive) + `varietyDim_eq_of_coordRingAlgEquiv`
  (LANDED), never the `fibreGenIdeal` inclusion. Bookkeeping grind, not a wall.
- **Next construction/consult that would settle the open part:** a focused SPECIFY on rung 2 — pin
  the EXACT Lean shape of the `AlgEquiv` `O(Σ^r∩U) ≃ₐ O(F)[δ vars]_{detΔ}`: which map realizes `Ψ`
  as an `aeval` coordinate substitution (the `DeepChartRing` R2-3b-3 pre-stage `example` is the
  template), and confirm the fibre subalgebra is the *retracted* `O(φ(Σ^r∩U)) = O(F)` (not a naive
  tuple-coordinate inclusion). That single check de-risks the one rung that carries the module count.
