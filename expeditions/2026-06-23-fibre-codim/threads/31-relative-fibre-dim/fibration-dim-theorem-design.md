# Thread 31 — framing-2 fibration-dimension theorem: build design

*Seat: pen-and-paper, witness direction. FINAL TASK (supersedes orbit-dim AND set-level briefs).
Design the cleanest `varietyDim`-native proof of `varietyDim Σ^r = δ + varietyDim F` so the tide
builds the right ~5-8 modules, exploiting the constant-isomorphic-fibre homogeneity as the lever.
Read-only — no Lean writes, no builds. Decorrelated xhigh Codex fired independently.*

## STRATEGY (one line)

**Realize the homogeneity lever as an EXPLICIT regular trivialization `Σ^r_Δ ≅ Mat^{=r}_Δ × F` on each
pivot chart (the gauge map `A ↦ (mult A, P(mult A)•A)`), transport to a coordinate-ring `AlgEquiv`
via the LANDED `varietyDim_eq_of_coordRingAlgEquiv`, and get the `+δ` from the LANDED Mathlib
`MvPolynomial.ringKrullDim_of_isNoetherianRing` (no domain hypothesis — handles reducible `O(F)`);
glue over the finite pivot cover.** This is substrate **(iv)**, NOT the literal trdeg-tower
(substrate ii). ~7 modules, all non-circular, the only absent-machinery exposure is a *tailored*
localization-no-drop lemma (not a general theorem).

## CHOSEN SUBSTRATE + the one design correction to the brief

The brief names framing-2 as "group-sweep needs the **fibration-dimension theorem**" and lists
candidate (ii) **trdeg-additivity in the tower `k ⊆ K(base) ⊆ K(total)`**. After adjudication (mine +
a decorrelated xhigh Codex, independently) the verdict is:

> **The trdeg-tower (substrate ii) is NOT the cleanest realization of framing-2 — it is a trap.**
> `trdeg_add_eq` IS present at v4.29 (`AlgebraicIndependent/TranscendenceBasis.lean:548`) and the
> engine already uses it (`AffineNoetherRank.trdeg_eq_of_integral_injective`), BUT it requires the
> **top ring to be a domain** (`[NoZeroDivisors A]`). `O(Σ^r)`, `O(F)` are reducible, so it applies
> only after passing to a top irreducible component `Σ_0` — and there the route hits the SAME wall the
> orbit-dim brief hit: **identifying the relative trdeg `trdeg_{K(Mat^{=r})}(K(Σ_0))` with `dim F`
> needs generic-fibre / generic-flatness machinery** (the fibre over the generic point of `Mat^{=r}`
> is `F` only generically; homogeneity of CLOSED fibres does not, by itself, give the relative trdeg).
> So trdeg-tower does NOT let homogeneity dodge the obstruction.

The homogeneity lever's cleanest realization is the **explicit trivialization map** — that IS the
group-sweep `Σ^r = ⋃_P (P•)''F` made into a *regular section* over the chart. So substrate (iv) is
the faithful realization of framing-2's homogeneity, and it sidesteps trdeg entirely: the additivity
`dim(O(F)[δ vars]_loc) = dim O(F) + δ` is a *polynomial-extension* fact (Noetherian-only, reducible OK),
NOT a trdeg-tower fact (domain-only). **My previous set-level-trivialization certificate reached the
same substrate; this design pins it as the build plan.** Decorrelated Codex converged on (iv)
independently, with the identical reasoning that (ii) cannot identify relative-trdeg = fibre-dim
without generic-fibre machinery.

**Candidate scorecard (each: present-at-v4.29? does homogeneity dodge reducibility?):**
- **(i) Order/Krull chain bounds** — primitives present (`Order.krullDim`, `ringKrullDim`,
  `HasGoingDown.of_flat`), but NO relative `dim X = dim Y + dim fibre` chain theorem; needs
  going-down/flatness `mult` lacks globally; homogeneity of closed fibres does not supply it. **Reject.**
- **(ii) trdeg-tower** — `trdeg_add_eq` present but domain-only; relative-trdeg = fibre-dim needs
  generic-fibre machinery (the obstruction). **Reject as the spine** (it can serve as a *cross-check*
  on one component, not the main route).
- **(iii) Spec/localization going-down** — pieces present (`IsLocalization.orderIsoOfPrime`,
  `height_map_of_disjoint`, `AtPrime.ringKrullDim_eq_height`); packaged `ringKrullDim_localization`
  absent; cleaner only AS the localization-no-drop sub-lemma INSIDE (iv). **Subsumed into (iv).**
- **(iv) chart trivialization + `ringKrullDim_of_isNoetherianRing`** — the `+δ` lemma is PRESENT and
  domain-free; the homogeneity gauge gives the trivialization explicitly; reducibility handled by
  Noetherian-only. **CHOSEN.**

## The proof, in 7 named steps (dependency order)

Notation: `q = d 0`, `p = d (Fin.last N)`, `δ = r(p+q−r)`, `Δ` = top-left `r×r` minor of `mult`,
`U_Δ = {A | detΔ(mult A) ≠ 0}` the pivot chart, `F = fibre d E`.

**Step 1 [LANDED] — the homogeneity input.** `Σ^r = ⋃_P (P•)''F`
(`EndBaseChangeSweep.productRankLocus_eq_iUnion_smul_fibre`), `mult_smul`, `image_smul_fibre`,
`codimRepCanonical_fibre_eq_of_rank_eq` (G1). These are the constant-isomorphic-fibre facts. **HERE the
homogeneity enters**: it lets Step 3's trivialization map be a regular *section* (the gauge `P(M)`
depending regularly on the base point `M`), which is what makes the fibre dimension constant WITHOUT
upper-semicontinuity.

**Step 2 [MUST-BUILD, ~1 module] — the base Schur chart.** On a nonzero-`r×r`-minor chart of
`Mat^{=r}`, `Mat^{=r}_Δ ≅ Spec k[δ vars]_{detΔ}` — the δ free Schur coordinates `(Δ, B12, B21)` with
`B22 = B21 Δ⁻¹ B12` forced. This is the LANDED `N=1` `DeterminantalBasePresentation` content
(`basePresentationEquiv`, `SchurLoc = Localization.Away detSchurS`); Step 2 packages it as the base
factor. **Reuse, not new theory.**

**Step 3 [MUST-BUILD, the CORE, ~2 modules] — the total-space trivialization.**
`Σ^r ∩ U_Δ ≅ Mat^{=r}_Δ × F` via the regular maps
  - forward: `A ↦ (mult A, P(mult A) • A)`, `P(M) = endpointGauge` (the LANDED Schur-data gauge over
    `SchurLoc`, which depends *regularly* on `M` because its blocks `L,H` are matrices over `SchurLoc =
    Localization.Away detΔ` — `SchurGauge.{Lmat, Hmat, endpointGauge}`, all LANDED);
  - inverse: `(M, B) ↦ P(M)⁻¹ • B`.
  Well-defined: `mult(P(M)•A) = P(M)_N · mult A · P(M)_0⁻¹` (`mult_smul`), and `endpointGauge` is built
  so the normalized product is `E` (the matrix heart `schurComplement_normal_form`, LANDED:
  `L⁻¹·M·H⁻¹ = diag(I_r,0)`). So `P(mult A)•A ∈ fibre E = F`, and the two maps are mutually inverse by
  the group action. **This uses ONLY `mult_smul` + the landed gauge + `schurComplement_normal_form` —
  NO Chevalley, NO upper-semicontinuity, NO trdeg, NO flatness.** This is the group-sweep realized as a
  regular trivialization.

**Step 4 [MUST-BUILD + LANDED, ~1 module] — set-iso → coordinate-ring `AlgEquiv` → `varietyDim`.**
The regular iso of Step 3 induces a coordinate-ring `k`-algebra iso `O(Σ^r ∩ U_Δ) ≅ O(Mat^{=r}_Δ × F)`,
and `VarietyDimRadical.varietyDim_eq_of_coordRingAlgEquiv` (LANDED — transports `varietyDim` across an
`AlgEquiv` even between DIFFERENT ambient spaces) gives `varietyDim(Σ^r ∩ U_Δ) = varietyDim(Mat^{=r}_Δ
× F)`. **Crucially NON-CIRCULAR**: everything reads through `vanishingIdeal` (radical by construction);
`varietyDim` is radical-insensitive (`ringKrullDim_quotient_radical`), so no reducedness / no strict
ideal inclusion / no ideal-generation is ever needed (this is exactly what dissolved the R2-3b-4 wall).

**Step 5 [Mathlib-present, ~0.5 module] — the product/polynomial-extension `+δ`.**
`O(Mat^{=r}_Δ × F) ≅ O(F)[δ Schur vars]_{detΔ}` (the base factor is FREE polynomial coordinates over
the fibre ring, localized at `detΔ`). The `+δ` is **`MvPolynomial.ringKrullDim_of_isNoetherianRing`**
(`KrullDimension/Polynomial.lean:119`, PRESENT at v4.29): `ringKrullDim (MvPolynomial ι A) = ringKrullDim
A + Nat.card ι` for finite `ι`, ANY commutative Noetherian `A` — **no domain hypothesis**, so reducible
`A = O(F)` is fine. *This is the single reason (iv) beats (ii): the dimension-addition step is
Mathlib-present and domain-free.*

**Step 6 [MUST-BUILD, ~1.5 modules, RISK] — localization no-drop.** Inverting `detΔ` does not drop the
top dimension of `O(F)[δ vars]`: `varietyDim(O(F)[δ vars]_{detΔ}) = varietyDim(O(F)[δ vars]) = δ + dim F`.
Cheapest route (the substrate-iii pieces, used as a *tailored* lemma, NOT a general theorem):
`≤` from `IsLocalization.orderIsoOfPrime` (prime correspondence); `≥` by passing to a TOP minimal prime
`𝔭` of `O(F)` (so `dim(O(F)/𝔭) = max = dim F`), then a closed-point/maximal-ideal `𝔪 ⊇ 𝔭` avoiding
`detΔ` with `height(𝔪 A_{detΔ}) = height 𝔪` (`IsLocalization.height_map_of_disjoint`,
`AtPrime.ringKrullDim_eq_height`) and the engine's affine-domain equidimensionality at a closed point
(`OrbitTangentCotangent.height_eq_ringKrullDim_of_isMaximal_fintype`,
`FibreDimFibration.affine_domain_height_add_ringKrullDim_quotient_eq_fintype`, both LANDED). The
"`detΔ` avoids a top component" sub-point is the density step (Step 7). Reducibility appears here ONLY
as `max over top minimal primes of O(F)`, contributing `δ + max_i dim F_i = δ + dim F`.

**Step 7 [MUST-BUILD, ~1 module, RISK] — finite-cover glue + density.**
`varietyDim(⋃_Δ (Σ^r ∩ U_Δ)) = max_Δ varietyDim(Σ^r ∩ U_Δ)` over the finite pivot-minor cover of
`Σ^r` (every `A ∈ Σ^r` has `rank(mult A) = r`, so some `r×r` minor of `mult A` is nonzero — `A ∈` some
`U_Δ`; this is the cover). Union-max from `vanishingIdeal(⋃) = sInf vanishingIdeals` + minimal-prime
coheight algebra (template: `SigmaComponents.minimalPrimes_sInf_of_finite_of_isPrime`; the catenary
direction is `RadicalCatenary`). Each chart has dim `δ + dim F` (Steps 4-6), so the max is `δ + dim F`.
Density (each top component meets some `U_Δ`) is automatic from the cover (`Σ^r ⊆ ⋃_Δ U_Δ` exactly),
but the union-max ↔ `varietyDim Σ^r` bridge (open chart dim = ambient locus dim, since `Σ^r = ⋃ (Σ^r ∩
U_Δ)` is a genuine equality, not just dense) needs the `varietyDim(open piece) = varietyDim(whole)` no-
drop — folded into Step 6's no-drop for the relevant component.

**Assembly [LANDED] — feed `RouteCAssembly`.** Steps 1-7 give `hSweep : varietyDim Σ^r = δ +
varietyDim F`, which discharges `RouteCAssembly.codimRepCanonical_fibre_eq_cCodim_add_shift_of_sweep'`
(LANDED, conditional bank) → `codim F = C + δ` unconditional (modulo the separately-tracked `hClosure`,
now landed per task #53).

## Reducibility handling (the make-or-break — concrete)

The route NEVER applies trdeg or the `varietyDim = trdeg` domain method to `O(Σ^r)` or `O(F)`. The
chart ring is a *localized polynomial ring* `O(F)[δ vars]_{detΔ}` over the possibly-reducible `O(F)`,
and `MvPolynomial.ringKrullDim_of_isNoetherianRing` handles that directly (Noetherian-only). Reducibility
surfaces in exactly two bounded places: (a) Step 6's `≥`, as a `max over top minimal primes of O(F)`
(each top prime contributes `δ + dim F_i`, max `= δ + dim F`); (b) Step 7's finite-union max over charts.
Both are minimal-prime bookkeeping, NOT the absent Chevalley/relative-Noether machinery. The
homogeneity lever (Step 3's regular trivialization) is what makes the chart a *clean product* — without
it, the relative dimension would need generic-fibre machinery. Decorrelated Codex states this identically:
*"Do not apply trdeg to O(Σ^r) or O(F). The chart ring is a localized polynomial ring over the possibly
reducible O(F), and `ringKrullDim_of_isNoetherianRing` handles that directly."*

## Localization-top-dim sub-lemma — placement + route

Sits at **Step 6**, after the chart `AlgEquiv` (Step 4) and the polynomial `+δ` (Step 5), before the
chart-dimension conclusion. Cheapest v4.29 route: a TAILORED lemma for `Localization.Away detΔ
(MvPolynomial (Fin δ) A)` with `A = O(F)` — NOT a general `ringKrullDim_localization`. `≤` from prime
correspondence (`IsLocalization.orderIsoOfPrime`); `≥` from a top component + a maximal ideal avoiding
`detΔ` + the engine's closed-point equidimensionality (`height_eq_ringKrullDim_of_isMaximal_fintype`,
LANDED). ~1-1.5 modules. NOT a wall.

## Single biggest risk

**Step 3→4: turning the set-level trivialization into a coordinate-ring `AlgEquiv`, including the
saturation / localized-coordinate bridge for the principal open `U_Δ`.** If the chart-coordinate
plumbing (presenting `O(Σ^r ∩ U_Δ)` as `O(F)[δ vars]_{detΔ}` through the gauge substitution and the
localization at `detΔ`) gets messy, it can re-create much of the missing localization/product
infrastructure — i.e. drift back toward the R2-3b-4 ring-plumbing that walled. **Mitigation / the one
de-risk to run FIRST:** confirm (a SPECIFY) that the δ Schur base-coordinates appear as genuinely
*free* polynomial generators over `FibreAlg` after the gauge substitution (so Step 5's
`ringKrullDim_of_isNoetherianRing` applies on the nose), and that the `detΔ`-localization commutes
cleanly with the quotient (`IsLocalization.map_radical`-style, the shape `DeepChartRing` already uses).
This single check decides whether Step 3-6 is the planned ~4 modules or re-incurs the plumbing wall.
Codex names the identical risk: *"the riskiest step is the set-level chart trivialization to
coordinate-ring AlgEquiv, including the saturation/localized-coordinate bridge for the principal open."*

Second risk: Step 7 density/union-max if the cover bookkeeping is fiddlier than the SPIKE template.

## Module decomposition (~7 serious sub-lemmas)

| # | Sub-lemma | Status |
|---|---|---|
| 1 | Homogeneity input (sweep + `mult_smul` + G1) | LANDED (`EndBaseChangeSweep`, `FibreNormalForm`) |
| 2 | Base Schur chart `Mat^{=r}_Δ ≅ k[δ vars]_{detΔ}` | LANDED-reuse (`DeterminantalBasePresentation`); ~1 mod to package |
| 3 | Total trivialization `Σ^r∩U_Δ ≅ Mat^{=r}_Δ × F` (gauge section) | MUST-BUILD ~2 mod (the CORE; uses landed `endpointGauge`, `schurComplement_normal_form`, `mult_smul`) |
| 4 | Set-iso → coord-ring `AlgEquiv` → `varietyDim` | MUST-BUILD ~1 mod + LANDED `varietyDim_eq_of_coordRingAlgEquiv` |
| 5 | Polynomial `+δ` | Mathlib-present `ringKrullDim_of_isNoetherianRing`; ~0.5 mod to apply |
| 6 | Localization no-drop (the sub-lemma) | MUST-BUILD ~1.5 mod (substrate-iii pieces + landed closed-point equidim) |
| 7 | Finite-cover glue + density | MUST-BUILD ~1 mod (minimal-prime algebra, SPIKE template) |

**Total ≈ 7 serious sub-lemmas / ~6-7 modules**, all non-circular. Matches both the earlier ~6-10
set-level estimate and Codex's independent ~7.

## Engine handles VERIFIED (file + name)

LANDED (read, confirmed):
- `EndBaseChangeSweep.productRankLocus_eq_iUnion_smul_fibre` (`:81`) — `Σ^r = ⋃_P (P•)''F`.
- `FibreNormalForm.{mult_smul (:77), image_smul_fibre (:87), codimRepCanonical_fibre_eq_of_rank_eq (:322)}`.
- `SchurGauge.{schurComplement_normal_form (:168), endpointGauge (:132), Lmat/Hmat, isUnit_Lmat/Hmat}`
  — the regular gauge section over `SchurLoc`, and the matrix-normal-form heart.
- `EndpointNormalization.{gaugeEquiv, gaugeEquiv_multPoly (:242), aeval_gaugeSub_multPoly (:143)}` —
  the gauge as a coordinate-ring `AlgEquiv` + mult-transport, over an arbitrary coefficient ring.
- `VarietyDimRadical.{varietyDim_eq_of_coordRingAlgEquiv (:57), ringKrullDim_quotient_radical (:40),
  ringKrullDim_quotient_comap_ringEquiv (:80)}` — the `varietyDim` transport + radical shield.
- `DeterminantalBasePresentation.basePresentationEquiv` + `SchurLoc` — the `N=1` base Schur chart.
- `DeterminantalStratumDim.varietyDim_productRankLocusLE_stratum` — `dim Mat^{≤r} = δ` (via catenary).
- `RouteCAssembly.codimRepCanonical_fibre_eq_cCodim_add_shift_of_sweep'` (`:102`) — consumes `hSweep`.
- `RadicalCatenary.height_add_ringKrullDim_quotient_eq_card_of_ne_top` + `SigmaComponents`
  `minimalPrimes_sInf_of_finite_of_isPrime` — the union-max template.
- `OrbitTangentCotangent.height_eq_ringKrullDim_of_isMaximal_fintype`,
  `FibreDimFibration.affine_domain_height_add_ringKrullDim_quotient_eq_fintype` — closed-point equidim
  for Step 6.
- **Mathlib v4.29 PRESENT:** `MvPolynomial.ringKrullDim_of_isNoetherianRing`
  (`KrullDimension/Polynomial.lean:119`, domain-free); `trdeg_add_eq`
  (`TranscendenceBasis.lean:548`, domain-only — the reason (ii) is rejected as the spine);
  `IsLocalization.orderIsoOfPrime`, `IsLocalization.height_map_of_disjoint`,
  `IsLocalization.AtPrime.ringKrullDim_eq_height`.

SEARCHED AND ABSENT (handled by detour, NOT walls):
- `ringKrullDim (A ⊗_k B) = dim A + dim B`, trdeg-of-tensor — detoured by the poly-extension form (Step 5).
- packaged `ringKrullDim_localization` — detoured by the tailored Step 6 lemma.
- general Chevalley / relative Noether normalization — NOT needed (homogeneity gives the explicit
  trivialization, Step 3).

## Decorrelated Codex (xhigh, gpt-5.x) — independent read

Fired with the candidate substrates listed but my recommendation WITHHELD. Codex independently CHOSE
substrate (iv) — *"pivot-chart trivialization + `MvPolynomial.ringKrullDim_of_isNoetherianRing` …
the cleanest because the only dimension-addition step is Mathlib-present and works for reducible
rings"* — explicitly REJECTING (ii) for the same reason I give: *"trdeg_add_eq is present, but it needs
a domain top ring … homogeneity of closed fibres does not identify relative trdeg with fibre dimension
without either generic-fibre machinery or an explicit local trivialization."* Its 7-step strategy, its
reducibility handling, its localization-no-drop route, and its biggest-risk call all match this design.
Transcript: `codex/fibration-dim-substrate-{prompt,answer}.md`. **Agree** on every load-bearing point;
the decorrelated read converged on the identical substrate, the identical `+δ` lemma, and the identical
risk — strong evidence the design is stable.

## Close

- **Firmest result:** build framing-2 as the **explicit gauge-trivialization** `Σ^r_Δ ≅ Mat^{=r}_Δ × F`
  (substrate iv), NOT the trdeg-tower (substrate ii). The homogeneity lever is the regular section
  `A ↦ (mult A, P(mult A)•A)` — it makes the chart a clean product so the `+δ` is the domain-free
  `ringKrullDim_of_isNoetherianRing`, dodging both the absent tensor theorem AND the trdeg domain
  obstruction. ~7 modules, all non-circular, the only absent-machinery exposure a *tailored*
  localization-no-drop (reachable from landed closed-point equidim).
- **Most likely to break it:** Step 3→4 chart-coordinate plumbing (the set-iso → `AlgEquiv` +
  localized-coordinate bridge) re-creating the R2-3b-4 ring plumbing. **De-risk FIRST** with a SPECIFY
  pinning `O(Σ^r ∩ U_Δ) ≅ O(FibreAlg)[δ free vars]_{detΔ}` and confirming the δ vars are FREE
  generators — that single check decides ~4 modules vs re-wall.
- **Next construction/consult to settle the open part:** that Step-3-4 SPECIFY (pin the exact chart
  presentation + free-generator check) is the highest-value de-risk before the grind commits. If it
  confirms, the route is a clean ~7-module build with no absent-theorem exposure; if it shows the δ vars
  are coupled, fall back is the tailored tensor-dim lemma (still domain-free via `ringKrullDim_of_isNoetherianRing`
  applied to the appropriate presentation, ~+1-2 modules).

---

## Tide progress log (write-tide, 2026-06-25)

**Banked (committed, sorry/axiom-clean):**
- rung-1 `Core.SchurChartIff` — chart-membership iff `rank[[Δ,B12],[B21,B22]] ≤ r ⟺ B22 = B21·Δ⁻¹·B12`
  (and `= r` form); via Mathlib LDU `fromBlocks_eq_of_invertible₁₁` + landed `RankNormalFormDim` helpers.
- rung-3 `Core.VarietyDimPolyExtension` — `varietyDim_eq_of_polyExtensionAlgEquiv`:
  `varietyDim W = varietyDim F + card ι` from a coordinate-ring `AlgEquiv O(W) ≃ₐ MvPolynomial ι O(F)`.
  Domain-free (`MvPolynomial.ringKrullDim_of_isNoetherianRing`). Universes relaxed to `σ τ ι : Type*`.

**Assembly VALIDATED (SPECIFY skeleton, built then removed — not committed):** the three contracts
  - rung-2: `O(Σ^r∩U_Δ) ≃ₐ[k] MvPolynomial (SchurVar) O(F)`  [MUST-BUILD]
  - rung-4: `varietyDim(Σ^r∩U_Δ) = varietyDim Σ^r`  (one-chart density)  [MUST-BUILD]
  - rung-3 brick + `card_SchurVar = δ`  [LANDED]
chain correctly into `hSweep` via the rung-5 preview proof (`obtain ⟨e⟩ := rung2; rw [← rung4, rung3, card_SchurVar, add_comm]`).

**Decorrelated Codex (gpt-5.5, xhigh) verdict** (`codex/rung2-algequiv-{prompt,answer}.md`): confirms the
design on every load-bearing point. (A) chart AlgEquiv IS necessary (sweep+const-fibre alone do NOT give +δ;
infinite union of equal-dim sets can be larger). (B) build rung-2 as explicit `aeval` substitutions Θ*/Λ*
descended through `vanishingIdeal` NOT `fibreGenIdeal`; the set-level retraction does NOT itself give the
coord-ring AlgEquiv. (C) ONE chart suffices if a one-chart GL-density no-drop is proved (skip finite cover).

**Remaining = the hard core (rung-2 + rung-4), ~4-6 modules, TWO MATHLIB-ABSENT-RISK items:**
the `SchurLoc`-localization handling inside the AlgEquiv, and the orbit-density no-drop. The concrete next
sub-lemma is the **`k`-valued set-level section** `s(M)=(P_N=[[Δ,0],[B21,I]], P_0⁻¹=[[I,Δ⁻¹B12],[0,I]])` and
its retraction-into-`F` property `φ(A)=s(mult A)⁻¹•A ∈ F` (uses only landed `mult_smul`,
`schurComplement_normal_form`, rung-1 chart-iff) — then lift to the coord-ring AlgEquiv.
