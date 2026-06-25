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

---

## Tide progress log — update 2 (rung-2 set-level geometry DONE)

**Banked rung-2 bricks (committed, sorry/axiom-clean):**
- `Core.ChartSection` — `k`-valued chart gauge `Lmatk`/`Hmatk` (+ invertibility), explicit block
  inverses, and `normalize_chart_matrix : (Lmatk M)⁻¹·M·(Hmatk M)⁻¹ = diag(I_r,0)` (the matrix heart,
  over `k`; reindex + `schurComplement_normal_form` + rung-1 `rank_le_iff_schur_eq`).
- `Core.ChartRetraction` — `chartGauge M : BaseChangeGroup` (`L⁻¹` at `last`, `H` at `0`) +
  `chartGauge_mem_fibre : chartGauge(mult A)•A ∈ fibre(diag(I_r,0))` (the retraction φ onto F, via
  `mult_smul`; lands because of the rank relation).

So the **set-level geometry of the trivialization is essentially done** (the regular retraction φ exists
and lands in F). What remains is the two genuinely-hard, absent-theorem-exposed pieces:

**Remaining R2a — the coordinate-ring AlgEquiv** `O(Σ^r∩U_Δ) ≃ₐ[k] MvPolynomial (SchurVar) O(F)`.
The set bijection Φ=(mult,φ)/Ψ exists; the AlgEquiv is the comorphism, realized as `aeval` of the Ψ
substitution descended through `vanishingIdeal` (NOT `fibreGenIdeal`). The localized-coordinate bridge
(presenting the chart ring over `SchurLoc = Localization.Away detΔ`) is the bookkeeping grind.

**Remaining R2b — the localization no-drop / one-chart density** (MATHLIB-ABSENT confirmed: no packaged
`ringKrullDim (Localization.Away f) = …` at v4.29). `varietyDim` is closure-based, so the cleanest is
**rung-4 density**: `vanishingIdeal(canonicalCoord '' Σ^r∩U_Δ) = vanishingIdeal(canonicalCoord '' Σ^r)`
(same Zariski closure) ⟹ `varietyDim(chart)=varietyDim Σ^r` directly — but the chart ring is the
*localized* `O(F)[SchurVar]_{detΔ}` while the closure ring is `O(Σ^r)`, so a no-drop relating
`dim(O(F)[SchurVar]_{detΔ}) = dim(O(F)[SchurVar]) = δ + dim F` is still needed. Buildable from
`IsLocalization.height_map_of_disjoint` + `AtPrime.ringKrullDim_eq_height` + the engine's closed-point
equidim (`height_eq_ringKrullDim_of_isMaximal_fintype`), the `≥` via a top maximal ideal avoiding detΔ —
a multi-lemma custom construction, NOT a one-liner.

---

## Tide progress log — update 3 (set-level trivialization COMPLETE; AlgEquiv-descent SPECIFY)

**Banked (committed, sorry/axiom-clean) — set-level trivialization done both directions:**
- `Core.ChartSection.factor_chart_matrix` — `L·E·H = M` (converse of `normalize_chart_matrix`).
- `Core.ChartBijection` — `chartGauge_smul_retraction` (Ψ∘Φ=id), `mult_chartGauge_inv_smul_fibre`
  (`mult(Ψ(M,B))=M` for `B ∈ fibre E`, the base reconstruction). Both bijection directions hold.
- `Core.LocalizationKrullDim.ringKrullDim_localization_le` — the `≤` half of the no-drop.

Tide total so far: 8 commits, ~570 LoC new sorry-free Core theory, all green. Modules:
`SchurChartIff`, `VarietyDimPolyExtension`, `ChartSection`, `ChartRetraction`, `ChartBijection`,
`LocalizationKrullDim`.

**SPECIFY — the AlgEquiv descent (the remaining deepest plumbing, R2-3b-4 re-approached via vanishingIdeal):**
Target (step 3): `Localization.Away (mk detΔ) (O(Σ^r)) ≃ₐ[k] Localization.Away g (MvPolynomial SchurVar O(F))`,
where `O(Σ^r) = MvPolynomial (RepCoord d) k ⧸ vanishingIdeal(canonicalCoord '' Σ^r)` and
`O(F) = MvPolynomial (RepCoord d) k ⧸ vanishingIdeal(canonicalCoord '' fibre E)` (RADICAL ideals — NOT
`fibreGenIdeal`/`IadDeep`, the wall).
Reusable pieces wired:
 - `EndpointNormalization.gaugeEquiv (endpointGauge)` : the gauge `AlgEquiv` of `MvPolynomial (RepCoord d) SchurLoc`,
   with `gaugeEquiv_multPoly` carrying `multPoly → L⁻¹·multPoly·H⁻¹` (= normalized).
 - `IsLocalization.algEquivOfAlgEquiv` (v4.29 present) : transports a base `AlgEquiv` to localizations
   when submonoids correspond.
The genuine remaining content: identify the gauge-normalized `vanishingIdeal(Σ^r)` (over `SchurLoc`,
localized) with the FREE extension `vanishingIdeal(F)[SchurVar]` — the freeness-presentation step. This
is what the rung-3 freeness cert verified holds (δ Schur vars FREE over `O(F)`); the Lean realization
must ride `vanishingIdeal` and `varietyDim_eq_of_coordRingAlgEquiv`, NEVER the generator-ideal containment.
Best built AFTER `pp-nodrop`'s component cert lands (it informs the reducible-component structure of the
normalized ideal).

---

## Tide progress log — update 4 (step-3 AlgEquiv descent: factored plan + signature-validated)

**Signature-validated (local SPECIFY built then removed — no absent-API gap at v4.29):** the step-3→5
contracts all typecheck. `Localization.Away` on the `vanishingIdeal`-quotient ring,
`MvPolynomial ι (fibreCoordRing)`, `nonZeroDivisors`, and the `gaugeEquiv`/`algEquivOfAlgEquiv`/
`Ideal.quotientEquivAlg` framing all resolve. The remaining work is PROOFS, not infrastructure.

**Reusable abbrevs pinned** (vanishingIdeal-based, to re-state when grinding):
`fibreCoordRing d E := MvPolynomial (RepCoord d) k ⧸ vanishingIdeal(canonicalCoord '' fibre d E)`;
`sigmaCoordRing d r := … ⧸ vanishingIdeal(canonicalCoord '' productRankLocus d r)`;
`sigmaDetΔ := Quotient.mk (det of the top-left r×r submatrix of (Matrix.of (multPoly d)))`.

**The step-3 AlgEquiv descent, FACTORED (4 sub-lemmas, the R2-3b-4 hard rung via vanishingIdeal):**
- **(3a)** gauge normalizes the generic product over `SchurLoc`: `gaugeEquiv (endpointGauge) (multPoly r c)
  = E r c` on the chart. Pure algebra from LANDED `gaugeEquiv_multPoly` (gives `(L⁻¹·multPoly·H⁻¹) r c`)
  + the SchurLoc-level Schur relation. NEEDS a SchurLoc Schur-relation bridge (the chart-locus condition
  at the polynomial/SchurLoc level) — genuine new plumbing, but independent of no-drop/avoidance.
- **(3b)** the gauge `comap` maps `vanishingIdeal(Σ^r)` (over SchurLoc) to the normalized ideal — the
  ideal-transport, via (3a) + the `vanishingIdeal` characterization. Rides `gaugeEquiv` (vanishingIdeal-free).
- **(3c)** the freeness identification: normalized `vanishingIdeal = vanishingIdeal(F)[SchurVar]` FREE
  (the rung-3 freeness cert content). Interacts with the reducible-component structure → benefits from
  pp-nodrop's cert.
- **(3d)** localization descent: `Ideal.quotientEquivAlg` + `IsLocalization.algEquivOfAlgEquiv` to land
  the localized AlgEquiv. Mechanical given (3a)-(3c).

Build order when grinding: (3a) first (independent), then (3b), then (3c) with the component cert,
then (3d). Estimate: ~3-4 modules. The whole step-3 stays strictly vanishingIdeal-side (Ideal.quotientEquivAlg
on the gauge-transported vanishingIdeal — NEVER the IadDeep/fibreGenIdeal generator route).

---

## Tide progress log — update 5 (step-3a landed; route-β decision for the descent)

**Banked (committed):** `Core.ChartGaugeNormalize.gaugeEquiv_endpointGauge_multPoly` (step-3a) — the
unconditional gauge-conjugation transport `gaugeEquiv(endpointGauge)(multPoly r c) =
(C(Lmat⁻¹)·multPoly·C(Hmat⁻¹)) r c` over `SchurLoc`, from LANDED `gaugeEquiv_multPoly` +
`liftGauge_endpointGauge_last/_zero_inv`.

**Route decision for the coordinate-ring descent (3b/3c/3d):** TWO routes considered.
- **ROUTE-α** (SchurLoc gaugeEquiv descent): descend 3a's SchurLoc-coefficient gaugeEquiv to the
  k-vanishingIdeal quotient. RISK: the variable-gauge → SchurLoc-coeff connection is a coefficient
  base-change with unvalidated Mathlib support (`vanishingIdeal_image_smul` is k-valued FIXED gauges only).
- **ROUTE-β** (k-level Ψ comorphism, CHOSEN): skip the SchurLoc descent. The set maps Φ/Ψ
  (`ChartBijection`, over k) give the comorphism directly. `Ψ(M,B) = chartGauge(M)⁻¹•B` is a regular
  map `base × F → Σ^r∩U_Δ` over k, regular after localizing at detΔ (chartGauge⁻¹ entries involve Δ⁻¹).
  Its `aeval` comorphism over k descends through `vanishingIdeal` directly — no SchurLoc coefficient-descent,
  and the detΔ-localization it requires IS the target chart localization. k-native, matches the
  `varietyDim_eq_of_coordRingAlgEquiv` discipline, reuses the landed set-bijection. 3a becomes a
  cross-check/alternative, not the spine.

Confirmation requested from controller (α-vs-β shapes the ~2-3 module grind). Proceeding with β.

---

## Tide progress log — update 6 (no-drop ≥ FACTORED — shared by step-4 and step-5)

`dim(R[1/g]) = dim R` (the no-drop, both step-4 source and step-5 poly-ext) FACTORS as:
1. **[LANDED] ≤** — `LocalizationKrullDim.ringKrullDim_localization_le`.
2. **dim R = max over minimal primes of dim(R/p)** — the `RadicalCatenary` pattern;
   `RadicalCatenary.exists_minimalPrime_ringKrullDim_quotient_ge` is LANDED.
3. **pick a TOP minimal prime `p₀` with `g ∉ p₀`** — the avoidance:
   - step-4: the `pp-nodrop` cert (Fact A corner=r + Fact B GL-permutation-to-top-left ⟹ detΔ ∉ a top
     minimal prime of `O(Σ^r)`).
   - step-5: `g = detSchurS` is a nonzero `k`-coefficient polynomial, so its image is nonzero in
     EVERY component `MvPolynomial ι (A/p)` (sympy-confirmed clean — no delicate avoidance).
4. **[ONE NEW SUB-LEMMA, shared] affine-domain localization preserves dim**: for `D = R/p₀` a
   finite-type domain over `k` and `0 ≠ g ∈ D`, `dim(D[1/g]) = dim D`. Buildable from the engine's
   `AffineDomainDimension` (trdeg = dim for affine domains) + `Frac(D[1/g]) = Frac D` (localization at a
   nonzero element of a domain doesn't change the fraction field). The genuinely-new piece both no-drops share.

**Efficient build structure:** ONE shared abstract no-drop lemma
`(R Noetherian, g avoids a top minimal prime) ⟹ ringKrullDim (Localization.Away g R) = ringKrullDim R`,
consuming sub-lemma (4); step-4 and step-5 then differ only in the avoidance input (3). ~2-3 modules
covering BOTH (not 1.5-2 + 0.5-1 separately).

---

## Tide progress log — update 7 (no-drop sub-lemma (iv) route VALIDATED — no absent API)

The one genuinely-new sub-lemma both no-drops share — **(iv) affine-domain localization preserves dim**:
`dim(Localization.Away g D) = dim D` for `D` a finite-type domain over `k`, `0 ≠ g ∈ D` — route VALIDATED,
all pieces present at v4.29:
- `D` and `D[1/g]` share the fraction field: `IsLocalization.isFractionRing_of_isLocalization`
  (`LocalizationLocalization.lean:279`) — `FractionRing D` is a fraction ring of the localization `D[1/g]`.
  **This is the key bridge; PRESENT, no absent API.**
- `dim = trdeg_k(FracField)` for affine domains: the engine's `AffineNoetherRank.trdeg_eq_of_integral_injective`
  + `ringKrullDim_quotient_unbotD_eq_trdeg_toNat` (the latter stated for `R⧸p`; `D[1/g]` is finite-type
  `= D[X]/(gX−1)`, a domain, so the affine-domain `dim=trdeg` applies once presented as such).
- so `dim(D[1/g]) = trdeg Frac(D[1/g]) = trdeg Frac D = dim D`.
The residual work in (iv): present `D[1/g]` as a finite-type-domain quotient and transport trdeg — fresh
but mechanical, ~1 module. NO absent-theorem exposure (the fraction-field bridge is the crux and it's present).

Full no-drop ≥ then = (iv) + RadicalCatenary max-over-min-primes (LANDED) + avoidance (pp-nodrop cert /
clean nonzero-k-coeff for step-5). Step-3 freeness presentation (3b/3c, route-β) is the separate remaining
piece (component-wise radical-ideal identification, component structure in hand).

---

## Tide progress log — update 8 (the no-drop + dimension-arithmetic SPINE landed; route-3 fixed)

**Banked (committed-pending-controller-integration, all sorry/axiom-clean, whole-library green):**
- `Core.AffineLocalizationNoDrop` (150 LoC) — three theorems:
  - `ringKrullDim_eq_trdeg_of_fg_domain` — `dim A = (trdeg k A).toNat` for ANY f.g. `k`-domain (via
    Noether `exists_integral_inj_algHom_of_fg` + engine `trdeg_eq_of_integral_injective`). General
    affine-domain dim=trdeg the engine lacked at this generality.
  - `trdeg_localization_eq` — `trdeg k S = trdeg k D` for `S = M⁻¹D`, `M ≤ nonZeroDivisors D` (sandwich
    `k ⊆ D ⊆ S`, `S ↪ Frac D` algebraic so `trdeg D S = 0`, `trdeg_add_eq`). GENERAL submonoid → directly
    usable by step-4 source.
  - `ringKrullDim_localizationAway_eq_of_fg_domain` — the (iv) headline `dim(D[1/g]) = dim D`, `D` f.g.
    `k`-domain, `g ≠ 0`.
  - `ringKrullDim_localizationAway_eq_of_avoids_top_prime` — the SHARED abstract no-drop over a reducible
    f.g. `k`-algebra `R`: `g` avoiding a TOP-dim **prime** `p₀` (`dim(R/p₀)=dim R`, `g∉p₀`) ⟹
    `dim(R[1/g])=dim R`. ≤ from LANDED `ringKrullDim_localization_le`; ≥ via surjection
    `R[1/g] ↠ (R/p₀)[1/ḡ]` (`Localization.awayMap`) + (iv). **Minimality NOT needed** (weakened from
    minimalPrime to prime — eases both avoidance proofs).
- `Core.ChartLocalizedPolyDim` (61 LoC) — `ringKrullDim_eq_of_localized_polyExtensionAlgEquiv`: the
  ROUTE-3 dimension-arithmetic wrapper. From a LOCALIZED chart `AlgEquiv`
  `Localization.Away dsig ≃ₐ[k] Localization.Away gfib` + the two no-drop equalities (hsig source, hP
  schur), concludes `dim Osig = dim Ofib + card ι`. Pure arithmetic.
- `Core.SchurSideNoDrop` (92 LoC) — `ringKrullDim_localizationAway_eq_of_schurSide`: the schur-side `hP`
  FULLY DISCHARGED. For `P = MvPolynomial ι A`, top-dim prime `q₀` of `A`, `gfib = map (algebraMap k A) g₀`
  with `g₀ ≠ 0`: `dim(P[1/gfib]) = dim P`. Witness `p₀ = Ideal.map C q₀`: prime via
  `quotientEquivQuotientMvPolynomial` (P/p₀ ≅ MvPolynomial ι (A/q₀), domain); top-dim via the equiv +
  `ringKrullDim_of_isNoetherianRing`; `gfib ∉ p₀` via the reduction `map (mk q₀)` (kills p₀, sends gfib to
  `map (algMap k (A/q₀)) g₀ ≠ 0`). Also `isPrime_map_C_of_isPrime` (reusable). **No minimal-prime theory
  needed** — the weakened "top prime" hypothesis + the C-quotient equiv suffice.

**ROUTE-3 DECISION (Codex xhigh decorrelated, `codex/step3-routebeta-spec-{prompt,answer}.md`):** localize
BOTH sides, no-drop twice. ROUTE-2 (feed un-localized O(Σ^r) to the poly-ext brick) CONFIRMED WRONG —
O(Σ^r) un-localized is NOT a free poly ext (Schur coords regular only after inverting detΔ). Wall to avoid:
the localized chart AlgEquiv via `sigmaIdeal`/`IadDeep`/`fibreGenIdeal` generator equalities (R2-3b-4 wall);
stay vanishingIdeal-side, `IsLocalization.liftAlgHom`/`Ideal.Quotient.liftₐ` for descent,
`IsLocalization.algEquivOfAlgEquiv` for the localized lift.

**REMAINING for hSweep (3 obligations the ChartLocalizedPolyDim wrapper consumes):**
1. **The LOCALIZED chart AlgEquiv `e`** — `Localization.Away (mk detΔ) O(Σ^r) ≃ₐ[k] Localization.Away gfib (MvPolynomial SchurVar O(F))`.
   The genuine HARD rung: variable-gauge Ψ comorphism (k-level, route-β) descended through vanishingIdeal,
   then localized via `algEquivOfAlgEquiv`. ~3 modules; the wall-risk piece. DESERVES A FRESH TIDE.
2. **source no-drop `hsig`** — `ringKrullDim_localizationAway_eq_of_avoids_top_prime` at R = O(Σ^r),
   g = detΔ, p₀ = a top minimal prime of O(Σ^r) avoiding detΔ (the pp-nodrop cert
   `nodrop-density-adjudication.md`: Fact A `exists_kostantPartition_partitionIdeal_eq_of` + Fact B
   H'-permutation). ~1-1.5 modules (wire the cert to a top prime + detΔ∉it).
3. **final wiring** — feed e + hsig + (SchurSideNoDrop) hP to the wrapper → `dim O(Σ^r) = dim O(F) + δ`,
   convert through `varietyDim`/`unbotD`, → `hSweep` → `RouteCAssembly._of_sweep'` → unconditional codim.
   ~1 module, mechanical once (1)+(2) land.

---

## Tide progress log — update 9 (final-wiring spine LANDED + descent crux LANDED; e/hsig scoped, NOT yet built)

**Banked (committed `4b88911f`, both zero-sorry, axiom-clean `[propext, Classical.choice, Quot.sound]`):**
- `Core.ChartSweepWiring` (the conditional-bank FINAL-WIRING SKELETON — obligation 3 DONE):
  - `varietyDim_eq_shift_of_ringKrullDim_eq` (general): `ringKrullDim O(Z) = ringKrullDim O(F) + m`
    ⟹ `varietyDim Z = m + varietyDim F`, `O(F)` nontrivial, `σ : Type*` (NOT `Type u` — `RepCoord d`
    is `Type 0`, the universe bug to avoid). The `unbotD 0` bridge.
  - `sweep_of_localizedChartAlgEquiv`: takes `e : Localization.Away dsig ≃ₐ[k] Localization.Away gF`,
    `hsig`, `hP`, `hF`-nontrivial; emits the EXACT RouteCAssembly `hSweep` shape
    `varietyDim (canonicalCoord '' productRankLocus d r) = δ + varietyDim (canonicalCoord '' fibre d E)`,
    `δ = card SchurVar = r(p+q−r)`. Uses local abbrevs `sweepSigma/Fibre/SigmaRing/FibreRing`.
    **So the whole step-3 spine is now machine-checked except the two named hypotheses `e`, `hsig`.**
- `Core.PrincipalOpenComorphism` (the descent CRUX primitive): `away_eq_zero_iff_exists_pow_mul_mem`
  — `mk' (mk a) 1 = 0` in `Localization.Away (mk f₀ : O(Z))` ⟺ `∃ n, f₀^n·a ∈ vanishingIdeal Z`, via
  `IsLocalization.mk'_eq_zero_iff` + `Quotient.eq_zero_iff_mem`. This is the vanishingIdeal-side
  zero-test the localized-AlgEquiv descent rides — the R2-3b-4 generator-ideal wall is *structurally*
  avoided (no generator containment, only membership + clearing denominators).

**Fresh decorrelated Codex (xhigh, `codex/localized-chart-algequiv-{prompt,answer}.md`) — verdict on `e`:**
- **Route (b) confirmed:** build `chartPsiLoc`/`chartPhiLoc` DIRECTLY as localized AlgHoms (each via
  `IsLocalization.liftAlgHom` of an `Ideal.Quotient.liftₐ` of an `aeval`), glue by `AlgEquiv.ofAlgHom`,
  extensionality `Localization.algHom_ext` (`@[ext high]`, present). NOT a k-level denominator-free
  `OΣ ≃ₐ[k] P` (false globally — the Ψ comorphism contains `Δ⁻¹`).
- **All Mathlib API verified present at v4.29:** `liftAlgHom`, `algEquivOfAlgEquiv`, `algHom_ext`,
  `Away.lift/awayMap/mapₐ`, `mk'_eq_zero_iff`, `quotientEquivQuotientMvPolynomial`, `eval_multPoly`
  (the load-bearing `eval (canonicalCoord A) (multPoly r c) = (mult A) r c` bridge). **NO absent theorem.**
- **The wall, precisely:** the Ψ-direction descent `vanishingIdeal Σ ⊆ ker chartPsiAeval` (Φ-direction is
  easier — denominator-free numerators). Discharge by point-realization: for a target chart point with
  `detSchurS ≠ 0`, build `A := chartGauge(M)⁻¹•B ∈ Σ` (LANDED `mult_chartGauge_inv_smul_fibre`), so
  `p ∈ vanishingIdeal Σ` evaluates to `0` there; the per-point vanishing → `0`-in-localization is the
  clearing-denominators primitive (LANDED). **Codex confirmed NO shorter path** (no dimension-only route;
  `basePresentationEquiv` only trivializes the BASE chart; the set bijection alone does not preserve
  `varietyDim`). Size estimate ~1.2–1.8k LoC across 4–5 modules.

**Subtlety found on `hsig` (obligation 2 — NOT as cheap as the cert scoped):** `sweep_of_localizedChartAlgEquiv`'s
`hsig` is over `productRankLocus` (rank **=r**, matching RouteCAssembly which applies `hClosure`
separately). The pp-nodrop cert + `sigmaIdeal`/`exists_kostantPartition_partitionIdeal_eq_of` are over
`productRankLocusLE` (rank **≤r**) / `sigmaIdeal`. `vanishingIdeal (productRankLocus)` is NOT freely
equal to `vanishingIdeal (productRankLocusLE)` — that IS the closure content `hClosure` carries (rank-=r
is not Zariski-closed). So `hsig` is **entangled with `hClosure`**: either prove `hsig` over the LE form
and add a `vanishingIdeal (productRankLocus) = vanishingIdeal (productRankLocusLE)` bridge (= the closure
fact, Cited in RouteCAssembly), or restate `dsig`/`hsig` on the LE coordinate ring. Worth a SPECIFY before
the `hsig` grind. ~1.5–2 modules (up from 1–1.5).

---

## Tide progress log — update 10 (`e` seams 1-2 LANDED; gauge-vehicle B fixed; the wall located)

**Banked (committed, zero-sorry, axiom-clean):**
- `Core.ChartLocalizedCoordinates` (seam 1, `f827ebf1`): `chartDsig` (source `dsig = mk(vanishingIdeal
  Σ^r) ΔPdeep`) + `chartGfib` (schur-side `gF = map(algebraMap k O(F)) detSchurS`) — the EXACT
  `dsig`/`gfib` the wrapper `ringKrullDim_eq_of_localized_polyExtensionAlgEquiv` consumes (definitional
  match), with image-unit facts.
- `Core.ChartSchurConnect` (seam 2, `ffc97b5f`): `schurToGfib : SchurLoc →ₐ[k] Localization.Away gF`
  via `IsLocalization.Away.mapₐ` of `mapAlgHom (Algebra.ofId k O(F))` at `detSchurS`, + the unit
  alignment `mapAlgHom_ofId_detSchurS`. **Resolves the update-5 concern** (the SchurLoc-coeff base-change
  IS clean).

**Gauge-vehicle TIE-BREAK (decorrelated Codex xhigh, `codex/gauge-vehicle-{prompt,answer}.md`): VEHICLE B.**
Use the LANDED `endpointGauge` over `SchurLoc` + `gaugeEquiv_endpointGauge_multPoly` (step-3a), carried
into the targets by `schurToGfib` (seam 2). NOT vehicle A (re-deriving `Lmatk/Hmatk/chartGauge`,
`[Field k]`-bound for a concrete matrix, over the localization CommRing — that reopens the L/H plumbing).
So the SchurLoc-coefficient gauge route (the "route-α RISK" of update-5) is in fact the CLEAN vehicle:
`Away.mapₐ` makes the coefficient base-change a one-liner.

**The Ψ substitution, pinned (Codex vehicle-B):** `psiSub : RepCoord d → Localization.Away gF`,
`psiSub x = aeval fibCoordT (gaugeSub d (endpointGauge⁻¹) x)` with `fibCoordT x = algebraMap O(F)
(Away gF) (mk(vanishingIdeal F)(X x))` and the `SchurLoc`-coefficients carried via `schurToGfib`. Then
`chartPsiAeval = aeval psiSub`, descend through `vanishingIdeal Σ` (point-realization + the LANDED
clearing-denominators `away_eq_zero_iff_exists_pow_mul_mem`), lift via `IsLocalization.liftAlgHom`. Φ
dually into `Away dsig`. Glue `AlgEquiv.ofAlgHom`, ext `Localization.algHom_ext`.

**THE WALL (precisely, Codex):** the Ψ product-reconstruction lemma
`aeval fibCoordT (gaugeEquiv d endpointGauge⁻¹ (multPoly rr cc)) = (forced Schur chart matrix entry
rr cc in Away gF)`, via `gaugeEquiv_multPoly` at `P⁻¹` + `endpointGauge_zero/last` + the fibre relation
`mult B = normalForm` + a generic `L·E·H` Schur factorization over the localized target. The
genuinely-hard remaining rung; everything else (descents, round-trips, glue) follows the de-risked
clearing-denominators + point-realization pattern. ~3-4 more modules. **The whole `e` route now has NO
absent-API exposure and a single located wall.**

---

## Tide progress log — update 11 (`e` seams 3+3b LANDED; the Ψ comorphism + its gauge factorization)

**Banked (committed, zero-sorry, axiom-clean; controller-aggregated):**
- `Core.ChartPsiSubstitution` (seam 3, `fac3cbe0`): the un-descended Ψ comorphism via vehicle B —
  `fibCoordT` (fibre-coord evaluator `RepCoord d → Away gF`), `chartPsiTower` (`= aevalTower schurToGfib
  fibCoordT`, carries `SchurLoc`-coeff gauge polys into the target), `chartPsiSub` (`= chartPsiTower ∘
  gaugeSub(endpointGauge⁻¹)`), `chartPsiAeval` (`= aeval chartPsiSub`).
- `Core.ChartPsiReconstruct` (seam 3b, `9763c8eb`): `chartPsiTower_gaugeEquiv` —
  `chartPsiTower (gaugeEquiv(endpointGauge⁻¹) p) = eval₂Hom schurToGfib (chartPsiSub-blocks) p`. The
  bridge reducing the Ψ reconstruction to the LANDED `gaugeEquiv_multPoly` at the inverse gauge. Proved
  via `MvPolynomial.map_aeval` (ring-hom level, scalar-free — sidesteps the `→ₐ[k]`/`→ₐ[SchurLoc]`
  scalar-mismatch) + `aevalTower_comp_algebraMap`. **The fiddly `eval₂`/coercion threading is now a
  solved, reusable pattern for the descent.**

**`e` seam ledger (6 of ~10 modules landed):** seam0 spine (`ChartSweepWiring`) + crux
(`PrincipalOpenComorphism`) ✓; seam1 (`ChartLocalizedCoordinates`) ✓; seam2 (`ChartSchurConnect`) ✓;
seam3 (`ChartPsiSubstitution`) ✓; seam3b (`ChartPsiReconstruct`) ✓. **Remaining (~3-4 modules):**
(a) the product-reconstruction VALUE (`gaugeEquiv(endpointGauge⁻¹)(multPoly) = (Lmat·multPoly·Hmat)`,
then the chart-matrix entry on the fibre via `factor_chart_matrix` over the localization); (b) the Ψ
vanishingIdeal descent → `IsLocalization.liftAlgHom` (point-realization + the LANDED
`away_eq_zero_iff_exists_pow_mul_mem`); (c) the Φ direction symmetrically (`aevalTower` into
`Away dsig`, SchurVar→multPoly blocks); (d) the round-trips + `AlgEquiv.ofAlgHom` glue (ext via
`Localization.algHom_ext`). All API present; route fully de-risked; the gauge-vehicle + factorization
infrastructure is in place.

**Handoff state:** spine green & committed; the two remaining hard inputs (`e`, `hsig`) are isolated
named hypotheses, fully scoped, no absent-API exposure, but each a multi-module grind. The `e` build is
the ~1.2–1.8k-LoC route-(b) plumbing (Ψ/Φ localized AlgHoms + round-trips), wall = the Ψ vanishingIdeal
descent (mechanism de-risked: point-realization + the LANDED clearing-denominators primitive).
