# Thread 31 — set-level chart-trivialization for `hSweep`: reachability adjudication

*Seat: pen-and-paper, witness direction. RE-TASK (supersedes orbit-dim brief). Target: does the
PARAMETERIZED endpoint gauge carry the gauge-image of `Σ̄^r ∩ chart` onto the PRODUCT SET
(base δ-directions) × (fibre E) AT THE SET LEVEL — escaping the R2-3b-4 ring-level circularity?
Read-only — no Lean writes, no builds. Decorrelated xhigh Codex fired independently.*

## VERDICT (one line)

**REACHABLE — the set level genuinely ESCAPES the R2-3b-4 circularity.** The membership equality
"`A ∈ Σ̄^r ∩ chart ⟺ gauge(A) ∈ product set`" is *pointwise Schur-complement linear algebra*
(`rank M ≤ r ⟺ B22 − B21 Δ⁻¹ B12 = 0` on `detΔ ≠ 0`) — NO reducedness, NO strict ideal inclusion,
NO ideal-generation, NO primality. It feeds `varietyDim` through `vanishingIdeal` (radical by
construction) + the LANDED `varietyDim_eq_of_coordRingAlgEquiv` / `ringKrullDim_quotient_comap_ringEquiv`
gauge transport. The residual wall is NO LONGER the determinantal-ideal/reducedness obstruction; it
relocates to the **product/principal-open dimension** package — and that is *lighter than first
feared*: the `+δ` part is the LANDED Mathlib `MvPolynomial.ringKrullDim_of_isNoetherianRing`
(present at v4.29, NOT the `proof_wanted`), routed through `O(chart) ≅ O(F)[δ Schur vars]_loc` rather
than the absent tensor theorem. **Estimate ~6-10 modules**, all non-circular; the genuine new pieces
are the localized-polynomial-extension dimension + the localization-no-drop + the finite-cover/density
glue. My reading and a decorrelated xhigh Codex concur on every load-bearing point.

---

## The make-or-break (Q1): the set equality is pointwise linear algebra, NOT the strict inclusion

This is the decisive distinction between the set-level route and the walled R2-3b-4 ring route.

**The R2-3b-4 circularity, precisely.** The ring route built `Sred = Localization.Away ΔPdeep ⧸
IadDeep` (`DeepChartRing.lean`, `IadDeep = (sigmaIdeal d r).map (algebraMap…)`) and tried a *ring iso*
`e : Sred ≃ₐ[k] SchurLoc ⊗_k FibreAlg`. Its forward map needed the **strict ideal inclusion**
`sigmaIdeal ≤ ker(comorphism)`, available only as `≤ radical(ker)`; establishing the strict inclusion
**is** the reducedness of the cut, the thing `e` was meant to prove. The `N = 1` analogue SUCCEEDED
(`DeterminantalBasePresentation`: `Iad = J` earned via `Ideal.height_strict_mono_of_is_prime` — *both
ideals PRIME*, equal height + containment ⟹ equal) precisely because `N = 1` is IRREDUCIBLE. For deep
`N ≥ 2`, `Σ̄^r` is REDUCIBLE (`SigmaComponents`: `sigmaIdeal = sInf orbitIdeals`, θ minimal primes,
θ > 1 generically) — so `IadDeep`/`J` are NOT prime, the height-strict-mono argument FAILS, and "equal
height + containment ⟹ equal" is false for reducible loci (the brief's wall note). THAT is the
R2-3b-4 wall.

**The set-level escape sidesteps exactly that ideal-equality.** The crux fact:

> On the pivot chart `U = {detΔ ≠ 0}`, for a block matrix `M = [[Δ, B12], [B21, B22]]` with `det Δ ≠ 0`,
> **`rank M ≤ r  ⟺  B22 − B21 Δ⁻¹ B12 = 0`.**

This is elementary: the unitriangular conjugation `L⁻¹ · M · H⁻¹` (with `L = [[I,0],[B21Δ⁻¹,I]]`,
`H = [[Δ,B12],[0,I]]`) collapses `M` to `[[I_r, 0],[0, Δ⁻¹·(B22 − B21Δ⁻¹B12)·…]]`-type block-diagonal
form, and `L, H` invertible (over the localization) preserve rank — so `rank M ≤ r ⟺` the
Schur-complement block vanishes. The matrix heart `schurComplement_normal_form` is **LANDED**
(`SchurGauge.lean:168`, sorry-free, network-free, any `CommRing`): `L⁻¹·M·H⁻¹ = diag(I_r,0)` *given*
the Schur relation `B22 = B21Δ⁻¹B12`. The remaining step is the *iff* (rank ≤ r ⟺ Schur block = 0),
standard `Matrix.rank` linear algebra on a principal open.

**Why this is free of reducedness (CRISP yes/no answer to Q1): YES, free.** The set equality is checked
**pointwise** — `A ∈ Σ̄^r ∩ U ⟺ gauge(A)` has the normalized block form with `B22` determined by
`(Δ, B12, B21)`. The proof is membership-iff-membership of point sets, and uses only:
(i) `schurComplement_normal_form` (landed) + the rank-iff (linear algebra); (ii) `mult` equivariance
`mult(P • A) = P_N · mult A · P_0⁻¹` (`FibreNormalForm.mult_smul`, landed) to send the normalized
point into `fibre E`; (iii) the sweep set identity `Σ^r = ⋃_P (P•)''F`
(`EndBaseChangeSweep.productRankLocus_eq_iUnion_smul_fibre`, landed). No nilpotents, no radical
membership, no `IadDeep = J` ideal equality, no primality. Codex (decorrelated) independently reaches
the identical CRISP yes: *"the set equality is genuinely pointwise linear algebra. It is not
equivalent to the strict ideal inclusion … No nilpotents, no radical membership, no reducedness."*

**The formal mechanism that turns the set equality into `varietyDim`** (all LANDED, all non-circular):
- `sigmaIdeal := vanishingIdeal(canonicalCoord '' Σ̄^r)` is **radical by construction**
  (`SigmaComponents.lean:130`) — contrast `fibreGenIdeal := span{multPoly − C(B)}`
  (`MultComorphism.lean:153`), the generator ideal whose radicality the OLD route needed. The set
  route NEVER touches `fibreGenIdeal`'s radicality.
- `varietyDim Z := (ringKrullDim (R ⧸ vanishingIdeal Z)).unbotD 0` reads `Z` only through its
  vanishing ideal, and is radical-insensitive (`VarietyDimRadical.ringKrullDim_quotient_radical`,
  landed). So the whole build runs on the reduced/closed-set structure.
- The gauge `gaugeEquiv (endpointGauge)` is a **regular AUTOMORPHISM** of `MvPolynomial (RepCoord d)
  SchurLoc` (`EndpointNormalization.gaugeEquiv`, an `AlgEquiv` via `AlgEquiv.ofAlgHom`, round-trips
  by the group-action laws — landed), with mult-transport `aeval_gaugeSub_multPoly` (landed). A
  regular automorphism transports `vanishingIdeal` by `comap` WITHOUT generators
  (`FibreNormalForm.vanishingIdeal_image_smul` + `RingEquiv.height_comap`, landed), and preserves
  `varietyDim` (`VarietyDimRadical.ringKrullDim_quotient_comap_ringEquiv` /
  `varietyDim_eq_of_coordRingAlgEquiv`, landed — the latter transports `varietyDim` across a
  coordinate-ring `AlgEquiv` even between DIFFERENT ambient spaces, the bridge to the product set).

So the set-level route uses a *bijective* comap of an automorphism (free), not the *non-injective*
comorphism whose strict-inclusion need walled the ring route. **The circularity is structurally
absent.** This is a genuine route-improvement, not the old wall in disguise.

---

## The residual wall (Q2): product-set dimension — lighter than feared

Granting the set equality `gauge(Σ̄^r ∩ U) = (base δ-set) × (fibre E)`, the `varietyDim` must split:
`varietyDim(chart) = δ + varietyDim F`. Codex confirms the mathematics (`dim(X×Y) = dim X + dim Y`,
reducible included, via `max_{i,j}(dim X_i + dim Y_j) = max dim X_i + max dim Y_j`).

**The Mathlib gap and its cheap detour (FACT-checked against the v4.29 source):**
- The general tensor theorem `ringKrullDim (A ⊗_k B) = dim A + dim B` is **ABSENT** (confirmed: no
  such lemma; `MvPolynomial.fin_ringKrullDim_eq_add_of_isNoetherianRing` is a `proof_wanted`,
  `KrullDimension/Basic.lean:94`). `trdeg`-of-tensor also absent. So the LITERAL "product set" framing
  (a tensor product of coordinate rings) hits the absent theorem.
- **BUT the cheaper route avoids it.** The chart total ring is a *localized polynomial extension* of
  the fibre ring by the δ Schur base-coordinates: `O(chart) ≅ O(F)[δ Schur vars]_loc`. The `+δ` then
  comes from **`MvPolynomial.ringKrullDim_of_isNoetherianRing`** — which IS PRESENT at v4.29
  (`KrullDimension/Polynomial.lean:119`): `ringKrullDim (MvPolynomial ι R) = ringKrullDim R + Nat.card ι`
  for finite `ι`, ANY commutative Noetherian `R` (no domain hypothesis — handles reducible `O(F)`).
  This is the SAME lemma the engine already uses for the `N = 1` base presentation
  (`DeterminantalBasePresentation`, "Sd a polynomial localization"). So the product-dimension wall the
  SPECIFY/noncirc docs flagged as "the dominant new cost / the real Mathlib gap" is **partly
  dissolved**: the polynomial-extension `+δ` is landed Mathlib; only the *localization-no-drop* +
  *reducible-max bookkeeping* remain new.

**Is this the real residual wall?** It is the *dominant* residual COST, but it is NOT a wall (not
Mathlib-absent in the form needed). Codex concurs: *"you can avoid the fully general product theorem
… use Mathlib's present `MvPolynomial.ringKrullDim_of_isNoetherianRing` for the `+δ` part, plus a
principal-open localization no-drop lemma. This is still real work, but narrower than arbitrary
reducible product dimension."* The one genuine subtlety to verify in the build: that the gauge over
`SchurLoc` (a *localization*, not a field) and the chart structure genuinely present `O(chart)` as
`O(F)[δ vars]_loc` at the SET level — i.e. the set product `(base δ-directions) × (fibre E)` has
coordinate ring `O(F) ⊗ O(δ-affine-space)` localized; since one factor is a free polynomial ring (the
δ base coords are unconstrained on the chart), this is a polynomial extension, NOT a general tensor of
two constrained rings. That is what makes `ringKrullDim_of_isNoetherianRing` apply.

---

## The localization-dimension sublemma (Q3): reachable, not a wall

"A non-empty Zariski-open `D(f)` of an irreducible affine variety `A` has `dim A`."
`ringKrullDim_localization` is Mathlib-absent at v4.29 (confirmed: no packaged theorem). But the
sublemma is reachable by the height-at-a-closed-point route, and the engine ALREADY has the closed-
point equidimensionality bricks:
1. `dim A_f ≤ dim A` (prime correspondence / `IsLocalization.orderIsoOfPrime`, present).
2. pick a maximal `𝔪` with `f ∉ 𝔪`; `height(𝔪 A_f) = height 𝔪` (localization preserves height at a
   prime disjoint from the inverted set — `IsLocalization` height lemmas, present).
3. for a finite-type domain over a field, `height 𝔪 = ringKrullDim A` — this is the engine's LANDED
   `OrbitTangentCotangent.height_eq_ringKrullDim_of_isMaximal_fintype` /
   `FibreDimFibration.affine_domain_height_add_ringKrullDim_quotient_eq_fintype`.
4. ⟹ `dim A_f ≥ dim A`, so `=`.

Codex independently sketches the same five-step route and names the same Mathlib pieces
(`IsLocalization.orderIsoOfPrime`, `AtPrime.ringKrullDim_eq_height`) + the engine's
`height_eq_ringKrullDim_of_isMaximal`. **Reachable, ~1-2 modules.** The reducible caveat (the chart
must meet the relevant top component — Q4 density) is handled below. NOT the conceptual wall.

---

## The glue + density (Q4): reachable, real but bounded cost

- **Finite-union max:** `varietyDim(⋃_i Z_i) = max_i varietyDim Z_i`. The engine's `RadicalCatenary`
  (`height_add_ringKrullDim_quotient_eq_card_of_ne_top`, landed) already gives `dim(R⧸I) = card −
  height I` for reducible `I` via minimal-prime bookkeeping; the union-max form is reachable from
  `vanishingIdeal(⋃) = sInf vanishingIdeals` + minimal-prime/coheight algebra (the SPIKE
  `minimalPrimes_sInf_of_finite_of_isPrime` in `SigmaComponents` is the template). ~1-2 modules.
- **Density:** each top component of `Σ̄^r` meets some rank-`r` pivot chart (`detΔ ≠ 0` somewhere on
  it). This is a component/generic-rank statement (NOT reducedness). The θ/component machinery
  (`SigmaComponents`, `CThetaGeometric`) plausibly supplies it (each top component is a maximal orbit
  closure `Ō_M` of corner exactly `r`, where the generic point has product-rank exactly `r`, so some
  `r×r` minor of `mult` is nonzero there). ~1 module if it leans on the landed component identification;
  budget 1 more if a fresh generic-rank-on-a-component lemma is needed. Codex flags this as the one
  step to size carefully — "if already available from the θ/component machinery, glue is manageable;
  otherwise budget another component/density module." I agree; it is the second-most-likely place the
  estimate slips.

---

## Module-count estimate (honest)

| Rung | Content | Status |
|---|---|---|
| 1 | Chart membership iff: `rank M ≤ r ⟺ Schur block = 0` on `detΔ≠0` (the Q1 crux) | PROVABLE — landed `schurComplement_normal_form` + rank-iff linear algebra. ~1-2 modules. |
| 2 | Gauge-image set equality `gauge(Σ̄^r∩U) = (base δ-set)×(fibre E)`, via sweep identity + equivariance | PROVABLE-cheap — landed sweep + `mult_smul` + rung 1. ~1-2 modules. |
| 3 | `O(chart) ≅ O(F)[δ vars]_loc` dimension: `+δ` via landed `ringKrullDim_of_isNoetherianRing` + localization-no-drop (Q3) | ~2-3 modules (dominant cost; `+δ` lemma landed, no-drop + reducible-max new). |
| 4 | Finite-cover glue + density (Q4) | ~2-3 modules (density is the sizing risk). |
| 5 | Assemble `hSweep` → feed landed `RouteCAssembly._of_sweep'` | ~1 module. |

**Total ≈ 6-10 modules**, ALL non-circular. (Slightly below the earlier 9-13 SPECIFY estimate,
because the `+δ` poly-extension lemma being landed Mathlib removes one of the "product-dimension"
sub-rungs the SPECIFY budgeted as new.)

---

## Engine handles VERIFIED (file + name)

PRESENT (read and confirmed):
- `SchurGauge.schurComplement_normal_form` (`:168`) — `L⁻¹·M·H⁻¹ = diag(I_r,0)`, the Q1 matrix heart.
  Sorry-free, any `CommRing`. `+ endpointGauge` (`:132`), `isUnit_Lmat`/`isUnit_Hmat`, the Schur unit
  `isUnit_det_schurΔLoc`.
- `EndBaseChangeSweep.productRankLocus_eq_iUnion_smul_fibre` (`:81`) — `Σ^r = ⋃_P (P•)''F`.
- `FibreNormalForm.{mult_smul (:77), vanishingIdeal_image_smul (:111), codimRep_baseChange_image (:141)}`
  — equivariance + automorphism vanishing-ideal transport by comap.
- `EndpointNormalization.{gaugeEquiv, aeval_gaugeSub_multPoly (:143)}` — the regular automorphism +
  mult-transport over an arbitrary coefficient ring (here `SchurLoc`).
- `VarietyDimRadical.{ringKrullDim_quotient_radical, varietyDim_eq_of_coordRingAlgEquiv (:57),
  ringKrullDim_quotient_comap_ringEquiv (:80)}` — the radical-insensitivity shield + the
  cross-ambient-space `varietyDim` transport (the linchpin).
- `SigmaComponents.sigmaIdeal` (`:130`) = `vanishingIdeal(…)` (radical by construction); reducible
  (θ minimal primes).
- `RadicalCatenary.height_add_ringKrullDim_quotient_eq_card_of_ne_top` — reducible catenary
  `dim = card − height`, the union-max template.
- **Mathlib** `MvPolynomial.ringKrullDim_of_isNoetherianRing` (`KrullDimension/Polynomial.lean:119`)
  — `dim (MvPolynomial ι R) = dim R + card ι`, finite `ι`, any Noetherian `R`. THE `+δ` brick;
  PRESENT (NOT the `proof_wanted`).
- **Mathlib** `IsLocalization.orderIsoOfPrime`, `AtPrime.ringKrullDim_eq_height`, engine
  `height_eq_ringKrullDim_of_isMaximal_fintype` — the Q3 localization-no-drop bricks.

SEARCHED AND ABSENT (handled by detour, NOT walls):
- `ringKrullDim (A ⊗_k B) = dim A + dim B` (absent — detoured via the poly-extension form).
- `ringKrullDim_localization` packaged (absent — detoured via the closed-point height route, Q3).
- `varietyDim(⋃) = max` packaged (absent — buildable from minimal-prime algebra, Q4).

---

## Decorrelated Codex (xhigh, gpt-5.x) — independent read

Fired with the hypothesis WITHHELD (the four questions + facts only; I did NOT tell it my tentative
"escapes"). Codex VERDICT independently matches: *"SET-LEVEL ESCAPES the circularity; the residual
wall is the absent reducible product/principal-open dimension package … about 3 tailored modules,
5-ish for a general product theorem."* On Q1 it gave the identical CRISP yes (pointwise Schur-complement
linear algebra, not the strict inclusion). On Q2 it independently named the SAME detour
(`O(F)[δ vars]_loc` via the present `ringKrullDim_of_isNoetherianRing`, avoiding the absent tensor
theorem). On Q3 it independently sketched the SAME closed-point height route. On Q4 it independently
flagged density as the sizing risk. Transcript: `codex/set-level-trivialization-{prompt,answer}.md`.
**Agree** with the adjudication on every load-bearing point; the decorrelated read surfaced no escape
or wall I missed, and converged on the same residual + the same Mathlib detour. (Codex's module count
is for the dimension package alone, ~3-5; my 6-10 total includes rungs 1-2 chart-iff + rung 4 glue.)

---

## Close

- **Firmest result:** the set-level chart-trivialization is **REACHABLE and genuinely non-circular**.
  The R2-3b-4 circularity was specific to building a *ring iso* through a *generator* ideal (needing
  primality / strict inclusion / reducedness, all of which FAIL for the reducible deep loci). The set
  level works through `vanishingIdeal` (radical) + `varietyDim` (radical-insensitive) + a *regular
  automorphism* comap (bijective, free) — the membership equality is pointwise Schur-complement linear
  algebra. The residual is the product/principal-open DIMENSION package, with the `+δ` part LANDED
  Mathlib (`ringKrullDim_of_isNoetherianRing`), the localization-no-drop reachable (closed-point
  height), the glue+density reachable (minimal-prime algebra + component machinery). ~6-10 modules.
- **Most likely thing to break it:** (a) the chart structure presenting `O(chart)` as a *polynomial*
  extension `O(F)[δ vars]_loc` rather than a *general* tensor — if the δ base coordinates are NOT
  cleanly free/unconstrained on the chart (e.g. the Schur localization couples them to fibre
  coordinates in a way that blocks `ringKrullDim_of_isNoetherianRing`), the build falls back to the
  absent tensor theorem and the cost jumps. (b) the Q4 density — if "each top component meets a
  rank-`r` chart" is NOT immediate from the landed θ/component machinery, budget +1 module.
- **Next construction/consult that would settle the open part:** a focused SPECIFY on rung 3 — pin
  the EXACT chart presentation `O(Σ̄^r ∩ U) ≅ ?` and confirm the δ base coordinates appear as FREE
  polynomial generators over `FibreAlg` (localized), so `ringKrullDim_of_isNoetherianRing` applies
  directly. That single check decides whether rung 3 is ~2-3 modules (poly-extension) or re-incurs the
  absent tensor wall. It is the highest-value de-risk before the grind commits to rung 3.
