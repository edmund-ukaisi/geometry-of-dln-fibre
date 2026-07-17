import DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedPeelStep
import DLNFibre.DLN.RLCT.Validate.RouteMSJIncidenceGluing

/-!
# `RouteMSJProductCorankEngine` — the NATIVE product-corank engine (Lane 2, SKELETON)

**Thread `genm-l2engine`, aoyagi-full endgame.** The mission: discharge the socket
`cited_aoyagi_product_corank` (`RouteMSJDecoratedPeelStep:70`) NATIVELY — the `min-corank ≥ 2`
product-corank / joint-Vandermonde box-finiteness that is (the DLN specialisation of) Aoyagi's
worked-out log-resolution (Entropy 2013, App. C, Step 1 (i)–(v)). When the terminal theorem
`productCorankBoxFinite` here is sorry-free, the carried `Prop` hypothesis becomes a native theorem →
`(□)` closes at clean-three with NO Aoyagi hypothesis. SCOPE EXCLUDES meromorphic continuation + the
order `θ`.

**THIS IS THE SKELETON (statements-first).** The terminal is TYPED so it IS the socket's `Prop`
(verified by the in-file `fit` example `example : cited_aoyagi_product_corank := @productCorankBoxFinite`).
The analytic content is isolated into NAMED holes whose HYPOTHESIS LISTS are the progress metric.

## The terminal fits the socket (the FIT)

`productCorankBoxFinite` has verbatim the unfolded `cited_aoyagi_product_corank` signature (ρ dropped —
the freed-Γ integrand uses only `κ`, precision.md 1.1.3). The `fit` example forces the defeq.

## The resolution structure the engine transcribes (from prodcorank-cert + decstep-cert, 8 rounds)

For a min-corank≥2 pivot cut `t` (`a = M₀−t ≥ 2`, `b = M₁−t ≥ 2`), one peel of the freed-Γ triple
integral (`∫ A' ∫ x ∫ Γ`) decomposes as (decstep round-4 §1):

1. **Schur-weld** (banked, `chartInner_schurWeld_eq`): `freedSchurLoss = frobSq(P·Q̃ₚ) +
   frobSq(C·Q̃ₚ + Γ·Q_b)`, `Q̃ₚ = Q_p + P⁻¹·B₁₂·Q_b` (the pivot-shifted tail, `pivotTail`).
2. **Integrate the coupling `C = x.2`** (banked `gammaAtom_aniso_shifted_eq`, verified c-agnostic): →
   the **PIVOT Gram** `det(Q̃ₚ·Q̃ₚᵀ)^{−a/2}` × `(w + ‖Γ·Q_b·(I − P_{Q̃ₚ})‖²)^{−(c'−a·t/2)}`. Carry the
   PIVOT Gram (full rank `t`, `qbox`-disposable), **NEVER the corank Gram** `det(Q_b·Q_bᵀ)` — the atom
   trap (`a < q−b+1` is `a<a` = FALSE at edge dims, divergent on the rank-deficient corank locus).
3. **Stratify the shared-tail rank** `r = rank Q_b` (`tailRankStratum`): the outer `A'`-box splits into
   the finitely many rank sectors; per sector the stratum codim is `A_r = (corank at the deepened cut)² =
   peelCharge M (deepened cut)` (round-5 care-point — NOT the mislabeled `(b−r)²`).
4. **Resolve the inner residual** `frobSq(Γ·Q_b·(I−P_{Q̃ₚ}))` via the **c×c SVD determinantal chart
   family** (`corankSVD_chartFamily_lt_top`, the §H heart — `d = c` exceptional coordinates on the
   measurable eigenframe, NOT a single radial which resolves only `Γ=0` for c≥2), with the
   **transverse-Jacobian `> −1` sign repair** uniform across shared-tail rank strata
   (GAP-IN-RELATIVE-JACOBIAN): `|det J| = A_r` codim raises the naive `k−n` exceptional exponent above
   `−1`, because `Q̃ₚ, Q_b` are shared DEEPER products (non-submersive pullback), not free matrices.
5. **Land on `hIH`.** Each stratum's pushforward is a finite sum of shifted PLAIN reduced-chain integrals
   `redChain t M` at the threshold shifted by `½·peelCharge`, closed by `hIH (redChain t M)` — the
   descent's arithmetic (`reducedChain_threshold_shift`) is banked and AIRTIGHT.

## What is BANKED (consume, do NOT re-derive) — §A–§G of recon-map

finite-cover glue (`lintegral_lt_top_of_finite_cover`/`_finset_cover`); the `rightMulₚ` CoV kit
(`det_rightMulₚ`, exact Haar Jacobian); the radial engine (`corner_block_cube_lintegral_lt_top` =
`rlct=codim/2` realized); `qbox_lintegral_lt_top` (Wishart pivot-Gram disposal); the measurable
eigenframe (`measurableEigendecomp`, the SVD substrate); the `minAdm`/QIP backbone
(`half_minAdm_sub_half_peelCharge_le`, threshold-invariance DONE); the Schur-weld / shear / freed-Γ
spine (`gammaPeelIntegral_schurShearFree_eq`, `gammaAtom_aniso_shifted_eq`, the two scoped inner atoms
`freedSchurLoss_inner_peel_lt_top` / `_bounded_lt_top`).

## What is FORBIDDEN (5 DEAD routes, refuters in recon-map §DEAD + witness-battery W1–W3)

(1) ATOM TRAP — carry PIVOT Gram, not corank Gram (step 2). (2) naive-`m²` / single-factor
transversality at min≥2 (W1: joint center `(x,y,b)` survives; W2: `C_m < m²` undershoots). (3) a single
radial coord for c≥2 (resolves only `Γ=0`). (4) pointwise inner-peel (the atoms need PosDef Gram — lift
to MEASURE-level, supplied by the descent, NOT pointwise). (5) `cornerComparator` flat domination
(L≥1-unsound) + radialize-and-drop-Jacobian.

## Coverage (W4 E5, l2witness — ADJUDICATED COVER) — the per-cut Prop is UNAFFECTED

W4 pins two boundaries: the PATH boundary `= 5` (smallest `n` with NO all-`d≤1` optimal peel path) and
the COVER boundary `= 4` (smallest `n` with a binding `d≥2` atom anywhere on the optimal recursion).
**The COVER boundary is OPERATIVE for this engine**, because `decoratedPeelStep_proof` bounds the box by
`sjBoundaryPeel` then `ENNReal.sum_lt_top` over ALL cuts `(t,ρ,κ)` — so EVERY term must be finite: the
resolution is a COVER (all cuts), not a chosen dominating path. A single dominating branch (PATH, `n≥5`)
is obstructed by W1 (single-factor blow-ups leave the joint center `(x,y,b)` with its alignment
coordinate). **Consequence (adjudicated): every `d = min(M₀−t, M₁−t) ≥ 2` cut in the sum routes to THIS
engine; `n=3` is the largest fully-native square chain; `n≥4` each have binding `d≥2` atoms the cover
transcribes** (e.g. `(4,4,4,4)` has TWO: `@t=2` block `2×2` and `(3,4,4)@t=1` block `2×3`; budget EXACTLY
tight — charge + `minAdm(reduced) = minAdm(M)`, no slack, so the transcribe delivers the threshold
exactly, W4 E4′). This does NOT change the terminal `Prop` (keyed per-cut on `2 ≤ min(M₀−t, M₁−t)`). If a
valid cover whose `d≥2` binding charts resolve NATIVELY (evading W1) is later found, the footprint
shrinks — but that is to be PROVEN, not assumed; the default is `n≥4`.

## Named holes — the hypothesis-list report

* PROVEN bricks: `reducedChain_threshold_shift` (descent arithmetic), `tailRankStrata_cover`
  (region-glue index-completeness).
* Analytic holes (`sorry`): `corankSVD_chartFamily_lt_top` (§H heart — the c×c SVD determinantal
  resolution), `corankStratum_lt_top` (the per-stratum outer-measure descent — the whole §H, consuming
  the SVD family + transverse-Jac sign repair + relative principalization + `hIH`).

This module is UNTRACKED / NOT wired into `DLNFibre.lean` or `AxCheck` — the canonical library stays
clean-three; the controller wires it when the analytic holes are filled. `#print axioms` on the terminal
is the mint check (deferred to fill-completion).
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory
open scoped ENNReal BigOperators

variable {L : ℕ}

/-! ## Helper objects for the resolution -/

/-- **The pivot-shifted tail** `Q̃ₚ = Q_p + P⁻¹·B₁₂·Q_b` (`P = of x.1.1`, `B₁₂ = of x.1.2`,
`Q_p = Q.submatrix Sum.inl id`, `Q_b = Q.submatrix Sum.inr id`) — the full-row-rank (generically) tail
whose Gram `Q̃ₚ·Q̃ₚᵀ` the C-integration (step 2) carries. NEVER the corank Gram `Q_b·Q_bᵀ` (atom trap). -/
noncomputable def pivotTail {t a b q : ℕ} (x : SJOuter t a b)
    (Q : Matrix (Fin t ⊕ Fin b) (Fin q) ℝ) : Matrix (Fin t) (Fin q) ℝ :=
  Q.submatrix Sum.inl id + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id

/-- **The shared-tail corank rank** `r = rank Q_b` at an outer tail parameter `A'`, `Q_b` the bottom
block of the reindexed tail product `(prod (tailChain M) A').submatrix (blockSplitEquiv κ) id`. The
`A'`-box stratifies into the finitely many rank sectors (step 3); `r ≤ M₁−t` (`Matrix.rank_le_card_height`). -/
noncomputable def tailCorankRank (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ)
    (κ : Fin t ↪ Fin (M 1)) (A' : Params (tailChain M)) : ℕ :=
  (((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id).submatrix Sum.inr id).rank

/-- **The shared-tail rank-`r` stratum** of the outer `A'`-box (step 3). The cover
`⋃_{r ≤ M₁−t} tailRankStratum` is total (`tailRankStrata_cover`); per stratum the residual is resolved
by the c×c SVD chart family with the `A_r`-codim transverse Jacobian. -/
noncomputable def tailRankStratum (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ)
    (κ : Fin t ↪ Fin (M 1)) (r : ℕ) : Set (Params (tailChain M)) :=
  {A' | tailCorankRank M t κ A' = r}

/-! ## PROVEN brick 1 — the descent arithmetic (threshold shift onto the reduced chain) -/

/-- **The reduced-chain threshold shift (PROVEN, banked arithmetic).** Below the geometric threshold
`c' < ½·minAdm M`, at a legal cut `t ≤ min(M₀,M₁)`, the `½·peelCharge`-shifted threshold is STRICTLY
below `½·minAdm (redChain t M)` — so `hIH (redChain t M)` closes each reduced-chain term (step 5). This
is the airtight arithmetic half of the descent; the surviving analytic content is the transverse-Jacobian
realization of this budget (`corankStratum_lt_top`). Consumes the banked
`half_minAdm_sub_half_peelCharge_le` (the `minAdm` recursion, QIP backbone §F). -/
theorem reducedChain_threshold_shift (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ)
    (ht2 : t ≤ min (M 0) (M 1)) (c' : NNReal) (hc' : (c' : ℝ) < (minAdm M : ℝ) / 2) :
    (c' : ℝ) - (peelCharge M t : ℝ) / 2 < (minAdm (redChain t M) : ℝ) / 2 := by
  have h := half_minAdm_sub_half_peelCharge_le M t ht2
  linarith

/-! ## PROVEN brick 2 — region-glue index-completeness (the shared-tail rank cover is total) -/

/-- **The shared-tail rank strata cover the outer box up to null (PROVEN, region glue).** Every outer
tail parameter `A'` lies in the rank-`r` stratum for its own `r = tailCorankRank ≤ M₁−t`, so the
finite family `{tailRankStratum M t κ r}_{r < M₁−t+1}` covers `paramsBoxM (tailChain M) 1` with EMPTY
complement (a fortiori null). This is the index-completeness the finite-cover glue
(`lintegral_lt_top_of_finset_cover`) needs (recon §A, §4 gap 3 — Lean labor over banked math, DONE).

**Coverage note (W4 E5, adjudicated COVER):** the strata here are keyed on `rank Q_b` (the per-`A'`
inner cover). Which CUTS `t` route to this engine is the W4 COVER question — operative because
`sjBoundaryPeel + ENNReal.sum_lt_top` demands EVERY cut finite (not a chosen path): every `d≥2` cut
transcribes, `n≥4` each carry binding `d≥2` atoms, `n=3` is the largest fully-native square. Orthogonal
to this per-`A'` rank cover, which is total for any single cut. -/
theorem tailRankStrata_cover (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ) (κ : Fin t ↪ Fin (M 1)) :
    volume ((paramsBoxM (tailChain M) 1) \
      ⋃ i ∈ (Finset.univ : Finset (Fin (M 1 - t + 1))), tailRankStratum M t κ (i : ℕ)) = 0 := by
  have hsub : (paramsBoxM (tailChain M) 1) ⊆
      ⋃ i ∈ (Finset.univ : Finset (Fin (M 1 - t + 1))), tailRankStratum M t κ (i : ℕ) := by
    intro A' _
    have hle : tailCorankRank M t κ A' ≤ M 1 - t := by
      have := Matrix.rank_le_card_height
        (((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id).submatrix Sum.inr id)
      simpa [tailCorankRank] using this
    refine Set.mem_iUnion₂.mpr ⟨⟨tailCorankRank M t κ A', ?_⟩, Finset.mem_univ _, rfl⟩
    omega
  rw [Set.diff_eq_empty.mpr hsub]
  exact measure_empty

/-! ## Analytic hole (§H heart) — the c×c SVD determinantal chart family -/

/-- **THE §H HEART (hole) — the c×c SVD determinantal resolution of the corank singularity.** For a
corank block `min(a,b) ≥ 2` and a projected tail `S : Matrix (Fin b) (Fin q) ℝ` (the `Q_b·(I−P_{Q̃ₚ})`
of step 4), the pure corank singularity `‖Γ·S‖^{−2c'}` (free `Γ : Fin a → Fin b`) is box-integrable
below the ACTIVE-DIRECTION threshold `2c' < a·rank(S)` (the image `Γ ↦ Γ·S` has dimension `a·rank(S)`).

This is the resolution CONSTRUCTION (Aoyagi App. C Step 1, item (a)): the FULL multi-singular-value
blow-up — `d = c` exceptional coordinates on the measurable eigenframe (`measurableEigendecomp`) of
`S·Sᵀ` — NOT a single radial coordinate (which resolves only `Γ=0`, not the rank-`1..c−1` cone; DEAD
for c≥2, decstep round-3 §3). The threshold `2c' < a·rank(S)` is the `> −1` exceptional-exponent
certificate; the transverse-Jacobian sign repair (GAP-IN-RELATIVE-JACOBIAN) is what makes `rank(S)`
(not the naive `b`) the operative count uniformly across shared-tail rank strata.

**Kill-conditions (must pass):** min(a,b)≥2 (W1: joint center survives single-factor); the count is
`rank(S)` not `b` (W2: `C_m < m²`, the non-submersive product-corank gap); tightness at the binding
cell (W3/W4). **Status: OPEN** (the genuinely-new §H content — transcription of Aoyagi's resolution;
the arithmetic budget is banked, the analytic determinantal CoV + Jacobian bookkeeping is NEW).

**Level discipline (l2witness E5, load-bearing):** the eventual PROOF must establish genuine
PRINCIPALIZATION — that the chart family is an actual SNC log-resolution whose charts principalize the
joint ideal (W1: single-factor blow-ups do NOT — the joint center `(x,y,b)` with its alignment coordinate
survives). A cross-check of the divisor RATIOS `min_i (a_iᵢ+1)/(2Nᵢ) ≥ c*` certifies `rlct ≥ c*`
CONDITIONAL on the `(aᵢ,Nᵢ)` coming from a valid resolution; it does NOT certify that validity, and a
green ratio-check is NOT by itself a native re-derivation of `rlct = c*`. Establishing the resolution's
validity at d≥2 (not merely its ratios) is exactly this hole's burden — the boundary between native and
cited. `hthr = 2c' < a·rank(S)` is the active-direction count of the corank block ALONE; the operative
per-stratum gate couples it with the transverse-Jacobian `|det J| = A_r = (b−r)²` weight (satred's
rank-sector charge, `min_r[A_r + minAdm(reducedᵣ)] = minAdm`), so the final per-chart exponent form is
NOT `hthr` alone — it is pinned when the SVD chart maps are built. -/
theorem corankSVD_chartFamily_lt_top {a b q : ℕ} (hab : 2 ≤ min a b)
    (S : Matrix (Fin b) (Fin q) ℝ) (c' : NNReal)
    (hthr : 2 * (c' : ℝ) < (a : ℝ) * (S.rank : ℝ))
    (box : Set (Fin a → Fin b → ℝ)) (hbox : volume box < ⊤) :
    ∫⁻ Γ in box, ENNReal.ofReal ((frobSq (Matrix.of Γ * S)) ^ (-(c' : ℝ))) < ⊤ := by
  sorry

/-! ## Analytic hole — the per-stratum outer-measure descent (the whole §H at measure level) -/

/-- **THE PER-STRATUM DESCENT (hole) — the freed triple integral over one shared-tail rank stratum.**
For a min-corank≥2 cut `t` below threshold, GIVEN the one-shorter PLAIN IH `hIH`, the freed-Γ triple
integral RESTRICTED to the rank-`r` stratum `tailRankStratum M t κ r` is finite. This is the outer
`(S,J)` measure-level descent — where the genuinely-new content lives (the inner Γ-integral is finite
POINTWISE by `freedSchurLoss_inner_bounded_lt_top`; the difficulty is the OUTER integrability against
the `x → pivot-rank-drop` / `A' → tail-rank-drop` singularities).

Its fill (the transcription of Aoyagi App. C Step 1) consumes, per stratum:
* **C-integration → PIVOT Gram** (banked `gammaAtom_aniso_shifted_eq`, measure-level): trades the
  coupling `C = x.2` for `det(Q̃ₚ·Q̃ₚᵀ)^{−a/2}` (full rank `t`), NEVER the corank Gram (atom trap);
* **the c×c SVD chart family** `corankSVD_chartFamily_lt_top` (§H heart) resolving the projected residual
  `Γ·Q_b·(I−P_{Q̃ₚ})` to monomial normal form with `|det J| = A_r` codim (transverse-Jacobian `> −1`
  sign repair, uniform across strata — GAP-IN-RELATIVE-JACOBIAN);
* **the relative principalization** of `(Q̃ₚ, Γ·Q_b)` (`Q_b^⊥·Q̃ₚᵀ = 0` identically — a RELATIVE, not
  absolute, principalization): the pushforward is a finite sum of shifted PLAIN reduced-chain integrals;
* **`qbox_lintegral_lt_top`** disposes the pivot Gram; **`hIH (redChain t M)`** at the
  `reducedChain_threshold_shift`-shifted threshold closes each reduced-chain term.

**Kill-conditions:** carry PIVOT not corank Gram; `Γ·Q_b` STRATIFIED not integrated free (overshoot);
`|det J|` always carried; the pivot-Gram gate `c<c+1` is TOP-STRATUM only (deeper strata via the
transverse-Jac repair / recursion). **Status: OPEN** (the multi-tide §H heart at measure level). -/
theorem corankStratum_lt_top (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ)
    (ht : 1 ≤ t) (ht2 : t ≤ min (M 0) (M 1)) (hcork : 2 ≤ min (M 0 - t) (M 1 - t))
    (κ : Fin t ↪ Fin (M 1)) (c' : NNReal) (hc' : (c' : ℝ) < (minAdm M : ℝ) / 2)
    (hIH : ∀ M' : Fin (L + 1 + 1) → ℕ, RouteMBoxThresholdFinite M') (r : ℕ) :
    (∫⁻ A' in tailRankStratum M t κ r,
        ∫⁻ x in outerDom t (M 0 - t) (M 1 - t) 1,
          ∫⁻ Γ in {Γ : Fin (M 0 - t) → Fin (M 1 - t) → ℝ |
              Γ + schurShift x ∈ genBox (Fin (M 0 - t)) (Fin (M 1 - t)) 1},
            ENNReal.ofReal ((freedSchurLoss x Γ
              ((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id)) ^ (-(c' : ℝ)))) < ⊤ := by
  sorry

/-! ## The TERMINAL — typed = the socket's `Prop` (reduces to the holes via the finite-cover glue) -/

/-- **TERMINAL — the native product-corank box-finiteness = `cited_aoyagi_product_corank` (unfolded).**
For a min-corank≥2 pivot cut `t` below the geometric threshold, GIVEN the one-shorter PLAIN IH, the
freed-Γ triple integral is finite. When sorry-free this DISCHARGES the socket natively (see the `fit`
example) → `(□)` at clean-three, no Aoyagi hypothesis.

The proof REDUCES (banked region glue) the outer `A'`-integral to the finitely many shared-tail rank
strata: `tailRankStrata_cover` (index-completeness, PROVEN) + `corankStratum_lt_top` (per-stratum
descent, the §H hole). `ρ` is dropped (the freed-Γ integrand uses only `κ`, precision.md 1.1.3). -/
theorem productCorankBoxFinite {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ)
    (ht : 1 ≤ t) (ht2 : t ≤ min (M 0) (M 1))
    (hcork : 2 ≤ min (M 0 - t) (M 1 - t))
    (κ : Fin t ↪ Fin (M 1)) (c' : NNReal)
    (hc' : (c' : ℝ) < (minAdm M : ℝ) / 2)
    (hIH : ∀ M' : Fin (L + 1 + 1) → ℕ, RouteMBoxThresholdFinite M') :
    (∫⁻ A' in paramsBoxM (tailChain M) 1,
        ∫⁻ x in outerDom t (M 0 - t) (M 1 - t) 1,
          ∫⁻ Γ in {Γ : Fin (M 0 - t) → Fin (M 1 - t) → ℝ |
              Γ + schurShift x ∈ genBox (Fin (M 0 - t)) (Fin (M 1 - t)) 1},
            ENNReal.ofReal ((freedSchurLoss x Γ
              ((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id)) ^ (-(c' : ℝ)))) < ⊤ := by
  refine lintegral_lt_top_of_finset_cover
    (Finset.univ : Finset (Fin (M 1 - t + 1)))
    (fun i => tailRankStratum M t κ (i : ℕ))
    (paramsBoxM (tailChain M) 1)
    (fun A' => ∫⁻ x in outerDom t (M 0 - t) (M 1 - t) 1,
        ∫⁻ Γ in {Γ : Fin (M 0 - t) → Fin (M 1 - t) → ℝ |
            Γ + schurShift x ∈ genBox (Fin (M 0 - t)) (Fin (M 1 - t)) 1},
          ENNReal.ofReal ((freedSchurLoss x Γ
            ((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id)) ^ (-(c' : ℝ))))
    (tailRankStrata_cover M t κ)
    (fun i _ => corankStratum_lt_top M t ht ht2 hcork κ c' hc' hIH (i : ℕ))

/-- **THE FIT** — `productCorankBoxFinite` discharges the socket `cited_aoyagi_product_corank`. Once the
two analytic holes (`corankSVD_chartFamily_lt_top`, `corankStratum_lt_top`) are sorry-free, this makes
the carried box-level Aoyagi hypothesis a NATIVE theorem → `(□)` at clean-three. -/
example : cited_aoyagi_product_corank := @productCorankBoxFinite

end DLNFibre.DLN.RLCT
