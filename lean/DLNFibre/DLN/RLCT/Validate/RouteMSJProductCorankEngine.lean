import DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedPeelStep
import DLNFibre.DLN.RLCT.Validate.RouteMSJIncidenceGluing
import DLNFibre.DLN.RLCT.Validate.RouteMSJCorankMorse
import DLNFibre.DLN.RLCT.Validate.RouteMSJPivotWishart

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
3. **Stratify the full pivot-tail rank** `k = rank Q` (`tailProductRank`/`tailRankStratum`): the outer
   `A'`-box splits into the finitely many rank sectors. Keyed on `rank Q` (the full `[Q_p; Q_b]`), which
   DOMINATES both `rank Q̃ₚ` and `rank Q_b` — so the pivot-degenerate locus `{rank Q̃ₚ<t}` (gammaAtom's
   `hG` failure) is captured at the positive-measure level (`rank Q̃ₚ` depends on `x` not `A'`, so the
   literal joint pair-over-`A'` is ill-defined; `rank Q` is the A'-only dominating realization — action #1).
   Per sector the stratum codim is `A_r = (corank at the deepened cut)² = peelCharge M (deepened cut)`
   (round-5 care-point — the invariant is `(corank-at-cut)²`, not a mislabeled index).
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

/-- **The full pivot-tail rank** `k = rank Q` at an outer tail parameter `A'`, `Q` the reindexed tail
product `(prod (tailChain M) A').submatrix (blockSplitEquiv κ) id` (rows `Fin t ⊕ Fin (M₁−t)` — the
pivot block `Q_p` stacked on the corank block `Q_b`). This A'-only rank **DOMINATES BOTH**
`rank Q̃ₚ ≤ min(t, rank Q)` (`Q̃ₚ = [I | P⁻¹B₁₂]·Q`, the pivot-shifted tail) and `rank Q_b ≤ rank Q`, so
stratifying on it captures the **pivot-degenerate locus** `{rank Q̃ₚ < t}` (where gammaAtom's PosDef `hG`
fails) at the POSITIVE-MEASURE level: `{rank Q̃ₚ < t} ∩ {rank Q ≥ t}` is `x`-null (for a.e. `x`, `Q̃ₚ` has
full row rank `t` when `rank Q ≥ t` — the exceptional `(P,B₁₂)` locus is a proper subvariety), so gammaAtom
applies a.e. on `{rank Q ≥ t}`; the genuine positive-measure degeneracy is `{rank Q < t}`. `k ≤ t+(M₁−t)`
(`Matrix.rank_le_card_height`).

**Realization of the controller's joint `(rank Q̃ₚ, rank Q_b)` index (action #1, RECONCILED):** `rank Q̃ₚ`
depends on `x` (via `P, B₁₂`), NOT on `A'`, so the literal pair-over-`A'` is ILL-DEFINED and a
pair-over-`(A',x)` cover would drag in the measurability of a parameterized inner integral. `rank Q` is
the A'-only DOMINATING index that controls both and captures the positive-measure pivot degeneracy — the
clean realization that keeps the terminal's outer-`A'` cover (no nested-integral measurability). Flagged
to the controller for confirmation. -/
noncomputable def tailProductRank (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ)
    (κ : Fin t ↪ Fin (M 1)) (A' : Params (tailChain M)) : ℕ :=
  ((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id).rank

/-- **The full pivot-tail rank-`k` stratum** of the outer `A'`-box. The cover
`⋃_{k ≤ t+(M₁−t)} tailRankStratum` is total (`tailRankStrata_cover`); the TOP stratum `k = t+(M₁−t)` is
where the tail is full rank so `Q̃ₚ·Q̃ₚᵀ` is a.e. PosDef (gammaAtom's C-integration → PIVOT Gram applies),
while deeper strata `k < t+(M₁−t)` carry the joint pivot/corank degeneracy resolved by the c×c SVD chart
family + the transverse-Jacobian `A_r = (b−r)²` repair. -/
noncomputable def tailRankStratum (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ)
    (κ : Fin t ↪ Fin (M 1)) (k : ℕ) : Set (Params (tailChain M)) :=
  {A' | tailProductRank M t κ A' = k}

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

/-- **The full pivot-tail rank strata cover the outer box up to null (PROVEN, region glue).** Every outer
tail parameter `A'` lies in the rank-`k` stratum for its own `k = tailProductRank ≤ t+(M₁−t)`, so the
finite family `{tailRankStratum M t κ k}_{k < t+(M₁−t)+1}` covers `paramsBoxM (tailChain M) 1` with EMPTY
complement (a fortiori null). This is the index-completeness the finite-cover glue
(`lintegral_lt_top_of_finset_cover`) needs (recon §A, §4 gap 3 — Lean labor over banked math, DONE), now
re-established for the JOINT-dominating full-tail rank index (action #1).

**Coverage note (W4 E5, adjudicated COVER):** the strata here are keyed on `rank Q` (per-`A'`). Which
CUTS `t` route to this engine is the separate W4 COVER question — operative because
`sjBoundaryPeel + ENNReal.sum_lt_top` demands EVERY cut finite (not a chosen path): every `d≥2` cut
transcribes, `n≥4` each carry binding `d≥2` atoms, `n=3` is the largest fully-native square. Orthogonal
to this per-`A'` rank cover, which is total for any single cut. -/
theorem tailRankStrata_cover (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ) (κ : Fin t ↪ Fin (M 1)) :
    volume ((paramsBoxM (tailChain M) 1) \
      ⋃ i ∈ (Finset.univ : Finset (Fin (t + (M 1 - t) + 1))), tailRankStratum M t κ (i : ℕ)) = 0 := by
  have hsub : (paramsBoxM (tailChain M) 1) ⊆
      ⋃ i ∈ (Finset.univ : Finset (Fin (t + (M 1 - t) + 1))), tailRankStratum M t κ (i : ℕ) := by
    intro A' _
    have hle : tailProductRank M t κ A' ≤ t + (M 1 - t) := by
      have := Matrix.rank_le_card_height
        ((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id)
      simpa [tailProductRank, Fintype.card_sum, Fintype.card_fin] using this
    refine Set.mem_iUnion₂.mpr ⟨⟨tailProductRank M t κ A', ?_⟩, Finset.mem_univ _, rfl⟩
    omega
  rw [Set.diff_eq_empty.mpr hsub]
  exact measure_empty

/-! ## §H heart (FILLED, imported) — the c×c Morse corank family -/

-- `corankSVD_chartFamily_lt_top {a b q} (hab : 2 ≤ min a b) (S) (c') (hthr : 2c' < a·rank S)
--   (box) (hbox : Bornology.IsBounded box) : ∫⁻ Γ in box, ofReal((frobSq (Γ·S))^(-c')) < ⊤`
-- is PROVEN sorry-free (clean-three) in `DLNFibre.DLN.RLCT.Validate.RouteMSJCorankMorse` (merged from
-- `genm-l2morse`), imported above. With `S` FIXED it is a MORSE (smooth-linear-center) singularity —
-- a PSD quadratic form of rank `a·rank(S)`, resolved by one spectral CoV (unit Jacobian) + one
-- `corner_block_cube_lintegral_lt_top` on the `a·rank(S)` active block (l2svd cert §§1–4). NOT a
-- determinantal blow-up; the "d=c / single-radial-DEAD / sign-repair" language belongs to the JOINT
-- (varying-S) problem = `corankStratum_lt_top`'s obligation 2. The `corankStratum` descent consumes it
-- directly (same fully-qualified name). SCOPE (l2svd §7): fixed-S INNER finiteness only — it does NOT
-- carry a uniform-across-strata quantitative bound `inner ≤ C(S)` with `C(S)` outer-integrable; that
-- stronger form is obligation 2 (`nonsubmersive_Ar_principalization`), the GAP.

/-! ## ★ THE ISOLATED WALL — obligation 2 (the non-submersive `A_r` principalization) -/

/-- **★ OBLIGATION 2 — THE WALL (isolated, the minimal remaining gap; native-vs-cite = LATE-102).**
The outer integrability of the **pivot change-of-variables Jacobian** `|det Ψ(Q_b(A'))|^{−t} =
det(Q_b(A')·Q_b(A')ᵀ)^{−t/2}` (`Ψ` = the invertible part of `Q_b`'s right-singular frame; `Q_b(A')` = the
corank block `Sum.inr` of the shared tail product) against the rank-drop boundary `{A' : rank Q_b(A') < b}`.
This is the ONE genuinely-OPEN gap of the native engine; everything above it (the Morse corank family
`corankSVD_chartFamily_lt_top`, the top-stratum pivot-Gram disposal, the region glue, the descent
arithmetic) is EXPENSIVE-TRANSCRIPTION.

**Why it is a WALL, not transcription (l2svd cert §9, prodcorank-cert, decstep round-5 —
`GAP-IN-RELATIVE-JACOBIAN`).** `det(Q_b·Q_bᵀ)^{−t/2}` here is a CoV JACOBIAN weight (from freeing the
pivot tail for `qbox`), NOT a carried corank-Gram integrand (that would be the atom trap). For a FREE
`Q_b` the outer integral is finite iff `t < q − b + 1` (standard, submersive; per-rank codim `(b−r)(q−r)`,
vanishing order `(b−r)`, threshold `q−r`, min `q−b+1`). But `Q_b(A')` is a **shared DEEPER PRODUCT**
(nested DLN factors), and the product map is **NON-SUBMERSIVE** at the rank-drop locus: the pullback
acquires factor divisors the free-matrix count never sees. Concretely (Codex, decisive) for `Q_b = L·R`
(`L` free `b×b`, `R` free `b×q`), `|det Ψ(Q_b)| = |det L|·|det Ψ(R)|`, so integrability requires
SIMULTANEOUSLY `t < 1` (the extra divisor `{det L = 0}`, codim 1, linear vanishing) AND `t < q−b+1` —
threshold `t < 1`, STRICTLY worse than the free baseline when `q > b`. The transverse Jacobian `= A_r`
STRUCTURE transcribes (Aoyagi Case-2 carries the codim exponent), but its EXACT VALIDITY — that blowing
up `{rank Q_b(A')=r}` through the product parametrization principalizes with ALL exponents `> −1` and NO
smaller-ratio divisor — is genuinely ABSENT from Aoyagi's worked EXACT results (his general Theorem 5
gives only UPPER bounds; exact values only `N=1`/small `H`; the finiteness `rlct ≥ c*` direction is his
stated future work). **Circularity guard:** one cannot use "rlct = c* (Aoyagi) ⟹ no smaller-ratio
divisor" inside a native proof.

**Reconciliation with the airtight arithmetic.** satred's `A_r = (b−r)²` (`= peelCharge(M, deepened cut)`;
round-5 care-point — the invariant is `(corank at the deepened cut)²`, carried as a kill-condition) and
`min_r[A_r + minAdm(reducedᵣ)] = minAdm(M)` (verified `(4,4,4,4)@t=2 A_r=[0,1,4]→11`, n=3..15) are the
airtight BUDGET; l2witness cross-checks the ratios `min_i (a_i+1)/(2Nᵢ) ≥ c*`. But a green ratio-check
certifies `rlct ≥ c*` CONDITIONAL on the `(aᵢ,Nᵢ)` coming from a VALID resolution — it does NOT certify
that validity (the non-submersive principalization), which is exactly this hole.

**Status: OPEN — THE WALL.** ESCALATED to the operator (LATE-102 native-vs-cite): build the multi-tide
non-submersive product-corank resolution, or consolidate at the cite (`cited_aoyagi_product_corank` as a
carried box-level Prop, one level below `cited_aoyagi_dln`). satred owns the `A_r` arithmetic, l2witness
the ratios; the non-submersive transverse-Jac VALIDITY is the operator decision. -/
theorem nonsubmersive_Ar_principalization (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ)
    (ht2 : t ≤ min (M 0) (M 1)) (κ : Fin t ↪ Fin (M 1)) (c' : NNReal)
    (hc' : (c' : ℝ) < (minAdm M : ℝ) / 2)
    (hIH : ∀ M' : Fin (L + 1 + 1) → ℕ, RouteMBoxThresholdFinite M') :
    (∫⁻ A' in paramsBoxM (tailChain M) 1,
        ENNReal.ofReal
          (((((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id).submatrix Sum.inr id) *
              (((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id).submatrix Sum.inr id).transpose).det
            ^ (-(t : ℝ) / 2))) < ⊤ := by
  sorry

/-! ## Analytic hole — the per-stratum outer-measure descent (the whole §H at measure level) -/

/-- **THE PER-STRATUM DESCENT (hole) + THE MEASURE-REDUCTION DESIGN NOTE.** For a min-corank≥2 cut `t`
below threshold, GIVEN the one-shorter PLAIN IH `hIH`, the freed-Γ triple integral RESTRICTED to the
full-pivot-tail rank-`k` stratum `tailRankStratum M t κ k` is finite. This is the outer `(S,J)`
measure-level descent — where the genuinely-new content lives (the inner Γ-integral is finite POINTWISE
by `freedSchurLoss_inner_bounded_lt_top`; the difficulty is the OUTER integrability against the
`x → pivot-rank-drop` / `A' → tail-rank-drop` singularities).

## Measure-reduction design note (the traced gammaAtom chain, all 4 caveats)

The chain, per stratum: **(step 2)** integrate the coupling `C = x.2` via `gammaAtom_aniso_shifted_eq`
with `R := Q̃ₚ` (`t×q`), `S := Γ·Q_b`, `w := frobSq(P·Q̃ₚ)` → `det(Q̃ₚ·Q̃ₚᵀ)^{−a/2}·Cresid·(w +
frobSq(Γ·Q_b·Π))^{−(c'−a·t/2)}`, `Π = 1 − Q̃ₚᵀ(Q̃ₚQ̃ₚᵀ)⁻¹Q̃ₚ`. The `det(Q̃ₚQ̃ₚᵀ)^{−a/2}` (constant in `Γ`)
is the **PIVOT Gram** (NEVER the corank Gram — atom trap); the residual chains into
`corankSVD_chartFamily_lt_top` with `S := Q_b·Π` (the unbuffered SVD hole DOMINATES the `w>0`-buffered
residual, `w>0 ⟹ (w+f)^{−d} ≤ f^{−d}`, so its finiteness suffices). The FOUR caveats the fill discharges:

1. **Box ≤ full-space (TRANSCRIPTION).** `gammaAtom` is a full-`ℝ^{a×t}` identity; the `C`-domain here is
   the `outerDom` box. Resolve by monotonicity (box ⊆ full-space, nonneg integrand) → UPPER BOUND (suffices
   for `< ⊤`); Fubini (banked S1Fubini) isolates `∫_C`.
2. **JOINT rank index — ADOPTED (action #1).** gammaAtom's `hG : (Q̃ₚQ̃ₚᵀ).PosDef` ⟺ `rank Q̃ₚ = t` holds
   only a.e.; the degenerate locus is not seen by `rank Q_b` alone. Re-indexed on `rank Q` (`tailProductRank`,
   dominating both `rank Q̃ₚ, rank Q_b`): on the TOP stratum `k = t+(M₁−t)`, `hG` holds a.e.-`x` (gammaAtom
   applies); deeper `k` route to the SVD family / the bounded branch on the pivot-degenerate locus.
3. **`a·t/2` threshold dispatch (TRANSCRIPTION).** gammaAtom needs `c' > a·t/2`; below it, use
   `freedSchurLoss_inner_bounded_lt_top` (pivot energy `>0`, box finite) directly. Per-cut `by_cases`.
4. **Pivot-Gram disposal is NOT literal qbox (ROUTED to l2svd, action #2).** `qbox_lintegral_lt_top`
   disposes a FREE-matrix Gram over a ball; `Q̃ₚ = Q_p + P⁻¹B₁₂Q_b` is NOT free — needs a `(P,B₁₂) → Q̃ₚ`
   CoV (Jacobian bookkeeping) before qbox fires. And qbox's gate `a < q−t+1` is TOP-stratum only; deeper
   strata are marginal/fail → the transverse-Jacobian `A_r = (b−r)²` repair (decstep round-4 KILL-guard 4).
   These are the pivot-tail ANALOGUES of l2svd's corank-tail SVD family (shared `measurableEigendecomp`
   substrate + `A_r` budget; satred derives `A_r`, l2witness checks ratios).

**Kill-conditions:** carry PIVOT not corank Gram; `Γ·Q_b` STRATIFIED not integrated free (overshoot);
`|det J|` always carried; the pivot-Gram gate is TOP-STRATUM only.

**§9 BOUNDARY-BLOW-UP CORRECTION (l2svd cert — the decomposition is a blow-up, NOT a null-partition).**
The rank-`Q` strata `tailRankStratum M t κ k` are a NULL-partition: for `k <` the generic rank,
`{rank Q = k}` is a determinantal subvariety of `A'`-space, Lebesgue-NULL, so `∫` over it `= 0` trivially
— the finite-cover glue proves finiteness there only where it was never in doubt. The genuine content is
the TOP (generic-rank) stratum's OUTER integrability against the null rank-drop BOUNDARY, resolved by a
rank-boundary BLOW-UP (positive-codim exceptional divisors carrying the `A_r` weights), NOT a partition
into null exact-rank pieces. That blow-up's transverse-Jacobian `= A_r` VALIDITY for the non-submersive
shared product `Q_b(A')` is `nonsubmersive_Ar_principalization` (obligation 2, THE isolated wall).

**Reduction (the hypothesis list).** `corankStratum_lt_top` REDUCES to: (i) `corankSVD_chartFamily_lt_top`
(the Morse corank family, l2morse → `genm-l2morse`, TRANSCRIPTION); (ii) the top-stratum pivot-Gram
disposal (obligation 1, TRANSCRIPTION — the `(P,B₁₂)→free-Wishart` CoV + `qbox`, cert §8); (iii)
`nonsubmersive_Ar_principalization` (obligation 2, the ONE genuinely-open WALL). **Status: OPEN**, its
sole non-transcription dependency being obligation 2. -/
theorem corankStratum_lt_top (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ)
    (ht : 1 ≤ t) (ht2 : t ≤ min (M 0) (M 1)) (hcork : 2 ≤ min (M 0 - t) (M 1 - t))
    (κ : Fin t ↪ Fin (M 1)) (c' : NNReal) (hc' : (c' : ℝ) < (minAdm M : ℝ) / 2)
    (hIH : ∀ M' : Fin (L + 1 + 1) → ℕ, RouteMBoxThresholdFinite M') (k : ℕ) :
    (∫⁻ A' in tailRankStratum M t κ k,
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
    (Finset.univ : Finset (Fin (t + (M 1 - t) + 1)))
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
