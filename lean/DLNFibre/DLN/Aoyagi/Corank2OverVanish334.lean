import DLNFibre.DLN.Aoyagi.Corank2NativeJac334
import DLNFibre.DLN.Aoyagi.Corank2NativeEntry334
import DLNFibre.DLN.Aoyagi.Corank2FanCover334
import DLNFibre.Core.Aoyagi.MonomialSumSqRLCT

/-!
# `DLN.Aoyagi.Corank2OverVanish334` — the over-vanishing (3,3,4) value side (DLN concrete pieces)

The over-vanishing-144 seat's DLN concrete deliverables (3)–(5), built against the LOCKED Core value
engine `Core.Aoyagi.monoSumSq_integrableAtFilter_of_lt` (the Tonelli crux is a separate seat's).

The over-vanishing leaves carry NO single-entry survivor (the clean-144 `hentry` is dead); the loss
pulls back to a monomial-squared times a nondegenerate sum-of-squares in a `jac`-free coordinate
block:

`loss ∘ (gFin c ∘ Ψ_c)(u) ≥ vm(u)² · ∑_{j ∈ Z_c} u_j²`

via (3) the pullback `loss ∘ gFin c = vm²·∑_k vf_k²`, (4) the regular-sequence `subset_le_sum` (drop
the 4 non-regular `vf`, keep the 8) + the native unipotent change-of-variables `Ψ` that straightens
those 8 `vf` to coordinates `z_j`, and — per the elder's fold-`Ψ`-into-the-chart design — `Ψ` enters
as a `blockShear` folded into the chart `g' = gFin c ∘ Ψ`, so the fan cover transports verbatim.

## §0 — the cover-transport atom (piece 5): `Ψ` folded into the chart preserves the cover

Since `Ψ = blockShear φ` is a homeomorphism of `ℝ²¹` inflating a `0`-ball by `r ↦ r + C·r²`
(`Corank2FanCover334.blockShear_covers_scaled`), each leaf's original image `gFin c '' domFin c`
sits inside the folded chart's image over the enlarged domain — so the whole-conjugate cover
(`native_hcover`) survives replacing `gFin c` by `gFin c ∘ Ψ` on the over-vanishing leaves.
-/

open MeasureTheory Set Metric Filter Topology RLCT
open DLNFibre.Core.Aoyagi
open DLNFibre.DLN.Aoyagi.NativeFan334
open DLNFibre.DLN.Aoyagi.Corank2CoreGenWrap
open DLNFibre.DLN.Aoyagi.NativeEntry334

namespace DLNFibre.DLN.Aoyagi.OverVanish334

/-- **The cover-transport atom (piece 5).** For any chart `g` and any `blockShear φ` with keep-set
`keep` (`hkeep`/`hread`) whose displacement is quadratically bounded on the `r`-ball
(`‖φ x‖ ≤ C·r²`), the original image `g '' closedBall 0 r` sits inside the folded chart's image
`(g ∘ blockShear φ) '' closedBall 0 (r + C·r²)`. So folding `Ψ = blockShear φ` into a chart
preserves any `0`-ball cover (at the cost of the `r ↦ r + C·r²` domain inflation), the elder's
fold-`Ψ`-into-the-chart route. Generic over `D`; the over-vanishing leaves apply it at `D = 21`,
`g = gFin c`, `r = leafR`. -/
theorem image_comp_blockShear_superset {D : ℕ}
    (g : (Fin D → ℝ) → (Fin D → ℝ)) {r : ℝ}
    {φ : (Fin D → ℝ) → (Fin D → ℝ)} (keep : Fin D → Prop)
    (hkeep : ∀ u i, keep i → φ u i = 0)
    (hread : ∀ u v : Fin D → ℝ, (∀ i, keep i → u i = v i) → φ u = φ v)
    {C : ℝ} (hquad : ∀ x : Fin D → ℝ, ‖x‖ ≤ r → ‖φ x‖ ≤ C * r ^ 2) :
    g '' closedBall 0 r ⊆ (g ∘ blockShear φ) '' closedBall 0 (r + C * r ^ 2) := by
  have hbox := Corank2FanCover334.blockShear_covers_scaled keep hkeep hread hquad
  calc g '' closedBall (0 : Fin D → ℝ) r
      ⊆ g '' (blockShear φ '' closedBall 0 (r + C * r ^ 2)) := Set.image_mono hbox
    _ = (g ∘ blockShear φ) '' closedBall 0 (r + C * r ^ 2) :=
        (Set.image_comp g (blockShear φ) _).symm

/-! ## §1 — the per-chart integrability bridge (Core engine → the V-lower wire)

The per-chart obligation the (over-vanishing) V-lower wire consumes: at a base point `p`, the
weighted pulled-back loss `|jacDet g'| · (∑ (Fᵢ ∘ g')²)^{-cc}` is integrable near `p`. For the
over-vanishing charts this rides the Core product engine, NOT the chain engine: the loss dominates
the product germ `vm²·∑_Z z²` (`hdom`, from the pullback + regular-sequence `Ψ`-straightening), so
the Core engine's integrability of `W · (vm²·∑_Z z²)^{-cc}` transfers to the loss by the
junk-guarded domination `wLocalAdmissibleExponents_subset_of_eventually_le` (using
`locallyNullZeros_monoSumSqGerm`). Generic over `F` / `g'`; the over-vanishing seat feeds
`F = coreGen`, `g' = gFin c ∘ Ψ_c`, `W = jacWeight (jacFin c)`. The over-vanishing analogue of
`integrableAtFilter_of_sandwich`.
-/

/-- **Per-chart integrability from the product-germ domination** (the over-vanishing analogue of
`integrableAtFilter_of_sandwich`). If the weight is the monomial Jacobian weight
(`|jacDet g'| = jacWeight jac`), `cc` is below both the monomial threshold of `vm` and the
sum-of-squares threshold `|Z|/2`, the regular-sequence block `Z` is disjoint from `supp(vm)` and
`jac`-free there, and the pulled-back loss `∑ (Fᵢ ∘ g')²` dominates the product germ `vm²·∑_Z z²`
near `p` (`hdom`), then the weighted pulled-back loss is integrable near `p`. Consumes the LOCKED
Core engine `monoSumSq_integrableAtFilter_of_lt` (its Tonelli hole propagates; tracked-open). -/
theorem chart_integrableAtFilter_of_monoSumSq_dom {D Mn : ℕ}
    {F : Fin Mn → (Fin D → ℝ) → ℝ} {g' : (Fin D → ℝ) → (Fin D → ℝ)}
    {a jac : Fin D → ℕ} {Z : Finset (Fin D)} {p : Fin D → ℝ} {cc : ℝ}
    (hbind : (bindingAxes a).Nonempty) (hZne : Z.Nonempty)
    (hZa : ∀ j ∈ Z, a j = 0) (hZjac : ∀ j ∈ Z, jac j = 0)
    (hc0 : 0 ≤ cc)
    (hthr : cc < monomialThreshold a jac hbind) (hsos : 2 * cc < (Z.card : ℝ))
    (hFmeas : ∀ i, Measurable (F i)) (hg'meas : Measurable g')
    (hW : ∀ u, |jacDet g' u| = jacWeight jac u)
    (hdom : ∀ᶠ u in 𝓝 p, monoSumSqGerm a Z u ≤ sumSqFam (fun i ↦ F i ∘ g') u) :
    IntegrableAtFilter
      (fun u ↦ |jacDet g' u| * negPow (sumSqFam (fun i ↦ F i ∘ g')) cc u) (𝓝 p) := by
  -- the weight is measurable (`fderiv` is measurable everywhere; `det`, `abs` continuous).
  have hWmeas : Measurable (fun u ↦ |jacDet g' u|) := by
    have h1 : Measurable (fun u ↦ (fderiv ℝ g' u).det) :=
      ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℝ g')
    exact h1.abs
  -- the pulled-back loss is measurable (a finite sum of squares of `Fᵢ ∘ g'`).
  have hLmeas : Measurable (sumSqFam (fun i ↦ F i ∘ g')) := by
    unfold sumSqFam
    exact Finset.measurable_sum _ (fun i _ ↦ ((hFmeas i).comp hg'meas).pow_const 2)
  -- Core product engine: `W · (vm²·∑_Z z²)^{-cc}` is integrable near `p`.
  have hP : IntegrableAtFilter
      (fun u ↦ |jacDet g' u| * negPow (monoSumSqGerm a Z) cc u) (𝓝 p) := by
    refine monoSumSq_integrableAtFilter_of_lt (W := fun u ↦ |jacDet g' u|) hbind hZne hZa hZjac hc0
      hthr hsos (unit := fun _ ↦ 1) continuousAt_const one_ne_zero measurable_const ?_
    filter_upwards with u
    simp only [hW u, mul_one]
  have hmem : cc ∈ wLocalAdmissibleExponents (fun u ↦ |jacDet g' u|) (monoSumSqGerm a Z) p :=
    ⟨hc0, hP⟩
  have hnull := locallyNullZeros_monoSumSqGerm a hZne p
  have hWnn : ∀ᶠ u in 𝓝 p, 0 ≤ |jacDet g' u| := Filter.Eventually.of_forall (fun u ↦ abs_nonneg _)
  have hbound : ∀ᶠ u in 𝓝 p, 0 ≤ monoSumSqGerm a Z u ∧
      monoSumSqGerm a Z u ≤ sumSqFam (fun i ↦ F i ∘ g') u :=
    hdom.mono (fun u h ↦ ⟨monoSumSqGerm_nonneg a Z u, h⟩)
  have hsub := wLocalAdmissibleExponents_subset_of_eventually_le hWmeas hLmeas hWnn hbound hnull
  exact (hsub hmem).2

/-! ## §2 — the regular-sequence domination (piece 4) and the `Ψ`-folded weight

The two generic facts that instantiate the bridge's `hdom` and `hW` from the per-type pnp data:
- `monoSumSqGerm_le_sumSqFam_comp` — from the pullback `loss ∘ g = vm²·∑_k vf_k²`, the `Ψ`-fixing of
  `vm`, and the `Ψ`-straightening of the 8 regular-sequence `vf` to the `Z`-coordinates, the loss of
  the FOLDED chart `g ∘ Ψ` dominates the product germ `vm²·∑_Z z²` (drop the non-regular squares,
  reindex the straightened block). This is piece (4): `subset_le_sum` + the `Ψ` change-of-variables.
- `jacWeight_fixOn` — `Ψ` fixing every binding axis of `h` leaves `jacWeight h` invariant (the
  non-binding axes contribute `|·|^0 = 1` either way). Feeds the folded weight
  `|jacDet (g ∘ Ψ)| = jacWeight jac` (via `jacDet_comp` + `|jacDet Ψ| = 1` + this).
-/

/-- **The regular-sequence domination (piece 4).** Given the pullback
`∑ (Fᵢ ∘ g)² = (∏ v_d^{vmExp d})² · ∑_k (vf_k)²`, the `Ψ`-invariance of the monomial `vm`
(`hvmfix`), and the `Ψ`-straightening `vf_k ∘ Ψ = z_{zc k}` of the regular-sequence indices `k ∈ S`
onto the coordinate block `Z = zc '' S` (`hstr`, `hzc_inj`, `hzc_img`), the loss of the folded chart
`g ∘ Ψ` dominates the product germ `monoSumSqGerm vmExp Z`. Drop the non-regular squares
(`sum_le_sum_of_subset`), reindex the straightened regular block onto `Z` (`sum_image`). -/
theorem monoSumSqGerm_le_sumSqFam_comp {D Mn : ℕ}
    {F : Fin Mn → (Fin D → ℝ) → ℝ} {g Ψ : (Fin D → ℝ) → (Fin D → ℝ)}
    {vf : Fin Mn → (Fin D → ℝ) → ℝ} {vmExp : Fin D → ℕ} {S : Finset (Fin Mn)} {Z : Finset (Fin D)}
    {zc : Fin Mn → Fin D}
    (hpull : ∀ v, sumSqFam (fun i ↦ F i ∘ g) v
        = (∏ d, (v d) ^ (vmExp d)) ^ 2 * ∑ k, (vf k v) ^ 2)
    (hvmfix : ∀ u, (∏ d, (Ψ u d) ^ (vmExp d)) = (∏ d, (u d) ^ (vmExp d)))
    (hstr : ∀ u, ∀ k ∈ S, vf k (Ψ u) = u (zc k))
    (hzc_inj : ∀ x ∈ S, ∀ y ∈ S, zc x = zc y → x = y) (hzc_img : S.image zc = Z)
    (u : Fin D → ℝ) :
    monoSumSqGerm vmExp Z u ≤ sumSqFam (fun i ↦ F i ∘ (g ∘ Ψ)) u := by
  have h1 : sumSqFam (fun i ↦ F i ∘ (g ∘ Ψ)) u = sumSqFam (fun i ↦ F i ∘ g) (Ψ u) := by
    simp only [sumSqFam, Function.comp_apply]
  rw [h1, hpull (Ψ u), hvmfix u]
  unfold monoSumSqGerm
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  calc ∑ j ∈ Z, (u j) ^ 2
      = ∑ k ∈ S, (u (zc k)) ^ 2 := by rw [← hzc_img, Finset.sum_image hzc_inj]
    _ = ∑ k ∈ S, (vf k (Ψ u)) ^ 2 := Finset.sum_congr rfl (fun k hk ↦ by rw [hstr u k hk])
    _ ≤ ∑ k, (vf k (Ψ u)) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun k _ _ ↦ sq_nonneg _)

/-- **`jacWeight` is invariant under a map fixing every binding axis.** If `Ψ u d = u d` at every
`d` with `h d > 0`, then `jacWeight h (Ψ u) = jacWeight h u` (the non-binding axes contribute
`|·|^0 = 1` regardless). Feeds the `Ψ`-folded chart weight: the over-vanishing `Ψ` keeps `supp(vm)`,
which is exactly `supp(jacFin c)`, so folding `Ψ` leaves `jacWeight (jacFin c)` unchanged. -/
theorem jacWeight_fixOn {D : ℕ} (h : Fin D → ℕ) {Ψ : (Fin D → ℝ) → (Fin D → ℝ)} {u : Fin D → ℝ}
    (hfix : ∀ d, 0 < h d → Ψ u d = u d) :
    jacWeight h (Ψ u) = jacWeight h u := by
  unfold jacWeight
  refine Finset.prod_congr rfl (fun d _ ↦ ?_)
  rcases Nat.eq_zero_or_pos (h d) with h0 | hpos
  · rw [h0, pow_zero, pow_zero]
  · rw [hfix d hpos]

/-! ## §3 — the uniform `u_{p1}` factor-out of the pullback (piece 3, reusable step)

The first, uniform `vm` factor of the pullback: `u_{p1}` factors out of every one of the 12
`coreGen` entries (from `A0_gFlat_factor` + `A1_gFlat_spectator` + `Matrix.mul_smul`), so the whole
loss carries `u_{p1}²`. The FURTHER per-type factors (`u_{p2}` / `u_{p3}` from the inner blow-ups
inside `gInner`) plus the identification of the 12 residual factors `vf_k` are the per-type work
that completes (3); this §3 is the reusable step shared by all 16 canonical types.
-/

/-- **The uniform `u_{p1}` factor of a `coreGen` entry.** `coreGen k (gFlat idx w) = u_{p1}·resid`,
where `resid = (A1 (gInner idx w) · A0'')_k` and `A0'' = A0 (update (gInner idx w) p1 1)`. From
`mult_eWrap` (`coreGen k v = (A1 v · A0 v)_k`) + `A1_gFlat_spectator` + `A0_gFlat_factor` +
`Matrix.mul_smul` (the scalar `u_{p1}` pulls out of the product). -/
theorem coreGen_gFlat_factor (idx : Idx) (w : Fin 21 → ℝ)
    (k : Fin (dvec (Fin.last 2) * dvec 0)) :
    coreGen dvec eWrap k (gFlat idx w)
      = w idx.1.1 *
        (A1 (gInner idx w) * A0 (Function.update (gInner idx w) idx.1.1 1))
          (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 := by
  have h1 : coreGen dvec eWrap k (gFlat idx w)
      = (A1 (gFlat idx w) * A0 (gFlat idx w))
          (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 := by
    simp only [coreGen]
    exact congrFun (congrFun (mult_eWrap (gFlat idx w)) _) _
  rw [h1, A1_gFlat_spectator, A0_gFlat_factor, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]

end DLNFibre.DLN.Aoyagi.OverVanish334
