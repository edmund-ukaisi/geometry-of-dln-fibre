import DLNFibre.DLN.RLCT.Validate.DeepestMinRlct
import DLNFibre.DLN.RLCT.Validate.LossHomogeneity
import DLNFibre.DLN.RLCT.Validate.DeepestFrontGauge
import DLNFibre.DLN.RLCT.Validate.R1ResolutionInterfaceL2
import DLNFibre.DLN.RLCT.Foundations.S1NodeFlatHomog
import DLNFibre.DLN.RLCT.Foundations.ParamsFlatLinear

/-!
# `DLNFibre.DLN.RLCT.Validate.D1L2ExplicitCoreProducer` — the D1 `≥`-leg via the EXPLICIT core

The corrected D1 `≥`-leg architecture (`genm-d1l2close2` statement card): retire the two-IFT-peel
producer (whose second peel routes through the germ-discarding existence-only IFT inverse `Ψsymm`,
discarding the higher-order germ that pins the RLCT value) and route through the **EXPLICIT
homogeneous core** `dlnLoss (H − r) 0`. Two banked pieces reduce the whole leg to ONE producer:

* `deepest_le_of_optimal_via_L2_ge` (`DeepestMinRlct`, PROVEN) — the abstract bridge.
* `deepest_le_of_homogeneous_core` (`DeepestMinRlct`, PROVEN, hypothesis-free: measurable +
  degree-`D` homogeneous ⟹ `rlctAtOn F 0 ≤ rlctAtOn F v`) — Aoyagi Theorem 4.

The **new correction** this module lands: `hCore : coreDeepest ≤ coreV` is discharged by the
homogeneity comparison on the SAME explicit core `dlnLoss (H − r) 0` at two points (`0` and
`corePoint_v`), NOT by the blocked residual-value identity through the abstract IFT residual. Because
the core is the explicit polynomial, its homogeneity is accessible: `dlnLoss M 0` is degree-`2L`
homogeneous (scaling all layers), transported to the flat coordinates for `deepest_le_of_homogeneous_core`.

## What this module delivers

* `dlnLoss_zero_smul` — the full (all-layer) homogeneity: `dlnLoss M 0 (c • A) = c ^ (2·L) · dlnLoss M 0 A`.
* `flatNodeLoss_smul` — its flat shadow, feeding `deepest_le_of_homogeneous_core`.
* `core_zero_le_of_params` — the **Params-domain** Aoyagi Theorem 4 (the previously-blocked `hCore`):
  `rlctAtOn (dlnLoss M 0) 0 ≤ rlctAtOn (dlnLoss M 0) P` for every reduced-core point `P`.
* `d1ge_L2_hAtV_explicit` — the SOLE remaining open obligation, the crux: the Aoyagi Step-1 explicit
  iterated corner-elimination block reduction landing `rlctAt v` on the explicit core at an explicit
  reduced-core point.
* `d1ge_L2_deepestPoint_via_explicit_core` — the `HeadlineL2Assembly.hD1ge_L2` drop-in: assembles the
  three pieces (deepest value #44 + R1 ; `core_zero_le_of_params` ; `d1ge_L2_hAtV_explicit`) via the
  banked bridge.
-/

open MeasureTheory
open scoped ENNReal Topology BigOperators
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## Full (all-layer) homogeneity of the deepest core `dlnLoss M 0` -/

/-- The `prodAux` recursion-step with the dependent-`Fin` cast discharged by HEq (local copy of the
`LossHomogeneity` private helper). -/
private theorem prodAux_step' (H : Fin (L + 1) → ℕ) (A : Params H) (k : ℕ) (hk : k + 1 < L + 1)
    (Mstep : Matrix (Fin (H ⟨k, Nat.lt_of_succ_lt hk⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ)
    (hheq : HEq (A ⟨k, Nat.lt_of_succ_lt_succ hk⟩) Mstep) :
    prodAux H A (k + 1) hk = prodAux H A k (Nat.lt_of_succ_lt hk) * Mstep := by
  rw [prodAux]; congr 1; rw [eq_comm]; apply eq_of_heq
  exact hheq.symm.trans (heq_of_eqRec_eq rfl rfl)

/-- **The prefix product scales by `c ^ k` under an all-layer scaling.** `prodAux (c • A) k = c ^ k •
prodAux A k`: each of the first `k` layers contributes one factor of `c`. Induction on `k`; the
successor step pulls one `c` out of the current layer (`Matrix.mul_smul`) and folds it into the
prefix power. -/
theorem prodAux_smul_pow (H : Fin (L + 1) → ℕ) (c : ℝ) (A : Params H) :
    ∀ (k : ℕ) (hk : k < L + 1),
      prodAux H (c • A) k hk = c ^ k • prodAux H A k hk := by
  intro k
  induction k with
  | zero => intro hk; simp only [prodAux, pow_zero, one_smul]
  | succ k ih =>
      intro hk
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      -- clean transported step matrix for the UNSCALED tuple (sidesteps the prodAux Eq.mpr cast).
      let Mstep : Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ := by
        have e1 : (⟨k, hk'⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).castSucc := by
          apply Fin.ext; simp [Fin.castSucc]
        have e2 : (⟨k + 1, hk⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).succ := by
          apply Fin.ext; simp [Fin.succ]
        rw [e1, e2]; exact A ⟨k, hkL⟩
      have hM : HEq (A ⟨k, hkL⟩) Mstep := by dsimp only [Mstep]; exact heq_of_eqRec_eq rfl rfl
      -- the scaled tuple's layer `k` is `c • A ⟨k,hkL⟩` (Pi smul), HEq to `c • Mstep`.
      have hMs : HEq ((c • A) ⟨k, hkL⟩) (c • Mstep) := by
        have h1 : (c • A) ⟨k, hkL⟩ = c • A ⟨k, hkL⟩ := rfl
        rw [h1]; cases hM; rfl
      rw [prodAux_step' H (c • A) k hk (c • Mstep) hMs,
          prodAux_step' H A k hk Mstep hM, ih hk',
          Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_succ]

/-- **`prod` scales by `c ^ L` under an all-layer scaling** (`prod (c • A) = c ^ L • prod A`).
Specialises `prodAux_smul_pow` at `k = L`. -/
theorem prod_smul_pow (H : Fin (L + 1) → ℕ) (c : ℝ) (A : Params H) :
    prod H (c • A) = c ^ L • prod H A := by
  rw [prod, prod]; exact prodAux_smul_pow H c A L (Nat.lt_succ_self L)

/-- **The deepest core `dlnLoss M 0` is degree-`2L` homogeneous** (all-layer scaling). From
`prod_smul_pow` (the product scales by `c ^ L`) + the sum-of-squares (each square by `(c ^ L) ^ 2 =
c ^ (2L)`). This is the `hhomog` input Aoyagi Theorem 4 (`deepest_le_of_homogeneous_core`) needs. -/
theorem dlnLoss_zero_smul (H : Fin (L + 1) → ℕ) (c : ℝ) (A : Params H) :
    dlnLoss H 0 (c • A) = c ^ (2 * L) * dlnLoss H 0 A := by
  unfold dlnLoss
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hp : prod H (c • A) = c ^ L • prod H A := prod_smul_pow H c A
  simp only [Matrix.sub_apply, Matrix.zero_apply, sub_zero, hp, Matrix.smul_apply, smul_eq_mul]
  rw [mul_pow, ← pow_mul, Nat.mul_comm L 2]

/-! ## The flat shadow + measurability -/

/-- The measurable-equiv inverse `(paramsEquivFlat M).symm` agrees with the linear-equiv inverse
`(paramsEquivFlatLinear M).symm` (both invert the same forward function). -/
theorem paramsEquivFlat_symm_eq_linear (M : Fin (L + 1) → ℕ) (y : Fin (flatDim M) → ℝ) :
    (paramsEquivFlat M).symm y = (paramsEquivFlatLinear M).symm y := by
  apply (paramsEquivFlat M).injective
  rw [(paramsEquivFlat M).apply_symm_apply, ← paramsEquivFlatLinear_coe,
    (paramsEquivFlatLinear M).apply_symm_apply]

/-- **The flat node loss is degree-`2L` homogeneous** (all-coordinate scaling): `flatNodeLoss M (c • x)
= c ^ (2L) · flatNodeLoss M x`. The flat `symm` is linear, so all-coordinate scaling pulls back to an
all-layer scaling of the matrices, where `dlnLoss_zero_smul` applies. -/
theorem flatNodeLoss_smul (M : Fin (L + 1) → ℕ) (c : ℝ) (x : Fin (flatDim M) → ℝ) :
    flatNodeLoss M (c • x) = c ^ (2 * L) * flatNodeLoss M x := by
  unfold flatNodeLoss
  rw [paramsEquivFlat_symm_eq_linear, map_smul, ← paramsEquivFlat_symm_eq_linear,
    dlnLoss_zero_smul]

/-- `flatNodeLoss M` is measurable (a polynomial `dlnLoss` composed with the continuous flat inverse). -/
theorem measurable_flatNodeLoss (M : Fin (L + 1) → ℕ) : Measurable (flatNodeLoss M) :=
  (measurable_dlnLoss M 0).comp (paramsEquivFlat M).symm.measurable

/-! ## The Params-domain Aoyagi Theorem 4 (the previously-blocked `hCore`) -/

/-- **The reduced-core RLCT transports to the flat shadow.** For every `P : Params M`,
`rlctAtOn (dlnLoss M 0) P = rlctAtOn (flatNodeLoss M) (paramsEquivFlat M P)`, via the
measure-preserving homeomorphism `paramsEquivFlat` (`rlctAtOn_comp_homeomorph`). -/
theorem rlctAtOn_dlnLoss_zero_flat (M : Fin (L + 1) → ℕ) (P : Params M) :
    rlctAtOn (fun A : Params M => dlnLoss M 0 A) P
      = rlctAtOn (flatNodeLoss M) (paramsEquivFlat M P) := by
  -- the homeomorph coe = the measurable-equiv coe = `paramsEquivFlat M`.
  have hcoefun : ⇑(paramsEquivFlatCLE M).toHomeomorph = ⇑(paramsEquivFlat M) := by
    rw [ContinuousLinearEquiv.coe_toHomeomorph, paramsEquivFlatCLE_coe]
  have hcomp := rlctAtOn_comp_homeomorph
    (M := Params M) (M' := (Fin (flatDim M) → ℝ))
    (paramsEquivFlatCLE M).toHomeomorph
    (by rw [hcoefun]; exact measurePreserving_paramsEquivFlat M)
    (by rw [hcoefun]; exact (paramsEquivFlat M).measurableEmbedding)
    (flatNodeLoss M) P
  -- `flatNodeLoss M (paramsEquivFlat M w) = dlnLoss M 0 w`
  have hid : (fun w : Params M => flatNodeLoss M ((paramsEquivFlatCLE M).toHomeomorph w))
      = fun w : Params M => dlnLoss M 0 w := by
    funext w
    rw [hcoefun, flatNodeLoss, (paramsEquivFlat M).symm_apply_apply]
  rw [hid] at hcomp
  rw [hcomp, hcoefun]

/-- **Aoyagi Theorem 4 on the reduced core (`Params` domain).** The deepest core point `0 : Params M`
has minimal local RLCT over every reduced-core point `P`: `rlctAtOn (dlnLoss M 0) 0 ≤ rlctAtOn
(dlnLoss M 0) P`. This is the previously-blocked `hCore` — discharged by the homogeneity comparison
`deepest_le_of_homogeneous_core` on the EXPLICIT core (degree-`2L` homogeneous, `flatNodeLoss_smul`),
transported through `paramsEquivFlat`, NOT by any residual-value identity. -/
theorem core_zero_le_of_params (M : Fin (L + 1) → ℕ) (P : Params M) :
    rlctAtOn (fun A : Params M => dlnLoss M 0 A) (fun _ => 0 : Params M)
      ≤ rlctAtOn (fun A : Params M => dlnLoss M 0 A) P := by
  rw [rlctAtOn_dlnLoss_zero_flat M (fun _ => 0), rlctAtOn_dlnLoss_zero_flat M P]
  -- `paramsEquivFlat M 0 = 0` (linear)
  have hz : paramsEquivFlat M (fun _ => 0 : Params M) = 0 := by
    rw [← paramsEquivFlatLinear_coe]
    exact map_zero (paramsEquivFlatLinear M)
  rw [hz]
  exact deepest_le_of_homogeneous_core (flatNodeLoss M) (paramsEquivFlat M P) (2 * L)
    (measurable_flatNodeLoss M) (fun c x => flatNodeLoss_smul M c x)

/-! ## The crux (SORRY): the explicit block-reduction producer -/

/-- **The D1 `≥`-leg explicit-core producer (L = 2), the crux.** At a general optimal `v`
(`prod H v = B`), Aoyagi's Step-1 explicit corner-elimination block reduction lands the local RLCT of
the loss at `v` on the EXPLICIT reduced core `dlnLoss (H − r) 0` at some explicit reduced-core point,
plus the regular shift `nRegL2 H r / 2`:

    ∃ P : Params (H − r), nRegL2 H r / 2 + rlctAtOn (dlnLoss (H − r) 0) P ≤ rlctAt H (dlnLoss H B) v.

TRUTH CONFIRMED (analytic, Codex xhigh + numeric, `genm-hAtV`, witness (4,4,4)/r=1, middle-stratum
`v`): the explicit Schur reduction is EXACT and germ-preserving. Pick a common invertible `r×r` minor
of the layers at `v` (exists since every partial product has `rank ≥ r`; front WLOG puts it top-left).
Block `A0 = [[X,Y],[Z,W]]`, `A1 = [[S,T],[U,V]]`; on `{det X ≠ 0, det M11 ≠ 0}` (`Mᵢⱼ` the product
blocks) the regular coordinates `p = (M11 − I, M12, M21)` (dimension `= nRegL2 H r`) separate, and the
slice residual at `p = 0` is EXACTLY `‖A0red · A1red‖² = dlnLoss (H − r) 0 (A0red, A1red)`, with
`A0red = W − Z X⁻¹ Y`, `A1red = V − U M11⁻¹ M12` the reduced `(H − r)`-core factors (Schur complement
`M22 − M21 M11⁻¹ M12 = A0red A1red`, sympy-verified `‖Δ‖ ≈ 1e-15`). NO existence-only `Ψsymm`: the
residual is polynomial in the entries + rational in `det X`, `det M11`. There is a genuine dimension
gap (`flatDim − nReg − dimParams(H − r) = r(2 H1 − r)`, e.g. `7` at (4,4,4)/r=1): the reduction map is a
SUBMERSION, not a diffeo — the extra directions are FLAT (the loss is constant along them).

REDUCTION TO ONE REMAINING PIECE (all analytic bricks BANKED). The crux reduces — via the banked
`rlctAt_ge_nReg_add_slice_of_residual` (the `nReg`-block quasi-split from a `C¹` slice residual) — to
producing the EXPLICIT Schur chart transfer

    hchart_explicit : rlctAt H (dlnLoss H B) v
        = rlctAtOn (fun p => (∑ i, p.1 i ^ 2) + (∑ i, qₑ p i ^ 2)) (0, t0)

with `qₑ` the EXPLICIT (Schur, `Ψsymm`-free) residual — the germ-preserving analogue of
`dln_hchart_residual`. Given `hchart_explicit`, `hAtV` follows: the slice residual `∑ qₑ(0,·)²` equals
`dlnLoss (H − r) 0 ∘ φ` (φ the Schur submersion onto the reduced core), so
`rlctAtOn (∑ qₑ(0,·)²) t0 = rlctAtOn (dlnLoss (H − r) 0) P` for `P = φ_essential(t0)` by the BANKED
`rlctAtOn_spectator_peel` (peels the flat directions — this IS the "flat-direction Fubini" brick, ALREADY
in `S1Spectator`) + `rlctAtOn_comp_homeomorph` (the essential linear reindex) + `rlctAtOn_unit_invariant_aux`
(the bounded Gram/Jacobian unit, non-vanishing per modelidwit's Gram-sandwich). The Params-domain
Aoyagi Theorem 4 (`core_zero_le_of_params`, PROVEN above) then dominates any such `P`.

THE WALL (isolated, honest): `hchart_explicit` itself — certifying the explicit rational corner-
elimination map as a local measurable chart with the essential/flat coordinate split and the
bounded-unit Jacobian (Codex-flagged step 5). This is the general-`v` analogue of the deepest-point
`DeepestGaugeChart` multi-file build (which lands the same chart at the ORIGIN, for rank-`r`-exact
layers); a fresh ~600–1500-line sub-tide, NOT a further gate on the abstract germ-discarded `Ψsymm`
residual. UNCONDITIONAL at L = 2 (no `hbox`): the deepest value uses the banked hbox-free R1
`r1_resolution_interface_L2_generic`, and this leg dominates the core by Theorem 4, never computing an
`M'`-degraded value. Base case of the ∀-L `rlctAt_deepest_le_of_optimal` (Skeleton:1172, same
recursion). -/
theorem d1ge_L2_hAtV_explicit
    (H : Fin (2 + 1) → ℕ) (r : ℕ) (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ)
    (v : Params H) (hopt : prod H v = B) (hB : B.rank = r) :
    ∃ P : Params (fun s => H s - r),
      (nRegL2 H r : ℝ≥0∞) / 2
          + rlctAtOn (fun A : Params (fun s => H s - r) =>
              dlnLoss (fun s => H s - r)
                (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last 2))) ℝ) A)
              P
        ≤ rlctAt H (dlnLoss H B) v := by
  sorry

/-! ## The `HeadlineL2Assembly.hD1ge_L2` drop-in -/

/-- **The LEAF-2 drop-in via the explicit core.** At the front-pivoted `B`, for the constructed
`deepestPoint`, the D1 per-point `≥`-leg closes from three pieces: the deepest-side value
`hDeepest` (#44 at L = 2 fed the banked R1 value), the Params-domain Aoyagi Theorem 4
`core_zero_le_of_params` (`hCore`), and the explicit-core producer `d1ge_L2_hAtV_explicit` (`hAtV`).
The banked bridge `deepest_le_of_optimal_via_L2_ge` combines them. `coreDeepest = ofReal(lambdaCore
(H − r))`; R1 identifies it with `rlctAtOn (dlnLoss (H − r) 0) 0`, at which `core_zero_le_of_params`
compares against the producer's reduced-core point. -/
theorem d1ge_L2_deepestPoint_via_explicit_core
    (H : Fin (2 + 1) → ℕ) (r : ℕ) (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ)
    (hB : B.rank = r) (hr : ∀ s : Fin (2 + 1), r ≤ H s) (hL : 1 ≤ 2)
    (hpos : ∀ s : Fin (2 + 1), r < H s)
    (htop : (B.submatrix (Fin.castLE (hr 0) : Fin r → Fin (H 0))
        (id : Fin (H (Fin.last 2)) → Fin (H (Fin.last 2)))).rank = r)
    (hcolfront : (B.submatrix (id : Fin (H 0) → Fin (H 0))
        (Fin.castLE (hr (Fin.last 2)) : Fin r → Fin (H (Fin.last 2)))).rank = r)
    (v : Params H) (hopt : prod H v = B) :
    rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr hL)
      ≤ rlctAt H (dlnLoss H B) v := by
  set M := (fun s => H s - r) with hM
  -- the banked R1 value at the reduced widths: `rlctAtOn (dlnLoss M 0) 0 = ofReal(lambdaCore M)`.
  have hR1 : rlctAtOn (fun A : Params M =>
        dlnLoss M (0 : Matrix (Fin (M 0)) (Fin (M (Fin.last 2))) ℝ) A) (fun _ => 0 : Params M)
      = ENNReal.ofReal (lambdaCore M : ℝ) :=
    r1_resolution_interface_L2_generic (le_refl 2) (by norm_num) M
      (fun s => Nat.sub_pos_of_lt (hpos s))
  -- the deepest-side value: #44-at-L2 (front-pivot) fed the banked R1 value at `M = H − r`.
  have hDeepest : rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr hL)
      = (nRegL2 H r : ℝ≥0∞) / 2 + ENNReal.ofReal (lambdaCore M : ℝ) :=
    deepest_regular_core_normal_form_L2_front H r B hB hr hL (le_refl 2) hpos htop hcolfront
      (by norm_num) hR1
  -- the explicit-core producer supplies the reduced-core point + the `hAtV` lower bound.
  obtain ⟨P, hAtV⟩ := d1ge_L2_hAtV_explicit H r B v hopt hB
  -- `hCore : ofReal(lambdaCore M) ≤ rlctAtOn (dlnLoss M 0) P` — R1 ▸ Params-domain Theorem 4.
  have hCore : ENNReal.ofReal (lambdaCore M : ℝ)
      ≤ rlctAtOn (fun A : Params M =>
          dlnLoss M (0 : Matrix (Fin (M 0)) (Fin (M (Fin.last 2))) ℝ) A) P := by
    rw [← hR1]; exact core_zero_le_of_params M P
  exact deepest_le_of_optimal_via_L2_ge (B := B) H r
    (rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr hL)) (rlctAt H (dlnLoss H B) v)
    (nRegL2 H r) (ENNReal.ofReal (lambdaCore M : ℝ))
    (rlctAtOn (fun A : Params M =>
      dlnLoss M (0 : Matrix (Fin (M 0)) (Fin (M (Fin.last 2))) ℝ) A) P)
    hDeepest hAtV hCore

/-- **The general-`L` (pinned `L = 2`) drop-in for `HeadlineL2Assembly.hD1ge_L2`.** Same conclusion
as `d1ge_L2_deepestPoint_via_explicit_core`, stated at general `L` with the `hL2 : 2 ≤ L`,
`hLlt : L < 3` pins the headline scaffold carries — so it plugs directly into the assembly's `hD1ge_L2`
slot without a substitution there. The pins force `L = 2`, reducing to the `Fin 3` producer. -/
theorem d1ge_L2_deepestPoint_via_explicit_core_genL {L : ℕ}
    (H : Fin (L + 1) → ℕ) (r : ℕ) (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ)
    (hB : B.rank = r) (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (hpos : ∀ s : Fin (L + 1), r < H s)
    (htop : (B.submatrix (Fin.castLE (hr 0) : Fin r → Fin (H 0))
        (id : Fin (H (Fin.last L)) → Fin (H (Fin.last L)))).rank = r)
    (hcolfront : (B.submatrix (id : Fin (H 0) → Fin (H 0))
        (Fin.castLE (hr (Fin.last L)) : Fin r → Fin (H (Fin.last L)))).rank = r)
    (hLlt : L < 3)
    (v : Params H) (hopt : prod H v = B) :
    rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr hL) ≤ rlctAt H (dlnLoss H B) v := by
  obtain rfl : L = 2 := by omega
  exact d1ge_L2_deepestPoint_via_explicit_core H r B hB hr hL hpos htop hcolfront v hopt

end DLNFibre.DLN.RLCT
