1. **image**

(a) Verdict: **ACHIEVABLE-CHEAP**.

(b) Cheapest sound route:

1. Prove a new origin lemma:
   `interiorLivePhi_zero : interiorLivePhi ha h0r h0c 0 = 0` (**NEW**).
   Route: use `hmap_leaf` (**KNOWN local**), `kLDU_zero` (**NEW**), `pivotBlowupOn_zero` (**NEW**), and `BchartLeaf_zero` via `BparamsLeaf_zero` + `paramsEquivFlat_deepest` (**KNOWN local**).
2. For `kLDU_zero`, prove `kLens_zero` from `kLens_eq`; use `simp` on `matrixSplit`, `lowMatL`, `upMatL`, `Matrix.diagonal` (**some simp shape INFERRED**).
3. Get continuity as:
   `(interiorLive_diff ha h0r h0c).continuous` (**KNOWN local pattern**).
4. Copy `phi334_image_subset_cubeBox`: use `isOpen_set_pi`, `isOpen_Ioo`, `cubeBox_subset_of_isOpen` (**KNOWN local usage**).
5. Convert `[0,δ]^N ⊆ cubeBox N δ` by coordinate `simp [cubeBox, Set.mem_Icc]` and `linarith` (**KNOWN tactic route**).

(c) Blocker: none. But there is **no alternative** if `φ 0 ≠ 0`: since every source box contains `0`, the statement for all `ε > 0` forces `interiorLivePhi 0 ∈ cubeBox N ε` for all `ε`, hence `interiorLivePhi 0 = 0`. The fixed `1` is harmless only because the live chart’s radial coordinate kills it at the origin.

2. **Umeas**

(a) Verdict: **ACHIEVABLE-MEDIUM**.

(b) Cheapest sound route:

1. Prove `continuous_interiorLiveUnit` (**NEW**) directly, not via the rate identity.
2. Use `(differentiable_kLDU M (tach M) ha).continuous` (**KNOWN local**) and coordinate continuity for `x leafPivot`; build continuity of `rfinFixedPivot ... (kLDU x)` by `continuous_pi` / `continuous_matrix` (**`continuous_pi` KNOWN, `continuous_matrix` GUESS exact name**).
3. Prove fieldwise continuity of the live decoder blocks `genBlkFlatLive ...`: readers are coordinate projections; use `Continuous.matrix_mul`, `.add`, `.smul`, `Continuous.matrix_reindex`, and fromBlocks continuity (**`Continuous.matrix_reindex` KNOWN local; exact `matrix_mul`/fromBlocks continuity names GUESS**).
4. Prove continuity of `Hmat 0` by downward recursion on `Chain.HmatAux`/`suffixAux` using `Chain.HmatAux_succ`, `Chain.suffixAux_succ` (**KNOWN local**) plus matrix continuity.
5. Finish by unfolding `VvalGen`/`HrGen`: finite sums of squares of continuous entries, then `exact continuous_interiorLiveUnit.measurable` (**`Continuous.measurable` KNOWN**).

(c) Blocker: none, but this is new infrastructure. The identity
`(x leafPivot)^2 * interiorLiveUnit x = continuous`
does not prove measurability across `{x leafPivot = 0}`.

3. **Ubound**

(a) Verdict: **BLOCKED-NEEDS-INFRA**.

(b) Cheapest sound route:

1. After `continuous_interiorLiveUnit`, prove the **upper-bound half** by the `Uval222_le_on_box` pattern: `isCompact_univ_pi (fun _ => isCompact_Icc)` (**KNOWN local**), `Set.eq_empty_or_nonempty`, `IsCompact.exists_isMaxOn` (**KNOWN local**), choose `max 1 (U u0)`.
2. For a.e. positivity, introduce a live polynomial:
   `UPolyLive : MvPolynomial (Fin (routeMAmbient M)) ℝ` (**NEW**).
3. Prove `eval_UPolyLive :
   MvPolynomial.eval x UPolyLive = interiorLiveUnit ha h0r h0c x` (**NEW**).
4. Prove `UPolyLive_ne_zero` (**NEW**), then apply `MvPolynomial.ae_eval_ne_zero` (**KNOWN local**) and combine with `interiorLiveUnit_nonneg` (**KNOWN local**) to get `0 < interiorLiveUnit` a.e.
5. Transfer full-volume a.e. positivity to `volume.restrict box` using `ae_mono`/`Measure.restrict_le_self` (**GUESS exact names**).

(c) Precise blocker: step 2-4 are missing for the **live + `rfinFixedPivot` + `kLDU`** unit. Existing `achieverUfun`, `UPolyGen`, `eval_UPolyGen`, and `ae_eval_ne_zero` infrastructure is for the dead-leaf `genBlkFlatStruct` decoder, not this live lensed decoder. The R1 witness is also for a different chart. Sound discharge needs either generic `kLens/kLDU` over `MvPolynomial` plus eval naturality, or a specialized nonzero-polynomial theorem for `interiorLiveUnit`.

**CHEAPEST OVERALL ORDER**

1. Do `image` first: cheap and independent; it requires only the origin lemma.
2. Do `Umeas` next: medium, and it unlocks the compact upper-bound half of `Ubound`.
3. Do not try to close full `Ubound` until the live nonzero-polynomial infrastructure exists. `Umeas` helps boundedness only; it does not help the soundness-critical a.e.-positivity.