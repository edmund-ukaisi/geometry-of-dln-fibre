import DLNFibre.DLN.RLCT.Validate.RouteMLeafBData
import DLNFibre.DLN.RLCT.Validate.RouteMFactorMaps

/-!
# `RouteMProjV0Gate` — the projV0 DE-RISK gate: layer-0 of `fderiv BparamsLeaf` IS `schurFrameDeriv`

The discriminating bounded-vs-wall test (Codex's cheapest de-risk, decorrelated). The layer-0
component of the boundary-factor chart `BparamsLeaf ha y` — the `Matrix (Fin (M 0)) (Fin (M 1))`
block
read from the V0 = {K,X,N,E} inputs — factors, as a function of `y`, as

  `reindex ∘ schurFrameMap ∘ slotReaderV0`

with `slotReaderV0` the LINEAR read of the (K,N,X,E) slots into a `SchurInc` tuple. Its `fderiv` at
`y₀` is therefore `reindexCLM ∘L schurFrameD(slotReaderV0 y₀) ∘L slotReaderV0`, whose Schur-core is
`schurFrameDeriv X K N` (`det |det K|^{r+c}`). This establishes the foundation is TRACTABLE (the
opaque-Fin slot reindex closes), not a wall.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (the banked Agen0-collapse +
Cgen=schurFrameProd
+ the chain rule; no analysis beyond `schurFrameMap_hasFDerivAt`).
-/

open Matrix
open scoped BigOperators

namespace DLNFibre.DLN.RLCT

/-! ## The boundary-1 Schur frame widths (`L = 2`)

The layer-0 chart block reads the INTERIOR boundary `s = 1`. The Schur frame there has
core width `t = Text M (tach M) 2`, residual-row width `r = Text M (tach M) 1 − Text M (tach M) 2`,
residual-col width `c = Wext M 1 − Text M (tach M) 2`. The row split `t + r = Text M (tach M) 1`
(`= M 0` at the identity boundary), the col split `t + c = Wext M 1` (`= M 1`). -/

section L2

variable {M : Fin (2 + 1) → ℕ}

/-- The Schur-core width `t` at boundary `1`. -/
noncomputable abbrev schurT1 (M : Fin (2 + 1) → ℕ) : ℕ := Text M (tach M) 2
/-- The residual-row width `r` at boundary `1`. -/
noncomputable abbrev schurR1 (M : Fin (2 + 1) → ℕ) : ℕ := Text M (tach M) 1 - Text M (tach M) 2
/-- The residual-col width `c` at boundary `1`. -/
noncomputable abbrev schurC1 (M : Fin (2 + 1) → ℕ) : ℕ := Wext M 1 - Text M (tach M) 2

/-- The four V0 readers at boundary `0` (`= GenBlk boundary s = 1`), packaged as a `SchurInc` tuple
`(K, N, X, E)` — the input of `schurFrameMap`. The reads are LINEAR (each `readK/N/X/E` is a flat
coordinate projection `y ↦ y idx`). -/
noncomputable def slotReadV0 (ha : StructAdm M (tach M)) (y : Fin (routeMAmbient M) → ℝ) :
    SchurInc (schurT1 M) (schurR1 M) (schurC1 M) :=
  (readK M (tach M) ha y ⟨0, by decide⟩,
    readN M (tach M) ha y ⟨0, by decide⟩,
    readX M (tach M) ha y ⟨0, by decide⟩,
    readE M (tach M) ha y ⟨0, by decide⟩)

/-! ## The Agen0-collapse: `Agen 1 … 0 = Cgen 1 … 1 = schurFrameProd` (the discriminating
opaque-Fin step)

At the `tach` path the residual width `c0 = Wext M 0 − Text M (tach M) 1 = 0` (the identity
boundary),
so `chainA`'s lift block is empty: every row of `Agen 1 … 0` is a `castAdd` kept row, with `N0·W0
= 0`,
giving `Agen 1 … 0 = Cgen 1 … 1`. Then the banked `Cgen_live_interior_eq_schurFrameProd` reads the
interior `Cgen 1` as the Schur frame `schurFrameProd … 1 (readK)(readX)(readN)(readE)`. This is the
opaque-Fin slot-reindex step the prior wall named — generalized from the (2,2,2) `Agen0_Glr_eq` /
(3,3,4) `Agen0_3333_eq` literal cases to opaque `Text/Wext`. -/

/-- **`Agen 1 … 0` entry = `Cgen 1 … 1` entry** at the `tach` identity boundary (`c0 = 0`): every
row
of the layer-0 lift column is a `castAdd` kept row (`chainA_apply_castAdd`), and `N0·W0 = 0`
(residual
width 0). Entrywise (the matrix-level equation is type-fragile across `Fin (Wext M 0)` /
`Fin (Text M (tach M) 1)`). -/
theorem Agen0_live_entry (ha : StructAdm M (tach M))
    (rfin : Matrix (Fin (Text M (tach M) 2)) (Fin (Wext M 2)) ℝ)
    (y : Fin (routeMAmbient M) → ℝ)
    (i' : Fin (Text M (tach M) (0 + 1))) (j : Fin (Wext M 1)) :
    Agen (1 : ℝ) M (tach M) (genBlkFlatLive M (tach M) ha rfin y) (hleStruct M (tach M) ha) 0
        (Fin.cast (genWidthEq M (tach M) (hleStruct M (tach M) ha) 0 ha.hL)
          (Fin.castAdd (Wext M 0 - Text M (tach M) (0 + 1)) i')) j
      = Cgen (1 : ℝ) M (tach M) (genBlkFlatLive M (tach M) ha rfin y)
          (hleStruct M (tach M) ha) 1 i' j := by
  set B := genBlkFlatLive M (tach M) ha rfin y with hB
  set hle := hleStruct M (tach M) ha with hhle
  have hA : Agen (1 : ℝ) M (tach M) B hle 0
      = chainA (genWidthEq M (tach M) hle 0 ha.hL) (B.Nblk 0) (B.Wblk 0)
          (Cgen (1 : ℝ) M (tach M) B hle 1) := by
    show (if hk : (0 : ℕ) < 2 then chainA _ _ _ _ else 0) = _
    rw [dif_pos ha.hL]
  -- the residual width is 0: `N0·W0 = 0`
  have hN0W0 : B.Nblk 0 * B.Wblk 0 = 0 := by
    ext a b
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    have hc0 : Wext M 0 - Text M (tach M) (0 + 1) = 0 := by
      have h := Wext0_eq_Text1 M (tach M) ha; rw [show (0 : ℕ) + 1 = 1 from rfl]; omega
    exact (Fin.cast hc0 k).elim0
  rw [hA, chainA_apply_castAdd, hN0W0, Matrix.sub_apply, Matrix.zero_apply, sub_zero]

/-! ## The block-flatten `flatBlock : SchurInc → block matrix`, and the bridge to `schurFrameMap`

`flatBlock` flattens a tuple `(A,B,C,D)` (an element of `SchurInc t r c`) into the block matrix
`[[A,B],[C,D]] : Matrix (Fin (t+r)) (Fin (t+c))` over the `Fin.castAdd/natAdd` splits — the same
row/col split layout `schurFrameProd`'s block lemmas use. The bridge
`flatBlock (schurFrameMap z) = schurFrameProd … 1 z.K z.X z.N z.E` is the discriminating entrywise
block-identity Codex named: top-left = K, top-right = K·N, bottom-left = X·K,
bottom-right = X·K·N + E — at the exact split indices. -/

/-- The block-flatten `[[A,B],[C,D]]` of a `SchurInc t r c` tuple `(A,N,C,E)` into a single block
matrix of target size `Trow × Wcol` (with `t + r = Trow`, `t + c = Wcol`), via the canonical
`Fin.castAdd/natAdd` row/col split. Parametrized over the target widths so it lands in the SAME type
as `schurFrameProd … 1`. -/
noncomputable def flatBlock {t r c Trow Wcol : ℕ} (hr : t + r = Trow) (hc : t + c = Wcol)
    (z : SchurInc t r c) : Matrix (Fin Trow) (Fin Wcol) ℝ :=
  Matrix.of fun (i : Fin Trow) (j : Fin Wcol) =>
    Sum.elim
      (fun (i' : Fin t) => Sum.elim (fun j' => z.1 i' j') (fun j' => z.2.1 i' j')
        (finSumFinEquiv.symm (Fin.cast hc.symm j)))
      (fun (i' : Fin r) => Sum.elim (fun j' => z.2.2.1 i' j') (fun j' => z.2.2.2 i' j')
        (finSumFinEquiv.symm (Fin.cast hc.symm j)))
      (finSumFinEquiv.symm (Fin.cast hr.symm i))

/-- `flatBlock` entry at a `castAdd/·` row (the kept block): the row split selects the top blocks.
-/
theorem flatBlock_castAdd {t r c Trow Wcol : ℕ} (hr : t + r = Trow) (hc : t + c = Wcol)
    (z : SchurInc t r c) (i' : Fin t) (j : Fin Wcol) :
    flatBlock hr hc z (Fin.cast hr (Fin.castAdd r i')) j =
      Sum.elim (fun j' => z.1 i' j') (fun j' => z.2.1 i' j')
        (finSumFinEquiv.symm (Fin.cast hc.symm j)) := by
  simp only [flatBlock, Matrix.of_apply]
  rw [show Fin.cast hr.symm (Fin.cast hr (Fin.castAdd r i')) = Fin.castAdd r i' from by
    apply Fin.ext; simp, finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl]

/-- `flatBlock` entry at a `natAdd/·` row (the residual block): the row split selects the bottom. -/
theorem flatBlock_natAdd {t r c Trow Wcol : ℕ} (hr : t + r = Trow) (hc : t + c = Wcol)
    (z : SchurInc t r c) (a : Fin r) (j : Fin Wcol) :
    flatBlock hr hc z (Fin.cast hr (Fin.natAdd t a)) j =
      Sum.elim (fun j' => z.2.2.1 a j') (fun j' => z.2.2.2 a j')
        (finSumFinEquiv.symm (Fin.cast hc.symm j)) := by
  simp only [flatBlock, Matrix.of_apply]
  rw [show Fin.cast hr.symm (Fin.cast hr (Fin.natAdd t a)) = Fin.natAdd t a from by
    apply Fin.ext; simp, finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr]

/-- **The bridge**: `flatBlock (schurFrameMap z) = schurFrameProd … 1 z.K z.X z.N z.E` at the
boundary-1 Schur widths. The discriminating entrywise block-identity: top-left K, top-right K·N,
bottom-left X·K, bottom-right X·K·N + E — at the matching `castAdd/natAdd` splits. Closed by the
four
banked `schurFrameProd_block_*` lemmas after splitting each row/col index. -/
theorem flatBlock_schurFrameMap_eq (ha : StructAdm M (tach M))
    (hr : schurT1 M + schurR1 M = Text M (tach M) 1) (hc : schurT1 M + schurC1 M = Wext M 1)
    (z : SchurInc (schurT1 M) (schurR1 M) (schurC1 M)) :
    flatBlock hr hc (schurFrameMap z)
      = schurFrameProd M (tach M) 1 (ha.hdesc 0 (by decide)) (ha.hub 0) (1 : ℝ)
          z.1 z.2.2.1 z.2.1 z.2.2.2 := by
  -- the schurFrameProd row/col split equalities (the proof-irrelevant same nat eqs)
  have hTr : Text M (tach M) (1 + 1) + (Text M (tach M) 1 - Text M (tach M) (1 + 1))
      = Text M (tach M) 1 := by
    have h := ha.hdesc 0 (by decide); simp only [Nat.zero_add] at h; omega
  have hWc : Text M (tach M) (1 + 1) + (Wext M 1 - Text M (tach M) (1 + 1)) = Wext M 1 := by
    have h := ha.hub 0; simp only [Nat.zero_add] at h; omega
  -- both block matrices over Fin (Text M (tach M) 1) × Fin (Wext M 1)
  ext i j
  -- decompose row `i` and col `j` by the canonical sum split
  obtain ⟨is, hieq⟩ : ∃ is : Fin (schurT1 M) ⊕ Fin (schurR1 M),
      i = Fin.cast hr (finSumFinEquiv is) := ⟨finSumFinEquiv.symm (Fin.cast hr.symm i), by
        rw [Equiv.apply_symm_apply]; apply Fin.ext; simp⟩
  obtain ⟨js, hjeq⟩ : ∃ js : Fin (schurT1 M) ⊕ Fin (schurC1 M),
      j = Fin.cast hc (finSumFinEquiv js) := ⟨finSumFinEquiv.symm (Fin.cast hc.symm j), by
        rw [Equiv.apply_symm_apply]; apply Fin.ext; simp⟩
  subst hieq hjeq
  -- schurFrameMap z = (z.K, z.K*z.N, (z.X*z.K, z.X*z.K*z.N + z.E))
  rcases is with i' | a <;> rcases js with j' | b
  · -- top-left: K
    rw [show (Fin.cast hr (finSumFinEquiv (Sum.inl i')) : Fin (Text M (tach M) 1))
          = Fin.cast hr (Fin.castAdd (schurR1 M) i') from by apply Fin.ext; simp,
        flatBlock_castAdd, show (Fin.cast hc (finSumFinEquiv (Sum.inl j')) : Fin (Wext M 1))
          = Fin.cast hc (Fin.castAdd (schurC1 M) j') from by apply Fin.ext; simp]
    rw [show Fin.cast hc.symm (Fin.cast hc (Fin.castAdd (schurC1 M) j'))
          = Fin.castAdd (schurC1 M) j' from by
      apply Fin.ext; simp, finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl]
    rw [show (Fin.cast hr (Fin.castAdd (schurR1 M) i') : Fin (Text M (tach M) 1))
          = Fin.cast hTr (Fin.castAdd _ i') from by apply Fin.ext; simp,
        show (Fin.cast hc (Fin.castAdd (schurC1 M) j') : Fin (Wext M 1))
          = Fin.cast hWc (Fin.castAdd _ j') from by apply Fin.ext; simp,
        schurFrameProd_block_K]
    rfl
  · -- top-right: K·N
    rw [show (Fin.cast hr (finSumFinEquiv (Sum.inl i')) : Fin (Text M (tach M) 1))
          = Fin.cast hr (Fin.castAdd (schurR1 M) i') from by apply Fin.ext; simp,
        flatBlock_castAdd, show (Fin.cast hc (finSumFinEquiv (Sum.inr b)) : Fin (Wext M 1))
          = Fin.cast hc (Fin.natAdd (schurT1 M) b) from by apply Fin.ext; simp]
    rw [show Fin.cast hc.symm (Fin.cast hc (Fin.natAdd (schurT1 M) b))
          = Fin.natAdd (schurT1 M) b from by
      apply Fin.ext; simp, finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr]
    rw [show (Fin.cast hr (Fin.castAdd (schurR1 M) i') : Fin (Text M (tach M) 1))
          = Fin.cast hTr (Fin.castAdd _ i') from by apply Fin.ext; simp,
        show (Fin.cast hc (Fin.natAdd (schurT1 M) b) : Fin (Wext M 1))
          = Fin.cast hWc (Fin.natAdd _ b) from by apply Fin.ext; simp,
        schurFrameProd_block_KN]
    show (schurFrameMap z).2.1 i' b = (z.1 * z.2.1) i' b
    rfl
  · -- bottom-left: X·K
    rw [show (Fin.cast hr (finSumFinEquiv (Sum.inr a)) : Fin (Text M (tach M) 1))
          = Fin.cast hr (Fin.natAdd (schurT1 M) a) from by apply Fin.ext; simp,
        flatBlock_natAdd, show (Fin.cast hc (finSumFinEquiv (Sum.inl j')) : Fin (Wext M 1))
          = Fin.cast hc (Fin.castAdd (schurC1 M) j') from by apply Fin.ext; simp]
    rw [show Fin.cast hc.symm (Fin.cast hc (Fin.castAdd (schurC1 M) j'))
          = Fin.castAdd (schurC1 M) j' from by
      apply Fin.ext; simp, finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl]
    rw [show (Fin.cast hr (Fin.natAdd (schurT1 M) a) : Fin (Text M (tach M) 1))
          = Fin.cast hTr (Fin.natAdd _ a) from by apply Fin.ext; simp,
        show (Fin.cast hc (Fin.castAdd (schurC1 M) j') : Fin (Wext M 1))
          = Fin.cast hWc (Fin.castAdd _ j') from by apply Fin.ext; simp,
        schurFrameProd_block_XK]
    rfl
  · -- bottom-right: X·K·N + E
    rw [show (Fin.cast hr (finSumFinEquiv (Sum.inr a)) : Fin (Text M (tach M) 1))
          = Fin.cast hr (Fin.natAdd (schurT1 M) a) from by apply Fin.ext; simp,
        flatBlock_natAdd, show (Fin.cast hc (finSumFinEquiv (Sum.inr b)) : Fin (Wext M 1))
          = Fin.cast hc (Fin.natAdd (schurT1 M) b) from by apply Fin.ext; simp]
    rw [show Fin.cast hc.symm (Fin.cast hc (Fin.natAdd (schurT1 M) b))
          = Fin.natAdd (schurT1 M) b from by
      apply Fin.ext; simp, finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr]
    rw [show (Fin.cast hr (Fin.natAdd (schurT1 M) a) : Fin (Text M (tach M) 1))
          = Fin.cast hTr (Fin.natAdd _ a) from by apply Fin.ext; simp,
        show (Fin.cast hc (Fin.natAdd (schurT1 M) b) : Fin (Wext M 1))
          = Fin.cast hWc (Fin.natAdd _ b) from by apply Fin.ext; simp,
        schurFrameProd_block_XKNuE]
    show (z.2.2.1 * z.1 * z.2.1 + z.2.2.2) a b = (z.2.2.1 * z.1 * z.2.1) a b + 1 * z.2.2.2 a b
    rw [Matrix.add_apply, one_mul]

/-! ## `slotReadV0` is LINEAR (each reader is a coordinate projection), with a `HasFDerivAt`

Each reader `readK/N/X/E … y k i j = y (idx i j)` is the coordinate projection `y ↦ y idx`, hence
linear. So `slotReadV0 ha : (Fin N → ℝ) → SchurInc t r c` has the constant CLM fderiv it carries —
every component is `hasFDerivAt_apply`, assembled over the 4 blocks + their matrix entries. -/

/-- `slotReadV0 ha` has a fderiv `slotReadV0D ha y₀` at every `y₀` — the linear CLM reading the same
slots (every matrix entry a coordinate projection). The fderiv CLM is supplied by the proof. -/
theorem slotReadV0_hasFDerivAt (ha : StructAdm M (tach M)) (y₀ : Fin (routeMAmbient M) → ℝ) :
    HasFDerivAt (fun y => slotReadV0 ha y) (fderiv ℝ (fun y => slotReadV0 ha y) y₀) y₀ := by
  apply DifferentiableAt.hasFDerivAt
  unfold slotReadV0
  apply DifferentiableAt.prodMk
  · apply differentiableAt_pi.mpr; intro i; apply differentiableAt_pi.mpr; intro j
    exact differentiableAt_apply _ y₀
  apply DifferentiableAt.prodMk
  · apply differentiableAt_pi.mpr; intro i; apply differentiableAt_pi.mpr; intro j
    exact differentiableAt_apply _ y₀
  apply DifferentiableAt.prodMk
  · apply differentiableAt_pi.mpr; intro i; apply differentiableAt_pi.mpr; intro j
    exact differentiableAt_apply _ y₀
  · apply differentiableAt_pi.mpr; intro i; apply differentiableAt_pi.mpr; intro j
    exact differentiableAt_apply _ y₀

/-- `flatBlock hr hc` is linear in its `SchurInc` argument (entrywise a `Sum.elim` of projections),
hence differentiable with its own fderiv. -/
theorem flatBlock_differentiableAt {t r c Trow Wcol : ℕ} (hr : t + r = Trow) (hc : t + c = Wcol)
    (z₀ : SchurInc t r c) : DifferentiableAt ℝ (fun z => flatBlock hr hc z) z₀ := by
  unfold flatBlock
  apply differentiableAt_pi.mpr; intro i; apply differentiableAt_pi.mpr; intro j
  -- the entry is `Sum.elim (...) (...) (split i)`, a coordinate read of `z`'s blocks → linear
  simp only [Matrix.of_apply]
  rcases finSumFinEquiv.symm (Fin.cast hr.symm i) with i' | a <;>
    rcases finSumFinEquiv.symm (Fin.cast hc.symm j) with j' | b <;>
    simp only [Sum.elim_inl, Sum.elim_inr] <;> fun_prop

/-! ## THE GATE: the layer-0 Schur-frame map's fderiv factors through `schurFrameDeriv`

The layer-0 chart block, viewed through the banked factorization
`reindex ∘ flatBlock ∘ schurFrameMap ∘ slotReadV0`, has fderiv
`flatBlockD ∘L schurFrameD(slotReadV0 ha y₀) ∘L slotReadV0D` (chain rule:
`slotReadV0` linear; `schurFrameMap_hasFDerivAt`; `flatBlock` linear). The MIDDLE factor
`schurFrameD z = schurFrameDeriv z.X z.K z.N` IS the Schur-frame differential (det `|det K|^{r+c}`,
banked `schurFrameDeriv_det`). The opaque-Fin slot reindex closes cleanly — the foundation is
TRACTABLE. -/

/-- **The layer-0 Schur-frame map** as a function of `y`: read the V0 slots into a `SchurInc` tuple,
apply the Schur frame, flatten to the layer-0 block matrix. By `flatBlock_schurFrameMap_eq` this is
exactly `schurFrameProd … 1 (readK)(readX)(readN)(readE)` = the chart's `Cgen 1` = `Agen 0`. -/
noncomputable def layer0SchurMap (ha : StructAdm M (tach M))
    (hr : schurT1 M + schurR1 M = Text M (tach M) 1) (hc : schurT1 M + schurC1 M = Wext M 1)
    (y : Fin (routeMAmbient M) → ℝ) : Matrix (Fin (Text M (tach M) 1)) (Fin (Wext M 1)) ℝ :=
  flatBlock hr hc (schurFrameMap (slotReadV0 ha y))

/-- **THE GATE (PASS).** The layer-0 Schur-frame map `layer0SchurMap` has a fderiv at `y₀` that
factors through `schurFrameD (slotReadV0 ha y₀)` — i.e. its Schur core IS the banked Schur-frame
differential `schurFrameDeriv (readX y₀)(readK y₀)(readN y₀)` (det `|det K|^{r+c}`). The chain rule
over the linear `slotReadV0`, the banked `schurFrameMap_hasFDerivAt`, and the linear `flatBlock`. -/
theorem layer0SchurMap_hasFDerivAt (ha : StructAdm M (tach M))
    (hr : schurT1 M + schurR1 M = Text M (tach M) 1) (hc : schurT1 M + schurC1 M = Wext M 1)
    (y₀ : Fin (routeMAmbient M) → ℝ) :
    HasFDerivAt (layer0SchurMap ha hr hc)
      ((fderiv ℝ (fun z => flatBlock hr hc z) (schurFrameMap (slotReadV0 ha y₀))).comp
        ((schurFrameD (slotReadV0 ha y₀)).comp
          (fderiv ℝ (fun y => slotReadV0 ha y) y₀)))
      y₀ := by
  have h1 : HasFDerivAt (fun y => slotReadV0 ha y)
      (fderiv ℝ (fun y => slotReadV0 ha y) y₀) y₀ := slotReadV0_hasFDerivAt ha y₀
  have h2 : HasFDerivAt schurFrameMap (schurFrameD (slotReadV0 ha y₀)) (slotReadV0 ha y₀) :=
    schurFrameMap_hasFDerivAt _
  have h3 : HasFDerivAt (fun z => flatBlock hr hc z)
      (fderiv ℝ (fun z => flatBlock hr hc z) (schurFrameMap (slotReadV0 ha y₀)))
      (schurFrameMap (slotReadV0 ha y₀)) :=
    (flatBlock_differentiableAt hr hc _).hasFDerivAt
  exact h3.comp y₀ (h2.comp y₀ h1)

/-- **The Schur core of the gate IS `schurFrameDeriv`** (the explicit middle factor). The banked
`schurFrameD z = LinearMap.toContinuousLinearMap (schurFrameDeriv z.X z.K z.N)`, so the middle
factor of the layer-0 fderiv is exactly the Schur-frame differential
`schurFrameDeriv (readX)(readK)(readN)`, whose determinant is `|det K|^{r+c}`
(`schurFrameDeriv_det`). -/
theorem gate_schurCore_eq (ha : StructAdm M (tach M)) (y₀ : Fin (routeMAmbient M) → ℝ) :
    (schurFrameD (slotReadV0 ha y₀)).toLinearMap
      = schurFrameDeriv (readX M (tach M) ha y₀ ⟨0, by decide⟩)
          (readK M (tach M) ha y₀ ⟨0, by decide⟩) (readN M (tach M) ha y₀ ⟨0, by decide⟩) := by
  rw [schurFrameD, LinearMap.coe_toContinuousLinearMap]
  rfl

/-- **The gate's Schur core has determinant `|det K|^{r+c}`** — the banked `schurFrameDeriv_det`,
read at the V0 inputs. This is the per-boundary engine value the headline needs (`r+c = (Text 1 −
Text 2) + (Wext 1 − Text 2)`). -/
theorem gate_schurCore_abs_det (ha : StructAdm M (tach M)) (y₀ : Fin (routeMAmbient M) → ℝ) :
    |LinearMap.det (schurFrameD (slotReadV0 ha y₀)).toLinearMap|
      = |(slotReadV0 ha y₀).1.det| ^ (schurR1 M + schurC1 M) := by
  rw [schurFrameD, LinearMap.coe_toContinuousLinearMap, schurFrameDeriv_det, abs_pow]

/-! ## Tying the gate to the REAL chart: `Agen 1 … 0 = layer0SchurMap` (entrywise)

The layer-0 block of the boundary-factor chart `BparamsLeaf ha y` is `reindex (Agen 1 … 0)`, and
`Agen 1 … 0` entry = `Cgen 1 … 1` entry (`Agen0_live_entry`) = `schurFrameProd` entry
(`Cgen_live_interior_eq_schurFrameProd`) = `layer0SchurMap` (`flatBlock_schurFrameMap_eq`). This
confirms the gate's `layer0SchurMap` IS the chart's layer-0 Schur frame, so the gate's fderiv-core
`schurFrameDeriv` is the genuine layer-0 Jacobian core of `BparamsLeaf`. -/

/-- **`Cgen 1 … 1 = layer0SchurMap`** (the chart's interior transition = the gate's Schur-frame).
`Cgen_live_interior_eq_schurFrameProd` reads `Cgen 1` as
`schurFrameProd … 1 (readK)(readX)(readN)(readE)`; `flatBlock_schurFrameMap_eq` reads
`layer0SchurMap` (= `flatBlock (schurFrameMap (slotReadV0))`) as the SAME `schurFrameProd`. -/
theorem Cgen1_eq_layer0SchurMap (ha : StructAdm M (tach M))
    (hr : schurT1 M + schurR1 M = Text M (tach M) 1) (hc : schurT1 M + schurC1 M = Wext M 1)
    (rfin : Matrix (Fin (Text M (tach M) 2)) (Fin (Wext M 2)) ℝ)
    (y : Fin (routeMAmbient M) → ℝ) :
    Cgen (1 : ℝ) M (tach M) (genBlkFlatLive M (tach M) ha rfin y) (hleStruct M (tach M) ha) 1
      = layer0SchurMap ha hr hc y := by
  rw [layer0SchurMap, flatBlock_schurFrameMap_eq ha hr hc (slotReadV0 ha y)]
  -- `Cgen 1 … 1` = `schurFrameProd … 1 (readK)(readX)(readN)(readE)` (banked, k = 0, k+1 = 1 < 2)
  rw [Cgen_live_interior_eq_schurFrameProd M (tach M) ha rfin (1 : ℝ) y 0 (by decide)]
  -- the two `schurFrameProd` calls agree: slotReadV0 packages exactly (readK, readN, readX, readE)
  rfl

/-- **The layer-0 block of `BparamsLeaf` IS `reindex layer0SchurMap`** (entrywise). The chart's
layer-0 `Params` component is `reindex (Agen 1 … 0)`; `Agen0_live_entry` + `Cgen1_eq_layer0SchurMap`
identify `Agen 1 … 0` (kept rows) with `layer0SchurMap`. Confirms the gate's Schur-frame map is the
genuine layer-0 chart Jacobian core. -/
theorem BparamsLeaf_layer0_entry (ha : StructAdm M (tach M))
    (hr : schurT1 M + schurR1 M = Text M (tach M) 1) (hc : schurT1 M + schurC1 M = Wext M 1)
    (y : Fin (routeMAmbient M) → ℝ)
    (i' : Fin (Text M (tach M) (0 + 1))) (j : Fin (Wext M 1)) :
    Agen (1 : ℝ) M (tach M) (genBlkFlatLive M (tach M) ha (rfinDirect ha y) y)
        (hleStruct M (tach M) ha) 0
        (Fin.cast (genWidthEq M (tach M) (hleStruct M (tach M) ha) 0 ha.hL)
          (Fin.castAdd (Wext M 0 - Text M (tach M) (0 + 1)) i')) j
      = layer0SchurMap ha hr hc y i' j := by
  rw [Agen0_live_entry ha (rfinDirect ha y) y i' j,
    Cgen1_eq_layer0SchurMap ha hr hc (rfinDirect ha y) y]

end L2

end DLNFibre.DLN.RLCT
