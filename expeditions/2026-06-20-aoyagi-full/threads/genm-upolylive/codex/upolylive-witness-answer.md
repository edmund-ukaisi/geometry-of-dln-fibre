**VERDICT:** option **(a)**: re-run/extract the generic surviving-entry argument and instantiate it with the live decoder.

**Independence Check**
Yes for `Rfin L`: by your description, `Hmat_pivot`, `Hmat_row_thread`, and `suffix_carrier` only read `Bmat`, `Nblk`, `Wblk`, and `Rmat`. Since

```lean
(genBlkFlatLive ha rfin x).Bmat = (genBlkFlatStruct ha x).Bmat
(genBlkFlatLive ha rfin x).Nblk = (genBlkFlatStruct ha x).Nblk
(genBlkFlatLive ha rfin x).Wblk = (genBlkFlatStruct ha x).Wblk
(genBlkFlatLive ha rfin x).Rmat = (genBlkFlatStruct ha x).Rmat
```

are definitional or `simp` consequences, the live `Rfin` override is invisible to that proof.

For the radial scalar: **ASSUMING `Hmat_pivot` is genuinely stated for arbitrary `u` and concludes the literal pivot entry/indicator without a hypothesis like `u = 1`, then yes, the argument is scalar-independent.** The only possible hidden scalar dependence is inside `Hmat_pivot`, because that is where `u • Rmat` could enter. If the actual conclusion is instead something like

```lean
(chainOfMt u B hle).Hmat ... = u * ...
```

then the proof is not scalar-independent; you must add `wInt_leafPivot : w leafPivot = 1` or at least `w leafPivot ≠ 0`.

**Lean Skeleton**

```lean
lemma live_survival_entry_wInt
    (hp₁ : 1 ≤ p) (hpL : p < L) :
    let w := wInt M ha p
    let B := genBlkFlatLive ha (rfinFixedPivot ha w) w
    (chainOfMt (w leafPivot) B hle).Hmat 0 (ρ, 0) = 1 := by
  intro w B

  -- Same hypotheses used in `achieverUfun_wInt_ne_zero`,
  -- transported through the definitional shared fields.
  have hBmat := by
    simpa [B, genBlkFlatLive, genBlkFlatStruct] using
      genBlk_Bmat_pivot  (M := M) (ha := ha) (x := w) (p := p) hp₁ hpL

  have hRmat := by
    simpa [B, genBlkFlatLive, genBlkFlatStruct] using
      genBlk_Rmat_pivot (M := M) (ha := ha) (x := w) (p := p) hp₁ hpL

  have hW := by
    simpa [B, genBlkFlatLive, genBlkFlatStruct] using
      readW_wInt (M := M) (ha := ha) (p := p) hp₁ hpL

  have hsuf := by
    exact suffix_carrier (B := B) (u := w leafPivot) hW -- plus existing args

  have hpiv := by
    exact Hmat_pivot (B := B) (u := w leafPivot) hBmat hRmat -- plus args

  exact Hmat_row_thread (B := B) (u := w leafPivot) hpiv hsuf -- plus args


lemma interiorLiveUnit_wInt_ne_zero
    (hp₁ : 1 ≤ p) (hpL : p < L) :
    interiorLiveUnit (wInt M ha p) ≠ 0 := by
  let w := wInt M ha p
  have hk : kLDU M (tach M) ha w = w :=
    kLDU_wInt M ha p hp₁ hpL

  change
    sqSumHmat0
      (chainOfMt (w leafPivot)
        (genBlkFlatLive ha (rfinFixedPivot ha (kLDU M (tach M) ha w))
          (kLDU M (tach M) ha w)) hle) ≠ 0

  rw [hk]

  exact sqSumHmat0_ne_zero_of_entry (ρ, 0) (by
    simpa using live_survival_entry_wInt (M := M) (ha := ha) (p := p) hp₁ hpL)


lemma exists_interiorLiveUnit_ne_zero
    (hdrop : InteriorDrop M) :
    ∃ w, interiorLiveUnit w ≠ 0 := by
  rcases hdrop with ⟨p, hp₁, hpL, hrest⟩
  exact ⟨wInt M ha p, interiorLiveUnit_wInt_ne_zero (M := M) (ha := ha) hp₁ hpL⟩


lemma UPolyLive_ne_zero
    (hdrop : InteriorDrop M) :
    UPolyLive ≠ 0 := by
  rcases exists_interiorLiveUnit_ne_zero (M := M) (ha := ha) hdrop with ⟨w, hw⟩
  intro hzero
  have hval : interiorLiveUnit w = 0 := by
    simpa [hzero] using (eval_UPolyLive (u := w)).symm
  exact hw hval
```

**Trap**

Do not use `rfinFixedPivot ha w` to claim `w leafPivot = 1`. The override affects the live decoder’s `Rfin`, not the scalar argument `w leafPivot` passed to `chainOfMt`. If `Hmat_pivot` secretly returns an entry proportional to `u`, this is exactly where the live/leaf pivot can break the dead-leaf proof.