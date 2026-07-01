import DLNFibre.DLN.RLCT.Validate.RouteMInteriorDeepRank0
import DLNFibre.DLN.RLCT.Validate.RouteMUPolyLive
import DLNFibre.DLN.RLCT.Validate.RouteMAchieverWitnessInterior

/-!
# `RouteMInteriorDeepRank0AePos` — a.e.-positivity of the `deepRank = 0` unit factor (item 6)

The soundness pin the `deepRank = 0` interior handler (`RouteMInteriorDeepRank0`) needs: the unit factor
of the E-block radial blow-up chart is a.e.-positive,
`∀ᵐ u, 0 < VvalGen (u eBlockPivot) M (tach M) (genBlkFlatEfp ha hp1 hp2 u) hle`.

## Route (Codex xhigh, route (a))

Mirror `RouteMUPolyLive.interiorLiveUnit_ae_pos`: encode the unit as `eval u` of a NAMED nonzero
polynomial `UPolyEfp : MvPolynomial (Fin N) ℝ`, then `MvPolynomial.ae_eval_ne_zero` gives the zero set
is null, and `VvalGen_nonneg` (sum of squares) upgrades `≠ 0` to `0 <`.

Three pieces:

* **the polynomial Efp decoder** `genBlkFlatEfpGen` over `MvPolynomial` — the live decoder
  `genBlkFlatLiveGen` (`rfin = 0`, since the leaf is `Text 2 = 0`-dim) with the pivot boundary `1`'s
  `Rmat` overridden (via `Function.update`) to `rmatPad (EfixedReaderGen x)`, the E-pivot pinned to the
  constant `1`. Its `GenBlkMap` to the ℝ `genBlkFlatEfp` under `eval u` glues the shared-field map
  (`genBlkFlatLiveGen_genBlkMap_of`) with the pivot-`Rmat` naturality (`rmatPad_map` + `EfixedReaderGen_map`).
* **`eval u UPolyEfp = VvalGen (u eBlockPivot) … (genBlkFlatEfp u) hle`** — `eval u` pushes through the
  `∑∑·²` (`sqSumHmat0_map`) and the chain naturality (`chainOfMt_map`) identifies the chains; the ℝ side is
  `VvalGen` by `VvalGen_eq_sqSumHmat0`. The poly pivot is `Xvec eBlockPivot`, `eval u ↦ u eBlockPivot`.
* **the NONZERO witness `UPolyEfp ≠ 0`** — via the interior-drop witness `wInt M ha 1` (pivot at boundary
  `p = 1`): there `readE (wInt 1) ⟨0⟩ = EfixedReader (wInt 1)` (both are the `(0,0)`-pivot indicator), so the
  Efp decoder AT `wInt 1` is the plain `genBlkFlatLive ha 0 (wInt 1)`, and the surviving quotient entry
  `Hmat 0 (ρ, 0) = 1` is built by the SAME machinery (`Hmat_pivot`/`Hmat_row_thread`/`suffix_carrier`) as
  `achieverUfun_wInt_ne_zero`, on the `rfin = 0` decoder (the surviving entry is `Rfin`-blind).

Axiom-clean `[propext, Classical.choice, Quot.sound]` (no S2; the nullity is the elementary
`MvPolynomial.volume_zeroSet_eq_zero`).
-/

open scoped BigOperators
open MvPolynomial Matrix MeasureTheory

namespace DLNFibre.DLN.RLCT

variable {M : Fin (2 + 1) → ℕ}

/-! ## The polynomial E-fixed-pivot reader + decoder -/

/-- **The generic E-fixed-pivot reader** — the `CommRing`-generic `EfixedReader`: the pivot `(0,0)` entry
is the constant `1`, off `(0,0)` the coordinate `readE x ⟨0⟩`. Maps under `eval u` to `EfixedReader ha u`. -/
noncomputable def EfixedReaderGen (ha : StructAdm M (tach M)) {𝕜 : Type} [CommRing 𝕜]
    (x : Fin (routeMAmbient M) → 𝕜) :
    Matrix (Fin (Text M (tach M) (0 + 1) - Text M (tach M) (0 + 2)))
      (Fin (Wext M (0 + 1) - Text M (tach M) (0 + 2))) 𝕜 :=
  Matrix.of fun i j =>
    if i.val = 0 ∧ j.val = 0 then 1 else readE M (tach M) ha x ⟨0, by decide⟩ i j

/-- **The generic Efp reader maps to the ℝ one** under a ring hom `f` when `f (vp q) = vr q` for all `q`. -/
theorem EfixedReaderGen_map (ha : StructAdm M (tach M)) {𝕜 𝕜' : Type} [CommRing 𝕜] [CommRing 𝕜']
    (vp : Fin (routeMAmbient M) → 𝕜) (vr : Fin (routeMAmbient M) → 𝕜') (f : 𝕜 →+* 𝕜')
    (hv : ∀ q, f (vp q) = vr q) :
    Matrix.map (EfixedReaderGen ha vp) f = EfixedReaderGen ha vr := by
  ext i j
  simp only [Matrix.map_apply, EfixedReaderGen, Matrix.of_apply]
  split
  · exact map_one f
  · exact hv _

/-- **The generic Efp reader over ℝ is `EfixedReader`** (same formula). -/
theorem EfixedReaderGen_eq (ha : StructAdm M (tach M)) (x : Fin (routeMAmbient M) → ℝ) :
    EfixedReaderGen ha x = EfixedReader ha x := by
  ext i j
  simp only [EfixedReaderGen, EfixedReader, Matrix.of_apply]

/-- **The polynomial E-fixed-pivot decoder** `genBlkFlatEfpGen` — the generic `deepRank = 0` decoder over
any `CommRing`: `genBlkFlatLiveGen ha 0 x` with the pivot boundary `1`'s `Rmat` overridden (via
`Function.update`) to `rmatPad (EfixedReaderGen x)`. Mirrors `genBlkFlatEfp`. -/
noncomputable def genBlkFlatEfpGen (ha : StructAdm M (tach M))
    (hp1 : Text M (tach M) (1 + 1) ≤ Text M (tach M) 1) (hp2 : Text M (tach M) (1 + 1) ≤ Wext M 1)
    {𝕜 : Type} [CommRing 𝕜] (x : Fin (routeMAmbient M) → 𝕜) : GenBlk M (tach M) 𝕜 where
  Bmat := (genBlkFlatLiveGen M (tach M) ha 0 x).Bmat
  Nblk := (genBlkFlatLiveGen M (tach M) ha 0 x).Nblk
  Wblk := (genBlkFlatLiveGen M (tach M) ha 0 x).Wblk
  Rmat := Function.update (genBlkFlatLiveGen M (tach M) ha 0 x).Rmat 1
    (rmatPad M (tach M) 1 hp1 hp2 (EfixedReaderGen ha x)
      : Matrix (Fin (Text M (tach M) 1)) (Fin (Wext M 1)) 𝕜)
  Rfin := (genBlkFlatLiveGen M (tach M) ha 0 x).Rfin

/-- **The generic Efp decoder over ℝ is `genBlkFlatEfp`** (definitional — same fields). -/
theorem genBlkFlatEfpGen_eq_efp (ha : StructAdm M (tach M))
    (hp1 : Text M (tach M) (1 + 1) ≤ Text M (tach M) 1) (hp2 : Text M (tach M) (1 + 1) ≤ Wext M 1)
    (x : Fin (routeMAmbient M) → ℝ) :
    genBlkFlatEfpGen ha hp1 hp2 x = genBlkFlatEfp ha hp1 hp2 x := by
  unfold genBlkFlatEfpGen genBlkFlatEfp
  rw [genBlkFlatLiveGen_eq_live, EfixedReaderGen_eq]

/-! ## The Efp decoder's `GenBlkMap` (poly → ℝ under `eval u`) -/

/-- **The Efp decoder's `GenBlkMap`** under `eval`-related vectors `(vp, vr)`. The four
`Bmat/Nblk/Wblk/Rfin`-type fields are `genBlkFlatLiveGen`'s (via `genBlkFlatLiveGen_genBlkMap_of` with
`rfin = 0`); the `Rmat` field's `Function.update` at `1` splits by `k = 1`: off `1` it is the shared
`genBlkFlatLiveGen` `Rmat`, at `1` it is `rmatPad (EfixedReaderGen)` (natural via `rmatPad_map` +
`EfixedReaderGen_map`). -/
theorem genBlkFlatEfpGen_genBlkMap_of (ha : StructAdm M (tach M))
    (hp1 : Text M (tach M) (1 + 1) ≤ Text M (tach M) 1) (hp2 : Text M (tach M) (1 + 1) ≤ Wext M 1)
    {𝕜 𝕜' : Type} [CommRing 𝕜] [CommRing 𝕜']
    (vp : Fin (routeMAmbient M) → 𝕜) (vr : Fin (routeMAmbient M) → 𝕜') (f : 𝕜 →+* 𝕜')
    (hv : ∀ q, f (vp q) = vr q) :
    GenBlkMap M (tach M) (genBlkFlatEfpGen ha hp1 hp2 vp) (genBlkFlatEfpGen ha hp1 hp2 vr) f := by
  -- the base `genBlkFlatLiveGen` map (`rfin = 0` on both sides)
  have hbase : GenBlkMap M (tach M)
      (genBlkFlatLiveGen M (tach M) ha 0 vp) (genBlkFlatLiveGen M (tach M) ha 0 vr) f :=
    genBlkFlatLiveGen_genBlkMap_of M (tach M) ha vp vr f hv 0 0
      (by rw [Matrix.map_zero _ (map_zero _)])
  refine ⟨hbase.hBmat, hbase.hNblk, hbase.hWblk, ?_, hbase.hRfin⟩
  -- the `Rmat` field: `Function.update … 1 (rmatPad (EfixedReaderGen))` on both sides
  intro k
  change ((Function.update (genBlkFlatLiveGen M (tach M) ha 0 vp).Rmat 1
      (rmatPad M (tach M) 1 hp1 hp2 (EfixedReaderGen ha vp))) k).map f
    = (Function.update (genBlkFlatLiveGen M (tach M) ha 0 vr).Rmat 1
      (rmatPad M (tach M) 1 hp1 hp2 (EfixedReaderGen ha vr))) k
  by_cases hk : k = 1
  · subst hk
    rw [Function.update_self, Function.update_self, rmatPad_map,
      EfixedReaderGen_map ha vp vr f hv]
  · rw [Function.update_of_ne hk, Function.update_of_ne hk]
    exact hbase.hRmat k

/-! ## `UPolyEfp` + its evaluation -/

/-- **The named nonzero polynomial `UPolyEfp`** — `sqSumHmat0` of the POLYNOMIAL Efp decoder chain, at the
poly pivot `Xvec eBlockPivot`. `eval u UPolyEfp = VvalGen (u eBlockPivot) … (genBlkFlatEfp u) hle`. -/
noncomputable def UPolyEfp (ha : StructAdm M (tach M))
    (hr : 0 < Text M (tach M) 1 - Text M (tach M) 2) (hc : 0 < Wext M 1 - Text M (tach M) 2)
    (hp1 : Text M (tach M) (1 + 1) ≤ Text M (tach M) 1) (hp2 : Text M (tach M) (1 + 1) ≤ Wext M 1) :
    MvPolynomial (Fin (routeMAmbient M)) ℝ :=
  sqSumHmat0 (chainOfMt
    (Xvec (routeMAmbient M) (eBlockPivot ha hr hc)) M (tach M)
    (genBlkFlatEfpGen ha hp1 hp2 (Xvec (routeMAmbient M)))
    (hleStruct M (tach M) ha)).toChain

/-- **`eval u UPolyEfp = VvalGen (u eBlockPivot) … (genBlkFlatEfp u) hle`.** -/
theorem eval_UPolyEfp (ha : StructAdm M (tach M))
    (hr : 0 < Text M (tach M) 1 - Text M (tach M) 2) (hc : 0 < Wext M 1 - Text M (tach M) 2)
    (hp1 : Text M (tach M) (1 + 1) ≤ Text M (tach M) 1) (hp2 : Text M (tach M) (1 + 1) ≤ Wext M 1)
    (u : Fin (routeMAmbient M) → ℝ) :
    MvPolynomial.eval u (UPolyEfp ha hr hc hp1 hp2)
      = VvalGen (u (eBlockPivot ha hr hc)) M (tach M) (genBlkFlatEfp ha hp1 hp2 u)
          (hleStruct M (tach M) ha) := by
  -- the Efp `GenBlkMap` for `eval u` (poly `Xvec` decoder → ℝ `u` decoder)
  have hmap : GenBlkMap M (tach M)
      (genBlkFlatEfpGen ha hp1 hp2 (Xvec (routeMAmbient M)))
      (genBlkFlatEfpGen ha hp1 hp2 u) (MvPolynomial.eval u) :=
    genBlkFlatEfpGen_genBlkMap_of ha hp1 hp2 (Xvec (routeMAmbient M)) u (MvPolynomial.eval u)
      (eval_Xvec u)
  -- the chain naturality (poly pivot kept SYMBOLIC), then the pivot `eval u (Xvec p) = u p`
  have hchain := chainOfMt_map hmap
    (Xvec (routeMAmbient M) (eBlockPivot ha hr hc)) (hleStruct M (tach M) ha)
  rw [VvalGen_eq_sqSumHmat0, ← genBlkFlatEfpGen_eq_efp ha hp1 hp2 u, UPolyEfp,
    sqSumHmat0_map _ (MvPolynomial.eval u), hchain, eval_Xvec u]

/-! ## The nonzero witness -/

/-- At the interior-drop witness `wInt M ha 1` the E-fixed-pivot reader IS `readE (wInt 1) ⟨0⟩`: both are
the `(0,0)`-pivot indicator (`EfixedReader` pins `(0,0) ↦ 1` and reads `readE` elsewhere; `readE (wInt 1)`
is the pivot indicator at boundary `p = 1`, so `(0,0) ↦ 1`, else `0`). -/
theorem EfixedReader_wInt1 (ha : StructAdm M (tach M)) :
    EfixedReader ha (wInt M ha 1) = readE M (tach M) ha (wInt M ha 1) ⟨0, by decide⟩ := by
  ext i j
  rw [EfixedReader, Matrix.of_apply, readE_wInt]
  by_cases hij : i.val = 0 ∧ j.val = 0
  · rw [if_pos hij, if_pos ⟨rfl, hij.1, hij.2⟩]
  · rw [if_neg hij, if_neg (fun h => hij ⟨h.2.1, h.2.2⟩)]

/-- **At the witness `wInt 1` the Efp decoder IS the plain `genBlkFlatLive ha 0 (wInt 1)`** — the pivot
`Rmat`-override collapses (the `Function.update` value equals the underlying `Rmat 1`, since
`EfixedReader (wInt 1) = readE (wInt 1) ⟨0⟩`). -/
theorem genBlkFlatEfp_wInt1 (ha : StructAdm M (tach M))
    (hp1 : Text M (tach M) (1 + 1) ≤ Text M (tach M) 1) (hp2 : Text M (tach M) (1 + 1) ≤ Wext M 1) :
    genBlkFlatEfp ha hp1 hp2 (wInt M ha 1) = genBlkFlatLive M (tach M) ha 0 (wInt M ha 1) := by
  have hRmat1 : rmatPad M (tach M) 1 hp1 hp2 (EfixedReader ha (wInt M ha 1))
      = (genBlkFlatLive M (tach M) ha 0 (wInt M ha 1)).Rmat 1 := by
    rw [EfixedReader_wInt1 ha]
    change rmatPad M (tach M) 1 hp1 hp2 (readE M (tach M) ha (wInt M ha 1) ⟨0, by decide⟩)
      = (genBlkFlatStruct M (tach M) ha (wInt M ha 1)).Rmat 1
    rfl
  -- unfold `genBlkFlatEfp` to the `GenBlk.mk` (only `Rmat` overridden via `Function.update`); the update
  -- collapses (value = underlying `Rmat 1`), leaving the `genBlkFlatLive` structure by eta.
  unfold genBlkFlatEfp
  rw [hRmat1, Function.update_eq_self]

/-- **The Efp unit is nonzero at the interior-drop witness `wInt M ha 1`.** At `p = 1` the Efp decoder
coincides with the plain `genBlkFlatLive ha 0 (wInt 1)` (`readE (wInt 1) ⟨0⟩ = EfixedReader (wInt 1)`, both
the `(0,0)` pivot indicator), and the surviving quotient entry `Hmat 0 (ρ, 0) = 1` is built by the
`achieverUfun_wInt_ne_zero` machinery on the `rfin = 0` decoder. -/
theorem eDeepRank0Unit_wInt_ne_zero (ha : StructAdm M (tach M)) (hdr0 : Text M (tach M) 2 = 0)
    (hr : 0 < Text M (tach M) 1 - Text M (tach M) 2) (hc : 0 < Wext M 1 - Text M (tach M) 2)
    (hp1 : Text M (tach M) (1 + 1) ≤ Text M (tach M) 1) (hp2 : Text M (tach M) (1 + 1) ≤ Wext M 1)
    (hM2 : 0 < Wext M 2) :
    VvalGen (wInt M ha 1 (eBlockPivot ha hr hc)) M (tach M)
        (genBlkFlatEfp ha hp1 hp2 (wInt M ha 1)) (hleStruct M (tach M) ha) ≠ 0 := by
  -- at `p = 1` the Efp decoder IS the plain `genBlkFlatLive ha 0 (wInt 1)`; reduce to `sqSumHmat0`
  rw [genBlkFlatEfp_wInt1 ha hp1 hp2, VvalGen_eq_sqSumHmat0]
  set hle := hleStruct M (tach M) ha with hledef
  set u := wInt M ha 1 (eBlockPivot ha hr hc) with hudef
  set B := genBlkFlatLive M (tach M) ha 0 (wInt M ha 1) with hBdef
  set c := (chainOfMt u M (tach M) B hle).toChain with hcdef
  -- the interior-drop data at pivot `p = 1` (`kp = 0`, `L = 2`)
  have hpL : (1 : ℕ) < 2 := by decide
  have hr' : Text M (tach M) 2 < Text M (tach M) 1 := by omega
  have hcd : ∀ b, 1 ≤ b → b < 2 → Text M (tach M) (b + 1) < Wext M b := by
    intro b hb1 hbL
    obtain rfl : b = 1 := by omega
    rw [show (1 : ℕ) + 1 = 2 from rfl]; omega
  -- the descent facts (verbatim from `interiorLiveUnit_wInt_ne_zero`, specialized to `p = 1`)
  have hTdesc : ∀ s, s < 1 → Text M (tach M) (s + 1) ≤ Text M (tach M) s := by
    intro s hsp
    obtain rfl : s = 0 := by omega
    exact le_of_eq (Text0_eq_Text1_struct M (tach M) ha.h0).symm
  have hρlt : ∀ s, s < 1 → Text M (tach M) (1 + 1) < Text M (tach M) (s + 1) := by
    intro s hsp
    obtain rfl : s = 0 := by omega
    rw [show (1 : ℕ) + 1 = 2 from rfl, show (0 : ℕ) + 1 = 1 from rfl]
    exact hr'
  have hsurvW : ∀ s, 1 ≤ s → s ≤ 2 → survRowVal M (tach M) s < Wext M s := by
    intro s hps hsL
    by_cases hsl : s = 2
    · subst hsl; simpa [survRowVal] using hM2
    · simp only [survRowVal, if_neg hsl]; exact hcd s hps (by omega)
  -- the live decoder's `Wblk`/`Bmat`/`Rmat` ARE the struct decoder's (definitional `rfl`)
  have hWblk : ∀ k, B.Wblk k = (genBlkFlatStruct M (tach M) ha (wInt M ha 1)).Wblk k := fun _ => rfl
  -- (I-suffix) carrier survival
  have hsuffix : ∀ s, 1 ≤ s → ∀ (r : Fin (Wext M s)), r.val = survRowVal M (tach M) s →
      ∀ (hsL : s ≤ 2), c.suffix s hsL r ⟨0, hM2⟩ = 1 := by
    intro s hps r hr'' hsL
    refine suffix_carrier hM2 (fun s' hps' hs' r' hr''' c' => ?_) hsurvW (2 - s) s (by omega) hps r hr''
    have hcds' : 0 < Wext M s' - Text M (tach M) (s' + 1) := by
      have := hcd s' hps' (by omega)
      simp only [survRowVal, if_neg (by omega : s' ≠ 2)] at hr'''; omega
    have hrlift : r' = liftRow M (tach M) hle s' hs' ⟨0, hcds'⟩ := by
      apply Fin.ext
      simp only [liftRow, Fin.val_cast, Fin.val_natAdd, hr''']
      simp only [survRowVal, if_neg (by omega : s' ≠ 2), Nat.add_zero]
    rw [hrlift, chain_A_liftRow s' hs' _ c']
    obtain ⟨k, rfl⟩ : ∃ k, s' = k + 1 := ⟨s' - 1, by omega⟩
    change B.Wblk (k + 1) _ c' = _
    rw [hWblk, show (genBlkFlatStruct M (tach M) ha (wInt M ha 1)).Wblk (k + 1)
          = (if hk : k < 2 then (if hk2 : k + 1 < 2 then
              readW M (tach M) ha (wInt M ha 1) ⟨k, hk⟩ hk2 else 0) else 0) from rfl,
      dif_pos (by omega), dif_pos hs', readW_wInt]
    simp only [survCol, survRowVal, true_and]
    rfl
  -- the pivot boundary `p = 0 + 1`
  have hkpL : (0 : ℕ) < 2 := by decide
  have hr2 : Text M (tach M) (0 + 2) < Text M (tach M) (0 + 1) := hr'
  have hcd2 : Text M (tach M) (0 + 2) < Wext M (0 + 1) := hcd 1 (le_refl _) hpL
  set ρcast : Fin (Text M (tach M) (0 + 1)) :=
    Fin.cast (show Text M (tach M) (0 + 2) + (Text M (tach M) (0 + 1) - Text M (tach M) (0 + 2))
        = Text M (tach M) (0 + 1) by omega) (Fin.natAdd _ ⟨0, by omega⟩) with hρcastdef
  set colP : Fin (Wext M (0 + 1)) :=
    Fin.cast (show Text M (tach M) (0 + 2) + (Wext M (0 + 1) - Text M (tach M) (0 + 2))
        = Wext M (0 + 1) by omega) (Fin.natAdd _ ⟨0, by omega⟩) with hcolPdef
  have hcolPval : colP.val = survRowVal M (tach M) (0 + 1) := by
    simp only [hcolPdef, Fin.val_cast, Fin.val_natAdd, Nat.add_zero, survRowVal,
      if_neg (by omega : 0 + 1 ≠ 2)]
  -- (I-base) `Hmat 1 (ρ, 0) = 1` (the pivot value)
  have hpivot : c.Hmat (0 + 1) (le_of_lt hpL) ρcast ⟨0, hM2⟩ = 1 := by
    refine Hmat_pivot hpL hM2 colP ρcast ?_ ?_ ?_
    · intro j
      exact genBlk_Bmat_succ_bot ha (0 + 1) 0 hkpL ⟨0, by omega⟩ j
    · intro cc
      exact genBlk_Rmat_pivot ha 0 hkpL hr2 hcd2 cc
    · exact hsuffix (0 + 1) (le_refl _) colP hcolPval (le_of_lt hpL)
  have hρT : ∀ s, s ≤ 0 + 1 → Text M (tach M) (0 + 1 + 1) < Text M (tach M) s := by
    intro s hs
    have hle' : Text M (tach M) (0 + 1) ≤ Text M (tach M) s := by
      match s with
      | 0 => exact le_of_eq (Text0_eq_Text1_struct M (tach M) ha.h0).symm
      | 1 => exact le_refl _
    exact lt_of_lt_of_le hr2 hle'
  -- the live `E s = 0` for `s < 1` (`Rmat s = 0` shared with struct)
  have hEzero : ∀ s, s < 0 + 1 → c.E s = 0 := by
    intro s hs
    change B.Rmat s * Agen u M (tach M) B hle s = 0
    have hRz : B.Rmat s = 0 := by
      change (genBlkFlatStruct M (tach M) ha (wInt M ha 1)).Rmat s = 0
      obtain rfl : s = 0 := by omega
      rfl
    rw [hRz, Matrix.zero_mul]
  -- (I-up) thread the row up to `0`
  have hHmat0 : c.Hmat 0 (Nat.zero_le 2) (rhoAt M (tach M) (0 + 1) 0 (hρT 0 (by omega)))
      ⟨0, hM2⟩ = 1 := by
    refine Hmat_row_thread (B := B) hpL hM2 hρT (fun s hs => hTdesc s (by omega))
      ?_ (fun s hs => hEzero s hs) (fun s hs => hρlt s (by omega)) ?_ (0 + 1) 0 (by omega)
    · convert hpivot using 2
    · intro s hsp a j
      obtain rfl : s = 0 := by omega
      exact genBlk_Bmat_zero_top ha (0 + 1) a j _
  exact sqSumHmat0_ne_zero_of_entry c (rhoAt M (tach M) (0 + 1) 0 (hρT 0 (by omega)))
    ⟨0, hM2⟩ hHmat0

/-- **`UPolyEfp ≠ 0`** — from the witness `eDeepRank0Unit_wInt_ne_zero` via `eval_UPolyEfp`. -/
theorem UPolyEfp_ne_zero (ha : StructAdm M (tach M)) (hdr0 : Text M (tach M) 2 = 0)
    (hr : 0 < Text M (tach M) 1 - Text M (tach M) 2) (hc : 0 < Wext M 1 - Text M (tach M) 2)
    (hp1 : Text M (tach M) (1 + 1) ≤ Text M (tach M) 1) (hp2 : Text M (tach M) (1 + 1) ≤ Wext M 1)
    (hM2 : 0 < Wext M 2) :
    UPolyEfp ha hr hc hp1 hp2 ≠ 0 := by
  intro h0
  refine eDeepRank0Unit_wInt_ne_zero ha hdr0 hr hc hp1 hp2 hM2 ?_
  rw [← eval_UPolyEfp ha hr hc hp1 hp2 (wInt M ha 1), h0, map_zero]

/-! ## The a.e.-positivity atom (the item-6 deliverable) -/

/-- **Item 6: a.e.-positivity of the `deepRank = 0` unit factor** —
`∀ᵐ u, 0 < VvalGen (u eBlockPivot) M (tach M) (genBlkFlatEfp ha hp1 hp2 u) hle`. Via `eval_UPolyEfp`
(`unit = eval · UPolyEfp`) + `MvPolynomial.ae_eval_ne_zero` (`UPolyEfp ≠ 0` ⟹ the zero set is null) +
`VvalGen_nonneg` (`≠ 0 ⟹ > 0`). -/
theorem eDeepRank0Unit_ae_pos (ha : StructAdm M (tach M))
    (hdr0 : Text M (tach M) 2 = 0)
    (hr : 0 < Text M (tach M) 1 - Text M (tach M) 2) (hc : 0 < Wext M 1 - Text M (tach M) 2)
    (hp1 : Text M (tach M) (1 + 1) ≤ Text M (tach M) 1) (hp2 : Text M (tach M) (1 + 1) ≤ Wext M 1)
    (hM2 : 0 < Wext M 2) :
    ∀ᵐ u, 0 < VvalGen (u (eBlockPivot ha hr hc)) M (tach M)
      (genBlkFlatEfp ha hp1 hp2 u) (hleStruct M (tach M) ha) := by
  have hae := MvPolynomial.ae_eval_ne_zero _ (UPolyEfp_ne_zero ha hdr0 hr hc hp1 hp2 hM2)
  filter_upwards [hae] with u hu
  rw [← eval_UPolyEfp ha hr hc hp1 hp2 u] at *
  refine lt_of_le_of_ne ?_ (Ne.symm hu)
  rw [eval_UPolyEfp ha hr hc hp1 hp2 u]
  exact VvalGen_nonneg _ M (tach M) _ _

end DLNFibre.DLN.RLCT
