import DLNFibre.DLN.RLCT.Validate.RouteMKLens

/-!
# `RouteMFlatLive` — the LIVE-leaf structured achiever decoder + its decoder-agnostic rate (∀M)

The DET-route decoder for the interior branch. The radial-separability certificate + the verified
`(3,3,3,3)` monomial det `|u0|^5·|u1|^4·|u4|^2·|u9|^3` are for the LIVE-leaf `B_det` family (`Rfin ≠ 0`,
the leaf block FREE); the dead-leaf `genBlkFlatStruct` (`Rfin := 0`) gives the WRONG radial exponent
`q = #interior-E-blocks ≠ minAdm − 1` (Codex-confirmed: at `(3,3,3,3)`, `q = 3` but `minAdm − 1 = 5`). So
the interior chart's determinant genuinely needs the live leaf. See `threads/80-genM-nodechart/`
`item3-2b-deadleaf-gap.md` (the decision-A refinement) + `codex/liveleaf-budget-{prompt,answer}.md`.

**This module banks the NO-REGRET part** (independent of the budget cardinality `#angular = minAdm − 1`,
which the parallel `genm-budget` pen-and-paper adjudicates): the live-leaf decoder + the decoder-agnostic
rate. `genBlkFlatLive M t ha rfin x` is the structured decoder with the leaf residual `Rfin L := rfin`
made LIVE (a free leaf block, read from `x` — the SPECIFIC slot-rerouting reader is the deferred budget
piece). The identity boundary is UNCHANGED from `genBlkFlatStruct` (`Bmat 0 = reindex 1`, `Rmat 0 = 0`),
so the decoder-agnostic rate engine (`routeMCore_phiGen` + `hC0_struct_gen`) fires verbatim:

  `routeMCore (phiFlatLive M t ha hN rfin x) = (x p)² · UvalLive …`.

Sub-tides 1+2a (`phiFlatLDU`/`kLDU`, `RouteMFlatLDU`/`RouteMKLens`) are decoder-agnostic; here they are
re-instantiated on the live decoder. The budget identity (`#angular = minAdm − 1` + square-chart for the
rerouted layout) is DEFERRED — it is the determinant-side cardinality, not the rate.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (matrix algebra; the rate engine, no analysis).
-/

open Matrix
open scoped BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The live-leaf structured decoder (structured decoder + a free leaf `Rfin`) -/

/-- **The LIVE-leaf structured decoder** `genBlkFlatLive M t ha rfin x` — the dead-leaf
`genBlkFlatStruct M t ha x` with the leaf residual `Rfin L` made LIVE: `Rfin k := if k = L then rfin
else 0`. The interior blocks (`Bmat`/`Nblk`/`Wblk`/`Rmat`) and the identity boundary are UNCHANGED, so
`Bmat 0 = reindex 1`, `Rmat 0 = 0` (the rate's identity-boundary precondition) hold verbatim. The leaf
block `rfin` is the free leaf coordinate matrix; the SPECIFIC reader (which `x`-slots feed `rfin` + the
interior-pivot fixing) is the deferred budget piece. -/
noncomputable def genBlkFlatLive (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (rfin : Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (x : Fin (routeMAmbient M) → ℝ) : GenBlk M t where
  Bmat := (genBlkFlatStruct M t ha x).Bmat
  Nblk := (genBlkFlatStruct M t ha x).Nblk
  Wblk := (genBlkFlatStruct M t ha x).Wblk
  Rmat := (genBlkFlatStruct M t ha x).Rmat
  Rfin := fun k => if h : k = L then h ▸ rfin else 0

/-- The live decoder's identity boundary matches the dead one: `Bmat 0 = reindex 1`, `Rmat 0 = 0`
(both `rfl` — they are the structured decoder's, unchanged). -/
theorem genBlkFlatLive_Bmat0 (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (rfin : Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ) (x : Fin (routeMAmbient M) → ℝ) :
    (genBlkFlatLive M t ha rfin x).Bmat 0 = (genBlkFlatStruct M t ha x).Bmat 0 := rfl

theorem genBlkFlatLive_Rmat0 (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (rfin : Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ) (x : Fin (routeMAmbient M) → ℝ) :
    (genBlkFlatLive M t ha rfin x).Rmat 0 = (genBlkFlatStruct M t ha x).Rmat 0 := rfl

/-! ## The identity-boundary `hC0` for the live decoder (verbatim from the structured proof) -/

/-- **The identity boundary `C 0 = 1`** for the live decoder — the `C0_eq_one_gen` proof reads ONLY
`Bmat 0`/`Rmat 0` (both unchanged from the structured decoder), so it holds verbatim. -/
theorem C0_eq_one_live (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (rfin : Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (v : ℝ) (x : Fin (routeMAmbient M) → ℝ) :
    (chainOfMt v M t (genBlkFlatLive M t ha rfin x) (hleStruct M t ha)).toChain.C 0
      = (1 : Matrix (Fin (Text M t 0)) (Fin (Text M t 0)) ℝ) := by
  rw [chainOfMt_C_zero v M t _ (hleStruct M t ha) ha.hL,
    show (genBlkFlatLive M t ha rfin x).Rmat 0 = 0 from rfl, smul_zero, add_zero]
  have hBmat : (genBlkFlatLive M t ha rfin x).Bmat 0
      = Matrix.reindex (Equiv.refl _) (finCongr (Text0_eq_Text1_struct M t ha.h0))
          (1 : Matrix (Fin (Text M t 0)) (Fin (Text M t 0)) ℝ) := rfl
  have h1W : Text M t 1 = Wext M 0 := Wext0_eq_Text1 M t ha
  rw [hBmat]
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.cast (Text0_eq_Text1_struct M t ha.h0) i)]
  · rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.refl_apply,
      finCongr_symm, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self, Matrix.one_apply_eq, one_mul]
    have hjcol : (j : Fin (Wext M 0)) = Fin.cast (genWidthEq M t (hleStruct M t ha) 0 ha.hL)
        (Fin.castAdd (Wext M 0 - Text M t (0 + 1)) (Fin.cast h1W.symm j)) := by
      apply Fin.ext; simp
    rw [hjcol, chainQ_apply_castAdd, Matrix.one_apply, Matrix.one_apply]
    by_cases h : (i : ℕ) = (j : ℕ)
    · rw [if_pos (by apply Fin.ext; simpa using h), if_pos (by apply Fin.ext; simpa using h)]
    · rw [if_neg (by intro hc; exact h (by simpa using congrArg Fin.val hc)),
        if_neg (by intro hc; exact h (by simpa using congrArg Fin.val hc))]
  · intro b _ hb
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.refl_apply,
      finCongr_symm, finCongr_apply]
    rw [show (1 : Matrix (Fin (Text M t 0)) (Fin (Text M t 0)) ℝ) i
          (Fin.cast (Text0_eq_Text1_struct M t ha.h0).symm b) = 0 from by
      rw [Matrix.one_apply, if_neg]; intro hc; apply hb; rw [hc]; apply Fin.ext; simp]
    rw [zero_mul]
  · intro hi; exact absurd (Finset.mem_univ _) hi

/-- **`hC0` for the live decoder** (`C 0 · suffix 0 = suffix 0` from `C 0 = 1`). -/
theorem hC0_live (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (rfin : Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (v : ℝ) (x : Fin (routeMAmbient M) → ℝ) :
    (chainOfMt v M t (genBlkFlatLive M t ha rfin x) (hleStruct M t ha)).toChain.C 0
        * (chainOfMt v M t (genBlkFlatLive M t ha rfin x)
            (hleStruct M t ha)).toChain.suffix 0 (Nat.zero_le L)
      = (chainOfMt v M t (genBlkFlatLive M t ha rfin x)
          (hleStruct M t ha)).toChain.suffix 0 (Nat.zero_le L) := by
  rw [C0_eq_one_live M t ha rfin v x]; exact Matrix.one_mul _

/-! ## The live-leaf chart + its decoder-agnostic rate -/

/-- **The LIVE-leaf structured achiever chart** `phiFlatLive M t ha hN rfin x := phiGen (x p) M t
(genBlkFlatLive M t ha (rfin x) x) hle`, where the leaf block `rfin x` may itself read from `x` (the
free leaf coordinates). The radial scalar is read from the ORIGINAL `x` at the pivot `p`. -/
noncomputable def phiFlatLive (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (hN : 0 < routeMAmbient M)
    (rfin : (Fin (routeMAmbient M) → ℝ) → Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (x : Fin (routeMAmbient M) → ℝ) : Fin (routeMAmbient M) → ℝ :=
  phiGen (x (structPivot M hN)) M t (genBlkFlatLive M t ha (rfin x) x) (hleStruct M t ha)

/-- **The LIVE-leaf unit factor** `UvalLive … := VvalGen (x p) M t (genBlkFlatLive …) hle`. -/
noncomputable def UvalLive (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (hN : 0 < routeMAmbient M)
    (rfin : (Fin (routeMAmbient M) → ℝ) → Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (x : Fin (routeMAmbient M) → ℝ) : ℝ :=
  VvalGen (x (structPivot M hN)) M t (genBlkFlatLive M t ha (rfin x) x) (hleStruct M t ha)

/-- **The rate transfers to the LIVE-leaf chart ∀M (NO bridge)**: `routeMCore M (phiFlatLive rfin x) =
(x p)² · UvalLive rfin x`. Decoder-agnostic: `routeMCore_phiGen` + the live identity-boundary `hC0_live`
(which holds verbatim — the identity boundary is unchanged from the structured decoder). -/
theorem routeMCore_phiFlatLive (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (hN : 0 < routeMAmbient M)
    (rfin : (Fin (routeMAmbient M) → ℝ) → Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (x : Fin (routeMAmbient M) → ℝ) :
    routeMCore M (phiFlatLive M t ha hN rfin x)
      = (x (structPivot M hN)) ^ 2 * UvalLive M t ha hN rfin x :=
  routeMCore_phiGen (x (structPivot M hN)) M t (genBlkFlatLive M t ha (rfin x) x)
    (hleStruct M t ha)
    (hC0_live M t ha (rfin x) (x (structPivot M hN)) x)

/-- **`0 ≤ UvalLive`** — sum of squares (banked `VvalGen_nonneg`). -/
theorem UvalLive_nonneg (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (hN : 0 < routeMAmbient M)
    (rfin : (Fin (routeMAmbient M) → ℝ) → Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (x : Fin (routeMAmbient M) → ℝ) :
    0 ≤ UvalLive M t ha hN rfin x :=
  VvalGen_nonneg _ M t _ _

/-- **Non-vacuity of the live rate**: with `rfin = fun _ => 0`, `routeMCore_phiFlatLive` gives the
`(x p)²·UvalLive` rate on the leaf-killed decoder (the rate is genuinely transferred to the live chart,
not vacuous; the `rfin = 0` leaf is the dead-leaf reduction). -/
example (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (hN : 0 < routeMAmbient M)
    (x : Fin (routeMAmbient M) → ℝ) :
    routeMCore M (phiFlatLive M t ha hN (fun _ => 0) x)
      = (x (structPivot M hN)) ^ 2 * UvalLive M t ha hN (fun _ => 0) x :=
  routeMCore_phiFlatLive M t ha hN (fun _ => 0) x

end DLNFibre.DLN.RLCT
