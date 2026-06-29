import DLNFibre.DLN.RLCT.Validate.RouteMKLens
import DLNFibre.DLN.RLCT.Validate.RouteMAchieverWitnessInterior

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

/-! ## The R1 active-center decoder: fixed-1 pivot at `p*` + freed-slot live `Rfin`

The DET-route decoder (R1, controller-confirmed): the structured decoder with the active-center pivot
boundary `p` (the witness's deepest drop `p*`, `InteriorDrop`) carrying a FIXED `1`-pivot
`E_{p}(0,0) = 1` (the gauge-fixed radial direction, a literal — not a free `readE`), and the freed
pivot-slot's budget rerouted to a live leaf `Rfin`. The slot-guard verdict (verified vs `B_det3333`):
this relocates WHICH slot is the fixed-1 (the pivot E-slot → fixed; its coordinate reroutes to `Rfin`),
keeping `N = flatDim` (the `chartDim_eq_flatDim` "+1 radial −1 fixed residual" accounting) — NO new
Fin-N bijection. The identity boundary is unchanged, so the rate holds decoder-agnostically. -/

/-- **The fixed pivot E-indicator** at boundary `s` — `e_{(0,0)}`: `1` at the first residual row/col,
`0` elsewhere (the gauge-fixed radial direction the `u·Rmat` blow-up targets). -/
def pivotEIndicator (M t : Fin (L + 1) → ℕ) (s : ℕ) :
    Matrix (Fin (Text M t s - Text M t (s + 1))) (Fin (Wext M s - Text M t (s + 1))) ℝ :=
  Matrix.of fun i j => if i.val = 0 ∧ j.val = 0 then 1 else 0

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

/-! ## The R1 active-center decoder `genBlkFlatLiveR1` -/

/-- **The R1 active-center decoder** `genBlkFlatLiveR1 M t ha p hp rfin x` — the live decoder
`genBlkFlatLive` with the `Rmat` at the active-center pivot boundary `p` OVERRIDDEN to the fixed
`1`-pivot `rmatPad (pivotEIndicator)` (the gauge-fixed radial direction), via `Function.update` on the
`ℕ`-indexed `Rmat` family (no dependent-Fin cast — `p : ℕ`, the updated value is at the exact
`Matrix (Fin (Text p)) (Fin (Wext p)) ℝ` type). The pivot needs the row/col drops `Text(p+1) ≤ Text p`,
`Text(p+1) ≤ Wext p` (`hp` — from `InteriorDrop`'s `p*`). All other blocks (incl the identity boundary
`Rmat 0`, untouched since `p ≥ 1`) and the live leaf `rfin` are as in `genBlkFlatLive`. -/
noncomputable def genBlkFlatLiveR1 (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (p : ℕ)
    (hp1 : Text M t (p + 1) ≤ Text M t p) (hp2 : Text M t (p + 1) ≤ Wext M p)
    (rfin : Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (x : Fin (routeMAmbient M) → ℝ) : GenBlk M t where
  Bmat := (genBlkFlatLive M t ha rfin x).Bmat
  Nblk := (genBlkFlatLive M t ha rfin x).Nblk
  Wblk := (genBlkFlatLive M t ha rfin x).Wblk
  Rmat := Function.update (genBlkFlatLive M t ha rfin x).Rmat p
    (rmatPad M t p hp1 hp2 (pivotEIndicator M t p))
  Rfin := (genBlkFlatLive M t ha rfin x).Rfin

/-- The R1 decoder's `Rmat` at the pivot `p` IS the fixed `1`-pivot pad (`Function.update` hit). -/
theorem genBlkFlatLiveR1_Rmat_pivot (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (p : ℕ)
    (hp1 : Text M t (p + 1) ≤ Text M t p) (hp2 : Text M t (p + 1) ≤ Wext M p)
    (rfin : Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ) (x : Fin (routeMAmbient M) → ℝ) :
    (genBlkFlatLiveR1 M t ha p hp1 hp2 rfin x).Rmat p
      = rmatPad M t p hp1 hp2 (pivotEIndicator M t p) :=
  Function.update_self ..

/-- The R1 decoder's identity boundary `Rmat 0 = 0` (untouched: `Function.update` at `p ≥ 1` misses `0`).
Needs `p ≠ 0` (the pivot is interior, `1 ≤ p`). -/
theorem genBlkFlatLiveR1_Rmat0 (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (p : ℕ) (hp0 : p ≠ 0)
    (hp1 : Text M t (p + 1) ≤ Text M t p) (hp2 : Text M t (p + 1) ≤ Wext M p)
    (rfin : Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ) (x : Fin (routeMAmbient M) → ℝ) :
    (genBlkFlatLiveR1 M t ha p hp1 hp2 rfin x).Rmat 0
      = (0 : Matrix (Fin (Text M t 0)) (Fin (Wext M 0)) ℝ) := by
  show Function.update (genBlkFlatLive M t ha rfin x).Rmat p _ 0 = _
  rw [Function.update_of_ne (Ne.symm hp0)]
  rfl

/-- **The identity boundary `C 0 = 1`** for the R1 decoder — reads only `Bmat 0`/`Rmat 0`, both unchanged
(`Bmat 0` is the live decoder's; `Rmat 0 = 0` since `p ≥ 1` misses the update). Proof verbatim from
`C0_eq_one_live` (the `Bmat 0` is identical; `Rmat 0 = 0` via `genBlkFlatLiveR1_Rmat0`). -/
theorem C0_eq_one_liveR1 (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (p : ℕ) (hp0 : p ≠ 0)
    (hp1 : Text M t (p + 1) ≤ Text M t p) (hp2 : Text M t (p + 1) ≤ Wext M p)
    (rfin : Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (v : ℝ) (x : Fin (routeMAmbient M) → ℝ) :
    (chainOfMt v M t (genBlkFlatLiveR1 M t ha p hp1 hp2 rfin x) (hleStruct M t ha)).toChain.C 0
      = (1 : Matrix (Fin (Text M t 0)) (Fin (Text M t 0)) ℝ) := by
  rw [chainOfMt_C_zero v M t _ (hleStruct M t ha) ha.hL,
    genBlkFlatLiveR1_Rmat0 M t ha p hp0 hp1 hp2 rfin x, smul_zero, add_zero]
  have hBmat : (genBlkFlatLiveR1 M t ha p hp1 hp2 rfin x).Bmat 0
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

/-- **`hC0` for the R1 decoder** (`C 0 · suffix = suffix` from `C 0 = 1`). -/
theorem hC0_liveR1 (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (p : ℕ) (hp0 : p ≠ 0)
    (hp1 : Text M t (p + 1) ≤ Text M t p) (hp2 : Text M t (p + 1) ≤ Wext M p)
    (rfin : Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (v : ℝ) (x : Fin (routeMAmbient M) → ℝ) :
    (chainOfMt v M t (genBlkFlatLiveR1 M t ha p hp1 hp2 rfin x) (hleStruct M t ha)).toChain.C 0
        * (chainOfMt v M t (genBlkFlatLiveR1 M t ha p hp1 hp2 rfin x)
            (hleStruct M t ha)).toChain.suffix 0 (Nat.zero_le L)
      = (chainOfMt v M t (genBlkFlatLiveR1 M t ha p hp1 hp2 rfin x)
          (hleStruct M t ha)).toChain.suffix 0 (Nat.zero_le L) := by
  rw [C0_eq_one_liveR1 M t ha p hp0 hp1 hp2 rfin v x]; exact Matrix.one_mul _

/-- **The R1 active-center chart** `phiFlatLiveR1 … := phiGen (x p₀) M t (genBlkFlatLiveR1 …) hle`
(`p₀ = structPivot`, the radial scalar). The pivot boundary `p` (active center) carries the fixed
`1`-pivot; the radial is read from `x` at `p₀`. -/
noncomputable def phiFlatLiveR1 (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (hN : 0 < routeMAmbient M) (p : ℕ)
    (hp1 : Text M t (p + 1) ≤ Text M t p) (hp2 : Text M t (p + 1) ≤ Wext M p)
    (rfin : (Fin (routeMAmbient M) → ℝ) → Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (x : Fin (routeMAmbient M) → ℝ) : Fin (routeMAmbient M) → ℝ :=
  phiGen (x (structPivot M hN)) M t (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x) (hleStruct M t ha)

/-- **The R1 active-center chart at an ARBITRARY radial slot `p₀`**
`phiFlatLiveR1At … p₀ … := phiGen (x p₀) M t (genBlkFlatLiveR1 …) hle`. Identical to
`phiFlatLiveR1` but reads the radial scalar at the supplied slot `p₀` rather than the hard-wired
`structPivot M hN = ⟨0,_⟩`. Frees the achiever node to put the radial axis on a reader-complement
slot (the `PivotNotReader`-free chart construction): `phiFlatLiveR1 = phiFlatLiveR1At (structPivot)`
(`phiFlatLiveR1At_structPivot`). The pivot boundary `p` (active center) carries the fixed `1`-pivot
exactly as before — only the radial *read slot* moves. -/
noncomputable def phiFlatLiveR1At (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (p : ℕ) (hp1 : Text M t (p + 1) ≤ Text M t p) (hp2 : Text M t (p + 1) ≤ Wext M p)
    (p₀ : Fin (routeMAmbient M))
    (rfin : (Fin (routeMAmbient M) → ℝ) → Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (x : Fin (routeMAmbient M) → ℝ) : Fin (routeMAmbient M) → ℝ :=
  phiGen (x p₀) M t (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x) (hleStruct M t ha)

/-- `phiFlatLiveR1` is `phiFlatLiveR1At` at the default radial slot `structPivot M hN`. -/
theorem phiFlatLiveR1At_structPivot (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (hN : 0 < routeMAmbient M) (p : ℕ)
    (hp1 : Text M t (p + 1) ≤ Text M t p) (hp2 : Text M t (p + 1) ≤ Wext M p)
    (rfin : (Fin (routeMAmbient M) → ℝ) → Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ) :
    phiFlatLiveR1 M t ha hN p hp1 hp2 rfin
      = phiFlatLiveR1At M t ha p hp1 hp2 (structPivot M hN) rfin := rfl

/-- **The R1 unit factor** `UvalLiveR1 … := VvalGen (x p₀) M t (genBlkFlatLiveR1 …) hle`. -/
noncomputable def UvalLiveR1 (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (hN : 0 < routeMAmbient M) (p : ℕ)
    (hp1 : Text M t (p + 1) ≤ Text M t p) (hp2 : Text M t (p + 1) ≤ Wext M p)
    (rfin : (Fin (routeMAmbient M) → ℝ) → Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (x : Fin (routeMAmbient M) → ℝ) : ℝ :=
  VvalGen (x (structPivot M hN)) M t (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x) (hleStruct M t ha)

/-- **The rate transfers to the R1 active-center chart ∀M (NO bridge)**: `routeMCore M (phiFlatLiveR1 …) =
(x p₀)² · UvalLiveR1 …`. Decoder-agnostic (`routeMCore_phiGen` + the R1 identity boundary `hC0_liveR1`,
which holds since the active center `p ≥ 1` leaves `Bmat 0`/`Rmat 0` untouched). -/
theorem routeMCore_phiFlatLiveR1 (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (hN : 0 < routeMAmbient M) (p : ℕ) (hp0 : p ≠ 0)
    (hp1 : Text M t (p + 1) ≤ Text M t p) (hp2 : Text M t (p + 1) ≤ Wext M p)
    (rfin : (Fin (routeMAmbient M) → ℝ) → Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (x : Fin (routeMAmbient M) → ℝ) :
    routeMCore M (phiFlatLiveR1 M t ha hN p hp1 hp2 rfin x)
      = (x (structPivot M hN)) ^ 2 * UvalLiveR1 M t ha hN p hp1 hp2 rfin x :=
  routeMCore_phiGen (x (structPivot M hN)) M t (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x)
    (hleStruct M t ha)
    (hC0_liveR1 M t ha p hp0 hp1 hp2 (rfin x) (x (structPivot M hN)) x)

/-- **Non-vacuity: the R1 pivot E-block genuinely carries the fixed `1`** at `(0,0)` (the gauge-fixed
radial direction), given the strict row/col drops at `p` (so the residual block is nonempty). The
`InteriorDrop` `p*` supplies these strict drops, so the fixed pivot is realised — not vacuous. -/
theorem pivotEIndicator_apply_zero (M t : Fin (L + 1) → ℕ) (s : ℕ)
    (hr : 0 < Text M t s - Text M t (s + 1)) (hc : 0 < Wext M s - Text M t (s + 1)) :
    pivotEIndicator M t s ⟨0, hr⟩ ⟨0, hc⟩ = 1 := by
  simp [pivotEIndicator]

/-- **`UvalLiveR1 ≥ 0`** — sum of squares (banked `VvalGen_nonneg`). -/
theorem UvalLiveR1_nonneg (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (hN : 0 < routeMAmbient M)
    (p : ℕ) (hp1 : Text M t (p + 1) ≤ Text M t p) (hp2 : Text M t (p + 1) ≤ Wext M p)
    (rfin : (Fin (routeMAmbient M) → ℝ) → Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (x : Fin (routeMAmbient M) → ℝ) :
    0 ≤ UvalLiveR1 M t ha hN p hp1 hp2 rfin x :=
  VvalGen_nonneg _ M t _ _

/-! ## Wiring the active-center pivot `p*` from `InteriorDrop`

`InteriorDrop M` supplies an interior boundary `p` (`1 ≤ p < L`) with the strict row-drop
`Text(p+1) < Text(p)` and the tail column-drops `Text(b+1) < Wext(b)` on `[p, L−1]` — in particular at
`b = p`, `Text(p+1) < Wext(p)`. So the R1 decoder's hypotheses `hp1 : Text(p+1) ≤ Text(p)`,
`hp2 : Text(p+1) ≤ Wext(p)`, and the nonempty residual block (`pivotEIndicator_apply_zero`) are all
discharged from `InteriorDrop`'s `p*`. -/

/-- **`InteriorDrop` discharges the R1 pivot hypotheses at its `p*`.** From `InteriorDrop M`, the
witnessing `p` (`1 ≤ p < L`) has the row-drop `Text(p+1) < Text(p)` (`hp1` strict) and the column-drop
`Text(p+1) < Wext(p)` (`hp2` strict, the `b = p` tail case) — so the fixed-`1` pivot is placeable. -/
theorem interiorDrop_pivot_hyps (M : Fin (L + 1) → ℕ) (hInt : InteriorDrop M) :
    ∃ p, p ≠ 0 ∧ Text M (tach M) (p + 1) < Text M (tach M) p
      ∧ Text M (tach M) (p + 1) < Wext M p := by
  obtain ⟨_, p, hp1, hpL, hr, hcd⟩ := hInt
  exact ⟨p, by omega, hr, hcd p (le_refl p) hpL⟩

/-! ## The R1 interior witness (count-FREE; reuses the dead-leaf witness)

The `Ubound` a.e.-positivity input for the R1 chart: `∃ w, UvalLiveR1 … w ≠ 0`. At the dead-leaf witness
point `wInt M ha p` (with the leaf `rfin = 0`), the R1 decoder and the dead-leaf `genBlkFlatStruct` AGREE:
the only R1 override is `Rmat p = rmatPad(pivotEIndicator)`, and at `wInt` the dead-leaf reads
`Rmat p = rmatPad(readE (wInt p) p)` where `readE (wInt p)` at the pivot IS the `(0,0)=1` indicator
(`readE_wInt`); `Rfin = 0` matches. So `UvalLiveR1 … 0 wInt = UvalStructV … wInt = achieverUfun wInt ≠ 0`
by the banked `exists_achieverUfun_ne_zero_interior`. NO new induction — count-free non-vanishing. -/

/-- **`readE (wInt p)` at the pivot boundary `p = k+1` IS `pivotEIndicator`** (both the `(0,0)=1`
indicator). The decoder-agreement input. -/
theorem readE_wInt_pivot_eq (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : ℕ) (hk : k < L) :
    readE M (tach M) ha (wInt M ha (k + 1)) ⟨k, hk⟩ = pivotEIndicator M (tach M) (k + 1) := by
  funext i j
  rw [readE_wInt M ha (k + 1) ⟨k, hk⟩ i j, pivotEIndicator, Matrix.of_apply]
  simp only [Fin.val_mk, true_and]

/-- **The live decoder at `rfin = 0` IS the dead-leaf structured decoder.** Field-wise: Bmat/Nblk/Wblk/Rmat
are definitional copies; the `Rfin` field's `h ▸ 0` transported-zero equals `genBlkFlatStruct`'s `0`.

The `Rfin` `h ▸ 0` transported-zero is closed by `simp only [genBlkFlatLive]` (exposing the dite under the
projection) + `split` + `subst h; rfl` — the `simp only` is the load-bearing step (`show`/`change`/`unfold`
all fail the `▸` motive; `simp only [genBlkFlatLive]` reduces the projection cleanly). -/
theorem genBlkFlatLive_zero_eq (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (x : Fin (routeMAmbient M) → ℝ) :
    genBlkFlatLive M t ha 0 x = genBlkFlatStruct M t ha x := by
  have hRfin : (genBlkFlatLive M t ha 0 x).Rfin = (genBlkFlatStruct M t ha x).Rfin := by
    funext s
    rw [show (genBlkFlatStruct M t ha x).Rfin s = 0 from by cases s <;> rfl]
    simp only [genBlkFlatLive]
    split
    · rename_i h; subst h; rfl
    · rfl
  -- the other four fields are definitional copies; assemble via the constructor injectivity
  have heq : genBlkFlatLive M t ha 0 x
      = GenBlk.mk (genBlkFlatStruct M t ha x).Bmat (genBlkFlatStruct M t ha x).Nblk
          (genBlkFlatStruct M t ha x).Wblk (genBlkFlatStruct M t ha x).Rmat
          (genBlkFlatStruct M t ha x).Rfin := by
    rw [← hRfin]; rfl
  rw [heq]

/-- **The R1 decoder at `(wInt p, rfin = 0)` equals the dead-leaf structured decoder at `wInt p`.**
Field-by-field: Bmat/Nblk/Wblk are the structured decoder's (unchanged); `Rfin = 0` on both; `Rmat`
agrees — away from `p` the `Function.update` is the identity, and at `p` the fixed `rmatPad(pivotEIndicator)`
equals the structured `rmatPad(readE (wInt p) p)` (`readE_wInt_pivot_eq`). -/
theorem genBlkFlatLiveR1_wInt_Rmat (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : ℕ) (hk : k < L)
    (hp1 : Text M (tach M) (k + 1 + 1) ≤ Text M (tach M) (k + 1))
    (hp2 : Text M (tach M) (k + 1 + 1) ≤ Wext M (k + 1)) :
    (genBlkFlatLiveR1 M (tach M) ha (k + 1) hp1 hp2 0 (wInt M ha (k + 1))).Rmat
      = (genBlkFlatStruct M (tach M) ha (wInt M ha (k + 1))).Rmat := by
  funext s
  show Function.update (genBlkFlatLive M (tach M) ha 0 (wInt M ha (k + 1))).Rmat (k + 1)
      (rmatPad M (tach M) (k + 1) hp1 hp2 (pivotEIndicator M (tach M) (k + 1))) s = _
  by_cases hs : s = k + 1
  · subst hs
    rw [Function.update_self]
    show _ = (if hk' : k < L then rmatPad M (tach M) (k + 1) (ha.hdesc k hk') (ha.hub k)
        (readE M (tach M) ha (wInt M ha (k + 1)) ⟨k, hk'⟩) else 0)
    rw [dif_pos hk, readE_wInt_pivot_eq M ha k hk]
  · rw [Function.update_of_ne hs]; rfl

/-- **The R1 decoder at `(wInt p, rfin = 0)` IS the dead-leaf structured decoder at `wInt p`.** Combines
`genBlkFlatLive_zero_eq` (the `rfin=0` reduction: Bmat/Nblk/Wblk/Rfin) with `genBlkFlatLiveR1_wInt_Rmat`
(the Rmat fixed-pivot = the structured `readE (wInt) p`). The R1 fixed pivot is invisible at `wInt`
because `wInt`'s `readE` at `p` IS the same `(0,0)=1` indicator. -/
theorem genBlkFlatLiveR1_wInt_eq (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : ℕ) (hk : k < L)
    (hp1 : Text M (tach M) (k + 1 + 1) ≤ Text M (tach M) (k + 1))
    (hp2 : Text M (tach M) (k + 1 + 1) ≤ Wext M (k + 1)) :
    genBlkFlatLiveR1 M (tach M) ha (k + 1) hp1 hp2 0 (wInt M ha (k + 1))
      = genBlkFlatStruct M (tach M) ha (wInt M ha (k + 1)) := by
  have hbase : genBlkFlatLive M (tach M) ha 0 (wInt M ha (k + 1))
      = genBlkFlatStruct M (tach M) ha (wInt M ha (k + 1)) := genBlkFlatLive_zero_eq M (tach M) ha _
  have heq : genBlkFlatLiveR1 M (tach M) ha (k + 1) hp1 hp2 0 (wInt M ha (k + 1))
      = GenBlk.mk (genBlkFlatLive M (tach M) ha 0 (wInt M ha (k + 1))).Bmat
          (genBlkFlatLive M (tach M) ha 0 (wInt M ha (k + 1))).Nblk
          (genBlkFlatLive M (tach M) ha 0 (wInt M ha (k + 1))).Wblk
          (genBlkFlatLiveR1 M (tach M) ha (k + 1) hp1 hp2 0 (wInt M ha (k + 1))).Rmat
          (genBlkFlatLive M (tach M) ha 0 (wInt M ha (k + 1))).Rfin := rfl
  rw [heq, genBlkFlatLiveR1_wInt_Rmat M ha k hk hp1 hp2,
    show (genBlkFlatLive M (tach M) ha 0 (wInt M ha (k + 1))).Bmat
      = (genBlkFlatStruct M (tach M) ha (wInt M ha (k + 1))).Bmat from by rw [hbase],
    show (genBlkFlatLive M (tach M) ha 0 (wInt M ha (k + 1))).Nblk
      = (genBlkFlatStruct M (tach M) ha (wInt M ha (k + 1))).Nblk from by rw [hbase],
    show (genBlkFlatLive M (tach M) ha 0 (wInt M ha (k + 1))).Wblk
      = (genBlkFlatStruct M (tach M) ha (wInt M ha (k + 1))).Wblk from by rw [hbase],
    show (genBlkFlatLive M (tach M) ha 0 (wInt M ha (k + 1))).Rfin
      = (genBlkFlatStruct M (tach M) ha (wInt M ha (k + 1))).Rfin from by rw [hbase]]

/-- **The R1 interior witness** (the count-free `Ubound` input, now CLOSED): a flat point where the R1
unit is nonzero, at an interior-drop pivot `p = k+1` (the STRICT row-drop `hr` + the tail column-drops
`hcd`, both supplied from `InteriorDrop`'s `p*`; `hML` the leaf). The R1 decoder at `(wInt p, rfin=0)`
IS the dead-leaf `genBlkFlatStruct` (`genBlkFlatLiveR1_wInt_eq`), so `UvalLiveR1 … 0 (wInt p) =
achieverUfun (wInt p)`, nonzero by the exposed dead-leaf `achieverUfun_wInt_ne_zero` — count-free
(non-vanishing, NOT the `minAdm−1` degree). -/
theorem exists_UvalLiveR1_ne_zero_interior (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hN : 0 < routeMAmbient M) (k : ℕ) (hkL : k + 1 < L) (hML : 0 < Wext M L)
    (hr : Text M (tach M) (k + 1 + 1) < Text M (tach M) (k + 1))
    (hcd : ∀ b, k + 1 ≤ b → b < L → Text M (tach M) (b + 1) < Wext M b) :
    ∃ w : Fin (routeMAmbient M) → ℝ,
      UvalLiveR1 M (tach M) (structAdm_tach M hL) hN (k + 1)
        (le_of_lt hr) (le_of_lt (hcd (k + 1) (le_refl _) hkL)) (fun _ => 0) w ≠ 0 := by
  refine ⟨wInt M (structAdm_tach M hL) (k + 1), ?_⟩
  rw [UvalLiveR1, genBlkFlatLiveR1_wInt_eq M (structAdm_tach M hL) k (by omega)
    (le_of_lt hr) (le_of_lt (hcd (k + 1) (le_refl _) hkL))]
  -- `VvalGen … (genBlkFlatStruct … wInt) = achieverUfun (wInt)` (definitional); nonzero by the exposed
  -- dead-leaf survival witness at the pivot `p = k+1` (the LOAD-BEARING reduction is proven above).
  show achieverUfun M hL hN (wInt M (structAdm_tach M hL) (k + 1)) ≠ 0
  exact achieverUfun_wInt_ne_zero M hL hN hML (k + 1) (by omega) hkL hr hcd

end DLNFibre.DLN.RLCT
