import DLNFibre.Core.Aoyagi.Corank2FaithfulComposite
import DLNFibre.DLN.Aoyagi.LearningCoefficient

/-!
# `DLN.Aoyagi.Corank2CoreGenWrap` — #112 Phase-1 part-C: the `coreGen`-level (3,3,4) two-sided `hideal`

Wraps the `flat(Pmat)`-level faithful two-sided `hideal` (`Core.Aoyagi.Corank2FaithfulComposite`) up to
the ACTUAL `coreGen (3,3,4) e ∘ g` the `Chart.hideal` field mandates, via the pivot block-center blow-up.

## The construction (sympy-verified, `gate3-codex/coregen_bexp_check.py`)

- **`eWrap`** — the custom transpose flatten `ℝ²¹ ≃ₜ Tuple (3,3,4)`: `A₀ = C₁ᵀ` (the `C₁`-block coords
  `0-7` off-pivot + `20` pivot), `A₁ = C₂ᵀ` (coords `8-19`), so `mult = A₁·A₀ = (C₁·C₂)ᵀ = Pmatᵀ`
  (`mult_eWrap`). NOT `canonFlatten` — this layout-matching `e` lets the block-elim apply directly; it is a
  coordinate reindex, hence measure-preserving + origin-fixing (the value engine's `coreReduction` accepts
  any such `e`).
- **`sigmaPiv`** — the pivot block-center blow-up `blockBlowupMap {0..7,20} 20`: the `C₁`-block off-pivot
  coords gain the pivot factor `c₁₁ = coord 20`, so `C₁∘sigmaPiv = c₁₁·C₁_strict` and hence
  `coreGen∘sigmaPiv = c₁₁·Pmat` EXACTLY (the `c₁₁` factors OUT — a blow-up, NOT a `1/c₁₁` normalization).
- **`gWrap = sigmaPiv ∘ gFaithful`** — the full (3,3,4) resolution chart. Then
  `coreGen (3,3,4) eWrap ∘ gWrap = c₁₁·(Pmat∘gFaithful)` (`coreGen_comp_gWrap`), and the `flat(Pmat)`-level
  `⟨Pmat∘gFaithful⟩ = ⟨E⟩` (`Corank2FaithfulComposite.hideal_faithful_*`) lifts to
  `⟨coreGen∘gWrap⟩ = ⟨c₁₁·E⟩` — the `coreGen`-level two-sided `hideal`, dominant monomial `c₁₁·E`
  (`bexpWrap`, `M'=1` principal).

`c₁₁·E` (not `E`) is the honest `coreGen`-level dominant: the pivot `c₁₁` is a genuine exceptional
coordinate (it vanishes at the deepest point). The `c₁₁`-divisor ratio `(|S|−1+1)/(2·1) = 9/2 = 4.5 > 4`,
so `E` stays the binding divisor and the payoff `rlct = 4` is unchanged (the pivot factor is non-binding).
-/

open Matrix Set
open DLNFibre.Core DLNFibre.Core.Aoyagi DLNFibre.Core.Aoyagi.Corank2Proto
open DLNFibre.Core.Aoyagi.Corank2HidealProto DLNFibre.Core.Aoyagi.Corank2FaithfulComposite

namespace DLNFibre.DLN.Aoyagi.Corank2CoreGenWrap

/-- The (3,3,4) dimension vector as a reducible `abbrev` — lets instance synthesis collapse the dependent
matrix widths (`dvec (Fin.succ 0)` → `Fin 3` etc.) under `HMul`. -/
abbrev dvec : Fin 3 → ℕ := ![3, 3, 4]

/-! ## The transpose flatten `eWrap : ℝ²¹ ≃ₜ Tuple (3,3,4)` -/

/-- `A₀ = C₁ᵀ` (3×3): reads the `C₁`-block coords — pivot `c₁₁ = coord 20`, off-pivot `= coords 0-7`. -/
def A0 (u : Fin 21 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![u 20, u 2, u 3; u 0, u 4, u 6; u 1, u 5, u 7]

/-- `A₁ = C₂ᵀ` (4×3): reads coords `8-19`, `A₁ a b = u (8 + 4b + a)`. -/
def A1 (u : Fin 21 → ℝ) : Matrix (Fin 4) (Fin 3) ℝ := fun a b => u ⟨8 + 4 * b.val + a.val, by omega⟩

/-- The transpose flatten's forward map (the 2-layer tuple built by nested `Fin.cases`). -/
def eFun (u : Fin 21 → ℝ) : Tuple (k := ℝ) dvec :=
  fun i => i.cases (A0 u) (fun j => j.cases (A1 u) (fun k => k.elim0))

theorem continuous_A0 : Continuous A0 :=
  continuous_matrix (fun r c => by
    fin_cases r <;> fin_cases c <;>
      (simp only [A0, of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_two, tail_cons,
        head_cons, empty_val', cons_val_fin_one, head_fin_const]; exact continuous_apply _))

theorem continuous_A1 : Continuous A1 :=
  continuous_matrix (fun r c => by simp only [A1]; exact continuous_apply _)

/-- Projecting one entry `A i r c` of a tuple is continuous (composed coordinate projections). -/
theorem continuous_tupleEntry (i : Fin 2) (r : Fin (dvec i.succ)) (c : Fin (dvec i.castSucc)) :
    Continuous (fun A : Tuple (k := ℝ) dvec => A i r c) :=
  (continuous_apply c).comp ((continuous_apply r).comp (continuous_apply i))

/-- The inverse map: extract the 21 coordinates from a tuple (`C₁`-block from `A₀ᵀ`, `C₂` from `A₁ᵀ`). -/
def eInv (A : Tuple (k := ℝ) dvec) : Fin 21 → ℝ := fun k =>
  if k.val = 0 then A 0 ⟨1, by decide⟩ ⟨0, by decide⟩
  else if k.val = 1 then A 0 ⟨2, by decide⟩ ⟨0, by decide⟩
  else if k.val = 2 then A 0 ⟨0, by decide⟩ ⟨1, by decide⟩
  else if k.val = 3 then A 0 ⟨0, by decide⟩ ⟨2, by decide⟩
  else if k.val = 4 then A 0 ⟨1, by decide⟩ ⟨1, by decide⟩
  else if k.val = 5 then A 0 ⟨2, by decide⟩ ⟨1, by decide⟩
  else if k.val = 6 then A 0 ⟨1, by decide⟩ ⟨2, by decide⟩
  else if k.val = 7 then A 0 ⟨2, by decide⟩ ⟨2, by decide⟩
  else if k.val = 20 then A 0 ⟨0, by decide⟩ ⟨0, by decide⟩
  else A 1 ⟨(k.val - 8) % 4, by have h : dvec (Fin.succ 1) = 4 := rfl; rw [h]; omega⟩
         ⟨(k.val - 8) / 4 % 3, by have h : dvec (Fin.castSucc 1) = 3 := rfl; rw [h]; omega⟩

/-- The transpose flatten `ℝ²¹ ≃ₜ Tuple (3,3,4)` (a continuous coordinate reindex). -/
noncomputable def eWrap : (Fin 21 → ℝ) ≃ₜ Tuple (k := ℝ) dvec where
  toFun := eFun
  invFun := eInv
  left_inv u := by funext k; fin_cases k <;> rfl
  right_inv A := by funext i; fin_cases i <;> (funext r c; fin_cases r <;> fin_cases c <;> rfl)
  continuous_toFun := by
    refine continuous_pi (fun i => ?_)
    fin_cases i
    · exact continuous_A0
    · exact continuous_A1
  continuous_invFun := by
    refine continuous_pi (fun k => ?_)
    fin_cases k <;> (simp only [eInv, Fin.isValue] <;> apply continuous_tupleEntry)

/-- `eWrap 0 = 0` (a coordinate reindex fixes the origin). -/
theorem eWrap_zero : eWrap (0 : Fin 21 → ℝ) = 0 := by
  show eFun 0 = 0
  funext i
  fin_cases i
  · show A0 0 = 0; ext r c; fin_cases r <;> fin_cases c <;> simp [A0]
  · show A1 0 = 0; ext r c; simp [A1]

/-- **`mult ∘ eWrap = A₁·A₀`** (the paired `multPrefix` form + `mul_one`). -/
theorem mult_eWrap (u : Fin 21 → ℝ) : mult dvec (eWrap u) = A1 u * A0 u := by
  have h : mult dvec (eWrap u) = A1 u * (A0 u * 1) := rfl
  rw [h]; congr 1; exact Matrix.mul_one (A0 u)

/-! ## The pivot block-center blow-up + the full chart -/

/-- The pivot block-center blow-up `blockBlowupMap {0..7,20} 20`: the `C₁`-block off-pivot coords `0-7`
gain the pivot factor `c₁₁ = coord 20`; the `C₂` coords `8-19` are spectators (fixed). -/
noncomputable def sigmaPiv : (Fin 21 → ℝ) → (Fin 21 → ℝ) :=
  blockBlowupMap ({0, 1, 2, 3, 4, 5, 6, 7, 20} : Finset (Fin 21)) 20

/-- The full (3,3,4) resolution chart `gWrap = sigmaPiv ∘ gFaithful` (pivot blow-up ∘ the faithful
`flat(Pmat)`-level chart). -/
noncomputable def gWrap : (Fin 21 → ℝ) → (Fin 21 → ℝ) := sigmaPiv ∘ gFaithful

theorem continuous_gWrap : Continuous gWrap :=
  (continuous_blockBlowupMap _ _).comp continuous_gFaithful

/-! ## The `c₁₁`-factorisation entry relation -/

/-- **The entry relation** (sympy `coregen_bexp_check.py`): pulling `mult ∘ eWrap` back through `gWrap`
scales the transposed product by the pivot `c₁₁ = gFaithful u 20`:
`(A₁·A₀)(gWrap u) r c = (gFaithful u 20) · (Pmat … c r)(gFaithful u)`. The `C₁`-block blow-up gives the
common `c₁₁` factor; the transpose `(r,c)↦(c,r)` matches `mult`'s `4×3` to `Pmat`'s `3×4`. -/
theorem mult_gWrap_entry (u : Fin 21 → ℝ) (r : Fin 4) (c : Fin 3) :
    (A1 (gWrap u) * A0 (gWrap u)) r c
      = gFaithful u 20 *
        (Pmat (cc 0) (cc 1) (cc 2) (cc 3) (cc 4) (cc 5) (cc 6) (cc 7) C2conc c r) (gFaithful u) := by
  fin_cases r <;> fin_cases c <;>
    simp only [A0, A1, gWrap, sigmaPiv, Function.comp_apply, blockBlowupMap, Pmat, C1, Q2inv, C2conc,
      cc, Matrix.mul_apply, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
      Matrix.head_fin_const, Matrix.cons_val_fin_one, Matrix.empty_val', Pi.mul_apply, Pi.add_apply,
      Fin.reduceFinMk, Fin.reduceEq, Finset.mem_insert, Finset.mem_singleton] <;>
    norm_num [gFaithful, Fin.ext_iff] <;> ring

/-! ## The `coreGen`-level dominant monomial `c₁₁·E` -/

/-- The `coreGen`-level dominant monomial `b₁ = c₁₁·E = u₂₀·u₀`, exponent vector `[1 at 0, 1 at 20]`,
`monomialFam` (`Fin 1`) form. -/
def bexpWrap : Fin 1 → Fin 21 → ℕ := fun _ d => if d = 0 ∨ d = 20 then 1 else 0

/-- `monomialFam bexpWrap` is the single dominant monomial `c₁₁·E = u₀·u₂₀`. -/
theorem monomialFam_bexpWrap (k : Fin 1) (u : Fin 21 → ℝ) : monomialFam bexpWrap k u = u 0 * u 20 := by
  simp only [monomialFam, bexpWrap]
  have h1 : ∀ d : Fin 21, u d ^ (if d = 0 ∨ d = 20 then 1 else 0)
      = if d = 0 ∨ d = 20 then u d else 1 := fun d => by split_ifs <;> simp
  simp_rw [h1]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one,
    show Finset.filter (fun d : Fin 21 => d = 0 ∨ d = 20) Finset.univ = {0, 20} from by decide,
    Finset.prod_insert (by decide), Finset.prod_singleton]
