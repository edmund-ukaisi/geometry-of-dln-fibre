import DLNFibre.DLN.RLCT.Validate.DeepestGaugeChart
import DLNFibre.Core.MeasureTheory.PolynomialZeroSet
import Mathlib.Algebra.MvPolynomial.Basic

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestCoreNonvanishing` — the `hMid ⟹ hGne` bridge

The L2 lemmas (`deepest_regular_smooth_split`, `deepest_regular_core_reduces`) carry the analytic
precondition `hGne`: the reduced core `dlnLoss M 0 ∘ flatSymm` is `≠ 0` a.e. on a neighbourhood of the
flat origin. This module discharges `hGne` from the structural non-degeneracy of the reduced widths.

## The fidelity finding (crux2, 2026-06-22) — the hypothesis is `r < H_s` for ALL `s`

`dlnLoss M 0 A = ‖prod M A‖²` (sum of squares of the layer-product entries). `hGne` (`≢ 0` a.e.) needs
the product map `prod M` to be NOT identically zero — which holds iff **every** reduced width
`M_s = H_s − r ≥ 1`, ENDPOINTS included. If any `M_s = 0` (interior `r = H_s`, or endpoint `r = H_0`
/ `r = H_L`), then `prod M ≡ 0` (a zero-width vertex annihilates the chain, or an entry-empty endpoint
product), so `dlnLoss M 0 ≡ 0` and `hGne` FAILS. The interior-only `hMid` (`∀ s, 0 < s.val → r < H
s.castSucc`) does NOT suffice — it misses `M_0 = 0` and `M_L = 0`. The faithful hypothesis is `∀ s,
1 ≤ M s` (equivalently `r < H_s ∀ s`). [RESOLVED by the controller: route (B). The headline stays
NON-STRICT (`r ≤ min`, paper-faithful, audit-verified true at the boundary); the rungs prove the
non-degenerate bulk `∀ s, M_s ≥ 1` (this module's hypothesis), and the degenerate boundary `some M_s = 0`
is the headline's separate case `#70` (direct-Morse `rlctAt = nReg/2`, NOT the additive route which gives
`⊤`).]

## Route (Codex g175 + the controller's #69/#70 decoupling)

`hGne` needs `≠ 0` A.E. (not everywhere — the basepoint `0` has `dlnLoss M 0 0 = 0`), so a measure-zero
argument is unavoidable. Decoupled into:
1. **The constructive nonzero witness** (`dlnLoss_deepest_core_ne_zero_witness`, crux2, PROVEN): an
   explicit `A` with `dlnLoss M 0 A ≠ 0` when all `M_s ≥ 1` — each layer `= e₀₀` (a `1` at `(0,0)`), so
   the product's `(0,0)` entry is `1`. Route-independent, pure algebra.
2. **The general null lemma** (`mvpoly_zeroSet_null`, #69, network-free, → `DLNFibre.Core`, dispatched to
   a sibling formaliser): `(p : MvPolynomial (Fin n) ℝ) (hp : p ≠ 0) → volume {x | eval x p = 0} = 0`.
3. **The connection** (`dlnLoss_deepest_core_ae_ne_zero`, crux2): encode `dlnLoss M 0 ∘ flatSymm = eval z
   P`, `P ≠ 0` from (1), invoke (2). See the theorem's connection-plan docstring.

The all-`M_s ≥ 1` hypothesis is the non-degenerate bulk the rungs (R1/L2/D1) prove; the degenerate
boundary (`some M_s = 0`, `r = H_s`) is the headline's separate case (#70, direct-Morse `rlctAt = nReg/2`,
`lambdaCore = 0`; the headline stays NON-STRICT / paper-faithful `r ≤ min`, audit-verified true). The
headline case-splits on `(∀ s, M_s ≥ 1)` (crux2 owns the wiring).
-/

open MeasureTheory Matrix
open scoped ENNReal BigOperators Topology
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- The `e₀₀` witness parameter: every layer is the matrix with `1` at `(0,0)`, `0` elsewhere. The
constructive non-degeneracy witness — when every reduced width `M_s ≥ 1`, its layer product has
`(0,0)`-entry `1`, so `dlnLoss M 0` is `≥ 1 > 0` there (not identically zero). -/
noncomputable def e00Witness (M : Fin (L + 1) → ℕ) : Params M :=
  fun s => Matrix.of fun i j => if (i : ℕ) = 0 ∧ (j : ℕ) = 0 then (1 : ℝ) else 0

/-- A matrix-type cast (from dimension equalities) pushes through to entries of an `e₀₀`-style `of`
matrix: the cast preserves the polymorphic `if ↑i = 0 ∧ ↑j = 0` formula, with the indices `Fin.cast`-ed
(both `0 ↦ 0`). Used to evaluate `prodAux`'s cast-transported layer at `(0,0)`. -/
private theorem cast_e00_entry {a a' b b' : ℕ} (ha : a = a') (hb : b = b')
    (h : Matrix (Fin a) (Fin b) ℝ = Matrix (Fin a') (Fin b') ℝ)
    (f : Fin a → Fin b → ℝ) (i : Fin a') (j : Fin b') :
    (cast h (Matrix.of f)) i j = f (Fin.cast ha.symm i) (Fin.cast hb.symm j) := by
  subst ha; subst hb; rfl

/-- The `(0,0)` entry of the `e₀₀`-witness partial product is `1` (induction on chain length). The
`0`-indices are valid since each `M_s ≥ 1`. -/
theorem prodAux_e00Witness_zero (M : Fin (L + 1) → ℕ) (hpos : ∀ s, 1 ≤ M s)
    (k : ℕ) (hk : k < L + 1) :
    prodAux M (e00Witness M) k hk ⟨0, hpos 0⟩ ⟨0, hpos ⟨k, hk⟩⟩ = 1 := by
  induction k with
  | zero => simp [prodAux, Matrix.one_apply]
  | succ k ih =>
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      have e1 : (⟨k, hk'⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).castSucc := by
        apply Fin.ext; simp [Fin.castSucc]
      have e2 : (⟨k + 1, hk⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).succ := by
        apply Fin.ext; simp [Fin.succ]
      -- the cast-transported layer `Lyr` is the `e₀₀` matrix at the `prodAux`-needed type. Its entries:
      -- `Lyr i j = if ↑i=0 ∧ ↑j=0` (push the nested cast through via `cast_cast` + `cast_e00_entry`).
      set Lyr : Matrix (Fin (M ⟨k, hk'⟩)) (Fin (M ⟨k + 1, hk⟩)) ℝ :=
        (by rw [e1, e2]; exact e00Witness M ⟨k, hkL⟩) with hLyr
      have hLyr_entry : ∀ (i : Fin (M ⟨k, hk'⟩)) (j : Fin (M ⟨k + 1, hk⟩)),
          Lyr i j = if (i : ℕ) = 0 ∧ (j : ℕ) = 0 then (1 : ℝ) else 0 := by
        intro i j
        simp only [hLyr, e00Witness, eq_mpr_eq_cast, cast_cast]
        -- the collapsed single cast of an `of` matrix evaluates by `cast_e00_entry` (term-mode unify).
        exact (cast_e00_entry (congrArg M e1) (congrArg M e2) (by rw [e1, e2]) _ i j).trans (by
          simp [Fin.coe_cast])
      -- `prodAux (k+1) = prodAux k * Lyr`; evaluate at `(0,0)` via `mul_apply` + the single 0-term.
      show (prodAux M (e00Witness M) k hk' * Lyr) ⟨0, hpos 0⟩ ⟨0, hpos ⟨k + 1, hk⟩⟩ = 1
      rw [Matrix.mul_apply,
        Finset.sum_eq_single (⟨0, hpos ⟨k, hk'⟩⟩ : Fin (M ⟨k, hk'⟩))]
      · rw [ih hk', hLyr_entry]; simp
      · intro l _ hl
        have hl0 : (l : ℕ) ≠ 0 := fun h => hl (Fin.ext h)
        rw [hLyr_entry]; simp [hl0]
      · intro h; exact absurd (Finset.mem_univ _) h

theorem dlnLoss_deepest_core_ne_zero_witness (M : Fin (L + 1) → ℕ) (hpos : ∀ s, 1 ≤ M s) :
    ∃ A : Params M, dlnLoss M (0 : Matrix (Fin (M 0)) (Fin (M (Fin.last L))) ℝ) A ≠ 0 := by
  refine ⟨e00Witness M, ?_⟩
  -- `prod M (e00) (0,0) = 1`, so the `(0,0)` summand of `dlnLoss = ∑∑ (prod − 0)²` is `1 > 0`.
  have hprod : prod M (e00Witness M) ⟨0, hpos 0⟩ ⟨0, hpos (Fin.last L)⟩ = 1 := by
    have := prodAux_e00Witness_zero M hpos L (Nat.lt_succ_self L)
    -- `prod = prodAux L`, and `⟨0, hpos ⟨L, _⟩⟩ = ⟨0, hpos (Fin.last L)⟩` (same `Fin.last`).
    rw [prod]
    convert this using 2
  -- the loss is a sum of squares with a `1`-term, so it is positive (hence `≠ 0`).
  intro hzero
  have hsq : (prod M (e00Witness M) ⟨0, hpos 0⟩ ⟨0, hpos (Fin.last L)⟩
      - (0 : Matrix (Fin (M 0)) (Fin (M (Fin.last L))) ℝ) ⟨0, hpos 0⟩ ⟨0, hpos (Fin.last L)⟩) ^ 2 = 0 := by
    have hnn : ∀ i, (0 : ℝ) ≤ ∑ j, ((prod M (e00Witness M) - 0) i j) ^ 2 :=
      fun i => Finset.sum_nonneg fun j _ => sq_nonneg _
    have hi : ∑ j, ((prod M (e00Witness M) - 0) ⟨0, hpos 0⟩ j) ^ 2 = 0 := by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnn i)).1 hzero ⟨0, hpos 0⟩
        (Finset.mem_univ _)
      simpa using this
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).1 hi
      ⟨0, hpos (Fin.last L)⟩ (Finset.mem_univ _)
    simpa [Matrix.sub_apply] using this
  simp only [Matrix.zero_apply, sub_zero, hprod] at hsq
  norm_num at hsq

/-! ## The single-`P` encoding: `dlnLoss M 0 ∘ flatSymm = MvPolynomial.eval` of one `P`

To consume `MvPolynomial.ae_eval_ne_zero` (the `@68ef083` Core brick), express `dlnLoss M 0 (flatSymm z)`
as `eval z P` for one `P`. `prod`/`prodAux` are ℝ-specific, so we mirror `prodAux` over a generic
`CommRing` (`prodPolyAux`) and relate by `eval z` (`Matrix.map_mul`, a ring hom). The layer `X`-matrices
`(Xmat s) i j = X (flat-index of (s,i,j))` satisfy `(Xmat s).map (eval z) = (flatSymm z) s`, so the
products agree under `eval z`. -/

open MvPolynomial in
/-- The generic-`CommRing` mirror of `prodAux` (same recursion + cast structure). -/
noncomputable def prodPolyAux {R : Type*} [CommRing R] (M : Fin (L + 1) → ℕ)
    (A : (s : Fin L) → Matrix (Fin (M s.castSucc)) (Fin (M s.succ)) R) :
    (k : ℕ) → (hk : k < L + 1) → Matrix (Fin (M 0)) (Fin (M ⟨k, hk⟩)) R
  | 0, _ => (1 : Matrix (Fin (M 0)) (Fin (M 0)) R)
  | k + 1, hk => by
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      refine (prodPolyAux M A k hk') * ?_
      have e1 : (⟨k, hk'⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).castSucc := by
        apply Fin.ext; simp [Fin.castSucc]
      have e2 : (⟨k + 1, hk⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).succ := by
        apply Fin.ext; simp [Fin.succ]
      rw [e1, e2]; exact A ⟨k, hkL⟩

/-- `prodPolyAux` maps to `prodAux` under any ring hom applied per layer: if `(A s).map f = B s` for
every layer, then `(prodPolyAux M A k).map f = prodAux M B k`. The eval-commutes engine. -/
theorem prodPolyAux_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (M : Fin (L + 1) → ℕ)
    (A : (s : Fin L) → Matrix (Fin (M s.castSucc)) (Fin (M s.succ)) R)
    (B : (s : Fin L) → Matrix (Fin (M s.castSucc)) (Fin (M s.succ)) S)
    (hAB : ∀ s, (A s).map f = B s) (k : ℕ) (hk : k < L + 1) :
    (prodPolyAux M A k hk).map f = prodPolyAux M B k hk := by
  induction k with
  | zero => simp [prodPolyAux, Matrix.map_one f f.map_zero f.map_one]
  | succ k ih =>
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      have e1 : (⟨k, hk'⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).castSucc := by
        apply Fin.ext; simp [Fin.castSucc]
      have e2 : (⟨k + 1, hk⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).succ := by
        apply Fin.ext; simp [Fin.succ]
      -- both recursions: `prev * (cast layer)`; `.map f` distributes (Matrix.map_mul) + IH + hAB.
      set LyrA : Matrix (Fin (M ⟨k, hk'⟩)) (Fin (M ⟨k + 1, hk⟩)) R :=
        (by rw [e1, e2]; exact A ⟨k, hkL⟩) with hLyrA
      set LyrB : Matrix (Fin (M ⟨k, hk'⟩)) (Fin (M ⟨k + 1, hk⟩)) S :=
        (by rw [e1, e2]; exact B ⟨k, hkL⟩) with hLyrB
      show (prodPolyAux M A k hk' * LyrA).map f = prodPolyAux M B k hk' * LyrB
      rw [Matrix.map_mul, ih hk']
      congr 1
      -- `LyrA.map f = LyrB`: cast-transported `(A ⟨k,hkL⟩).map f = B ⟨k,hkL⟩` (hAB).
      have hcast : LyrA.map f = LyrB := by
        simp only [hLyrA, hLyrB]
        rw [← hAB ⟨k, hkL⟩]
        -- `(cast h (A …)).map f = cast h ((A …).map f)`: map commutes with the dim-cast.
        ext i j
        simp only [Matrix.map_apply]
        congr 1 <;> · rw [e1, e2]
      exact hcast

/-- `prodPolyAux` over ℝ IS `prodAux` (same recursion + cast structure) — the bridge from the generic
mirror back to the loss's `prodAux`. By induction (both: base `1`, step `prev * cast layer`). -/
theorem prodPolyAux_eq_prodAux (M : Fin (L + 1) → ℕ) (A : Params M) (k : ℕ) (hk : k < L + 1) :
    prodPolyAux M A k hk = prodAux M A k hk := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      conv_lhs => rw [prodPolyAux]
      conv_rhs => rw [prodAux]
      rw [ih hk']
      -- the cast-transported layer is the SAME in both defs (identical `rw [e1,e2]; exact A …`).
      rfl

/-- The per-layer `X`-variable matrix: entry `(i,j)` is the coordinate variable `X` at the flat index
of `(s, i, j)` (the `Fintype.equivFin (FlatIdx M)` of `⟨⟨s, i⟩, j⟩`). Its `eval z` is `(flatSymm z) s`. -/
noncomputable def coreXmat (M : Fin (L + 1) → ℕ) (s : Fin L) :
    Matrix (Fin (M s.castSucc)) (Fin (M s.succ)) (MvPolynomial (Fin (flatDim M)) ℝ) :=
  Matrix.of fun i j => MvPolynomial.X ((Fintype.equivFin (FlatIdx M)) ⟨⟨s, i⟩, j⟩)

/-- `(coreXmat M s).map (eval z) = (paramsEquivFlat M).symm z s` — the `X`-matrix evaluates to the
flat-unpacked layer matrix (each `eval z (X idx) = z idx = (flatSymm z) s i j`, the coordinate `rfl`). -/
theorem coreXmat_map_eval (M : Fin (L + 1) → ℕ) (z : Fin (flatDim M) → ℝ) (s : Fin L) :
    (coreXmat M s).map (MvPolynomial.eval z) = ((paramsEquivFlat M).symm z) s := by
  ext i j
  simp only [coreXmat, Matrix.map_apply, Matrix.of_apply, MvPolynomial.eval_X]
  rfl

/-- **The reduced-core polynomial** `P`: `∑ᵢⱼ (prodPolyAux M coreXmat L i j)²` — the formal polynomial
with `eval z P = dlnLoss M 0 ((paramsEquivFlat M).symm z)`. -/
noncomputable def corePoly (M : Fin (L + 1) → ℕ) : MvPolynomial (Fin (flatDim M)) ℝ :=
  ∑ i, ∑ j, (prodPolyAux M (coreXmat M) L (Nat.lt_succ_self L) i j) ^ 2

/-- `eval z (corePoly M) = dlnLoss M 0 ((paramsEquivFlat M).symm z)` — the encoding identity. The
`prodPolyAux`-over-`coreXmat` maps (via `eval z`, `prodPolyAux_map` + `coreXmat_map_eval`) to
`prodAux M (flatSymm z) = prod M (flatSymm z)`, and `dlnLoss = ∑ entries²`. -/
theorem eval_corePoly (M : Fin (L + 1) → ℕ) (z : Fin (flatDim M) → ℝ) :
    MvPolynomial.eval z (corePoly M)
      = dlnLoss M (0 : Matrix (Fin (M 0)) (Fin (M (Fin.last L))) ℝ) ((paramsEquivFlat M).symm z) := by
  have hmap := prodPolyAux_map (MvPolynomial.eval z) M (coreXmat M)
    (fun s => ((paramsEquivFlat M).symm z) s) (coreXmat_map_eval M z) L (Nat.lt_succ_self L)
  -- `eval z (prodPolyAux … i j) = (prod M (flatSymm z)) i j` (the map identity, entrywise).
  have hentry : ∀ i j, MvPolynomial.eval z (prodPolyAux M (coreXmat M) L (Nat.lt_succ_self L) i j)
      = prod M ((paramsEquivFlat M).symm z) i j := by
    intro i j
    have h1 := congrFun (congrFun hmap i) j
    -- `prodPolyAux M (flatSymm z) L = prodAux M (flatSymm z) L = prod M (flatSymm z)`.
    rw [prodPolyAux_eq_prodAux M ((paramsEquivFlat M).symm z) L (Nat.lt_succ_self L)] at h1
    simpa [Matrix.map_apply, prod] using h1
  -- `dlnLoss M 0 A = ∑ᵢⱼ (prod M A i j)²` (the `− 0` vanishes entrywise).
  have hdln : dlnLoss M (0 : Matrix (Fin (M 0)) (Fin (M (Fin.last L))) ℝ) ((paramsEquivFlat M).symm z)
      = ∑ i, ∑ j, (prod M ((paramsEquivFlat M).symm z) i j) ^ 2 := by
    unfold dlnLoss; simp
  rw [corePoly, hdln]
  simp only [map_sum, map_pow]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hentry i j]

/-- **The reduced core is `≠ 0` a.e. near the origin** (`hGne`, the bridge target). When every reduced
width `M_s ≥ 1`, `dlnLoss M 0 ∘ (paramsEquivFlat M).symm = eval · (corePoly M)` (`eval_corePoly`) with
`corePoly M ≠ 0` (the witness ⟹ `eval (flat witness) (corePoly M) = dlnLoss(witness) ≠ 0`), so by
`MvPolynomial.ae_eval_ne_zero` (Core, `@68ef083`) it is `≠ 0` a.e. (on `U = univ`). The `hMid ⟹ hGne`
bridge's ae-leg — sorry-free, Route-1. -/
theorem dlnLoss_deepest_core_ae_ne_zero (M : Fin (L + 1) → ℕ) (hpos : ∀ s, 1 ≤ M s) :
    ∃ U ∈ 𝓝 (0 : Fin (flatDim M) → ℝ),
      ∀ᵐ z ∂(volume.restrict U),
        dlnLoss M (0 : Matrix (Fin (M 0)) (Fin (M (Fin.last L))) ℝ)
          ((paramsEquivFlat M).symm z) ≠ 0 := by
  -- `corePoly M ≠ 0` from the witness: `eval (flat witness) (corePoly M) = dlnLoss(witness) ≠ 0`.
  obtain ⟨A, hA⟩ := dlnLoss_deepest_core_ne_zero_witness M hpos
  have hP_ne : corePoly M ≠ 0 := by
    intro hP0
    apply hA
    have := eval_corePoly M ((paramsEquivFlat M) A)
    rw [hP0] at this
    simpa using this.symm
  -- `ae_eval_ne_zero` at `p := corePoly M`, on `U = univ`, rewritten via `eval_corePoly`.
  refine ⟨Set.univ, Filter.univ_mem, ?_⟩
  have hae := MvPolynomial.ae_eval_ne_zero (corePoly M) hP_ne
  refine (ae_restrict_of_ae hae).mono fun z hz => ?_
  rw [← eval_corePoly M z]; exact hz

end DLNFibre.DLN.RLCT
