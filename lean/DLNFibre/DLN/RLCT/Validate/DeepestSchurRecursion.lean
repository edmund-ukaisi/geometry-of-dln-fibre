import DLNFibre.DLN.RLCT.Validate.DeepestSchurComparability

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestSchurRecursion` — the general-`L` Schur-product LDU recursion

The `L`-factor generalization of the banked two-layer identity `schur_product_ldu`
(`DeepestSchurComparability`). For an `L`-layer chain of `2×2`-blocked matrices
`C_s = fromBlocks (I_r+X_s) Y_s Z_s T_s` (an `r×r` regular pivot block, a core block of varying
width `m_s`), the (1,1)-block Schur complement of the ordered product factors as the ordered product
of the per-layer Schur cores interspersed with unipotent corrections:

    Sch(C_0·C_1·…·C_{L−1}) = S_0·(1−K_1)·S_1·(1−K_2)·S_2·…·(1−K_{L−1})·S_{L−1}

where `S_s = Sch(C_s)` is the per-layer Schur core and `K_k` is the off-pivot coupling
`(C_k)₂₁·((C_0·…·C_k)₁₁)⁻¹·((C_0·…·C_{k−1})₁₂)` (the cert's `K_k = (C_k)₂₁·(P_k)₁₁⁻¹·(P_{k−1})₁₂`
with the cert's *inclusive* `P_k = C_0·…·C_k`). In the Lean encoding the fold `partProd C j` is the
*first `j`* layers `C_0·…·C_{j−1}` (`partProd C 0 = 1`), so `cert P_k = partProd C (k+1)` and
`K_k = Kcoup C k = (C_k)₂₁·((partProd C (k+1))₁₁)⁻¹·((partProd C k)₁₂)`. Design cert:
`expeditions/2026-06-20-aoyagi-full/threads/genm-gauge120/cert.md` (identity F2), exact-algebra
verification in `codex/schur_ldu2.py` (non-commutative, L=3,4, r,M∈{1,2}) + a rectangular
varying-width recheck.

## Why the widths are `Type`-valued, not `Fin (H k)`

The chain uses a width family `m : ℕ → Type*`, so layer `k` has type
`Matrix (r ⊕ m k) (r ⊕ m (k+1)) α` and the partial-product fold
`partProd C (k+1) = partProd C k * C k` is **cast-free** — the shared middle type `r ⊕ m k` matches
definitionally. This is the same abstraction the base case `schur_product_ldu` uses (abstract core
types `m0 m1 m2 : Type*`); it avoids the `finCongr`/`prodAux` reindex bookkeeping that the DLN
`Fin (H k)` product carries. The `Fin`-side bridge (relating the DLN `prod`/`prodAux` to this
abstract `fromBlocks` fold) is a separate downstream wiring step
(`DeepestBlockDecomp.reindex_mul_fromBlocks`), not this identity.

## Status

Pure `Matrix`/`Ring` algebra over a general `CommRing`; no `deepestSplit`, no `Params`. The
invertibility of every layer pivot and every partial-product pivot is carried as an explicit
`Invertible` hypothesis (matching how `schur_product_ldu` carries `[Invertible (A0*A1+Y0*Z1)]`); at
the deepest point these hold because each `C_s(0) = blockdiag[I_r, 0]` forces `(P_k)₁₁(0) = I_r`,
but that analytic fact is a later sub-lemma, not this algebraic identity.
-/

open Matrix
namespace DLNFibre.DLN.RLCT

-- `blockSchur_mul` carries `Fintype`/`DecidableEq` on the outer core types purely to invoke the
-- base case `schur_product_ldu`; they are unused in its own statement.
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

section
variable {r : Type*} [Fintype r] [DecidableEq r] {α : Type*} [CommRing α]

/-- The `(1,1)`-block Schur complement of a `2×2`-blocked matrix, using the total ring inverse
`Ring.inverse` on the pivot block (so it is a genuine `def` even where the pivot is singular; the
recursion theorems below carry the `Invertible` hypotheses that make it the honest Schur
complement). For `P = fromBlocks A Y Z T` with `A` invertible, `blockSchur P = T − Z·A⁻¹·Y`. -/
noncomputable def blockSchur {a b : Type*} (P : Matrix (r ⊕ a) (r ⊕ b) α) : Matrix a b α :=
  P.toBlocks₂₂ - P.toBlocks₂₁ * Ring.inverse P.toBlocks₁₁ * P.toBlocks₁₂

/-- The `(1,1)` block of the identity `2×2`-blocked matrix is the identity. -/
theorem toBlocks₁₁_one {a b : Type*} [DecidableEq a] [DecidableEq b] :
    (1 : Matrix (a ⊕ b) (a ⊕ b) α).toBlocks₁₁ = 1 := by
  rw [← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₁₁]

/-- **Schur complement of a two-factor blocked product** (the `toBlocks`-native recast of
`schur_product_ldu`). For blocked matrices `G0 : (r ⊕ a) × (r ⊕ b)` and `G1 : (r ⊕ b) × (r ⊕ c)`
with `G0₁₁`, `G1₁₁` and `(G0·G1)₁₁` all invertible, the Schur complement of the product factors as
`Sch(G0·G1) = Sch(G0)·(1 − K)·Sch(G1)`, `K = G1₂₁·((G0·G1)₁₁)⁻¹·G0₁₂` the off-pivot correction.
The `Fintype`/`DecidableEq` on `a`, `c` are unused in the statement but required to invoke the base
case `schur_product_ldu`, which carries them. -/
theorem blockSchur_mul {a b c : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (G0 : Matrix (r ⊕ a) (r ⊕ b) α) (G1 : Matrix (r ⊕ b) (r ⊕ c) α)
    (h0 : Invertible G0.toBlocks₁₁) (h1 : Invertible G1.toBlocks₁₁)
    (hP : Invertible (G0 * G1).toBlocks₁₁) :
    blockSchur (G0 * G1)
      = blockSchur G0
          * (1 - G1.toBlocks₂₁ * Ring.inverse (G0 * G1).toBlocks₁₁ * G0.toBlocks₁₂)
          * blockSchur G1 := by
  -- The four blocks of the product (`fromBlocks_multiply` after writing each factor by its blocks).
  have hblocks : G0 * G1 = Matrix.fromBlocks
      (G0.toBlocks₁₁ * G1.toBlocks₁₁ + G0.toBlocks₁₂ * G1.toBlocks₂₁)
      (G0.toBlocks₁₁ * G1.toBlocks₁₂ + G0.toBlocks₁₂ * G1.toBlocks₂₂)
      (G0.toBlocks₂₁ * G1.toBlocks₁₁ + G0.toBlocks₂₂ * G1.toBlocks₂₁)
      (G0.toBlocks₂₁ * G1.toBlocks₁₂ + G0.toBlocks₂₂ * G1.toBlocks₂₂) := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks G0, ← Matrix.fromBlocks_toBlocks G1]
    rw [Matrix.fromBlocks_multiply]
  -- The product pivot as an explicit block (definitional once `hblocks` is applied).
  have hpiv : (G0 * G1).toBlocks₁₁
      = G0.toBlocks₁₁ * G1.toBlocks₁₁ + G0.toBlocks₁₂ * G1.toBlocks₂₁ := by
    rw [hblocks, Matrix.toBlocks_fromBlocks₁₁]
  letI := h0; letI := h1
  -- Transport the product-pivot invertibility to the explicit block, so `⅟` there matches the base.
  letI hPblk : Invertible (G0.toBlocks₁₁ * G1.toBlocks₁₁ + G0.toBlocks₁₂ * G1.toBlocks₂₁) :=
    hpiv ▸ hP
  -- Unfold `blockSchur`, read off the product blocks, bridge `Ring.inverse → ⅟`, apply the base.
  simp only [blockSchur, hblocks, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
    Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂, Ring.inverse_invertible]
  exact schur_product_ldu G0.toBlocks₁₁ G1.toBlocks₁₁ G0.toBlocks₁₂ G1.toBlocks₁₂
    G0.toBlocks₂₁ G1.toBlocks₂₁ G0.toBlocks₂₂ G1.toBlocks₂₂

variable {m : ℕ → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]

/-- The product of the first `k` layers `C 0 · C 1 · … · C (k−1)`, of block shape
`(r ⊕ m 0) × (r ⊕ m k)`. A dependent-width fold; cast-free (the shared middle type `r ⊕ m k` matches
definitionally). -/
def partProd (C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α) :
    (k : ℕ) → Matrix (r ⊕ m 0) (r ⊕ m k) α
  | 0 => 1
  | k + 1 => partProd C k * C k

/-- The off-pivot correction of the `k`-th recursion step: `K_k = (C_k)₂₁·((P_{k+1})₁₁)⁻¹·(P_k)₁₂`,
with `P_j = partProd C j` the partial products. Total (`Ring.inverse`). -/
noncomputable def Kcoup (C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α) (k : ℕ) :
    Matrix (m k) (m k) α :=
  (C k).toBlocks₂₁ * Ring.inverse (partProd C (k + 1)).toBlocks₁₁ * (partProd C k).toBlocks₁₂

/-- The ordered product of per-layer Schur cores interspersed with the unipotent corrections:
`coreProd C k = S_0·(1−K_1)·S_1·…·(1−K_{k−1})·S_{k−1}`, of shape `(m 0) × (m k)`
(`coreProd C 0 = 1`). -/
noncomputable def coreProd (C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α) :
    (k : ℕ) → Matrix (m 0) (m k) α
  | 0 => 1
  | k + 1 => coreProd C k * (1 - Kcoup C k) * blockSchur (C k)

/-- **The single-step chain recursion.** Peeling the last layer: the Schur complement of the first
`k+1` layers factors as `Sch(P_{k+1}) = Sch(P_k)·(1 − K_k)·Sch(C_k)`, `K_k = Kcoup C k`. Direct
application of `blockSchur_mul` to `G0 = partProd C k`, `G1 = C k`. -/
theorem blockSchur_partProd_succ (C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α) (k : ℕ)
    (h0 : Invertible (partProd C k).toBlocks₁₁) (h1 : Invertible (C k).toBlocks₁₁)
    (hP : Invertible (partProd C (k + 1)).toBlocks₁₁) :
    blockSchur (partProd C (k + 1))
      = blockSchur (partProd C k) * (1 - Kcoup C k) * blockSchur (C k) := by
  -- `partProd C (k+1) ≡ partProd C k * C k` and `Kcoup C k` unfold definitionally to the
  -- off-pivot correction, so this is exactly `blockSchur_mul` at `G0 = partProd C k`, `G1 = C k`.
  exact blockSchur_mul (partProd C k) (C k) h0 h1 hP

/-- **The general-`L` Schur-product LDU recursion** (identity F2). The `(1,1)`-block Schur
complement of the `L`-layer ordered product `C_0·C_1·…·C_{L−1}` equals the ordered product of the
per-layer Schur cores interspersed with the unipotent corrections `1 − K_k`. Carries `Invertible`
hypotheses on every layer pivot (`k < L`) and every partial-product pivot (`k ≤ L`). Proved by
induction on `L`, peeling the last layer with `blockSchur_partProd_succ` (whose step is the banked
two-factor `schur_product_ldu`). -/
theorem schur_product_ldu_rec (C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α) (L : ℕ)
    (hLayer : ∀ k, k < L → Invertible (C k).toBlocks₁₁)
    (hPart : ∀ k, k ≤ L → Invertible (partProd C k).toBlocks₁₁) :
    blockSchur (partProd C L) = coreProd C L := by
  revert hLayer hPart
  induction L with
  | zero =>
    intro _ _
    -- `partProd C 0 = 1`, `coreProd C 0 = 1`; `blockSchur 1 = 1 − 0·1⁻¹·0 = 1`.
    simp only [partProd, coreProd, blockSchur]
    rw [show (1 : Matrix (r ⊕ m 0) (r ⊕ m 0) α) = Matrix.fromBlocks 1 0 0 1 from
      Matrix.fromBlocks_one.symm]
    -- `simp only` (not full `simp`) so `fromBlocks_one` does not rewrite the split back to `1`.
    simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
      Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂, Ring.inverse_one,
      Matrix.zero_mul, Matrix.mul_zero, sub_zero]
  | succ k ih =>
    intro hLayer hPart
    -- IH with the layer/partial hypotheses restricted from `k+1` down to `k`.
    have ihres := ih (fun j hj => hLayer j (by omega)) (fun j hj => hPart j (by omega))
    -- Peel the last layer, then substitute the IH; `coreProd` closes the step definitionally.
    rw [blockSchur_partProd_succ C k (hPart k (by omega)) (hLayer k (by omega))
        (hPart (k + 1) (by omega)), ihres]
    rfl

/-! ## Non-vacuity witness

The hypotheses of `schur_product_ldu_rec` are satisfiable and the identity applies: for the constant
chain of identity layers (`r = Fin 1`, core `Fin 1`, over `ℚ`) every layer pivot and every
partial-product pivot is `1`, hence invertible, so the theorem holds at `L = 3`. This rules out
vacuity-by-unsatisfiable-hypotheses. The interspersed corrections `1 − K_k` are genuinely nonzero
for other chains: the `L = 2` instance of this recursion coincides with the base case
`schur_product_ldu`, whose own file (`DeepestSchurComparability`) carries a `K ≠ 0`, `R − ∏S ≠ 0`
witness. -/
example :
    let C : (s : ℕ) →
        Matrix (Fin 1 ⊕ (fun _ : ℕ => Fin 1) s) (Fin 1 ⊕ (fun _ : ℕ => Fin 1) (s + 1)) ℚ :=
      fun _ => 1
    blockSchur (partProd C 3) = coreProd C 3 := by
  intro C
  have hone : ∀ k, partProd C k = 1 := by
    intro k
    induction k with
    | zero => rfl
    | succ n ih => rw [partProd, ih, one_mul]
  refine schur_product_ldu_rec _ 3 (fun k _ => ?_) (fun k _ => ?_)
  · rw [toBlocks₁₁_one]; exact invertibleOne
  · rw [hone k, toBlocks₁₁_one]; exact invertibleOne

end
end DLNFibre.DLN.RLCT
