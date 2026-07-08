import DLNFibre.DLN.RLCT.Validate.DeepestPsiSplitGenMoved

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestPsiSplitGenLeftCol` — the left-column half of Invariant A (#120 `hstep2`)

The genuinely `L`-recursive down-half of Invariant A for the general-`L` joint move `psiSplitRawGen`
(cert `expeditions/2026-06-20-aoyagi-full/threads/genm-d1psidesign/cert.md`, §1 item 4). Working over the
same abstract `Type`-valued chain as `DeepestPsiSplitGenMoved` / `DeepestSchurRecursion`, this module
builds the **left-column accumulator** and proves the moved chain's single down-block edit `Z₀` restores
the bottom-left block `(partProd)₂₁` of the full product.

The banked top-row half (`topRow_movedC`) fixes `(P₁₁, P₁₂)` for **any** `Z₀` override; here the specific
`Z₀` (the `deltaV0` accumulator) makes `(partProd (movedC C (Z0edit0 C L)) L)₂₁ = (partProd C L)₂₁`,
supplying the abstract half of the reg-preservation germ `hsub3reg` (the concrete `deepestEFull`
instantiation is downstream — see the module's closing note).

## The mechanism (cert §1, re-derived clean for Lean)

For a general chain `C`, write the partial products `Q_s = partProd C s = [[B_s,R_s],[D_s,H_s]]`. Two clean
`L`-recursive identities (verified exactly, `L ≤ 5`, `sympy/lc_check`):

* `partProd_toBlocks₁₁_succ`: `B_{s+1} = B_s · N_s · A_s` (`N_s = nMix C s`, `A_s = (C s)₁₁`).
* `partProd_toBlocks₂₁_succ`: `D_{s+1} = D_s · N_s · A_s + blockSchur(Q_s) · Z_s` (`Z_s = (C s)₂₁`).

The second gives the closed form `D_s = leftAccum C s · B_s` (`partProd_toBlocks₂₁_eq_leftAccum`), where
`leftAccum C s = ∑_{j<s} blockSchur(Q_j)·V_j·N_j⁻¹·B_j⁻¹` (`V_j = vDown C j`). Since the move preserves the
top row (`B̂_s = B_s`), preserving the left column reduces to `leftAccum (movedC …) L = leftAccum C L`.

## Status
Pure `Matrix`/`Ring` algebra over a general `CommRing`; no `deepestSplit`, no `Params`. `IsUnit`/`Invertible`
of the layer/partial pivots and the pivot-mix `N_s` is carried as explicit hypotheses (they hold at the
deepest point, where every pivot is `I`). Exact-verified `L ≤ 5, m ≤ 2, r ≤ 2` (cert §2 + `lc_check.py`).
-/

open Matrix
namespace DLNFibre.DLN.RLCT

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

section
variable {r : Type*} [Fintype r] [DecidableEq r] {α : Type*} [CommRing α]

/-! ## Block-multiplication helpers (the `r ⊕ ·` bottom-row block reads of a product) -/

omit [DecidableEq r] in
/-- The `(2,1)` block of a product `P * Q` of `r ⊕ ·`-blocked matrices:
`(P Q)₂₁ = P₂₁ Q₁₁ + P₂₂ Q₂₁`. -/
theorem toBlocks₂₁_mul {a b c : Type*} [Fintype b]
    (P : Matrix (r ⊕ a) (r ⊕ b) α) (Q : Matrix (r ⊕ b) (r ⊕ c) α) :
    (P * Q).toBlocks₂₁ = P.toBlocks₂₁ * Q.toBlocks₁₁ + P.toBlocks₂₂ * Q.toBlocks₂₁ := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks P, ← Matrix.fromBlocks_toBlocks Q]
  rw [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₁]

/-- The `(2,1)` block of the identity `2×2`-blocked matrix is `0`. -/
theorem toBlocks₂₁_one {a b : Type*} [DecidableEq a] [DecidableEq b] :
    (1 : Matrix (a ⊕ b) (a ⊕ b) α).toBlocks₂₁ = 0 := by
  rw [← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₂₁]

variable {m : ℕ → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]

/-! ## General-chain identities (any chain `C`, invertibility hypotheses) -/

/-- The pivot absorbs the normalised up-direction: `B_s · u_s = R_s` (`B_s = (partProd C s)₁₁`). -/
theorem pivot_mul_uNorm (C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α) (s : ℕ)
    (hB : IsUnit (partProd C s).toBlocks₁₁) :
    (partProd C s).toBlocks₁₁ * uNorm C s = (partProd C s).toBlocks₁₂ := by
  rw [uNorm, ← Matrix.mul_assoc, Ring.mul_inverse_cancel _ hB, Matrix.one_mul]

omit [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] in
/-- The normalised down-direction absorbs the layer pivot: `V_s · A_s = Z_s` (`Z_s = (C s)₂₁`). -/
theorem vDown_mul_pivot (C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α) (s : ℕ)
    (hA : IsUnit (C s).toBlocks₁₁) :
    vDown C s * (C s).toBlocks₁₁ = (C s).toBlocks₂₁ := by
  rw [vDown, Matrix.mul_assoc, Ring.inverse_mul_cancel _ hA, Matrix.mul_one]

/-- **The pivot-block recursion.** `B_{s+1} = B_s · N_s · A_s`. -/
theorem partProd_toBlocks₁₁_succ (C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α) (s : ℕ)
    (hB : IsUnit (partProd C s).toBlocks₁₁) (hA : IsUnit (C s).toBlocks₁₁) :
    (partProd C (s + 1)).toBlocks₁₁
      = (partProd C s).toBlocks₁₁ * nMix C s * (C s).toBlocks₁₁ := by
  have hstep : (partProd C (s + 1)).toBlocks₁₁
      = (partProd C s).toBlocks₁₁ * (C s).toBlocks₁₁
        + (partProd C s).toBlocks₁₂ * (C s).toBlocks₂₁ := by
    rw [show partProd C (s + 1) = partProd C s * C s from rfl, toBlocks₁₁_mul]
  rw [hstep, nMix, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul]
  congr 1
  rw [← Matrix.mul_assoc (partProd C s).toBlocks₁₁ (uNorm C s) (vDown C s),
    pivot_mul_uNorm C s hB,
    Matrix.mul_assoc (partProd C s).toBlocks₁₂ (vDown C s) (C s).toBlocks₁₁,
    vDown_mul_pivot C s hA]

/-- **The left-column recursion** (cert's re-derived clean form, the `L`-recursive heart). The bottom-left
block of the partial product satisfies `D_{s+1} = D_s · N_s · A_s + blockSchur(Q_s) · Z_s`. Uses only
`H_s = blockSchur(Q_s) + D_s · B_s⁻¹ · R_s` (`blockSchur` def) and the pivot cancellations. -/
theorem partProd_toBlocks₂₁_succ (C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α) (s : ℕ)
    (hA : IsUnit (C s).toBlocks₁₁) :
    (partProd C (s + 1)).toBlocks₂₁
      = (partProd C s).toBlocks₂₁ * nMix C s * (C s).toBlocks₁₁
        + blockSchur (partProd C s) * (C s).toBlocks₂₁ := by
  have hstep : (partProd C (s + 1)).toBlocks₂₁
      = (partProd C s).toBlocks₂₁ * (C s).toBlocks₁₁
        + (partProd C s).toBlocks₂₂ * (C s).toBlocks₂₁ := by
    rw [show partProd C (s + 1) = partProd C s * C s from rfl, toBlocks₂₁_mul]
  -- `D_s N_s A_s = D_s A_s + D_s · B_s⁻¹ R_s · Z_s` (the `1 + u V` expansion, `V A = Z`).
  have hDNA : (partProd C s).toBlocks₂₁ * nMix C s * (C s).toBlocks₁₁
      = (partProd C s).toBlocks₂₁ * (C s).toBlocks₁₁
        + (partProd C s).toBlocks₂₁
            * (Ring.inverse (partProd C s).toBlocks₁₁ * (partProd C s).toBlocks₁₂)
            * (C s).toBlocks₂₁ := by
    rw [nMix, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul]
    congr 1
    rw [uNorm, ← Matrix.mul_assoc (partProd C s).toBlocks₂₁
        (Ring.inverse (partProd C s).toBlocks₁₁ * (partProd C s).toBlocks₁₂) (vDown C s),
      Matrix.mul_assoc ((partProd C s).toBlocks₂₁
        * (Ring.inverse (partProd C s).toBlocks₁₁ * (partProd C s).toBlocks₁₂)) (vDown C s)
        (C s).toBlocks₁₁, vDown_mul_pivot C s hA]
  -- `H_s = blockSchur(Q_s) + D_s · B_s⁻¹ R_s`.
  have hH : (partProd C s).toBlocks₂₂
      = blockSchur (partProd C s)
        + (partProd C s).toBlocks₂₁ * Ring.inverse (partProd C s).toBlocks₁₁
            * (partProd C s).toBlocks₁₂ := by
    rw [blockSchur]; abel
  rw [hstep, hDNA, hH, Matrix.add_mul, Matrix.mul_assoc (partProd C s).toBlocks₂₁
      (Ring.inverse (partProd C s).toBlocks₁₁) (partProd C s).toBlocks₁₂]
  abel

/-- The `j`-th left-column increment `blockSchur(Q_j)·V_j·N_j⁻¹·B_j⁻¹`
(`Q_j = partProd C j`, `V_j = vDown C j`, `N_j = nMix C j`, `B_j = (partProd C j)₁₁`). -/
noncomputable def gTerm (C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α) (j : ℕ) :
    Matrix (m 0) r α :=
  blockSchur (partProd C j) * vDown C j * Ring.inverse (nMix C j)
    * Ring.inverse (partProd C j).toBlocks₁₁

/-- The left-column accumulator `leftAccum C L = ∑_{j<L} gTerm C j`. -/
noncomputable def leftAccum (C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α) (L : ℕ) :
    Matrix (m 0) r α :=
  ∑ j ∈ Finset.range L, gTerm C j

/-- **The closed form for the bottom-left block.** `D_L = leftAccum C L · B_L`. Induction on `L` using
the pivot recursion `partProd_toBlocks₁₁_succ` and the left-column recursion `partProd_toBlocks₂₁_succ`;
the accumulator's `N_j⁻¹`/`B_j⁻¹` cancel against the recursion's `B_{s+1} = B_s N_s A_s`. -/
theorem partProd_toBlocks₂₁_eq_leftAccum (C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α) (L : ℕ)
    (hP : ∀ k, IsUnit (partProd C k).toBlocks₁₁) (hA : ∀ k, IsUnit (C k).toBlocks₁₁)
    (hN : ∀ k, IsUnit (nMix C k)) :
    (partProd C L).toBlocks₂₁ = leftAccum C L * (partProd C L).toBlocks₁₁ := by
  induction L with
  | zero =>
    rw [show partProd C 0 = 1 from rfl, toBlocks₂₁_one, leftAccum, Finset.range_zero,
      Finset.sum_empty, Matrix.zero_mul]
  | succ n ih =>
    have hla : leftAccum C (n + 1)
        = leftAccum C n + blockSchur (partProd C n) * vDown C n * Ring.inverse (nMix C n)
            * Ring.inverse (partProd C n).toBlocks₁₁ := by
      rw [leftAccum, Finset.sum_range_succ, ← leftAccum, gTerm]
    rw [partProd_toBlocks₂₁_succ C n (hA n), ih, hla,
      partProd_toBlocks₁₁_succ C n (hP n) (hA n), Matrix.add_mul]
    congr 1
    · -- `(leftAccum C n · B_n) · N_n · A_n = leftAccum C n · (B_n · N_n · A_n)`.
      rw [Matrix.mul_assoc (leftAccum C n) (partProd C n).toBlocks₁₁ (nMix C n),
        Matrix.mul_assoc (leftAccum C n) ((partProd C n).toBlocks₁₁ * nMix C n) (C n).toBlocks₁₁]
    · -- `g_n · (B_n · N_n · A_n) = blockSchur(Q_n) · Z_n` (the cancellation).
      simp only [Matrix.mul_assoc]
      rw [Ring.inverse_mul_cancel_left _ _ (hP n), Ring.inverse_mul_cancel_left _ _ (hN n),
        vDown_mul_pivot C n (hA n)]

/-! ## Moved-chain relating lemmas (the move's data agrees with `C`'s, up to the `Ŵ`/`Z₀` shift) -/

/-- The zeroth normalised up-direction vanishes (`u_0 = 0`), since `R_0 = (partProd C 0)₁₂ = 0`. -/
theorem uNorm_zero (C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α) : uNorm C 0 = 0 := by
  rw [uNorm, show partProd C 0 = 1 from rfl, toBlocks₁₂_one, Matrix.mul_zero]

/-- The move preserves the normalised up-direction: `û_s = u_s` (the top row is preserved). -/
theorem uNorm_movedC (C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α) (Z0edit : Matrix (m 0) r α)
    (hB : ∀ s, IsUnit (partProd C s).toBlocks₁₁) (hNu : ∀ s, IsUnit (nMix C s)) (s : ℕ) :
    uNorm (movedC C Z0edit) s = uNorm C s := by
  rw [uNorm, uNorm, (topRow_movedC C Z0edit hB hNu s).1, (topRow_movedC C Z0edit hB hNu s).2]

/-- The move preserves the normalised down-direction at layers `s ≥ 1` (`Ẑ_{s+1} = Z_{s+1}`). -/
theorem vDown_movedC_succ (C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α)
    (Z0edit : Matrix (m 0) r α) (s : ℕ) :
    vDown (movedC C Z0edit) (s + 1) = vDown C (s + 1) := by
  rw [vDown, vDown, movedC, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₁₁]
  rfl

/-- The move preserves the pivot-mix `N_s` (`û_s = u_s`; at `s = 0` both are `1` since `u_0 = 0`). -/
theorem nMix_movedC (C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α) (Z0edit : Matrix (m 0) r α)
    (hB : ∀ s, IsUnit (partProd C s).toBlocks₁₁) (hNu : ∀ s, IsUnit (nMix C s)) (s : ℕ) :
    nMix (movedC C Z0edit) s = nMix C s := by
  rw [nMix, nMix, uNorm_movedC C Z0edit hB hNu s]
  cases s with
  | zero => rw [uNorm_zero, Matrix.zero_mul, Matrix.zero_mul]
  | succ n => rw [vDown_movedC_succ]

/-- The move preserves the off-pivot coupling `K_s` (`Ẑ_s` only enters through `R_s`, and `R_0 = 0`;
for `s ≥ 1`, `Ẑ_s = Z_s`). -/
theorem Kcoup_movedC (C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α) (Z0edit : Matrix (m 0) r α)
    (hB : ∀ s, IsUnit (partProd C s).toBlocks₁₁) (hNu : ∀ s, IsUnit (nMix C s)) (s : ℕ) :
    Kcoup (movedC C Z0edit) s = Kcoup C s := by
  rw [Kcoup, Kcoup, (topRow_movedC C Z0edit hB hNu (s + 1)).1,
    (topRow_movedC C Z0edit hB hNu s).2,
    show (movedC C Z0edit s).toBlocks₂₁ = movedZ C Z0edit s from by
      rw [movedC, Matrix.toBlocks_fromBlocks₂₁]]
  cases s with
  | zero =>
    rw [show (partProd C 0).toBlocks₁₂ = 0 from by
        rw [show partProd C 0 = 1 from rfl, toBlocks₁₂_one], Matrix.mul_zero, Matrix.mul_zero]
  | succ n => rfl

/-- The accumulated Schur factor of the moved partial products, `Ŵ_s = ∏_{j<s} (1−K_j)·S̃_j`
(`Ŵ_0 = 1`). This is `Z₀`-free (it uses only `C`'s couplings and the targets `S̃_j = schurTilde C j`). -/
noncomputable def wHatAccum (C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α) :
    (k : ℕ) → Matrix (m 0) (m k) α
  | 0 => 1
  | k + 1 => wHatAccum C k * (1 - Kcoup C k) * schurTilde C k

/-- **The moved partial-product Schur complement is `Ŵ_s`.** `blockSchur(Q̂_s) = coreProd(movedC) s`
(the Schur recursion `schur_product_ldu_rec` on the moved chain), and `coreProd(movedC) s = wHatAccum C s`
(each factor is `(1−K_j)·S̃_j` via `Kcoup_movedC` + `blockSchur_movedC`, independent of `Z₀`). -/
theorem blockSchur_partProd_movedC (C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α)
    (Z0edit : Matrix (m 0) r α) (hB : ∀ s, IsUnit (partProd C s).toBlocks₁₁)
    (hNu : ∀ s, IsUnit (nMix C s)) (hA : ∀ k, IsUnit (C k).toBlocks₁₁) (s : ℕ) :
    blockSchur (partProd (movedC C Z0edit) s) = wHatAccum C s := by
  have hcore : ∀ k, coreProd (movedC C Z0edit) k = wHatAccum C k := by
    intro k
    induction k with
    | zero => rfl
    | succ n ih =>
      rw [coreProd, wHatAccum, ih, Kcoup_movedC C Z0edit hB hNu n, blockSchur_movedC]
  rw [← hcore s]
  refine schur_product_ldu_rec (movedC C Z0edit) s (fun k _ => ?_) (fun k _ => ?_)
  · rw [show (movedC C Z0edit k).toBlocks₁₁ = (C k).toBlocks₁₁ from by
        rw [movedC, Matrix.toBlocks_fromBlocks₁₁]]
    exact (hA k).invertible
  · rw [(topRow_movedC C Z0edit hB hNu k).1]
    exact (hB k).invertible

/-! ## Zeroth-layer simplifications (`Q_0 = 1` ⟹ every normalised datum is trivial) -/

/-- The `(2,2)` block of the identity `2×2`-blocked matrix is the identity. -/
theorem toBlocks₂₂_one {a b : Type*} [DecidableEq a] [DecidableEq b] :
    (1 : Matrix (a ⊕ b) (a ⊕ b) α).toBlocks₂₂ = 1 := by
  rw [← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₂₂]

/-- The zeroth partial Schur complement is `1` (`blockSchur(Q_0) = blockSchur 1 = 1`). -/
theorem blockSchur_partProd_zero (C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α) :
    blockSchur (partProd C 0) = 1 := by
  rw [show partProd C 0 = 1 from rfl, blockSchur, toBlocks₂₂_one, toBlocks₂₁_one, Matrix.zero_mul,
    Matrix.zero_mul, sub_zero]

/-- The zeroth pivot-mix is `1` (`N_0 = 1 + u_0·V_0 = 1` since `u_0 = 0`). -/
theorem nMix_zero (C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α) : nMix C 0 = 1 := by
  rw [nMix, uNorm_zero, Matrix.zero_mul, add_zero]

/-- The zeroth left-column increment is the raw normalised down-direction `g_0 = V_0` (every other
factor is `1`). -/
theorem gTerm_zero (C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α) : gTerm C 0 = vDown C 0 := by
  rw [gTerm, blockSchur_partProd_zero, nMix_zero,
    show (partProd C 0).toBlocks₁₁ = 1 from by rw [show partProd C 0 = 1 from rfl, toBlocks₁₁_one],
    Ring.inverse_one, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one]

/-! ## The left-column accumulator agrees, and the bottom-left block is restored -/

/-- The `j`-th `deltaV0` summand `(blockSchur(Q_j) − Ŵ_j)·V_j·N_j⁻¹·B_j⁻¹`. -/
noncomputable def hTermLC (C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α) (j : ℕ) :
    Matrix (m 0) r α :=
  (blockSchur (partProd C j) - wHatAccum C j) * vDown C j * Ring.inverse (nMix C j)
    * Ring.inverse (partProd C j).toBlocks₁₁

/-- The zeroth `deltaV0` summand vanishes (`blockSchur(Q_0) = Ŵ_0 = 1`). -/
theorem hTermLC_zero (C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α) : hTermLC C 0 = 0 := by
  rw [hTermLC, blockSchur_partProd_zero, show wHatAccum C 0 = 1 from rfl, sub_self,
    Matrix.zero_mul, Matrix.zero_mul, Matrix.zero_mul]

/-- The left-column mismatch `ΔV_0 = ∑_{j<L}(blockSchur(Q_j) − Ŵ_j)·V_j·N_j⁻¹·B_j⁻¹` (cert `a_L − ã_L`).
Its `j = 0` summand is `0`, so the sum effectively runs from `j = 1`. -/
noncomputable def deltaV0 (C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α) (L : ℕ) :
    Matrix (m 0) r α :=
  ∑ j ∈ Finset.range L, hTermLC C j

/-- The concrete `Z₀` override: `Z'_0 = Z_0 + ΔV_0·A_0` (cert `(V_0 + ΔV_0)·A_0`). -/
noncomputable def Z0edit0 (C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α) (L : ℕ) :
    Matrix (m 0) r α :=
  (C 0).toBlocks₂₁ + deltaV0 C L * (C 0).toBlocks₁₁

/-- **The moved accumulator agrees with the original.** With the `Z₀` override `Z0edit0 C L`, the moved
chain's left-column accumulator equals the original's: `leftAccum (movedC C (Z0edit0 C L)) L =
leftAccum C L`. The per-layer increment difference is `Ŵ_j·V_j·N_j⁻¹·B_j⁻¹ − blockSchur(Q_j)·V_j·…`,
which sums to `−ΔV_0`; the `j = 0` down-edit `V̂_0 − V_0 = ΔV_0` (cert §1) cancels it. -/
theorem leftAccum_movedC (C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α) (L : ℕ)
    (hP : ∀ k, IsUnit (partProd C k).toBlocks₁₁) (hA : ∀ k, IsUnit (C k).toBlocks₁₁)
    (hN : ∀ k, IsUnit (nMix C k)) (hL : 1 ≤ L) :
    leftAccum (movedC C (Z0edit0 C L)) L = leftAccum C L := by
  set Z0e := Z0edit0 C L with hZ0e
  have hdiff : ∀ j ∈ Finset.range L,
      gTerm (movedC C Z0e) j - gTerm C j
        = (if j = 0 then deltaV0 C L else 0) - hTermLC C j := by
    intro j _
    cases j with
    | zero =>
      rw [if_pos rfl, hTermLC_zero, sub_zero, gTerm_zero (movedC C Z0e), gTerm_zero C]
      simp only [vDown]
      rw [show (movedC C Z0e 0).toBlocks₂₁ = Z0e from by
          rw [movedC, Matrix.toBlocks_fromBlocks₂₁]; rfl,
        show (movedC C Z0e 0).toBlocks₁₁ = (C 0).toBlocks₁₁ from by
          rw [movedC, Matrix.toBlocks_fromBlocks₁₁],
        hZ0e, Z0edit0, Matrix.add_mul,
        Matrix.mul_assoc (deltaV0 C L) (C 0).toBlocks₁₁ (Ring.inverse (C 0).toBlocks₁₁),
        Ring.mul_inverse_cancel _ (hA 0), Matrix.mul_one]
      abel
    | succ n =>
      rw [if_neg (by omega : ¬(n + 1 = 0))]
      simp only [gTerm, hTermLC]
      rw [blockSchur_partProd_movedC C Z0e hP hN hA (n + 1), vDown_movedC_succ C Z0e n,
        nMix_movedC C Z0e hP hN (n + 1), (topRow_movedC C Z0e hP hN (n + 1)).1]
      simp only [Matrix.sub_mul]
      abel
  rw [leftAccum, leftAccum, ← sub_eq_zero, ← Finset.sum_sub_distrib, Finset.sum_congr rfl hdiff,
    Finset.sum_sub_distrib, Finset.sum_ite_eq' (Finset.range L) 0 (fun _ => deltaV0 C L),
    if_pos (Finset.mem_range.mpr hL), ← deltaV0, sub_self]

/-- **Invariant A, left-column half.** With the `Z₀` override `Z0edit0 C L`, the moved chain restores the
bottom-left block of the full product: `(partProd (movedC C (Z0edit0 C L)) L)₂₁ = (partProd C L)₂₁`.
Combines the closed form `partProd_toBlocks₂₁_eq_leftAccum` on both chains with the accumulator agreement
`leftAccum_movedC` and the banked top-row preservation `topRow_movedC`. -/
theorem leftCol_movedC (C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α) (L : ℕ)
    (hP : ∀ k, IsUnit (partProd C k).toBlocks₁₁) (hA : ∀ k, IsUnit (C k).toBlocks₁₁)
    (hN : ∀ k, IsUnit (nMix C k)) (hL : 1 ≤ L) :
    (partProd (movedC C (Z0edit0 C L)) L).toBlocks₂₁ = (partProd C L).toBlocks₂₁ := by
  have hPm : ∀ k, IsUnit (partProd (movedC C (Z0edit0 C L)) k).toBlocks₁₁ := fun k => by
    rw [(topRow_movedC C (Z0edit0 C L) hP hN k).1]; exact hP k
  have hAm : ∀ k, IsUnit (movedC C (Z0edit0 C L) k).toBlocks₁₁ := fun k => by
    rw [show (movedC C (Z0edit0 C L) k).toBlocks₁₁ = (C k).toBlocks₁₁ from by
      rw [movedC, Matrix.toBlocks_fromBlocks₁₁]]
    exact hA k
  have hNm : ∀ k, IsUnit (nMix (movedC C (Z0edit0 C L)) k) := fun k => by
    rw [nMix_movedC C (Z0edit0 C L) hP hN k]; exact hN k
  rw [partProd_toBlocks₂₁_eq_leftAccum (movedC C (Z0edit0 C L)) L hPm hAm hNm,
    partProd_toBlocks₂₁_eq_leftAccum C L hP hA hN, leftAccum_movedC C L hP hA hN hL,
    (topRow_movedC C (Z0edit0 C L) hP hN L).1]

/-- **Invariant A, abstract (both halves).** With the `Z₀` override `Z0edit0 C L`, the moved chain
preserves all three reg-residual blocks of the full product — the top block-row (`(P₁₁, P₁₂)`, the
banked `topRow_movedC`) and the bottom-left block (`P₂₁`, the `leftCol_movedC` above). This is the
abstract heart of the reg-preservation germ `hsub3reg` (`deepestEFull` is invariant under the move). -/
theorem regBlocks_movedC (C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α) (L : ℕ)
    (hP : ∀ k, IsUnit (partProd C k).toBlocks₁₁) (hA : ∀ k, IsUnit (C k).toBlocks₁₁)
    (hN : ∀ k, IsUnit (nMix C k)) (hL : 1 ≤ L) :
    (partProd (movedC C (Z0edit0 C L)) L).toBlocks₁₁ = (partProd C L).toBlocks₁₁
      ∧ (partProd (movedC C (Z0edit0 C L)) L).toBlocks₁₂ = (partProd C L).toBlocks₁₂
      ∧ (partProd (movedC C (Z0edit0 C L)) L).toBlocks₂₁ = (partProd C L).toBlocks₂₁ :=
  ⟨(topRow_movedC C (Z0edit0 C L) hP hN L).1, (topRow_movedC C (Z0edit0 C L) hP hN L).2,
    leftCol_movedC C L hP hA hN hL⟩

/-! ## Non-vacuity witness

The hypotheses of `leftCol_movedC` are satisfiable and the identity applies: for the constant chain of
identity layers (`r = Fin 1`, core `Fin 1`, over `ℚ`) every layer pivot is `1`, every partial-product
pivot is `1`, and every pivot-mix `nMix` is `1` (the down blocks vanish), so all three `IsUnit`
hypotheses hold and `leftCol_movedC` fires at `L = 3`. This rules out vacuity-by-unsatisfiable-hypotheses.
(For this constant chain `ΔV₀ = 0`; the genuine `ΔV₀ ≠ 0` regime at `L ≥ 3` is the theorem's content,
exact-verified `L ≤ 5, m ≤ 3` in the cert.) -/
example :
    let C : (s : ℕ) →
        Matrix (Fin 1 ⊕ (fun _ : ℕ => Fin 1) s) (Fin 1 ⊕ (fun _ : ℕ => Fin 1) (s + 1)) ℚ :=
      fun _ => 1
    (partProd (movedC C (Z0edit0 C 3)) 3).toBlocks₂₁ = (partProd C 3).toBlocks₂₁ := by
  intro C
  have hone : ∀ k, partProd C k = 1 := by
    intro k
    induction k with
    | zero => rfl
    | succ n ih => rw [partProd, ih, one_mul]
  have hN1 : ∀ k, nMix C k = 1 := by
    intro k
    rw [nMix, vDown, show C k = 1 from rfl, toBlocks₂₁_one, Matrix.zero_mul, Matrix.mul_zero, add_zero]
  refine leftCol_movedC C 3 (fun k => ?_) (fun k => ?_) (fun k => ?_) (by norm_num)
  · rw [hone k, toBlocks₁₁_one]; exact isUnit_one
  · rw [show C k = 1 from rfl, toBlocks₁₁_one]; exact isUnit_one
  · rw [hN1 k]; exact isUnit_one

end
end DLNFibre.DLN.RLCT
