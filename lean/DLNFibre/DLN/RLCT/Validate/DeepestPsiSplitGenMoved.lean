import DLNFibre.DLN.RLCT.Validate.DeepestSchurRecursion

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestPsiSplitGenMoved` — the abstract moved-chain algebra (#120 `hstep2`)

The network-free algebraic core of the general-`L` joint move `psiSplitRawGen` (cert
`expeditions/2026-06-20-aoyagi-full/threads/genm-d1psidesign/cert.md`). Working over the same abstract
`Type`-valued chain as `DeepestSchurRecursion` (a width family `m : ℕ → Type*`, layer `s` of shape
`Matrix (r ⊕ m s) (r ⊕ m (s+1))`, cast-free `partProd`), this module builds the **moved chain** `movedC`
— the cert's joint move in coordinates — and discharges the two invariants at the abstract level:

* **Invariant B (core untwist).** Each moved layer's Schur complement is the target
  `S̃_s = (1 − K_s)·S_s` (`blockSchur_movedC`), and the plain product of the moved Schur cores equals
  `blockSchur (partProd C L)` (`prodSchurCore_eq_blockSchur_partProd`, via `schur_product_ldu_rec`). This
  is the abstract heart of `hsub4core` (the conj-absorb reads `Score = ‖blockSchur(P)‖²`).

* **Invariant A, top-row half.** The up-edit `Y'_s = Y_s + N_s⁻¹ u_s (S_s − S̃_s)` leaves the top
  block-row `((partProd)₁₁, (partProd)₁₂)` of every partial product unchanged — for **any** `Z₀` down
  override (`topRow_movedC`). At `s = L` this is `(P'11, P'12) = (P11, P12)`, the clean half of `hsub3reg`.
  The down half (`(partProd)₂₁ = P21` via the `Z₀` accumulator) is the remaining `L`-recursive lemma.

The move fixes pivots (`A_s = (C s)₁₁`), edits every up-block, edits one down-block `Z₀`, and reconstructs
cores by `T'_s = S̃_s + Z'_s A_s⁻¹ Y'_s`. Exact-verified `L ≤ 5, m ≤ 3, r ≤ 2` (cert §2, `codex_construction.py`).

## Status
Pure `Matrix`/`Ring` algebra over a general `CommRing`; no `deepestSplit`, no `Params`. Invertibility of
the layer/partial pivots and of the pivot-mix `N_s` is carried as explicit `IsUnit`/`Invertible`
hypotheses (they hold at the deepest point, where every pivot is `I`). The `Fin`-side bridge to the DLN
`framedParamsPivot` product is downstream wiring (see `DeepestSchurRecursion`'s note).
-/

open Matrix
namespace DLNFibre.DLN.RLCT

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

section
variable {r : Type*} [Fintype r] [DecidableEq r] {α : Type*} [CommRing α]

/-! ## Block-multiplication helpers (the `r ⊕ ·` top-row block reads of a product) -/

omit [DecidableEq r] in
/-- The `(1,1)` block of a product `P * Q` of `r ⊕ ·`-blocked matrices:
`(P Q)₁₁ = P₁₁ Q₁₁ + P₁₂ Q₂₁`. -/
theorem toBlocks₁₁_mul {a b c : Type*} [Fintype b]
    (P : Matrix (r ⊕ a) (r ⊕ b) α) (Q : Matrix (r ⊕ b) (r ⊕ c) α) :
    (P * Q).toBlocks₁₁ = P.toBlocks₁₁ * Q.toBlocks₁₁ + P.toBlocks₁₂ * Q.toBlocks₂₁ := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks P, ← Matrix.fromBlocks_toBlocks Q]
  rw [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁]

omit [DecidableEq r] in
/-- The `(1,2)` block of a product `P * Q` of `r ⊕ ·`-blocked matrices:
`(P Q)₁₂ = P₁₁ Q₁₂ + P₁₂ Q₂₂`. -/
theorem toBlocks₁₂_mul {a b c : Type*} [Fintype b]
    (P : Matrix (r ⊕ a) (r ⊕ b) α) (Q : Matrix (r ⊕ b) (r ⊕ c) α) :
    (P * Q).toBlocks₁₂ = P.toBlocks₁₁ * Q.toBlocks₁₂ + P.toBlocks₁₂ * Q.toBlocks₂₂ := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks P, ← Matrix.fromBlocks_toBlocks Q]
  rw [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₂]

variable {m : ℕ → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]

/-! ## The normalised partial data (cert §0: `u_s, V_s, N_s`) -/

/-- Normalised up-direction `u_s = B_s⁻¹ R_s`, with `B_s = (partProd C s)₁₁`, `R_s = (partProd C s)₁₂`. -/
noncomputable def uNorm (C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α) (s : ℕ) :
    Matrix r (m s) α :=
  Ring.inverse (partProd C s).toBlocks₁₁ * (partProd C s).toBlocks₁₂

/-- Normalised down-direction `V_s = Z_s A_s⁻¹ = (C s)₂₁ · A_s⁻¹`. -/
noncomputable def vDown (C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α) (s : ℕ) :
    Matrix (m s) r α :=
  (C s).toBlocks₂₁ * Ring.inverse (C s).toBlocks₁₁

/-- The pivot-mix `N_s = I + u_s V_s` (unit near the deepest point, where `N_s = I`). -/
noncomputable def nMix (C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α) (s : ℕ) :
    Matrix r r α :=
  1 + uNorm C s * vDown C s

/-- The per-layer Schur target `S̃_s = (1 − K_s)·S_s`, `K_s = Kcoup C s`, `S_s = blockSchur (C s)`. -/
noncomputable def schurTilde (C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α) (s : ℕ) :
    Matrix (m s) (m (s + 1)) α :=
  (1 - Kcoup C s) * blockSchur (C s)

/-- The up-edit `ΔY_s = N_s⁻¹ u_s (S_s − S̃_s)` (the amount added to `Y_s`). -/
noncomputable def upEdit (C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α) (s : ℕ) :
    Matrix r (m (s + 1)) α :=
  Ring.inverse (nMix C s) * uNorm C s * (blockSchur (C s) - schurTilde C s)

/-! ## The moved chain (cert §1: pivots fixed; up-edit all layers; `Z₀` override; cores) -/

/-- The moved down-block: the `Z₀` override at layer `0`, else the original `Z_s = (C s)₂₁`. -/
def movedZ (C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α) (Z0edit : Matrix (m 0) r α) :
    (s : ℕ) → Matrix (m s) r α
  | 0 => Z0edit
  | (s + 1) => (C (s + 1)).toBlocks₂₁

/-- The moved up-block `Y'_s = Y_s + ΔY_s` (independent of the `Z₀` override). -/
noncomputable def movedY (C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α) (s : ℕ) :
    Matrix r (m (s + 1)) α :=
  (C s).toBlocks₁₂ + upEdit C s

/-- The moved core `T'_s = S̃_s + Z'_s A_s⁻¹ Y'_s` (so the moved Schur complement is exactly `S̃_s`). -/
noncomputable def movedT (C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α)
    (Z0edit : Matrix (m 0) r α) (s : ℕ) : Matrix (m s) (m (s + 1)) α :=
  schurTilde C s + movedZ C Z0edit s * Ring.inverse (C s).toBlocks₁₁ * movedY C s

/-- The moved layer `Ĉ_s = [[A_s, Y'_s],[Z'_s, T'_s]]`. -/
noncomputable def movedC (C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α)
    (Z0edit : Matrix (m 0) r α) (s : ℕ) : Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α :=
  Matrix.fromBlocks (C s).toBlocks₁₁ (movedY C s) (movedZ C Z0edit s) (movedT C Z0edit s)

/-! ## Invariant B — the moved Schur cores -/

/-- **Invariant B, per layer.** The moved layer's Schur complement is the target `S̃_s`. Immediate: the
core reconstruction `T'_s = S̃_s + Z'_s A_s⁻¹ Y'_s` makes the `Z'_s A_s⁻¹ Y'_s` terms cancel. -/
theorem blockSchur_movedC (C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α)
    (Z0edit : Matrix (m 0) r α) (s : ℕ) :
    blockSchur (movedC C Z0edit s) = schurTilde C s := by
  unfold blockSchur movedC
  rw [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁,
    Matrix.toBlocks_fromBlocks₂₂, movedT, add_sub_cancel_right]

/-- The plain product of the moved Schur cores `∏_{s<k} blockSchur (movedC C Z0edit s)`
(`prodSchurCore C Z0edit 0 = 1`). -/
noncomputable def prodSchurCore (C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α)
    (Z0edit : Matrix (m 0) r α) : (k : ℕ) → Matrix (m 0) (m k) α
  | 0 => 1
  | k + 1 => prodSchurCore C Z0edit k * blockSchur (movedC C Z0edit k)

/-- The plain product of the moved Schur cores equals the original chain's `coreProd`. Each factor is
`(1 − K_s)·S_s` (`blockSchur_movedC` + `schurTilde`), matching the `coreProd` fold up to associativity. -/
theorem prodSchurCore_eq_coreProd (C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α)
    (Z0edit : Matrix (m 0) r α) (k : ℕ) :
    prodSchurCore C Z0edit k = coreProd C k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    rw [prodSchurCore, coreProd, ih, blockSchur_movedC, schurTilde, ← Matrix.mul_assoc]

/-- **Invariant B, global.** The plain product of the moved Schur cores equals the Schur complement of
the original full product `blockSchur (partProd C L)` — the `Score` the conj-absorb reads. Combines
`prodSchurCore_eq_coreProd` with the banked Schur-product recursion `schur_product_ldu_rec`. -/
theorem prodSchurCore_eq_blockSchur_partProd (C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α)
    (Z0edit : Matrix (m 0) r α) (L : ℕ)
    (hLayer : ∀ k, k < L → Invertible (C k).toBlocks₁₁)
    (hPart : ∀ k, k ≤ L → Invertible (partProd C k).toBlocks₁₁) :
    prodSchurCore C Z0edit L = blockSchur (partProd C L) := by
  rw [prodSchurCore_eq_coreProd]
  exact (schur_product_ldu_rec C L hLayer hPart).symm

/-! ## Invariant A — the top-row lemma -/

/-- The `Z₀` override is invisible to the left column of the partial products through the `(1,2)` block:
`R_s · Z'_s = R_s · Z_s`. At `s = 0`, `R_0 = 0`; at `s ≥ 1`, `Z'_s = Z_s` definitionally. -/
theorem R_mul_movedZ (C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α)
    (Z0edit : Matrix (m 0) r α) (s : ℕ) :
    (partProd C s).toBlocks₁₂ * movedZ C Z0edit s
      = (partProd C s).toBlocks₁₂ * (C s).toBlocks₂₁ := by
  cases s with
  | zero =>
    rw [show partProd C 0 = 1 from rfl, toBlocks₁₂_one, Matrix.zero_mul, Matrix.zero_mul]
  | succ n => rfl

/-- The up-edit cancellation (abstract, distributed): `B·ΔY + R·(V·ΔY) = R·D` with `ΔY = N⁻¹ u D`.
With `B·u = R` (`R = B_s u_s`) and `N = 1 + u V` a unit, `(B + R V) = B N`, so
`(B + R V)·ΔY = B N N⁻¹ u D = B u D = R D`, and distributing `(B + R V)·ΔY` gives the stated form. -/
theorem cancel_up {ρ σ τ : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype σ]
    (B N : Matrix ρ ρ α) (u : Matrix ρ σ α) (V : Matrix σ ρ α) (R : Matrix ρ σ α) (D : Matrix σ τ α)
    (hRu : B * u = R) (hN : N = 1 + u * V) (hNunit : IsUnit N) :
    B * (Ring.inverse N * u * D) + R * (V * (Ring.inverse N * u * D)) = R * D := by
  have hBN : B + R * V = B * N := by
    conv_rhs => rw [hN, Matrix.mul_add, Matrix.mul_one]
    rw [← hRu, Matrix.mul_assoc]
  have hkey : (B + R * V) * (Ring.inverse N * u * D) = R * D := by
    rw [hBN, Matrix.mul_assoc B N, ← Matrix.mul_assoc N (Ring.inverse N * u) D,
      ← Matrix.mul_assoc N (Ring.inverse N) u, Ring.mul_inverse_cancel N hNunit, Matrix.one_mul,
      ← Matrix.mul_assoc B u D, hRu]
  rw [← hkey, Matrix.add_mul, Matrix.mul_assoc R V]

/-- The top-right-block recursion step (abstract). Given the original core relation `T = S + V·Y`, the
`Z₀`-invisibility `R·(Zt·Ainv) = R·V`, and the up-edit cancellation `key`, the moved layer preserves the
top-right block: `B·Y' + R·T' = B·Y + R·T` (with `Y' = Y + ΔY`, `T' = S̃ + Zt·Ainv·Y'`). -/
theorem Rstep {ρ σ σ' : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype σ]
    (B : Matrix ρ ρ α) (R : Matrix ρ σ α) (V : Matrix σ ρ α)
    (Y ΔY : Matrix ρ σ' α) (Sc St T : Matrix σ σ' α) (Ainv : Matrix ρ ρ α) (Zt : Matrix σ ρ α)
    (hT : T = Sc + V * Y)
    (hWV : R * (Zt * Ainv) = R * V)
    (key : B * ΔY + R * (V * ΔY) = R * (Sc - St)) :
    B * (Y + ΔY) + R * (St + Zt * Ainv * (Y + ΔY)) = B * Y + R * T := by
  have hWterm : R * (Zt * Ainv * (Y + ΔY)) = R * (V * (Y + ΔY)) := by
    rw [← Matrix.mul_assoc R (Zt * Ainv) (Y + ΔY), hWV, Matrix.mul_assoc R V (Y + ΔY)]
  have expand_key : B * ΔY + R * (V * ΔY) + R * St = R * Sc := by
    rw [key, Matrix.mul_sub]; abel
  rw [hT, Matrix.mul_add B Y ΔY, Matrix.mul_add R St (Zt * Ainv * (Y + ΔY)), hWterm,
    Matrix.mul_add V Y ΔY, Matrix.mul_add R (V * Y) (V * ΔY), Matrix.mul_add R Sc (V * Y),
    ← expand_key]
  abel

/-- **Invariant A, top-row half.** For any `Z₀` override, the moved chain preserves the top block-row
`((partProd)₁₁, (partProd)₁₂)` of every partial product. Induction on `s`: the pivot block via
`R_mul_movedZ` (the `Z₀` edit is invisible), the up block via `Rstep` (the up-edit cancels). At `s = L`
this is `(P'11, P'12) = (P11, P12)`. Carries `IsUnit` on the partial pivots `B_s` and the pivot-mix
`N_s` (both hold at the deepest point). -/
theorem topRow_movedC (C : (s : ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α)
    (Z0edit : Matrix (m 0) r α)
    (hB : ∀ s, IsUnit (partProd C s).toBlocks₁₁) (hNu : ∀ s, IsUnit (nMix C s)) (s : ℕ) :
    (partProd (movedC C Z0edit) s).toBlocks₁₁ = (partProd C s).toBlocks₁₁
      ∧ (partProd (movedC C Z0edit) s).toBlocks₁₂ = (partProd C s).toBlocks₁₂ := by
  induction s with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    obtain ⟨ih11, ih12⟩ := ih
    have hm11 : (movedC C Z0edit n).toBlocks₁₁ = (C n).toBlocks₁₁ := by
      rw [movedC, Matrix.toBlocks_fromBlocks₁₁]
    have hm12 : (movedC C Z0edit n).toBlocks₁₂ = movedY C n := by
      rw [movedC, Matrix.toBlocks_fromBlocks₁₂]
    have hm21 : (movedC C Z0edit n).toBlocks₂₁ = movedZ C Z0edit n := by
      rw [movedC, Matrix.toBlocks_fromBlocks₂₁]
    have hm22 : (movedC C Z0edit n).toBlocks₂₂ = movedT C Z0edit n := by
      rw [movedC, Matrix.toBlocks_fromBlocks₂₂]
    refine ⟨?_, ?_⟩
    · -- pivot block `(partProd)₁₁`
      have lhs : (partProd (movedC C Z0edit) (n + 1)).toBlocks₁₁
          = (partProd C n).toBlocks₁₁ * (C n).toBlocks₁₁
            + (partProd C n).toBlocks₁₂ * movedZ C Z0edit n := by
        rw [show partProd (movedC C Z0edit) (n + 1)
            = partProd (movedC C Z0edit) n * movedC C Z0edit n from rfl,
          toBlocks₁₁_mul, hm11, hm21, ih11, ih12]
      have rhs : (partProd C (n + 1)).toBlocks₁₁
          = (partProd C n).toBlocks₁₁ * (C n).toBlocks₁₁
            + (partProd C n).toBlocks₁₂ * (C n).toBlocks₂₁ := by
        rw [show partProd C (n + 1) = partProd C n * C n from rfl, toBlocks₁₁_mul]
      rw [lhs, rhs, R_mul_movedZ]
    · -- up block `(partProd)₁₂`
      have lhs : (partProd (movedC C Z0edit) (n + 1)).toBlocks₁₂
          = (partProd C n).toBlocks₁₁ * movedY C n
            + (partProd C n).toBlocks₁₂ * movedT C Z0edit n := by
        rw [show partProd (movedC C Z0edit) (n + 1)
            = partProd (movedC C Z0edit) n * movedC C Z0edit n from rfl,
          toBlocks₁₂_mul, hm12, hm22, ih11, ih12]
      have rhs : (partProd C (n + 1)).toBlocks₁₂
          = (partProd C n).toBlocks₁₁ * (C n).toBlocks₁₂
            + (partProd C n).toBlocks₁₂ * (C n).toBlocks₂₂ := by
        rw [show partProd C (n + 1) = partProd C n * C n from rfl, toBlocks₁₂_mul]
      rw [lhs, rhs, movedT, movedY]
      -- the algebraic step
      have hRu : (partProd C n).toBlocks₁₁ * uNorm C n = (partProd C n).toBlocks₁₂ := by
        rw [uNorm, ← Matrix.mul_assoc, Ring.mul_inverse_cancel _ (hB n), Matrix.one_mul]
      have hT : (C n).toBlocks₂₂ = blockSchur (C n) + vDown C n * (C n).toBlocks₁₂ := by
        rw [blockSchur, vDown]; abel
      have hWV : (partProd C n).toBlocks₁₂ * (movedZ C Z0edit n * Ring.inverse (C n).toBlocks₁₁)
          = (partProd C n).toBlocks₁₂ * vDown C n := by
        rw [vDown, ← Matrix.mul_assoc (partProd C n).toBlocks₁₂ (movedZ C Z0edit n)
          (Ring.inverse (C n).toBlocks₁₁), ← Matrix.mul_assoc (partProd C n).toBlocks₁₂
          (C n).toBlocks₂₁ (Ring.inverse (C n).toBlocks₁₁), R_mul_movedZ]
      have key : (partProd C n).toBlocks₁₁ * upEdit C n
          + (partProd C n).toBlocks₁₂ * (vDown C n * upEdit C n)
          = (partProd C n).toBlocks₁₂ * (blockSchur (C n) - schurTilde C n) :=
        cancel_up (partProd C n).toBlocks₁₁ (nMix C n) (uNorm C n) (vDown C n)
          (partProd C n).toBlocks₁₂ (blockSchur (C n) - schurTilde C n) hRu rfl (hNu n)
      exact Rstep (partProd C n).toBlocks₁₁ (partProd C n).toBlocks₁₂ (vDown C n)
        (C n).toBlocks₁₂ (upEdit C n) (blockSchur (C n)) (schurTilde C n) (C n).toBlocks₂₂
        (Ring.inverse (C n).toBlocks₁₁) (movedZ C Z0edit n) hT hWV key

end
end DLNFibre.DLN.RLCT
