import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

/-!
# Raw matrix chains in Aoyagi paper order

This file provides the matrix-only chain product used by the Aoyagi blow-up
expedition.  The edge matrices are in paper order,
`C p : Matrix (κ p.castSucc) (κ p.succ) R`, so extending the upper endpoint
multiplies by the new edge on the right.
-/

namespace DLNFibre
namespace DLN
namespace Aoyagi

open Matrix

universe u v

section RawPaperMatrixChain

variable {R : Type u} [Semiring R] {N : ℕ}
variable (κ : Fin (N + 1) → Type v) [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
variable (C : ∀ p : Fin N, Matrix (κ p.castSucc) (κ p.succ) R)

/-- The right-multiply step for the raw paper-order matrix chain. -/
def paperMatrixChainStep (i : Fin (N + 1)) :
    ⦃m : ℕ⦄ → (i ≤ m) →
      ((hm : m < N + 1) → Matrix (κ i) (κ ⟨m, hm⟩) R) →
        ((hm : m + 1 < N + 1) → Matrix (κ i) (κ ⟨m + 1, hm⟩) R) :=
  fun {m} _ rec hm ↦
    let p : Fin N := ⟨m, Nat.lt_of_succ_lt_succ hm⟩
    show Matrix (κ i) (κ p.succ) R from
      (show Matrix (κ i) (κ p.castSucc) R from rec p.castSucc.isLt) * C p

/-- The raw paper-order product `C i * ... * C (j-1)` for `i ≤ j`. -/
def paperMatrixChain (i j : Fin (N + 1)) (hij : i ≤ j) :
    Matrix (κ i) (κ j) R :=
  Nat.leRec (motive := fun m _ ↦
      (hm : m < N + 1) → Matrix (κ i) (κ ⟨m, hm⟩) R)
    (fun _ ↦ 1) (paperMatrixChainStep κ C i) hij j.isLt

/-- The empty raw paper-order matrix chain is the identity. -/
@[simp]
theorem paperMatrixChain_self (i : Fin (N + 1)) :
    paperMatrixChain κ C i i le_rfl = 1 := by
  unfold paperMatrixChain
  exact congrFun (Nat.leRec_self (motive := fun m _ ↦ (hm : m < N + 1) →
    Matrix (κ i) (κ ⟨m, hm⟩) R) (fun _ ↦ 1) (paperMatrixChainStep κ C i)) i.isLt

/-- Raw paper-order matrix chains are independent of the proof of endpoint order. -/
theorem paperMatrixChain_proof_irrel (i j : Fin (N + 1)) (hij hij' : i ≤ j) :
    paperMatrixChain κ C i j hij = paperMatrixChain κ C i j hij' := by
  congr

/-- Extending the upper endpoint multiplies by the new paper edge on the right. -/
theorem paperMatrixChain_succ_right (i : Fin (N + 1)) (p : Fin N)
    (hip : i ≤ p.castSucc) :
    paperMatrixChain κ C i p.succ (hip.trans (Fin.castSucc_le_succ p)) =
      paperMatrixChain κ C i p.castSucc hip * C p := by
  unfold paperMatrixChain
  exact congrFun (Nat.leRec_succ (h1 := Fin.val_fin_le.mpr hip)
    (h2 := Fin.val_fin_le.mpr (hip.trans (Fin.castSucc_le_succ p)))
    (refl := fun _ ↦ 1) (le_succ_of_le := paperMatrixChainStep κ C i)) p.succ.isLt

/-- The one-edge raw paper-order matrix chain is that edge. -/
@[simp]
theorem paperMatrixChain_edge (p : Fin N) (h : p.castSucc ≤ p.succ) :
    paperMatrixChain κ C p.castSucc p.succ h = C p := by
  calc
    paperMatrixChain κ C p.castSucc p.succ h
        = paperMatrixChain κ C p.castSucc p.succ
            (le_rfl.trans (Fin.castSucc_le_succ p)) :=
          paperMatrixChain_proof_irrel κ C p.castSucc p.succ h _
    _ = C p := by
      simpa using paperMatrixChain_succ_right κ C p.castSucc p le_rfl

end RawPaperMatrixChain

section SourceSuffix

variable {R : Type u} [Semiring R]

/-- Aoyagi's one-based source layer `s` as the zero-based vertex `Fin (L + 1)`. -/
def sourceLayerIndex (L s : ℕ) (hs0 : 1 ≤ s) (hsL : s ≤ L + 1) : Fin (L + 1) :=
  ⟨s - 1, by omega⟩

/-- Aoyagi's one-based source edge `s` as the zero-based edge `Fin L`. -/
def sourceEdgeIndex (L s : ℕ) (hs0 : 1 ≤ s) (hsL : s ≤ L) : Fin L :=
  ⟨s - 1, by omega⟩

/-- The lower endpoint of source edge `s` is source layer `s`. -/
@[simp]
theorem sourceEdgeIndex_castSucc (L s : ℕ) (hs0 : 1 ≤ s) (hsL : s ≤ L) :
    (sourceEdgeIndex L s hs0 hsL).castSucc =
      sourceLayerIndex L s hs0 (by omega) := by
  ext
  simp [sourceEdgeIndex, sourceLayerIndex]

/-- The upper endpoint of source edge `s` is source layer `s + 1`. -/
@[simp]
theorem sourceEdgeIndex_succ (L s : ℕ) (hs0 : 1 ≤ s) (hsL : s ≤ L) :
    (sourceEdgeIndex L s hs0 hsL).succ =
      sourceLayerIndex L (s + 1) (by omega) (by omega) := by
  ext
  simp [sourceEdgeIndex, sourceLayerIndex]
  omega

/-- The raw Aoyagi suffix `∏_{s=S+2}^L C^(s)`, with source layers numbered from `1`. -/
def sourceSuffixProduct {L : ℕ}
    (κ : Fin (L + 1) → Type v) [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (C : ∀ p : Fin L, Matrix (κ p.castSucc) (κ p.succ) R)
    (S : ℕ) (hS : S + 1 ≤ L) :
    Matrix (κ (sourceLayerIndex L (S + 2) (by omega) (by omega))) (κ (Fin.last L)) R :=
  paperMatrixChain κ C (sourceLayerIndex L (S + 2) (by omega) (by omega))
    (Fin.last L) (by
      change S + 2 - 1 ≤ L
      omega)

end SourceSuffix

end Aoyagi
end DLN
end DLNFibre
