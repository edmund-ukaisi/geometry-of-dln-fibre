import DLNFibre.DLN.RLCT.Foundations.Loss

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJTailProd` — the head-dropped tail chain (P1)

**Thread `genm-sj4-base`, Piece #1 (the `Z_tail` tail-product infra).** The units-free Γ×R γ' clause of
`FaithfulSJAt` (`RouteMSJAdm`) splits the deeper parameter space `Z ≃ᵐ (front block) × R` with the
deeper tail `Z_tail : R → Matrix …`, identifying each residual as an entry of `Γ(z) · Z_tail(r)`. For
the split to be a genuine measure-preserving factorization AND for the base leg (#4) to force `Z_tail`
to a fixed invertible matrix at width-2 (so the dropped units bound is DERIVED, not assumed), the tail
coordinate `R` is the **head-dropped parameter space** `Params (dropHead M)` and
`Z_tail := prod (dropHead M)` — the genuine suffix layer product `A⁽²⁾·…·A⁽ᴸ⁾`.

The load-bearing fact for #4: at the **width-2 base** the head-dropped chain has a single vertex and
**no layers**, so `Params (dropHead M)` is a one-point space and the tail product is the empty fold
`= 1`. Hence at the base `Z_tail ≡ 1` (invertible), giving the units bound `c = 1` trivially — the
mechanism the P0 cert (units DROPPED) relies on. (`genm-sj4-recon` §8-P1; the tail-tie is decorrelated-
confirmed NECESSARY, `codex/ztail-tie-answer.md`: the literal free-`R` untied γ' is UNSOUND — it admits
a divergent `Z_tail = diag(1,0)` witness.)

Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix

variable {L : ℕ}

/-- **The head-dropped chain** `dropHead M : Fin (L+1) → ℕ` of a width-`(≥2)` chain
`M : Fin (L+1+1) → ℕ`: drop the first vertex, keeping vertices `1, …, L+1`. Tail vertex `i` is vertex
`i.succ` of `M` — a clean `Fin.succ` reindex (no width casts). Its layers are `A⁽²⁾, …, A⁽ᴸ⁾`; its layer
product `prod (dropHead M)` is the deeper tail `Z_tail` of the split γ'. -/
def dropHead {L : ℕ} (M : Fin (L + 1 + 1) → ℕ) : Fin (L + 1) → ℕ := fun i => M i.succ

/-- `dropHead M` reads vertex `0` as `M 1` (the first tail vertex). -/
@[simp] theorem dropHead_zero {L : ℕ} (M : Fin (L + 1 + 1) → ℕ) : dropHead M 0 = M 1 := rfl

/-- `dropHead M` reads its last vertex as `M`'s last vertex. -/
@[simp] theorem dropHead_last {L : ℕ} (M : Fin (L + 1 + 1) → ℕ) :
    dropHead M (Fin.last L) = M (Fin.last (L + 1)) := by
  change M (Fin.last L).succ = M (Fin.last (L + 1))
  rw [Fin.succ_last]

/-- **The tail product at the width-2 base is the identity.** For a width-2 chain `M : Fin (1+1) → ℕ`
(`L = 0`), the head-dropped chain `dropHead M : Fin 1 → ℕ` has a single vertex and **no layers**, so its
parameter space `Params (dropHead M)` is a one-point space and the tail product is the empty fold `= 1`
(`prodAux … 0`). This forces `Z_tail ≡ 1` (invertible) at the base — the dropped units bound is DERIVED
here (`c = 1`), not carried. -/
theorem tailProd_width2 (M : Fin (1 + 1) → ℕ) (r : Params (dropHead M)) :
    prod (dropHead M) r = (1 : Matrix (Fin (M 1)) (Fin (M 1)) ℝ) := rfl

end DLNFibre.DLN.RLCT
