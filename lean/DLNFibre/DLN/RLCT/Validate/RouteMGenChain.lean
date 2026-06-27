import DLNFibre.DLN.RLCT.Validate.RouteMChainBlock
import DLNFibre.DLN.RLCT.Validate.RouteMChainRate
import DLNFibre.DLN.RLCT.Validate.RouteMExtraction

/-!
# `RouteMGenChain` — the ∀M achiever `FactoredChain` over an opaque descent path (the structural lift)

The `(3,3,3,3)` `chain3333` (`RouteM3333Chain`) lifted to ARBITRARY `M : Fin (L+1) → ℕ` and an arbitrary
weakly-decreasing descent path `t : Fin (L+1) → ℕ` (the rate identity is PATH-AGNOSTIC, so this holds for
ANY `t` with `t 0 = M 0`, `t k ≤ M k`; the achiever minimiser is the special case that gives the
downstream `minAdm−1` Jacobian). The per-`k` `match`-defined `(3,3,3,3)` fields become a single uniform
`dite`-guarded recursion over the opaque `t`-widths:

* `Wext M` / `Text M t` — the ambient (`= M k`) and compressed (`Text 0 = M 0`, `Text (k+1) = t k`)
  width families, ℕ-indexed by an explicit `dite` (NOT `![…].getD`).
* `GenBlk M t` — the per-boundary block data (kept `Bmat`, residual `Nblk`, lift `Wblk`, residual `Rmat`,
  leaf `Rfin`) at the opaque widths.
* `chainOfMt` — the `FactoredChain L u`. `C k = Bmat k · chainQ(N_k) + u • Rmat k` (interior `k < L`),
  `C L = u • Rfin L` (leaf); `A k = chainA(N_k)(W_k)(C(k+1))`. `hC`/`hQA` discharged uniformly by
  `dif_pos` + `chainQ_mul_chainA` (the block algebra is M-agnostic); `base` by `dif_neg`. The identity
  boundary `k = 0` (`c_0 = M_0 − t_0 = 0`) needs NO special-casing — `chainQ`/`chainA` at `c = 0` are fine.

This is the ∀M rate engine's input. `RouteMGenChartId` consumes it for `prod M (φ u) = u • H` →
`routeMCore M (φ u) = u²·V`.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (pure matrix algebra; no analysis).
-/

namespace DLNFibre.DLN.RLCT

open Matrix

variable {L : ℕ}
variable {𝕜 : Type} [CommRing 𝕜]

/-! ## The width families (ℕ-indexed, explicit `dite` — NOT `![…].getD`) -/

/-- Ambient widths `Wwid k = M k` (for `k ≤ L`; `1` beyond, irrelevant). -/
def Wext (M : Fin (L + 1) → ℕ) : ℕ → ℕ := fun k => if h : k < L + 1 then M ⟨k, h⟩ else 1

/-- Compressed widths `Twid 0 = M 0`, `Twid (k+1) = t k` (for `k ≤ L`; `1` beyond). -/
def Text (M : Fin (L + 1) → ℕ) (t : Fin (L + 1) → ℕ) : ℕ → ℕ :=
  fun k => match k with
  | 0 => M 0
  | (j + 1) => if h : j < L + 1 then t ⟨j, h⟩ else 1

@[simp] theorem Wext_apply (M : Fin (L + 1) → ℕ) (k : ℕ) (h : k < L + 1) :
    Wext M k = M ⟨k, h⟩ := by simp [Wext, h]

@[simp] theorem Text_zero (M : Fin (L + 1) → ℕ) (t : Fin (L + 1) → ℕ) : Text M t 0 = M 0 := rfl

@[simp] theorem Text_succ (M : Fin (L + 1) → ℕ) (t : Fin (L + 1) → ℕ) (j : ℕ) (h : j < L + 1) :
    Text M t (j + 1) = t ⟨j, h⟩ := by simp [Text, h]

/-- The compressed width at `0` equals the ambient at `0` (`Text 0 = M 0 = Wext 0`) — the identity
boundary's `Twid 0 = Wwid 0`. -/
theorem Text_zero_eq_Wext (M : Fin (L + 1) → ℕ) (t : Fin (L + 1) → ℕ) :
    Text M t 0 = Wext M 0 := by simp [Text, Wext]

/-! ## The per-boundary block data -/

/-- **The per-boundary block data** for the achiever chain over `M`, `t`. Per `k`: the kept part `Bmat`
(`Fin (Twid k) → Fin (Twid (k+1))`), the residual `Nblk` (`Fin (Twid (k+1)) → Fin (Wwid k − Twid (k+1))`),
the lift `Wblk` (`Fin (Wwid k − Twid (k+1)) → Fin (Wwid (k+1))`), the residual block `Rmat`, and the leaf
residual `Rfin` (used at `k = L`). All at the opaque `Text`/`Wext` widths. -/
structure GenBlk (M : Fin (L + 1) → ℕ) (t : Fin (L + 1) → ℕ) (𝕜 : Type := ℝ)
    [CommRing 𝕜] where
  /-- The kept part `B_k = P_k K_k`. -/
  Bmat : (k : ℕ) → Matrix (Fin (Text M t k)) (Fin (Text M t (k + 1))) 𝕜
  /-- The residual block `N_k` (the chaining row's residual). -/
  Nblk : (k : ℕ) → Matrix (Fin (Text M t (k + 1))) (Fin (Wext M k - Text M t (k + 1))) 𝕜
  /-- The lift `W_k` (the chaining factor's lower rows). -/
  Wblk : (k : ℕ) → Matrix (Fin (Wext M k - Text M t (k + 1))) (Fin (Wext M (k + 1))) 𝕜
  /-- The residual block `R̄_k` (the `u`-carrying part of `C_k`). -/
  Rmat : (k : ℕ) → Matrix (Fin (Text M t k)) (Fin (Wext M k)) 𝕜
  /-- The leaf residual (`C_L = u • Rfin L`). -/
  Rfin : (k : ℕ) → Matrix (Fin (Text M t k)) (Fin (Wext M k)) 𝕜

/-! ## The chain fields (uniform `dite`-guarded over opaque widths) -/

/-- The chaining width arithmetic at boundary `k` (`k < L`): `Twid (k+1) + (Wwid k − Twid (k+1)) = Wwid k`
(needs `Twid (k+1) ≤ Wwid k`, the descent admissibility). -/
theorem genWidthEq (M t : Fin (L + 1) → ℕ) (hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k)
    (k : ℕ) (hk : k < L) : Text M t (k + 1) + (Wext M k - Text M t (k + 1)) = Wext M k := by
  have := hle k hk; omega

/-- **The compressed transition `C`** (uniform): interior `C k = Bmat k · chainQ(N_k) + u • Rmat k`
(`k < L`), leaf `C L = u • Rfin L`. -/
noncomputable def Cgen (u : 𝕜) (M t : Fin (L + 1) → ℕ) (B : GenBlk M t 𝕜)
    (hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k) :
    (k : ℕ) → Matrix (Fin (Text M t k)) (Fin (Wext M k)) 𝕜 := fun k =>
  if hk : k < L then B.Bmat k * chainQ (genWidthEq M t hle k hk) (B.Nblk k) + u • B.Rmat k
  else u • B.Rfin k

/-- **The layer `A`** (uniform): `A k = chainA(N_k)(W_k)(C (k+1))` (`k < L`), `0` beyond. -/
noncomputable def Agen (u : 𝕜) (M t : Fin (L + 1) → ℕ) (B : GenBlk M t 𝕜)
    (hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k) :
    (k : ℕ) → Matrix (Fin (Wext M k)) (Fin (Wext M (k + 1))) 𝕜 := fun k =>
  if hk : k < L then chainA (genWidthEq M t hle k hk) (B.Nblk k) (B.Wblk k) (Cgen u M t B hle (k + 1))
  else 0

/-- **The chaining row `Qmat`** (uniform): `Qmat k = chainQ(N_k)` (`k < L`), `0` beyond. -/
noncomputable def Qgen (M t : Fin (L + 1) → ℕ) (B : GenBlk M t 𝕜)
    (hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k) :
    (k : ℕ) → Matrix (Fin (Text M t (k + 1))) (Fin (Wext M k)) 𝕜 := fun k =>
  if hk : k < L then chainQ (genWidthEq M t hle k hk) (B.Nblk k) else 0

/-- **The ∀M achiever `FactoredChain`** over `M`, the descent path `t`, and block data `B`. `step`/`base`
discharged uniformly (`dif_pos`/`dif_neg` + `chainQ_mul_chainA`); the identity boundary `k = 0` (`c_0 = 0`)
needs no special-casing. -/
noncomputable def chainOfMt (u : 𝕜) (M t : Fin (L + 1) → ℕ) (B : GenBlk M t 𝕜)
    (hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k) : FactoredChain L u where
  Wwid := Wext M
  Twid := Text M t
  A := Agen u M t B hle
  C := Cgen u M t B hle
  Bmat := B.Bmat
  Qmat := Qgen M t B hle
  Rmat := B.Rmat
  R := B.Rfin L
  hC := by
    intro k hk
    show Cgen u M t B hle k = B.Bmat k * Qgen M t B hle k + u • B.Rmat k
    unfold Cgen Qgen
    rw [dif_pos hk, dif_pos hk]
  hQA := by
    intro k hk
    show Qgen M t B hle k * Agen u M t B hle k = Cgen u M t B hle (k + 1)
    unfold Qgen Agen
    rw [dif_pos hk, dif_pos hk]
    exact chainQ_mul_chainA _ _ _ _
  base := by
    show Cgen u M t B hle L = u • B.Rfin L
    unfold Cgen
    rw [dif_neg (lt_irrefl L)]

@[simp] theorem chainOfMt_Wwid (u : 𝕜) (M t : Fin (L + 1) → ℕ) (B : GenBlk M t 𝕜)
    (hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k) :
    (chainOfMt u M t B hle).toChain.Wwid = Wext M := rfl

@[simp] theorem chainOfMt_C_zero (u : 𝕜) (M t : Fin (L + 1) → ℕ) (B : GenBlk M t 𝕜)
    (hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k) (hL : 0 < L) :
    (chainOfMt u M t B hle).toChain.C 0
      = B.Bmat 0 * chainQ (genWidthEq M t hle 0 hL) (B.Nblk 0) + u • B.Rmat 0 := by
  show Cgen u M t B hle 0 = _
  unfold Cgen; rw [dif_pos hL]

end DLNFibre.DLN.RLCT
